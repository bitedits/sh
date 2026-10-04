(* sh_run_c_parity.ml
 *
 * The ONLY hand-written OCaml around the CLEAN BOUNDED KERNEL
 * (sh_run_c.ml, produced by sh_extract_jpl_c.v from sh_jpl_run_c.v +
 * sh_jpl_run_phase3.v + sh_jpl_run.v + sh_jpl_scan.v).  It has four unverified
 * parts:
 *   (1) boundary glue: ordinary OCaml <-> the extracted types;
 *   (2) a HOST LOOP: `mrun` is a pure first-order driver that stops at an
 *       external command and returns the effect as DATA, so something must
 *       service that seam and re-enter.  In Coq that is `host`, which takes a
 *       `phi` function and is therefore deliberately NOT extracted.  The
 *       `service`/`host` pair below is its executable twin, written without any
 *       function-valued argument — i.e. it is the prototype of the C main loop
 *       that JPL.7 will hand-write, and running it proves that `mrun`'s data
 *       surface (idx, argv, continuation stack, state) is ENOUGH to service the
 *       seam from outside the kernel.
 *   (3) the fidelity harness: the SAME observable facts sh_concrete.v §7-§9
 *       verifies, re-run through BOTH drivers — `mrun` (the machine that still
 *       calls the recursive helpers) and `mrun_c` (JPL.5-A.6, rewired onto the
 *       proved tail loops) — from one shared table, so a fact that only holds
 *       for one of the two shows up as a [FAIL] line rather than a gap in
 *       coverage.
 *   (4) the rewired kernel's OWN surface: the expander loop (`expand_it`) the
 *       kernel now calls, the word cap (`expand_c`), the branch
 *       guard (`branch_guardb`), and the one place the rewiring is deliberately
 *       weaker than the model — a case site whose guard fails, where the
 *       reference answers and `mrun_c` reports DLim.
 *
 * Each command check asserts two things about the machine's answer:
 *   - `host_value = literal`   : the clean kernel reproduces the verified fact;
 *   - `host_value = run_value` : it agrees with the recursive reference `run` on
 *     the same input (design invariant #2, behavioural isomorphism).
 * The rewired column asserts the same two things about `host_c_value`, which is
 * the executable reading of sh_jpl_run_c.v's transports: `mrun_c_ok` (soundness,
 * no hypothesis) and `host_c_agree` (completeness under `no_sat`) — and the §5
 * checks below are exactly where `no_sat` FAILS, so they assert the refusal
 * rather than an answer.
 *
 * Together with sh_run_parity.ml (run = literal) and sh_run_iter_parity.ml
 * (mloop = literal), this pins run == mloop == mrun+host == mrun_c+host ==
 * verified facts.
 *
 * DIFFERENCE FROM THE OTHER TWO ARTIFACTS, and the reason it exists: nats are
 * machine ints here (ExtrOcamlNatInt), so the Peano<->int conversion glue of
 * sh_run_iter_parity.ml disappears — `nat_of_int` is the identity.  That is what
 * the JPL.5 emitter needs to see: a kernel whose numbers already have a C type.
 *
 * §4 adds a second, smaller table: the proved tail loops of sh_jpl_scan.v
 * (getv_it / setv_it / glob_iter / match_any_iter / be_getv / be_setv) checked
 * against the concrete scans they were proved equal to, in the EMITTED code.
 * Coq already proves the agreement (sh_jpl_scan.v §4/§5); this only confirms
 * Extraction did not lose it.  Note the fuel asymmetry it exposes: glob_it
 * spends fuel per forward step AND per backtrack retry, so the same word needs
 * a larger budget than concrete `glob` consumes — hence GLOB_FUEL below, not the
 * command fuel.  Deciding the emitted fuel policy is JPL.5's job, not ours.
 *
 * Build & run — this is exactly verify_models.sh section 2c, which is the
 * canonical runner (sh_extract_jpl_c.v is the extraction driver; it also
 * byte-checks the vendored copy in src/kernel before running this):
 *   coqc sh_concrete.v sh_jpl.v sh_jpl_run.v sh_jpl_run_phase2.v
 *        sh_jpl_run_phase3.v sh_jpl_scan.v sh_jpl_run_c.v sh_extract_jpl_c.v
 *   ocamlc -w -a -o sh_run_c_parity sh_run_c.mli sh_run_c.ml sh_run_c_parity.ml
 *   ./sh_run_c_parity
 *)
open Sh_run_c

(* ═══════════════════════════════════════════════════════════════════
   (1) boundary glue — string <-> text; nat is already an int
   ═══════════════════════════════════════════════════════════════════ *)

let nat_of_int n = n (* identity: the artifact is int-valued *)

let text_of_string s =
  List.init (String.length s) (fun i -> Char.code s.[i])

let string_of_text t =
  String.concat "" (List.map (fun b -> String.make 1 (Char.chr b)) t)

type env = (string * string) list

let env_to_text (e : env) : (text * text) list =
  List.map (fun (k, v) -> (text_of_string k, text_of_string v)) e

let env_of_pairs (p : (text * text) list) : env =
  List.map (fun (k, v) -> (string_of_text k, string_of_text v)) p

type obs = { o_status : int; o_env : env }

let observe (st : cstate) : obs =
  { o_status = st.cstatus; o_env = env_of_pairs st.cenv }

let state ?(status = 0) ?(env : env = []) () : cstate =
  { cstatus = nat_of_int status; cenv = env_to_text env }

let skip = Skip
let ext w = Ext (0, [ text_of_string w ])
let assign k v = Assign (text_of_string k, text_of_string v)
let seq a b = Seq (a, b)
let and_ a b = And (a, b)
let or_ a b = Or (a, b)
let bang c = Bang c
let if_ c t e = If (c, t, e)
let while_ c b = While (c, b)
let for_ v ws body = For (text_of_string v, List.map text_of_string ws, body)

let case_ s brs =
  Case (text_of_string s,
        List.map (fun (ps, b) -> (List.map text_of_string ps, b)) brs)

(* ═══════════════════════════════════════════════════════════════════
   (2) the host: service one DEff from data, re-enter, no function argument
   ═══════════════════════════════════════════════════════════════════ *)

(* Budget per SEGMENT and per whole host run.  sh_jpl_run_phase2/3's well-founded
   `cfg_budget` proves every succeeding run finishes in finitely many steps, so a
   budget far above what these tiny §7-§9 programs need only means "never
   saturate"; any None below then comes from command fuel, mirroring run. *)
let budget = 100000

(* One seam service, inlined rather than passed as a function: the whole point of
   5-A.4 is that the kernel hands back DATA and the host decides what to do with
   it.  pure_run_phi is the verified leaf (sh_concrete §pure_phi). *)
let service idx argv s = pure_run_phi idx argv s

let rec host b g =
  if b = 0 then None
  else
    match mrun (b - 1) g with
    | DDone st -> Some st
    | DEff (idx, argv, k, s) ->
        (match service idx argv s with
         | Some s' -> host (b - 1) { cf = 0; cc = None; ck = k; cs = s' }
         | None -> None)
    | DLim -> None

(* The SAME host loop over the REWIRED driver: nothing here is specific to either
   machine except the name of the kernel, which is the point — the effect data
   surface `dres` is identical, so one host services both.  Coq calls this shape
   `host_c` (sh_jpl_run_c.v §4) and proves host_c = host under `no_sat`. *)
let rec host_c b g =
  if b = 0 then None
  else
    match mrun_c (b - 1) g with
    | DDone st -> Some st
    | DEff (idx, argv, k, s) ->
        (match service idx argv s with
         | Some s' -> host_c (b - 1) { cf = 0; cc = None; ck = k; cs = s' }
         | None -> None)
    | DLim -> None

let cfg fuel c (s : cstate) : cfg =
  { cf = nat_of_int fuel; cc = Some c; ck = []; cs = s }

let host_value fuel c (s : cstate) : obs option =
  match host budget (cfg fuel c s) with
  | None -> None
  | Some st -> Some (observe st)

let host_c_value fuel c (s : cstate) : obs option =
  match host_c budget (cfg fuel c s) with
  | None -> None
  | Some st -> Some (observe st)

(* the recursive reference, int-valued like the kernel *)
let run_value fuel c (s : cstate) : obs option =
  match run pure_run_phi (nat_of_int fuel) c s with
  | None -> None
  | Some st -> Some (observe st)

let expand_of fuel (env : env) (status : int) (word : string) : string =
  string_of_text (expand (nat_of_int fuel) (env_to_text env) (nat_of_int status)
                    (text_of_string word))

let glob_c fuel (pat : string) (str : string) : bool =
  glob (nat_of_int fuel) (text_of_string pat) (text_of_string str)

(* ═══════════════════════════════════════════════════════════════════
   (3) fidelity harness — mirror sh_concrete.v §7-§9 through BOTH drivers
   ═══════════════════════════════════════════════════════════════════ *)

let passes = ref 0
let fails = ref 0

let check name cond =
  if cond then (incr passes; Printf.printf "  [PASS] %s\n" name)
  else (incr fails; Printf.printf "  [FAIL] %s\n" name)

let f = 16 (* ample command fuel for these tiny programs *)
let empty = state ()

(* one table, two machines: the fact is asserted of the recursive-helper machine
   AND of the rewired one, each against the literal and against `run`. *)
let cmd_check name fuel c s exp =
  check name (host_value fuel c s = exp && host_value fuel c s = run_value fuel c s)

let cmd_check_c name fuel c s exp =
  check (name ^ " [rewired]")
        (host_c_value fuel c s = exp && host_c_value fuel c s = run_value fuel c s)

type fact = { name : string; fuel : int; cmd : cmd; st : cstate; exp : obs option }

(* ── §7 control-flow boundary laws, and §9's end-to-end reads ───────── *)
let facts =
  [ { name = "and-left-false-stops"; fuel = f; st = empty;
      cmd = and_ (ext "false") (ext "true");
      exp = Some { o_status = 1; o_env = [] } };
    { name = "or-left-true-stops"; fuel = f; st = empty;
      cmd = or_ (ext "true") (ext "false");
      exp = Some { o_status = 0; o_env = [] } };
    { name = "seq-runs-both-last-wins"; fuel = f; st = empty;
      cmd = seq (ext "false") (assign "k" "v");
      exp = Some { o_status = 0; o_env = [("k", "v")] } };
    { name = "while-false-zero-iterations"; fuel = f; st = empty;
      cmd = while_ (ext "false") (assign "z" "1");
      exp = Some { o_status = 1; o_env = [] } };
    { name = "bang-inverts-false"; fuel = f; st = empty;
      cmd = bang (ext "false"); exp = Some { o_status = 0; o_env = [] } };
    { name = "bang-inverts-true"; fuel = f; st = empty;
      cmd = bang (ext "true"); exp = Some { o_status = 1; o_env = [] } };
    { name = "if-true-runs-then"; fuel = f; st = empty;
      cmd = if_ (ext "true") (assign "a" "b") (assign "a" "c");
      exp = Some { o_status = 0; o_env = [("a", "b")] } };
    { name = "if-false-runs-else"; fuel = f; st = empty;
      cmd = if_ (ext "false") (assign "a" "b") (assign "a" "c");
      exp = Some { o_status = 0; o_env = [("a", "c")] } };
    { name = "ex-status-unknown-127"; fuel = f; st = empty;
      cmd = ext "nosuchcmd"; exp = Some { o_status = 127; o_env = [] } };
    { name = "for-binds-last"; fuel = f; st = empty;
      cmd = for_ "x" ["a"; "b"] [skip]; exp = Some { o_status = 0; o_env = [("x", "b")] } };
    { name = "for-empty-zero-runs"; fuel = f; st = state ~status:5 ();
      cmd = for_ "x" [] [ext "false"]; exp = Some { o_status = 0; o_env = [] } };
    { name = "for-expands-word"; fuel = f; st = state ~env:[("a", "9")] ();
      cmd = for_ "x" ["$a"] [skip];
      exp = Some { o_status = 0; o_env = [("a", "9"); ("x", "9")] } };
    { name = "case-first-match"; fuel = f; st = empty;
      cmd = case_ "a" [(["a"], [ext "false"]); (["*"], [ext "true"])];
      exp = Some { o_status = 1; o_env = [] } };
    { name = "case-glob-fallback"; fuel = f; st = empty;
      cmd = case_ "a" [(["b"], [ext "false"]); (["*"], [ext "true"])];
      exp = Some { o_status = 0; o_env = [] } };
    { name = "case-no-match-zero"; fuel = f; st = empty;
      cmd = case_ "a" [(["b"], [ext "false"])];
      exp = Some { o_status = 0; o_env = [] } } ]

let () =
  List.iter (fun ft ->
    cmd_check ft.name ft.fuel ft.cmd ft.st ft.exp;
    cmd_check_c ft.name ft.fuel ft.cmd ft.st ft.exp) facts

(* ── §8 expander + globber (same emitted scan code the machine drives) ── *)
let () =
  check "expand-dollar-name" (expand_of f [("a", "b")] 0 "$a" = "b");
  check "expand-unset-empty" (expand_of f [] 0 "$a" = "");
  check "expand-brace-name" (expand_of f [("a", "b")] 0 "${a}" = "b");
  check "expand-dollar-question-zero" (expand_of f [] 0 "$?" = "0");
  check "expand-dollar-question-one" (expand_of f [] 1 "$?" = "1");
  check "expand-lone-dollar-literal" (expand_of f [] 0 "$@A" = "$@A");
  check "glob-exact" (glob_c f "ab" "ab");
  check "glob-question" (glob_c f "a?" "ac");
  check "glob-star" (glob_c f "a*" "acd");
  check "glob-mismatch" (not (glob_c f "ab" "ac"));
  check "assign-then-expand-readback"
    (host_value f (assign "a" "b") empty = Some { o_status = 0; o_env = [("a", "b")] }
     && host_value f (assign "a" "b") empty = run_value f (assign "a" "b") empty
     && expand_of f [("a", "b")] 0 "$a" = "b");
  check "assign-then-expand-readback [rewired]"
    (host_c_value f (assign "a" "b") empty = Some { o_status = 0; o_env = [("a", "b")] }
     && host_c_value f (assign "a" "b") empty = run_value f (assign "a" "b") empty)

(* the emitted expander loop, and the same call through L2's `expand`, both read
   back as strings so the comparison is a plain equality of outputs. *)
let expand_it_of fuel (env : env) (status : int) (word : string) : string =
  string_of_text (expand_it (nat_of_int fuel) (env_to_text env) (nat_of_int status)
                    (text_of_string word))

(* the sweep's words: every shape the expander dispatches on, plus the ones that
   run off the end of the word (unterminated brace, bare '$', a name that is not
   set).  Each sweep is 15 words x 9 fuels = 135 comparisons; the two sweeps below
   (unset env, then a set env) are therefore 270 comparisons of the loop against
   L2's expand. *)
let exp_words =
  [ ""; "$"; "$a"; "$b"; "$?"; "${a}"; "${a"; "$}"; "$a$b"; "x$ay"; "${abc}";
    "$*"; "$a@"; "@$"; "$$" ]

let expand_sweep (env : env) (status : int) : bool =
  let bad = ref 0 in
  List.iter
    (fun w ->
      for fuel = 0 to 8 do
        if expand_it_of fuel env status w <> expand_of fuel env status w
        then incr bad
      done)
    exp_words;
  !bad = 0

(* ═══════════════════════════════════════════════════════════════════
   (4) the proved tail loops, in the emitted code (sh_jpl_scan.v §4/§5)
   ═══════════════════════════════════════════════════════════════════ *)

let gfuel = 64 (* see the fuel note in the header *)

let getv_it_c f e k =
  getv_it (nat_of_int f) (text_of_string k) (env_to_text e)
let getv_c e k = getv (text_of_string k) (env_to_text e)

let setv_it_c e k v =
  let m = env_to_text e in
  match setv_it (List.length m + 1) (text_of_string k) (text_of_string v) [] m with
  | Some r -> r = setv (text_of_string k) (text_of_string v) m
  | None -> false

let be_roundtrip e k v =
  let m = env_to_text e in
  match be_setv (text_of_string k) (text_of_string v)
          { be_pairs = m; be_len = List.length m } with
  | BOk e' -> be_getv (text_of_string k) e' = Some (text_of_string v)
  | BLimit -> false

let () =
  check "getv_it==getv hit"
    (getv_it_c 4 [("a", "b"); ("c", "d")] "c" = getv_c [("a", "b"); ("c", "d")] "c");
  check "getv_it==getv miss"
    (getv_it_c 4 [("a", "b")] "z" = None && getv_c [("a", "b")] "z" = None);
  check "setv_it==setv replace" (setv_it_c [("a", "b"); ("c", "d")] "a" "z");
  check "setv_it==setv append" (setv_it_c [("a", "b")] "c" "d");
  check "be_getv/be_setv roundtrip" (be_roundtrip [("a", "b")] "k" "v");
  check "glob_iter==glob star"
    (glob_iter (nat_of_int gfuel) (text_of_string "a*b") (text_of_string "axxb")
     = glob (nat_of_int gfuel) (text_of_string "a*b") (text_of_string "axxb"));
  check "glob_iter==glob nomatch"
    (glob_iter (nat_of_int gfuel) (text_of_string "a*b") (text_of_string "axxc")
     = glob (nat_of_int gfuel) (text_of_string "a*b") (text_of_string "axxc"));
  check "match_any_iter==match_any"
    (match_any_iter (nat_of_int gfuel)
       [ text_of_string "a"; text_of_string "a*" ] (text_of_string "ac")
     = match_any (nat_of_int gfuel)
         [ text_of_string "a"; text_of_string "a*" ] (text_of_string "ac"));

  (* sh_jpl_scan.v §6: the expander LOOP against L2's `expand`.  Unlike the glob
     loops above there is no fuel side condition to respect — expand_it_correct
     is hypothesis-free — so the sweep is over EVERY fuel as well. *)
  check "expand_it==expand name"
    (expand_it_of f [("a", "b")] 0 "$a" = expand_of f [("a", "b")] 0 "$a");
  check "expand_it==expand lone dollar"
    (expand_it_of f [] 0 "$@A" = expand_of f [] 0 "$@A");
  check "expand_it==expand brace"
    (expand_it_of f [("a", "b")] 0 "${a}x" = expand_of f [("a", "b")] 0 "${a}x");
  check "expand_it==expand qmark"
    (expand_it_of f [] 127 "$?" = expand_of f [] 127 "$?");
  check "expand_it==expand zero fuel"
    (expand_it_of 0 [("a", "b")] 0 "$a" = "" && expand_of 0 [("a", "b")] 0 "$a" = "");
  check "expand_it==expand sweep, unset env" (expand_sweep [] 7);
  check "expand_it==expand sweep, set env"
    (expand_sweep [("a", "b"); ("abc", "z")] 127)

(* ═══════════════════════════════════════════════════════════════════
   (5) the rewired kernel's own surface: the cap, the guard, and the refusal
   ═══════════════════════════════════════════════════════════════════ *)

(* expand_c is the ONE place the word cap is enforced, and it is a total
   saturating function: BOk the expansion when it fits MAX_WORD, BLimit when it
   does not.  Nothing in the kernel can emit an oversized word. *)
let cap = 256 (* MAX_WORD *)

let capped fuel (env : env) (word : string) : (string * int) option =
  match expand_c (nat_of_int fuel) (env_to_text env) 0 (text_of_string word) with
  | BOk bw -> Some (string_of_text bw.bw_bytes, bw.bw_len)
  | BLimit -> None

let () =
  check "expand_c admits exactly at the cap"
    (capped 4096 [("a", String.make cap 'x')] "$a"
     = Some (String.make cap 'x', cap));
  check "expand_c saturates one byte over the cap"
    (capped 4096 [("a", String.make (cap + 1) 'x')] "$a" = None)

(* The guard, in the emitted code: a linear comparison of branch_need against the
   site fuel, plus the caps.  7 is this pattern's threshold (§6 of
   sh_jpl_run_c.v measures branch_need ["*a"] "aaa" = 7), so 6 refuses and 7
   admits — the guard decides at the SAME site fuel the reference matcher needs,
   which is what makes it cheap enough to keep. *)
let () =
  check "branch_guardb refuses one below the threshold"
    (branch_guardb 6 [ text_of_string "*a" ] (text_of_string "aaa") = false);
  check "branch_guardb admits at the threshold"
    (branch_guardb 7 [ text_of_string "*a" ] (text_of_string "aaa") = true);
  check "branch_guardb enforces the list cap"
    (branch_guardb 4096 (List.init 1024 (fun _ -> [ 97 ])) [ 97 ] = true
     && branch_guardb 4096 (List.init 1025 (fun _ -> [ 97 ])) [ 97 ] = false);
  check "branch_guardb enforces the word cap"
    (branch_guardb 4096 [ [ 97 ] ] (text_of_string (String.make 256 'a')) = true
     && branch_guardb 4096 [ [ 97 ] ] (text_of_string (String.make 257 'a')) = false)

(* The measured band, end to end: the reference answers at command fuel 8, the
   rewired machine reports DLim — and this is the ONLY kind of disagreement the
   rewiring admits (a refusal, never a wrong answer: sh_jpl_run_c.v §3/§4). *)
let band_case = case_ "aaa" [(["*a"], [ext "true"])]

let () =
  check "reference answers where the rewired machine saturates"
    (host_value 8 band_case empty = Some { o_status = 0; o_env = [] }
     && host_c_value 8 band_case empty = None);
  check "one fuel higher the rewired machine agrees"
    (host_c_value 9 band_case empty = Some { o_status = 0; o_env = [] }
     && host_c_value 9 band_case empty = host_value 9 band_case empty
     && host_c_value 9 band_case empty = run_value 9 band_case empty)

(* The rewired assignment goes through the scan, and the environment it writes is
   read back by the concrete expander — the same end-to-end read §9 asserts. *)
let () =
  let a = assign "a" "b" in
  check "rewired assign==scan readback"
    (host_c_value f a empty = Some { o_status = 0; o_env = [("a", "b")] }
     && expand_of f [("a", "b")] 0 "$a" = "b")

let () =
  Printf.printf "\n==> %d clean-kernel fidelity checks, %d failed\n" !passes !fails;
  if !fails = 0 then begin
    Printf.printf "All %d clean-kernel fidelity checks passed successfully!\n" !passes;
    exit 0
  end else begin
    Printf.printf "CLEAN-KERNEL FIDELITY FAILURE (see [FAIL] lines above)\n";
    exit 1
  end
