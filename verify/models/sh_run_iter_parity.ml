(* sh_run_iter_parity.ml
 *
 * The ONLY hand-written OCaml around the extracted ITERATIVE kernel
 * (sh_run_iter.ml, produced by sh_extract_iter.v from sh_jpl_run.v's machine).
 * Like sh_run_parity.ml it has two unverified parts:
 *   (1) a thin boundary glue: ordinary OCaml <-> the extracted types; and
 *   (2) the extraction-fidelity harness, which re-runs the SAME 26 observable
 *       facts sh_concrete.v §7-§9 verifies by kernel-reflexivity — but this time
 *       through the JPL-shaped iterative machine `mloop` (a non-recursive `step`
 *       dispatcher + a fuel-bounded tail driver), NOT the recursive `run`.
 *
 * Because sh_extract_iter.v extracts BOTH `run` and `mloop` into one module that
 * shares a single set of datatypes, each command check asserts two things about
 * the machine's answer:
 *   - `mloop_value = literal`  : the iterative kernel reproduces the verified fact;
 *   - `mloop_value = run_value`: the iterative kernel agrees with the recursive
 *     reference on the same input — the behavioural isomorphism (design
 *     invariant #2).  Together with sh_run_parity.ml (run = literal) this pins
 *     run == mloop == verified facts for every §7-§9 boundary.
 *
 * `mloop` needs a step budget B (an extra nat, orthogonal to the command fuel F
 * inside the config).  Well-foundedness (sh_jpl_run_phase2.v: next_decrease /
 * prec_wf) proves every succeeding run finishes in < cfg_budget steps, so a B
 * far above that bound just means "never saturate on budget" — the machine then
 * reaches Odone with the exact answer, and any BLimit comes only from fuel F
 * exhaustion, mirroring run's None.  The tiny §7-§9 programs need only dozens of
 * steps; BUDGET below is deliberately many orders above that.
 *
 * Build & run (verify_models.sh does this; see sh_extract_iter.v for the driver):
 *   coqc sh_concrete.v sh_jpl.v sh_jpl_run.v sh_extract_iter.v
 *   ocamlc -w -a -o sh_run_iter_parity sh_run_iter.mli sh_run_iter.ml sh_run_iter_parity.ml
 *   ./sh_run_iter_parity
 *)
open Sh_run_iter

(* ═══════════════════════════════════════════════════════════════════
   (1) boundary glue — string <-> text, int <-> Peano nat, constructors
   ═══════════════════════════════════════════════════════════════════ *)

(* Tail-recursive: the step budget is large, so the naive S-descending build
   would blow the OCaml stack; this accumulates without deepening. *)
let nat_of_int n =
  let rec aux k acc = if k <= 0 then acc else aux (k - 1) (S acc) in
  aux n O

let rec int_of_nat = function O -> 0 | S k -> 1 + int_of_nat k

let text_of_string s =
  List.init (String.length s) (fun i -> nat_of_int (Char.code s.[i]))

let rec string_of_text = function
  | [] -> ""
  | b :: r -> String.make 1 (Char.chr (int_of_nat b)) ^ string_of_text r

type env = (string * string) list

let env_to_text (e : env) : (text * text) list =
  List.map (fun (k, v) -> (text_of_string k, text_of_string v)) e

let env_of_cstate (st : cstate) : env =
  List.map (fun (k, v) -> (string_of_text k, string_of_text v)) st.cenv

type obs = { o_status : int; o_env : env }

let observe (st : cstate) : obs =
  { o_status = int_of_nat st.cstatus; o_env = env_of_cstate st }

let state ?(status = 0) ?(env : env = []) () : cstate =
  { cstatus = nat_of_int status; cenv = env_to_text env }

let skip = Skip
let ext w = Ext (O, [ text_of_string w ])
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

(* ── the recursive reference: run under a fuel budget through pure_phi ── *)
let run_value fuel c (s : cstate) : obs option =
  match Sh_run_iter.run Sh_run_iter.pure_phi (nat_of_int fuel) c s with
  | None -> None
  | Some s' -> Some (observe s')

(* ── the JPL-shaped iterative kernel: mloop over the initial config ── *)
let budget = 100000

let mloop_value fuel c (s : cstate) : obs option =
  match Sh_run_iter.mloop Sh_run_iter.pure_phi (nat_of_int budget)
          { cf = nat_of_int fuel; cc = Some c; ck = []; cs = s } with
  | BOk st -> Some (observe st)
  | BLimit -> None

let expand fuel (env : env) (status : int) (word : string) : string =
  string_of_text
    (Sh_run_iter.expand (nat_of_int fuel) (env_to_text env) (nat_of_int status)
       (text_of_string word))

let glob fuel (pat : string) (str : string) : bool =
  Sh_run_iter.glob (nat_of_int fuel) (text_of_string pat) (text_of_string str)

(* ═══════════════════════════════════════════════════════════════════
   (2) fidelity harness — mirror sh_concrete.v §7-§9 through mloop
   ═══════════════════════════════════════════════════════════════════ *)

let passes = ref 0
let fails = ref 0

let check name cond =
  if cond then (incr passes; Printf.printf "  [PASS] %s\n" name)
  else (incr fails; Printf.printf "  [FAIL] %s\n" name)

let f = 16 (* ample command fuel for these tiny programs *)
let empty = state ()

(* Each command check: the machine reaches the verified literal AND agrees with
   the recursive reference. *)
let cmd_check name fuel c s exp =
  let m = mloop_value fuel c s in
  check name (m = exp && m = run_value fuel c s)

(* ── §7 control-flow boundary laws ───────────────────────────────── *)
let () =
  cmd_check "and-left-false-stops" f (and_ (ext "false") (ext "true")) empty
    (Some { o_status = 1; o_env = [] });
  cmd_check "or-left-true-stops" f (or_ (ext "true") (ext "false")) empty
    (Some { o_status = 0; o_env = [] });
  cmd_check "seq-runs-both-last-wins" f (seq (ext "false") (assign "k" "v")) empty
    (Some { o_status = 0; o_env = [("k", "v")] });
  cmd_check "while-false-zero-iterations" f (while_ (ext "false") (assign "z" "1")) empty
    (Some { o_status = 1; o_env = [] });
  cmd_check "bang-inverts-false" f (bang (ext "false")) empty
    (Some { o_status = 0; o_env = [] });
  cmd_check "bang-inverts-true" f (bang (ext "true")) empty
    (Some { o_status = 1; o_env = [] });
  cmd_check "if-true-runs-then" f (if_ (ext "true") (assign "a" "b") (assign "a" "c")) empty
    (Some { o_status = 0; o_env = [("a", "b")] });
  cmd_check "if-false-runs-else" f (if_ (ext "false") (assign "a" "b") (assign "a" "c")) empty
    (Some { o_status = 0; o_env = [("a", "c")] });
  cmd_check "ex-status-unknown-127" f (ext "nosuchcmd") empty
    (Some { o_status = 127; o_env = [] })

(* ── §8 expander + globber (same extracted scan code the machine drives) ── *)
let () =
  check "expand-dollar-name" (expand f [("a", "b")] 0 "$a" = "b");
  check "expand-unset-empty" (expand f [] 0 "$a" = "");
  check "expand-brace-name" (expand f [("a", "b")] 0 "${a}" = "b");
  check "expand-dollar-question-zero" (expand f [] 0 "$?" = "0");
  check "expand-dollar-question-one" (expand f [] 1 "$?" = "1");
  check "expand-lone-dollar-literal" (expand f [] 0 "$@A" = "$@A");
  check "glob-exact" (glob f "ab" "ab");
  check "glob-question" (glob f "a?" "ac");
  check "glob-star" (glob f "a*" "acd");
  check "glob-mismatch" (not (glob f "ab" "ac"))

(* ── §9 end-to-end: machine writes the env, expand/glob read it back ── *)
let () =
  check "assign-then-expand-readback"
    (mloop_value f (assign "a" "b") empty = Some { o_status = 0; o_env = [("a", "b")] }
     && mloop_value f (assign "a" "b") empty = run_value f (assign "a" "b") empty
     && expand f [("a", "b")] 0 "$a" = "b");
  cmd_check "for-binds-last" f (for_ "x" ["a"; "b"] [skip]) empty
    (Some { o_status = 0; o_env = [("x", "b")] });
  cmd_check "for-empty-zero-runs" f (for_ "x" [] [ext "false"]) (state ~status:5 ())
    (Some { o_status = 0; o_env = [] });
  cmd_check "for-expands-word" f (for_ "x" ["$a"] [skip]) (state ~env:[("a", "9")] ())
    (Some { o_status = 0; o_env = [("a", "9"); ("x", "9")] });
  cmd_check "case-first-match" f
    (case_ "a" [(["a"], [ext "false"]); (["*"], [ext "true"])]) empty
    (Some { o_status = 1; o_env = [] });
  cmd_check "case-glob-fallback" f
    (case_ "a" [(["b"], [ext "false"]); (["*"], [ext "true"])]) empty
    (Some { o_status = 0; o_env = [] });
  cmd_check "case-no-match-zero" f
    (case_ "a" [(["b"], [ext "false"])]) empty
    (Some { o_status = 0; o_env = [] })

let () =
  Printf.printf "\n==> %d iterative-kernel fidelity checks, %d failed\n" !passes !fails;
  if !fails = 0 then begin
    Printf.printf "All %d iterative-kernel fidelity checks passed successfully!\n" !passes;
    exit 0
  end else begin
    Printf.printf "ITERATIVE FIDELITY FAILURE (see [FAIL] lines above)\n";
    exit 1
  end
