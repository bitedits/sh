(* sh_run_parity.ml
 *
 * The ONLY hand-written OCaml around the extracted kernel (sh_run.ml).  It has
 * two parts:
 *   (1) a thin, UNVERIFIED boundary: ordinary OCaml values (strings/ints) <-> the
 *       extracted types (Peano nat, text = list of byte-code nats), plus readable
 *       command constructors.  Nothing here is proof-bearing.
 *   (2) the extraction-fidelity harness: it re-runs, against the EXTRACTED OCaml
 *       kernel, every control-flow boundary law (sh_concrete.v §7) and every
 *       computational example (§8 expander / globber, §9 end-to-end) that the Rocq
 *       kernel verifies by reflexivity.  Those facts are kernel-checked in Coq, so
 *       the extracted program producing identical verdicts is direct evidence that
 *       Extraction preserved the model's semantics — the precondition the plan
 *       names before the hand-written interpreters are retired (Phase 3d).
 *
 * Build & run (verify_models.sh does this; see sh_extract.v for the driver):
 *   coqc sh_concrete.v; coqc sh_extract.v
 *   ocamlc -w -a -o sh_run_parity sh_run.mli sh_run.ml sh_run_parity.ml
 *   ./sh_run_parity
 *)
open Sh_run

(* ═══════════════════════════════════════════════════════════════════
   (1) boundary glue — string <-> text, int <-> Peano nat, constructors
   ═══════════════════════════════════════════════════════════════════ *)

let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n - 1))
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

(* run a command under a fuel budget through the model's own pure seam; None
   means the budget ran out first *)
let value fuel c (s : cstate) : obs option =
  match Sh_run.run Sh_run.pure_phi (nat_of_int fuel) c s with
  | None -> None
  | Some s' -> Some (observe s')

let expand fuel (env : env) (status : int) (word : string) : string =
  string_of_text
    (Sh_run.expand (nat_of_int fuel) (env_to_text env) (nat_of_int status)
       (text_of_string word))

let glob fuel (pat : string) (str : string) : bool =
  Sh_run.glob (nat_of_int fuel) (text_of_string pat) (text_of_string str)

(* ═══════════════════════════════════════════════════════════════════
   (2) fidelity harness — mirror sh_concrete.v §7-§9 in the derived OCaml
   ═══════════════════════════════════════════════════════════════════ *)

let passes = ref 0
let fails = ref 0

let check name cond =
  if cond then (incr passes; Printf.printf "  [PASS] %s\n" name)
  else (incr fails; Printf.printf "  [FAIL] %s\n" name)

let f = 16 (* ample fuel for these tiny programs *)
let empty = state ()

(* ── §7 control-flow boundary laws ───────────────────────────────── *)
let () =
  check "and-left-false-stops"
    (value f (and_ (ext "false") (ext "true")) empty = Some { o_status = 1; o_env = [] });
  check "or-left-true-stops"
    (value f (or_ (ext "true") (ext "false")) empty = Some { o_status = 0; o_env = [] });
  check "seq-runs-both-last-wins"
    (value f (seq (ext "false") (assign "k" "v")) empty
     = Some { o_status = 0; o_env = [("k", "v")] });
  check "while-false-zero-iterations"
    (value f (while_ (ext "false") (assign "z" "1")) empty
     = Some { o_status = 1; o_env = [] });
  check "bang-inverts-false"
    (value f (bang (ext "false")) empty = Some { o_status = 0; o_env = [] });
  check "bang-inverts-true"
    (value f (bang (ext "true")) empty = Some { o_status = 1; o_env = [] });
  check "if-true-runs-then"
    (value f (if_ (ext "true") (assign "a" "b") (assign "a" "c")) empty
     = Some { o_status = 0; o_env = [("a", "b")] });
  check "if-false-runs-else"
    (value f (if_ (ext "false") (assign "a" "b") (assign "a" "c")) empty
     = Some { o_status = 0; o_env = [("a", "c")] });
  check "ex-status-unknown-127"
    (value f (ext "nosuchcmd") empty = Some { o_status = 127; o_env = [] })

(* ── §8 expander + globber ───────────────────────────────────────── *)
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

(* ── §9 end-to-end: run writes the env, expand/glob read it back ─── *)
let () =
  let s1 = value f (assign "a" "b") empty in
  check "assign-then-expand-readback"
    (s1 = Some { o_status = 0; o_env = [("a", "b")] }
     && expand f [("a", "b")] 0 "$a" = "b");
  check "for-binds-last"
    (value f (for_ "x" ["a"; "b"] [skip]) empty
     = Some { o_status = 0; o_env = [("x", "b")] });
  check "for-empty-zero-runs"
    (value f (for_ "x" [] [ext "false"]) (state ~status:5 ())
     = Some { o_status = 0; o_env = [] });
  check "for-expands-word"
    (value f (for_ "x" ["$a"] [skip]) (state ~env:[("a", "9")] ())
     = Some { o_status = 0; o_env = [("a", "9"); ("x", "9")] });
  check "case-first-match"
    (value f (case_ "a" [(["a"], [ext "false"]); (["*"], [ext "true"])]) empty
     = Some { o_status = 1; o_env = [] });
  check "case-glob-fallback"
    (value f (case_ "a" [(["b"], [ext "false"]); (["*"], [ext "true"])]) empty
     = Some { o_status = 0; o_env = [] });
  check "case-no-match-zero"
    (value f (case_ "a" [(["b"], [ext "false"])]) empty
     = Some { o_status = 0; o_env = [] })

let () =
  Printf.printf "\n==> %d extraction-fidelity checks, %d failed\n" !passes !fails;
  if !fails = 0 then begin
    Printf.printf "All %d extraction-fidelity checks passed successfully!\n" !passes;
    exit 0
  end else begin
    Printf.printf "FIDELITY FAILURE (see [FAIL] lines above)\n";
    exit 1
  end
