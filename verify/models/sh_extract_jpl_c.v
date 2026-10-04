(* sh_extract_jpl_c.v

 * JPL.5-A.5 — extraction of the CLEAN BOUNDED KERNEL (Phase 3d-C, path A).

 * What this file is: the derived half of the pipeline for the closure-free
 * machine.  Nothing here is proof-bearing; it only configures and invokes
 * Coq's Extraction machinery, exactly as sh_extract.v (recursive `run`) and
 * sh_extract_iter.v (JPL.4 `mloop`) do for their layers.  It differs from both
 * in the SETTINGS: this is the first extraction that asks for the JPL-shaped
 * target representation rather than a faithful copy of the Coq term.

 *   1. nat -> machine integer.  `ExtrOcamlNatInt` replaces the Peano `O`/`S`
 *      encoding with OCaml `int`, which is what the JPL.5 emitter maps to the
 *      fixed-width `uint32_t` of sh_jpl's cap_order / cap_fuel_order (every value
 *      is provably <= MAX_FUEL = 136 449 < 2^31, so the word cannot wrap).  Peano
 *      nats have no C representation at all, so without this the emitter would
 *      have to invent one.
 *   2. arithmetic as primitives.  Coq's `Nat.div` / `Nat.modulo` / `Nat.sub` are
 *      transparent fixpoints, so an unhooked extraction emits them as OCaml
 *      recursion — a JPL Rule 6 violation imported from the standard library
 *      rather than from our model.  The `Extract Constant` hooks below replace
 *      them with `/`, `mod`, and clamped `-`.
 *      TOOLCHAIN GOTCHA (measured, Rocq 9.2): the hooks bind only if `Arith` and
 *      `PeanoNat` are imported BEFORE the `Extract Constant` lines.  Required in
 *      the other order, the hint refers to a constant the extraction engine never
 *      sees and is silently ignored — extraction still succeeds, and the emitted
 *      file keeps `let rec divmod`.  Nothing warns.
 *   3. the kernel entry point is FIRST-ORDER.  `mrun : nat -> cfg -> dres` takes
 *      no `phi` function (sh_jpl_run_phase3.v §8 exhibits exactly that type), so
 *      the emitted driver has no functional parameter and no captured
 *      environment — the construct JPL Rules 6/29 forbid.  `host`, the Coq model
 *      of the C main loop, is deliberately NOT extracted: a host that takes a
 *      function argument is what the C side re-implements as a plain loop over
 *      `mrun`'s `DEff` data (JPL.7).  The parity harness's hand-written OCaml
 *      host is the executable prototype of that loop.

 * Div-by-zero, which the hooks make a real risk: the only divisors reachable
 * from the extracted surface are the LITERALS 256 (`nstat k = k mod 256`) and 10
 * (`nat_digits`'s decimal split), so no division by a variable can occur.  The
 * one variable-divisor site in the bounded layer, sh_jpl's `b_divmod`, guards
 * `Nat.eqb b 0` and returns BLimit before dividing.  Both facts are restated in
 * the JPL.6 lint list, which is where a mechanical check belongs.

 * Surface extracted (and why each is here):
 *   mrun, step        the JPL-shaped kernel — the emitter's actual input;
 *   dres, cfg, out    its data surface, so the .mli documents the boundary the
 *                     C host must service;
 *   run, pure_run_phi the recursive REFERENCE, extracted into the same module so
 *                     the parity harness can compare mrun against run on one
 *                     shared set of datatypes with no coercion glue (the same
 *                     trick sh_extract_iter.v uses).  They are parity-only and
 *                     are NOT part of the C surface.
 *   expand, glob      the scans the machine drives, exposed so §8's expander /
 *                     globber checks run through the same emitted code the
 *                     machine uses internally.
 *   getv_it, setv_it, be_getv, be_setv, glob_iter, match_any_iter, expand_it
 *                     the proved tail loops of sh_jpl_scan.v (§4, §5, §6).
 *   step_c, mrun_c, expand_c, assign_c, bind_word_o, enter_for_c,
 *   enter_case_c, branch_guardb
 *                     THE REWIRED KERNEL (sh_jpl_run_c.v, JPL.5-A.6, wired
 *                     2026-10-04): the same machine with `setv` replaced by the
 *                     `setv_it` scan, `match_any` by `branch_guardb` +
 *                     `match_any_iter`, and `bind_word`'s write by the scan.
 *                     `mrun : nat -> cfg -> dres` stays first-order, so the
 *                     rewired driver `mrun_c` has no functional parameter
 *                     either.  `host_c` is NOT extracted for the same reason
 *                     `host` is not — it takes `phi : run_phi`, a function type;
 *                     the parity harness's OCaml host loop is its twin and runs
 *                     against `mrun_c` too.
 *   jpl_caps_table    THE CAP TABLE AS DATA (sh_jpl.v §1.1, 5-B.2a).  Extraction
 *                     emits a constant only where code mentions it, so the four
 *                     caps the proofs alone use (MAX_WIDTH, MAX_ARGV, MAX_CMD,
 *                     MAX_STACK) would vanish, and the emitter would have to hold
 *                     its own copy of numbers the model owns — the parallel
 *                     encoding this project already retired sh_model.ml over.
 *                     The record carries all nine, pinned field-by-field by
 *                     jpl_caps_are_locked, and jpl_cmd/jpl_stack are spelled from
 *                     the fuel margin (max_cmd_from_margin, max_stack_from_margin)
 *                     so the artifact grows by 63 lines instead of carrying a
 *                     4096-application Int.succ chain for each pool capacity.
 *                     MEASURED (Rocq 9.2): the emitted .mli keeps the record
 *                     CONCRETE — `type jpl_caps = { jpl_width : int; ... }` —
 *                     because no extracted code accesses a projection, so no
 *                     extraction-opaque-accessed warning fires; the emitter reads
 *                     the record literal out of the .ml either way.
 *
 * `step`/`mrun` (the recursive-helper machine) and `run` stay in the artifact as
 * the IN-MODULE ORACLE: the harness asserts `mrun_c` == `mrun` == `run` on the
 * same datatypes, which is the executable restatement of `step_c_ok` plus the
 * transports of sh_jpl_run_c.v §3-§4.
 *
 * This artifact is gate rung 2c (verify_models.sh) and is vendored as
 * src/kernel/sh_run_c.ml{,i}, so a re-extraction that changes it must be followed
 * by re-copying the vendored pair or the anti-rot diff fails.

 * sh_run_c.ml / sh_run_c.mli are BUILD ARTIFACTS: regenerated by the gate and
 * removed on cleanup, never edited by hand.  This is a THIRD, additive artifact;
 * it does not touch sh_run.ml or sh_run_iter.ml, so both existing gates stay
 * green.

 * Build (Rocq >= 9.0):
 *   coqc sh_concrete.v; coqc sh_jpl.v; coqc sh_jpl_run.v
 *   coqc sh_jpl_run_phase2.v; coqc sh_jpl_run_phase3.v; coqc sh_jpl_scan.v
 *   coqc sh_jpl_run_c.v
 *   coqc sh_extract_jpl_c.v      # writes sh_run_c.ml + sh_run_c.mli
 *)

From Stdlib Require Import Extraction.

(* Must precede the Extract Constant hooks below — see the TOOLCHAIN GOTCHA
   above.  ExtrOcamlNatInt itself pulls the same libraries, but importing it
   first leaves the hooks unbound. *)
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ExtrOcamlNatInt.

Require Import sh_concrete.          (* run, pure_phi, the scan helpers *)
Require Import sh_jpl.               (* bres / BOk / BLimit, the caps *)
Require Import sh_jpl_run.           (* step / cfg / out, pure_run_phi *)
Require Import sh_jpl_run_phase2.    (* cfg_budget / next — provenance only *)
Require Import sh_jpl_run_phase3.    (* dres / mrun — the closure-free driver *)
Require Import sh_jpl_scan.          (* getv_it / setv_it / *_iter tail loops *)
Require Import sh_jpl_run_c.         (* step_c / mrun_c — the REWIRED kernel *)

(* Emit beside this file so the gate's ocamlc finds them. *)
Set Extraction Output Directory ".".

(* Transparent stdlib arithmetic that would otherwise extract to recursion.
   `minus`/`mult`/`leb`/`Nat.eqb` are already hooked by ExtrOcamlNatInt; these
   four are not.  `Nat.divmod` is hooked too only to retire the recursive
   `divmod` that `Nat.div`/`Nat.modulo` are built from — with the other three
   hooks in place nothing calls it, but extraction still emits its body, and a
   `let rec` in the artifact is a JPL.6 lint failure waiting to happen. *)
Extract Constant Nat.div => "(Stdlib.( / ))".
Extract Constant Nat.modulo => "(Stdlib.(mod))".
Extract Constant Nat.divmod => "(fun x y _ _ -> (Stdlib.( / ) x y, Stdlib.(mod) x y))".
Extract Constant Nat.sub => "(fun x y -> Stdlib.max 0 (x - y))".
(* `Nat.max` is NOT hooked by ExtrOcamlNatInt: left alone it emits as a
   Peano-successor recursion inside the extracted `Nat` module, and the branch
   guard's `branch_need` calls it once per pattern.  Stdlib.max on the int
   representation is the same function, primitive and non-recursive. *)
Extract Constant Nat.max => "(Stdlib.max)".

Extraction "sh_run_c"
  mrun step dres cfg out run pure_run_phi expand glob expand_it
  getv_it setv_it be_getv be_setv glob_iter match_any_iter
  mrun_c step_c expand_c assign_c bind_word_o enter_for_c enter_case_c
  branch_guardb jpl_caps_table.
