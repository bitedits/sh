# AXIOTACK — General Verification Architecture (the axiom stack)

Technical map of how the `sh` kernel is verified and where every trust
assumption lives. The governing rule (user-locked): **one hand-written truth,
everything else derived mechanically, and the Coq kernel never sees an axiom.**
`verify/models/verify_models.sh` is the executable form of this document — it is
green only if the whole stack below holds.

## The one invariant that ties it together

Every `.v` layer must pass `coqchk -o -silent` reporting **four `<none>` lines**
(Axioms / type-in-type / unsafe (co)fixpoints / assumed positivity). No `Axiom`,
`Parameter`, `Admitted`, or `admit` anywhere. The only non-Coq trust is at two
*empirical* boundaries (the `==` rungs marked below), each backed by a machine-
checked harness, never by a human claim.

## The stack, bottom-up

| # | Layer | File | What it fixes | Key results |
|---|-------|------|---------------|-------------|
| L0 | POSIX oracle | `/bin/sh` + `verify/src/conformance.sh` | ground-truth stdout | 33-case corpus diff (external) |
| L1 | Relational spec | `sh_properties.v` | what a shell *means*: `Inductive exec`, `Fixpoint run` | `exec_run`, `exec_deterministic`, `exec_preserves_wf`; boundary theorems `and_left_false_stops` … `while_roll`, `bang_inverts` |
| L2 | Concrete model (**single source of truth**) | `sh_concrete.v` | words=byte `text`, env, `expand`/`glob`/`match_any`, full `run phi f c s` | `teqb_*`, `getv_set_same`, `nstat_lt`, `ex_status_*`; §7 `and/or/seq/while/bang/if` lemmas; §8/§9 `expand_*`/`glob_*`/`case_*` Examples by `reflexivity` |
| L3 | Bounded data layer | `sh_jpl.v` | the C-legal representation + saturate-to-error | caps `cap_order`; `bres`/`bbind`/`b_fuel_ok`; `b_add/b_sub/b_mul/b_divmod` `_ok`/`_limit`; `wf_bword`/`mk_bword_wf`/`b_push_wf`/`b_app_wf`; `benv_setv_fits`/`setv_length_le`; `b_nstat_lt`; `cmd_count`/`cmd_fits`; §9 `iso_*` agreement with L2 |
| L4 | Iterative scans | `sh_jpl_scan.v` | kill the tree recursion the emitter cannot loop | `bt_nil_wf`, `bt_eq_refl` (`bt_eq = teqb`), `bt_append_full` saturation; `glob_it`/`glob_iter` + `match_any_iter` tail loops, cross-checked vs L2 `glob`/`match_any` by `reflexivity` (`gi_matches_concrete_*`) |
| L5 | Small-step machine | `sh_jpl_run.v` | control flow as data, no closures in the loop | `step_cmd`/`step_ret`/`step`, `mloop`; meaning fold `frame_run`/`cont_run`/`cfg_run`/`out_run`; `step_preserves`; **soundness** `mrun_sound`, `mrun_correct`, `run_none_mloop_limit` |
| L6 | Liveness / completeness | `sh_jpl_run_phase2.v` | a step budget always exists | rank `cfg_budget`, `next_decrease`, `prec_wf`; **liveness** `mrun_live`; monotone `mloop_ok_monotone`; **two-sided** `mloop_iff`, `mloop_sound_complete` (= L5 `run ⇄ mloop`) |

L5+L6 together give the machine↔spec equivalence: `mloop φ B (CFG F ⌜c⌝ [] s) =
b_of (run φ F c s)` for all budgets past a witness — so the emitted `while`-driver
is *proved* to mean exactly the kernel-verified `run`.

## Derived (never hand-written) artifacts

| Rung | From → To | Mechanism | Fidelity check |
|------|-----------|-----------|----------------|
| D1 | L2 → OCaml `run` | `sh_extract.v` (Coq `Extraction`) | `sh_run.ml` == `src/kernel/sh_run.ml` (anti-rot `diff -q`) |
| D2 | L5+L6 → OCaml `mloop` | `sh_extract_iter.v` (one module: `step`,`mloop`,`run`,…) | `sh_run_iter.ml` == `src/kernel/sh_run_iter.ml` (anti-rot) |
| D3 | derived OCaml == L2 literal | `sh_run_parity.ml`, `sh_run_iter_parity.ml` | **26 + 26** §7–§9 checks; per command `mloop == run == verified literal` |
| D4 | `src/kernel/*` → `ush` | `dune` lib `sh_kernel` (wrapped=false) | `dune build` green; L0 conformance via `verify/src/conformance.sh` |

The `==` rungs D1/D2 are byte-equality of a build artifact against its vendored
copy (kills rot); D3 is the one *empirical* Coq↔OCaml bridge (Extraction
faithfulness); D4/L0 is the POSIX-oracle bridge. Everything between L1 and L6 is
pure Coq with four `<none>`.

## Gate (`verify_models.sh`)

Current: **8/8** — six Coq `coqc + coqchk` gates (L1–L6) + two extraction blocks
(D1–D3 recursive and iterative, each with anti-rot diff + 26 parity). `--skip-coq`
/ `--skip-extract` narrow it; cleanup deletes all `.vo` + derived `.ml/.mli` so the
gate never leaves build artifacts in the tree.

## Status vs the JPL C99 goal

L1–L6 verify the *semantic* kernel axiom-free. The JPL-compliance plan for the
emitted C99 (representation budgets, no-recursion, saturate-to-error) lives in
`JPL.md`; the Coq layers above are what let its emitter (#25) and lint
gate (#26) run on a bounded, iterative, phi-as-data extraction.
