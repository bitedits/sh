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
| L3 | Bounded data layer | `sh_jpl.v` | the C-legal representation + saturate-to-error | caps `cap_order` + `cap_fuel_order` (chain now ends at `MAX_FUEL` = 136 449 < 2³¹, the no-wrap bound); fuel caps amended 2026-10-04: `GLOB_FUEL` = L4's `fuel_top` at two full-width words (132 353, defined *derivationally* from `MAX_WORD` so it cannot drift), `MAX_FUEL` = `GLOB_FUEL` + 4096 (the machine threads one fuel through its countdown *and* its scans), gate accepts that budget — `b_fuel_accepts_glob_fuel`; `bres`/`bbind`/`b_fuel_ok`; `b_add/b_sub/b_mul/b_divmod` `_ok`/`_limit`; `wf_bword`/`mk_bword_wf`/`b_push_wf`/`b_app_wf`; `benv_setv_fits`/`setv_length_le`; `b_nstat_lt`; `cmd_count`/`cmd_fits`; §9 `iso_*` agreement with L2 |
| L4 | Iterative scans | `sh_jpl_scan.v` | kill the tree recursion the emitter cannot loop | `bt_nil_wf`, `bt_eq_refl` (`bt_eq = teqb`), `bt_append_full` saturation; `glob_it`/`glob_iter` + `match_any_iter` tail loops, **agreement with L2 proved both ways for arbitrary input** — soundness in §4.2 (`glob_it_sound` → `ok_it`, `glob_iter_sound` → declarative `gmatch`, `glob_iter_accepts_glob`, `match_any_iter_sound`) and completeness in §4.3 (`glob_it_complete` over the anchored invariant `cinv`, `glob_iter_complete_at` at the loop's own quadratic budget `fuel_top pat str = (P+S+1)*(S+1)+P+S`, two-sided `glob_iter_iff_glob`, two-sided `match_any_iter_iff_match_any`); §4.1's `reflexivity` cross-checks (`gi_matches_concrete_*`) remain as samples only; §4.3 also pins the budget gap by computation (§4.2.4: `*a`/`aaa` — L2 decides at 6, the loop needs 7, `fuel_top` = 29), and **§4.3.15 then adds the guard the *machine* needs and L4 could not state before: `branch_need pats w = max_i (|p_i| + |w| + i + 2)`, L2's exact site threshold, with `branch_decisive_need`/`branch_need_decisive` proving it necessary AND sufficient (so minimal, not convenient) and `branch_guardb`/`branch_guardb_match` the boolean the kernel evaluates; §4.3.14 turns that law into L3's constant**: `scan_mono`/`fuel_top_nat_mono` give monotonicity in each length, `fuel_top_le_glob_fuel` proves `lengths ≤ MAX_WORD ⇒ fuel_top ≤ GLOB_FUEL` with no numeral evaluated (the top case is definitional), and the machine-facing corollaries `glob_iter_glob_fuel_complete`, `glob_iter_max_fuel_complete` and `match_any_iter_in_budget` (call shape `GLOB_FUEL + length pats`) are what JPL.5-A.6 consumes; §4.2.2 also fixes L2 `glob`'s own budget: `glob_iff_gmatch` gives `glob f` ⟺ `gmatch` for `S (len pat + len str) <= f`, and `glob_fuel_mono` for fuel weakening; env tail loops `getv_it`/`setv_it` + array API `be_getv`/`be_setv` proved equal to L3 `benv_getv`/`benv_setv` (`be_getv_agree`/`be_setv_agree`), capacity law `be_setv_refuses_at_capacity`, write-then-read `be_getv_be_setv_same`. **§6 (JPL.5-A.7, 2026-10-04) adds the last one: the word expander.**  L2's `expand`/`expand_name`/`expand_brace` **mutual fixpoint** becomes ONE fuel-bounded tail loop `expand_go` over an explicit cell `ExpK { ek_mode; ek_inp; ek_out; ek_name }` (`expand_it` = its `EMain`/empty-accumulator entry), entered by writing the mode field instead of returning into another fixpoint, with the output accumulated REVERSED (one `rev` per expansion, not one per byte).  Agreement is `expand_go_correct` (the invariant `expand_go f m st (ExpK mode inp o nm) = rev o ++ expand_at m st f mode inp nm`, induction on fuel) and its corollary `expand_it_correct`, which carries **no hypothesis at all** — the loop mirrors L2's fuel decrements one for one, so unlike §4.3.13b/§4.3.15 there is no fuel-law gap, hence **no guard and no raised capacity constant**.  §6.4 pins the behaviour by computation over byte encodings (`text = list nat`): name, lone `$`, `${a}`, `$?`, unset and `{$a}` name brace forms, status 127, zero fuel, and **no re-scan of a substituted value**, plus four equalities against the reference at deliberately low fuel.  `getv` is called in its concrete form *deliberately* (it is already a forward tail scan; routing substitution through `getv_it` would add a parallel encoding of one scan without removing a recursion). **Consumption status (measured on the D5 artifact, 2026-10-04, after 5-A.7):** every scan L8 reaches the seam with is now one of §4/§5/§6's proved tail loops — `setv_it`, `match_any_iter` (+ the `glob_iter`/`glob_it` pair behind it) and `expand_go` are REACHED from `mrun_c`'s closure, and L2's `expand`/`expand_name`/`expand_brace` are gone from it. `getv_it` is reached only from its own extraction root `be_getv` (fuel = `be_len`, the length the bounded carrier already holds), i.e. **live in the artifact, unreachable from the machine** — the distinction `JPL.md` §9.1's 5-A.6 row blurred; see that doc's 5-A.7 row for the census and for the test that would retire `be_getv`/`getv_it` together |
| L5 | Small-step machine | `sh_jpl_run.v` | control flow as data, no closures in the loop | `step_cmd`/`step_ret`/`step`, `mloop`; meaning fold `frame_run`/`cont_run`/`cfg_run`/`out_run`; `step_preserves`; **soundness** `mrun_sound`, `mrun_correct`, `run_none_mloop_limit` |
| L6 | Liveness / completeness | `sh_jpl_run_phase2.v` | a step budget always exists | rank `cfg_budget`, `next_decrease`, `prec_wf`; **liveness** `mrun_live`; monotone `mloop_ok_monotone`; **two-sided** `mloop_iff`, `mloop_sound_complete` (= L5 `run ⇄ mloop`) |
| L7 | phi-as-DATA driver (JPL.5-A.4) | `sh_jpl_run_phase3.v` | no closure inside the kernel loop | `dres` (`DDone`/`DEff` data/`DLim`), `mrun B g` with **no `phi` argument**, `host phi B g`; boundaries `mrun_done_sound`/`mrun_eff_sound`; determinism `mrun_dres_monotone`/`host_monotone`; segment ranking `mrun_deff_budget`; **soundness** `host_sound`, **completeness** `host_live` (strong induction on `cfg_budget`), `host_iff_run` |
| L8 | Rewired machine (JPL.5-A.6 + 5-A.7) | `sh_jpl_run_c.v` | the kernel reaches the seam only through L4's PROVED tail loops | sites `expand_c` and the `enter_case_c` scrutinee on `expand_it` (L4 §6; word cap on the result, one expansion per site, read back into the reference-phrased statements by `exp_ref` = `repeat rewrite expand_it_correct`, **no guard needed**), `assign_c`/`bind_word_o` (`setv_it` scan), `enter_for_c`, `enter_case_c` = `branch_guardb` + `match_any_iter`; **headline `step_c_ok`** — `step_c g <> Olimit -> step_c g = step g`, CONDITIONAL by necessity (L2's `match_any` decides at the linear `branch_need`, L4's loop needs the quadratic `fuel_top`), and §6 exhibits a command the reference answers while `step_c` saturates, so no unconditional equality exists; driver transport `mrun_c_ok` (soundness, no hypothesis) and `host_c_bok_is_host_bok`; completeness only under `no_sat` (`host_c_agree`, `host_c_iff_run`); budgets proved **MINIMAL, not merely enough**: `guard_fuel_is_least` (`case_site_fuel` = 1537 is ATTAINED by an in-caps branch set ⇒ least uniform site fuel), `glob_fuel_is_tight`/`fuel_top_at_caps` (`GLOB_FUEL` is literally `fuel_top` at two full-width words), `case_allowance_inside_glob_fuel` (1537 + 1024 = 2561 ≤ GLOB_FUEL), `max_fuel_margin_eq_MAX_CMD` (`MAX_FUEL - GLOB_FUEL` is exactly `MAX_CMD`), `enter_case_c_chain_clear` (a whole branch chain saturates nowhere at ample fuel) |

L5+L6 together give the machine↔spec equivalence: `mloop φ B (CFG F ⌜c⌝ [] s) =
b_of (run φ F c s)` for all budgets past a witness — so the emitted `while`-driver
is *proved* to mean exactly the kernel-verified `run`.  L7 restates the same
equivalence for the driver that is actually emittable (`mrun` + host-side seam), so
the closure-free shape and the proven shape are the same shape.  L8 keeps that
equivalence but changes *what the driver calls*: every scan site goes through L4's
tail loops.  Because the two matchers disagree about fuel, L8's contract is
one-directional by design — soundness is unconditional (`mrun_c`/`host_c` never
disagree with L7 when they answer), completeness is carried by the single
hypothesis `no_sat` — and its budgets are proved least as well as sufficient, which
is what turns "the guard costs a comparison" from a claim into a theorem.

## Derived (never hand-written) artifacts

| Rung | From → To | Mechanism | Fidelity check |
|------|-----------|-----------|----------------|
| D1 | L2 → OCaml `run` | `sh_extract.v` (Coq `Extraction`) | `sh_run.ml` == `src/kernel/sh_run.ml` (anti-rot `diff -q`) |
| D2 | L5+L6 → OCaml `mloop` | `sh_extract_iter.v` (one module: `step`,`mloop`,`run`,…) | `sh_run_iter.ml` == `src/kernel/sh_run_iter.ml` (anti-rot) |
| D3 | derived OCaml == L2 literal | `sh_run_parity.ml`, `sh_run_iter_parity.ml` | **26 + 26** §7–§9 checks; per command `mloop == run == verified literal` |
| D4 | `src/kernel/*` → `ush` | `dune` lib `sh_kernel` (wrapped=false) | `dune build` green; L0 conformance via `verify/src/conformance.sh` |
| D5 | L4+L5+L6+L7+**L8** → int-native OCaml kernel, BOTH drivers | `sh_extract_jpl_c.v` (`ExtrOcamlNatInt` + `Nat.div`/`modulo`/`divmod`/`sub`/`max` hooks) → `sh_run_c.ml`/`.mli` | **66** checks in `sh_run_c_parity.ml`: the 15 §7–§9 facts re-run from ONE table through `mrun` *and* the rewired `mrun_c` with the same hand-written closure-free host (`host == literal == run` for each driver), + 8 tail-loop-vs-concrete checks of the emitted `sh_jpl_scan` loops, + `expand_it` against L2's `expand` — 5 point checks and two sweeps of 15 words × 9 fuels (135 comparisons each, **270 over both**), + the rewired surface itself (`expand_c` admits at `MAX_WORD`, saturates one byte over; `branch_guardb` at its thresholds and caps; the measured case the reference answers while `mrun_c` reports `DLim`). **Gate rung 2c since 2026-10-04** (one of the 15) and **vendored** at `src/kernel/sh_run_c.ml{,i}` on the user's instruction, so it is anti-rot `diff -q`-checked against a fresh extraction like D1/D2.  Caveat kept honest: `ush` does not consume this module — the vendored copy exists so the artifact JPL.5 lowers is the byte-for-byte one the gate verified, not because a shipped binary links it.  Its bytes are also the input of **D6** below, which reads them without translating them |
| D6 | D5's **vendored bytes** → the emitter's *input contract* | `verify/c/jpl_front.ml` (OCaml compiler-libs `Parse` + `Ast_iterator`), driven by `verify/c/jpl_front.sh` | **Not a translation — a reading.**  Computes the typed closure from the roots the C host calls (`mrun_c,step_c`), classifies every expression/pattern constructor it meets against JPL.5's *declared* subset, and exits non-zero on anything outside it; the inventory lives in `verify/c/closure.txt` and is byte-compared anti-rot like D1/D2/D5.  Measured: artifact **81** bindings / **76** signatures / **14** type declarations *(the artifact grew with **5-B.2a**, which exports the cap table as data: `closure.txt` and `layout.txt` now both read **87 / 81 / 15**, byte-compared)*; shipped closure **47** bindings / **17** recursive = 6 fuel-bounded tail loops + 2 print-only aliases + 9 length-bounded structural recursions — re-derived independently by a text identifier graph over the same bytes, which returns the **same 47 names and the same 17 recursive names, set-equal**, and corrects the **45** members `JPL.md` §9.1's 5-A.7 row recorded (its edge rule was narrower; the recursive split it reasoned from was right).  **Root-sensitive, and gate block 2d asserts both directions**: `mrun_c,step_c` ⇒ `SUBSET OK`; oracle roots `run,step,mrun` ⇒ `OFF-SUBSET mutual fixpoint: expand, expand_name, expand_brace, run, run_seq, run_for, run_case` + exit 1 — i.e. §9.2's decision 1 (which root JPL.6's Rule-6 lint binds) settled by measurement rather than asserted, and the gate refuses a lint that would accept every root.  Its TYPE VOCABULARY section is what corrected `JPL.md` §6: `cmd`/`frame`/`stack` are *recursive* value types (`Seq of cmd * cmd`, `Case of text * (text list * cmd list) list`, `stack = frame list`), so no inline fixed-capacity encoding exists at any setting of the caps — the C99 values must be handles into a static node pool, with `text` the one inline leaf.  **No new fidelity claim**: D6 binds the *shape* the emitter may read, not the behaviour of what it emits (that stays with the later rungs — D7 laid out the types, the emitted *behaviour* is D8's differential vectors, then JPL.6/JPL.7) |
| D7 | D5's **vendored bytes** → the C99 **type layer** (`verify/c/sh_run_jpl.h`) + its report (`verify/c/layout.txt`) | `verify/c/jpl_emit.ml` over the shared reader `verify/c/jpl_ast.ml`, driven by `verify/c/jpl_emit.sh` | **Representation, not behaviour.**  Applies `JPL.md` §6's rules R1–R8 to the same typed closure (roots `mrun_c,step_c`): 40 C types, 31 prototypes, 5 polymorphic bindings left **PENDING** rather than instantiated, 5 pools sized from the artifact's own `jpl_caps_table`, `text` as the one inline leaf and everything recursive as a handle into a pool.  Three fidelity checks, all in gate block **2e**: (i) the header compiles under `clang -std=c99 -Wall -Wextra -Wconversion -Wsign-conversion -pedantic -Werror -fsyntax-only`, and **34 `typedef char jpl_check_*[…]` array-bound assertions** make every emitted size and every cap relation a build failure if wrong (27 rows checked individually, 13 one-word typedefs covered conjunctively, 5 cap orders + the word width); (ii) a **differential** reading of the capacities — the emitter's syntactic fold of `jpl_caps_table` vs the OCaml runtime *evaluating* the same extracted term, nine-for-nine, then matched against the emitted `#define`s; (iii) anti-rot `diff -q` of both vendored evidence files.  Block **2e-negative** asserts root sensitivity: oracle roots ⇒ `FATAL: tn: a function-typed value has no layout` (`run`'s `run_phi` parameter), a *different* refusal than D6's mutual-fixpoint one.  What it measured and thereby corrected in §6: 5 polymorphic bindings need monomorphization, only `cmd` reaches itself, and **the word slab has no capacity in the LOCKED table** — `jpl_word_pool[]` is declared undimensioned, so D7's output is complete-but-unlinkable until the model adds `MAX_WORDS`.  The three non-derived layout choices are numbered in `JPL.md` §6.2 and printed by the report itself.  **No new behavioural claim**: no function body exists yet, so nothing here is evidence about the emitted kernel's correctness — that is D8/#26/#27 |

The `==` rungs D1/D2/D5 are byte-equality of a build artifact against its vendored
copy (kills rot); D3 is the one *empirical* Coq↔OCaml bridge (Extraction
faithfulness); D4/L0 is the POSIX-oracle bridge. Everything between L1 and L8 is
pure Coq with four `<none>`.

D5 is the same kind of bridge as D3, on the *iterative* side, and it is where the
extraction settings are pinned: `nat` becomes a machine `int` (`type text = int
list`), `mrun` emits as one tail loop with no functional argument, and Coq's nat
elimination emits as the value `(fun fO fS n -> if n=0 then fO () else fS (n-1))`,
which JPL.5 lowers to `if (n == 0)` and JPL.6 must not read as recursion.  Two
ordering facts are load-bearing there: `Arith`/`PeanoNat` must be required *before*
the `Extract Constant` hints or they are silently ignored, and `Nat.divmod` must be
hooked even though nothing calls it (unhooked, Extraction defines a genuinely
recursive `divmod`).

## Gate (`verify_models.sh`)

Current: **15/15** — eight Coq `coqc + coqchk` gates (L1–L8) + three extraction
blocks (D1–D3: recursive, iterative, and the JPL-settings clean kernel — each an
anti-rot `diff -q` against its vendored `src/kernel/` copy plus a parity run of
26 / 26 / 66 checks) + **block 2d (D6)**, the emitter front end: the typed closure over
the vendored bytes, and its **negative control**, which asserts the *oracle* roots are
refused (a subset check that accepts every root is not a gate) + **block 2e (D7)**, the
representation layer: emit, compile the header under the strict C99 flag set, diff the
folded capacities against the artifact *evaluated* by the OCaml runtime, and byte-compare
both vendored evidence files — with **2e-negative** asserting the layout tool refuses the
oracle roots because its driver is a function value.  2d and 2e need no Rocq
toolchain, so they run under `--skip-coq` as well; if `ocamlfind` /
`compiler-libs.common` is absent the rung is recorded **SKIP** and the summary prints
the skip count — a rung that silently vanishes would otherwise read as a pass.
`--skip-coq` / `--skip-extract` narrow the Coq side.  Cleanup deletes
every `.vo`, the `lia`/`nia` caches, the harness binaries and all derived
`.ml/.mli` (now including `sh_run_c.ml/.mli`), so the gate never leaves build
artifacts in the tree. `--help` prints the header comment by end-pattern rather
than a fixed line count, so adding a `Covers:` entry cannot silently truncate it.

## Status vs the JPL C99 goal

L1–L8 verify the *semantic* kernel axiom-free. The JPL-compliance plan for the
emitted C99 (representation budgets, no-recursion, saturate-to-error) lives in
`JPL.md`; the Coq layers above are what let its emitter (#25) and lint
gate (#26) run on a bounded, iterative, phi-as-data extraction.
