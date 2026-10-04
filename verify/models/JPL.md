# JPL-Compliant C99 Extraction — Design Specification

**Scope.** Governing design reference for Phase 3d-C: produce a C99 kernel whose
emitted form satisfies the **JPL D-60411 *shall* rules (LOC-1…LOC-4)**, while keeping
every *semantic* transform inside the verified Coq model. The Introduction motivates
the NASA JPL standard and its Levels-of-Compliance structure; Sections 1–9 state the
standing design (principles, compliance contract, bounded representation, machine
architecture, extraction contract, verification strategy, construction order). Dated
decisions, build milestones, and live validation probes are quarantined under
[HISTORY — development record and hints](#history--development-record-and-hints).
The language-agnostic verification stack (axiom layers L0–L6, derived rungs D1–D4)
is documented separately in `AXIOTACK.md`; this file governs only the C99-targeted
re-architecture that sits on top of it.

## Table of contents

- [Introduction](#introduction) — motivation and structure of the NASA JPL standard
- [1. Problem: why re-architecture (not direct emit)](#1-problem-why-re-architecture-not-direct-emit)
- [2. Design principles (invariants)](#2-design-principles-invariants)
- [3. D-60411 compliance contract — how each *shall* rule is supported](#3-d-60411-compliance-contract--how-each-shall-rule-is-supported-file--theorem)
- [4. Bounded representation (the budget)](#4-bounded-representation-the-budget)
  - [4.1 Capacity constants](#41-capacity-constants)
  - [4.2 Overflow / bound-exhaustion policy](#42-overflow--bound-exhaustion-policy--saturate-to-error)
- [5. Recursion elimination — the small-step machine](#5-recursion-elimination--the-small-step-machine)
- [6. Extraction contract](#6-extraction-contract)
  - [6.1 Established extraction behaviour](#61-established-extraction-behaviour)
- [7. Verification: JPL lint gate (design)](#7-verification-jpl-lint-gate-design)
- [8. Verification: differential gate (design)](#8-verification-differential-gate-design)
- [9. Construction order (matches task list)](#9-construction-order-matches-task-list)
  - [9.1 Build order (No · Description · Files)](#91-build-order-no--description--files)
  - [9.2 Stage accounting](#92-stage-accounting)
- [HISTORY — development record and hints](#history--development-record-and-hints)

## Introduction

*The NASA JPL C standard — its motivation, structure, and the rule set we target.*

**In one line.** D-60411 organises C rules into **six Levels of Compliance**
(LOC-1…LOC-6, 120 rules cumulative, of which 31 are self-contained JPL-authored at
LOC-1…4); this project targets the kernel-critical **Rules 1–10**, treating every
*shall* at LOC-1…4 as **Mandatory** and elevating two *should* rules (R6 effects-as-
data, R17 fixed-width types) to Mandatory as well.

**Authoritative source (cited, not reproduced).** This project targets the
**JPL Institutional Coding Standard for the C Programming Language**, JPL DocID
**D-60411**, Version 1.0 (dated 2009-03-03; the externally-distributed revision
2009-03-04, clearance CL#09-0763), Jet Propulsion Laboratory, California Institute
of Technology — © 2009 Caltech, U.S. Government sponsorship acknowledged. The
external edition omits third-party text (the MISRA-C:2004 rules of LOC-5/LOC-6 and
the ISO Appendix A), so the self-contained JPL-authored rules are **Rules 1–31 at
LOC-1…LOC-4**. Everything below is a *paraphrase with citation* — rule numbers and
short summaries in our own words — not a reproduction of the standard's text.

**Motivation.** D-60411 consolidates two earlier efforts — **MISRA-C:2004** and the
**"Power of Ten" rules** (IEEE Computer, June 2006, pp. 93–95) — into a single
institutional standard, and adds coverage for multi-threaded-software risks that
neither addressed. Its scope is *mission-critical flight software* on embedded
targets under strict resource constraints. The driving facts are exactly the ones
that make a mechanically-verified extraction attractive: flight code is effectively
**immutable after launch**, and many C constructs are **undefined,
implementation-defined, or silently lossy**, letting defects hide until flight.

**Structure: Levels of Compliance (LOC).** The standard defines six separately
certifiable levels; full compliance for newly-written code is expected at least
through LOC-4.

| LOC | Segment | Rules at level | Cumulative |
|---|---|---|---|
| LOC-1 | Language Compliance | 2 | 2 |
| LOC-2 | Predictable Execution | 10 | 12 |
| LOC-3 | Defensive Coding | 7 | 19 |
| LOC-4 | Code Clarity | 12 | 31 |
| LOC-5 | MISRA-C:2004 *shall* rules | 73 | 104 |
| LOC-6 | MISRA-C:2004 *should* rules | 16 | 120 |

**Convention: *shall* vs *should*.** *Shall* = a requirement that must be followed,
with compliance verified; *should* = a preference that must be addressed but admits
justified deviation. At LOC-1…4 every rule is a *shall* except a small asterisked
minority (e.g. Rule 17 fixed-width types, Rules 24–30). **Our "mandatory" target =
the *shall* rules at LOC-1…LOC-4**; we additionally honour the *should* rules where
they cost nothing.

**The rule set we target (Rules 1–10, paraphrased).** These kernel-critical rules
are what the Coq/emitter design is built to satisfy; §3 maps each to the Coq theorem
that proves it and the mechanism that emits it.

The **Verb** column is D-60411's own *shall*/*should*. The **Our tier** column is the
enforcement class this project actually applies, expressed in the legacy
*mandatory / apocryphal / advisory* (M/A/A) vocabulary of the superseded 2001 JPL
PowerPC scheme — kept here precisely to expose where our tier **misaligns** with
D-60411's verb:

| # | Rule (D-60411, paraphrased) | Verb | Our tier | Our design hook |
|---|---|---|---|---|
| 1 | Conform to ISO C; no reliance on undefined/unspecified behaviour | *shall* | **Mandatory** | pure Coq model; saturate-to-error carrier `bres` (§3, §4.2) |
| 2 | Compile with all warnings at the highest level + a static analyzer, zero diagnostics | *shall* | **Mandatory** | `clang -std=c99 -Wall -Wextra -Wconversion -Werror` in the lint gate (#26) |
| 3 | Every terminating loop has a statically determinable upper bound | *shall* | **Mandatory** | `b_fuel`/`MAX_FUEL`; `cfg_budget`/`mrun_live` termination (§3) |
| 4 | No direct or indirect recursion | *shall* | **Mandatory** | `mloop` tail driver; `glob_it`/`match_any_iter` (§3) |
| 5 | No dynamic memory allocation after task init (no `malloc`/`sbrk`/`alloca`) | *shall* | **Mandatory** | static pools; `wf_bword`/`wf_benv` length bounds (§3) |
| 6 | Prefer IPC messages; avoid callbacks; don't run another task's code | *should* | **Mandatory ▲** | `phi` seam returns effects as **data**, host re-enters (#32) |
| 7 | No task synchronisation via task delays | *shall* | **Advisory · N/A** | n/a — the kernel is single-threaded (linear discipline) |
| 8 | Shared data has a single owning task; ownership passed explicitly | *should* | **Advisory · N/A** | state is threaded functionally (`cstate`), no shared mutable globals |
| 9 | Avoid semaphores/locks; if used, one documented order | *should* | **Advisory · N/A** | n/a — no concurrency in the kernel |
| 10 | Use memory protection / safety margins / barrier patterns to catch violations | *shall* | **Mandatory** | length-carrying bounded arrays + `wf_*` predicates = in-software bounds checks |

**Crosswalk (M/A/A ↔ D-60411).** *mandatory* ≈ a D-60411 *shall* we enforce;
*advisory* ≈ a D-60411 *should*, or a *shall* whose subject matter does not occur in
this single-threaded, allocation-free kernel (marked **Advisory · N/A** — R7/R8/R9:
task synchronisation, shared-data ownership, and locks have no analogue);
*apocryphal* ≈ a legacy style rule we deliberately do **not** enforce. **▲ (elevated)**
marks the two rules we treat as stricter than D-60411 requires: **R6** (callbacks /
effects-as-data) and **R17** (fixed-width, unsigned-only types) are D-60411 *should*
but are **Mandatory** for us, because a function-pointer seam or a
narrow/signed/arithmetic-promoted type would break the extraction and the JPL lint
gate outright. Likewise the *no-float / no-char-or-short-arithmetic* constraint is
imported from MISRA (LOC-5) and the old mandatory set, not from a D-60411
LOC-1…4 *shall*. We reproduce **none** of the 2001 document's per-rule text or its
exact rule-by-rule classifications — they are cited only; the M/A/A labels above are
**our** enforcement tiers, not quotations from either standard.

Rules 11 (no `goto`/`setjmp`/`longjmp`) and 12 (no partial `enum` initialisation)
complete LOC-2; Rules 13–19 (Defensive Coding) and 20–31 (Code Clarity) complete
LOC-3/LOC-4. The constructs most relevant to the emitted C among those — fixed-width
types (17), explicit evaluation order (18), no side-effect expressions (19), no
non-constant function pointers (29), limited preprocessor (20–23) — are cited
against the matching rows of §3.

**Predecessor & references.** D-60411 v1.0 (2009) is the current published
institutional standard and supersedes the earlier JPL *PowerPC C Coding Standards*
(2001 — the "44-rule *mandatory / apocryphal / advisory*" scheme some of our older
notes still echo). This document now uses D-60411's Levels of Compliance and
*shall*/*should* verbs throughout; "mandatory" is used only as a synonym for a
D-60411 *shall* rule. Primary sources, as cited by D-60411:

- JPL, *JPL Institutional Coding Standard for the C Programming Language*,
  JPL DocID **D-60411**, Ver. 1.0, 2009-03-03 (external revision 2009-03-04,
  clearance CL#09-0763); Jet Propulsion Laboratory, California Institute of
  Technology. © 2009 Caltech, U.S. Government sponsorship acknowledged.
- MISRA, *MISRA-C:2004 — Guidelines for the Use of the C Language in Critical
  Systems*, Motor Industry Software Reliability Association, October 2004.
- Hennessy/Goldberg et al. lineage, *The Power of Ten — Rules for Developing Safety
  Critical Code*, IEEE Computer, June 2006, pp. 93–95.
- ISO/IEC 9899:1999(E), *Programming Languages — C* (C99).

Rule numbers and one-line summaries above are paraphrased for reference; the
authoritative wording is in D-60411 (and, for LOC-5/6, in MISRA-C:2004).

## 1. Problem: why re-architecture (not direct emit)

The current single source of truth, `verify/models/sh_concrete.v`, extracts (via
Coq Extraction) to OCaml (`src/kernel/sh_run.ml`) that is **fuel-bounded
recursion over heap lists** (Peano `nat`, `text = nat list`, `cmd` tree,
higher-order `obind` callbacks). A literal OCaml->C99 emit would therefore use
`malloc`, recursion, boxed unary naturals, and function pointers — each of which
breaks a JPL D-60411 *shall* rule (Rules 3–5).

Two commitments define the approach:
- Transforms that make the C JPL-clean live **in the Coq source**, not the
  emitter: re-aim the model to **iteration over bounded array structures**, then
  run a **simple, narrow** OCaml->C99 emitter.
- Target the **JPL D-60411 *shall* rules at LOC-1…LOC-4**, enforced mechanically by
  a lint gate over the emitted C.

## 2. Design principles (invariants)

1. **Transforms live in the Coq source, not the emitter.** Any rewrite that makes
   the C JPL-clean — iteration over recursion, bounded arrays over heap lists,
   effects as data over callbacks — is performed and *proved* in Coq. The emitter
   keeps exactly one mechanical duty: the **layout** mapping (bounded `list` →
   static array + length, `nat` → `uint32`), justified by the Coq `wf_bword`/`wf_benv`
   well-formedness bounds. Layout is representation, not semantics.
2. **Axiom-free throughout.** Every new Coq file must satisfy
   `coqchk -o -silent` four `<none>` lines. No `Axiom`/`Parameter`/`Admitted`.
3. **Behavioral isomorphism.** The new iterative kernel must reproduce the
   observable results of `sh_concrete.run` (same status/env outcomes) so the 26
   extraction-fidelity parity checks stay green when re-pointed at it.
4. **Keep existing gates green while building alongside.** Do not edit
   `sh_concrete.v` or `src/kernel/sh_run.ml` destructively. New files first;
   migrate ush + vendored kernel only after parity + conformance pass.  Adding a
   *block* to `verify_models.sh` is allowed and expected — the gate is the executable
   form of this plan, so a new artifact is not done until the gate checks it
   (2026-10-04: block 2c added on the user's approval; every existing block still has
   to stay green, which is what invariant 4 really guards).
5. **Saturate-to-error over wraparound.** A bound breach returns a defined
   `LIMIT_EXHAUSTED` status (the analogue of the model's `fuel = 0 -> None`), never
   silent wraparound — truncation must be observable, not hidden.

## 3. D-60411 compliance contract — how each *shall* rule is supported (file · theorem)

We target the **JPL D-60411 *shall* rules at LOC-1…LOC-4** (the self-contained
JPL-authored set; the Introduction cites the source and maps Rules 1–10). Compliance
is a two-sided contract: the **Coq source** proves the *semantic* precondition (the
program is bounded / non-recursive / effect-is-data), and the **emitter (#25) +
lint gate (#26)** enforce the *syntactic* form of the emitted C. The full general
verification stack is in `AXIOTACK.md`; per-rule support is below (D-60411 rule
numbers in the first column).

| D-60411 rule | Coq precondition (file · theorem) | Realized by |
|---|---|---|
| **R5** no dynamic allocation (static objects only) | every store is length-carrying + capped: `sh_jpl.v` `wf_bword`/`mk_bword_wf`/`b_push_wf`/`b_app_wf`, `wf_benv`/`benv_setv_fits`/`setv_length_le`; pool gate `cmd_count`/`cmd_fits` | emitter maps bounded `int list`→static array + len; no `malloc` |
| **R4** no recursion (direct or indirect); iteration only | control flow is a tail driver: `sh_jpl_run.v` `mloop` (single `step` per tick), and every scan the shipped kernel reaches is a fuel-indexed tail loop: `sh_jpl_scan.v` §4 `glob_it`/`match_any_iter` replace `sh_concrete.glob`/`match_any`'s tree recursion, §5 `setv_it`/`getv_it` replace the env scans, §6 `expand_go`/`expand_it` (5-A.7) replace `expand`/`expand_name`/`expand_brace`'s **mutual** fixpoint with one loop and agree with the reference at **every** fuel with no hypothesis; `nat`→`int` via `ExtrOcamlNatInt` (kills `add`/`sub`/`divmod` fixpoints) | emitter lowers tail `let rec`→`while` and, per §6.1, the **residual** `mrun_c` recursions (9, all length-bounded by `MAX_WORD`/`MAX_LIST`: `app`, `length`, `forallb`, `branch_need`, `rev`, `rev_append`, `teqb`, `getv`, `nat_digits`)→bounded copy loops; `Extract Constant Nat.div/mod/sub/max`→primitive ops (#33, #35) |
| **R17** fixed-width types (unsigned here) | `sh_jpl.v` §3 `b_add`/`b_sub`/`b_mul`/`b_divmod` + `cap_order`/`cap_fuel_order` (the chain now ends at `MAX_FUEL` = 136 449 < 2³¹, so no bounded value can wrap the word) | `uint32_t`; `-Wconversion`-clean casts (emitter) |
| **R1** no undefined/unspecified behaviour; explicit error on breach | saturate-to-error carrier `bres`/`bbind`; `sh_jpl.v` `b_add_limit`/`b_divmod_limit` (div-by-0 ⇒ `BLimit`, not UB); `sh_jpl_scan.v` `bt_append_full` | `BLimit` ⇒ defined `LIMIT_EXHAUSTED` return (matches fuel→`None`) |
| **R3** statically-bounded loop iterations | fuel budget `b_fuel`/`b_fuel_ok` (`≤ MAX_FUEL`); the scans are fuel-indexed `Fixpoint`s with a *proved* budget of their own (`sh_jpl_scan.v` §4.3.9 `fuel_top` for `glob_it`/`match_any_iter`), and since 2026-10-04 that budget has its own constant: `GLOB_FUEL` = `fuel_top` at two full-width words (132 353), sized by the proved `fuel_top_le_glob_fuel` (§4.3.14), with `MAX_FUEL = GLOB_FUEL + 4096` so the machine's single fuel covers the deepest scan plus its step allowance (`b_fuel_accepts_glob_fuel`, `glob_iter_max_fuel_complete`); machine step budget `sh_jpl_run_phase2.v` `cfg_budget`/`next_decrease`/`prec_wf` ⇒ every run terminates (`mrun_live`) | `while` with a decremented counter, no unbounded loop |
| **R17** (+ MISRA LOC-5) no float; no `char`/`short` arithmetic | model has no floats; bytes are `nat` codes (`sh_concrete.v` §1 `text = list nat`) | byte values stay `uint32_t` end to end (emitter) |
| **R6/R29** effects as data, not function pointers | `phi` seam emits `Oeffect idx argv k s` as a value (`sh_jpl_run.v` `out`); phi-as-data driver is #32 (`mloop` drops the `phi` function arg) | no closures/callbacks in emitted C (host re-enters on the data effect) |
| **R11** (+ style) no `goto`; single entry/exit; exhaustive `switch` (no `default`), init-all-locals | nothing in Coq (syntactic only) | emitter codegen (#25) + `verify/c/jpl_lint.sh` grep/clang audit (#26) |

Semantic soundness of the iterative driver itself (so the above is *proved* to
agree with the spec, not just shaped right): `sh_jpl_run.v` `step_preserves` +
`mrun_sound` (⊢), `sh_jpl_run_phase2.v` `mrun_live` + `mloop_iff` /
`mloop_sound_complete` (⇐ and the two-sided `run ⇄ mloop`).

## 4. Bounded representation (the budget)

`nat` (byte codes 0..255, fuel, status 0..255) maps to a fixed-width **unsigned**
machine type. All arithmetic is unsigned with an explicit bound discipline; within
the caps below, unsigned arithmetic is a bijection with Peano, so parity with the
OCaml kernel is preserved.

### 4.1 Capacity constants

| constant | value | bounds |
|---|---|---|
| `MAX_WIDTH` (nat word bits) | 32 | uint32_t; byte<=255, fuel<=136 449 (= `MAX_FUEL`), status<=255 all fit |
| `MAX_WORD` | 256 | expanded word / text length in bytes |
| `MAX_ARGV` | 64 | argument words per simple command |
| `MAX_ENV` | 128 | simultaneously live shell variables |
| `MAX_LIST` | 1024 | any intermediate list length (cmd-list bodies, word lists, case branches) |
| `MAX_CMD` | 4096 | node pool capacity for one lowered program's `cmd` tree |
| `MAX_STACK` | 8192 | explicit machine stack frames (= 2·`MAX_CMD`, one frame per live continuation of a node-pool-sized program; a cap on nesting, independent of the fuel cap) |
| `GLOB_FUEL` | 132 353 | **one glob/branch scan's own budget**, added 2026-10-04. Defined *derivationally*, not as a literal: `S (MAX_WORD + MAX_WORD) * S MAX_WORD + MAX_WORD + MAX_WORD`, i.e. `sh_jpl_scan.v` §4.3.9's `fuel_top` evaluated at two full-width words. §4.3.14's `fuel_top_le_glob_fuel` proves it covers the law for every in-budget pair of words; because the definition and the law share one expression, it cannot drift if `MAX_WORD` changes |
| `MAX_FUEL` | 136 449 | loop-iteration bound the machine may be handed (`b_fuel` refuses above it). Was the flat 4096 that matched ush's budget; now `GLOB_FUEL + 4096` — the deepest scan's proved budget plus the machine's own 4096-step allowance, because `step` hands ONE fuel both to its countdown and to the scans it calls |
| `case_site_fuel` | 1537 | **the branch guard's threshold**, added with 5-A.6 (`sh_jpl_run_c.v` §5). `S (MAX_LIST + MAX_WORD + MAX_WORD)`: L2's `match_any g pats w` globs pattern *i* at fuel `g-1-i`, so its worst in-caps branch needs exactly this much site fuel. **Proved least, not merely enough** — `branch_need_worst_case` exhibits a branch that ATTAINS it (`branch_need (rep MAX_LIST p) w = case_site_fuel`), so no smaller uniform site threshold decides every in-caps branch, and `guard_fuel_is_least` states that minimality for the guard itself |

Ordering is proved in two pieces: `cap_order` chains `MAX_WIDTH ≤ MAX_WORD`,
`MAX_ARGV ≤ MAX_ENV ≤ MAX_LIST ≤ MAX_CMD ≤ MAX_STACK`, and `cap_fuel_order` adds
`MAX_STACK ≤ GLOB_FUEL ≤ MAX_FUEL`. So the largest cap is `MAX_FUEL` = 136 449,
still three orders of magnitude inside a `uint32_t` (and inside `int32_t`), which
is what the no-wrap argument in §3/R17 rests on. Note the direction flip this
introduces: fuel is no longer below the frame cap — frames bound *nesting*, fuel
bounds *iterations*, and nothing in the tree requires one to dominate the other
(measured: no lemma or call site depends on `MAX_FUEL ≤ MAX_STACK`).

**The cap table is DATA the emitted C reads, so the artifact has to carry it
(sub-step 5-B.2a, 2026-10-04).**  §6's layout allocates against all nine constants
above, but Coq's extraction carries a constant only if the *kernel code mentions it*:
`MAX_WORD`, `MAX_ENV`, `MAX_LIST`, `GLOB_FUEL` and `MAX_FUEL` reach `sh_run_c.ml`
because a guard compares against them, while `MAX_WIDTH`, `MAX_ARGV`, `MAX_CMD` and
`MAX_STACK` appear in proofs only and would simply vanish from the artifact.  An
emitter that hard-coded the four missing numbers would hold a second, unchecked copy
of a LOCKED table — the same parallel-encoding failure that retired `sh_model.ml`.
`sh_jpl.v` §1.1 therefore re-exports the whole table as one extracted value,
`jpl_caps_table : jpl_caps`, and `jpl_caps_are_locked` re-proves every field against
its §1 literal, so a cap that drifts breaks the model build instead of silently
resizing a pool.  Two fields are *derived* rather than copied, both because a unary
`nat` literal extracts to one `Int.succ` per unit (4096 lines for `MAX_CMD`) and
because the derivation is itself the justification §4.1 already states:
`jpl_cmd := MAX_FUEL − GLOB_FUEL` is `max_fuel_margin_eq_MAX_CMD` turned into data,
and `jpl_stack := 2 · jpl_cmd` is this table's "= 2·`MAX_CMD`" note turned into a
definition.  `case_site_fuel` is deliberately **not** in the table: it is a
proof-side threshold, not something the C allocates against.  Strength: the
field-by-field equalities are **proved** in `sh_jpl.v`; that the artifact carries
them is **measured** by gate 2c's byte-identical re-extraction plus 2d's inventory.

**Three of these constants are now proved to be *tight*, which is a stronger claim
than "the budget suffices" and is what §4.2's saturate-to-error policy rests on:**

| result | content |
|---|---|
| `glob_fuel_is_tight` / `fuel_top_at_caps` (`sh_jpl_scan.v` §4.3.14) | `GLOB_FUEL` is *literally* `fuel_top MAX_WORD MAX_WORD`, the loop's own quadratic law evaluated at the two caps it must cover — so it is the least single budget for full-width words, and cannot drift from the law because definition and law are one expression |
| `branch_need_worst_case` / `guard_fuel_is_least` (`sh_jpl_run_c.v` §5.1–5.2) | 1537 is attained by a worst-shaped branch, hence least |
| `max_fuel_margin_eq_MAX_CMD` (`sh_jpl_run_c.v` §5.4) | `MAX_FUEL − GLOB_FUEL = MAX_CMD = 4096` exactly, i.e. the allowance above the deepest scan is the machine's own step bound and nothing more |

The two spending facts that make those constants usable from a machine:
`case_allowance_inside_glob_fuel` (guard threshold + a full pattern list, 2561,
still ≤ `GLOB_FUEL`) and `branch_chain_funded` (`GLOB_FUEL + MAX_LIST ≤ MAX_FUEL`) —
`enter_case_c_chain_clear` then proves the whole branch chain saturates *nowhere* at
ample fuel, so the guard costs nothing at the caps this layer carries.

**No constant moved for 5-A.7**, and that is the result worth stating: the expander
loop consumes exactly the fuel the reference consumes, so `expand_it` runs at the site
fuel `step_c` already hands out.  It is the first scan-side stage whose landing changed
no budget — 5-A.6 needed `GLOB_FUEL` and a raised `MAX_FUEL` because its loop's law
differed from the reference's, and 5-A.7's does not.

### 4.2 Overflow / bound-exhaustion policy — saturate-to-error

When an operation would exceed a cap, it returns a defined `LIMIT_EXHAUSTED`
status (the analogue of the model's fuel=0 -> `None`), surfaced to the host as a
hard failure — never silent wraparound. This keeps the "no undefined behaviour"
and "explicit error return" JPL spirit and matches the existing truncation
semantics. The carrier is `bres A = BOk A | BLimit`, threaded through every bounded
operation. The rejected alternative — modular wraparound — is simpler but can mask
truncation and diverge from the verified model on out-of-budget inputs.

## 5. Recursion elimination — the small-step machine

The executor becomes a `step` function, tail-recursive over an explicit bounded
stack (arrays, not a linked structure), iterated `fuel` times:

- `run` currently recurses via `obind (run .. c1 s) (run .. c2)` etc. Restate as a
  machine: `(control_stack, current_cmd, cstate)`; `step` pops/pushes bounded
  frames; the `phi` OS-effect seam is returned as a `Leaf` outcome the host
  services between steps (not a callback — function pointers with captured
  environments are JPL-hostile).
- `expand`/`glob`/`match_any` are re-expressed as accumulator/tail loops over the
  bounded store (single loop index, no self recursion).  Delivered: `expand`
  (`expand_go`/`expand_it`, 5-A.7 — the three L2 fixpoints become ONE loop over a
  `(mode, input, reversed output, reversed name)` cell, a mode switch being a write of
  the mode field), `glob` (its
  backtracking keeps one explicit `(pat, str)` resume cell — `bk` — rather than the
  dedicated backtrack stack this section first sketched; `MAX_STACK` bounds the
  machine's continuation frames, not glob) and `match_any` (`glob_it`/
  `glob_iter`/`match_any_iter`, 5-A.3), and the env scans `getv`/`setv` with the
  reversed-prefix accumulator `acc` (`getv_it`/`setv_it`, 5-A.2).  **Wired into the
  machine by 5-A.6** (`sh_jpl_run_c.v`, `step_c`/`mrun_c`/`host_c`): `setv_it`
  replaces `setv` at all three write sites, `match_any_iter` replaces the `match_any`
  tree at the `case` site, and `glob_it` reaches the artifact *through*
  `match_any_iter`; **5-A.7** then replaced the mutual expander at both of its sites
  (`expand_c`/`bind_word_o` and the `enter_case_c` scrutinee).  That rewiring is not a drop-in, because the two matchers have
  **different fuel laws** — L2 decides a branch at the linear `branch_need` threshold,
  the loop needs the quadratic `fuel_top` — so below `fuel_top` the loop answers
  `false` where L2 already answers `true` (`tree_decides_below_loop_need` measures the
  band: pattern `[*;a]` on `a-a-a`, L2 decisive at site fuel 6, loop needs 29).  The
  machine therefore *guards* each `case` site with one decidable boolean
  (`branch_guardb`: `branch_need ≤ site fuel` plus the three word/list caps) and reads
  a failed guard as the same saturate-to-error edge as exhausted fuel.  Consequence for
  the contract this section states: the machine's headline is the **conditional**
  `step_c_ok : step_c g <> Olimit -> step_c g = step g`, and §6 proves an
  *unconditional* equality is impossible (`host_c_saturates_where_host_answers` gives
  the command the reference answers at fuel 8 and the rewired kernel reports `BLimit`).
  Soundness stays unconditional (`mrun_c_ok`, `host_c_sound` — a value cannot have
  passed through a fired guard); completeness is transported under one hypothesis,
  `no_sat`.  The expander needed **neither** of those devices: 5-A.7's loop mirrors
  L2's fuel decrements one for one, so `expand_it_correct` holds at EVERY fuel with no
  hypothesis, no guard and no raised budget — the fuel-law mismatch that forced the
  `case` guard simply does not arise when the loop copies the reference's own steps.
  What is still deferred to the JPL.5 emitter is the class §6.1's first bullet already
  assigns to it: the bounded *structural* recursions the loops and the guard call —
  `teqb`, `nat_digits`, `branch_need`, `forallb`, `length`, `app`, `rev`/`rev_append` —
  every one of them length-bounded by `MAX_LIST`/`MAX_WORD`, so each becomes a bounded
  `for`/copy rather than a scan.  And `getv`, which `expand_go` calls *on purpose*:
  L2's `getv` is already a forward tail scan, so routing the substitution through
  `getv_it` would add a second encoding of the same scan instead of removing a
  recursion.  `getv_it`'s consumer is `be_getv` — the bounded-`benv` read that takes
  its fuel from `be_len`, the length the carrier already holds — which is a root of the
  extraction surface and is what makes it live in the artifact but unreachable from
  `mrun_c`; see §9.1's 5-A.7 row.
- Coq termination: measures on the (decreasing) fuel/index; still `Fixpoint`, but
  extraction yields a tail-recursive OCaml function -> a C `while`/`for`.

## 6. Extraction contract

Coq (iterative, array-based, bounded) --Extraction--> OCaml (tail loops + bounded
lists) --simple emitter--> C99. The emitter only has to handle: tail
`let rec ... acc` -> `for`/`while`; `uint32` nat; bounded sequences;
tagged-struct `cmd`; records->structs; `match`->`switch` (exhaustive, no default);
`option`/result -> a struct `{ ok; val }` or an out-param + status.
~~No monomorphization~~ is **refuted by 5-B.2's measurement**: five of the shipped
closure's bindings are polymorphic as extracted — `length`, `app`, `rev`,
`rev_append`, `forallb` — and each is reached by several call sites at *different*
element types (2–6 callers, counted in `verify/c/layout.txt`), so JPL.5-B.3 must
emit one C instance per instantiated type it meets.  What is true is *closure
conversion is not needed*: the `phi` seam is data (5-A.4), and there is no GC —
static pools only, sized as below.

**"fixed arrays + a length field" was this section's original phrasing and is now
corrected, because 5-B.1's type census refutes it for three of the types.**  A flat
inline array can only encode a type whose values have a bounded *shape*; `cmd`, `frame`
and `stack` do not — `Seq of cmd * cmd` and `Case of text * (text list * cmd list) list`
nest to `MAX_CMD` depth, so "the array for one `cmd`" has no finite size at any setting
of the caps.  5-B.2 then measured *which half of that sentence is self-reference*: a
reachability walk over the `.mli` declarations finds **`cmd` reaches itself** (`Seq`,
`And`, `Or`, `Bang`, `If`, `While`, `For`, `Case`) and is the only type in the artifact
that does, while `frame` does not (it holds `cmd` values and lists of them, and its
widest constructor is 4 fields) and `stack = frame list` is a **list**, which R3 pools
for a different reason than self-reference.  Grouping all three together was therefore
half right — and the grouping that survives is the one §1's cap *comments* state
(`MAX_CMD` = "node-pool capacity for one lowered `cmd` tree", `MAX_STACK` = "explicit
machine stack frames"), i.e. `cmd` and `frame` are pooled types and `stack` is a list
of handles.  The contract therefore splits by kind, and the split is read off the
artifact rather than chosen:

| OCaml value | C99 encoding | why |
|---|---|---|
| R1 `nat`, `int`, `bool`, `unit`, any handle | `uint32_t` | `ExtrOcamlNatInt` already made `nat` a machine int; the caps prove every value `< 2^32`; one word for every field means a pooled cell's size is a **sum**, so no cell is padded and `sizeof` is decidable by arithmetic |
| R2 `text` (= `int list` of codes) | pool element `jpl_text { jpl_nat wt_len; jpl_nat wt_code[JPL_MAX_WORD]; }` (1028 B), **reached only through** `jpl_wref` | one bounded leaf — but the codes stay `uint32_t`, because `sh_concrete.v` only *intends* each to be `< 256` and an intent is not a lemma; `uint8_t` there would be an unproved narrowing. A value is a slab index because 1028 B would otherwise be copied through every parameter and return of this closure |
| R3 every other `'a list` | handle `jpl_ref` + cons-cell pool `{ a jpl_<t>_hd; jpl_ref next; }`, `JPL_NIL = 0` | a list's length is capped, its *element count in memory* is not; index 0 is never allocated, so a capacity counts the reserved cell |
| R4 `option`, `bres` | by-value struct `{ jpl_nat tag; v val; }`, tags `JPL_NONE/JPL_SOME`, `JPL_BRES_OK/JPL_BRES_LIMIT` | fixed size; `BLimit` is the model's saturate-to-error edge (§4.2), so it is a tag and not a sentinel |
| R5 `(a * b)` | by-value struct `{ a fst; b snd; }` | the artifact builds only binary pairs; an n-ary tuple is refused rather than silently right-nested |
| R6 a declared `record` | by-value struct, fields in declaration order | the `.mli` already fixes the shape |
| R7 a declared `variant` | all-nullary → `uint32_t` enum; otherwise, if it is one of the **pooled** types → node `{ jpl_nat tag; jpl_nat slot[i]; }` with `i` = max ctor arity, every slot a single word; otherwise → *fat struct* `{ jpl_nat tag; <each ctor's payload, named> }` | JPL forbids unions, so a non-pooled variant carries every payload and the tag selects which mean anything; a pooled node exists because one cell must hold every constructor |
| R8 a signature mentioning a type variable | **PENDING**, not emitted | monomorphization is JPL.5-B.3's call-site census (see above); inventing an instance here would be a second encoding of the choice |

The rule set is applied mechanically, and the two places where it *refuses* are
evidence of that: `of_ct` fails on a type outside the artifact's vocabulary, and
`require` fails on a by-value cycle ("must be pooled"), instead of unrolling one.

Reclamation follows from the same reading: the extracted kernel is purely functional, so
a lowered `cons` allocates and never mutates in place, and a pool that only grows cannot
survive `MAX_FUEL` steps.  "Static pools only" is therefore satisfied by a **copying
collection at the step boundary** (fixed two-space pool, forwarding through the handle
table, live-set bounded by the caps) — not by `free`, and not by a per-step region reset,
which the sharing in a functional program would make unsound.  §9.2's decision 3 carries
the sizing numbers and states which half of this is measured and which half is still open.

**"live-set bounded by the caps" is measured to be false for the word slab, and the
emitter says so instead of sizing it.**  A `cmd` tree is bounded by `MAX_CMD` *nodes*,
but a `Case` node owns a pattern list of up to `MAX_LIST` words and a `For` node a word
list of the same, so live words are bounded by a **product** of two caps (every node
owning a full list: `MAX_CMD × MAX_LIST`), and no entry of the LOCKED table is the
capacity of a word.  `verify/c/layout.txt` therefore prints the implied range
(4 096 … 4 194 304 live words, 1 028 B each) and the header declares
`extern jpl_text jpl_word_pool[];` with **no dimension** — a `PENDING` capacity, not a
guessed one.  Closing it is a model change, not an emitter change: `sh_jpl.v` §1 has to
fix one number in that range, prove the machine never exceeds it, and export it through
`jpl_caps_table` the way 5-B.2a did for the other nine.  Until then JPL.5-B.3 can lower
every control flow in the closure but cannot link, because the slab has no extent.

### 6.1 Established extraction behaviour

A fuel-bounded tail `Fixpoint` (`scan (f:nat) (l:list) (acc:list)` with the
recursive call in tail position) extracts to OCaml `let rec scan f l acc = match f
with O -> ... | S f' -> ... scan f' r ...` — a genuine tail loop, so lowering to a
C `while` (decrement `f`, exit on `O`) is sound. Two obligations for the model/emitter:
- `List.rev`/`app` extract to NON-tail structural recursion; the source must use
  accumulator-style bounded helpers, or the emitter must lower bounded structural
  recursion (length <= MAX) to a bounded copy loop over whatever §6's table says that
  sequence is — a leaf `text` copies inline, a `cmd`/`frame` list copies *handles*.
- Extraction keeps a custom `nat = O|S` and `list = Nil|Cons` (or native list under
  ExtrOcamlBasic); the emitter maps these to `uint32_t` and, per §6's table, to an
  inline `MAX_WORD` buffer for bytes or a handle into a static node pool for the
  recursive types.

### 6.2 The three choices 5-B.2 could not derive

Everything in `verify/c/sh_run_jpl.h` is derived from a `.mli` line plus a capacity
folded out of the `.ml`, **except** three decisions, which the emitter numbers the same
way `verify/c/layout.txt` prints them so a reader can trace any number back to one of
them.  They are recorded here rather than hidden in the tool because §2's single-source
rule is about *semantics*: a layout choice is allowed to be a choice, as long as exactly
one place owns it and it is stated.

| # | choice | what was picked | why the artifact does not decide it |
|---|---|---|---|
| 1 | which declared types are **pooled** | `cmd`, `frame` | `cmd` is forced (it reaches itself); `frame` is bounded in shape (4 fields) and could be by-value, but §1's cap comments describe a *frame pool* (`MAX_STACK` = "explicit machine stack frames"), and a by-value frame embedded in a list cell would size the stack pool by the widest constructor instead of by `MAX_STACK`.  Picking the comment over the smaller encoding is the one place where the model's *intent* outranks the layout's arithmetic |
| 2 | which cap sizes which **list pool** | `pair(text,text)` → `MAX_ENV`; `frame` list → `MAX_STACK`; every other list kind → `MAX_LIST` | a list's cap depends on which list it is, and OCaml types do not carry that name.  The mapping is justified per kind by §5's `wf_benv` (an env is `MAX_ENV` pairs) and §1's `MAX_STACK` comment; the rest fall to `MAX_LIST` = "any intermediate list length" |
| 3 | the pool **headroom** factor | 2 | a pool must hold the live set *and* the garbage produced between step boundaries, and the per-step allocation bound is not yet established by proof or measurement (decision 3's open half).  So each pool is `cap × 2`, one doubling that is explicitly a placeholder until 5-B.3's allocation census replaces it with a measured number |

Decision 3 is also why the header's pool sizes are `#define JPL_POOL_<KIND>` rather than
bare dimensions: the factor appears once, in the emitter, and every cell count in the
report is printed as "n cells × headroom 2" so the arithmetic is visible.

## 7. Verification: JPL lint gate (design)

`verify/c/jpl_lint.sh` audits the emitted `sh_run.c`/`.h`:
- static ban list via grep + clang: no `malloc|calloc|realloc|free`, no direct or
  indirect recursion (call-graph acyclic within the emitted file), no `float|double`,
  no `char` used in arithmetic, no `short`, no VLAs (all arrays constant-sized), no
  `goto`, no `default:` in `switch`, one `return`/early-return style, all locals
  initialized, casts are explicit (`-Wconversion -Wsign-conversion` clean), no TAB.
- compile with `clang -std=c99 -Wall -Wextra -Wconversion -Wsign-conversion
  -pedantic -Werror`.

## 8. Verification: differential gate (design)

`verify/c/` host supplies the real `phi` (fork/execvp/pipe/redirect, cd/exit/:)
over the C kernel, then:
- replays the parity table (C99 == extracted iterative OCaml kernel) — currently the
  26 `mrun`-vs-`run` facts plus the **66** D5 checks, so the C99 has to reproduce every
  fact the OCaml artifact is pinned to, including the `expand_it` sweeps,
- replays the /bin-sh conformance corpus (C99 == /bin/sh) for the implemented
  subset (see the `src/` boundary memory).
Added to `verify_models.sh` / a new `verify/c/conformance.sh`; all prior gates
(OCaml-free now, so: Coq properties x2, extraction parity, src conformance) stay green.

## 9. Construction order (matches task list)

This is the **normative build order**: a strictly sequential dependency chain —
each stage's deliverable is a precondition for the next, so they are *stages*, not
parallel tracks. Read an arrow `->` as "blocks". Task numbers (#N) refer to the
project tracker; file names are the Coq/build artifacts the stage delivers.

**Label scheme (decoded).** `JPL.<phase>` = a top-level pipeline phase. When a
phase's precondition audit shows it cannot run on the current source, a **path**
letter is appended — `JPL.5-A` = the chosen "root-cause the Coq source first" path
for phase 5 (the alternative `B`, "transpile as-is", was rejected; see HISTORY).
`<phase>-<path>.<stage>` = an ordered prerequisite stage *inside* that path,
numbered in dependency order. So `5-A.1` is "stage 1 of the A path leading to phase
JPL.5 (the emitter)". In the **No** column below, `#N` is the tracker task;
**Files** lists the `.v`/`.ml` artifacts that stage reaches its goal through
(*italics* = planned, not yet in the tree).

### 9.1 Build order (No · Description · Files)

| No | Description | Files (Coq `.v` / OCaml `.ml`) |
|---|---|---|
| JPL.1 · #21 | Design plan (this document) | *`JPL.md`* (doc, not code) |
| JPL.2 · #22 | Bounded data layer: `bres`/`bword`/`benv`, saturate-to-error, fixed-width nat, `cmd_count` — agrees with `sh_concrete` §9 | `sh_jpl.v` ← `sh_concrete.v` |
| JPL.3 · #23 | Small-step machine: frames-as-data, explicit continuation stack, non-recursive `step`, phi-folded tail driver `mloop`; soundness `mrun_sound`/`mrun_correct` | `sh_jpl_run.v` ← `sh_concrete.v`, `sh_jpl.v` |
| JPL.3b · #28 | Liveness/completeness: well-founded `cfg_budget`, `mrun_live`, two-sided `mloop_iff`/`mloop_sound_complete` | `sh_jpl_run_phase2.v` ← `sh_jpl_run.v` |
| JPL.4 · #24 | Extract iterative kernel + re-run 26 parity (mloop == run == literal) | `sh_extract_iter.v` → `sh_run_iter.ml`/`.mli`; vendored `src/kernel/sh_run_iter.ml`/`.mli`; parity `sh_run_iter_parity.ml`; gate `verify_models.sh` |
| 5-A.1 · #29 | Bounded byte-array text `bt` (len-carrying, MAX_WORD) + the `bt_push`/`bt_eq`/`bt_append` write-and-compare seams, saturation lemmas and byte-agreement Examples. Scoped (per the 2026-10-03 refinement below) as **foundation + contract only**: `app`/`teqb`/`nat_digits`/`expand`/`expand_*` stay single-source and are the emitter's to lower | `sh_jpl_scan.v` §1–3 ← `sh_concrete.v`, `sh_jpl.v` |
| 5-A.2 · #30 | Tail-loop `getv`/`setv` over the `benv` array rep: fuel-bounded `getv_it` (cursor scan) + `setv_it` (cursor scan with the visited prefix in a reversed `acc`, spliced by tail-recursive `rev_append`), `None` = saturation; array API `be_getv`/`be_setv` proved equal to sh_jpl's `benv_getv`/`benv_setv`, plus the capacity law `be_setv_refuses_at_capacity` and `be_getv_be_setv_same` | `sh_jpl_scan.v` §5 ← `sh_concrete.v`, `sh_jpl.v`; gated by `verify_models.sh` — **DONE** (coqchk 4×`<none>`, agreement proved not sampled, gate green) |
| 5-A.3 · #31 | Iterative `glob`/`match_any`: the `glob f' ps str \|\| glob f' pat ss` **tree** recursion → one forward fuel-bounded tail scan `glob_it` carrying a single saved backtrack cell `bk` (no separate backtrack stack); `match_any_iter` a tail scan over the branch's patterns | `sh_jpl_scan.v` §4 ← `sh_concrete.v`, `sh_jpl.v`.  Agreement with concrete `glob` is **proved both ways for arbitrary input**: §4.2 soundness (`glob_iter f pat str = true -> gmatch pat str`, hence `-> glob (S (length pat + length str)) pat str = true`, with no fuel hypothesis on the loop side; `match_any_iter_sound` names a real branch match) and §4.3 completeness (at the loop's own `fuel_top`), so `glob_iter (fuel_top pat str) pat str = true <-> glob (S (P+S)) pat str = true`.  The `gi_matches_concrete_*` Examples are now only cheap regression samples |
| 5-A.3 gap · #34 | Close §4's sampled agreement with general theorems over arbitrary `pat`/`str`/`bk`, by way of a declarative `gmatch` spec of glob written independently of both implementations | `sh_jpl_scan.v` §4.2 + §4.3 — **DONE, both halves (2026-10-04)**.  *Soundness* (§4.2): spec + retry machinery (`gmatch`, `gmatch_star_app`, `gretry`, `ok_it`), L2 `glob` decides `gmatch` at **linear** fuel `S (P+S)` (`glob_iff_gmatch`, `glob_fuel_mono`), `glob_it_sound`/`glob_iter_sound`/`glob_iter_accepts_glob`/`match_any_iter_sound`.  *Completeness* (§4.3): `glob_iter_complete_at` — `gmatch pat str -> fuel_top pat str <= f -> glob_iter f pat str = true`, induction on fuel covering all six loop sites; then the two-sided `glob_iter_iff_glob` and `match_any_iter_iff_match_any` at the shared branch budget.  The budget is `fuel_top pat str = (P+S+1)*(S+1) + P + S` (`P = length pat`, `S = length str`) — the loop's own **quadratic** law, not §4.2.2's linear one, because the two genuinely differ: `*a` on `aaa` is the minimal witness (L2 decides at 6, the loop needs 7, `fuel_top` = 29; all three are `reflexivity`).  `ok_it`'s bare disjunction cannot carry this direction — a cell unrelated to the forward state satisfies it, and the install site is then left with no equation that forces the bound down — so §4.3 proves over the **anchored** invariant `cinv`: the saved pair is the forward pair with one and the same star-free lockstep chunk (`pre`, `pre'`) re-attached, `fmatch` recording that chunk, which is what makes every site strictly lower `state_bound`.  Gate green, `coqchk` 4×`<none>`, D5 artifact byte-identical with 34/34 parity.  **Budget consequence for #35 (closed same day):** the law's value at two full-width words, `fuel_top 256 256 = 132 353` (and the tighter *measured* `(P+1)*(S+1) = 66 049`), sits far above the then-locked `MAX_FUEL = 4096` — the proved law crosses 4096 at P=S=45, the measured law at 64 — so a glob budget of its own was unavoidable.  §1 now defines `GLOB_FUEL` derivationally from `MAX_WORD` as exactly that worst case and `MAX_FUEL = GLOB_FUEL + 4096`; `sh_jpl_scan.v` §4.3.14 proves the constant covers `fuel_top` for every in-budget word pair and states the completeness corollaries at `GLOB_FUEL`/`MAX_FUEL` |
| 5-A.4 · #32 | **phi-as-data driver**: closure-free `mrun` returns `DEff` effect DATA and takes **no** `phi` fn; `host` services the seam + re-enters; `host_sound`/`host_live`/`host_iff_run` restate JPL.3/3b over it | `sh_jpl_run_phase3.v` ← `sh_jpl_run_phase2.v`, `sh_jpl_run.v`, `sh_jpl.v`, `sh_concrete.v`; gated by `verify_models.sh` — **DONE** (coqchk 4×`<none>`, §7 Examples green) |
| 5-A.5 · #33 | Clean extraction **settings + artifact**: `ExtrOcamlNatInt` (nat→machine int) + `Nat.div`/`modulo`/`divmod`/`sub` hooks → `sh_run_c.ml`, in which the driver `mrun` emits as **one tail loop with no functional argument**; parity re-run through it | `sh_extract_jpl_c.v` ← `sh_jpl_run_phase3.v`, `sh_jpl_run.v`, `sh_jpl_scan.v`, `sh_jpl.v`, `sh_concrete.v`; artifact `sh_run_c.ml`/`.mli`, **vendored** as `src/kernel/sh_run_c.ml`/`.mli`; harness `sh_run_c_parity.ml`; **gate block 2c** (`verify_models.sh`, user-approved 2026-10-04) — **DONE (2026-10-04)**.  Evidence: 34 parity checks green (the 26 §7–§9 facts through `mrun` + a hand-written closure-free host, + 8 tail-loop-vs-concrete checks of the emitted `sh_jpl_scan` loops), the block's anti-rot `diff -q` against the vendored copy, a clean `dune build` of `sh_kernel` with the third module in it, and `verify/src/conformance.sh` still 33/33 (ush does **not** link `Sh_run_c`, so the vendored copy is the emitter's input pinned to a verified byte sequence, not a shipped dependency).  What the stage deliberately does **not** close: `step` still calls the concrete scans — measured **6 kernel call sites** (`setv` ×3 at `sh_run_c.ml`:1101/1148/1156, `match_any` ×1 at :1133, `expand` ×2 at :1101/1133; concrete `getv` :784 and `glob` :888 are reached only *through* `expand`/`match_any`, never directly).  Recursion inventory (call-graph measured over the artifact, 2026-10-03): 25 `let rec`/`and` bindings are emitted; `mrun`'s closure holds **15** of them — 2 already fuel-bounded tail loops (`mrun`, `enter_case`), 3 primitive aliases that only *print* as `let rec` (`add`→`(+)`, `sub`, `divmod`), and **10 genuine structural recursions** (`teqb`, `app`, `getv`, `setv`, `nat_digits`, `expand`, `expand_name`, `expand_brace`, `glob`, `match_any`).  The other 10: 4 in the `run` reference cluster (`run`, `run_seq`, `run_for`, `run_case`) and 6 unreachable from either root — `length`, `rev_append` plus the four *proved* tail loops `glob_it`, `match_any_iter`, `getv_it`, `setv_it`, i.e. 5-A.2/5-A.3's deliverables are dead code in the artifact until #35 rewires the 6 sites → 5-A.6.  *(The inventory in this row is now the **pre-#35 baseline**, superseded on 2026-10-04 by the re-measurement recorded in the 5-A.6 row: the 6 sites are rewired, block 2c runs **59** parity checks rather than 34, and this row's prediction "structural 10 → 8" measured **10 → 11**.  Kept unchanged because a wrong prediction that was checked is worth more than a right one that was not.)* |
| 5-A.6 · #35 | Rewire the machine's scans onto the proved tail loops so extraction *consumes* them: the rewired sites `expand_c`/`assign_c`/`bind_word_o`/`enter_for_c`/`enter_case_c` under a rewired dispatcher `step_c` (= `step_cmd_c`/`step_ret_c`), calling `setv_it` and `match_any_iter` (whence `glob_it`) at §4.3.14's budgets with agreement transported from `sh_jpl_scan.v` §4.3/§5, plus drivers `mrun_c`/`host_c`.  It also landed the guard machinery L4 did not have: **§4.3.15** of `sh_jpl_scan.v` — `branch_need` (the closed form of L2's exact site threshold, proved *necessary* by `branch_decisive_need` and *sufficient* by `branch_need_decisive`, so it is minimal rather than convenient), its cap bound `branch_need_in_caps`/`branch_need_le_max_fuel`, and `branch_guardb` with `branch_guardb_match`, the boolean the kernel evaluates.  **Not a search-and-replace of four names**: the two matchers have different fuel laws — L2's `match_any g pats w` globs pattern *i* at `g-1-i` and decides at the **linear** `branch_need pats w = max_i (length p_i + length w + i + 2)`, the loop needs the **quadratic** `fuel_top` per pattern — so below its own `fuel_top` the loop answers `false` where L2 already answers `true`, and §6 measures that band instead of assuming it (`tree_decides_below_loop_need`: `[*;a]` vs `a-a-a`, L2 decisive at site fuel 6, loop needs 29, all three by `vm_compute`).  A drop-in would therefore be unsound in the *wrong* direction, so `enter_case_c` evaluates `branch_guardb` (one decidable boolean: `branch_need <= site fuel`, conjoined with `length w <= MAX_WORD`, `length pats <= MAX_LIST` and per-pattern `<= MAX_WORD`), reads a failed guard as `Olimit` — the same saturate-to-error edge as exhausted fuel — and hands the loop its own `GLOB_FUEL + length pats`.  Consequence: the headline is **conditional**, `step_c_ok : forall g, step_c g <> Olimit -> step_c g = step g` (§2), and an unconditional `step_c = step` is proved **impossible** rather than merely unattempted (`host_c_saturates_where_host_answers` exhibits a `case` L2 answers at fuel 8 where `host_c` reports `BLimit`; `host_c_ample_case_matches_host` recovers it one fuel up).  The asymmetry is then the honest one: **soundness unconditional** (§3 `mrun_c_ok`/`mrun_c_done_sound`/`mrun_c_eff_sound`, §4 `host_c_sound`, `host_c_bok_is_host_bok` — a data boundary cannot have passed through a fired guard), **completeness under one hypothesis** `no_sat` (§4 `host_c_agree`/`host_c_complete`/`host_c_iff_run`), and the driver's shape fixed by typing rather than reading the artifact (§7 `mrun_c_type : Type := nat -> cfg -> dres`, `Example mrun_c_closure_free`).  Budgets raised where the proofs needed it and proved **least** where the plan previously claimed only sufficiency (§5): `case_site_fuel` = 1537 is *attained* (`branch_need_repl`, `branch_need_worst_case`) hence minimal (`guard_fuel_is_least`); `GLOB_FUEL` is *literally* `fuel_top MAX_WORD MAX_WORD` (`glob_fuel_is_tight`, `fuel_top_at_caps`); `MAX_FUEL - GLOB_FUEL = MAX_CMD` exactly (`max_fuel_margin_eq_MAX_CMD`); and the constants are usable, not just tight — `case_allowance_inside_glob_fuel` (2561 ≤ GLOB_FUEL), `branch_chain_funded`, `scan_budget_in_range`, and `enter_case_c_chain_clear` (induction on site fuel over a whole `MAX_LIST`-walk branch chain: ample fuel ⇒ no saturation), whose single `length (expand …) <= MAX_WORD` hypothesis is deliberate because L2 proves nothing about `expand`'s output length — `expand_c` is what turns that open question into a closed cap check on the *result*. | `sh_jpl_run_c.v` (new layer **L8**) ← `sh_concrete.v`, `sh_jpl.v`, `sh_jpl_run.v`, `sh_jpl_run_phase2.v`, `sh_jpl_scan.v`, `sh_jpl_run_phase3.v`; re-extracted by `sh_extract_jpl_c.v` → `sh_run_c.ml`/`.mli`, vendored `src/kernel/` copy re-synced, harness `sh_run_c_parity.ml`, **gate block 2c** + the new L8 Coq gate — **DONE (2026-10-04)**.  Evidence: `coqchk -o -silent` four `<none>` with no `Axiom`/`Parameter`/`Admitted`/`admit`/`Classical`/`Epsilon`; phase3's §7 `dres` surface re-produced by the rewired kernel **by computation** (§6 Examples); **59** parity checks green (was 34); block 2c's anti-rot `diff -q` against the re-vendored artifact; clean `dune build` of `sh_kernel`; `conformance.sh` still 33/33.  **Measured after-state, and a prediction corrected** (call graph over the re-extracted artifact; method matters — top-level `let rec`/`and` after stripping `(** val … **)` comments, closure from each root; the 2026-10-03 numbers also counted `sub`/`divmod` as reachable, which this artifact does not): **28** recursive bindings emitted (was 25); `mrun_c`'s closure **18** = 5 fuel-bounded tail loops (`mrun_c`, `enter_case_c`, `setv_it`, `match_any_iter`, `glob_it`) · 2 print-only aliases (`add`, `mul`) · **11** structural (`teqb`, `app`, `length`, `rev_append`, `forallb`, `getv`, `nat_digits`, `expand`, `expand_name`, `expand_brace`, `branch_need`); `mrun`'s closure **13** = 2 tail + 1 alias + the same **10** structural recursions counted pre-#35, so the reference root did not move; reachable from **neither** root: **5** — the four-member `run` oracle (kept because parity asserts `host == run`) plus `getv_it`.  5-A.5 predicted "tail loops 2 → 5, structural 10 → 8": the tail-loop half hit exactly and `setv`/`match_any`/`glob` did leave, but structural recursions went **10 → 11** because the guard is not free — it contributes `branch_need` and `forallb`, `expand_c`'s cap check and the loop's own `length pats` budget contribute `length`, `setv_it` contributes `rev_append`; 3 out, 4 in.  Its advice to route `be_setv`'s double `length` through the API turned out **moot** (the machine calls `setv_it` directly; `be_getv`/`be_setv` are in the surface only for §5's array-API checks).  So the qualitative claim stands and the quantitative one is corrected: #35 **converts** recursion and makes 5-A.2/5-A.3's deliverables live (dead proved loops 4 → 1) but does not reach zero, and the residual is still the `expand` group *plus* the guard's own bounded scans — every one of them length-bounded by `MAX_LIST`/`MAX_WORD`, hence inside §6.1's "lower bounded structural recursion" contract.    **PENDING as its own scan-side stage: `expand_it`** (tail-loop expander wired to `getv_it`, agreement against L2 `expand`) — the single remaining change that drains `getv`, `nat_digits`, `expand_*`, and with a capped word handed back by the API also `length`/`forallb`/`branch_need`.  Simplifications the re-analysis found (user: "maybe we will see some simplification"): `expand_c` is **one** `expand` call and `enter_case_c` expands the scrutinee **once per branch site**, shared by guard and matcher, so the rewired machine does exactly the reference's work per step; `Extract Constant Nat.max => "(Stdlib.max)"` was missing (`ExtrOcamlNatInt` hooks minus/mult/leb/eqb but **not** `max`), which would have emitted `branch_need`'s `max` as a Peano recursion; and the harness's duplicated fact tables collapsed into one 15-entry `facts` list driven through **both** machines, which is what makes the rewiring a parity claim rather than a second suite.  Parity **34 → 59** = 30 (15 facts × 2 drivers) + 12 §8/§9 expand/glob + readback (each now also `[rewired]`) + 8 tail-loop-vs-concrete (§4, unchanged) + 9 **boundary** checks that exercise the decisions #35 made rather than its happy path (`expand_c` admits at exactly 256 bytes and saturates at 257; `branch_guardb` refuses at 6 / admits at 7 on the `[*a]`-vs-`aaa` band and enforces the 1024-list and 256-word caps; the fuel-8 saturating `case` from OCaml and its fuel-9 agreement).  `verify_models.sh` **10/10 → 11/11** (`sh_jpl_run_c.v` joins `COQ_MACHINE`; block 2c's chain gained `coqc sh_jpl_run_c.v`) — edited under the standing authorization for that file (granted 2026-10-03, re-granted for the 2c wiring on 2026-10-04).  `sh_extract_jpl_c.v` now names both drivers on its surface (`mrun`/`step` kept in-module as the oracle for `host_c = host`) and still deliberately does **not** extract `host_c` (it takes `phi : run_phi`, a function type; the C host is JPL.7's).  *(Superseded on 2026-10-04 by **5-A.7**, which landed `expand_it` — but landed it with **hypothesis-free** agreement, so the expander needed neither the guard nor a raised budget that this row's `case` rewiring did.  One prediction here was wrong in advance and is corrected rather than edited away: `expand_it` is NOT "wired to `getv_it`", because L2's `getv` is already a forward tail scan and a second encoding of it would add a parallel implementation without removing a recursion.  This row's after-state census (28 recursive bindings emitted, `mrun_c` closure 18, `getv_it` the one dead proved loop) is re-measured in the 5-A.7 row.)* |
| 5-A.7 · #37 | **Last scan-side stage**: replace L2's `expand`/`expand_name`/`expand_brace` **mutual fixpoint** with ONE fuel-bounded tail loop and wire it into L8, so the extracted kernel reaches the OS seam with no non-tail scan left of the class §6.1 hands to the emitter | `sh_jpl_scan.v` **§6** (`exp_mode`/`exp_k`, `expand_go`/`expand_it`, agreement, §6.4 witnesses) + `sh_jpl_run_c.v` rewired at its two expansion sites; re-extracted `sh_run_c.ml`/`.mli`, vendored copy re-synced, harness `sh_run_c_parity.ml`, gate block 2c + the L8 Coq block — **DONE (2026-10-04)**.  *Design*: the three fixpoints become one loop over an explicit cell `ExpK { mode; inp; out; name }` — L2's mode switch is a **return into another fixpoint at fuel `f'`**, here it is a **write of `ek_mode` with the same `f'`**, which is why one fuel counter serves all three; the output accumulates REVERSED (one `rev` per expansion instead of one per byte) and the collected name is read back with `rev nm`; `ek_value` + `ek_valuesubst` bridge the substitution step to L2's `subst_var`.  *Crux*: because the decrements mirror the reference one for one, agreement is **exact at every fuel** — the invariant `expand_go_correct : expand_go f m st (ExpK mode inp o nm) = rev o ++ expand_at m st f mode inp nm` yields `expand_it_correct : expand_it f m st inp = expand f m st inp` with **no hypothesis at all**, so unlike §4.3.13b/§4.3.15 there is no fuel-law gap to guard and **no constant moved** (§4.1).  `getv` is called in its concrete form *on purpose*: it is already a forward tail scan, so wiring `getv_it` in here would have added a second encoding of the same scan rather than removed a recursion — recorded as the answer to 5-A.6's "wired to `getv_it`" phrasing.  *L8*: `expand_c` and the `enter_case_c` scrutinee now call `expand_it`; because §2/§5's statements stay phrased about the reference (the oracle is single-source), each proof reads the loop back through `Ltac exp_ref := repeat rewrite expand_it_correct`, and the headline `step_c_ok` is unchanged.  *Evidence*: `coqchk -o -silent` four `<none>` for `sh_jpl_scan` and `sh_jpl_run_c` (no `Axiom`/`Parameter`/`Admitted`/`admit`); §6.4's byte-level Examples (10 behavioural — name, lone `$`, brace, `$?`, unset brace, `{$a}`-style name brace, status 127, zero fuel, **no re-scan of a substituted value** — plus 4 equalities against the reference at deliberately low fuel); parity **59 → 66** (5 point checks + 2 sweeps of 15 words × 9 fuels = 135 loop-vs-reference comparisons each, **270 over both**, failing on the first mismatch); gate **11/11**; `dune build` clean; `conformance.sh` **33/33** with `ush` rebuilt against the re-vendored artifact.  *Measured after-state* (call graph over the artifact, comment banners stripped; the parse was independently re-derived two ways and the two agree on every number — a first pass that counted `(** val … **)` banners as code produced phantom edges, e.g. `enter_for → enter_case`, and had to be discarded): **76** top-level bindings, **30** recursive (5-A.6 recorded **28** recursive for the artifact it left, and did not record that file's total, so only the recursive counts are comparable across the two rows — the +2 is `expand_go` entering and `rev` entering, while `expand`/`expand_name`/`expand_brace` stay because the oracle roots still extract them); `mrun_c`'s closure **45** bindings / **17** recursive (was 18) — *[corrected by 5-B.1,
2026-10-04: the member count here is 2 low — a re-derivation by two methods (AST closure and
a text identifier graph over the same bytes) gives the same **47** names, set-equal, and the
same **17** recursive ones.  The recursive split this row depends on (6 + 2 + 9 = 17) is
unaffected, which is why the undercount survived: the plan only ever reasoned about the
recursive set.  `verify/c/closure.txt` is now the authoritative inventory.]* = **6** fuel-bounded tail loops (`mrun_c`, `enter_case_c`, `setv_it`, `match_any_iter`, `glob_it`, **`expand_go`**) · 2 print-only aliases (`add`, `mul`) · **9** bounded non-fuel recursions (`teqb`, `app`, `length`, `rev_append`, `forallb`, `getv`, `nat_digits`, `branch_need`, **`rev`**).  Delta: `expand`, `expand_name`, `expand_brace` **leave** the kernel's closure, `rev` **enters** it (the loop's one-pass final reversal, bounded by `MAX_WORD`).  The oracle roots did not move (`mrun` 13, `run` 15, `step` 12 — they still hold the `expand` group, which is the point of keeping them).  What is reachable from no kernel root: `be_getv`/`be_setv` (extraction roots in their own right, consumed by §5's array-API checks) and, through the former, `getv_it` — i.e. `getv_it` is *live in the artifact and dead in the machine*, which is the distinction 5-A.6's "the one proved loop still dead" blurred.  **Consequence for the plan**: the residual `mrun_c` recursion set is exactly §6.1's "lower bounded structural recursion" class plus six tail loops, and the mutual fixpoint that made JPL.5's opening decision 2 ("does `expand_it` precede the emitter?") non-trivial no longer exists — that decision is **closed by construction**, leaving only decision 1 (which root JPL.6's Rule-6 lint binds). |
| 5-B.1 · #38 | **Emitter front end**: read the extracted artifact the way the emitter must read it — the *typed closure from the roots the C host calls*, not the whole file — and refuse to proceed if any construct in that closure is outside JPL.5's declared subset.  Deliberately NOT a transpiler: it computes the closure, classifies every expression/pattern constructor it meets, recognises `ExtrOcamlNatInt`'s nat-destruct value (`(fun fO fS n -> if n=0 then fO () else fS (n-1))`) as a *switch*, not a call, and reports the allocation census + type vocabulary that the representation decision needs.  Loud failure is the deliverable — §9.2's decision 1 (which root Rule 6 binds) is answered by a **measured asymmetry** in the same tool: roots `mrun_c,step_c` ⇒ SUBSET OK, roots `run,step,mrun` ⇒ OFF-SUBSET on the mutual `expand`/`expand_name`/`expand_brace` fixpoint that the oracle cluster still drags in.  What the census then forces: `cmd`, `frame` and `stack` are **recursive** value types (`Seq of cmd * cmd`, `For of text * text list * cmd list`, `Case of text * (text list * cmd list) list`, `stack = frame list`), so no inline fixed-capacity encoding of them exists at any budget — §6's "static pools only" therefore means a **handle + node pool**, and only `text` is free to be an inline 256-byte run *[corrected by 5-B.2's layout: the leaf is 256 **`uint32_t` codes** = a 1028-byte `jpl_text`, and even that is reached through a `jpl_wref` handle rather than copied by value — see §6's R2*] | `verify/c/jpl_front.ml` (compiler-libs `Parse` + `Ast_iterator`), `verify/c/jpl_front.sh` (builds it in a `mktemp -d`, runs it, byte-compares the evidence), `verify/c/closure.txt` (the tracked inventory) — **DONE (2026-10-04)**.  Evidence: **gate 11/11 → 13/13** — new block **2d** runs the front end over the *vendored* bytes block 2c just bound to a fresh Extraction, plus **2d-negative**, which asserts the oracle roots are *refused* (a lint that accepts everything is not a gate); the toolchain-free rung is recorded **SKIP**, and the summary line now prints the skip count so a missing `ocamlfind` can never read as a pass.  Measured after-state: artifact **81** bindings / **76** typed signatures / **14** type declarations *[superseded the same day by **5-B.2a**: exporting `jpl_caps_table` added the `jpl_caps` record type and its field accessors to the artifact, and the tracked inventory `verify/c/closure.txt` now reads **87** bindings / **81** typed signatures / **15** type declarations — the figures 5-B.2's report prints from the same bytes.  The closure numbers below are unaffected: the caps table is data, not control flow, so the roots still reach 47 bindings / 17 recursive]*; roots `mrun_c,step_c` ⇒ **47** bindings, **17** recursive = 6 fuel-bounded tail loops (`mrun_c`, `enter_case_c`, `setv_it`, `match_any_iter`, `glob_it`, `expand_go`) + 2 print-only aliases (`add`, `mul`) + 9 length-bounded structural recursions (`length`, `app`, `rev`, `rev_append`, `forallb`, `teqb`, `getv`, `nat_digits`, `branch_need`) — which **agrees name-for-name with the 17-name recursive split of 5-A.7's census but supersedes its member count** (that row recorded 45, re-measured here at 47 by two methods — AST closure and a text identifier graph — that are set-equal; see the correction appended to that row); **2** mutual `let rec` groups exist in the file and **0** are in the shipped closure.  Expression classes met: ident 7068, apply 6572, construct 163, function 68, constant 61, tuple 43, record 42, match 40, if 32, field 28, let 11; pattern classes: var 253, construct 107, tuple 54, any 24.  Allocation census (the sizing input): literal `nat` 61, tuple 43, `record(4 fields)` 35, ctor `Onext` 25, cons 24, `option Some` 23, `option None` 15, ctor `false` 12, nil 12, unit 11, ctor `Olimit` 8, `record(2 fields)` 7, ctor `EMain` 6, ctor `true` 4, then 19 single-site constructors |
| 5-B.2a | **Cap table as data**: make the nine LOCKED constants readable by the emitter *from the artifact*, so no layout tool holds a second copy of §1's table | `sh_jpl.v` §1.1 (`jpl_caps` record, `jpl_caps_table`, `jpl_caps_are_locked`) → `jpl_caps`/`jpl_caps_table` in `sh_run_c.ml`/`.mli` — **DONE (2026-10-04)**.  *Why it was needed*: extraction carries a constant only when kernel code mentions it, so `MAX_WIDTH`, `MAX_ARGV`, `MAX_CMD` and `MAX_STACK` — proof-only in the kernel — would have vanished and the emitter would have had to hard-code them.  *Evidence*: re-extraction green, parity 66 unchanged, `conformance.sh` 33/33, and gate block 2c's artifact check; the differential in 5-B.2's block 2e is what makes this export load-bearing rather than decorative |
| 5-B.2 · #39 | **Representation layer**: turn §6's rules R1–R8 into the C99 header the host will compile against — every reached type laid out, every size and every cap relation enforced by the *compiler* rather than asserted by a comment | `verify/c/jpl_emit.ml` + `verify/c/jpl_ast.ml` (shared reader), `verify/c/jpl_emit.sh` (runner: build + emit, `clang -std=c99 -Wall -Wextra -Wconversion -Wsign-conversion -pedantic -Werror -fsyntax-only`, differential cap fold against the OCaml runtime, byte-compare of the vendored evidence), vendored `verify/c/sh_run_jpl.h` (365 lines) + `verify/c/layout.txt` (109 lines) — **DONE (2026-10-04)**.  *Evidence*: **gate 13/13 → 15/15** — block **2e** runs all four checks over the bytes block 2c bound to a fresh Extraction, block **2e-negative** asserts the oracle roots are *refused for the layout reason* (`a function-typed value has no layout`, on `run`'s `run_phi` driver parameter), which is a different root-sensitivity verdict than 2d-negative's mutual-fixpoint refusal.  40 C types emitted; **34 compile-time assertions** cover them all — 27 aggregate rows each followed by its own `sizeof` check, 13 one-word typedefs (scalars, handles, the all-nullary variant) covered conjunctively by `jpl_check_one_word_families`, plus the 5 cap relations and the word-width check; 31 prototypes emitted, **5 PENDING** (the polymorphic bindings, with their caller counts, because R8 refuses to invent an instance), and 5 bounded static pools totalling **187.0 KiB**.  *What this layer measured and §6 now records*: five shipped functions need monomorphization (`length, app, rev, rev_append, forallb`, 2–6 call sites each); only `cmd` reaches itself, so §6's "recursive types" sentence needed halving; and **the word slab cannot be sized** — no cap bounds the number of live `text` values, so `jpl_word_pool[]` is declared without a dimension and the model owes a `MAX_WORDS` before 5-B.3 can link (see §6, §6.2, and decision 3).  *Self-correction on the same day*: the report's first line claimed "40 C types emitted, each followed by a sizeof check", which the header disproved (27 of 40); the claim is now measured by the emitter itself and the family assertion closes the gap, so no emitted type's size is unverified |
| JPL.5 · #25 | Tail-loop OCaml → JPL-C99 **emitter** (pure layout only: `list`→array+len, `nat`→`uint32`) | *emitter input `sh_run_c.ml` → output `.c`* — **un-blocked, and now half-built: the layout half (5-B.2) is gated green as `sh_run_jpl.h`; the lowering half (5-B.3: 6 tail loops → `while`, 9 bounded structural recursions → copy loops, R8's monomorphization census, and the `MAX_WORDS` capacity the word slab needs) is what remains.**  5-A.5 settings + artifact, 5-A.6 kernel wired onto the proved loops, 5-A.7 no mutual fixpoint left, 5-B.1 typed closure + subset gate, **5-B.2 representation header + differential cap gate** |
| JPL.6 · #26 | Mechanical D-60411 *shall*-rule lint gate on emitted C (`clang -std=c99 -Wall -Wextra -Wconversion -Werror` + static analyzer) | *`verify/c/jpl_lint.sh`* — pending |
| JPL.7 · #27 | C host + differential conformance: C99 == extracted kernel == `/bin/sh` | *`verify/c/*`* + oracle `verify/src/conformance.sh`, `verify/src/cases` — pending |

Reference layers consumed above but not themselves stages: `sh_properties.v` (L1
relational spec), `sh_concrete.v` (L2 single source of truth), and the recursive
extraction `sh_extract.v` → `sh_run.ml` (vendored `src/kernel/sh_run.ml`, parity
`sh_run_parity.ml`), and the iterative extraction `sh_extract_iter.v` →
`sh_run_iter.ml` (vendored, parity `sh_run_iter_parity.ml`). The models gate
`verify_models.sh` compiles + axiom-checks every `.v` row and runs all three
extraction blocks (2c is the clean kernel — `sh_extract_jpl_c.v` →
`sh_run_c.ml`).

### 9.2 Stage accounting

Progress rollup against §9.1. **A stage is DONE only if its `.v` passes
`coqchk -o -silent` with the four `<none>` lines AND its empirical harness (parity /
conformance) is green** — an assertion that cannot yet be built is recorded PENDING,
never PASS. Update this table in the same edit that changes a stage's state; the
tracker task status and this rollup must agree.

| Bucket | Stages | Count |
|---|---|---|
| ✅ DONE | JPL.1, JPL.2, JPL.3, JPL.3b, JPL.4, 5-A.1, 5-A.2, 5-A.3, 5-A.3 gap (#34), 5-A.4, 5-A.5, 5-A.6, 5-A.7, 5-B.1, 5-B.2a, 5-B.2 (#39) | 16 |
| 🔵 IN PROGRESS | — | 0 |
| ⏳ PENDING | JPL.5 (#25, remaining half = 5-B.3 lowering + `MAX_WORDS`), JPL.6 (#26), JPL.7 (#27) | 3 |
| **Total** | | **19** |

The row that used to sit here — "⏳ UNNUMBERED follow-up: `expand_it`" — became numbered
stage **5-A.7** and is now DONE, which is the only scan-side work that stood between the
rewired kernel and the emitter.

All four 2026-10-04 items closed, the last of them by measurement rather than by
argument.  **#35** landed as new layer **L8** (`sh_jpl_run_c.v`): `step_c`/`mrun_c`/
`host_c` call the proved tail loops, so 5-A.2/5-A.3's deliverables are no longer dead
code inside the artifact — `mrun_c`'s closure holds **5** fuel-bounded tail loops where
`mrun`'s holds 2, and only `getv_it` stays unreachable.  Two surprises the rewiring
produced, both recorded rather than smoothed over.  (i) The agreement with the reference
machine is **necessarily conditional**: `step_c_ok` reads "`step_c g <> Olimit ->
step_c g = step g`", because L2's `match_any` decides at a *linear* fuel threshold while
`match_any_iter` needs a *quadratic* one, so the kernel guards each `case` site and reads
a refused guard as saturate-to-error.  L8 §6 exhibits the command that separates the two,
which makes "there is no unconditional `step_c = step`" a proved fact rather than a failed
attempt.  (ii) The predicted drop from 10 structural recursions to 8 did **not** happen;
it measured **10 → 11**, because the guard is not free (`branch_need`, `forallb`) and the
caps are checked with `length`.  Every budget #35 spends is now proved *least* rather than
merely sufficient — `guard_fuel_is_least` (1537 is attained by a worst-shaped branch, so no
smaller uniform site fuel decides every in-caps branch), `glob_fuel_is_tight` /
`fuel_top_at_caps` (`GLOB_FUEL` *is* `fuel_top` at two full-width words),
`max_fuel_margin_eq_MAX_CMD` (the allowance above the deepest scan is exactly `MAX_CMD`) —
and `enter_case_c_chain_clear` proves a legitimate branch chain never meets the guard at
ample fuel, so the guard protects against out-of-budget inputs instead of taxing normal
ones.  Soundness stayed unconditional throughout (`mrun_c_ok`, `host_c_sound`), which is
the asymmetry that makes the conditional headline safe to ship.  The earlier 2026-10-04
closes stand as recorded: #34 (glob's completeness half, §4.3), the sizing decision
(`GLOB_FUEL` = 132 353, `MAX_FUEL` = 136 449), and #33 (a gate rung and a vendored
artifact).

**5-A.7 (#37) closed the scan side.**  `expand_it` landed as `sh_jpl_scan.v` §6 and is
wired at both of L8's expansion sites, and the result that decides how the emitter has to
be scoped is that its agreement with the reference carries **no hypothesis**: the loop
mirrors L2's fuel decrements one for one, so where 5-A.6 needed a guard and two raised
budgets, 5-A.7 needed neither and **no capacity constant moved**.  The mutual fixpoint
`expand`/`expand_name`/`expand_brace` is out of the shipped kernel's closure (it stays in
the artifact only under the `run`/`step`/`mrun` oracle roots, which is what parity compares
against), the one new recursion it admits is `rev` — a one-pass copy bounded by `MAX_WORD`,
not a scan — and the kernel's residual is now exactly the class §6.1 assigns to the
emitter: six fuel-bounded tail loops, two print-only aliases, nine length-bounded
structural recursions.  The `getv_it` question this stage inherited is answered *keep*, and
the answer is measured rather than argued: `getv_it` is reached from the extraction root
`be_getv` (fuel = `be_len`, the length the bounded carrier already holds) and not from
`mrun_c`, because `expand_go` calls concrete `getv` deliberately — L2's `getv` is already a
forward tail scan, so routing substitution through `getv_it` would have created a second
encoding of one scan without removing a recursion, which is the parallel-encoding failure
mode §2's single-source rule forbids.

**5-B.1 (#38) opened the emitter side, and opened it by reading rather than writing.**
The stage is `verify/c/jpl_front.ml`: parse the extracted artifact with the compiler's own
`Parse`, resolve `.mli` signatures onto bindings, take the transitive closure from named
roots, classify every expression/pattern constructor against a declared subset, and
recognise `ExtrOcamlNatInt`'s nat-destruct value as a *switch* rather than a call (the
distinction 5-A.5 flagged and 5-B.1 now enforces: `nat2text`, `enter_seq` and `step_cmd_c`
contain that value with **zero** self-calls, so "does this binding recurse" is a question
about the binding, not about the presence of a `fun fO fS n -> …` term).  Three things it
produced were not assumed.  (i) The closure was re-derived by a **second method** — a text
identifier graph over the same bytes, comments stripped, `mrun_c,step_c` as roots — and it
returns the **same 47 names and the same 17 recursive ones**, set-equal, not merely
count-equal.  That cross-check also corrected 5-A.7's row, which recorded **45** members for
the same root: its edge rule was narrower than an identifier graph, so the count was low by
2 while its *recursive* split (6 + 2 + 9 = 17) was right, which is why the error survived —
the plan only ever reasoned about the 17.  (ii) Running the *same*
tool on the oracle roots fails on the mutual `expand` fixpoint — which is the measurement
behind §9.2's decision 1, now asserted by the gate in both directions (block 2d positive,
2d-negative refuses).  (iii) Its type-vocabulary section refuted §6's "fixed arrays + a
length field": `cmd`, `frame` and `stack` are recursive value types, so the C99 encoding
must be handles into a static node pool, and the emitter's real open question narrowed from
"which representation" to "**what reclaims cells between steps**" — recorded as decision 3,
with the `free`-free answer (step-boundary copying collection) and the fact that its
per-step allocation bound is not yet established by proof *or* measurement.

**Current front:** JPL.5 (#25), and inside it **5-B.3 — the lowering half**.  L1–L8 are
axiom-free and the shape JPL.5 reads is now the shape that is proved: `sh_run_c.ml`
extracts from `sh_jpl_run_c.v` + `sh_jpl_run_phase3.v` + `sh_jpl_run.v` + `sh_jpl_scan.v`
under the JPL settings, **66** parity checks bind it to the reference oracle, block 2c's
`diff -q` binds the vendored bytes to that extraction, block **2d (5-B.1)** reads those
same bytes the way the emitter has to — the typed closure from `mrun_c,step_c`, classified
construct by construct, refused if anything in it is outside the declared subset — and
block **2e (5-B.2)** now turns that closure's types into the C99 header the host will
compile against: 40 layouts, each size checked by the compiler, and all nine capacities
cross-checked between a syntactic constant fold and the OCaml runtime evaluating the same
extracted term.  Of the decisions open at JPL.5's opening, two are **settled by
measurement** and one is **half-settled, with the remaining half now named by a missing
constant rather than by a design choice**:

1. ~~Which root JPL.6's Rule-6 (no-recursion) lint binds~~ — **closed 2026-10-04 by 5-B.1,
   mechanically.**  The answer was already "the shipped roots", but 5-B.1 turned that from
   an argument into a *root-sensitive* result the gate asserts in both directions: over
   `mrun_c,step_c` ⇒ **SUBSET OK**, and over the oracle roots
   `run,step,mrun` it reports `OFF-SUBSET mutual fixpoint: expand, expand_name,
   expand_brace, run, run_seq, run_for, run_case` and exits 1.  Block 2d-negative pins the
   refusal, because a lint that accepts every root is not a gate.  The measured shape:
   artifact **81** bindings / **76** signatures / **14** type declarations *(the current
   artifact reads **87 / 81 / 15**; 5-B.2a's `jpl_caps_table` export added the record type
   and its accessors — see §9.1's 5-B.1 row)*; shipped closure
   **47** bindings / **17** recursive — and that closure was re-derived a second way (a text
   identifier graph over the same bytes) which returns the **same 47 names and the same 17
   recursive names, set-equal**, so the residual is cross-checked rather than single-sourced.
   The re-derivation also corrected §9.1's 5-A.7 row, which recorded **45** members for the
   same root: its edge rule was narrower than an identifier graph, so the count was low by 2
   while the *recursive* split every claim rests on (6 + 2 + 9 = 17) was right — which is why
   the error survived three stages of being quoted.  **2** mutual `let rec` groups exist in
   the file and **0** inside the shipped closure — exactly the distinction the lint needs.
2. ~~Whether `expand_it` precedes the emitter~~ — **closed 2026-10-04 by 5-A.7.**  The
   question was live because `expand`/`expand_name`/`expand_brace` form a **mutual**
   fixpoint, and eliminating mutual recursion is an algorithmic transform rather than the
   "pure layout" JPL.5 was scoped to be; the alternative was one more Coq stage, which is
   the trade 5-A.2/5-A.3 already made for `glob`/`match_any`/`setv`.  That stage is now
   done, so the emitter faces only tail loops and bounded structural recursion, and the
   critical path is JPL.5 → JPL.6 → JPL.7 with no scan-side prerequisite left.
3. **How a bounded OCaml list becomes a C99 value** (C99 has no GC).  5-B.1's TYPE
   VOCABULARY section answers the first half of this without any choice at all: `cmd`,
   `frame` and `stack` are **recursive** value types (`Seq of cmd * cmd`, `If of cmd *
   cmd * cmd`, `For of text * text list * cmd list`, `Case of text * (text list * cmd list)
   list`, `stack = frame list`), so an inline fixed-capacity encoding of them has no finite
   size at any value of the caps — "flat arrays everywhere" (§6's first phrasing) is
   **refuted by the artifact**, not by preference.  What is left is a **handle + node pool**
   for the recursive types, with `text` the one type free to be an inline `MAX_WORD`-element
   run, and the open sub-question is *reclamation*: the extracted kernel is purely
   functional, so cells are never mutated in place and a pool that only grows cannot last
   `MAX_FUEL` steps.  The plan's "no GC (static pools only)" is therefore read as a
   **copying collection at the step boundary** — a fixed two-space pool, forwarding via the
   handle table, whose bound is the live-set size (derivable from the LOCKED caps) rather
   than the run length.  Sizing input, as 5-B.1 estimated it on the LOCKED caps (a word cell
   = 4-byte length + `MAX_WORD` bytes = 260 B, a node = tag + ≤ 4 handles = 16 B): a live env
   is `MAX_ENV` pairs of words = 128 × 2 × 260 ≈ **65 KiB**, one branch site's pattern list is
   `MAX_LIST` words = 1024 × 260 ≈ **260 KiB**, `MAX_CMD` cmd nodes ≈ **64 KiB**, `MAX_STACK`
   frames ≈ **128 KiB** — so the worst-case live set is about **half a MiB**, which is the
   pool's order of magnitude, while the *per-step allocation* is what the differential
   harness has to *measure* (JPL.7), not assume.
   **5-B.2 (2026-10-04) settled the representation half by deriving it** — §6's rules R1–R8
   are now `verify/c/sh_run_jpl.h`, gate block 2e checks it, and §6.2 numbers the three
   choices the derivation could not make.  Two of 5-B.1's arithmetic inputs changed under
   measurement, and the header is the authority, not this paragraph: a `jpl_text` is
   **1028 B, not 260 B**, because R1 keeps every field one word and R2's codes stay
   `uint32_t` (the model *intends* each code `< 256` and never proves it, so narrowing to a
   byte would be an unproved claim — see §6's table); and the live set is **not** bounded by
   the caps once words are counted, because `MAX_CMD` nodes can each own a `MAX_LIST`-word
   list, so 5-B.1's "half a MiB" is a *sum of single-kind bounds*, not a simultaneous worst
   case.  Measured instead, from the derived pools: the bounded static total is
   **187.0 KiB** (env 3.0 KiB + three `MAX_LIST` kinds at 16.0 + 16.0 + 24.0 KiB + frame list
   128.0 KiB), every cell count printed as "n cells × headroom 2".  What is left open is
   exactly two things, and each now has an owner: **(a)** the word slab has *no* capacity —
   the model owes `sh_jpl.v` §1 a `MAX_WORDS` with a proof, then an export through
   `jpl_caps_table` the way 5-B.2a did for the other nine, and until then the header declares
   `extern jpl_text jpl_word_pool[];` undimensioned and 5-B.3 can lower every control flow
   but cannot link; **(b)** the per-step allocation bound, which §6.2's headroom 2 explicitly
   holds as a placeholder, to be replaced by 5-B.3's allocation census and JPL.7's measured
   high-water mark.  The stage that was tracked here as **5-B.2 / task #39** is DONE; the
   remaining half lives under JPL.5 (#25) as **5-B.3**.  Strength, restated: the recursivity
   that forces the handle encoding is **read off the artifact's own type declarations** (a
   definition, so certain), the 187.0 KiB and every cell size are **checked by the compiler**
   (34 `typedef char jpl_check_*[…]` array-bound assertions cover all 40 emitted types: each
   aggregate row by itself, the one-word typedefs as a family, every cap relation and the word
   width), the word range 4 096 … 4 194 304 live words is **arithmetic on LOCKED caps**, and
   the per-step allocation bound is **not established either way**.
   **5-B.2a (2026-10-04) closed the input side of this decision**: a layout that allocates
   against `MAX_CMD`/`MAX_STACK` needs those numbers *in the artifact*, and four of the nine
   §4.1 caps were not there because only proof code mentioned them.  `sh_jpl.v` §1.1 now
   exports the complete table as `jpl_caps_table`, field-pinned against the LOCKED literals
   by `jpl_caps_are_locked`, and the extraction driver carries it, so the emitter reads every
   cap from the same bytes it reads every function from and holds no cap of its own — a
   claim the gate now checks rather than asserts: block 2e's differential fold compares the
   emitter's *syntactic* reading of those nine literals against the OCaml runtime
   *evaluating* `jpl_caps_table`, and the emitted `#define`s must equal both.

**Verification state (the empirical net that makes DONE credible):**

| Check | Status | Where |
|---|---|---|
| Models gate (coqc + coqchk ×8 + 3 extraction blocks + the two emitter rungs) | **15/15 green** (11/11 until 5-B.1 added block 2d + its negative control → 13/13; 5-B.2 added block 2e + 2e-negative → 15/15) | `verify_models.sh` |
| Emitted C99 header compiles under the strict JPL flag set | **measured** — `clang -std=c99 -Wall -Wextra -Wconversion -Wsign-conversion -pedantic -Werror -fsyntax-only` clean over `verify/c/sh_run_jpl.h`; **34 compile-time assertions cover all 40 emitted types** (27 rows carry their own `sizeof` check, 13 one-word typedefs are covered by `jpl_check_one_word_families`, plus 5 cap relations and the word width), so a wrong byte count is a build failure, not a stale comment | `verify/c/jpl_emit.sh` check 2, gate block 2e |
| The nine capacities agree across the artifact, the fold and the header | **measured** — a probe that carries no number reads `Sh_run_c.jpl_caps_table` at runtime; the emitter's syntactic fold of the same term must match it name-for-name, and each value must appear as `#define JPL_<NAME> <value>u` in the emitted header | `verify/c/jpl_emit.sh` check 3, gate block 2e |
| The layout layer is root-sensitive too (has teeth) | **measured** — roots `run,step,mrun` ⇒ `FATAL: tn: a function-typed value has no layout`, exit 1; the refused value is the oracle cluster's driver parameter (`type run_phi = int -> text list -> cstate -> cstate option`), a *different* reason than 2d-negative's mutual-fixpoint refusal | gate block 2e-negative |
| Vendored representation evidence is byte-identical to a fresh emit | **measured** — `verify/c/sh_run_jpl.h` + `verify/c/layout.txt` regenerated and `diff -q`'d (`JPL_REGEN=1` to re-pin) | `verify/c/jpl_emit.sh` check 4, gate block 2e |
| Shipped closure inside the emitter's declared subset, over the vendored bytes | **measured** — `SUBSET OK` over roots `mrun_c,step_c`; inventory byte-compared against `verify/c/closure.txt` | `verify/c/jpl_front.sh`, gate block 2d |
| The subset check has teeth (root sensitivity) | **measured** — roots `run,step,mrun` ⇒ `OFF-SUBSET mutual fixpoint: expand, expand_name, expand_brace, run, run_seq, run_for, run_case`, exit 1 | gate block 2d-negative |
| `glob_it` soundness vs L2 `glob` (arbitrary input, no fuel hypothesis) | proved — `glob_it_sound`, `glob_iter_sound`, `glob_iter_accepts_glob`, `match_any_iter_sound` | `sh_jpl_scan.v` §4.2.3 |
| `glob` ↔ `gmatch` at linear fuel `S (len pat + len str)` | proved — `glob_iff_gmatch`, `glob_fuel_mono` | `sh_jpl_scan.v` §4.2.2 |
| `glob_it` **completeness** (a real match is always found) | **proved** — `glob_it_complete` / `glob_iter_complete_at` at `fuel_top`, arbitrary `pat`/`str`/`bk`, induction on fuel over all six sites | `sh_jpl_scan.v` §4.3.8–§4.3.12 |
| `glob_iter` ↔ L2 `glob`, two-sided at their own budgets | **proved** — `glob_iter_iff_glob` | `sh_jpl_scan.v` §4.3.12 |
| `match_any_iter` ↔ L2 `match_any`, two-sided | **proved** — `match_any_iter_iff_match_any` (via `gmatch` as the middle term) | `sh_jpl_scan.v` §4.3.13 |
| loop's quadratic budget covered by the L3 constants | **proved** — `fuel_top_le_glob_fuel` (`lengths ≤ MAX_WORD ⇒ fuel_top ≤ GLOB_FUEL`), `cap_fuel_order` (`MAX_STACK ≤ GLOB_FUEL ≤ MAX_FUEL`), `b_fuel_accepts_glob_fuel`, and the machine-facing `glob_iter_glob_fuel_complete` / `glob_iter_max_fuel_complete` / `match_any_iter_in_budget` | `sh_jpl_scan.v` §4.3.14, `sh_jpl.v` §1–2 |
| `step_c` agrees with `step` wherever nothing saturates (**the headline**) | **proved, conditionally** — `step_c_ok`; the condition is *necessary*, and §6 exhibits the separating command | `sh_jpl_run_c.v` §2 + §6 |
| `mrun_c`/`host_c` sound without hypothesis, complete under `no_sat` | **proved** — `mrun_c_ok`, `mrun_c_done_sound`, `mrun_c_eff_sound`, `host_c_sound`, `host_c_bok_is_host_bok` / `host_c_agree`, `host_c_complete`, `host_c_iff_run` | `sh_jpl_run_c.v` §3–4 |
| The budgets the rewired kernel spends are **least**, not merely enough | **proved** — `guard_fuel_is_least` (1537 attained, via `branch_need_repl`/`branch_need_worst_case`), `glob_fuel_is_tight`/`fuel_top_at_caps`, `max_fuel_margin_eq_MAX_CMD` | `sh_jpl_run_c.v` §5 |
| A legitimate `MAX_LIST`-branch chain never fires the guard at ample fuel | **proved** — `enter_case_c_chain_clear` (under the `expand ≤ MAX_WORD` hypothesis L2 cannot supply; `expand_c` supplies it as a cap check on the result) | `sh_jpl_run_c.v` §5.3 |
| The shipped driver is first-order (no closure in the loop) | **proved by typing** — `Example mrun_c_closure_free : mrun_c_type := mrun_c` | `sh_jpl_run_c.v` §7 |
| `expand_it` ↔ L2 `expand` — **agreement at every fuel, no hypothesis** | **proved** — `expand_go_correct` (the state invariant, induction on fuel) then `expand_it_correct`; no guard, no side condition, no raised budget | `sh_jpl_scan.v` §6.1–6.3 |
| The expander's observable behaviour | **computed** — 10 behavioural Examples (name, lone `$`, `${a}`, `$?`, unset brace, `{$a}`, status 127, zero fuel, no re-scan of a substituted value) + 4 equalities against the reference at deliberately low fuel, over `text = list nat` byte encodings | `sh_jpl_scan.v` §6.4 |
| Rewired kernel reproduces phase3's §7 surface, and consumes the proved loops | computed Examples + call-graph census measured twice independently (**6** fueled tail loops live in `mrun_c`'s closure: `mrun_c`, `enter_case_c`, `setv_it`, `match_any_iter`, `glob_it`, `expand_go`; `expand`/`expand_name`/`expand_brace` gone; `getv_it` live from the `be_getv` root only) | `sh_jpl_run_c.v` §1/§6, `sh_run_c.ml` |
| Extraction parity (recursive + iterative + clean/JPL-settings, both drivers) | 26 + 26 + **66** (the D5 block gained `expand_it`'s point checks and two fuel × word sweeps against L2's `expand` (135 comparisons each, **270 over both**)) | `sh_run_parity.ml`, `sh_run_iter_parity.ml`, `sh_run_c_parity.ml` |
| Axiom-freedom (every `.v`) | four `<none>` | `coqchk -o -silent` |
| POSIX conformance vs `/bin/sh` | 33/33 | `verify/src/conformance.sh` |

> Rationale, provenance and the live toolchain probes behind path (A) are the
> dated record in
> [HISTORY — development record and hints](#history--development-record-and-hints)
> ("JPL.5 — PRECONDITION AUDIT", "JPL.5 path chosen: (A)", the `5-A.*` notes). This
> section is the normative dependency chain; HISTORY is why it is shaped this way.

---

## HISTORY — development record and hints

Chronological record of dated decisions, build milestones, and live validation
probes. Sections 1–9 above are the standing design; this section is how the design
was built and what was verified empirically, kept so future work can trace the
rationale without polluting the normative spec.

### 2026-10-03 — decisions locked (provenance for §2, §4)

- **Saturate-to-error** overflow policy chosen over modular wraparound (principle 5).
- **Capacity defaults** (`MAX_*` in §4.1) confirmed as proposed.  Two of them moved
  on 2026-10-04 (see the `JPL.5-A.6 precondition` entry below): `GLOB_FUEL` added,
  `MAX_FUEL` raised from the flat 4096 to `GLOB_FUEL + 4096`.  The rest are still
  exactly as locked here.
- Supersedes the earlier "transpile `sh_run.ml` directly" plan, which violated the
  JPL D-60411 *shall* rules.

### JPL.2 — DONE (2026-10-03): verify/models/sh_jpl.v

`sh_jpl.v` is the bounded data layer, axiom-free (`coqchk -o -silent` → four
`<none>`), built *alongside* `sh_concrete.v` (which it `Require Import`s only as
the reference for the behavioural-isomorphism Examples — no re-implementation of
the byte scans).  It is wired into `verify_models.sh` as a 4th Coq gate; the
models gate is 4/4 and src conformance stays 33/33.

What it establishes (the contract JPL.3 must consume, not restate):
- §1 capacity constants `MAX_*` (LOCKED values), plus `cap_order` proving every
  cap `<= MAX_STACK < 2^32` so no bounded value can wrap the uint32 word.
  *(Amended 2026-10-04 — see the §4.1 table: `GLOB_FUEL` was added and
  `MAX_FUEL` raised to `GLOB_FUEL + 4096`, so the chain is now split —
  `cap_order` ends at `MAX_STACK` and `cap_fuel_order` continues
  `MAX_STACK <= GLOB_FUEL <= MAX_FUEL`.  The no-wrap argument re-bases on the new
  largest cap, `MAX_FUEL` = 136 449 < 2³¹; the shape of the claim is unchanged,
  only its constant.)*
- §2 `bres A` (`BOk`/`BLimit`) = the saturate-to-error carrier, with `bbind`,
  `bmap`, and `b_fuel` (refuses fuel `> MAX_FUEL`).
- §3 fixed-width arithmetic with a defined overflow policy: `b_add`/`b_sub`/
  `b_mul`/`b_divmod`, each with `*_ok`/`*_limit` characterisation lemmas;
  division by zero is an explicit `BLimit`, not the Coq `div 0 = 0` leak.
- §4 `bword` (byte array + length, cap MAX_WORD) with saturating `mk_bword`,
  `b_push`, `b_app`, and well-formedness lemmas.
- §5 `benv` (array of (name,value), cap MAX_ENV): total `benv_getv`, bounded
  `benv_setv`, `setv_length_le`, `benv_setv_fits` (a not-yet-full map always
  admits an update).
- §6 `bcstate` (bounded status + `benv`); `b_nstat` proven `< 256` via concrete
  `nstat_lt`.
- §7 `cmd_count` (fuel-bounded node estimate over the concrete `cmd`) and
  `cmd_fits` (pool-safety gate at MAX_CMD).
- §8 bounded scan *wrappers* `b_expand`/`b_glob`/`b_match_any`/`b_nat2text`.

SCOPE DECISION (carried into JPL.3): §8's scan helpers are fuel-bounded
*wrappers* around `sh_concrete`'s `expand`/`glob`/`match_any`, not yet iterative
accumulator loops over the array representation.  They fix the observable
bounded contract (reject over-budget fuel; saturate an expanded word past
MAX_WORD) but the actual recursion-elimination — rewriting these into single
tail loops over `bword`/`benv`, plus the `run` machine itself — is JPL.3's job.
JPL.3 must preserve the §8 saturation behaviour and the §9 isomorphism Examples.

### JPL.3 + JPL.3b — DONE (2026-10-03): verify/models/sh_jpl_run.v, sh_jpl_run_phase2.v

`sh_jpl_run.v` is the bounded small-step machine, axiom-free (`coqchk -o -silent`
→ four `<none>`), built *alongside* `sh_concrete.v` and `sh_jpl.v` (it `Require
Import`s both — the concrete `run` as the reference semantics, the `bres`/`BOk`/
`BLimit` carrier).  It is wired into `verify_models.sh` as a 4th Coq gate: models
5/5, extraction fidelity 26/26, src conformance 33/33 all stay green.

Architecture (the recursion-elimination the plan called for):
- **Frames as data**, not closures: an inductive `frame` (FSeq/FAnd/FOr/FBang/FIf/
  FWhile/FWhileBody/FSeqList/FForRest) carrying the *same* semantic fuel `f'` that
  concrete `run` threads, so the machine and the spec stay definitionally aligned.
- **Explicit continuation stack** (`stack := list frame`, head = innermost).  A
  config `CFG cf cc ck cs` = (fuel, optional current cmd, stack, concrete state).
- **`phi` as a DATA effect leaf**: `step` emits `Oeffect idx argv k s` for an
  external command; the host services it and re-enters at fuel 0.  No function
  pointer with a captured environment (JPL-hostile).
- **Non-recursive dispatcher**: `step_cmd`/`step_ret` are one-case `match`es; the
  only recursion is `enter_case` (a fuel-bounded *tail* `Fixpoint` — a CC re-dispatch
  would be off-by-one on fuel because `run phi g (Case)` internally calls
  `run_case (g-1)`).  `enter_seq`/`enter_for` stay non-recursive; their recursion is
  spread across driver iterations via `FSeqList`/`FForRest` frames.
- **Fuel-bounded tail driver** `mloop phi B g`: B is a step budget; each `step` is
  constant work, so `mloop` extracts to a `while` loop.

Soundness (the load-bearing theorem, proven unconditionally over the whole
control surface): a per-step meaning function `frame_run`/`cont_run`/`cfg_run`/
`out_run` folds the stack back into concrete `run`, giving
- `step_preserves : out_run phi (step g) = cfg_run phi g` — every machine step
  preserves the meaning of its configuration;
- `mrun_sound  : mloop phi B g = BOk st -> cfg_run phi g = Some st` — whatever the
  machine returns as `BOk` is exactly what `run` says the starting config means;
- `mrun_correct`/`run_none_mloop_limit` — the initial-config corollaries against
  concrete `run`, including "a rejected run can never be turned into a success".
- §7 re-checks the conformance boundary by computation: eight `Example`s run the
  machine over the And/Or/Seq/Bang/If/While/Assign surface and one ties `mloop`
  directly to `b_of (run ...)` on the pure seam, all `reflexivity`.

COMPLETED in JPL.3b (`sh_jpl_run_phase2.v`, imports this machine, axiom-free):
- **Completeness / liveness**: a well-founded step order `next g g'` (Onext
  successor, or the phi-served `CFG 0 None k s'` re-entry past an Oeffect seam) is
  ranked by a single natural measure `cfg_budget g = btask (pending) + bstack (k)`,
  proved strictly decreasing by `next_decrease`; its converse `prec` is therefore
  well-founded (Wf_nat), and well-founded induction gives
  - `mrun_live    : cfg_run phi g = Some st -> exists B, mloop phi B g = BOk st`;
  - `mrun_complete`/`mloop_iff`/`mloop_sound_complete` — the two-sided agreement
    with concrete `run` at the initial config, the latter stating that past an
    existence-witness budget `mloop` equals `b_of run` for every larger budget
    (via `mloop_ok_monotone`: a reached `BOk` is stable under extra budget since
    the driver is deterministic).  Soundness (sh_jpl_run.v) + this completeness is
    now a genuine iff, so `BLimit` means "genuinely out of budget", not merely
    "not-yet-proven-safe".  The whole `sh_jpl_run_phase2` module passes
    `coqchk -o -silent` with Axioms/`<none>` and keeps the models gate green.

DEFERRED (documented, not silently dropped):
- **Scan-level iterativity**: this machine drives `expand`/`glob`/`match_any` by
  calling the fuel-bounded concrete functions (same as §8's bounded wrappers).  The
  plan's target — those scans as iterative accumulator loops over `bword`/`benv`
  with no self recursion — is JPL.5 work; JPL.3/JPL.4 fix the control-flow
  machine's contract that they must feed.

### JPL.4 — DONE (2026-10-03): extract the iterative kernel + re-validate parity

Delivered the machine *as runnable code* and proved its OCaml behaviour
isomorphic to the already-verified recursive kernel — all additive, no existing
artifact touched destructively.

- **`verify/models/sh_extract_iter.v`** — extraction driver.  It emits `step`,
  `mloop` AND `run` (plus the `pure_phi` seam, `expand`, `glob`) in a *single*
  `Extraction` command, so all five land in one OCaml module sharing one set of
  datatype definitions.  That shared module is what lets the parity harness
  cross-check the iterative machine against the recursive spec by plain OCaml
  equality rather than a second, parallel encoding.
- **Second vendored artifact `src/kernel/sh_run_iter.ml` / `.mli`** — build
  output, never hand-edited, byte-identical to fresh extraction (the gate
  `diff -q`s it as anti-rot).  Additive: the recursive `src/kernel/sh_run.ml` and
  `ush` are untouched and stay green; `dune build` passes with both artifacts
  present (`sh_kernel` library globs them as separate top-level modules
  `Sh_run` / `Sh_run_iter`, no clash).
- **`verify/models/sh_run_iter_parity.ml`** — the 26 §7–§9 fidelity facts, now
  re-run through `mloop` (budget 100000, proven ample for these tiny programs by
  JPL.3b's well-founded step bound, so `BLimit` here only ever means genuine fuel
  exhaustion, mirroring `run`'s `None`).  Every command check asserts the
  three-way agreement in one shot: `mloop == run == the kernel-verified Coq
  literal`, i.e. behavioral isomorphism plus extraction fidelity together.
- **`verify_models.sh` extended** with a "2b. Iterative-kernel extraction" block
  (rebuild dep chain → `coqc sh_extract_iter.v` → anti-rot `diff` → `ocamlc`
  parity → run → assert): models gate is now **7/7 Coq+extraction checks**, with
  **26 recursive + 26 iterative parity checks** all green.

### JPL.5 — PRECONDITION AUDIT (2026-10-03): emitter cannot yet run clean

JPL.5 is the "simple emitter" step, but the audit shows its stated precondition
(the Extraction contract line: "OCaml (tail loops + fixed arrays)") is **not met**
by any current extraction artifact.  I inspected the vendored `src/kernel/
sh_run_iter.ml` (the machine JPL.4 just produced) function by function.  Its
*control driver* is clean — `mloop` (sh_run_iter.ml:698) is a genuine tail loop
→ `while`, and `step_cmd`/`step_ret`/`enter_seq`/`enter_for`/`enter_case` are
non-recursive or tail — but everything it *operates on* still violates the JPL
subset, because the machine was built over the **concrete** data layer, not the
bounded-array `sh_jpl` layer:

- **Peano `nat` + unary arithmetic**: `nat = O | S` (sh_run_iter.ml:2), with
  non-tail structural `add`(:25), `sub`(:34), `eqb`(:43), `leb`(:54),
  `divmod`(:63), `div`(:73), `modulo`(:81); `nstat` embeds a 256-deep unary
  literal (:100).  JPL needs fixed-width `uint32_t`.
- **Heap lists as the data representation**: `text = nat list` (:84); `app` is
  non-tail (:18); `setv` is non-tail (`(k,v') :: setv ...`, :129); `teqb` (:88),
  `getv` (:123) walk cons cells; `cstate.cenv : (text*text) list` (:119).  These
  extract to OCaml cons lists → `malloc` in C.  `sh_jpl.bword`/`benv` only *wrap*
  a `text` list with a length + a wf predicate; the underlying bytes are still
  Peano cons cells, so even that layer does not yield fixed arrays on extraction.
- **Non-tail / backtracking scans**: `expand`/`expand_name`/`expand_brace`
  (:330-376) recurse under `b :: _` and `app`; `glob` (:387) is tree recursion
  with backtracking (`(glob ..) || (glob ..)`); `match_any` (:409) likewise.  This
  is exactly the "scan-level iterativity" the plan DEFERRED out of JPL.3.
- **Closures / function pointers**: `run_phi = nat -> text list -> cstate ->
  cstate option` (:417), `obind` callback (:432), and `mloop` still takes `phi`
  as a *function* and services the effect seam by calling it inline (:698-709).
  The contract requires the seam be DATA (return the effect, let the host loop
  re-enter) — so even the "phi-as-data" invariant is not yet reflected in the
  extracted machine's signature.
- **Structural tree recursion in the spec path**: `run` (:448) and the mutual
  `run_seq`/`run_for`/`run_case` — inherent to the reference `run`, not the
  emitted `mloop`, but they share the same list/nat data, so the whole module
  drags the banned representation in.

Consequence: emitting this OCaml literally produces `malloc` + recursion +
function pointers — instant failures for the JPL lint gate (#26).  Hand-writing a
bounded C kernel instead would violate design invariant 1 ("transforms that make
the C JPL-clean live in the Coq source") and the single-source rule.  So the
"simple emitter" is genuinely blocked on a **bounded-representation, iterative-
scan, phi-as-data** extraction that does not yet exist.

Two ways to clear the precondition (DECISION, see below):

- **(A) Root-cause the source (recommended).**  Add a Coq layer where the machine
  runs over a genuinely fixed-capacity representation that *extracts* to static
  arrays/`uint32`, with `expand`/`glob`/`match_any`/`setv` rewritten as
  accumulator tail loops (glob's backtracking onto a bounded explicit stack), and
  `mloop` returning the effect as data (no `phi` function param).  Re-prove
  agreement with `sh_concrete.run` (axiom-free) and re-run the 26 parity checks
  against the re-extracted kernel.  Then JPL.5's emitter stays truly simple.
  Cost: substantial new Coq (this is the deferred scan-iterativity + array
  re-encoding, promoted to a prerequisite task before the emitter).  Keeps every
  semantic transform inside the verified model.
- **(B) Make the emitter smarter.**  Have the OCaml→C99 emitter itself map
  Peano `nat`→`uint32_t`, `list`→fixed array + length with saturating bounds
  checks, lower bounded structural recursion to copy loops, and glob backtracking
  to a bounded stack, over the *current* extraction.  Cost: the emitter becomes a
  safety-critical transpiler whose correctness is no longer covered by the Coq
  proofs, so trust rests entirely on the differential gate (#27) — and it
  contradicts locked invariant 1.

Note the feasibility wrinkle in both: Coq `Extraction` has no fixed-array/C
backend (only OCaml/Haskell), so "array-based" must mean an OCaml representation
the emitter can read as a bounded store (e.g. a length-carrying record over
`Coq.Array`/`Vector`, or a documented cons→static-pool lowering the source
provably bounds).  This is what (A) must settle in the Coq first.

#### JPL.5 path chosen: (A) root-cause the source (user, 2026-10-03)

The user selected (A): all *behavioral* transforms (tail-loop scans, phi-as-data)
go into a new axiom-free Coq bounded-representation layer that is re-proven to
agree with `sh_concrete.run` and re-runs the 26 parity checks, and only then does
a genuinely simple emitter run on it.  Design invariant 1 ("transforms live in
the Coq source") stays intact; the emitter keeps exactly the one mechanical duty
the original contract already granted it — the *layout* mapping (bounded `list`→
static array + length, `nat`→`uint32`) justified by the Coq `wf_bword`/`wf_benv`
bounds, which is representation, not semantics.

#### Validated toolchain probes (live, 2026-10-03) — de-risks (A)

Two throwaway extraction probes (deleted) settled the load-bearing unknowns:

1. **`nat`→`uint32`**: `From Stdlib Require Import ExtrOcamlNatInt` makes `nat`
   extract to OCaml `int`, `Nat.add`→`(+)`, `Nat.eqb`→`(=)`, `Nat.ltb`→int
   compare, `S x`→`Int.succ`.  So the Peano unary-recursion problem is solved at
   the extraction-config level.  CAVEAT: `Nat.sub`, `Nat.divmod`, `Nat.div`,
   `Nat.modulo` are **not** primitive-mapped by that plugin — they still extract
   to Coq fixpoints (a self-recursive `divmod` walking the dividend), which the
   lint gate bans.  Fix: add explicit `Extract Constant Nat.div -> "( / )"` /
   `Nat.modulo -> "mod"` / `Nat.sub`-as-saturating hooks in the new `.v` (the
   sh_jpl `b_divmod` already refuses div-by-zero to `BLimit`, so the primitive
   `/` is only ever called with a non-zero divisor — the guard that makes the
   constant hook sound).  Fuel/budget loops (`match f with 0|S f'`) extract to a
   clean `if (n==0) … else {n-1}` dispatcher, never to recursion — already fine.

2. **Tail loops**: an accumulator `Fixpoint` with the self-call in tail position
   extracts to a `let rec` whose recursive call is the returned value (verified
   on a membership `w_has_go`, a sum `scan_all_go`, and a fuel-bounded structural
   `w_count_go`).  These lower to a single `while`/`for`.  Confirms JPL.3b's
   earlier probe on the general case.

3. **Residual risk is representation, not control flow**: words/env stay `int
   list` (cons cells) and `nth_error` walks them; cons-patterns `[] | b :: r`
   survive extraction verbatim.  Coq has no array backend, so the *emitter* must
   map the length-bounded `list` to a static array + length, translate `nth_error
   xs i` to `i < len ? xs[i] : default`, and turn cons-matching into an index/
   pointer walk over the array.  To keep that a pure layout (no semantics), the
   Coq source's traversals are written as **index/fuel tail loops** so no
   cons-walking recursion is left for the emitter except the bounded `nth_error`
   it special-cases.

#### (A) sub-plan — prerequisite tasks before the emitter runs

Additive: build alongside `sh_concrete.v` / `src/kernel/sh_run.ml` / `ush`, keep
every existing gate green (invariant 3); the new artifacts are only wired into
`verify_models.sh` as additional gates.

- **5-A.1** Bounded byte-array text `bt` (length-carrying, cap MAX_WORD) with a
  total `bt_nth`, and `teqb`/`nat_digits`/`nat2text`/`expand`/`expand_name`/
  `expand_brace` rewritten as fuel-bounded **tail loops**; axiom-free; each
  agrees with the concrete `sh_concrete` helper on in-budget inputs (isomorphism
  Examples).
- **5-A.2** Bounded env `benv` (already in sh_jpl) gets tail-loop `getv`/`setv`
  over the array rep, agreeing with concrete `getv`/`setv`.
- **5-A.3** Iterative `glob`: the tree/backtracking recursion becomes a
  fuel-bounded scan over an explicit bounded backtrack state (or a proven
  equivalent forward loop); axiom-free isomorphism with concrete `glob`.
  (Hardest proof; the empirical net is the parity + /bin-sh corpus.)
- **5-A.4** phi-as-data driver: `mloop` returns the `Oeffect` as data and does
  NOT take a `phi` function; a host loop services the seam and re-enters.  Keep
  the JPL.3/3b soundness + completeness theorems (restate over the new driver).
- **5-A.5** New extraction `sh_extract_jpl_c.v`: import `ExtrOcamlNatInt` + the
  div/mod/sub constant hooks, extract the 5-A machine → `sh_run_c.ml` that is all
  tail loops + uint32 + length-bounded records + no closures.  Re-run the 26
  parity checks against it (extend the harness) and re-vendor.  Only THEN does
  the JPL.5 emitter (#25) map `sh_run_c.ml` → JPL-clean C99.

#### Mandatory-Coq vs emitter-lowered (scope refinement, 2026-10-03)

Re-reading the extraction contract against the probes, the Coq-side rewrites
split cleanly:

- **Emitter-lowered (no source change needed).**  Bounded *structural* recursion
  — `app`/`++`, `setv` (`(k,v') :: setv ..`), the `expand` group's `b :: _`/
  `nat2text st ++ _`, `teqb`/`getv` — is exactly the shape the contract already
  hands the emitter: "lower bounded structural recursion (length <= MAX) to a
  fixed-array copy loop" and map `nat list`→static array + `nth_error`→index.
  These stay single-source (they reuse `sh_concrete`'s definitions verbatim); the
  `wf_bword`/`wf_benv` length bounds are what make the lowering safe.  So 5-A.1
  is a *bounded-word foundation + contract*, and 5-A.2 (env) is thin: `getv` is
  already tail, `setv` is emitter-lowerable.
- **Mandatory Coq rewrite (the true blockers).**  (1) `glob`/`match_any`: tree /
  backtracking recursion (`(glob ..) || (glob ..)`) is NOT a linear structural
  walk, so the emitter cannot mechanically loop it — 5-A.3.  (2) the `phi`
  closure seam in `mloop` — 5-A.4.  (3) `Nat.sub`/`div`/`mod` extract to Coq
  fixpoints (probe 2) and must be replaced by primitive `uint32` ops via
  `Extract Constant` hooks (div-by-zero already guarded to `BLimit` by
  `b_divmod`) — folded into 5-A.5.

### JPL.5-A.1 — DONE (2026-10-03): verify/models/sh_jpl_scan.v (bounded-word foundation)

`sh_jpl_scan.v` is the bounded-word foundation for the clean extraction,
axiom-free (`coqchk -o -silent` → four `<none>`), built *alongside* `sh_concrete.v`
and `sh_jpl.v` (it aliases `bt := bword` and reuses `b_push`/`b_app`/`mk_bword`/
`teqb` — no re-implementation, per the single-source invariant).  Contents: §1 the
`bt` bounded word + well-formedness + `bt_nil`/`bt_of`; §2 the saturating `bt_push`
write seam; §3 the emitter-lowerable scans kept single-source (`bt_eq = teqb`,
`bt_append = b_app`) plus saturation proofs (`bt_append_full`) and byte-level
agreement Examples that anchor later re-extraction fidelity.  Wired into
`verify_models.sh` as a 6th Coq gate so the axiom-free guarantee cannot rot.  The
mandatory rewrites (iterative `glob`, phi-as-data driver, arithmetic extraction
hooks) are the still-open 5-A.3/5-A.4/5-A.5.

### JPL.5-A.4 — DONE (2026-10-03): verify/models/sh_jpl_run_phase3.v (phi-as-DATA driver)

`sh_jpl_run_phase3.v` removes the last higher-order argument from the kernel loop,
axiom-free (`coqchk -o -silent` → four `<none>`), additively: nothing in
`sh_jpl_run.v` / `sh_jpl_run_phase2.v` was edited.  Two observations made it tractable:

- `step` was **already** phi-free — at an `Ext` leaf it returns the data value
  `Oeffect idx argv k s`.  The only captured `phi` lived inside the tail driver
  `mloop phi B g`, which is exactly what Extraction would emit as a
  captured-environment function pointer (JPL Rules 6 / 29).
- phase2's effect edge of `next` (`g' = CFG 0 None k s'`) is *phi-independent* — any
  successor state qualifies — so `next_decrease` ranks the host's re-entry config
  directly, and the closure-free driver inherits the liveness proof instead of
  re-proving it.

Contents: §1 `dres` (`DDone` / `DEff` / `DLim`) + `mrun B g` (no `phi` at all) and
`host phi B g` (the model of the C main loop: run to a boundary, service one `DEff`,
re-enter at `CFG 0 None k s'`); §2 soundness of each boundary
(`mrun_done_sound`, `mrun_eff_sound` — the latter localises the whole seam
dependence into the returned data); §3 determinism under extra budget
(`mrun_dres_monotone`, `host_monotone`, `mrun_not_dlim`); §4 `mrun_deff_budget` — a
whole `mrun` segment ends on a strictly smaller `cfg_budget`, by composing
`next_decrease` over the `Onext` prefix plus the effect edge; §5 `host_sound`,
`host_live` (completeness by **strong induction on `cfg_budget`** via
`well_founded_induction lt_wf`, seeded from phase2 `mrun_live` and reconciled with
the §3 monotone lemmas because `mrun` budgets per step while `host` budgets per
segment), `host_correct`/`host_complete`/`host_iff_run`, `run_none_host_limit`; §6
the §7 boundary re-checked through the driver — `mrun` reaches `DDone` on pure
control flow with no seam, returns an `Ext` leaf as `DEff` **data**, and `host`
agrees with concrete `run` (`= b_of (run pure_run_phi …)`) on `Seq`/`And`/`If`/
`Case`/`For` including a fuel-starved `For`; §7 `mrun` exhibited as an inhabitant of
the first-order type `nat -> cfg -> dres` (no function argument anywhere).

Gate: wired into `verify_models.sh` (`COQ_MACHINE`) as the 7th Coq row — the gate is
now **9/9 green** (7 × `coqc + coqchk` + both extraction blocks, 26 + 26 parity),
user-approved.  Housekeeping: the retired phase2 development scratch
`scratch_jpl8.v` was deleted (its content lives in `sh_jpl_run_phase2.v`).

Next front: **5-A.2 (#30)** tail-loop `getv`/`setv`, then **5-A.5 (#33)**, which now
has a driver to extract that contains no closure at all.

### JPL.5-A.2 — DONE (2026-10-03): verify/models/sh_jpl_scan.v §5 (iterative env)

`sh_jpl_scan.v` §5 gives the bounded environment emitter-lowerable lookups,
axiom-free (`coqchk -o -silent` → four `<none>`), additively: `sh_concrete.v` was
not touched and `sh_jpl.v` gained only a §5 header-comment correction.  No new gate
row was needed — §5 lives in the already-gated `sh_jpl_scan.v`, so `verify_models.sh`
protects it from rot at once.

Why the rewrite was still required, despite the 2026-10-03 refinement calling `setv`
"emitter-lowerable": the refinement is true *for the emitter*, but it left the
emitter holding a proof obligation the Coq side could discharge for free —
`(k',v') :: setv k v r` is a non-tail append, so the lowered C would inherit either
recursion (Rule 6) or a hidden two-pass copy.  Proving the tail form instead keeps
the loop's bound and its agreement with the reference in one axiom-free file, and
makes 5-A.5 a pure wiring exercise.

Contents: `getv_it` (fuel-bounded cursor scan; the argument list is quantified with
the inducted variable first, `forall m f k`, because Coq's `induction` on a binder
re-introduces the preceding ones) and `setv_it` (same scan carrying the visited
prefix reversed in `acc`, spliced by tail-recursive `rev_append` — the identity
`rev_append (p :: acc) xs = rev_append acc (p :: xs)` is what turns each step into a
`reflexivity`); `*_exhaust` pins `None` as the saturation marker; `getv_it_agree` /
`setv_it_agree` prove agreement for EVERY input that fits the fuel (`<=` for the
read, `<` for the write, since the write may add one cell); the array API
`be_getv` / `be_setv` is then proved equal to sh_jpl's reference `benv_getv` /
`benv_setv` for well-formed `benv`, with `be_setv_wf`, the capacity law
`be_setv_refuses_at_capacity` (at `MAX_ENV`, an absent key yields `BLimit`, never a
silently dropped binding — it needs `setv_length_absent`, the exact-length companion
of sh_jpl's `setv_length_le`), `be_setv_admits` below capacity, and
`be_getv_be_setv_same` as the write-then-read law stated purely inside the bounded
API; ten byte-level Examples anchor the mnemonics (97 a, 98 b, 99 c, 100 d, 101 e).

Gate: **9/9 green** — unchanged shape (7 × `coqc + coqchk` + both extraction blocks,
26 + 26 parity), because the stage added no new file.

Still open, and deliberately *not* done here: `be_getv`/`be_setv` are proved but not
yet *consumed* — nothing extracts them until 5-A.5 wires `sh_jpl_scan.v` +
`sh_jpl_run_phase3.v` into `sh_extract_jpl_c.v`.  Until then the vendored
`src/kernel/sh_run_iter.ml` still shows `let rec getv` / `let rec setv` (lines
123/129), which is the correct state for an ungated reference layer.

Next front: **5-A.5 (#33)** — clean extraction of the closure-free, tail-loop
kernel.  Doc gaps closed in the same audit pass: §9.1's 5-A.1 row still carried its
pre-refinement scope and was corrected to "foundation + contract", with the `app` /
`teqb` / `nat_digits` / `expand`-group structural recursion now recorded explicitly
as the JPL.5 emitter's obligation on the 5-A.5 row; and §9.1's 5-A.3 row claimed an
"isomorphism with concrete `glob`" that §4's own banner does not deliver (its
`gi_matches_concrete_*` checks are `reflexivity` on parity's literals, i.e. sampled).
Both rows now say what is actually proved.  Proving `glob_it` ⟷ `glob` for arbitrary
in-budget input — the §5-style generalisation, most likely by generalising the
lemma to an arbitrary `bk` cell and inducting on fuel — is tracked as **task #34**,
not silently assumed.

### JPL.5-A.5 — IN PROGRESS (2026-10-03): verify/models/sh_extract_jpl_c.v + sh_run_c.ml + sh_run_c_parity.ml

This stage turned out not to be pure wiring, and the way it failed to be pure wiring
is the useful result.  `sh_extract_jpl_c.v` extracts the phase-3 surface
(`mrun`, `step`, `dres`, `cfg`, `out`, `run`, `pure_run_phi`, `expand`, `glob`, and the
5-A.2/5-A.3 tail loops `getv_it`/`setv_it`/`be_getv`/`be_setv`/`glob_iter`/
`match_any_iter`) under `ExtrOcamlNatInt` + four arithmetic hooks, producing
`sh_run_c.ml`/`.mli`.  What the artifact now says:

- `type text = int list` — `nat` is a machine `int` end to end, so the emitter never
  sees a Peano unary numeral.
- `mrun` emits as **one tail loop with no functional argument**, confirming 5-A.4's
  phi-as-data driver is what extraction consumes:
  `let rec mrun b g = nat_case (fun _ -> DLim) (fun b' -> match step g with … ) b`.
- `Coq`'s nat elimination prints as the lambda `(fun fO fS n -> if n=0 then fO ()
  else fS (n-1))` at **20** sites.  It is a *value*, passed to `mrun`/`step`/
  `enter_case`; JPL.5 lowers it to `if (n == 0)`, and JPL.6 must not flag it as
  recursion.
- Three bindings print as `let rec` but are aliases of primitives — `add = (+)`,
  and inside `module Nat` `sub = (fun x y -> Stdlib.max 0 (x - y))` and
  `divmod = (fun x y _ _ -> (x / y, x mod y))`.  A lint that greps `let rec` would
  report three false Rule-6 violations, so the check is "is the RHS a saturated
  primitive/fun-literal", not "does the binding use `rec`".  `divmod` is hooked even
  though nothing in the surface calls it: unhooked, Extraction *defines*
  `let rec divmod` with real Euclidean recursion, and that would be a true violation
  shipped in a file that otherwise passes.
- Div-by-zero on the hooked operators is closed by reachability, not by prayer: the
  only literal divisors in the extracted surface are 256 (`nstat k := k mod 256`,
  `sh_concrete.v:94`) and 10 (`nat_digits`, `:206`); every variable- divisor path goes
  through `b_divmod`, which guards `Nat.eqb b 0` → `BLimit` (`sh_jpl.v:142–143`).
  `host` is deliberately *not* extracted — it is the C side's job (JPL.7), and
  extracting it would put the OCaml `Some`/`match` driver in the emitter's input.

**Toolchain gotcha that cost the most time, recorded because the failure is silent:**
`Arith` and `PeanoNat` must be required *before* the `Extract Constant` lines.  With
`ExtrOcamlNatInt` imported first and `Nat.div` required afterwards, Coq accepts the
hints, extraction succeeds, and the artifact still contains the recursive `divmod` —
no warning, no error.  `Extract Inlined Constant` is not the fix; ordering is.  The
`sh_extract_jpl_c.v` header states this and the file's `From Stdlib Require Import
Arith. / PeanoNat.` lines are load-bearing, not stylistic.

**Recursion inventory — measured with a call graph over the artifact, not eyeballed**
(25 `let rec`/`and` bindings emitted):

| Set | Count | Contents |
|---|---|---|
| in `mrun`'s closure | 15 | 2 tail loops (`mrun`, `enter_case`) · 3 primitive aliases (`add`, `sub`, `divmod`) · **10 genuine structural recursions** (`teqb`, `app`, `getv`, `setv`, `nat_digits`, `expand`, `expand_name`, `expand_brace`, `glob`, `match_any`) |
| in `run`'s closure only | 4 | `run`, `run_seq`, `run_for`, `run_case` — the L2 reference oracle, extracted because parity asserts `host == run` |
| reached from neither | 6 | `length`, `rev_append`, and **the four proved tail loops** `glob_it`, `match_any_iter`, `getv_it`, `setv_it` |

So 5-A.2's and 5-A.3's deliverables are correct and dead: `step` still calls the
concrete scans at exactly **6 sites** — `setv` ×3 (`sh_run_c.ml`:1101 `bind_word`,
:1148/:1156 `step_cmd`'s `Assign` arms), `match_any` ×1 (:1133 `enter_case`), `expand`
×2 (:1101, :1133) — and concrete `getv`/`glob` enter the kernel only *through*
`expand`/`match_any`, never directly.  `setv` and `setv_it` now sit side by side in one
artifact, which is the clearest possible statement of "proved but not consumed".
That is stage **5-A.6 / #35**.  Its acceptance test is the same call graph, re-run,
and the measured prediction is *conversion*, not elimination: `setv`, `match_any` and
(through `match_any` alone) `glob` leave `mrun`'s closure, while `rev_append` and
`length` enter it — the extracted `setv_it` splices its reversed prefix with
`rev_append` (`sh_run_c.ml`:1316/1320, an *unfueled* tail recursion, so it lowers to a
plain `while`) and `be_setv` computes `length m` **twice** (:1334–1335).  Fueled tail
loops go 2 → 5 (`mrun`, `enter_case`, `getv_it`, `setv_it`, `match_any_iter`),
structural list recursions 10 → 8 (`teqb`, `app`, `getv`, `nat_digits`, `expand`,
`expand_name`, `expand_brace`, `length`).  Two consequences the plan had not stated:
`be_setv`'s two `length` calls recompute what `benv` already carries as `be_len`, so
the bounded API should return the length with the map rather than rescan it — fixing
that also removes `length` from the kernel closure; and *no* amount of scan rewiring
reaches zero recursion, because the `expand` group stays structural — that group, not
the scans, is the JPL.5 emitter's real remaining obligation.

*Re-measured on 2026-10-04 by the 5-A.6 entry at the end of this file.  The tail-loop half of
the prediction hit exactly (2 → 5) and `setv`/`match_any`/`glob` did leave the root; the
structural half did **not** (10 → 11, not 10 → 8), because the guard's `branch_need`/`forallb`
and the cap-checking `length` are new recursions the prediction could not have counted — the
fuel-law mismatch that forced the guard was itself the finding.  The `be_setv` double-`length`
fix advised below also turned out moot: the rewired machine calls `setv_it` directly.*

**The empirical net, green locally:** `sh_run_c_parity.ml` (compiled with
`ocamlc -w -a -o sh_run_c_parity sh_run_c.mli sh_run_c.ml sh_run_c_parity.ml`,
OCaml 5.5.1) prints **34 checks, 0 failed**.  26 of those are §7–§9's facts re-run
through the *int-native* artifact, each asserting `host == verified literal == run`.
The host is hand-written here — a closure-free `let rec host b g = … mrun (b-1) g …`
with `service idx argv = pure_run_phi idx argv` — and that is the stage's real
finding: it is the first *executable* proof that `mrun`'s `DEff (idx, argv, k, s)`
data surface is sufficient to service the OS seam from outside the kernel, with no
function passed in.  JPL.7's C main loop is allowed to rest on that, because it has
now been demonstrated rather than argued.  The remaining 8 checks are tail-loop-vs-
concrete spot checks (`getv_it`/`setv_it`/`be_getv`/`be_setv` roundtrip,
`glob_iter`/`match_any_iter`), which need `gfuel = 64` rather than the concrete
matcher's budget: `glob_it` spends one fuel unit per forward step *and* per backtrack
retry, so fuel does not transfer 1:1 between the two forms — calibrate, do not copy.

Why the row says IN PROGRESS rather than DONE, per §9.2's rule: (i) the artifact is
not yet in `verify_models.sh` — adding a third extraction block changes the gate's
shape (8 → 9 → 10), and gate edits need the user's approval; (ii) the vendoring
question is open — `src/kernel/`'s consumer is `ush`, whereas `sh_run_c.ml`'s consumer
is the JPL.5 emitter, so vendoring it may be a second parallel encoding rather than a
third rung; (iii) with the tail loops still dead code, the artifact is not yet the
kernel the emitter should receive.

### JPL.5-A.3 gap / #34 — PARTIAL (2026-10-04): verify/models/sh_jpl_scan.v §4.2, general soundness

5-A.3's tail loops were delivered with their agreement to L2 `glob` *sampled* (§4.1's
`gi_matches_concrete_*` are `reflexivity` on the literals parity happens to exercise).
This pass replaces that sampling with theorems about arbitrary inputs, in the one
direction that does not need a fuel hypothesis on the loop side.

**The bridge is a declarative spec, not a comparison of two implementations.**
`gmatch pat str` states what a glob means — `[]` matches only `[]`, a literal must
equal the head byte, `?` eats exactly one byte, `*` eats either nothing or one byte
and keeps matching (`gm_star_here`/`gm_star_take`) — and is written independently of
both `sh_concrete.glob` and `glob_it`.  Each of the two matchers is then related to it
separately, which is why the proofs stay small: `glob_true_gmatch` (L2 true ⇒ spec) and
`gmatch_glob` (spec ⇒ L2 true at linear fuel) together give `glob_iff_gmatch`, and the
loop gets `glob_it_sound` ⇒ `ok_it` ⇒ `gmatch` ⇒ L2.  `glob_iter_accepts_glob` is the
statement #35 can actually consume today: whatever `glob_iter` accepts, the reference
`glob` accepts at `S (length pat + length str)`.

**The loop's invariant is disjunctive, and that is exactly the limit of this half.**
`glob_it` carries a saved cell `bk = Some (bps, bstr)`, and entering a *new* `*`
replaces the old cell — the newer star subsumes the older, which is what
`gretry_gmatch_star` (via `gmatch_star_app`: a star eats any leading run) formalises.
So `ok_it pat str bk` = "the forward scan still matches, **or** the cell can still be
drained into a match" is enough for soundness at every one of the loop's six sites.  It
is *not* enough for completeness: the reverse induction must know that the cell and the
forward state come from the *same* derivation (`bstr = h ++ str` and `bps = pre ++ pat`),
otherwise draining the cell says nothing about the original pattern.  Recording that
honestly: the naive disjunction is sound, and completeness needs the linked invariant —
this is the shape of the remaining half of #34, not a missing lemma.

**Fuel: proved linear for L2, measured quadratic for the loop, and the gap is real.**
`gmatch_glob`'s measure is `length pat + length str`, which drops by ≥1 per recursive
`glob` call, so L2 saturates at `S (P+S)` — that is a theorem, and `glob_fuel_mono`
lifts it to any larger fuel.  The loop spends one unit per forward step *and* one per
backtrack retry, so its needs are quadratic; measured (python transcriptions of both
definitions, instruments in scratch):
- differential brute force, 496,860 pairs (pattern over `{a,b,c,*,?}` len ≤ 5 × string
  over `{a,b,c}` len ≤ 5, `glob` at fuel 24 vs `glob_it` at fuel 200): **0 mismatches**;
- fuel-hypothesis check `glob_it ((P+1)(S+1)) == glob (P+S+1)`, exhaustive over pattern
  len < 7 × string len < 8: **17,912,080 cases, 0 violations** — i.e. `(P+1)(S+1)` is
  the sizing law #35 should use for `GLOB_FUEL`, and no counterexample to it was found;
- the smallest input where the *linear* budget suffices for L2 but not for the loop is
  `*a` on `aaa`: `glob 6 [42;97] [97;97;97] = true` while `glob_iter 6 … = false` and
  `glob_iter 7 … = true`.  Those three are now `reflexivity` Examples **in the gated
  file** (§4.2.4), so the bounds are shown to differ against the real definitions and no
  longer rest on the python transcription; the `(P+1)(S+1)` sizing law itself is still
  only *measured* (the scratch instruments were deleted after the run, per the
  no-artifacts-in-the-tree rule), which is why #35 takes it as an input parameter to
  calibrate rather than as a lemma.

**Gate: 9/9 green, shape unchanged** — §4.2 adds theorems to an already-gated file
(`sh_jpl_scan.v`), and `coqchk -o -silent sh_jpl_scan` still reports the four `<none>`
lines.  D5 was re-checked in the same pass because it consumes this file: rebuilding
`sh_extract_jpl_c.v` yields a **byte-identical** `sh_run_c.ml` (proofs add no extraction
surface) and `sh_run_c_parity` still prints 34/34.  The development is constructive
throughout: no `Classical`/`Epsilon` (either would break the four-`<none>` invariant), no
`Axiom`/`Parameter`/`Admitted`/`admit`.
Docs updated in the same pass: §4's banner now separates the proved half from the
sampled one, §9.1 gains a 5-A.3-gap row, §9.2 counts it as PARTIAL, and AXIOTACK's L4
row says "soundness proved for arbitrary input" instead of "cross-checked by
`reflexivity`".

**Rocq 9.2 proof idioms that cost time here, recorded so the completeness pass does not
pay them again:** `Require Import List` is *not* enough for `[]`/`::` — `Import
ListNotations.` is load-bearing; boolean tests (`Nat.eqb`, `||`) can only be `destruct`ed
while the hypothesis is still `revert`ed, and `left`/`right` do not apply to `(A || B) =
true` (`apply orb_true_iff` first); `option` destructs Some-then-None; destructing a
nested pair leaves a `let` in the goal, so follow with `cbn`; `Nat.eqb_ne` does not exist
(carry the `eqn:Ep` hypothesis instead); `apply` cannot instantiate the fuel existential
of a `forall f, … <= f -> …` goal — pass the witness with `exact (lemma args)` or
`refine (… _)`; and `lia` needs `cbn` first whenever the goal still contains
`length []`/`length (x :: l)`.

Next: the completeness half of #34 (linked invariant + `(P+1)(S+1)`), then #35 can be
stated two-sided.

### JPL.5-A.3 gap / #34 — DONE (2026-10-04): verify/models/sh_jpl_scan.v §4.3, completeness

The half the §4.2 entry left open.  `gmatch pat str -> glob_iter (fuel_top pat str) pat
str = true`, for arbitrary `pat`/`str`, plus the two-sided statements #35 consumes:

    glob_iter_iff_glob          glob_iter (fuel_top pat str) pat str = true
                                  <-> glob (S (length pat + length str)) pat str = true
    match_any_iter_iff_match_any  match_any_iter (b + len pats) pats scrut = true
                                  <-> match_any (b + len pats) pats scrut = true
                                    (for any b dominating fuel_top of every branch)

**Why the anchored invariant was the whole job.**  §4.2's `ok_it` is a disjunction, so it
is satisfiable by a cell that has nothing to do with the forward state; the fuel induction
then has nothing to bite on at the install site (entering a new `*` overwrites the cell
with `(ps, str)`, and no relation between the old cell and the new forward state forces
`state_bound` down).  `cinv fwd fws bk` therefore *anchors* the cell: for some star-free
chunk `pre`/`pre'` recorded by `fmatch` (pattern and string advancing byte for byte),
`cp = pre ++ fwd` and `cs = pre' ++ fws`.  Three constructors — `ci_none` (no star seen
yet), `ci_scan` (anchored, forward still matches), `ci_cell` (anchored, cell drainable) —
and five site lemmas: `cinv_install` (a fresh `*`: the older cell's anchored match, hung
on the same lockstep prefix, re-establishes the fresh cell's spec — `gmatch_anchored_star`
is the one place the anchor equation is genuinely consumed), `cinv_forward` (the anchor
grows by the byte pair, `fmatch_app_cons`), `cinv_drain` (the cell gives a byte back:
`drain_gretry` shows the run still has one to give, else cancellation would have unstuck
the forward state), `cinv_nil_cell` (an empty cell string cannot coexist with a stuck
forward state — the anchor forces `pre = pre' = []`), `cinv_none_inv`.

**Supporting layer, written once and reused.**  `fmatch`/`nostar` (star-free lockstep),
`gmatch_hang` (a star-free leading chunk consumes exactly its own length — the workhorse
behind cancellation and the anchor), `gmatch_canc`, `app_prefix` (equal appends nest their
shorter prefix), `gmatch_star_absorb`, `gmatch_one_step`, and `gmatch_gretry_star`.

**Fuel.**  `state_bound pat str bk` adds the cell's own `scan |cp| |cs| = (|cp|+|cs|+1)(|cs|+1)`
on top of the forward state's lengths, so every site strictly lowers it: forward step ≥ 2,
install from `None` = |str|+2, install over a cell ≥ 1 (this is where the anchor's lengths
are needed), drain = |rstr|+3+|pat|+|str|, and every stuck site is reached only under a
`~gmatch` premise, so it never needs the bound at all.  Because `glob_it_complete` is
stated for *every* `f >= state_bound`, the theorem carries its own monotonicity — no
fuel-lifting lemma was needed, which is also what let `match_any_iter_complete` go
through with a bare `b + length pats <= f`.

**Honest limits of this pass.**  (i) `fuel_top` is *sound but loose*: on `*a`/`aaa` it is
29 where the measured minimum is 7, and the tighter `(P+1)(S+1)` law is still only
measured (§4.2.4's `reflexivity` Examples are the only in-tree arithmetic pins).  (ii) The
provable worst-case budget `fuel_top 256 256 = 132 353` sits above the locked
`MAX_FUEL = 4096` — proved-law crossover is P=S=45, measured-law crossover 64 — so #35
cannot reuse `MAX_FUEL` for glob; that is a constants-table decision for the user, and
this pass did not touch `sh_jpl.v` §1.  (iii) Nothing is wired yet: the four tail loops
are still dead code inside `sh_run_c.ml`, so #34's theorems license the #35 rewiring
rather than perform it.

**Gate / D5:** `verify_models.sh` **9/9**, `coqchk -o -silent sh_jpl_scan` four `<none>`,
no `Axiom`/`Parameter`/`Admitted`/`admit` and no `Classical`/`Epsilon`.  §4.3 is proof-only,
confirmed mechanically: re-running `sh_extract_jpl_c.v` reproduces `sh_run_c.ml` and
`sh_run_c.mli` **byte-identically**, and `sh_run_c_parity` still prints 34/34.

**Rocq 9.2 idioms that cost time here** (added to the list in the §4.2 entry, for whoever
repeats this shape): `destruct bk as [|(bps, bstr)]` **silently does not split the pair**
— it leaves a `let` in the goal and warns only about the unused intro pattern; destructure
in two steps (`destruct bk as [q|]` then `destruct q as [bps, bstr]`).  `option`/`bool`
cases are generated Some-first / true-first, so hand-written branch order must match.
`lia`/`nia` need every length normalised *first* (`cbn [state_bound length] in *; unfold scan
in *` as one tactic), and `nia` will not invent the nonnegativity of a product — `n <= n * S m`
is worth its own lemma (`prod_ge`).  `apply X; [ .. | .. ]` brackets cannot contain a bare
`exact`-style tactic sequence with semicolons in a term position (`exact (f (exists a; split))`
is a parse error) — apply the lemma, then prove the witness.  And `exact H` where `H : False`
does **not** close a `false = true` goal: `exfalso` first.

Next: #35 (wire `step_c` onto `glob_iter`/`match_any_iter`/`be_getv`/`be_setv`, decide
`GLOB_FUEL`), then the two open questions on #33 before JPL.5.
*(Superseded on the second clause the same day — see the 2026-10-04 entry below: the
glob budget is decided and implemented, so #35 is pure rewiring.)*

### JPL.5-A.6 precondition — DONE (2026-10-04): fuel budget raised, `GLOB_FUEL` added

User instruction: *"increase budget and add golbal fuel"* — the constants-table decision
§9.2 had handed back to the user, now taken.  Two files changed; no theorem was weakened.

**`sh_jpl.v` §1 (the LOCKED table).**  Added

    Definition GLOB_FUEL : nat :=
      S (MAX_WORD + MAX_WORD) * S MAX_WORD + MAX_WORD + MAX_WORD.   (* 132 353 *)
    Definition MAX_FUEL  : nat := GLOB_FUEL + 4096.                 (* 136 449 *)

`GLOB_FUEL` is **not a literal**: it is `sh_jpl_scan.v` §4.3.9's `fuel_top` evaluated at
two full-width words, written out from `MAX_WORD` so the constant and the law it is sized
from share one expression and cannot drift apart.  `MAX_FUEL` is that budget **plus** the
4096 this layer was originally budgeted for, because `step` threads ONE fuel number both
through its own countdown and into the scans it calls (`sh_jpl_run.v:121` `setv var
(expand g …)`, `:147` `match_any g pats (expand g …)`), so the machine's cap has to cover
the deepest scan it can be asked to run as well as its steps.  No slack is hidden in
`GLOB_FUEL` — the margin is the additive allowance, which is visible and named.

Ordering split to keep both halves cheap: `cap_order` retains the original small chain
`MAX_WIDTH ≤ MAX_WORD`, `MAX_ARGV ≤ MAX_ENV ≤ MAX_LIST ≤ MAX_CMD ≤ MAX_STACK` (one `lia`),
and a new `cap_fuel_order` proves `MAX_STACK ≤ GLOB_FUEL ∧ GLOB_FUEL ≤ MAX_FUEL`.  The
second link is structural (`MAX_FUEL` is `GLOB_FUEL` plus a positive allowance).  The
first is the only closed decision that needs the VM (`apply Nat.leb_le; vm_compute`).
**Toolchain note worth keeping:** a `Definition` whose body is a large decimal literal
(e.g. `262144`) is silently rewritten by Rocq 9.2 to `Init.Nat.of_num_uint 262144`, and
`lia` then treats it as an *opaque atom* — `Goal MAX_STACK <= GLOB_FUEL. lia.` fails with
"Cannot find witness" even though the fact is true.  Defining the cap as a sum/product of
small literals avoids both the atom problem and a 132 353-node Peano term.  Measured cost
of the change: `coqc sh_jpl.v` 0.77 s, `coqchk -o -silent sh_jpl` 8.5 s against a
reconstructed pre-change baseline of 8.0 s — i.e. ≈0.5 s, because §8's
`b_expand (MAX_FUEL + 1)` saturation `Example` now decides `Nat.leb` at 136 450 instead of
4097.  Also new in §2: `b_fuel_accepts_glob_fuel : b_fuel GLOB_FUEL = BOk GLOB_FUEL`, which
is the one-line statement that the raise achieved its purpose (before it, that same fuel
was `BLimit`).

**`sh_jpl_scan.v` §4.3.14 (the sizing, downstream — L4 may see L3, never the reverse).**
`fuel_top_nat`/`fuel_top_as_nat` move the law onto lengths, `scan_mono` (`Nat.mul_le_mono`)
and `fuel_top_nat_mono` give monotonicity in each length, and

    Theorem fuel_top_le_glob_fuel : forall pat str,
      length pat <= MAX_WORD -> length str <= MAX_WORD ->
      fuel_top pat str <= GLOB_FUEL.

goes by transitivity to `fuel_top_nat MAX_WORD MAX_WORD`, which is *definitionally*
`GLOB_FUEL` — so the top case is `Nat.le_refl`, with no numeral evaluated anywhere.  Three
machine-facing corollaries then compose it with §4.3.11–13: `glob_iter_glob_fuel_complete`,
`glob_iter_max_fuel_complete` (a real match between two well-formed words IS found by the
loop at the constant the machine is allowed to carry), and `match_any_iter_in_budget`,
whose fuel `GLOB_FUEL + length pats` is exactly the call shape #35 must emit for a `case`
arm.  Header comments at §4.2.4 and at the head of §4.3 now point at §4.3.14 instead of
deferring the decision, and `sh_extract_jpl_c.v`'s nat→int rationale re-bases from
`≤ MAX_STACK = 8192 < 2^32` to `≤ MAX_FUEL = 136 449 < 2^31`.

**What moved and what did not.**  The cap that grew is the *fuel* cap; nothing about the
representation changed, so `MAX_WIDTH/MAX_WORD/MAX_ARGV/MAX_ENV/MAX_LIST/MAX_CMD/MAX_STACK`
keep their 2026-10-03 values.  The relation `MAX_FUEL ≤ MAX_STACK` (4096 ≤ 8192) that the
old `cap_order` asserted is gone — deliberately: frames bound *nesting*, fuel bounds
*iterations*, and the check that nothing consumed that link came out empty (`cap_order` is
not a premise of any other lemma, and `MAX_STACK` appears in no machine file).  `MAX_STACK`
is therefore documented as `2·MAX_CMD`, which is its actual justification.

**Gate / D5:** `verify_models.sh` **9/9**, four `<none>` on every module including the two
edited ones; no `Axiom`/`Parameter`/`Admitted`/`admit`, no `Classical`/`Epsilon`.  The
constants are outside the extracted surface, confirmed mechanically rather than assumed:
re-running `sh_extract_jpl_c.v` reproduces `sh_run_c.ml`/`.mli` **byte-identically** (66 091
bytes, and `grep` finds no `4096`/`8192`/`MAX_FUEL` binding in it) and `sh_run_c_parity`
still prints 34/34.

**Honest limits.**  (i) The budget is now *proved sufficient*, not *proved minimal* —
`fuel_top` remains loose (`*a`/`aaa`: law 29, measured minimum 7), so a full-word glob is
given far more fuel than it needs; tightening it means proving the `(P+1)(S+1)` law, which
is still only measured.  (ii) `MAX_FUEL` no longer matches ush's 4096 fuel budget, a
deliberate divergence between the shipped OCaml ush and the JPL layer that §4.1 now states
explicitly.  (iii) #35 still has to *use* these constants — `step` keeps calling L2's
`glob`/`match_any`, so `GLOB_FUEL` is not yet referenced by any machine file.

Next: #35 (`step_c` onto `glob_iter`/`match_any_iter`/`be_getv`/`be_setv` at the budgets
§4.3.14 provides), then the two open questions on #33 before JPL.5.  *(Both questions
closed the same day — see the next entry.)*

### JPL.5-A.5 #33 closed — DONE (2026-10-04): D5 is gate block 2c and `sh_run_c.ml` is vendored

User instruction: *"1) wiring D5 into verify_models.sh (9/9 → 10/10) and 2) do
`sh_run_c.ml` 3) continue to #35"* — i.e. the two questions §9.2 had left open were
answered (wire it; vendor it), and #35 is now the front.

**`verify_models.sh` gains block 2c**, structured exactly like 2 and 2b so the three
artifacts are checked by one repeated shape: recompile the chain
(`sh_concrete` → `sh_jpl` → `sh_jpl_run` → `sh_jpl_scan` → phase2 → phase3 →
`sh_extract_jpl_c`), anti-rot `diff -q` the fresh `sh_run_c.ml`/`.mli` against the
vendored `src/kernel/` copies (FAIL prints the `cp` remedy), then `ocamlc` + run
`sh_run_c_parity` and require `passed successfully`.  Three collateral fixes the wiring
exposed, all of them real rot rather than cosmetics:
- the cleanup list never knew about the third artifact, so a run would have left
  `sh_run_c.ml/.mli` and the `sh_run_c_parity` binary in the tree (and `sh_run_c.{cmi,cmo}`
  were already covered by the `*.cmi *.cmo` glob).  Now deletes all of it, plus
  `.nia.cache` — `sh_jpl_scan.v` §4.3 runs `nia`, and that cache had never been cleaned.
- `--help` printed the header with a hardcoded `sed -n '1,46p'`.  Adding the two new
  `Covers:` entries would have silently truncated the help text at the old line count, so
  it now reads `awk 'NR==1,/^# Exit 0/'` — the range ends at a pattern, not at a number.
- the `sh_jpl_scan.v` `Covers:` entry still described the pre-#34 file ("byte-agreement
  Examples anchoring later re-extract fidelity … not yet consumed by the machine").  It
  now states what is actually proved: both-direction agreement for arbitrary input, and
  §4.3.14 sizing L3's fuel from `fuel_top`.

`sh_run_c_parity.ml`'s header likewise stopped describing itself as what "a future
verify_models.sh section would do".

**Vendoring.**  `src/kernel/sh_run_c.ml`/`.mli` (66 091 / 3 666 B) copied from a fresh
extraction, and `src/kernel/dune`'s header rewritten from a single-artifact comment into
the list of all three with their source `.v` files — the comment is what tells a reader
which file each vendored module must be regenerated from.  `dune build` after deleting
`_build` entirely: exit 0, zero lines matching `error`, `sh_kernel.{cma,cmxa}` produced
with `Sh_run_c` in the library.  `ush` is untouched by it — nothing in `src/` references
`Sh_run_c`, which is why the gate byte-check, not the build, is the thing keeping the
vendored copy honest.  `verify/src/conformance.sh` re-run after the copy: **33/33**.

**Gate: 10/10** — 7 × (`coqc` + `coqchk` four `<none>`) + 26 + 26 + 34 parity, each
preceded by its anti-rot diff.  All three extraction blocks report the vendored copy
identical, and the tree afterwards contains no `.vo`, no derived `.ml/.mli`, no harness
binaries and no caches.

**Consequence for #35, recorded so it is not rediscovered:** the artifact is now
gate-checked, so a #35 re-extraction must be followed by
`cp sh_run_c.ml sh_run_c.mli ../../src/kernel/` or block 2c fails on drift.  That is the
desired behaviour — it makes "the file the emitter reads" a verified byte sequence.

**Honest limits.**  (i) Vendoring an artifact no shipped binary consumes is a deliberate
exception to "kill parallel encodings": it is still *derived* (never hand-edited), and the
gate pins it; what it buys is that JPL.5 lowers exactly what was verified.  (ii) Block 2c
checks Extraction faithfulness for the int-native settings and the tail-loop surface only
as far as the harness exercises it — the 8 tail-loop checks are against the concrete
scans, whose agreement Coq already proves; the emitter's own fidelity remains JPL.6/JPL.7's
problem.  (iii) `dune build` still emits pre-existing `ush.ml` Warning 21
(nonreturning-statement) lines and one partial-match warning about `AndOr _`; neither is
from generated code and neither fails the build — noting it so the JPL.6 lint, which is a
*C* gate, is not mistaken for the OCaml warning situation.

### JPL.5-A.6 / #35 — DONE (2026-10-04): the rewiring landed, and measuring it corrected the plan

Framing instruction for the whole session: *"wire everything and reanalyse maybe we will see
some simplification if possible, increase budgets when needed and prove their minimal
bounds"*.  #35 had been scoped as mechanical — copy `step`, swap four names for their proved
tail loops, transport four agreement lemmas, re-extract.  It was not mechanical, and the part
that was not is the reason this entry exists.

**The thing that had to be discovered before any of it could be written.**  §4.3.13's
`match_any_iter_iff_match_any` compares `match_any (b + length pats)` with
`match_any_iter (b + length pats)` under `fuel_top p scrut <= b` — it hands **both** matchers
the same fuel.  `step` does not: it hands the site its countdown `g`.  So transporting that
lemma to a call site needs `g ≥ fuel_top`, and that is exactly where it is false: L2's
`match_any` decides a branch at the **linear** threshold `branch_need`, the loop needs the
**quadratic** `fuel_top`, and between them the loop says `false` while L2 already says `true`.
A naive rewire would not have failed to compile — it would have silently taken the *wrong
branch* of a `case` at low fuel, which is the worst kind of bug this layer can contain because
the answer is well-formed.  Measured rather than assumed: §6's `tree_decides_below_loop_need`
fixes the band with the smallest witness (`[*;a]` on `a-a-a`: L2 decisive at 6, loop needs 29,
all three numbers by `vm_compute`), and `host_c_saturates_where_host_answers` is the same
phenomenon as an end-to-end command.

**Why guard-and-saturate rather than "just hand the loop `MAX_FUEL`".**  That variant is
sound for the answers the loop produces, and it was the first thing tried in reasoning.  It
fails the *contract*: L2 at low fuel is not decisive and answers `false`, while the loop at
132 353 is decisive, so `step_c` would disagree with `step` in the other direction and stop
being a refinement of it; and a `case` whose matcher consumes none of the countdown would
break the single-fuel discipline the whole bounded layer is built on.  The guard keeps
`step_c` an artefact of `step`'s own budget: refuse when the site cannot fund the loop, and
report the same defined error the machine already reports for exhausted fuel.

**What landed, in which layer.**  L4 gained §4.3.15 (`branch_need` and its two-sided link to
`branch_decisive` — `branch_decisive_need` says the threshold is necessary,
`branch_need_decisive` says it is sufficient, so `f = branch_need pats w − 1` genuinely cannot
decide, which is what makes the number minimal instead of convenient — plus `branch_guardb`
and `branch_guardb_match`).  L8, the new file, is the machine: §1 the rewired sites, §2
`step_c_ok`, §3 `mrun_c` + `mrun_c_ok` + the two unconditional soundness theorems, §4
`host_c` with `no_sat` as the single completeness hypothesis, §5 the budget arithmetic, §6
phase3's §7 surface re-produced by computation together with the separating examples, §7 the
first-orderness check stated as a *typing* (`Example mrun_c_closure_free : mrun_c_type :=
mrun_c`) so it cannot rot into a reading of the artifact.

**"Prove their minimal bounds" — done, with one distinction kept visible.**  Three constants
are now pinned as least-possible: `case_site_fuel` = 1537 is *attained* by an in-caps branch
(`branch_need_repl` → `branch_need_worst_case` → `guard_fuel_is_least`), so no smaller uniform
site fuel decides every branch; `GLOB_FUEL` is *definitionally* `fuel_top MAX_WORD MAX_WORD`
(`glob_fuel_is_tight`, `fuel_top_at_caps`); and `MAX_FUEL − GLOB_FUEL = MAX_CMD` exactly
(`max_fuel_margin_eq_MAX_CMD`), i.e. the allowance above the deepest scan is the machine's own
step bound and no padding.  The distinction: `GLOB_FUEL` is "the least value *this law* takes
at the caps", **not** "the least budget the loop can work with" — `fuel_top` is still a loose
upper bound on the loop (measured: `*a`/`aaa` law 29 against a true minimum of 7; at the caps
the tighter measured law `(P+1)(S+1)` gives 66 049, half of `GLOB_FUEL`).  Proving *that*
tightness is a separate result nobody has yet, and the rows say so rather than letting
"tight" read as "optimal".  Sufficiency at the caps is proved (`fuel_top_le_glob_fuel`), and
`enter_case_c_chain_clear` is the lemma that makes the guard cost nothing to a legitimate
program: with `case_site_fuel + length brs ≤ g` and every pattern in caps, no site of the
whole branch chain saturates.

**Measured after-state — where the plan's own prediction was wrong.**  Call graph over the
re-extracted artifact, same script as the 2026-10-03 census.  28 top-level `let rec`/`and`
bindings (was 25).  `mrun_c`'s closure: **18** — 5 fueled tail loops (`mrun_c`,
`enter_case_c`, `setv_it`, `match_any_iter`, `glob_it`), 2 print-only aliases (`add`, `mul`),
11 structural (`teqb`, `app`, `length`, `rev_append`, `forallb`, `getv`, `nat_digits`,
`expand`, `expand_name`, `expand_brace`, `branch_need`).  `mrun`'s closure: **13** — the same
10 structural recursions the pre-#35 measurement counted, so the reference root did not move.
Neither root reaches: 5 — the `run` cluster (parity asserts `host == run`, so it stays
extracted on purpose) plus `getv_it`.  5-A.5 predicted "tail loops 2 → 5, structural 10 → 8".
The first hit exactly; the second came out **10 → 11**.  Three recursions left the root
(`setv`, `match_any`, `glob`) and four entered: `rev_append` from `setv_it` as predicted, and
`branch_need`/`forallb`/`length` **because of the guard and the cap checks** — a cost that did
not exist when the prediction was written, since the guard itself was the discovery.  The same
row's advice to stop `be_setv` recomputing `length` turned out moot: the machine calls
`setv_it` directly, and `be_getv`/`be_setv` are in the extracted surface only for §5's
array-API checks.  Recorded so the plan's numbers stay auditable: method matters as much as
result here — the 2026-10-03 count of 15 for `mrun` included `sub`/`divmod` as reachable,
which this artifact does not, so the comparable figures are the structural counts (10 → 10
unchanged for the reference root, 10 → 11 for the shipped one), not the totals.

**The simplifications the re-analysis found.**  (1) `expand_c` needs **one** call to `expand`,
not one for the guard and one for the write, and `enter_case_c` binds the scrutinee's
expansion once per branch site so guard and matcher share it; the draft did it twice.  Coq's
`let` extracts to OCaml's `let`, so this is one call in the artifact, and `cbn` zeta-reduces
it in the proofs, which is why the site lemmas still close by `rewrite Eb, Em`.  (2)
`ExtrOcamlNatInt` hooks minus/mult/leb/eqb but **not** `max`, so the freshly-reachable
`branch_need` emitted a genuine Peano `max` recursion; one added
`Extract Constant Nat.max => "(Stdlib.max)"` turned it into a primitive call.  Ordering still
bites: the hook is only honoured after `Arith`/`PeanoNat` are required.  (3) The harness had
grown a second copy of the §7–§9 fact table; it is now one `facts : fact list` iterated
through both drivers, which converts "did the rewiring break anything?" from a prose claim
into a per-command equality `machine == literal == run`.

**Tactics that cost time on this file, each one listed because the failure mode is silent or
misleading.**
- **Never bare `cbn`** in a file mentioning `GLOB_FUEL`/`MAX_FUEL`: it delta-unfolds `Nat.add`
  over a 132 353-sized unary literal.  A proof that finishes in ~1 s as `cbn [enter_case_c]`
  ran past ten minutes and looked exactly like a hang, and there is no `timeout` binary on
  macOS and no `Set Timing on.` in this configuration, so bisection had to be done by
  splitting the file in `/tmp` instead.
- `lia` keeps transparent Definitions as **atoms**: from `case_site_fuel <= g'` it proves
  `case_site_fuel <= g'` but not `0 < g'`.  `unfold case_site_fuel in H1 |- *` first, then
  `repeat split; lia`.
- `rewrite (lemma …)` can answer "Found no subterm matching" for a term that prints
  identically (implicit/`text`-vs-`list nat` mismatch under conversion).  `apply` unifies up to
  conversion where `rewrite` does not, so the shape that works is
  `assert (E : lhs = rhs) { apply (lemma …) } rewrite E.`
- Bullets nest only `-` → `+` → `*`; after a `*` level, switch to `[ … | … ]`.
- `Nat.add_sub_cancel_l` and `Nat.succ_pos` do not exist here (`Nat.lt_0_succ` does); the
  arithmetic step that needed them became `unfold MAX_FUEL, MAX_CMD. lia.`
- When a goal prints something unrecognisable, `exact I` makes Coq print the expected type.

**Gate, vendoring, empirical net.**  `verify_models.sh` 10/10 → **11/11**: `sh_jpl_run_c.v`
joined `COQ_MACHINE` and block 2c's compile chain gained `coqc sh_jpl_run_c.v` — an edit to
that script made under the standing authorization for it (2026-10-03, re-granted for the 2c
wiring on 2026-10-04), with a matching `Covers:` entry.  Parity 34 → **59**.  The artifact was
re-extracted and re-vendored (`cp sh_run_c.ml sh_run_c.mli ../../src/kernel/`), which block
2c's `diff -q` then bound; `dune build` clean with it; `conformance.sh` 33/33; the cleanup list
grew to cover the new module's `.vo`/`.glob`/`.aux`/caches so the run leaves nothing behind.

**Honest limits after #35.**  (i) The residual recursion is `expand`/`expand_name`/
`expand_brace`/`getv`/`nat_digits`/`teqb`/`app` plus the guard's `branch_need`/`forallb`/
`length` and `setv_it`'s `rev_append` — all length-bounded, and `expand_it` is the one stage
that drains most of it (`getv_it` is still dead precisely because `expand` still calls
concrete `getv`).  (ii) `host_c`'s completeness is conditional on `no_sat`, which is a
proposition about a run, not a decidable property of an input; the operational claim "a
well-formed program never saturates" rests on `enter_case_c_chain_clear`, and that lemma's
`length (expand h …) <= MAX_WORD` premise is one **L2 does not prove** — `expand_c` enforces
it as a cap check on the result, so the machine is total, but whoever builds the input
(parser, emitter) inherits the obligation.  Stated here so JPL.5 does not read it as closed.
(iii) `host_c` is deliberately still not extracted (its `phi : run_phi` is a function type;
the C host is JPL.7's job), so the artifact contains a kernel and an oracle, not a program.
(iv) As at every `==` rung, D5's parity is empirical — it is the Coq↔OCaml bridge, not a
theorem.

Next: JPL.5 (#25), whose opening has two decisions and no missing lemmas — which root
JPL.6's Rule-6 lint binds, and whether `expand_it` precedes the emitter (see §9.2's front
paragraph).  The second one is the question this stage leaves open on purpose: eliminating a
*mutual* fixpoint is not the "pure layout" JPL.5 was scoped to be, and this plan has so far
resolved every such case in favour of proving it in Coq.

### JPL.5-A.7 / #37 — DONE (2026-10-04): `sh_jpl_scan.v` §6 expander loop, L8 rewired onto it

**What landed.**  The last scan the shipped kernel still recursed into: L2's
`expand`/`expand_name`/`expand_brace` mutual fixpoint, now ONE fuel-bounded tail loop
`expand_go` over an explicit cell `ExpK { ek_mode; ek_inp; ek_out; ek_name }`, entered as
`expand_it f m st inp = expand_go f m st (ExpK EMain inp [] [])`.  Three design choices
carried the stage:

- **one fuel counter for the three fixpoints**.  In L2 a mode switch is a *return into
  another fixpoint at `f'`*; here it is a *write of `ek_mode` with the same `f'`*.  Because
  every step consumes exactly one fuel and at most one input byte — the same law the
  reference has — the loop's fuel is the reference's fuel at every point, and that is what
  makes the agreement theorem hypothesis-free.
- **output accumulated reversed**, so the final answer is one `rev` per expansion instead
  of one `::`/`++` rebuild per byte on the way out; the name accumulator is likewise
  reversed and read with `rev nm`.  `rev o ++ expand_at ..` is the invariant's right-hand
  side, which is why `rev_append`/`rev` lemmas do most of the leaf work.
- **`ek_value` + `ek_valuesubst`** as the bridge to L2's `subst_var`, needed because the
  loop's fuel-0 edge has to answer with a substitution too.

**The result that changed the plan's shape.**  `expand_it_correct : forall f m st inp,
expand_it f m st inp = expand f m st inp` carries **no hypothesis**.  Contrast 5-A.6, where
the two matchers' fuel laws differed (linear `branch_need` vs quadratic `fuel_top`) and the
`case` site therefore had to be *guarded*, with two constants raised to make the guard
affordable.  Here the loop copies the reference's steps, so there is nothing to guard, and
**no capacity constant moved** — §4.1 now records that explicitly, because "increase
budgets when needed and prove their minimal bounds" (the standing instruction for this
stage) is answered by a *null* budget result, and a null result has to be stated as such
rather than quietly omitted.

**What this stage predicted about itself and got wrong, recorded.**  5-A.6's row described
5-A.7 as "tail-loop expander **wired to `getv_it`**".  It is not wired to `getv_it`:
`expand_go` calls the concrete `getv`, because `getv` is already a forward tail scan, so
substituting with `getv_it` would have created a second encoding of one scan (the failure
mode §2's single-source rule is there to catch) without removing a recursion.  `getv_it`'s
consumer is `be_getv`, whose fuel is `be_len` — the length the bounded carrier already
holds, i.e. the bound `getv` itself cannot state.  Measured: `be_getv`'s closure is
{`be_getv`, `getv_it`, `teqb`}, and `getv_it` is unreachable from `mrun_c`.  So "dead" was
the wrong word all along: **live in the artifact, dead in the machine**.

**Census, measured twice.**  Call graph over the re-extracted `src/kernel/sh_run_c.ml`:
**76** top-level bindings, **30** recursive.  `mrun_c`'s closure **45** bindings / **17**
recursive = 6 fueled tail loops (`mrun_c`, `enter_case_c`, `setv_it`, `match_any_iter`,
`glob_it`, `expand_go`) · 2 print-only aliases (`add`, `mul`) · 9 bounded structural
(`teqb`, `app`, `length`, `rev_append`, `forallb`, `getv`, `nat_digits`, `branch_need`,
`rev`).  Delta from 5-A.6's 18: `expand`, `expand_name`, `expand_brace` out, `rev` in (the
loop's one-pass final reversal; a copy bounded by `MAX_WORD`, not a scan).  Oracle roots
unchanged: `mrun` 13, `run` 15, `step` 12 — they keep the `expand` group on purpose, since
`expand_it_correct` is what lets L8's §2/§5 statements, still phrased about the reference,
be read back against the loop (`Ltac exp_ref := repeat rewrite expand_it_correct`).
*Method warning, the reason a first measurement was thrown away:* the emitted file's
`(** val name : type **)` banners name the **next** binding, so a parser that treats them as
code invents edges from the preceding function to whatever they mention — it reported
`enter_for → enter_case`, `branch_guardb → getv_it` and an 8-binding `mrun_c` loop set.  The
final numbers come from two independent parses (span-per-top-level-binding, and a
chain-aware `let rec`/`and` counter) that agree on every figure.

**Gate, vendoring, empirical net.**  `coqc` + `coqchk -o -silent` four `<none>` for
`sh_jpl_scan.v` and `sh_jpl_run_c.v`, no `Axiom`/`Parameter`/`Admitted`/`admit` anywhere in
§6; §6.4's byte-level Examples (10 behavioural + 4 vs-reference at low fuel);
`sh_run_c_parity.ml` **59 → 66** — 5 `expand_it` point checks plus two sweeps of 15 words ×
9 fuels = 135 loop-vs-`expand` comparisons each, **270 over both**, the shape that fails on
the first mismatch instead of reporting a count.  `verify_models.sh` **11/11** (L8 was
already in `COQ_MACHINE`, so this stage changed the block's *comments*, not its wiring);
`dune build` clean; `conformance.sh` **33/33** with `ush` rebuilt against the re-vendored
`src/kernel/sh_run_c.ml{,i}`.

**Rocq 9.2 facts this file cost time on, each listed because the failure is silent or
misleading.**
- `rewrite H` on a *quantified* lemma rewrites only the **first** unified instance.  With two
  `rev`-shaped subterms in the goal this silently leaves the other one alone and the leaf
  "cannot be closed"; `rewrite !H` fails outright when nothing matches, so an
  idempotent-normalising tactic has to be `try rewrite !H` per family.  `rewrite ?H` means
  at-most-one, not "many".
- **`app_assoc` in this stdlib is left-associating**: `l ++ m ++ n = (l ++ m) ++ n`.  An
  accumulator goal shaped `a ++ (b ++ c)` therefore has *no* `app_assoc` subterm and
  `rewrite app_assoc` answers "Found no subterm matching ?M ++ ?M ++ ?M" while the
  `reflexivity`-level fact is obviously true.  The working normal form is
  `repeat rewrite <- app_assoc` then `app_nil_r`/`app_nil_l`, and a single `exp_norm`
 Ltac built from those is far more robust than a `try rewrite !X` chain.
- `rev_append l l' = rev l ++ l'` **already exists** as `rev_append_rev`; a bespoke
  `ra_spec` by induction is not needed, and attempting it fails with the confusing
  "No such goal" because `simpl` had already rewritten the goal into the lemma's own shape.
- **Ltac bodies resolve global references at definition time.**  `Ltac norm := rewrite
  rev_ra_spec` before `rev_ra_spec` exists errors at the *use* site with
  "reference rev_ra_spec was not found"; declare tactics after their lemmas.
- `cbn [f]` unfolds `f` only when the unfolding **creates a redex**.  After `destruct mode`,
  `expand_at m st f mode inp nm` has a *variable* in the scrutinee position, so `cbn`
  leaves it folded and the leaf mismatches — re-run `cbn [expand_at expand expand_name
  expand_brace]` after the `destruct`.  Conversely `cbn` must be told to leave `subst_var`
  alone, or it eats the redex `ek_valuesubst` needs to match.
- `cbn [expand]` on a **mutual** fixpoint does step it when the fuel is a constructor and
  leaves calls at a variable fuel untouched — which is exactly the per-leaf shape
  `expand_at` wants.  `expand (S f) m st []` reduces; `expand f m st []` does not, so the
  fuel-polymorphic empty-input case needs `expand_nil`.
- A tail loop that "idles" on empty input (taking a fuel step to return the same answer)
  forces every leaf of the induction to carry a rewrite of the reference's own idle step.
  Returning `rev o` directly for `EMain`/`[]` removed that obligation and the `expand_nil`
  rewrite with it — i.e. the *loop's* shape, not the proof's, was the cost.
- `show` is not a tactic.  `Show.` is a **command**, legal inside `Proof … Qed` only as a
  script line; for a symbolic normal form use
  `Eval cbn [rev app expand_go] in fun f m st => …`, and read byte values with
  `Eval vm_compute in …` before writing an `Example`'s right-hand side.
- `text` is `list nat`, so an `Example` cannot be written with string literals
  ("No interpretation for string \"a\"").  The byte mnemonics in §6.4 (`b_dollar` 36,
  `b_qmark` 63, 64 `@`, 97 a, 98 b, 99 c, 120 x, 122 z, `b_lbrace` 123, `b_rbrace` 125) exist
  so the cases read back as words.
- `coqc` exits **non-zero on a plain warning**, so a `for f in …; do coqc $f.v; done`
  rebuild chain aborts at the first file that warns (`|| true` per file), and the gate's
  cleanup deletes `.vo`s — an ad-hoc probe run therefore has to rebuild the chain first, or
  it fails with "Unable to locate library sh_concrete (.vos)" for a file that is plainly
  present.

**Honest limits after #37.**  (i) Agreement is exact, but `expand_c`'s **word cap** is still
a cap: L2 proves nothing about the output length of `expand`, so the obligation
`length (expand …) <= MAX_WORD` is enforced as a runtime check on the result and inherited
by whoever builds the input (parser, emitter).  `enter_case_c_chain_clear`'s premise is
deliberately phrased about `expand`, not `expand_it`, for the same reason.  (ii) The kernel
still contains 9 length-bounded structural recursions; they are inside §6.1's contract for
the emitter, not eliminated, and the count went **up** by one (`rev`) when the mutual
fixpoint went away.  (iii) `getv_it` stays out of the substitution path by choice; if the
emitter ends up reading `benv` through a direct array scan, `be_getv` **and** `getv_it`
should both be deleted rather than kept as a proved-but-unused second encoding — that is the
test that would close this stage's parallel-encoding question.

Next: JPL.5 (#25), the emitter.  One opening decision remains (§9.2's front: which root
JPL.6's Rule-6 lint binds); the other — whether `expand_it` precedes the emitter — is closed
by construction, because the mutual fixpoint it would have had to transform no longer exists
in the shipped kernel's closure.  *(Superseded the same day by **5-B.1**: that decision is
now closed by measurement, and the one that replaced it — the C99 value representation — is
§9.2's decision 3.)*

### JPL.5-B.1 / #38 — DONE (2026-10-04): `verify/c/jpl_front.ml`, the emitter front end

**What landed.**  Not a transpiler: a *reader*.  `verify/c/jpl_front.ml` parses the
extracted artifact with the compiler's own `Parse.implementation` / `Parse.interface`,
attaches `.mli` signatures to bindings, walks the transitive closure from **named roots**,
classifies every expression and pattern constructor it meets, and exits non-zero if any of
them is outside the emitter's declared subset.  `verify/c/jpl_front.sh` builds it into a
`mktemp -d` (removed on `trap`), runs it over the **vendored** `src/kernel/sh_run_c.ml{,i}`
— the same bytes block 2c byte-binds to a fresh Extraction — and `diff -q`s the report
against the tracked `verify/c/closure.txt`; `JPL_REGEN=1` regenerates deliberately.
`verify_models.sh` gained **block 2d** (the run) **and 2d-negative** (the oracle roots
*must* be refused), plus a `skip()` rung class so a missing `ocamlfind` is reported as a
skip and counted in the summary rather than silently vanishing.  Gate **11/11 → 13/13**.

**The finding that changed a normative section.**  The tool's TYPE VOCABULARY listing refuted
§6's original "fixed arrays + a length field": `cmd`, `frame` and `stack` are **recursive**
value types (`Seq of cmd * cmd`, `For of text * text list * cmd list`, `Case of text * (text
list * cmd list) list`, `stack = frame list`), so an inline fixed-capacity encoding of them
has no finite size at *any* setting of the caps.  §6 now splits by kind — `nat`→`uint32_t`,
`text`→inline `MAX_WORD` buffer, non-recursive records/variants→structs, recursive
types→**handle into a static node pool** — and the question that survives is narrower and
honest: *what reclaims cells between steps*.  The extracted kernel is purely functional, so
a lowered `cons` never mutates in place and a pool that only grows cannot last `MAX_FUEL`
steps; "static pools only" therefore means a step-boundary copying collection, not `free` and
not a region reset (region reset would be unsound precisely because functional values share).
§9.2's decision 3 records that, with its strength labels.

**A cross-check that corrected an earlier row.**  The closure was re-derived a second way —
a text identifier graph over the same bytes (comments stripped, top-level `let`/`and`
boundaries, every top-level name occurring in a body counted as an edge) — and it returns the
**same 47 names and the same 17 recursive names, set-equal** with the AST tool's output, not
merely count-equal.  That second method is also what exposed §9.1's 5-A.7 row as low by **2
members** (it recorded 45 for the same root): its edge rule was narrower than an identifier
graph.  The row now carries a bracketed correction rather than being edited silently, and the
reason the error survived three stages of being quoted is worth keeping: every claim built on
it was about the **recursive** split (6 + 2 + 9 = 17), which was right all along, so nothing
downstream noticed the member count.  `verify/c/closure.txt` is the authoritative inventory
from here on, because the gate re-derives it on every run.

**The distinction the census had to get right.**  `ExtrOcamlNatInt` emits Coq's nat
destruction as the *value* `(fun fO fS n -> if n=0 then fO () else fS (n-1))`, and it emits
that value for **every** `match n with O => … | S n' => …` — including the three sites in
this artifact that contain no self-call at all (`nat2text`, `enter_seq`, `step_cmd_c` each
show `nat-match 1, self 0` in `closure.txt`).  So "is this a loop" cannot be asked of the
term; it is a property of the **binding** (`let rec` with `self > 0`).  A naive scanner that
equated the destruct value with recursion would have reported a kernel that fails its own
Rule-6 lint, and the fix would have looked like a Coq change rather than a tool bug — which
is why this stage exists before the emitter does.

**Parsetree facts measured while writing it** (OCaml 5.5.1; each of these was a compile
error first, so they are recorded rather than re-derivable by trial): `Pexp_fun` **no longer
exists** — a function is `Pexp_function of function_param list * type_constraint option *
function_body`, with `Pparam_val of arg_label * expression option * pattern` and the body
either `Pfunction_body of expression` or `Pfunction_cases of case list * …`;
`Pexp_open`/`Pexp_letmodule`/`Pexp_letexception` are folded into `Pexp_struct_item`;
`Ppat_tuple` carries `(string option * pattern) list * closed_flag`, `Ppat_record` carries
`(Longident.t loc * pattern) list * closed_flag`, `Ppat_construct` carries
`Longident.t loc * (string loc list * pattern) option`, `Ppat_variant` carries a **plain
string** label; `constant` is a record `{pconst_desc; pconst_loc}` and `Pconst_integer of
string * char option` absorbs the int32/int64/nativeint suffixes; `case` is `{pc_lhs;
pc_guard; pc_rhs}`; `Ptyp_tuple` is `(string option * core_type) list`; `Psig_typesubst`
takes **one** argument list; `Pexp_ifthenelse`'s else branch is an `expression option`;
`Longident.Ldot` needs `m.txt ^ "." ^ s.txt`.  `Ast_mapper.mapper` is a record of functions,
**not** a class — the traversal here is `Ast_iterator.iterator` with `default_iterator` and
open recursion through `self`.

**Two bugs worth keeping, because both are silent-failure shapes.**  (i) *Mis-scoped
shadowing*: pushing pattern variables only inside the pattern made case-rhs variables (`p`,
`m`, `f`, `g`) resolve as **top-level edges**, inflating the closure and inventing
dependencies; the fix pushes them around the whole `case`, since a guard's bindings scope
over the rhs.  (ii) *Dangling else* in the runner's own argument parser: `if a then if b
then … else …` attached the `else` to the inner test, so `"mrun_c,step_c"` parsed to `[","]`
and the roots were wrong while the report still looked plausible — explicit `begin … end`
now brackets it.  A third, smaller lesson: the report first echoed the **absolute** artifact
path the runner passed, which made the tracked evidence machine-specific; the runner now
`cd`s to the repo root and prints repo-relative paths.

**Honest limits after #38.**  (i) The declared subset is *this plan's* subset, not NASA's:
D-60411 constrains the C output, so "OFF-SUBSET" means "JPL.5 as specified cannot lower
this", and the list is the artefact of a design decision, not a standard's text.  (ii) The
census **sizes** the memory-model decision; it decides nothing by itself, and the per-step
allocation bound it points at is still unmeasured (§9.2's decision 3).  (iii) No C has been
emitted yet: 2d binds the *input contract*, not the emitter's behaviour — that bridge is
D7/JPL.6/JPL.7 and is still green-by-absence, so nothing in this row may be read as
JPL-compliance of generated code.  *(Rung names moved under it: **D7** is now 5-B.2's
representation layer, emitted the same day, and the emitted-behaviour rung this row was
pointing at is **D8**.)*  (iv) The front end reads the artifact but re-encodes no
semantics; if it ever grows a rule that changes a verdict, it has become a second model of
the kernel and must be deleted rather than extended.

Next: **5-B.2 / #39** — the runtime representation header (handle + node pool, the inline
`text` leaf, the step-boundary collection) and the lowering of the 17 recursive bindings:
6 tail loops → `while`, 9 length-bounded structural recursions → bounded copy loops, 2
print-only aliases → dropped.

### JPL.5-B.2a — DONE (2026-10-04): the LOCKED cap table becomes DATA the artifact carries

§9.2's decision 3 says the layout allocates against the caps, and the first thing an
emitter that allocates needs is the numbers.  They were not there.  `Extraction` emits a
constant only when *code in the extracted kernel* mentions it: `MAX_WORD`, `MAX_ENV`,
`MAX_LIST`, `GLOB_FUEL`, `MAX_FUEL` appear in `sh_run_c.ml` because a guard compares
against them, while `MAX_WIDTH`, `MAX_ARGV`, `MAX_CMD`, `MAX_STACK` occur only in proofs
and were absent from the artifact entirely.  Hard-coding those four in the emitter would
have put a second, unchecked copy of a LOCKED table into a derived tool — the same
parallel-encoding failure that retired `sh_model.ml`, one layer down the stack.

The fix is one Coq record, not a scheme: `sh_jpl.v` §1.1 adds `jpl_caps` (nine fields,
one per LOCKED constant), `jpl_caps_table : jpl_caps` built from the literals, and
`jpl_caps_are_locked`, which re-proves every field against the LOCKED literal so the
table cannot drift from §1 by construction.  Extraction driver re-run; `jpl_caps` /
`jpl_caps_table` now appear in `sh_run_c.ml` + `.mli`.  Evidence: extraction green, parity
66 unchanged (this is data, so no control flow moved), `conformance.sh` 33/33, block 2c's
artifact `diff -q` re-bound to the new bytes.  *Consequence for the artifact census*: the
file grew from **81** bindings / **76** signatures / **14** declarations to **87 / 81 /
15**, which is why §9.1's 5-B.1 row now carries a supersession note; the shipped closure is
unchanged at 47 / 17 because nothing in a record projection is a call edge.

What makes this more than a plumbing change is 5-B.2's differential check: the emitter
folds the literals *syntactically* out of the artifact, and a separate OCaml probe reads
the same `jpl_caps_table` *at runtime*.  Both must equal the emitted `#define`s.  That is
the first check in this pipeline that compares a static reading with an evaluation of the
same term, and it is only possible because the caps became a value.

### JPL.5-B.2 / #39 — DONE (2026-10-04): `verify/c/jpl_emit.ml`, the representation layer, and the first emitted C in the tree

§6's R1–R8 became a program: read the `.mli`'s type vocabulary and the `.ml`'s bindings,
take the typed closure from `mrun_c,step_c` (the reader is `verify/c/jpl_ast.ml`, shared
with 5-B.1 rather than duplicated), lay out every reached type, and emit
`verify/c/sh_run_jpl.h`.  The header is 365 lines and **compiles**: `clang -std=c99 -Wall
-Wextra -Wconversion -Wsign-conversion -pedantic -Werror -fsyntax-only` is clean over it,
and that is not a courtesy — 27 of the 40 emitted types are followed by
`typedef char jpl_check_<T>_is_<N>[((sizeof (T) == Nu) ? 1 : -1)];`, the 5 cap relations and
the word width are checked the same way, and the remaining 13 one-word typedefs (R1 scalars,
R3 handles, R7's all-nullary variant) are covered conjunctively by
`jpl_check_one_word_families`, so **no emitted type's size is left to the reader**.  (C99 has
no `_Static_assert`; that is C11, and JPL rules bind us to C99, hence the
negative-array-bounds idiom.)  That last sentence is a *correction made the same day*: the
emitter's report first printed "40 C types emitted, each followed by a sizeof check the
compiler verifies", and the claim was false — counting the `jpl_check_*_is_*` lines in the
generated header against the report's own row list gave 27, not 40.  So the check count is
now measured by the tool (each `sizeof_check` registers the row it checked) and the uncovered
rows are asserted as a family rather than described in prose, which also means a future row
that is neither checked nor one-word cannot hide: it appears in the family conjunct with the
size the emitter claimed for it.  31 functions get prototypes; **5 are PENDING** with their
caller counts printed, because R8 refuses to invent a monomorphic instance — the refusal is
the deliverable, exactly as in 2d-negative.  In `AXIOTACK.md` this is derived rung **D7**
(the rung after D6's input contract) and gate block **2e**; the rung that will check emitted
*behaviour* — differential vectors against the kernel — is **D8**, still planned.

**Three things this layer measured that §6 records as refutations of §6's own text.**
(i) *"No monomorphization"* is false for the shipped closure: `length`, `app`, `rev`,
`rev_append`, `forallb` are polymorphic as extracted and each is reached at **different**
element types (2–6 callers).  (ii) *"Fixed arrays + a length field"* was already corrected
by 5-B.1; 5-B.2 then measured **which half of the recursive-type claim is real
self-reference** — a reachability walk over the `.mli` finds `cmd` reaches itself and is
the *only* type that does, while `frame` is 4-field bounded and `stack = frame list` is
pooled by R3 for a different reason, so §6's grouping of all three was half right and the
grouping that survives is the one §1's cap *comments* state.  (iii) *"Live-set bounded by
the caps"* is false for the word slab: `MAX_CMD` nodes can each own a `MAX_LIST`-word list,
so live words are bounded by a **product**, and no LOCKED entry is the capacity of a word.
The emitter therefore prints `extern jpl_text jpl_word_pool[];` with **no dimension** and a
range (4 096 … 4 194 304 words at 1028 B), rather than picking a number.  Closing that is a
**model** change (`sh_jpl.v` §1 owes a `MAX_WORDS` + proof + export), not an emitter change,
and it is now the named blocker for linking — 5-B.3 can lower every control flow and still
not produce an executable.

**Parsetree / emitter facts measured while writing it.**  `Ptype_external` carries **one**
argument in this Parsetree (it is `{pty_desc: Ptype_external of external_declaration}`, a
single record, so the pattern must be `Ptype_external _`); `String.prefix` does not exist in
the 5.5.1 stdlib the way it was assumed; `Printf.kprintf` is deprecated in favour of
`ksprintf`; `Parse.interface` on a `.mli` gives `signature_item list`, so the reader walks
`Psig_type`/`Psig_value` rather than the structure path.

**OCaml string-escape facts, because they produced two failed compiles of a tool that
otherwise type-checked.**  Inside `"…"`: backslash + newline **skips the next line's leading
whitespace**, so plain-indented continuation lines silently lose their indentation — the
emitted header came out with C comments jammed against column 0; backslash + spaces + text
**keeps** the spaces, which is the correct idiom for emitting indented C; backslash + a
non-blank, non-reserved character (`\#`, `\/`, `\e`) is Warning 14 *illegal backslash
escape*.  The nastiest member of the class is `\typedef`: OCaml reads `\t` + `ypedef`, so
the escape is accepted, the string is wrong, and only the C compiler notices — `clang`
reported `unknown type name 'ypedef'`.  Audited afterwards: no `\t` sequence remains in the
emitter.  The same class bit once more when the size checks were completed: an assertion
emitted as `[(( … ) ? 1 : -1);` — missing its `]` — type-checks in OCaml, runs, writes a
header, and fails only in C.  That is the whole argument for the runner's check 2 existing:
the emitter's own output is not evidence about the emitted C; the compiler is.

**Two gate-side bugs worth keeping, both silent-pass shapes.**  (i) The 2e success branch
grepped `^PASS:` over the runner's **ANSI-coloured** output, matched nothing, and under the
gate's `set -o pipefail` aborted the whole run with exit 1 and no message — the digest is
now stripped with `sed 's/\x1b\[[0-9;]*m//g'` before anchoring.  (ii) **The negative control
passed for the wrong reason first.**  `jpl_emit.sh` parsed `JPL_ROOTS` into a variable and
then never forwarded it to the binary, so 2e-negative re-ran the *shipped* roots and "failed"
only because the artifact check compared against a header the run had not produced; the
assertion looked like teeth and had none.  The runner now passes `"$ROOTS"` through, exactly
as `jpl_front.sh` does, and the oracle roots refuse with `FATAL: tn: a function-typed value
has no layout` — `tn` is this emitter's OCaml-type→C-type-name function (the message carries
its own author, not a binding name), and what it refuses is the oracle cluster's driver
parameter: `type run_phi = int -> text list -> cstate -> cstate option`, used by
`val run : run_phi -> …`, i.e. the higher-order style that 5-A.4 replaced with a data driver
for `mrun_c`.  That is a *different* reason from 2d-negative's mutual-fixpoint refusal, which
is why the gate asserts the message and not just the exit code.  A third, smaller one: the
PENDING count the gate printed came from the runner's coloured digest and read `1`; the first
fix counted `PENDING` *lines* in the vendored `layout.txt`, which read `2` — true of the file
but not the number anyone wants (it mixed the report's summary row with the pool table's
`PENDING` cell).  The gate now reads the emitter's own `PENDING` field from
FUNCTIONS AND VALUES and prints `5 polymorphic bindings are PENDING … and the word slab is
declared without a capacity`, i.e. the two different kinds of unfinished are named separately
instead of collapsed into one count.

**Honest limits after #39.**  (i) This is a **header**, not a program: no statement is
emitted, so nothing here has been checked against JPL.6's shall-rules for function bodies,
and the lint gate still has no input.  (ii) The 187.0 KiB bounded total is *derived from
caps*, which are LOCKED by policy (§3), not from a proof that the machine stays inside
them; the headroom 2 is an admitted placeholder (§6.2's choice 3).  (iii) The three choices
in §6.2 are genuinely choices — a reader who disagrees with pooling `frame` changes one
line and every size below it moves.  (iv) `jpl_word_pool` unsized means the artifact is
**not linkable**, so the "representation layer DONE" state means "every type the closure
reaches is laid out and checked", not "the runtime exists".  (v) The emitter stores no
semantics: if it ever grows a rule that changes a *behavioural* verdict rather than a
layout, it has become a second model of the kernel and must be deleted, same as 5-B.1's
limit (iv).

Next: **5-B.3**, still under JPL.5 (#25) — first the model's `MAX_WORDS` (§1 constant +
proof + `jpl_caps_table` export, per the standing "increase budgets when needed and prove
their minimal bounds"), then the lowering pass: 6 tail loops → `while`, 9 length-bounded
structural recursions → bounded copy loops (leaf `text` copies inline, `cmd`/`frame` lists
copy handles), the R8 monomorphization instances for the 5 polymorphic bindings, and
statement-level emission at the step boundary; then JPL.6 (#26) lints the result and JPL.7
(#27) runs it against `/bin/sh`.

