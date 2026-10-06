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
  - [6.2 The four choices the derived layers could not derive](#62-the-four-choices-the-derived-layers-could-not-derive)
  - [6.3 The lowering schemas the census measured](#63-the-lowering-schemas-the-census-measured-normative-list-5-b3a)
  - [6.4 What a body needs before it can be rendered](#64-what-a-body-needs-before-it-can-be-rendered-normative-list-5-b3b-ii-a)
  - [6.5 The second debt: what an owed row also touches](#65-the-second-debt-what-an-owed-row-also-touches-normative-list-5-b3b-ii-b-0)
  - [6.6 The pool runtime: how a cell comes to exist](#66-the-pool-runtime-how-a-cell-comes-to-exist-normative-list-5-b3b-ii-b-1)
  - [6.7 The step boundary: two spaces, forwarding, and what "live" means](#67-the-step-boundary-two-spaces-forwarding-and-what-live-means-normative-list-5-b3b-ii-b-2)
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
| `MAX_WORDS` | 16 642 | **cells of the word (text) slab**, added 2026-10-05 because 5-B.2's emitter could size every pool except this one. Not a new choice: a sum of the caps above, `2·MAX_STACK + 2·MAX_ENV + 2`, spelled with qualified `Nat.add` so the extracted artifact carries the *expression* rather than a numeral; measured after the fact (HISTORY, 5-B.2b) that the qualified spelling extracts as a call of the artifact's own recursive `module Nat.add` — `ExtrOcamlNatInt` hooks the `+` *notation* but not that path — which is harmless here only because `jpl_caps_table` is outside the `mrun_c`/`step_c` closure, so the lowered C sees the folded numeral and never this recursion. Summand by summand: `MAX_STACK` for the words a node-pool-fitting tree holds — **proved** by §7.1's `cmd_words ≤ 2·cmd_count` plus `cmd_fits`; a second `MAX_STACK` for the runtime-expanded copies an `FFor`/`FCase` frame holds — the **recorded obligation** "one live frame per source node", charged rather than assumed, because the machine's frames can hold expanded lists the source tree never spelled out; `2·MAX_ENV` for the environment's name and value cells — **proved** by §5's `benv_words_le`; and 2 for the per-step temporaries (`$?` rendered, and the word being expanded). `cap_words_order` places it: `MAX_STACK ≤ MAX_WORDS ≤ GLOB_FUEL` |
| `GLOB_FUEL` | 132 353 | **one glob/branch scan's own budget**, added 2026-10-04. Defined *derivationally*, not as a literal: `S (MAX_WORD + MAX_WORD) * S MAX_WORD + MAX_WORD + MAX_WORD`, i.e. `sh_jpl_scan.v` §4.3.9's `fuel_top` evaluated at two full-width words. §4.3.14's `fuel_top_le_glob_fuel` proves it covers the law for every in-budget pair of words; because the definition and the law share one expression, it cannot drift if `MAX_WORD` changes |
| `MAX_FUEL` | 136 449 | loop-iteration bound the machine may be handed (`b_fuel` refuses above it). Was the flat 4096 that matched ush's budget; now `GLOB_FUEL + 4096` — the deepest scan's proved budget plus the machine's own 4096-step allowance, because `step` hands ONE fuel both to its countdown and to the scans it calls |
| `case_site_fuel` | 1537 | **the branch guard's threshold**, added with 5-A.6 (`sh_jpl_run_c.v` §5). `S (MAX_LIST + MAX_WORD + MAX_WORD)`: L2's `match_any g pats w` globs pattern *i* at fuel `g-1-i`, so its worst in-caps branch needs exactly this much site fuel. **Proved least, not merely enough** — `branch_need_worst_case` exhibits a branch that ATTAINS it (`branch_need (rep MAX_LIST p) w = case_site_fuel`), so no smaller uniform site threshold decides every in-caps branch, and `guard_fuel_is_least` states that minimality for the guard itself |

Ordering is proved in three pieces: `cap_order` chains `MAX_WIDTH ≤ MAX_WORD`,
`MAX_ARGV ≤ MAX_ENV ≤ MAX_LIST ≤ MAX_CMD ≤ MAX_STACK`, `cap_words_order` adds
`MAX_STACK ≤ MAX_WORDS ≤ GLOB_FUEL`, and `cap_fuel_order` adds
`MAX_STACK ≤ GLOB_FUEL ≤ MAX_FUEL`. So the largest cap is `MAX_FUEL` = 136 449,
still three orders of magnitude inside a `uint32_t` (and inside `int32_t`), which
is what the no-wrap argument in §3/R17 rests on. Note the direction flip this
introduces: fuel is no longer below the frame cap — frames bound *nesting*, fuel
bounds *iterations*, and nothing in the tree requires one to dominate the other
(measured: no lemma or call site depends on `MAX_FUEL ≤ MAX_STACK`).

**The cap table is DATA the emitted C reads, so the artifact has to carry it
(sub-step 5-B.2a, 2026-10-04; the tenth field `jpl_words` added 2026-10-05).**
§6's layout allocates against all ten constants
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
| R8 a signature mentioning a type variable | **PENDING**, not emitted | monomorphization is JPL.5-B.3's call-site census (see above); inventing an instance here would be a second encoding of the choice.  *[**5-B.3b-i** landed that census's consequence on 2026-10-05, in the tool that owns the instance set rather than here: the **6** closed instances become prototypes in `verify/c/sh_run_jpl_abi.h`, the **6** open ones are still PENDING exactly as this row says, and the one closed instance whose parameter is function-typed is **refused** — the alternative would be D-60411's forbidden function pointer (§6.3's ABI paragraph)]* |

The rule set is applied mechanically, and the two places where it *refuses* are
evidence of that: `of_ct` fails on a type outside the artifact's vocabulary, and
`require` fails on a by-value cycle ("must be pooled"), instead of unrolling one.

Reclamation follows from the same reading: the extracted kernel is purely functional, so
a lowered `cons` allocates and never mutates in place, and a pool that only grows cannot
survive `MAX_FUEL` steps.  "Static pools only" is therefore satisfied by a **copying
collection at the step boundary** (fixed two-space pool, forwarding through the handle
table, live-set bounded by the caps) — not by `free`, and not by a per-step region reset
*on its own*, which the sharing in a functional program would make unsound.  *(§6.7, 2026-10-05,
is that sentence's specification, and it reconciles the reset §6.6 landed with it: a space **is**
a region, so `reset` is the collector's primitive and not its whole — the reachable cells are
evacuated into the other space before any region rewinds.)*  §6.2's decision 3 carries
the sizing numbers and states which half of this is measured and which half is still open.

**The word slab now has a capacity (2026-10-05), and the sentence above it — "live-set
bounded by the caps" — is what changed.**  5-B.2 measured that no LOCKED constant *is*
the number of live `text` values, and this section then argued the live words are
bounded by a **product** (`MAX_CMD × MAX_LIST` = 4 194 304).  That argument was per-node
and it was wrong: a tree in which every one of `MAX_CMD` nodes owned a full `MAX_LIST`
word list has `cmd_count` far above `MAX_CMD`, so `cmd_fits` refuses it before the
machine ever sees it.  Per-*tree*, §7.1's `cmd_words ≤ 2 · cmd_count` plus
`cmd_fits_words` prove the tree's own words are at most `2 · MAX_CMD = MAX_STACK`, and
§5's `benv_words_le` proves the environment adds `2 · MAX_ENV`.  `sh_jpl.v` §1 turned
that into `MAX_WORDS = 2·MAX_STACK + 2·MAX_ENV + 2` (16 642 cells) and §1.1 exported it
as the table's tenth field, so the emitter sizes `jpl_word_pool` from the artifact
instead of declaring it undimensioned.

What the number is *conditioned on* is the second `MAX_STACK`, and it is stated here as
a debt rather than a fact: an `FFor`/`FCase` frame holds the **expansion** of a tree
list, and expansion can multiply word count, so the live expanded cells equal the
tree's own occurrences only under the step-machine invariant "at most one live frame
per source node" — §7.2, unwritten.  If 5-B.3's measurement refutes it, `MAX_WORDS`
rises with it (the caps table and the gate re-pin together), or the machine grows a
pool-exhaustion check that saturates to `BLimit` instead of an invariant that makes
overflow impossible; either way the choice belongs to the model, not to an array
dimension invented at the emitter.

**Measured cost of the decision.**  A `jpl_text` cell is 1 028 B (§4/R2's inline
`uint32` codes), and §6.2's headroom of 2 doubles the capacity, so the slab is
`2 × 16 642 × 1 028` = **34 215 952 B ≈ 32.6 MiB of static extent** — it dominates every
other pool: the seven pools beside it total **635.0 KiB**, of which 187.0 KiB were the five
5-B.2 had already dimensioned and **448.0 KiB** are the two node pools 5-B.2c added
(`jpl_cmd_pool` 8 192 × 16 B = 128.0 KiB, `jpl_frame_pool` 16 384 × 20 B = 320.0 KiB).  Two
consequences are
recorded rather than smoothed over: the per-cell width is the lever (a proved
`code < 256` would let R2 use `uint8_t` codes and cut the slab ~4×, but
`sh_concrete.v` §1 only *intends* that bound, so narrowing here would be an unproved
claim — follow-on, not chosen), and a static extent this large is a fact the JPL.7 host
must face when it links, which is why it is printed in `layout.txt` rather than left to
the reader of a header.

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

### 6.2 The four choices the derived layers could not derive

Everything in `verify/c/sh_run_jpl.h` is derived from a `.mli` line plus a capacity
folded out of the `.ml`, **except** three decisions, which the emitter numbers the same
way `verify/c/layout.txt` prints them so a reader can trace any number back to one of
them.  They are recorded here rather than hidden in the tool because §2's single-source
rule is about *semantics*: a layout choice is allowed to be a choice, as long as exactly
one place owns it and it is stated.  **5-B.3a (2026-10-05) added a fourth.**  It is not a
choice about the header but a choice about *what may stand in for the live set* — the
input decision 3 was waiting for — and the census's measured answer is that nothing in the
artifact's text supplies it yet, so the placeholder stays rather than being replaced by an
invented number.

| # | choice | what was picked | why the artifact does not decide it |
|---|---|---|---|
| 1 | which declared types are **pooled** | `cmd`, `frame` — and each now also gets its **node pool**: `jpl_cmd_pool` of `MAX_CMD` cells × headroom, `jpl_frame_pool` of `MAX_STACK` × headroom, registered by the same rule (`node_layer`) that emits the node struct | `cmd` is forced (it reaches itself); `frame` is bounded in shape (4 fields) and could be by-value, but §1's cap comments describe a *frame pool* (`MAX_STACK` = "explicit machine stack frames"), and a by-value frame embedded in a list cell would size the stack pool by the widest constructor instead of by `MAX_STACK`.  Picking the comment over the smaller encoding is the one place where the model's *intent* outranks the layout's arithmetic.  The choice has two halves — the list of pooled names and the cap that sizes each — and 5-B.2c (2026-10-05) made them check each other: a name in `pooled_types` with no `pool_cap` entry is a hard refusal, because the silent alternative was a by-value layout of a type the decision says is pooled.  Before that fix the header dimensioned only the two types' *list* cells, so `cmd`/`frame` nodes were declared and never allocated |
| 2 | which cap sizes which **list pool** | `pair(text,text)` → `MAX_ENV`; `frame` list → `MAX_STACK`; every other list kind → `MAX_LIST` | a list's cap depends on which list it is, and OCaml types do not carry that name.  The mapping is justified per kind by §5's `wf_benv` (an env is `MAX_ENV` pairs) and §1's `MAX_STACK` comment; the rest fall to `MAX_LIST` = "any intermediate list length" |
| 3 | the pool **headroom** factor | 2 | a pool must hold the live set *and* the garbage produced between step boundaries, and the per-step allocation bound is not yet established by proof or measurement (decision 3's open half).  So each pool is `cap × 2`, one doubling that is explicitly a placeholder until 5-B.3's allocation census replaces it with a measured number.  *[**§6.7 / 5-B.3b-ii-b-2** (2026-10-05) gives the doubling its meaning without replacing it: the two halves become the from-space and the to-space of a copying collection, so the factor is no longer a guess about garbage but the shape the collector requires — and the number it protects, the live-set bound, is now **checked** (`BLimit` on to-space overflow) rather than trusted.  Decision 4 is unchanged: the measurement that would retire `2` belongs to JPL.7's high-water mark, and the emitted `_<stem>_peak` is the instrument for it]* |
| 4 | what number the placeholder is allowed to be replaced **by** (added by 5-B.3a, 2026-10-05) | nothing yet: the census reports **allocation sites** per pool (7 pools demanded, 309 allocation sites, 8 of them still type-variable) and states explicitly that a capacity is `sites × loop trips`, so the `× 2` stays a placeholder with a *named* owner — JPL.7's measured per-step high-water mark | a pool must hold the greatest number of cells **live at one step boundary**, and that is a property of executions, not of the artifact's text: no walk over the bytes can produce it, and reading the site count as an extent would be a silent substitution of a measurable number for the one that matters.  5-B.3a's obligation 1 is the refusal to make that substitution |

Decision 3 is also why the header's pool sizes are `#define JPL_POOL_<KIND>` rather than
bare dimensions: the factor appears once, in the emitter, and every cell count in the
report is printed as "n cells × headroom 2" so the arithmetic is visible.  Decision 4 is
why the census's pool rows are headed "**sites** in a sig / built by" and never "cells":
the same column that makes the demand check possible (`jpl_word_pool` demanded by 15 sites)
is the column that cannot say how many words are live at a step boundary, and the report
prints that limit as its own section rather than leaving it to the reader.

### 6.3 The lowering schemas the census measured (normative list, 5-B.3a)

§6.1 states what the emitter is *allowed* to lower (tail loops → `while`, length-bounded
structural recursion → bounded copy loops).  5-B.3a measured what the shipped closure
actually contains, and this list is now the normative input to 5-B.3b: a binding may be
lowered by the schema its class names, and a binding in no class is a refusal, not an
invention.  Counts are over roots `mrun_c,step_c` — **47** members, **17** of them defined
by fixpoint — and are printed by `verify/c/jpl_lower.ml` into the tracked
`verify/c/lowering.txt`, which gate block **2f** byte-compares.

| class | count | lowering target, and why it is expressible without recursion |
|---|---|---|
| straight-line | 26 | ordinary statements: no self-call, so nothing to convert.  Includes the cap bindings themselves (`mAX_WORD`, `mAX_LIST`, `gLOB_FUEL`, `mAX_FUEL`), which are data and must not be read as code |
| fuel tail loop | 7 | `while (fuel > 0) { fuel -= 1; body }` — the fuel arrives as a *parameter*, so the caller's bound is the loop's bound: `glob_it`, `match_any_iter`, `setv_it`, `expand_go`, `enter_case_c`, `mrun_c`, `nat_digits`.  Each row also names **where its first fuel comes from** (`parameter f (argument 1 of this binding)`), which is what makes the loop's bound a traced quantity rather than a guess |
| fuel idiom, one trip (no self-call) | 4 | **no loop at all**: the `ExtrOcamlNatInt` nat-destruct value `(fun fO fS n -> if n=0 then fO () else fS (n-1))` is present but its step binder never calls the binding back, so it runs one trip and lowers to `if (n == 0)` (JPL.6 must not read it as recursion).  `nat2text`, `enter_seq`, `enter_for_c`, `step_cmd_c` — and `nat2text` is the case whose step binder is *unnamed*, so the decremented fuel is discarded |
| structural tail loop | 3 | `while (handle != JPL_NIL) { cell = pool[handle]; body; handle = cell.next }` — decreases on a cons tail, whose length the enclosing case already bounds (`teqb`, `getv`, `rev_append`) |
| `BOUNDED FOLD (non-tail)` | 5 | **rewrite required, model side.**  `length`, `app`, `rev`, `forallb` and `branch_need` recurse in a non-tail position, and D-60411 forbids recursion, so no `while` exists for them: each is a 5-A-style Coq obligation, not an emitter trick.  This is decision 3's other half — until it lands, 5-B.3b emits *declarations* for these five and no bodies |
| operator alias | 2 | `add` → `+`, `mul` → `*` under the extraction hooks; they print as `let rec` and are dropped, which is why an inventory that counts them as recursions is wrong |

The three readings that accompany the split are the ones JPL.6 and JPL.7 consume:

- **R8's instance set, measured at the call sites**: 5 polymorphic bindings, **29** use
  points, **6 closed** instances (one C function each) and **6 still open**.  Every open
  instance is a *self*-use of a binding the interface itself declares polymorphic, so the
  shipped closure never decides its layout and 5-B.3b must not either — the honest output
  is the same PENDING the header already prints.
- **First-class functions**: **68** lambda sites, each positioned in one of the four places
  a lowering can absorb (a fuel continuation, an argument at a known call site, a redex
  applied at its own site, or the binding's own value), and **0** sites in a position no
  rule covers.  That zero is *asserted by the gate*, because a function value outside those
  four could only become a function pointer, which D-60411 forbids.
- **How the caps are enforced**: **4** comparisons against a locked cap (`branch_guardb`
  ×3, `expand_c` ×1) and **3** caps *handed to a call instead of compared* (`MAX_FUEL` as
  `setv_it`'s first argument twice, `GLOB_FUEL` as `match_any_iter`'s once, inside a
  computed sum).  A cap with 0 comparisons is therefore not evidence of an unenforced cap —
  which is the reason the census prints the handed column at all, and the reason
  `MAX_STACK`'s **0** of either kind is a finding: nothing the emitter lowers bounds the
  machine's stack depth (§6.2 decision 3's debt, 5-B.3a's obligation 3).

**5-B.3b-i rendered the first half of this list: the ABI.**  The **6** closed instances the
first reading above counts are now `verify/c/sh_run_jpl_abi.h`, and the rendering is a
*declaration* layer and nothing more — which is what the table's `BOUNDED FOLD` row
prescribes: **4** of the 6 carry that schema (3 declared with a body owed, the 4th not
nameable at all) and the other **2** are `rev_append`'s two instances, structural tail loops
§6.1 already licenses.  What the render measured about itself: **5** prototypes exist and **1**
is **refused** — `forallb` at its single call site closes to `(text -> bool) -> text list ->
bool`, so its parameter 1 is function-typed, no C type names it, and the only thing that
could is the function pointer D-60411 forbids.  That refusal is *printed, not failed*,
because `forallb` is already in the fold row above: a refusal with a named owner is a finding,
and an unowned one (`abi_blocked_outside_fold_set`) is the assertion.  Two invariants hold the
layer together.  **One naming rule**: the C type names in the ABI come from `jpl_ast.ml`'s
`value_name`, which `jpl_emit.ml` now calls for its own typedefs too, so 2e's layout header
and 2f's ABI header cannot state two variants of R1–R4; since 5-B.3b-ii-a the *symbol* rules
(`c_fn`, `c_upper`, `data_macro`, `cap_macro_of_data`) live in the same reader and the emitter's
hand-typed cap-name list is gone, so the definition a renderer writes, the prototype the ABI
writes and the `#define` the layout writes are one spelling of one name.  **Closed accounting**: block 2f
asserts `abi_instances == instances_closed`, prototypes + refusals == rendered, expressible +
owed == prototypes, compares those three against the rendered file's own declaration, refusal
and declaration-only comment lines, and then compiles the header *pair* under 2e's flags.  The
compile is the rung with unique teeth: a scratch experiment that made `value_name` return a
name the layout header never typedef'd left **every** SUMMARY count identical and failed only
at the compiler — which is why the accounting alone would not have been a gate.

**5-B.3b-ii-a rendered the second half: the bodies that need no pool, no allocator and no
function value.**  §6.3's shape is not the last word — a shape is still not a statement — so
§6.4 asks which bindings can become C *today*, and the answer came from running the renderer
rather than from predicting it: **4** of the 47 members are emitted as
`verify/c/sh_run_jpl_bodies.c` (`bstat`, `is_digit`, `is_alpha`, `is_name`), **2** of them
citing a data constant by its header macro, and the remaining 43 are rows naming the pooled
type (13), the §6.3 schema (15), the un-writable construct (2) or the fact that they need no
body at all (13 `DATA` + 2 `ALIAS`).  The two `ALIAS` rows arrived with a cross-rung finding
this section owns jointly with 2e: `jpl_add`/`jpl_mul` have a prototype in `sh_run_jpl.h` and
no definition anywhere, because their body IS a C operator — either the prototype goes or
JPL.6's lint forbids the by-name call, and inventing a definition would be a second lowering of
an operator §6.3 already replaced.  Every rendered body is then swept against the extracted
kernel it came from, over the artifact's whole bounded `nat` domain (§6.4's differential), so
"renderable" and "correct" remain two measured claims rather than one.

**What the census cannot answer, and who owns it.**  Extent vs site count is decision 4
above; the five non-tail folds are model-side rewrites; the stack-depth guard is either a
saturating check 5-B.3b emits or a bound `sh_jpl_run.v` proves; the 8 allocation sites that
still carry a type variable yield no representation from their own text.  All four are
printed inside `lowering.txt` under "WHAT THIS CENSUS CANNOT ANSWER", so a stage cannot be
reported as closed by a measurement that does not measure it.

### 6.4 What a body needs before it can be rendered (normative list, 5-B.3b-ii-a)

§6.3 decides the *shape* of a control flow; a shape is still not a statement.  Before any
body is emitted, one more question has to be answered per binding, and it is answerable from
the artifact's bytes: **does this body need a pool, an allocator, or a function value?**  A
`while` over a `text` walks handles the representation layer owns, so a body whose every
construct is scalar needs none of them and can become C today; a body that builds a value
cannot become anything until the step-boundary copying of decision 3 exists.  Guessing which
is which by binding name is the invention this section forbids — and so is classifying bodies
by rules of the census's own and then having a separate emitter follow different ones, which
is §2's forbidden second model of one artifact.  So **the verdict IS the renderer's own trial
result**: the licensed set below is implemented once, as `render_def`, and run as a trial over
all **47** closure members.  A body the trial accepts is emitted into
`verify/c/sh_run_jpl_bodies.c`; a body it refuses is reported in the refusal's own words,
naming the construct or the pooled type that made it fail.  The verdict column is therefore
not an opinion about the emitter — it is one of its runs.

| verdict | derived from | what it licenses |
|---|---|---|
| `DATA` | arity 0 **and** `try_fold` yields a numeral | nothing to render: its C form is a `#define` **2e already emitted** — `JPL_MAX_*`/`JPL_GLOB_FUEL` for the seven caps, `JPL_C_*` for the rest (`b_0` = 48, `b_uscore` = 95).  A body may reference it **only by that macro name**, never by a re-typed numeral, so one number keeps one name |
| `ALIAS` | §6.3's operator-alias class (`add`, `mul`) | no definition at all: the extraction hook makes it `+`/`*` at its use sites, which is why counting it as a recursion is wrong and counting it as an emittable function would be wrong twice |
| `RENDER` | the trial itself: `render_def` returned a definition, which means no rule below fired and every construct was inside the licensed scalar set | a C definition in `verify/c/sh_run_jpl_bodies.c`, plus one call in each generated differential driver |
| `OWED-REPRESENTATION` | the binding's **signature** takes or returns a pooled array, **or** §8 records an allocation site inside its body — both directions count, because building a value needs the allocator and reading one needs the cell to exist already | nothing yet: the value lives in a pool, and the pool's cells are produced by decision 3's step-boundary copying, which 5-B.3b-ii does not have |
| `OWED-SCHEMA` | §6.3's shape statement: a direct self-call above 0, or a class whose first statement has no C form yet (`BOUNDED FOLD`, a fuel loop, `BLOCKED`) | nothing: the shape does not exist in C (D-60411 Rule 6), so it is a 5-A-style model-side rewrite, exactly as §6.3's row says |
| `OWED-CONSTRUCT` | a construct outside the licensed set, **named** | nothing, and the name is the finding: the row says *which* construct, because a verdict without a named blocker is an assertion, not a census |

The **licensed scalar set** is closed and short, and everything outside it is
`OWED-CONSTRUCT` with the class printed: folded integer constants; `ident` resolving to a
parameter, a `DATA` binding, or a callee already verdicted `RENDER`; `if`/`then`/`else`;
the boolean and relational operators `(&&)`, `(||)`, `(=)`, `(<=)`, `(<)`; and patterns of
class `var`, `any` or `constant` only.  Deliberately *not* licensed: a `construct`/`tuple`/
`variant` expression (that is an allocation, so it is `OWED-REPRESENTATION` before it is
anything else), a `match` on anything but a scalar (the pool's tag read is decision 3's), a
lambda in any position but the binding's own value (D-60411 forbids the pointer it would
need — the same reason §6.3's ABI row refuses `jpl_forallb_1`), and a self-call (its schema
is §6.3's row, not this rule).

The rules are tried in **dependency order** — `ALIAS`, `DATA`, `OWED-SCHEMA`,
`OWED-REPRESENTATION`, then the renderer's own licensed set — because one body can match
several of them and the report has to say which one owns it.  The order is not cosmetic:
`teqb` reads a word slab, so the representation rule would refuse it, but its schema is a
structural tail loop and §6.3 owns that rewrite first.  `raw_bword` and `expand_c` show the
other half of the
same rule — straight-line, consing nothing, and still taking or returning a slab — which is why
`OWED-REPRESENTATION` reads the **signature** as well as the allocation sites.  Only the last
rule is this section's own set; the four before it restate §6.2's and §6.3's obligations, so a
verdict here never hides a debt an earlier section already owns.  What a verdict *does* hide is
the second debt on the same row, which is §6.5's measurement.

**Measured**, over the shipped closure (47 members in artifact order, straight out of the
trial): **11 `DATA` + 2 `ALIAS` + 4 `RENDER` + 13 `OWED-REPRESENTATION` + 15 `OWED-SCHEMA` +
2 `OWED-CONSTRUCT` = 47**.  The four rendered bodies are `bstat`, `is_digit`, `is_alpha` and
`is_name`, and `is_name` is the reason the trial is run as a **fixpoint** rather than a single
pass: it cites `JPL_C_B_USCORE` and calls `is_alpha`/`is_digit`, so it becomes renderable only
once its callees have verdicts — a callee with no verdict yet leaves the caller *undecided for
this pass*, which is not a refusal.  The two `OWED-CONSTRUCT` rows (`isz`, `step_c`) each print
the construct that failed, because a verdict with no named blocker is an assertion rather than a
census.

`ALIAS` arrives with a cross-rung **finding that has an owner, not a failure**: 2e's
representation header carries `jpl_add`/`jpl_mul` prototypes for bindings §6.3 says have no
definition, because the extraction hook spells them as `+`/`*` at the use site.  Either 2e drops
those prototypes or JPL.6's lint forbids calling them by name — inventing a definition here
would be a second lowering of an operator §6.3 already replaced.  The census prints the finding
in those words; 2f echoes it rather than re-summarising it.

Two invariants hold the verdicts together, and both are gate assertions rather than prose.
**Exactly one verdict per member**: the six classes partition the **47** closure members, so
their counts sum to 47 and a binding that received two verdicts or none fails the census.
**Every `DATA` name resolves in the header that owns it**: the macro a rendered body cites is
looked up in `sh_run_jpl.h`'s own `#define` lines, which is the same cross-rung direction 2f's
pool check uses — a rendered body that cites a macro 2e never emitted compiles nowhere, and
the failure must land here rather than in JPL.7's host.

**`RENDER` is a claim about constructs, not about behaviour.**  Saying a body needs no pool,
no allocator and no function value does not say the emitted C computes what the artifact
computes.  That is a second, independent rung and part of this stage: the rendered bindings
are swept over the artifact's own nat domain — `0 … MAX_FUEL`, **136 449** points, the bound
the caps table locks rather than a sampled subset — once through OCaml against the extracted
kernel and once through C against the emitted definition, and the two transcripts must agree
byte for byte.  **Neither driver is hand-written**: the census generates
`verify/c/jpl_bodies_diff.c` and `verify/c/jpl_bodies_diff.ml` from the same `RENDER` rows
that wrote the bodies file, so the set swept, the arity of each call and the fuel index's
placement are one list read twice rather than two lists that happen to agree, and the transcript
length is checked against the report's own `sweep_domain` key so no driver picks the range it is
testing.  The sweep is honest about its own shape: a rendered body of exactly one `nat`
parameter is covered **exhaustively** (the index is that parameter), while a body of another
arity is exercised along a **diagonal** — one index driving every argument — and the census
prints `bodies_swept_exhaustive` and `bodies_swept_diagonal` so the two claims cannot be
confused.  A differential over the whole domain is what makes "this body is simple enough to
render honestly" a measured statement; without it `RENDER` would be the census's opinion of
itself.

*Measured*: both drivers print **136 450** lines and `cmp` reports the transcripts identical,
over **4** exhaustively swept bodies (`bstat`, `is_digit`, `is_alpha`, `is_name`) and 0
diagonal ones; the swept fields take **5** distinct tuples across the domain, which is the
rung's own guard against a pair of constant transcripts agreeing for free.

*What this section does not close.*  43 of the 47 members have no C body after this stage: 15
wait on §6.3's loop schema, 13 on decision 3's step-boundary copying and `MAX_STACK`'s depth
guard, 2 on a construct the licensed set names but cannot write.  The five folds and
`forallb`'s function-typed parameter stay model-side (§6.3, and 5-B.3b-i's limit (iv) about
`branch_guardb`), and headroom 2 is untouched, because a rendered scalar body allocates nothing
and therefore measures nothing about extent.  `DATA` and `ALIAS` are 13 more members that need
no body by construction, so "no body" is not the same statement as "not renderable" — which is
why the partition, not the render count, is the number the gate sums.

### 6.5 The second debt: what an owed row also touches (normative list, 5-B.3b-ii-b-0)

§6.4's rules are tried in dependency order and the first that matches owns the row.  That is
right for a *verdict* — one row must have one owner, or the partition cannot be summed — and
it is wrong for a *plan*, because a row stops reporting the moment its first debt is named.
An `OWED-SCHEMA` row therefore prints its §6.3 shape and never prints the pools its signature
takes or returns: 15 members are verdicted on their schema, and for all the census currently
says about the other 13 §6.2 obligations they carry, the reader has to guess.  For 5-A and
5-B.3a the guess cost nothing — a non-tail fold is rewritten model-side whatever its operands
are.  For 5-B.3b it costs the ordering: the emitter cannot lower a `while` whose operands are
pool handles until the allocator and the step-boundary copying exist, so **the set difference
between the two debts, not either verdict, is what a slice can render.**

So the rule this section adds is narrow and is about reporting, not about licensing:

> **A binding may owe two debts — §6.3's shape and §6.2/decision 3's representation — exactly
> one verdict owns the row, and the census must print both.**

**Printed from one reading, so it cannot become a second model.**  The column is computed by
the same `pools_of` the renderability trial already consults, over the same shared reader's
types: nothing in §6.4 is re-derived here, and a row cannot report a pool in this column that
the trial declined to look at.  §6.4's table, its six verdicts and the partition that sums to
**47** are unchanged; no body is emitted by this section; `RENDER` stays the only verdict that
writes C.  A measurement that changes no verdict is the point — the alternative, promoting
`OWED-REPRESENTATION` above `OWED-SCHEMA`, would have re-labelled 15 rows and silently moved
the §6.3 obligation to a section that does not own it.

**What "no pool" has to mean, since it can mean three things.**  The representation measure is
a walk over the artifact's *declared* types, and it stops in three different places.  Conflating
them would let a zero read as freedom:

| a pool-free row because | how the walk sees it | what it still owes |
|---|---|---|
| its signature really is scalar | every position resolves to `nat`/`bool`/`unit` | only §6.3's shape — this is the case the slice order was written for |
| a list-shaped position still carries a **type variable** | `L_list e` with `e` unresolved, so `pool_of` returns nothing | decision 3 *and* R8: no cell type exists to size a pool with until the instance is closed (§6.3's instance set lists exactly which of these are still open) |
| a position is an **opaque declared type** | a `type … = …`-declared record or variant the walk does not descend into fields of | decision 3 possibly, and the census cannot tell — `step_c : cfg -> out` prints no pool although `cfg`'s `ck` field *is* the machine stack |

The third row is a measured limit of the measure, and it is also the explanation of a finding
§6.4 left open: 2e's header declares `jpl_frame_pool` (decision 1) and this walk demands no
frame node cell from anything, which the gate prints as "declared but not demanded".  A walk
that stops at a record boundary is why.  Changing the walk to descend fields would move rows
between §6.4's verdicts, so it is a slice of its own and not something this section does
quietly — until then every count of pool-free rows in this report is a **floor**, and the
gate's own wording says so rather than leaving it to the reader.

**Slice order, and the consequence the column exists to settle.**  With both debts printed, the
ordering below is forced by data instead of by taste.  The open question it settles is the one
§6.4's closing paragraph left standing: 15 rows wait on a `while` form, 13 on decision 3, and
if the two sets overlap then the loop forms land *after* the pool half and render nothing on
their own.

| slice | deliverable | owner | what it can render, and what it cannot |
|---|---|---|---|
| ii-b-0 | **this section**: the dual-debt column, its keys, the floor wording | §6.2 decision 3, §6.4's table | nothing — a measurement rung; its output decides which of the slices below is worth doing first |
| ii-b-1 | pool **allocator + handle runtime**: a bounded allocator per declared pool, handle types, saturate-to-error on exhaustion — **specified as §6.6, landed as `sh_run_jpl_pools.c`**; §6.6 chose a **region** with `reset` over a free list, because a per-cell `release` is ii-b-2's reachability rule before it is a function | decision 3 (extent half still open, §6.2 decision 4) | makes a *cell* exist; still no body, because a body must also be allowed to return one |
| ii-b-2 | **step-boundary copying**: values are copied into pool cells at a step boundary and reads take handles, per decision 3's collection rule — and with it the **reachability rule §6.6 declined to invent**, which is what makes a per-cell `release`, or a survivor surviving `reset`, meaningful at all.  **Specified as §6.7**, which splits it into ii-b-2a..e and resolves §6.1's "not a region reset" as *reset-without-evacuation*; the first slice is the edge table, because R7's one-word slots currently erase which slot is a handle.  **ii-b-2a landed 2026-10-05, ii-b-2b 2026-10-06 and ii-b-2c 2026-10-06**, so the classes, the
two-interval space and the per-cell move all exist; what does not exist yet is the *caller* — no root
list, no `jpl_collect()`, so no kernel step boundary reads a table to fill the other interval | decision 3 | unlocks the 13 `OWED-REPRESENTATION` rows whose schema is straight-line or a one-trip fuel idiom — the first set that can become C bodies |
| ii-b-3 | **fuel tail loop → `while (fuel > 0)`** | §6.3's fuel class (7 bindings) | the loop form is expressible today; a *body* needs ii-b-1/2 for its operands, which is what the column measures |
| ii-b-4 | **structural tail loop → handle-walk `while`** | §6.3's structural class (3 bindings, and `rev_append`'s 2 closed instances, the only ABI bodies §6.3 calls expressible) | same dependency as ii-b-3, plus the pool's `next` chain as the walk's advance |
| ii-b-5 | **`MAX_STACK` depth guard**: a saturating check, or a model-side proof of the bound the pool size already assumes | decision 3's named debt, §6.3's `MAX_STACK` finding (0 checks of either kind) | renders nothing; it is what makes the frame pool honest rather than decorative |
| ii-b-6 | the **5 `BOUNDED FOLD` rewrites** + `forallb`/`branch_guardb` specialisation, each a Coq obligation in the 5-A.2/5-A.3/5-A.7 style | §6.3's fold row and 5-B.3b-i's limit (iv) | nothing in C until the model side lands; §6.3 forbids the emitter from inventing a `while` for a non-tail recursion |

Nothing in ii-b-1 and ii-b-2 depends on a loop form, and ii-b-3/4 depend on both — so the
order below is not a preference about which rewrite is more interesting.  *Which* of the 15
schema rows actually carry the second debt is the measurement this section commissions; the
answer goes into the table of slices the next time one of them is cut, and the census prints it
every run.

**New measures, all marked by this section and all read by the gate as keys** (never as
formatted prose, per §6.4's convention that a missing key is a failure and not a zero):
`owed_schema_also_pool` and `owed_schema_pool_free` split the schema set, the three
`owed_schema_pool_free_{var,opaque,scalar}` keys name *which* of the three reasons a
pool-free row has and must sum to the second, `owed_construct_also_pool` does the same for the
two `OWED-CONSTRUCT` rows, `dual_debt_rows` counts rows carrying both debts, and
`debt_unaccounted` is the consistency assertion: **0**, meaning no row's debts contradict its
verdict — an `OWED-REPRESENTATION` row with nothing in any pool, or a `RENDER`/`DATA`/`ALIAS`/
`OWED-CONSTRUCT` row that turns out to touch one, would say that §6.4's rule order was not
the dependency order it claims to be.

**One cross-check this section owes the second table row in particular.**  A row classified
pool-free *because a position still carries a type variable* is not free in the sense the slice
order cares about: §6.3's instance set may already have closed that variable at a call site,
and if it did, the pool is decided — in the ABI header — and only this walk failed to see it.
So the census reads each such binding's **rendered closed instances** (`print_abi`'s own rows,
the same list that wrote `sh_run_jpl_abi.h`) and marks
`owed_schema_free_var_pooled_instance`: the number of variable-classified schema rows with at
least one closed instance whose parameters or result sit in a pool.  A positive count is a
finding, not a failure — the instance is the artifact's decision and the signature is the
interface's — and it is the count that says whether `ii-b-3`'s loop forms have any row that can
skip `ii-b-1`/`ii-b-2`.  A zero would be the opposite: bindings whose layout the shipped closure
genuinely never decides, still open in §6.3's sense.

*Measured* (5-B.3b-ii-b-0, over the same 47 members and the same `pool_of` reading): of the
**15** `OWED-SCHEMA` rows, **10** also touch a pool — `teqb`, `getv`, `nat_digits`, `glob_it`,
`match_any_iter`, `branch_need`, `setv_it`, `expand_go`, `enter_case_c` and `mrun_c`, and every
one of them reaches `jpl_word_pool`, which is the cheapest possible statement of why a `while`
cannot be written for them today: its operands are handles into cells nothing produces yet.  The
other **5** are pool-free and *all five* are pool-free because a position is still a type
variable (`length`, `app`, `rev`, `rev_append`, `forallb`); **0** schema rows are opaque-record
pool-free and **0** are pool-free in the plain scalar sense.  The cross-check then closes the
question the hand-read had got wrong: **4 of those 5** have a closed instance in
`sh_run_jpl_abi.h` whose parameters or result **are** pooled (`length` → `jpl_text_list_pool` +
`jpl_word_pool`, `rev` and `forallb` → `jpl_word_pool`, `rev_append` → both), and only `app` is
never closed anywhere in the shipped closure — §6.3's open set, exactly as its row says.  So the
answer §6.4 left open is measured rather than argued: **a loop form landed alone renders zero
bodies**, and `owed_schema_pool_free_scalar = 0` is the number that says so.
`owed_construct_also_pool = 0` — and that zero is the §6.4 rule order *holding*, since the trial
consults pools before its licensed set, so a construct refusal cannot coexist with a pooled
value on the same row.  `dual_debt_rows = 10` and the refused rows that touch a pool are **23**
= 10 + 0 + 13, which is the identity check 5 asserts.  `debt_unaccounted = 0`.  The two
`OWED-CONSTRUCT` rows are where the opaque family actually lives (`isz` behind `cstate`,
`step_c` behind `cfg` and `out`), which is the field-boundary limit's own evidence, and it is
the same evidence 2f's check 3 prints as `jpl_frame_pool` declared-but-not-demanded.
SUMMARY **35 → 44 keys**, `lowering.txt` **659 → 783 lines**, and no verdict count moved by
one — which is the check that this section measured rather than re-classified.

*What this section does not measure.*  Extent, again: a pool touch says a cell type is involved
in a binding, not how many of its cells are live at a step boundary, which is §6.2's decision 4
and still JPL.7's number.  Headroom 2 is untouched, because nothing was emitted here to
allocate.  And no behavioural claim: the emitted kernel's correctness stays with #26 and #27.

### 6.6 The pool runtime: how a cell comes to exist (normative list, 5-B.3b-ii-b-1)

§6.5's ordering puts this slice first, and it is the first slice of JPL.5-B.3 that emits
runnable C.  The gap it closes was already visible in the evidence: 2e's header declares
**eight** pools as `extern` arrays and nothing in the tree defines them — the file's own
comment says "definitions live in the emitted translation unit", and until this slice there
was no such translation unit.  A capacity no object carries is a number in a comment, and a
lowering that is told to "take a handle" has nothing to take a handle *out of*.  So the
deliverable is the mechanism decision 3 assumed without naming: for every declared pool, an
allocation point, a reclamation point, a handle type, and a saturate-to-error path a lowering
can read.

> **The rule: a pool's runtime is emitted from the same registry that sizes it.  A pool may
> not have a capacity without an allocator, and an allocator may not have a return type the
> registry did not give it.**

**A region, not a free list — and the reason is safety, not simplicity.**  The obvious
allocator keeps a stack of released cells and pops it.  That needs a `release(h)`, and a
`release` is only safe if something knows `h` is unreachable — which is exactly the rule
ii-b-2 has not written yet.  An allocator that can hand out a cell a survivor still points at
is not a simpler runtime, it is a wrong one.  So the runtime allocates **monotonically inside
a region** and returns every cell at once: the region boundary *is* decision 3's step
boundary, and "a pool must hold the live set and the garbage produced between step
boundaries" (§6.2's own words for headroom 2) is a description of a region, not of a free
list.  Reclamation at per-cell granularity is therefore not missing from ii-b-1; it is
owned by ii-b-2, because a per-cell free is a *rule about reachability* before it is a
function.

**The shape, per pool.**  `<s>` is the pool's stem — `word`, `cmd`, `frame`,
`text_list`, `frame_list`, `pair_text_text_list`, `cmd_list`,
`pair_text_list_cmd_list_list` — `C` is that pool's capacity macro, and the pattern is
written eight times by the emitter, never by a reader:

```c
/* the word slab: s = word, C = JPL_POOL_WORD = 33286 indices = 2 spaces × (16642 + 1) */
extern jpl_ref  jpl_word_next;     /* the CURRENT interval's allocation pointer, an absolute index */
extern jpl_ref  jpl_word_peak;     /* the most cells ONE interval ever served — a count, not an index */
extern jpl_ref  jpl_word_taken;    /* cells served, saturating at the counter's own top */
extern jpl_ref  jpl_word_refused;  /* allocations that found no cell: §4.2's edge */
extern jpl_text jpl_word_pool[JPL_POOL_WORD];
extern jpl_ref  jpl_word_origin[JPL_POOL_WORD];  /* §6.7: copied FROM, one entry per index */

jpl_wref jpl_word_alloc(void);           /* JPL_NIL when the current interval is full     */
jpl_ref  jpl_word_reset(void);           /* cells returned; next goes to the current base + 1 */
jpl_bool jpl_word_is_live(jpl_ref h);    /* h is a cell of the CURRENT interval           */
jpl_nat  jpl_pools_swap(void);           /* the one writer of the current interval        */
jpl_nat  jpl_pools_refusals(void);       /* the one sum the host reads                    */
```

Index `0` stays reserved — the header already says "index 0 is `JPL_NIL` and is never
allocated, so a capacity counts the reserved cell too" — and since §6.7's ii-b-2b **each
interval reserves its own**: a space of `C/SPACES` indices serves `C/SPACES - 1` cells, and the
two indices that name no cell are `0` and `cap + 1`.  That off-by-one is *a property the gate
measures*, not a convention: the probe allocates until it is refused, in **both** intervals, and
must be served exactly `cap` cells each time, where every bound is read out of the header's own
`#define`s.  `is_live` is then the three-bound interval test of §6.7 paragraph 4 — above the
current base, below the current top, below `next` — which is what turns a handle carried across
a swap into a decidable fact rather than a liveness analysis.

*How this differs from the one-region reading this section first landed, and why ii-b-2b had to
take the swap with it*: at one interval `C` was `2·cap`, `next` started at `1u`, `peak` was a
high-water index, and `is_live`'s interval test was observationally identical to `h != JPL_NIL &&
h < next` — so §6.7's design item (iii), a stale handle **below the current `next`**, could not be
fired by any probe.  The swap is therefore part of this slice and not of ii-b-2d: one global
`jpl_pools_space`, one writer `jpl_pools_swap()`, and 2d arrives to find the boundary already
crossable.  §6.6's *Measured* paragraph below is the two-interval reading, rewritten in the same
edit that re-pinned the evidence.

**Naming is derived, so it cannot drift.**  The stem is the substring of the array name
between `jpl_` and `_pool` — the same extraction that already spells `JPL_<KIND>` — so a pool
renamed by decision 1 renames its allocator, its four counters and its capacity macro in the
same keystroke.  Because those names live in the same C namespace as the kernel's, the gate
also refuses if any generated runtime name equals a closure prototype's name: §6.3's ABI and
§6.6's runtime must not both claim one spelling.

**Handle types: `p_handle` is the registry's missing column.**  Every handle in this project
is a `uint32_t`, so C's type system cannot distinguish a word handle from a `cmd` handle —
which is harmless for a human reading one file and fatal for a renderer choosing an allocator
by type.  The pool record therefore gains the handle type alongside the cell type, filled at
the three sites that register a pool (the word slab gives `jpl_wref`, the list rule gives the
handle it just typedef'd, the node rule gives `jpl_<nm>`), and `jpl_<s>_alloc` returns *that*.
A lowering can then ask the registry "what allocates a value of type `t`?" and get an answer
derived from the same lines that sized the cell — no table of pool names in the renderer,
which would be §2's forbidden second model of the layout.

**Saturation reaches the model through a handle, not through a carrier.**  §4.2's carrier is
Coq's `bres A = BOk A | BLimit`, and a runtime library has no `bres` to return: extraction
gives nothing for a function the model does not contain.  So an exhausted pool returns
`JPL_NIL` and increments its refusal counter, and the *lowering* is what turns a nil handle
into the model's edge.  That is not a new device — §5 already set the precedent for a
saturating boundary outside `bres`: `branch_guardb`'s failed guard "is read as the same
saturate-to-error edge as exhausted fuel".  A rendered body that ignores an allocator's nil
is therefore a conformance bug in the renderer, and it is checkable: nil is the one value no
successfully allocated handle can ever equal.

**The counters are the instrument decision 4 asked for, not its answer.**  Decision 4 refused
to read an *allocation-site count* as an *extent*, because the extent is a property of
executions.  A region allocator measures exactly that quantity at run time: `peak` is the
largest number of cells any single region held.  Stating it plainly keeps the honesty intact —
**with no kernel that allocates, every `peak` in this tree is 0**, so this slice ships the
instrument and not the number.  JPL.7 replaces headroom 2 when there is a measured peak to
replace it with, and the gate will print `peak = 0` as what it means rather than letting it
read as "the pool is nearly empty".

**`is_live` is a guard rail, not a liveness analysis.**  The runtime can answer one question
without knowing the graph: at one interval, `h != JPL_NIL && h < next` said `h` was handed out by
*this* region.  Since §6.7's ii-b-2b the question has one more bound and the paragraph's second
half is what changed: `h > CUR_BASE && h < CUR_TOP && h < next` also says `h` was born in the
interval that is *current*, so the stale handle the one-interval test could not see — one below the
current `next` but from the interval the swap abandoned — is now refused by a comparison, with no
reachability analysis anywhere.  What remains out of reach is the case no bounds test can express:
a handle into the *current* interval whose cell has been logically dead long before the interval
moves.  That is aliasing the copy rule must make impossible by evacuating survivors, and §6.6's
region design still does not clear cells.  So `is_live` makes a mistake *observable* in a probe —
now including the cross-interval mistake, which the gate fires on deliberately — while the
correctness of the copy discipline stays with #26 and #27, as everything behavioural in this plan
does.

**What this is *not*.**  §2.1 says transforms live in the Coq source and the emitter's one
mechanical duty is layout.  The runtime is layout's third person: `nat` → `uint32_t` and
`list` → static array are already here, and "a pool hands out bounded cells with a defined
failure" is the same kind of statement about representation.  **The Coq model contains no
store, and no kernel theorem changes because of this section.**  Cell *identity* — which
index a value got — is not modelled and is deliberately not observable in any result the
model states; what is bounded is the *number* of cells, which is decision 4's unproved half
and stays unproved here.  The mutable statics are also a single-thread claim: D-60411 allows
static objects (R5 requires them) and the machine is a sequence of steps, so the runtime has
one caller at a time and says so rather than pretending thread safety.

**Gate (three rungs inside block 2e — no new block, `verify_models.sh` unchanged).**  (1) The
emitted pools TU is compiled under the strict JPL flag set *without* `-fsyntax-only`, so the
definitions and every counter's arithmetic are checked by the compiler, including
`-Wconversion -Wsign-conversion` on the bound comparisons — the header's `-fsyntax-only` pass
could never see a defined object.  (2) A sweep generated from the header's own
`jpl_<stem>_alloc(void);` lines — one function per declared allocator, so the probe carries **no
number of its own** any more than the cap probe does — links against that TU and, per pool,
drives **both intervals** (the shape below is ii-b-2b's; at one interval the same sweep stopped at
the first `reset`): the first handle must be the interval's own base + 1, successive handles must
be distinct neighbours and `is_live`, `JPL_NIL` and the interval's own top index must never be
live, the interval must stop serving at exactly `cap` cells (`C/SPACES - 1`, read out of the
header's macros), `refused` must equal the attempts that produced no handle, three further attempts
must move `next` not at all, `reset` must return `cap` and leave `next` at its own base + 1, a
handle from the returned interval must read dead while `taken`, `peak` and `refused` read unchanged
(they are instruments, not part of the region), and a fresh `alloc` must hand the first index back.
**Then `jpl_pools_swap()` is called**: its return must be `(before + 1) mod SPACES` and agree with
the global, a handle kept from the interval just abandoned must read **dead while sitting below the
current `next`** (design item (iii) of §6.7, and the probe fails if that case never arose — the
rung measures the staleness, not just the code), an `alloc` before the rewind must be refused
rather than serve the new interval's reserved index, `reset` on the abandoned interval must return
**0** instead of wrapping its subtraction, the `origin` entry for that handle must read zero before
anything copies through it and must round-trip a written handle afterwards, the second interval must
then serve the *same* `cap` with `peak` still a per-region count rather than a doubled index, and
the sweep must hand the single global back so the next pool is measured on the interval its own
macros name — with `jpl_pools_space == 0u` asserted again in `main`, because one drifted pool is a
finding about the runtime, not about that pool.  Every bound in it is one of the pool's own
`JPL_POOL_*` / `JPL_<KIND>_*` macros, read out of the header, so the sweep and the allocator compare
against one constant.  (3) The report's `RUNTIME SUMMARY` keys are then
closed against each other, against the header and against the translation unit: a missing key is
a failure and not a zero (the census's convention, inherited),
`pools_with_capacity + pools_without_capacity == pools_declared`,
`allocators_emitted == resets_emitted == live_checks_emitted == pools_with_capacity`,
`counters_emitted == 4 × allocators_emitted`, `pool_arrays_defined == allocators_emitted`,
`refusals_sum_terms == allocators_emitted`,
`allocator_handles_defined_in_layout == allocators_emitted`,
`runtime_names_colliding_with_prototypes == 0`, `runtime_cells_total` equal to the sum of the
header's own macros, and the stems and macros in the report's table identical to the stems and
macros the header declares — three readings of one registry.  Since ii-b-2b the interval arithmetic
closes the same way: `runtime_cells_total == regions_per_pool × (space_cells_served_total +
allocators_emitted)` (the index domain divides back into the artifact's own caps plus one reserved
index each), `origin_indices_total == runtime_cells_total` with `origin_bytes_total == 4 ×` it and
`static_bytes_total_with_origins` the sum of the two byte keys, `interval_arithmetics_checked ==
allocators_emitted`, `interval_typedefs_emitted == 4 × allocators_emitted`, the header's own
interval `#define`s counted against `interval_macros_emitted == 6 × allocators + 1`, and the
indicator's assignments **counted in the file that defines it** — the definition plus exactly one
writer, so "one global, one writer" is a measurement rather than a sentence.  The vendored pin
count goes from two files to three: `sh_run_jpl.h`, `layout.txt`, `sh_run_jpl_pools.c`.

*Measured* (the numbers below are the tree's, re-pinned when **ii-b-2b** landed; what
5-B.3b-ii-b-1 first measured is the delta the paragraph names — and the counter figure below is
**2b's**, since **ii-b-2c** took `counters_emitted` **32 → 59** and `mutable_globals_emitted`
**33 → 68** while leaving every index, byte and origin figure here exactly as written, which is the
cross-check that a copy layer moved no domain): all
**8** pools are sized, so **8** allocators, **8** resets, **8** liveness checks and **32**
counters are emitted, over **80 660** indices and **34 868 416** bytes (**34 051.2 KiB**) of pool
storage, plus **8** `origin` tables of the same **80 660** indices — **322 640** bytes — for a
static price of **35 191 056** bytes, which is §6.7 paragraph 4's predicted total to the byte and
**0.93 %** above §6.6's `2·cap` reading rather than the doubling a naive two-pool layout implies.
**0** pools are unsized, so §6.6's other half — a declared type with no capacity
gets no runtime — is a rule the gate holds in reserve rather than one it exercised here.  The
sweep then reports, for every one of the eight: `cap` cells served in **each** interval
(`33 286` allocations across the sweep for the slab, `258` for the narrowest cons-pair pool — the
count spans both intervals plus the one reallocation phase 4 makes), `refused == 6`
(the three attempts past each interval's bound, the one refusal demanded of an un-rewound region
after the swap, and the attempt that ended each fill), `peak == cap` in both intervals — a
per-region count, where the high-water index would have read roughly `2·cap` — **2** stale handles
rejected while below the current `next`, and `0` assertion failures across all of them, with
`jpl_pools_refusals() == 48` equalling the per-pool sum and `jpl_pools_space == 0u` both after each
sweep and after all eight.  `runtime_names_colliding_with_prototypes == 0`, i.e. none of the
identifiers the two slices add — `_next`, `_peak`, `_taken`, `_refused`, `_alloc`, `_reset`,
`_is_live` and, since 2b, `_origin` for each of the eight pools, plus the one exported sum, the
single `jpl_pools_space` and its one writer `jpl_pools_swap()` — shadows a symbol of the
shipped closure, which is the check that lets §6.3's ABI header and this runtime share one
translation unit.  **ii-b-2c re-measured the same key at 0** with its own names in the set —
`_evac`, `_word_at`, `_word_put`, `_scan`, `_queue_start`, `_scan_one`, `_drain` per pool and the
one `jpl_pools_evac_by_class` — which is the rung that says the collector layer can live in the same
unit as the kernel's declarations.  The header
grows **376 → 477 → 557 → 805 → 1176** lines and the pools TU **363 → 487 → 769 → 1834**, and the
report carries the `POOL RUNTIME` table plus the interval keys in its `RUNTIME SUMMARY` (**25**
after 2b, **38** since 2c's eleven collector keys);
no §6.3, §6.4 or §6.5 count moved, and 2f's census still reads eight declared pools from the
same grep — 2b put its two intervals *inside* one array's index domain, so the name count is
unchanged, which is the property §6.7 paragraph 4 claimed and the grep confirms.
The rung's teeth were re-checked for this slice by mutating each of the following in turn, each
reverted before the next: reading `is_live` as §6.6 did (`h > CUR_BASE` → `h > 0u`, which is the same
test since `JPL_NIL` is 0) left every other number identical and produced **16** probe failures — the
two stale-handle assertions on all eight pools — and exited non-zero, which is what says the pair is
the slice's rung rather than its arithmetic; sizing the array as `SPACES × cap` made the emitted
`jpl_check_<s>_two_regions` and
`_regions_tile_the_array` typedefs refuse the header at compile time, which is the case for having
the relations in C rather than in prose; giving one registration site the old `2·cap` literal fired
the emitter's own `INTERVAL REFUSED` before any file was written; and a second assignment to the
indicator (measured directly: the TU's assignment count goes **2 → 3** against the rung's `1 +
space_globals_emitted`), and a dropped `JPL_<KIND>_LO_BASE`, each moved exactly the count that was supposed to
notice.  Because some of those mutate the *shipped* emitter, they were run against a scratch mirror of
`verify/c/` that reproduced a green control run first — the guard on `jpl_emit.ml` is right to
refuse an in-tree weakening of a landed invariant.  Every `peak` attributable to the *kernel* is still **0**, because no kernel body calls an
allocator yet — the number above is the sweep driving the runtime to its bound, which is exactly
the distinction §6.6's "instrument, not the number" paragraph was written to keep.

*What this section does not do.*  It renders **no body** — §6.4's `RENDER` verdict stays the
only verdict that writes a definition, and the four scalar-leaf bodies in
`sh_run_jpl_bodies.c` are untouched by anything here, which the gate checks byte-for-byte.
It measures **no extent** for a real run, for the reason two paragraphs above.  It changes no
§6.3 schema, no §6.4 verdict and no §6.5 count: the census cross-checks its pool *demand*
against the header's *declaration*, and this slice adds declarations that do not end in
`_pool[`, so the declared-pool set the census compares against stays the same eight.
Per-cell release, the two loop forms, the `MAX_STACK` depth guard and the five model-side fold
rewrites stay where §6.5's table put them; **the copy rule this section declines is §6.7**.

### 6.7 The step boundary: two spaces, forwarding, and what "live" means (normative list, 5-B.3b-ii-b-2)

§6.6 ended by *declining* a rule: an allocator that hands cells out monotonically can only
be safe if something else decides when the region may rewind.  That "something else" is
decision 3's collection, and this section is its normative content.  It is written before the
code because §6.1 already committed this project to a specific collector — and because that
sentence and §6.6's landed `reset` appear to disagree, which is the first thing this section
has to settle rather than paper over.

> **The rule: a collection happens only where every live handle is reachable from the machine
> state, and reachability is read from a table the emitter derives from the same `.mli`
> declarations the layout was built from.  A collector may not hard-code an edge, a root, or a
> slot's meaning; and a cell that cannot be reached may not be assumed reachable.**

**The apparent contradiction, and why both sentences stand.**  §6.1 says reclamation is
"a copying collection at the step boundary … **not** by a per-step region reset, which the
sharing in a functional program would make unsound", while §6.6 shipped `jpl_<s>_reset()` as
the reclamation point.  The two are not alternatives to choose between, because **a space *is*
a region**: `reset` is a primitive of the collector, not the collector.  What §6.1 rejects —
and what would indeed be unsound — is `reset` *as the whole of reclamation*: rewinding a region
while a shared tail is still referenced hands a live cell to a new allocation.  What this slice
adds is the half that makes the rewind legal: the reachable cells are evacuated into the other
space first, so by the time a region rewinds nothing points into it.  Read that way, §6.1's
parenthesis ("fixed two-space pool, forwarding through the handle table") is a description of
§6.6's runtime plus ii-b-2, and §6.1's "not" is about a reset with no evacuation.  §6.1's
sentence now points here rather than standing alone.

**1. The boundary, and the roots.**  The only place a collection may run is where the machine
state is the *whole* live set: `step_c` has returned an `out`, and the driver has not yet
consumed it.  At that instant the roots are enumerable, because §6.2's by-value rules R4–R6
make the state structs fixed-size values that cross the boundary by value, and their
handle-typed fields are exactly the roots:
- `cfg = { cf: nat, cc: opt_cmd, ck: stack, cs: cstate }` → `cc.opt_val` (a `cmd` handle, when
  the tag is `JPL_SOME`), `ck` (a `frame_list` handle), `cs.cenv` (a `pair_text_text_list`
  handle).  `cf` is a `nat` and is not a root.
- `out = Onext of cfg | Oeffect of int * text list * stack * cstate | Odone of cstate | Olimit`
  → the `cfg` case is the roots above; `Oeffect` roots its `text_list`, `stack` and `cstate`
  directly; `Odone` roots its `cstate`; `Olimit` has no roots.
That list is *derived*, not transcribed: every entry is a field whose type resolves to a pool
under the rules the layout already implements, so a model change that adds a handle-typed field
adds a root in the same run, and one that adds a field the derivation cannot resolve is a
refusal rather than a silently unscanned pointer.  The root *set* is bounded by the struct
arity (at most 4 per boundary, and one `out` at a time), so the root sweep is a bounded unroll,
not a loop over a runtime-length list.

**2. The root invariant, and who checks it.**  Reachability from the state is necessary but not
sufficient: the boundary is legal only if **no lowered C local carries a handle across it**.  A
local that is still live on the driver side is an unrecorded root, and a collector that misses a
root corrupts data rather than failing loudly — the one failure mode in this plan that is not
detectable at runtime.  It cannot be read off the `.mli`, because it is a property of the
*lowered bodies*, not of the types.  So it is recorded as an obligation with two owners and
deliberately not claimed here: (i) 5-B.3a's schema rows already state, per binding, whether its
body keeps a value live past its own tail call, and the collector may only be placed at
boundaries the census shows to be local-free; (ii) JPL.6's lint gets the conservative
mechanical check — a handle-typed local must not be read after the call that establishes the
boundary.  Until (ii) exists this slice's C is correct *under an assumption*, and the assumption
is named rather than buried.

**3. The edge table: what a pool cell points at.**  R7 stores a pooled variant as
`{ jpl_nat tag; jpl_nat slot[arity_max]; }` — `jpl_cmd_node` is 16 B with 3 slots,
`jpl_frame_node` is 20 B with 4 — which erases the *meaning* of a slot: to the runtime, a handle
and a `nat` are the same word.  A collector therefore cannot exist yet, and no amount of
collector code fixes that; what is missing is a second reading of the declarations R7 already
read.  The table covers **every pool**, not only the two node types, because the collector's scan
step is "take a cell apart" for whichever pool the cell came from: a node row is
`(tag, slot)` and a cons-cell row is `(hd, next)`, one row per pool since a list cell has no tag.
And it is keyed by **WORD, not by declared field**, because R3 keeps a list's element *inline*:
`jpl_pair_text_text_list_cell` is 12 B — two `jpl_wref`s and a tail — so one field is three words
of three different meanings.  A per-field table would need a second table saying how a field
splits, and a second table is a second model of one artifact.  Flattening to words makes the cell's
own arithmetic the table's instead: `words_per_row × 4 == sizeof (cell)` is emitted per pool as
`jpl_check_<stem>_edge_covers_the_cell`, so the compiler — not a comment — says a row covers the
struct it describes.  For each word of each row, exactly one class:
- **SCALAR** — a `nat`/`bool`/`unit` payload (`cf`-like indices: `Ext`'s count, every `F*`
  frame's first slot).  A word cell is all-scalar for the same reason and not by exception: its
  struct is `{ jpl_nat wt_len; jpl_nat wt_code[MAX_WORD] }`, so both fields resolve through the
  walk a payload uses — the array's element count comes from the cell's own width, which is the
  one number no declaration states — and the answer is 257 values, a cell the collector copies in
  full and from which it follows nothing.
- **EDGE(pool stem)** — a handle into a declared pool.  A cons cell's `next` is always an `EDGE`
  into its own pool, and a stem is a target only because the registry declared the pool.
- **UNUSED** — beyond that constructor's arity.  The class is required, not optional: reading an
  unused slot as an edge would scan a word that was never written, and the arity of every
  constructor is in the `.mli` line the header already prints as a comment
  (`/* For of text, text_list, cmd_list */`).
Three derived consequences belong to this table rather than to the collector.  First, **a `text`
inside a pooled slot is a word-pool handle, not the inline leaf**: §6.2 calls `text` "the one
inline leaf", but a one-word slot cannot hold `jpl_text`'s 1028 bytes, so R7 committed to
`jpl_wref` there the moment it made slots one word wide — `Assign`, `For`, `Case` and
`FForRest` are the sites, and the collector must follow those edges like any other.  Second, the
only aggregates a pooled cell holds **by value** are a cons cell's element pairs, and the table
counts the sites rather than claiming them: `edge_aggregates_flattened` is the number of positions
whose type was inline-by-value and therefore expanded into more than one word, and this artifact's
answer is 2 — `pair_text_text`'s two `jpl_wref`s, `pair_text_list_cmd_list`'s two list handles —
which is what a node's slots can never be, since `node_layer` refuses a pooled constructor argument
wider than one word before this table is ever built.  Third, what has **no reading** is refused,
and the refusal is the design rather than a gap in it: a by-value aggregate whose words mean
something only *under a tag* — an `option`, a `bres`, a fat variant — has no per-word class, because
the table would have to carry the tag to say which of its words are live, and a collector that
forwarded a stale payload word would free a live cell.  If the model ever puts one inline in a
pooled cell, the emitter stops instead of inventing the conditional class; likewise a position that
resolves to neither a declared pool nor an openable declaration — a type variable, an abstract type
with no manifest, a function type — is an emitter refusal, because an unfollowable edge is a live
cell that gets freed.  A cell with a *wrong* class is worse than a missing one, so `origin` and
`next` handling in ii-b-2c may only read classes this table produced.

*Measured* (5-B.3b-ii-b-2a, over the same eight declared arrays and the same registry): **8**
tables, one per sized pool, **26** rows and **358** word classes, and the three of them are a
partition exactly — **286** SCALAR + **27** UNUSED + **45** EDGE = 358, with the report's partition
residual at **0**.  Per pool: `cmd` 11 rows × 4 words (12/12/20), `frame` 9 × 5 (17/15/13), the three
2-word cons cells (0/0/2 each), the two 3-word pair cons cells (0/0/3 each), and the word slab 1 ×
257 **all** scalar — derived through the same walk a payload uses, not excepted from it, so §6.2's
"inline leaf" is now a table entry: the collector copies that cell in full and follows nothing from
it.  An edge may name **8** pools and the header declares **8**: the target set and
the pool set are the same names in both directions, which is §6.6's "nothing demands a pool that
is not declared" re-cut against §6.7's table.  `edge_aggregates_flattened` is **2**, and it is a
*derived* two: the gate counts the pools whose cell is named `jpl_pair_*` and requires each of
those to be 3 words wide and every other non-node pool not to be, so the number follows from the
cell names the type layer chose rather than from a literal someone maintains.

**4. Two spaces, and the arithmetic the split forces.**  Each pool keeps **one array** and is
divided into two index intervals: a from-space and a to-space, each the size of the cap that
sized the doubling.  That reading is what §6.2's headroom 2 *always was*: "the live set **and**
the garbage produced between step boundaries" is one half per space, so decision 3's placeholder
acquires a mechanical meaning instead of being re-guessed.
Choosing the single array over two named arrays is a cross-rung constraint, not a style
preference: 2f's census reads the declared pool set out of the header by grepping for
`jpl_…_pool[`, and sixteen declarations would answer "16 pools" to a check that asserts eight —
the interval split keeps the header's *name* count honest rather than editing the census to
follow.
The split does, however, force one number to move, and it is worth stating exactly because it is
the kind of off-by-one §6.6 made a gate rung out of: **a region reserves index `0`, so two regions
reserve two indices.**  §6.6's rule "a pool of `C` cells serves `C-1`" applied to one region; with
two, each space of `C/2` indices serves `C/2 - 1`, and a capacity of `2 × cap` would therefore
hold only `cap - 1` live cells — silently one less than the cap the artifact declares, with the
shortfall appearing at runtime as a `BLimit` the model does not produce.  So this slice changes
the registered capacity from `2 · cap` to **`2 · cap + 2`** and the intervals from
`[1, C/2)` / `[C/2+1, C)` to `[1, cap+1)` / `[cap+2, 2·cap+2)`: every pool keeps exactly its
cap usable cells, each space keeps its own reserved `0`, and the index that belongs to neither
space is `0` and `cap+1`, both of which are `JPL_NIL` for their own region.
The honest price of the whole slice is then computable rather than guessed: `+2` cells per pool
(**16** cells = 2·(1028 + 12 + 16 + 8 + 8 + 12 + 20 + 8) = **2 224 B**, dominated by the two word
cells), the eight `origin` arrays at 4 B per index (**322 640 B** over the new 80 660 indices),
and **which interval is current**, which is one value rather than one per pool: every pool of the
graph moves together at a step boundary, so eight independent flags would be eight chances to
disagree about a fact that has one cause.  The emitted runtime therefore gains exactly one mutable
global, `jpl_pools_space`, and exactly one writer of it, `jpl_pools_swap()`; `jpl_<stem>_next` stays
a single pointer per pool but becomes an **absolute** index interpreted against the current
interval, `reset` rewinds it to that interval's own base instead of to `1u`, and `peak` becomes the
widest a *region* served — a count, no longer an index — because decision 4's quantity is cells, not
positions in one big array.  The **scan pointer is deliberately absent from this slice**: it is the
to-space's queue, so it belongs to the evacuation that advances it (ii-b-2c), and emitting a counter
nothing writes yet would be the invention §6.2 refuses.  What 2b does emit beside the intervals is
the `origin` array per pool, sized by the same index domain, zero-initialised — and zero is already
the right initial value, because `JPL_NIL` means "not copied from anywhere" — while stale origins in
the interval that becomes the to-space are never read, since evacuation writes an entry before the
scan reads it, which is §6.6's no-clearing argument repeated for a second array.  **That argument
reaches the scan's back-pointer read only: the other question an evacuation asks — has this
from-space cell *already* been copied — is a read before any write, and paragraph 5bis discharges
it with four comparisons rather than with this sentence.**  The static total moves from §6.6's
**34 866 192 B / 80 644 cells** to about
**35 191 056 B / 34 366.3 KiB / 80 660 cells** — an increase of **0.93 %**, not the doubling a
naive "two pools" reading of §6.1 would produce.  (The space indicator is one `jpl_ref` for the
whole runtime and the swap is one function for the whole runtime, precisely because neither is per
pool.)  These are predictions this section makes so the
gate can refute them: the numbers the slice lands are the report's, and a mismatch is a finding
about the arithmetic here, not a licence to edit the report.
Handles stay **absolute** across the split, which buys two things: the origin table is one array
per pool indexed by the same handle, and a stale handle is decidable by one comparison — after a
swap, a handle in the *other* interval is outside the current space entirely, so `is_live` rejects
it without a liveness analysis.  That is §6.6's recorded aliasing debt discharged: the danger was
a handle below the current `next` naming a cell that got reused, and with two intervals a reused
cell sits in a different interval from the handle that refers to it.

*Measured* (5-B.3b-ii-b-2b; §6.6's *Measured* paragraph carries the sweep's numbers, so this one
carries the arithmetic's): every one of paragraph 4's predictions held to the byte.  The registered
capacity became `2·cap + 2` = `SPACES·(cap+1)`, so the eight pools go from **80 644** indices to
**80 660** — exactly **+16**, the two reserved zeros per pool — and the pool storage from
**34 866 192 B** to **34 868 416 B**, i.e. **+2 224 B** = 2·(Σ of the eight cells' byte widths),
dominated by the slab's 2×1 028 — which is the 2·(the caps' sum) this paragraph computes rather
than the near-doubling a "two arrays" reading implies.  One space serves
**40 322** cells summed over the pools, and the identity the gate asserts for it closes:
`40 322 + 8 == 80 660 / 2` — the eight are the reserved bases, which is the off-by-one this
paragraph exists to make visible.  `interval_arithmetics_checked == allocators_emitted == 8`,
**49** interval macros (six per pool plus `JPL_POOL_SPACES`), **32** `jpl_check_*` typedefs — four
per pool, so the tiling, the per-space cap and the origin domain are each a compile-time relation in
the file that declares the array — and **1** `jpl_check_pools_flip_cycles_the_intervals` pinning
`SPACES` against the swap's own cycle length.  The `origin` domain is the index domain
(`origin_indices_total == runtime_cells_total == 80 660`), which is what makes it safe to size by
`JPL_POOL_<KIND>` rather than by a second, drifting expression; its **322 640 B** are the 4 B per
index this paragraph predicted, and the static total is **35 191 056 B / 34 366.3 KiB**, **+0.93 %**
over §6.6.  The indicator is **one** global with **one** writer, measured by counting assignments in
the file that defines it — 2, the definition and `jpl_pools_swap()` — not by a sentence here.  And
what 2b did *not* touch is also measured: the edge layer still reads 8 tables / 26 rows / 358
classes / 45 EDGE words, because a word's class is a property of its cell's type and not of the
array that holds it, and §6.7's whole argument for splitting the table from the space depends on
those two counts moving independently.  The two slices share one name only: `origin` was the array
ii-b-2c had to write, and nothing wrote it until 2c landed — `alloc` now clears the cell it hands out
and `evac` writes the pair of entries 5bis's fourth arm reads, which is the *Measured* paragraph
below, not this sentence.

**5. The algorithm: Cheney-style evacuation, because R4 forbids the recursive one.**  The
textbook stop-and-copy `evacuate` is recursive over the node graph, and R4 is a hard no.
Cheney's variant needs no recursion and no worklist, because **the to-space is the queue**:
per pool, an allocation pointer and a scan pointer; roots are evacuated into the to-space, then
each pool's scan pointer walks its own to-space, and scanning a cell copies *its* children into
their pools' to-spaces; the collection is complete when every pool's scan pointer has caught its
allocation pointer.  Each cell is copied at most once, so sharing is preserved — which is the
property §6.1 said a functional program needs — and the total work per boundary is linear in the
cells actually reachable, with two nested *bounded* loops (pools × slots), satisfying R3.  One
requirement this places on the cell layout: the scan must know, for a to-space cell, which
from-space cell it was copied from, so its children are read from the right place.  **This
sentence was written before the primitive existed, and half of it is the wrong half:** a to-space
cell's children are *already in the copy*, which is what the whole-cell copy means — the scan reads
them from the to-cell and they name from-space cells until the scan forwards them, so no origin is
needed to find them.  What the parallel array is genuinely needed for is the other direction, the
one `is_live` cannot answer: a from-space handle asking whether it has a copy this round, and the
mutual arm of paragraph 5bis's test that says so.  The nodes
have no spare word (`cmd` uses all 3 slots at `If`, `frame` all 4 at `FForRest`), so the origin
goes in a **parallel array**: `jpl_ref jpl_<s>_origin[…]`, 4 B per index, sized and intervalled
exactly as paragraph 4 sizes the pool it describes — and paragraph 5bis uses that one array for
both directions, because the interval an index sits in fixes which role its entry has.
(The rejected alternative, an explicit worklist, adds a queue entry per cell *and* needs the
same origin information, so it costs more for a shape R3 would then have to bound separately.)

**5bis. The evacuation of one cell, and the four comparisons that make an origin entry mean *this
round* (the ii-b-2c contract).**  Paragraph 5 states the algorithm; this paragraph states the
primitive it is built from, because four of its choices are not free.

*The boundary goes swap-then-rewind, and that order is what makes the allocator reusable.*  A
collector that copies "into the other interval" needs an allocator for the other interval, and §6.6
emitted exactly one allocator per pool, bound against `CUR_BASE`/`CUR_TOP`.  Rather than a second
family of to-space allocators — a second model of the same bound, which is the drift §6.6's derived
naming rule exists to prevent — the boundary flips the indicator *first*: `jpl_pools_swap()`, then
`jpl_<s>_reset()` for every pool, whose rewind now lands on the to interval and, per ii-b-2b's
measured transient, returns **0** because `next` still names the region being abandoned.  After
those two calls `CUR_*` *is* the to-space: `jpl_<s>_alloc` copies into it unchanged, `is_live`
judges the copies live and the abandoned originals dead, and `peak` — the placeholder paragraph 6
says decision 4 needs — becomes the number of cells a boundary evacuated rather than the width of a
region a test happened to fill.  The consequence is worth naming: the from region's frontier stops
being tracked at that instant, because there is one `next` per pool and the rewind gave it to the to
region.  Nothing in paragraph 5 needs it — the queue walks the to region, and a from-space cell is
read by absolute index, which is the one thing handles have always been.

*The copy is one C statement; the word accessors are where the table meets the struct.*  R7's cells
are structs whose members are all `jpl_nat`/`jpl_ref`, one `uint32_t` each, and ii-b-2a emitted
`jpl_check_<stem>_edge_covers_the_cell` pinning `NPOS * 4u == sizeof (cell)` — which is the
compile-time proof that no member is padded.  So the copy is the structure assignment
`jpl_<s>_pool[t] = jpl_<s>_pool[h]`: C99, no pointer, no cast, no strict-aliasing question, and the
tree stays as pointer-free as §6.2 left it.  Rewriting one *word* of that cell does need an
index-to-field mapping, and the only sound source for it is the same recorded positions that
produced the classes, so per pool the emitter derives
`jpl_ref jpl_<s>_word_at(jpl_ref h, jpl_ref i)` and `void jpl_<s>_word_put(jpl_ref h, jpl_ref i,
jpl_ref v)`
as straight-line `if`-chains over that pool's own `NPOS` words: dotted paths where R3 put an
aggregate inline (`pair_text_text_list`'s element is `…_hd.p_fst`, `…_hd.p_snd`, then `…_next`),
named slot fields for a node (`cmd_slot0…2`, `frame_slot0…3`), and one array arm for the slab
(`wt_code[i - 1u]`, its element being a single word).  **No arm is a bare `else`,** and that is a
soundness choice rather than a style one: a chain whose last arm caught everything would answer the
*last member's* value for an index that has no member, so every arm tests its own index and a read
past the cell's last word falls through to the initialiser `JPL_NIL` — the empty list, which already
means "no child" and is the least-wrong answer a collector can give for a word that does not exist.
Coverage is enforced where the arms are built, not where they are printed: the emitter refuses if a
cell's registered members do not reach its `NPOS` words, if an array member is not the cell's
*trailing* words (only a trailing one can be addressed by the scan's own index), if a member's word
count disagrees with the paths its by-value type expands to, or if a member wider than one word
carries no type to split it — so "the chain covers the cell" is arithmetic in the file that generated
it plus the typedef ii-b-2a already emits, not a comment.  The array arm's upper bound is
`i < JPL_<stem>_NPOS`, the macro the table is dimensioned by, so the chain and the table cannot
disagree about where the cell ends.  Two rejected alternatives: casting `&pool[h]` to `jpl_ref *`, whose legality rests on
6.7.2.1p15 plus the very no-padding typedef this file is checking (a circularity the project does
not need, and it would be the first pointer in the tree); and a union overlay, which re-declares the
pool arrays, so 2e's forty layout checks and 2f's declared-pool grep would describe an object that
no longer exists.

*Forwarding, and why four arms and not three.*  `evac(h)` must answer two references to one cell
with one copy (paragraph 5's sharing property), so it asks "has `h` been copied *this* round?" — a
read before any write.  An entry is a this-round forwarding pointer exactly when
`o = origin[h]` is non-nil, **and** `o > CUR_BASE`, **and** `o < jpl_<s>_next`, **and**
`origin[o] == h`.
The first two arms say `o` names an index of the current (to) interval.  The third says that
interval has *reached* `o`: `next` only moves up from `CUR_BASE + 1u`, and every index below it was
written by this round, so an entry pointing at or above the frontier is residue and gets overwritten
by this round's copy.  The fourth is the mutual arm: an index below the frontier is occupied by a
cell this round copied from some handle, and `origin` at that index names that handle, so
equal-to-`h` is exactly "this is `h`'s copy".  That third arm carries a debt it cannot pay by
itself, and the trace that shows it is two rounds deep.  In round 1 a from-cell `h` is copied to `t`
and both entries are written: `origin[h] = t`, `origin[t] = h`.  In round 2 the intervals have
traded roles, `evac` is called on `t`, and it reads `o = origin[t] = h` — an index of the *current*
interval.  While the frontier has not reached `h` the third arm rejects and `t` is copied correctly;
once it has passed `h` — and it must, because round 2's copies land in the indices the earlier rounds
filled — all four arms hold, because `origin[h]` still names `t` from round 1 and nothing rewrote it.
`evac` would then return `h`: a cell whose words name the *other* interval's children, in a region
being overwritten one cell at a time.  So the third arm is only true if the entries below the
frontier *mean this round*, and the emitter makes that true the cheapest available way:
`jpl_<s>_alloc` sets `origin[h] = JPL_NIL` for the cell it hands out, one store on the path that
already moves three counters.  With it, an index below `next` has an origin this round wrote — nil if
nothing has been copied into it, its source otherwise — and since a cell is evacuated at most once
per round its destination's entry is written once, which is exactly the fact the mutual arm reads.
Why three arms are not enough: the from region *is*
the previous round's to region, so every cell in it that was evacuated or merely reused carries an
entry pointing into the current to interval — a two-interval scheme has no round whose from region is
clean of forward-looking entries, and a membership-plus-nonzero test would hand a parent its child's
*old* index as if it were new, which is a live cell in the abandoned region that nothing rewrites.
The two rejected alternatives are a generation stamp (a third parallel array, 4 B per index more,
for a fact the intervals already carry) and clearing the from region's entries in a pass over the
region at each boundary (correct, and refused for §6.6's reason: a loop whose cost is paid even when
nothing is shared — and it would walk the interval the collector is about to abandon, which is the
wrong half anyway).  What was adopted is the same fact charged to the work actually done: the clear
sits inside `alloc`, so a boundary that copies three cells clears three entries and a boundary that
shares one cell clears none beyond its copy.  One array, two roles, disambiguated by the interval an
index sits in and by the frontier that made the entries below it: that is the third thing
paragraph 4's split buys, after `is_live` and the reserved-zero arithmetic.  One guard precedes all
of it: `h` must name a cell of the region the boundary reads *from* (`OTHER_BASE < h < OTHER_TOP`),
and a handle outside it is refused and counted rather than copied — which also settles the case 5bis
would otherwise have to wave through, a caller handing `evac` a cell that is already in the
to-space: it is not a from-region handle, so it is refused instead of producing a copy of a copy.
`evac(JPL_NIL)` is `JPL_NIL` and increments nothing — the empty list is not a cell.

*The scan step reads the table, never the model.*  `jpl_<s>_scan_one(void)` takes the cell at
`scan`, derives its row (`jpl_<s>_word_at(scan, 0u)` read as a tag where the pool is tagged, `0u`
where it is not), and walks that row's `NPOS` classes: SCALAR does nothing (the value came with the
copy), UNUSED does nothing (the word was never written), and an EDGE word is replaced by the copy of
the handle it holds — `word_put(scan, i, jpl_pools_evac_by_class(cls, word_at(scan, i)))`.  The
dispatch is **one** function for the whole runtime with exactly one arm per id in the registry's
target set (**8** today, and the emitted `jpl_check_dispatch_arms_cover_every_target` pins the last
arm's id against `JPL_EDGE_TO_…` so the chain cannot silently cover a prefix of the domain) and a
final `else` that increments one runtime counter and returns the handle unchanged.  That branch is
impossible by construction — table and chain come from the same `edge_pool_ids ()` reading in the
same run — and it is still emitted, counted and asserted zero, because the alternative to measuring
an impossible case is trusting a sentence about it; and returning the handle unchanged is the *least*
wrong action, since the word then names a cell in the abandoned interval, `is_live` rejects it, and
the failure surfaces as a dead handle instead of a cell that looks live.  A tagged pool's row index
is guarded the same way: a tag at or above `NROWS` increments `jpl_<s>_badtag` and the scan stops
without rewriting any word, because a row the table does not have has no classes to trust, and
walking slots as if they were scalar is precisely the hard-coded edge this section's rule forbids.

*The fixpoint, and why it terminates.*  `jpl_<s>_queue_start(void)` sets `scan` to `CUR_BASE + 1u` —
an empty queue, the same expression `reset` rewinds `next` to; `jpl_<s>_drain(void)` is
`while (jpl_<s>_scan < jpl_<s>_next) scan_one();`.  Each step advances `scan` by one and only the
allocator moves `next`, so the loop is bounded by the cells the to region holds and every cell is
scanned at most once: R3's bounded loop, no counter of its own.  R4 holds because the call graph is
one-directional — `drain → scan_one → evac_by_class → evac(t) → alloc(t)` — and no `evac` reaches a
`scan`.  A pool's drain is a fixpoint *over that pool*: scanning pool P can copy into pool Q and move
Q's `next` ahead of Q's `scan`, so the loop over all eight pools belongs to 2d's `jpl_collect()` and
is deliberately not emitted here.

*What the new counters mean.*  Per pool, `copied` counts fresh copies, `forwarded` counts evacuate
calls answered by an existing copy — the sharing hits, and the only quantity that distinguishes a
correct copy from one that copies everything — `badtag` counts a tag with no row, and `badref`
counts a handle outside the region the boundary is reading from.  The runtime gains one global,
`jpl_pools_unclassified`, for the impossible class.  Three refusal counters, three distinct bugs: a
table that lost a constructor, a root list that named a cell in the wrong interval, and a class id
the dispatch does not reach — collapsing them into one "collector errors" counter would report that
something is wrong while hiding which of the three it is.  §6.6's four counters keep counting
allocator *events*, so the copies a boundary makes are included: `taken` counts cells served, and
`peak` is now the widest region any pool reached, which after this slice is the live set plus
whatever the program allocated into it — the quantity decision 4 asked for, still measured rather
than derived.  Every new counter saturates at `JPL_REF_TOP` and none is ever rewound, exactly like
§6.6's.

**Predictions 2c makes so the gate can refute them.**  The index domain does not move, because the
second role of `origin` costs no storage: `runtime_cells_total` and `origin_indices_total` stay
**80 660**, and `static_bytes_total_with_origins` stays **35 191 056 B**.  What the slice adds is
mutable state only: **40** new globals — 8 scan pointers and 32 counters (four per pool: `copied`,
`forwarded`, `badtag`, `badref`), all `jpl_ref`-wide = **+160 B**, taking all mutable runtime storage
from 33 globals / 132 B to **74 / 296 B**.  *(Refuted in five places, and the refutation is §6.2's
own rule: `badtag` is a counter nothing would write in the six untagged pools, so it is emitted only
for the two node pools — **35** new globals and **68 / 272 B** total, not 40 and 74 / 296.  The
*Measured* paragraph records it as a prediction that failed rather than editing the prediction.)*  `interval_macros_emitted` goes **49 → 65** (two per
pool, `JPL_<KIND>_OTHER_BASE` and `JPL_<KIND>_OTHER_TOP` — *other*, not *to*, because after the swap
the to-space is what `CUR_*` already names, so the second pair exists to bound the region the
boundary reads *from*, and a body that wrote `SPACE + …` would be a second model of arithmetic those
macros own); `counters_emitted` goes **32 → 64** (**59** actually, for the same `badtag` reason); and
the new keys are `scan_pointers_emitted` **8**, `evac_functions_emitted` **8**,
`evac_forward_arms_checked` **8**, `queue_start_functions_emitted` **8**,
`scan_step_functions_emitted` **8**, `drain_functions_emitted` **8**, `word_accessors_emitted`
**16**, `tag_guards_emitted` **2** (the two node pools), `dispatch_functions_emitted` **1**,
`dispatch_arms_emitted` **8** — which must equal `edge_target_pools`, and is the cross-check that
says the chain covers the domain the table can name — plus `origin_clears_emitted` **8**, the one
store per allocator that the third arm of the forwarding test depends on: it is counted in the
generated file rather than trusted here, because a collector whose sharing test silently stops
believing the frontier is a corruption, not a wrong count.  What must *not* move is measured too:
`allocators_emitted` stays **8** (that is the swap-first boundary's whole point), every
EDGE SUMMARY key stays at 8 tables / 26 rows / 358 classes / 286 + 27 + 45 / 2 flattened / residual
0, 2f's declared-pool grep stays at **eight** pools, the four rendered bodies stay byte-identical,
and the runner stays at **17** rungs because 2c's check lives inside `verify/c/jpl_emit.sh`, which
goes from eight checks to nine.

*Measured* (5-B.3b-ii-b-2c; the storage predictions above, the drive that reads them, and the three
mutations that say the drive has teeth).  The domain did not move: `runtime_cells_total` and
`origin_indices_total` are **80 660**, `static_bytes_total_with_origins` **35 191 056 B**, and
`interval_macros_emitted` is **65** — 49 plus the two `OTHER_*` bounds per pool, exactly as
predicted, including the *other*-not-*to* naming.  The mutable state prediction was the one the
slice refuted: **35** new globals rather than 40, because §6.2's rule (no counter nothing writes)
is what the `tag_guards_emitted` key exists to record, so `badtag` is emitted for the two node pools
only.  The account closes on itself: `counters_emitted` **32 → 59** = 8 `copied` + 8 `forwarded` + 8
`badref` + **2** `badtag` + 1 `unclassified`, and `mutable_globals_emitted` **33 → 68** = those 59
plus the 8 scan pointers plus the space indicator, i.e. **272 B / 0.3 KiB** instead of the predicted
296 — a measured runtime still costing less than one cell of the word slab.  Every other new key
landed where it was predicted: `evac_functions_emitted` = `evac_forward_arms_checked` =
`queue_start_functions_emitted` = `scan_step_functions_emitted` = `drain_functions_emitted` =
`scan_pointers_emitted` = `origin_clears_emitted` = **8** each, `word_accessors_emitted` **16**,
`tag_guards_emitted` **2**, `dispatch_functions_emitted` **1**, `dispatch_arms_emitted` **8** — and
that last equality is with `edge_target_pools`, so the chain is checked against the domain the table
can name rather than against a number typed here.  What must not move did not: `allocators_emitted`
**8** (the swap-first boundary's whole point, and now a *measured* one — the drive's second round
calls `alloc` and the copies land on the current `next`), all EDGE SUMMARY keys at 8 tables / 26 rows
/ 358 classes / 286 + 27 + 45 / 2 flattened / residual 0, 2f's declared-pool grep at **eight**, the
four rendered bodies byte-identical, and the runner at **17** rungs because this check lives inside
`verify/c/jpl_emit.sh`, which is now nine checks with the vendored-evidence re-pin **deferred** to
after the ninth so that `JPL_REGEN=1` cannot pin evidence the drive has not approved.

**The tag guards are now read three independent ways.**  The header's `JPL_<KIND>_NROWS > 1` count
(derived by awk from the emitted `#define`s), the report's `tag_guards_emitted`, and the number of
`badtag` arms in the generated TU must all be **2**; a second reading of the first two already existed
as check 7's row/arity cross-check, and the third is new.  The same awk path derives the drive's
*shape*: for every pool it finds the word of the cell whose edge class names **that same pool**,
recording the column as `word = col % NPOS` and the row as `col / NPOS`, and refuses if a table's
`NPOS`/`NROWS` are missing.  Six pools have such a word — `pair_text_text_list` (word 2 of row 0),
**`cmd` (word 1 of row 3, the `Seq` constructor)**, `text_list` (1 of 0), `cmd_list` (1 of 0),
`pair_text_list_cmd_list_list` (2 of 0), `frame_list` (1 of 0) — and two do not (`word`, `frame`).
*That set is a correction, not a quotation*: this section first said `cmd` had no self edge, which was
read from the node pool's tag rows rather than from the table, and the derivation found
`Seq (cmd, cmd)` in row 3.  No capacity, index, word or row number is written in the shell script, so
a pool that gains or loses a self edge changes the probe's size without anyone editing a literal.  For
a tagged pool the derived row index is also the value written into word 0, so each of those chains
measures `scan_one`'s tag→row arithmetic on the way to measuring the copy.

**The drive, and what one chain of three cells proves.**  For each self-edge pool the generated probe
builds `a → b`, `c → b` in the low interval (every one of the cell's `NPOS` words nilled first, then
word `iw` set to the child's handle, then the self-edge word set to `b`), crosses the boundary in the
runtime's own order — `swap`, `reset`, `queue_start`, `evac` the roots, `drain` — and crosses it back.
Round 1 requires `copied` **+3**, `forwarded` **+1** (the second parent must hit the mutual arm: this
is the same quantity 2e's cross-pool probe is meant to distinguish, measured per pool where no root
list is needed), the copy of `b` at `HI_BASE + 3u`, both parents' self edges rewritten to it, the whole
cell structurally equal to its source word by word, `scan == next` at the fixpoint, `next == HI_BASE +
4u` and `peak == 3u`.  Round 2 is where 5bis's third arm is actually tested: `origin[a]` still names
last round's `ta`, so the probe asserts the stale entry is *present*, then calls `alloc` and asserts
the index it hands back has `origin == JPL_NIL` — "alloc handed out a cell whose origin still names
LAST round's copy", the failure message M1 prints — then asserts that `evac(ta)` **copies** rather
than forwards (`copied` **+4**, `forwarded` unmoved, destination ≠ the fresh `f`), and that the drain
fixes the copy's edge to the current interval.  Every chain answers `copies 5 forwarded 1 badref 3
taken 9 peak 3`, six times, with 0 assertion failures overall.  The `badref` three are the domain
guard: a handle in the *current* interval (a copy of a copy), `JPL_<KIND>_OTHER_BASE` (the reserved
zero of the region being read from), and `JPL_POOL_<KIND>` (one past the array) — **18** refusals in
total, each with `next` unmoved, and `evac(JPL_NIL)` incrementing nothing.  The two tagged pools each
get a second test in which words 1..`NPOS`-1 hold distinct non-nil values that *would* be evacuated:
a garbage tag (`NROWS + 5`) must stop the scan with `badtag` **+1** and leave **4** (`cmd`) and **5**
(`frame`) of those words exactly as written, the whole cell otherwise untouched — a tautology if the
words were zeros, which is why they are not.  `jpl_pools_unclassified` is asserted zero per chain, per
tag test, and once for the whole run.

**Three mutations, all run in a scratch mirror, none of them in the tree.**  Deleting `alloc`'s origin
clear (M1) moves one report key — `origin_clears_emitted` **8 → 0** — and produces **78** probe
failures, six chains' worth of the round-2 assertions plus the clear's own.  Weakening the mutual arm
to the frontier test it already passes (M2, `origin[o] == h` → `o < next`, arity-preserving so the C
compiles and no tautology warning fires) moves **no** `RUNTIME SUMMARY` key and produces the same
**78** failures, all of them the stale-forwarding case.  Rewiring one dispatch arm's class macro so
`text_list`'s edges evacuate through `frame` (M3) also moves **no** summary key — the arm count, the
table and the header all stay consistent — and produces **24** failures with `unclassified` reaching
**10**, which is the impossible branch turning out not to be impossible.  The strongest claim this
supports is the honest one: **two of the three bugs a collector can have here are invisible to every
count in the report**, and the drive is the only rung that sees them.  All three were reverted before
the evidence was re-pinned, and the classifier that rightly refuses to weaken a landed invariant in
`jpl_emit.ml` is the reason they were run on a copy.

**Honest limits after 2c.**  (i) With one `next` per pool, the `reset()` that follows a `swap()`
returns **0** — the guard `(next > CUR_BASE) && (next <= CUR_TOP)` fails because `next` still names
the interval being abandoned, which is 5bis's "the from region's frontier stops being tracked at that
instant" seen from the other side.  Cells are still freed; the quantity "cells returned by this reset"
is only meaningful when a reset does not cross a boundary, which is the case check 5 drives.  (ii)
`peak` in this tree is still **0** for every kernel-attributable run: the drive's `peak 3` is the
probe's, and the first caller that would move a pool's peak inside the C kernel is ii-b-2d's
`jpl_collect()`.  (iii) The chains are one-pool-deep-by-construction: the dispatch is crossed, since a
self edge is routed through `evac_by_class`, but a chain that visits three *different* pools is design
item (ii)'s cross-pool case and waits on ii-b-2e.  (iv) No root list, no `jpl_collect()`, no loop over
pools, and no `BLimit` — `evac` on a full to interval returns `JPL_NIL` and the refused copy is
counted, fatal only in 2d.

**6. Overflow is `BLimit`, not a guess.**  Decision 4 said no walk over the artifact's text can
produce the live-set bound, and this slice does not produce one.  What it changes is what happens
when the number is wrong: if the to-space of any pool fills mid-collection, the boundary returns
the model's own saturate-to-error edge (§4.2's `BLimit`, R4's `JPL_BRES_LIMIT`) instead of
corrupting or looping.  So headroom 2 goes from *assumed* to *checked*, and `_peak` — emitted and
instrumented by §6.6, still **0** because no body calls an allocator — becomes the measurement
that either retires the placeholder or proves it too small.  The honest consequence: a
`BLimit` the kernel does not produce would make the C diverge from the verified model, and no
rung in this tree can see that yet; it is JPL.7's differential that measures it, and it belongs
to that stage rather than being asserted here.

**7. What this slice must NOT reach for.**  No body becomes renderable by the collector alone —
§6.4's `OWED-REPRESENTATION` rows wait on the copy rule *and* on §6.3's schema for their
allocation sites, so the 13 rows unlock with ii-b-3/4, not here.  `release` stays absent: with a
collector, per-cell free is redundant, and shipping one would reintroduce the exact rule this
section derives.  No *per-boundary* clearing pass is emitted, for §6.6's reason, and 5bis keeps that
promise for `origin` too: the one store that exists is the allocator clearing the cell it hands out,
which is charged to a copy rather than to a region.  And no
reachability claim is made about the four rendered bodies: they allocate nothing, so they sit outside
this slice entirely, which the gate checks byte-for-byte.  **2c's own edge of this list** is the
boundary: it emits no root list, no `jpl_collect()`, and no loop over pools, because those are the
composition 2d owns and a primitive that also chose the composition would be two changes in one
slice.  It likewise does not decide what an overflow *means*: when the to interval is full, `evac`
returns `JPL_NIL`, the parent's word becomes `JPL_NIL`, and the `refused` counter §6.6 already
emitted is what records it — counted here, fatal only in 2d, where the boundary can answer with the
model's own `BLimit`.  Two honest limits follow from the same scope.  `evac`'s domain is
from-space handles: 2d's roots guarantee that, and calling it on a to-space handle would copy a
copy — wasteful, never corrupt, and not something 2c can be tested for without the roots that do not
exist yet.  And `copied`/`forwarded` are cumulative like `taken`, so they measure a boundary only by
its delta, which is how 2e's probe will read them.

**Slices.**  The work is ordered so that every rung's refusal is a *class* refusal before it is
a collector bug:

| slice | content | refuses | unlocks |
|---|---|---|---|
| ii-b-2a | **the derived edge table**, **landed** as `jpl_<stem>_edge[]` in `sh_run_jpl.h` + `sh_run_jpl_pools.c`: one class per **word** of every sized pool's cell — SCALAR / EDGE(stem) / UNUSED — computed from the positions the layout rules recorded while emitting the structs, published under `JPL_<stem>_NPOS/NROWS/NEDGE`, with `NPOS × 4 == sizeof (cell)` pinned by a `jpl_check_*` typedef per pool | a position whose type resolves to no declared pool; a by-value aggregate whose words mean something only *under a tag* (option, `bres`, fat variant) inline in a cell; a row wider than its cell; an array field whose element size does not divide the words its row leaves; an untagged row that does not fill its cell; a pool registered without a shape | the collector's data dependency; and it re-measures R7 and R3, since the header's slot comments, the flattened-aggregate count and the table must agree |
| ii-b-2b | **the two intervals**, **landed** as the arithmetic paragraph 4 predicts: per pool `JPL_<KIND>_CAP/_SPACE/_LO_BASE/_HI_BASE/_CUR_BASE/_CUR_TOP` (dimension `SPACES·(cap+1) = 2·cap+2`, each space reserving its own index 0), four `jpl_check_*` typedefs per pool pinning that the regions tile the array and that one region serves exactly the artifact's `cap`, one `jpl_<stem>_origin[]` over the whole index domain, `jpl_<stem>_next` read as an absolute index against the current interval, `is_live` re-expressed as "in the current interval and below the current allocation pointer", `reset` rewinding to `CUR_BASE + 1u` with `peak` a per-region count — and **the swap itself**: one `jpl_pools_space` global for the whole runtime with exactly one writer, `jpl_pools_swap()` | an index that belongs to neither interval or to both; intervals that do not tile the array; a per-space bound that does not serve exactly the artifact's `cap` (the off-by-one paragraph 4 names); a pool whose new total exceeds the counter's own top (a `jpl_check_*` typedef, not a runtime test); a second writer of the space indicator | ii-b-2c's evacuation, which needs a place to copy into and an origin to write; and it is the rung that proves §6.6's aliasing debt is a *comparison*, not an analysis, because a handle from the previous interval now reads dead **while sitting below the current `next`** — the case a `h < next` test cannot distinguish |
| ii-b-2c | **evacuate one cell**, **landed** as 5bis specifies it: the swap-then-rewind order, so §6.6's one allocator per pool *is* the to-space allocator (`allocators_emitted` still **8**) and `origin` finally has writers; the whole-cell structure assignment; `jpl_<s>_evac` with the four-arm forwarding test, its third arm made true by the **8** clears `alloc` does; `jpl_<s>_word_at`/`_word_put` chains with **no bare `else`** (**16** accessors, coverage enforced where the arms are built rather than in a comment); one `jpl_pools_evac_by_class` over the whole target-id domain (**8** arms == `edge_target_pools`, plus `unclassified` asserted zero); the to-space scan pointer with `queue_start`/`scan_one`/`drain` reaching a fixpoint *over one pool*; `copied`/`forwarded`/`badref` per pool and `badtag` for the **2** tagged ones — and, beside the counts, a **generated drive**: six self-edge chains, the edge word derived per pool by awk from the emitted tables, crossed over two boundaries | a slot class the dispatch does not name (an `else` that counts and leaves the word alone rather than guessing); a tag with no row (a scan that stops instead of walking slots as scalar); an origin entry that points into the to interval but above the frontier, or below it while naming a different origin (the stale-forwarding case three arms would accept); an allocator that hands a cell out without clearing its origin entry, which is what makes the third arm mean *this round*; a handle outside the region the boundary reads *from* (`badref`, which is also the answer to a copy of a copy); a pointer or a cast entering the tree — *and three of these six are now measured rather than asserted: two of the mutations that produce them move no report key at all, and only the drive sees them* | the multi-pool walk, and `peak` becoming the live-set quantity decision 4 asked for |
| ii-b-2d | **the roots and the boundary**: derived root list for `cfg`/`out`, `jpl_collect()` = evacuate roots + drain every pool's scan + swap intervals, saturating to `BLimit` on any to-space overflow | a root field that is not a declared pool edge; a `collect` that returns success with a pool's scan pointer behind its allocation pointer | the first reclamation that is legal rather than merely available |
| ii-b-2e | **the gate**: a generated probe that builds a known graph in one region, collects, and asserts survivors, sharing (two parents, one survivor), stale-handle rejection, and that an overflow path returns `BLimit` — plus the SUMMARY identities closing the table against the header | any count in the report that the header's `#define`s and the probe's assertions do not independently agree with | JPL.7's differential, which is where a wrong live-set bound becomes visible |

**Verification design (2g, once landed).**  Three claims need rungs beyond "it compiles".  (i) The
edge table is *derived*, so the gate must recompute it from the `.mli` text by an independent path
(the slot comments the emitter already prints) and require agreement — a table hand-written to
match the layout would pass a self-consistency check and still be wrong.  **This one landed with
ii-b-2a**, as `verify/c/jpl_emit.sh` check 7, and it reads four things that never see each other:
the header's constructor comments (its rows, and its widest arity as tag + slots); the `.mli`'s own
alternatives, with **parenthesis depth counted** so that `Case of text * (text list * cmd list)
list` answers two slots where a naive `*` count answers three; the initialiser tokens in the pools
TU; and the report's keys, which must equal all three.  Two structural properties a collector depends
on are asserted from the tokens rather than from prose: a node row's **first** word is SCALAR
because it is the tag, and an UNUSED word is **trailing** because a hole in the middle is exactly
what a "width minus the tail" reading would walk past.  (ii) `collect` must be
driven, not read: a probe that allocates a graph with *known* sharing and asserts the survivor
count is the only way to distinguish a correct copy from one that copies everything (both fit in
the space at these capacities, so no bound catches it).  **The single-pool half of (ii) belongs to
2c, not to 2e**: one cell per pool evacuated through the primitive, one chain of its own pool's
cells driven to its fixpoint, and one child referenced twice so `forwarded` must answer 1 while
`copied` answers 3 — which is the same distinction (ii) names, measured where no root list is
needed to make it.  **Landed with 2c**, and it answered as written: every one of the six self-edge
chains reports `copies 5 forwarded 1 taken 9` across *two* boundaries — round 1 copies three cells and
forwards once, round 2 copies two more (`evac` of the root copy, then the drain's fix-up of that copy's
edge) while `forwarded` stays at **1**, and the 9 allocations are the chain's own three cells, those
five copies, and the one `alloc` whose cleared origin is what makes round 2 copy instead of forward.
So the sharing hit and the fresh-copy count are separate quantities in the report and in the probe.  (iii) Staleness must be asserted
positively: a handle from the previous interval must read dead, and a cell of the *current*
interval below the current allocation pointer must read live, in the same run — the direction that a
single-number summary cannot lie about.  **(ii) waits on ii-b-2e's probe for its cross-pool case; the
per-pool case landed with ii-b-2c; (iii) landed with ii-b-2b**, because it is
the swap, not the copy, that makes the two directions differ: while one interval is the only region,
`h < next` and "in the current interval and below `next`" answer identically, so the rung with teeth
is the one that allocates below the pointer *and* across the base.  That is what check 5's sweep now
does per pool: it takes one handle in the low interval, swaps, and asserts *both* `low_h < next`
(counted in `stale_below`) and `is_live(low_h) == JPL_FALSE` (counted in `stale_dead`), then requires
the two counters to be **equal and non-zero** — a probe that never reached the interesting case would
otherwise pass it silently.  The same handle is re-asserted dead a second time in the high interval,
after that region's own `next` has grown past it, which is the rung a one-interval reading of
`is_live` cannot pass: reverting the comparison to §6.6's `h != JPL_NIL` changed no report key, no
table, and no other assertion, and produced **16** probe failures — two per pool — before exiting
non-zero.

**Next slice.**  ii-b-2d, the roots and the boundary.  ii-b-2a landed the table, ii-b-2b the space a
copy goes *into*, and **ii-b-2c the move itself**: a word's class read from the table, a SCALAR coming
with the whole-cell copy, an EDGE turned into a to-space handle through `origin`, and the scan pointer
that `queue_start` starts at `CUR_BASE + 1u` and `drain` advances to a fixpoint over one pool — so the
sentence this section used to close with, "45 EDGE words and two regions, with no C that reads one from
the other", is no longer true: 45 EDGE words now have a reader, and it is measured across two
boundaries.  What is still true is that **nothing calls it**: there is no root list for `cfg`/`out`, no
`jpl_collect()` that evacuates roots, drains all eight pools and swaps, and no `BLimit` on the overflow
path — those three are ii-b-2d, and until it lands no kernel step reclaims anything, so every
kernel-attributable `peak` in this tree is still the 0 the report prints.

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
| 5-B.2 · #39 | **Representation layer**: turn §6's rules R1–R8 into the C99 header the host will compile against — every reached type laid out, every size and every cap relation enforced by the *compiler* rather than asserted by a comment | `verify/c/jpl_emit.ml` + `verify/c/jpl_ast.ml` (shared reader), `verify/c/jpl_emit.sh` (runner: build + emit, `clang -std=c99 -Wall -Wextra -Wconversion -Wsign-conversion -pedantic -Werror -fsyntax-only`, differential cap fold against the OCaml runtime, byte-compare of the vendored evidence), vendored `verify/c/sh_run_jpl.h` (365 lines) + `verify/c/layout.txt` (109 lines) — **DONE (2026-10-04)**.  *Evidence*: **gate 13/13 → 15/15** — block **2e** runs all four checks over the bytes block 2c bound to a fresh Extraction, block **2e-negative** asserts the oracle roots are *refused for the layout reason* (`a function-typed value has no layout`, on `run`'s `run_phi` driver parameter), which is a different root-sensitivity verdict than 2d-negative's mutual-fixpoint refusal.  40 C types emitted; **34 compile-time assertions** cover them all — 27 aggregate rows each followed by its own `sizeof` check, 13 one-word typedefs (scalars, handles, the all-nullary variant) covered conjunctively by `jpl_check_one_word_families`, plus the 5 cap relations and the word-width check; 31 prototypes emitted, **5 PENDING** (the polymorphic bindings, with their caller counts, because R8 refuses to invent an instance), and 5 bounded static pools totalling **187.0 KiB**.  *What this layer measured and §6 now records*: five shipped functions need monomorphization (`length, app, rev, rev_append, forallb`, 2–6 call sites each); only `cmd` reaches itself, so §6's "recursive types" sentence needed halving; and **the word slab cannot be sized** — no cap bounds the number of live `text` values, so `jpl_word_pool[]` is declared without a dimension and the model owes a `MAX_WORDS` before 5-B.3 can link (see §6, §6.2, and decision 3).  *[Both halves of that last claim were superseded on 2026-10-05 by **5-B.2b**: `sh_jpl.v` §1 gained `MAX_WORDS` with §7.1/§5 behind it, §1.1 exported it as the table's tenth field, and `jpl_word_pool` is now dimensioned — the "cannot link" consequence is gone.  The measurement that produced the claim still stands and is the reason the fix was a model change: no LOCKED cap *is* a word count.]*  *Self-correction on the same day*: the report's first line claimed "40 C types emitted, each followed by a sizeof check", which the header disproved (27 of 40); the claim is now measured by the emitter itself and the family assertion closes the gap, so no emitted type's size is unverified |
| 5-B.2b · #40 | **`MAX_WORDS`: size the last undimensioned pool from the model, not the emitter.**  5-B.2 left `jpl_word_pool[]` declared without a dimension because no LOCKED cap *is* the number of live `text` cells, and this section's predecessor argument (a `MAX_CMD × MAX_LIST` product) was **per-node and wrong** — `cmd_fits` gates the whole tree, so a tree that fits has at most `2·MAX_CMD` word occurrences.  The stage therefore did not invent a number: it added the two counters the bound needs (`sh_jpl.v` §7.1 `cmd_words`, the honest word-occurrence count; §5 `benv_words`, name+value cells), proved `cmd_words ≤ 2·cmd_count` for the *same* fuel with the attainment exhibited (`Assign` costs 2 words for 1 node, so no tighter uniform factor exists), reflected it through `cmd_fits` into `cmd_fits_words`, placed the constant with `cap_words_order`/`MAX_WORDS_lt_fuel`, and exported it as `jpl_caps_table`'s tenth field so the emitter reads it from the artifact like the other nine | `verify/models/sh_jpl.v` §1 (`MAX_WORDS`, `cap_words_order`, `MAX_WORDS_lt_fuel`), §1.1 (`jpl_words` field, `jpl_caps_okb`, the order chain `jpl_stack ≤ jpl_words ≤ jpl_glob_fuel`), §5 (`benv_words`, `benv_words_le`), §7.1 (`cmd_words_list`/`_pair`/`_pairs`/`cmd_words`, `cmd_words_le_count`, `cmd_fits_unfold`, `cmd_fits_le`, `cmd_fits_words`, 2 attainment Examples); `verify/c/jpl_emit.ml` (`c_words`, the `jpl_words` cap row, `word_layer` sized `headroom × MAX_WORDS`, the two new C assertions `jpl_check_words_is_the_named_sum`/`jpl_check_words_order`, and a "could not size" section that now reports *nothing* undimensioned); `verify/c/jpl_emit.sh` (ten-field probe, guard `9`→`10`); `verify/models/verify_models.sh` block 2e's printed slab line — **DONE (2026-10-05)**.  *Evidence*: gate **15/15** (no new rung; block 2e's differential fold now agrees on **ten** capacities, `jpl_words 16642`, across the emitter's syntactic fold, the OCaml runtime evaluating `jpl_caps_table`, and the emitted `#define`s; block 2d still byte-compares `closure.txt`), `coqc sh_jpl.v` **8.6 s** with `coqchk -o -silent` four `<none>`, parity **66** unchanged, `conformance.sh` **33/33**, header **370 lines / 36 compile-time assertions** and it passes the JPL flag set, six pools dimensioned, bounded static total **33 601.0 KiB** of which the slab is **33 414.0 KiB** (33 284 cells × 1 028 B), report PENDING now **5** (R8's polymorphic bindings only).  *Measured side-effects, both recorded rather than assumed*: the artifact grew **87 → 89** bindings (`mAX_WORDS`, `benv_words`) while the *shipped closure* over roots `mrun_c,step_c` stayed **byte-identical** — the new constants are data outside the control-flow closure, so the lowering pass never sees `MAX_WORDS`, and only the folded numeral reaches C; and `MAX_WORDS`'s `Nat.add` spelling extracts as a call of the artifact's **recursive** `Nat.add` (`ExtrOcamlNatInt` hooks `+`/`*`/`-`/`div`/`modulo`/`divmod`/`max`/`eqb`/`leb` but *not* the qualified `Nat.add` form), i.e. the value 16 642 is produced by 8 192-deep non-tail recursion at module init — correct as measured, and a fact JPL.6's artifact-side census must not mistake for a reachable recursion.  *What this stage does NOT close*: the second `MAX_STACK` summand, whose condition "at most one live frame per source node" is named in §6 and still unwritten (if 5-B.3 refutes it, `MAX_WORDS` rises and the caps table + header re-pin together), and §6.2's headroom factor 2, still a placeholder until the allocation census.  *Proof-engineering finding, recorded because the two spellings prove the same fact and only one is buildable*: the first version of `cmd_fits_words` used `unfold cmd_fits in Hf` and made `sh_jpl.v` exceed **600 s**; isolating it measured the cost as **>45 s at fuel 128 as well as at 4096** (so it is not the numeral), while `rewrite cmd_fits_unfold in Hf` over the identical equation is **5.1 s** — comparing a *term* against its own delta short-circuits, comparing the two sides across an `eq bool … true` forces the fuel-bounded fixpoint to be reduced under all eleven `cmd` branches.  The file carries the four measurements at §7.1 |
| 5-B.2c | **Make §6.2's decision 1 mean what it says, and put the shared reading in one file.**  Two things this stage found while scoping 5-B.3, both of which would have become bugs in the lowering pass rather than bugs here: **(i)** the emitter declared `cmd`/`frame` *pooled* and then dimensioned only their **list** cells — `sh_run_jpl.h` had 6 `extern` pools and no `jpl_cmd_pool`/`jpl_frame_pool`, so a host linking the node encoding would have had nowhere to allocate a node.  **(ii)** the value-type view (`of_ct`), the constant folder and the cap-table reader lived inside `jpl_emit.ml`, and 5-B.3 needs exactly those three — a second copy in a third tool is the parallel-encoding failure §2 forbids, and two AST walks over one `.mli` is how a transpiler starts disagreeing with its own gate | `verify/c/jpl_emit.ml` (`pool_cap` now yields `(cells, cap macro, why)`; `node_layer` registers its own pool from that triple, so the struct and its allocation are emitted by one rule; `named_layer` refuses a name in `pooled_types` that `pool_cap` does not size, replacing a silent fall-through to `fat_layer`; the report's decision-1 section prints each pooled type's pool and cap macro instead of a hand-typed sentence); `verify/c/jpl_ast.ml` §8-§10 (the shared value-type view, constant folder and cap-table reader, moved out of the emitter — one reader, three consumers: `jpl_front.ml`, `jpl_emit.ml`, `jpl_lower.ml`); `verify/c/jpl_emit.ml` shrank 1074 → 879 lines — vendored `verify/c/sh_run_jpl.h` (376 lines, 76 `typedef`s, 63 `#define`s, **8** `extern` pools, 36 assertions) + `verify/c/layout.txt` (118 lines) re-pinned — **DONE (2026-10-05)**.  *Evidence*: gate **15/15** (block 2e's four checks unchanged in kind: emission, C99 compile of the widened header, the ten-capacity differential fold, byte-compare — and 2e-negative still refuses the oracle roots for the function-typed reason); bounded static total **34 049.0 KiB**, of which the slab **33 414.0 KiB** (98 %) and the two new node pools **448.0 KiB** (`jpl_cmd_pool` 8 192 cells × 16 B, `jpl_frame_pool` 16 384 × 20 B).  *The refactor's own check*: moving §1-§3 of the emitter into the shared reader was verified by re-running the emitter and requiring the vendored bytes to be **identical**, so "same reading" is measured, not claimed.  *Why the node sizes are what they are*: a `jpl_cmd_node` is tag + 4 slots (max ctor arity) = 16 B, a `jpl_frame_node` tag + 4 = 20 B with padding to 20, each followed by its own `jpl_check_*_is_<N>` typedef, so both are compiler-checked.  *What this stage does NOT close*: the headroom 2 on these two pools is the same placeholder decision 3 carries for the other six — the node pools get their per-step allocation census from 5-B.3a, and if it refutes 2 the factor changes for all eight at once |
| 5-B.3a · #41 | **The lowering census: measure the shape before writing any of it.**  *This stage* emits no C — it measures, deciding the four things the emitter cannot invent later — one lowering schema per shipped binding (self-call count, tail/non-tail split, the source of its first fuel), R8's instance set resolved at the call sites, where each of the 68 lambda values sits, and which pools the closure demands — plus the obligations the artifact's text cannot answer: extent vs site count, the non-tail folds, and that nothing shipped bounds stack depth | `verify/c/jpl_lower.ml` (the third of the shared `jpl_ast.ml` reader's three consumers), `verify/c/jpl_lower.sh`, vendored `verify/c/lowering.txt` — **DONE (2026-10-05)**.  *Evidence*: gate **15/15 → 17/17** — block **2f** plus **2f-negative**, which refuses the oracle roots as a **mutual fixpoint**, the third independent refusal reason over one artifact.  **47 members = 26 straight-line + 7 fuel tail loops + 4 one-trip fuel idioms + 3 structural tail loops + 5 `BOUNDED FOLD` + 2 aliases**, a split that **retired this table's own inherited estimate** ("6 + 2 + 9" in the 5-B.1 and 5-A.7 rows): there are 7 fuel loops because `nat_digits` is one, and 5 of the 8 recursions that remained have no `while` at any budget.  R8 measured, not assumed: 5 polymorphic bindings, 29 uses, **6 closed + 6 open** instances.  The runner takes every assertion from the report's **SUMMARY** keys and treats a missing key as a failure, because an absent measurement is not a zero.  *Two bugs the measurement caught in itself*: the instance walk first pushed the `.mli`'s **unfreshened** `'a1` into the shared store, so all five polymorphic bindings read one entry and the "instance set" measured whichever binding inference touched last; and recorded lambda sites stored instance names as **strings**, so one report printed two names for one variable.  See §6.2 decision 4, §6.3, and the HISTORY entry |
| 5-B.3b-i · #41 | **The ABI: R8's closed set rendered as C declarations, and nothing more** — the half of 5-B.3b whose input the census had already measured completely.  Declarations only, because §6.3's `BOUNDED FOLD` row is not landed: its obligation now appears as a comment *in the emitted file* rather than as prose in the plan | `verify/c/jpl_lower.ml` §8b (`print_abi`/`write_abi` + 6 new SUMMARY keys), `verify/c/jpl_ast.ml` (`value_name`, `has_fun`), `verify/c/jpl_emit.ml` (its hard-coded `"jpl_wref"` replaced by that shared rule), `verify/c/jpl_lower.sh` checks 4–6, vendored `verify/c/sh_run_jpl_abi.h` (50 lines) — **DONE (2026-10-05)**.  *Evidence*: gate stays **17/17** with no new rung (2f gained the ABI accounting, the ABI compile, and the negative run's artifact-immutability assertion); `lowering.txt` **418 → 507 lines**, SUMMARY **18 → 24 keys**; `closure.txt`, `layout.txt` and `sh_run_jpl.h` **byte-unchanged**, so the ABI consumes the layout without editing it.  **5 prototypes + 1 refusal**, bodies **2 expressible / 3 owed**, `abi_blocked_outside_fold_set = 0`, and the header pair compiles under 2e's own flag set.  *Why the compile rung is not redundant with the accounting*: a scratch build in which `value_name` returned a name the layout header never typedef'd left **every** count identical and failed only at the compiler.  *Side finding*: `pr_lt` flattened arrow types, so the refused instance printed as `text -> bool -> text list -> bool` — a three-argument first-order function, i.e. the exact distinction the refusal under it makes; the printer now parenthesises a left-nested arrow the way OCaml's does.  *What it does NOT close*: 0 bodies (5-B.3b-ii), and `forallb`'s un-nameable instance — its only shipped use is an **inline lambda** inside `branch_guardb`, a binding the schema census calls straight-line, so 5-B.3b-ii owes that guard a model-side specialisation §6.3's fold row does not list |
| 5-B.3b-ii-a · #42 | **The first C bodies, and the census that decides which bodies may be written at all.**  5-B.3b-i answered "what does this function's *interface* cost in C"; the bodies need a second, independent question (§6.4): does this body need a **pool, an allocator, or a function value**?  The stage's load-bearing choice is that the answer is **not a classification rule written next to the emitter** — §6.4's licensed scalar set is implemented once, as a renderer, and *run as a trial* over all 47 members, so a verdict is one of the renderer's own runs in its own words and the census cannot claim a body renderable that the emitter then could not write.  A body the trial accepts becomes a definition in `sh_run_jpl_bodies.c`; a refusal becomes a row naming the construct, the pooled type, or the §6.3 schema that stopped it, and the six verdicts are asserted to **partition** the closure rather than describe part of it | `verify/c/jpl_lower.ml` §8c–§8d (`base_verdict`, `pools_of`, `render_e`/`render_def`, `print_render` as a fixpoint, `write_bodies`, `write_diff_c`/`write_diff_ml` + 11 new SUMMARY keys), `verify/c/jpl_ast.ml` §9 (`c_fn`, `c_upper`, `data_macro`, `cap_data`, `cap_macro_of_data`, `is_cap_data` — the C *spelling* rules lifted out of the emitter so 2e's `#define`s, the census's prototypes and the renderer's citations are one rule), `verify/c/jpl_emit.ml` (its hand-typed seven-name `cap_bindings` list replaced by `cap_macro_of_data`, i.e. by the artifact's own cap table), `verify/c/jpl_lower.sh` checks 5–8, vendored `verify/c/sh_run_jpl_bodies.c` (49 lines) + `verify/c/jpl_bodies_diff.c` (20) + `verify/c/jpl_bodies_diff.ml` (14) — **DONE (2026-10-05)**.  *Evidence*: gate stays **17/17** — no new `verify_models.sh` rung was needed, because 2f's own script grew from six checks to eight.  `lowering.txt` **507 → 659 lines**, SUMMARY **24 → 35 keys**; `jpl_lower.ml` 2043 → 2667, `jpl_lower.sh` 330 → 558.  **The measured partition: 11 `DATA` + 2 `ALIAS` + 4 `RENDER` + 13 `OWED-REPRESENTATION` + 15 `OWED-SCHEMA` + 2 `OWED-CONSTRUCT` = 47, `render_unaccounted = 0`.**  The four rendered bodies are `bstat`, `is_digit`, `is_alpha`, `is_name`, two of them citing a data constant by its header macro (`JPL_C_B_0`, `JPL_C_B_USCORE`), and every one of the 11 `DATA` names resolves as a `#define` in `sh_run_jpl.h` — the cross-rung direction that keeps a missing constant from first appearing in JPL.7's host.  *The trial is a fixpoint, and one body proves why*: `is_name` cites a `DATA` macro **and** calls `is_alpha`/`is_digit`, so it is undecided until its callees are verdicted — a callee still waiting leaves the caller undecided rather than refused.  *The differential*: both drivers are **generated from the same RENDER rows** that wrote the bodies file, so no hand adds a call to one side; each is built (the C under 2e's flags minus `-fsyntax-only`, the OCaml against the vendored extraction) and run over `0 … MAX_FUEL` — **136 450 lines each, `cmp` identical**, `bodies_swept_exhaustive = 4 / diagonal = 0` because every rendered body takes exactly one `nat`, and the transcript's swept fields take **5** distinct values, which is the rung's guard against a pair of constant transcripts agreeing for free.  Line counts are checked against the report's own `sweep_domain`, so neither driver picks the range it tests.  *Why the compile rung and the differential are not redundant*: a renderer can emit C that compiles and computes something else; only the sweep says which.  *The refactor's own check, to 5-B.2c's standard*: the naming rules moved into the shared reader and the emitter's cap list became derived from the artifact, and 2d and 2e were re-run requiring `closure.txt`, `layout.txt` and `sh_run_jpl.h` to stay **byte-identical** — they do, so "one reading, three consumers" is measured rather than claimed.  *Side finding, with an owner*: `ALIAS` rows `jpl_add`/`jpl_mul` have a prototype in 2e's header and no definition anywhere, because their body IS a C operator — either 2e drops those prototypes or JPL.6's lint forbids calling them by name; the census prints it as a finding, not a failure.  *What it does NOT close*: 43 members still have no body (15 on §6.3's loop schema = 5-B.3b-ii-b, 13 on decision 3's step-boundary copying and `MAX_STACK`'s depth guard, 2 on a named construct), nothing here touches headroom 2 because a scalar body allocates nothing, and `branch_guardb`/`forallb`'s model-side specialisation stays owed from 5-B.3b-i.  See §6.4 and the HISTORY entry |
| 5-B.3b-ii-b-0 · #41 | **The second debt: every owed row is now read twice.**  §6.4's rules stop at the first match, so an `OWED-SCHEMA` row never printed the pools its signature takes or returns — and 5-B.3b-ii's slice order turns on exactly that overlap, because a `while` whose operands are pool handles is not writable until the pool half exists.  The stage is a **measurement with no licence attached**: the same `pool_of` reading the renderability trial consults, asked of all 47 members and printed as two debt columns beside the one verdict, changing no verdict and emitting no C.  "No pool" must carry a **reason** — scalar / type-variable / behind-a-declared-type's-fields — because a zero without a reason is precisely the licence §6.5 refuses; and the type-variable family is cross-checked against §6.3's **closed instances**, since `sh_run_jpl_abi.h` may already have decided the cell this walk cannot see | `verify/c/jpl_lower.ml` §9e (`sight`, `sight_of`, `opaque_ty`, `shape_debt`, `instance_pools`, `print_debts` + 9 new SUMMARY keys), `verify/c/jpl_lower.sh` check 5 (five identities, one inequality, the slice finding), `verify/models/JPL.md` §6.5 — **DONE (2026-10-05)**.  *Evidence*: gate stays **17/17** and `jpl_lower.sh` stays at eight checks; `lowering.txt` **659 → 783 lines**, SUMMARY **35 → 44 keys**, and **not one verdict count moved** (11 + 2 + 4 + 13 + 15 + 2 = 47), which is the check that this section measured instead of re-classifying.  **Measured: 10 of the 15 §6.3-shape rows also carry the representation debt; all 5 remaining rows are pool-free only because a position is still a type variable; 0 are pool-free in the plain scalar sense; and 4 of those 5 are POOLED at a closed instance** (`length`, `rev`, `rev_append`, `forallb` — only `app` is never closed in the shipped closure).  `owed_construct_also_pool = 0` (the §6.4 rule order *holding*, not an accident), `dual_debt_rows = 10`, refused-rows-touching-a-pool = **23** = 10 + 0 + 13 (asserted), `debt_unaccounted = 0`.  **The consequence belongs to the plan, not the tool: a loop form landed alone would render zero bodies**, so ii-b-1/ii-b-2 (allocator, handles, step-boundary copying) come before ii-b-3/ii-b-4 (the loop forms) — which is what §6.5's slice table now states as measured rather than as preference.  *Honest limit*: the walk stops at a declared record or variant, so every pool-free count is a **FLOOR** — `isz` sits behind `cstate` and `step_c` behind `cfg`/`out`, and the same boundary is why 2e's `jpl_frame_pool` is declared while nothing demands it.  Entering record fields would move rows between §6.4's verdicts, so it is a slice of its own.  See §6.5 and the HISTORY entry |
| 5-B.3b-ii-b-1 · #41 | **The pool runtime: how a cell comes to exist.**  Up to here the header declared eight `extern` arrays and a comment promised "definitions live in the emitted translation unit" — a translation unit that did not exist, so a handle in `sh_run_jpl.h` named nothing.  The stage's load-bearing choice is **reclamation at region granularity, not a free list**: a per-cell `release(h)` is only safe once a rule says which handles still reach a cell, and that rule is ii-b-2's, so freeing per cell here would be the same kind of invention §6.2 refuses.  A region boundary *is* decision 3's step boundary, which makes the design honest about what it cannot do yet — and it makes the quantity decision 4 said no text walk could produce **measurable** rather than assumed: `_peak` records the widest point any one region reached.  Every name is derived from the registry that sizes the pool (stem → `JPL_POOL_<KIND>` → `_next/_peak/_taken/_refused` + `_alloc/_reset/_is_live`), so a pool cannot gain a capacity without an allocator or an allocator without a return type the layout defined | `verify/c/jpl_emit.ml` (`pool.p_handle` as the registry's missing column, `pool_stem`/`pool_macro`/`sized_pools`/`runtime_names`, `runtime_decl`/`runtime_section`, `pool_definition`/`pools_c_text`, 13 new SUMMARY keys + three refusals that exit 1), `verify/c/jpl_emit.sh` checks 3, 5 and 6 (compile the TU, sweep it at its bound, close its accounting), vendored `verify/c/sh_run_jpl_pools.c` (363 lines, new) — **DONE (2026-10-05)**.  *Evidence*: gate stays **17/17** — no new `verify_models.sh` rung, because 2e's script grew from four checks to seven.  `sh_run_jpl.h` **376 → 477** lines; the emitted pools TU compiles under `-std=c99 -Wconversion -Wsign-conversion -Werror` **without** `-fsyntax-only`, which is the first time a definition of a mutable static in this tree has been through a compiler at all.  **Measured: 8 pools sized ⇒ 8 allocators, 8 resets, 8 liveness checks, 32 counters, 80 644 cells, 34 866 192 bytes of static storage, 0 unsized pools, 0 name collisions with the closure's 47 symbols.**  The bounds sweep — generated from the header's own `_alloc(void);` lines, so it carries no capacity number either — reports for every pool `served == C-1`, `refused == 4`, `peak == C-1`, `0` assertion failures, and `jpl_pools_refusals() == 32` equal to the per-pool sum; `2f`'s census still reads **eight** declared pools from the same grep, and all five of its artifacts stayed byte-identical.  *The rung has teeth*: mutating one emitted comparison (`next < C` → `next <= C`) produced five distinct failures on the word pool and exited non-zero, and the mutation was reverted before the evidence was re-pinned.  *Design debt recorded rather than hidden*: a `reset` does **not** clear cells (clearing at every boundary would price the step by the pool, not the data, and no lemma requires zero bytes), `is_live` catches only a handle carried across a rewind — the aliasing a handle below the current `next` can still produce is exactly what ii-b-2's copy rule must forbid — and **every `peak` attributable to the kernel is still 0**, because no body calls an allocator yet.  *What it does NOT close*: no body rendered (§6.4's four stand alone and unchanged), no extent measured for a real run, headroom 2 untested, and the 13 `OWED-REPRESENTATION` rows stay owed because a cell existing is not a body being allowed to return one.  See §6.6 and the HISTORY entry |
| 5-B.3b-ii-b-2a · #41 | **The edge table: which word of a cell is an edge.**  §6.6 made a cell exist and R7 made every one of its slots the same `uint32_t`, so "reachable from the roots" was a phrase with no referent: a handle and a `nat` are one word, and only the `.mli` knows which is which.  The stage's load-bearing choice is **one class per WORD, not per declared field**, because R3 keeps a list's element inline — `jpl_pair_text_text_list_cell` is 12 B of three words with three different meanings, so a per-field table would need a *second* table saying how a field splits, which is §2's forbidden second model of one artifact.  Flattening instead makes the cell's own arithmetic the table's: `NPOS × 4 == sizeof (cell)` is emitted per pool as a `jpl_check_*` typedef, so the compiler says a row covers the struct it describes.  A position that resolves to no declared pool, a row wider than its cell, **an array field whose element does not divide the words its row leaves** (the word slab's codes: the count comes from the cell's width, so if it does not divide, this reading did not walk the whole cell), **an untagged row that does not fill its cell**, a pool registered without a shape, and **a by-value aggregate whose words mean something only under a tag** (option, `bres`, fat variant) are emitter refusals, not classes: a collector that forwarded a stale payload word — or that never scanned a word at all — frees a live cell, so guessing is worse than stopping | `verify/c/jpl_emit.ml` (§6c: `edge_class`/`edge_pool_ids`/`edge_class_macro`/`edge_target`/`edge_cell_words`/`edge_expand`/`edge_classes_of`/`edge_row`/`edge_tables`/`edge_decl`/`edge_definition`/`edge_section`, the `edge_defs_b` buffer, `runtime_names` extended so a table cannot shadow a closure symbol, 10 `EDGE SUMMARY` keys + six edge-layer refusal sites that exit 1), `verify/c/jpl_emit.sh` **check 7** (three awk readings — `edges_from_tags.awk`, `edges_from_table.awk`, `ctors_from_mli.awk` — the per-stem loop and the key identities; 784 lines, checks seven → eight), vendored `verify/c/sh_run_jpl.h` **477 → 557** lines and `sh_run_jpl_pools.c` **363 → 487**, `layout.txt` 185 with 31 of them the edge blocks — **DONE (2026-10-05)**.  *Evidence*: gate **17/17**, exit 0, with no new `verify_models.sh` rung; the header and the pools TU still compile under D7's full flag set, and 2f's census still reads **eight** declared pools from its own `jpl_…_pool[` grep with all five of its artifacts byte-identical.  **Measured: 8 tables / 26 rows / 358 word classes = 286 SCALAR + 27 UNUSED + 45 EDGE, partition residual 0; `cmd` 11×4 = 12/12/20, `frame` 9×5 = 17/15/13, three cons cells at 0/0/2, two pair cons cells at 0/0/3, the word slab 1×257 all-scalar, now derived rather than excepted (`P_leaf L_nat`: the cell's 257 words less its length word, in groups of the element's one word, so the row is the struct's own array and its scan copies the cell in full and follows nothing); 8 edge targets == 8 declared pools, both directions; `edge_aggregates_flattened = 2`.**  *The flattened count is derived, not quoted*: the gate counts the pools whose cell is named `jpl_pair_*`, requires each of those to be 3 words wide and every other non-node pool not to be, so the number follows from the type layer's own cell names instead of from a literal someone maintains.  *The rung has teeth, twice, by two different readings*: retagging a node row's first word as an edge (`P_tag → [E_edge "cmd"]`) left checks 1–6 green and the C still compiling — the table was well-formed, in the cell's width, and self-consistent with the report — while check 7 produced **20** `TAGWORD` failures and exit 1; reclassifying padding as SCALAR (`E_unused → E_scalar`) moved every report key together with the file, kept the partition closed, and was caught because the `.mli`'s arities predict `cmd` 12 and `frame` 15 UNUSED words against a measured 0.  Both mutations were reverted before the evidence was re-pinned.  *What it does NOT close*: this is a data dependency, not a collector — no `origin` array, no two intervals, the registered capacities are still §6.6's `2·cap` (all three of those closed by **ii-b-2b**, the next row), nothing reads a table yet, and no reachability claim is made about any body.  The emitter's six edge-layer refusals have **no rung that fires them** at these roots (a `.mli` that put an `option` inline in a pooled cell would), so the refusal code is read, not measured; of the two collector-side rungs §6.7's verification design calls, (iii) landed with ii-b-2b and (ii) waits on ii-b-2e's probe.  See §6.7 and the HISTORY entry |
| 5-B.3b-ii-b-2b · #41 | **The two intervals: a place to copy into, and the comparison that makes staleness decidable.**  After 2a the runtime could say *which words of a cell are edges* but not *where a copy would go*: §6.6's array was one region with a reserved index 0, so a collector had no to-space, no origin to forward through, and — the part that turns out to be load-bearing — `is_live` had no test that a one-region reading could not fake.  The stage's load-bearing choices are three.  **One array, two intervals**: the dimension becomes `SPACES·(cap+1)` = `2·cap+2`, each space reserving its own index 0, because §6.6's "a pool of `C` indices serves `C-1`" is a *per-region* law and a capacity of `2·cap` would therefore have served `cap-1` live cells — one less than the artifact's cap, surfacing at runtime as a `BLimit` the model does not produce.  **One indicator for the whole graph**: `jpl_pools_space` is a single global with a single writer `jpl_pools_swap()`, not eight per-pool flags, because every pool moves together at a step boundary and eight independent flags are eight chances to disagree about a fact with one cause.  **Handles stay absolute**, which is what buys the origin table its domain and staleness its one comparison. The scan pointer is deliberately *not* emitted here — it is the to-space's queue, so it belongs to the evacuation that advances it | `verify/c/jpl_emit.ml` (the interval arithmetic as derived macros `JPL_<KIND>_CAP/_SPACE/_LO_BASE/_HI_BASE/_CUR_BASE/_CUR_TOP`, four `jpl_check_*` typedefs per pool, `origin[]` per pool over the index domain, `next` as an absolute index read against `CUR_BASE/CUR_TOP`, `is_live` as the three-bound test, `reset` rewinding to the current base with a two-sided guard, `peak` as a per-region count, `jpl_pools_space` + `jpl_pools_swap` + its flip-cycle typedef, the `INTERVAL REFUSED` sites, 12 new `RUNTIME SUMMARY` keys), `verify/c/jpl_emit.sh` (**check 5**'s sweep rewritten to four phases over **both** intervals — 6 interval macros per pool now re-derived from the header, the `stale_below == stale_dead` pair, the `returned == 0`/`next == HI_BASE+1` transient rungs and the `sizeof(origin)` domain rung, and two probe-wide rungs — `sizeof (jpl_ref) == 4`, and the indicator back at `0u` after **all eight** sweeps, which is what makes one global a claim about the whole runtime rather than about each pool; **check 6**'s interval identities including the one-writer count taken from the file that defines the global, so its `RUNTIME SUMMARY` key set goes **13 → 25**); vendored `sh_run_jpl.h` **557 → 805**, `sh_run_jpl_pools.c` **487 → 769**, `layout.txt` → 217 — **DONE (2026-10-06)**.  *Evidence*: gate **17/17**, exit 0, with **no new `verify_models.sh` rung** (2e's script stayed at eight checks).  **Measured: 80 660 indices (+16 — two reserved bases per pool), pool storage 34 868 416 B (+2 224 = 2·Σ cell widths), 8 origins of the same 80 660 indices = 322 640 B, static total 35 191 056 B = 34 366.3 KiB = +0.93 % over §6.6 — paragraph 4's predictions, to the byte; 40 322 cells served by ONE space, with `40 322 + 8 == 80 660 / 2` the off-by-one made visible; 49 interval macros, 32 per-pool typedefs + 1 flip typedef, `space_globals_emitted == swap_functions_emitted == 1`, and the indicator's assignments counted in the TU at 2 = definition + writer.**  The sweep drives every pool through both regions: `served == cap` per interval, `next == CUR_TOP` at each bound, `refused == 6`, `peak == cap` in **both** intervals (a per-region count — the high-water index would have read ≈`2·cap`), a swap that returns `(before+1) % SPACES`, an un-rewound region that **refuses** rather than serving its own reserved nil, and a `reset` of an abandoned interval that returns **0** instead of wrapping.  0 assertion failures across all eight, `jpl_pools_space == 0u` after every sweep and after all eight.  *The rung has teeth, and each mutation was reverted before the next*: reading `is_live` as §6.6 did (`h > CUR_BASE` → `h > 0u`, the same test since `JPL_NIL` is 0) left **every report key identical** and produced **16** probe failures — the stale-below-`next` assertion in both intervals of all eight pools — and exited non-zero; `SPACES × cap` made two of the emitted typedefs refuse the header at compile time; a stale `2·cap` literal at one registration site fired the emitter's own `INTERVAL REFUSED` before any file was written; and a second assignment to the indicator (the TU's assignment count measured going **2 → 3** against the rung's `1 + space_globals_emitted`), and a dropped `JPL_<KIND>_LO_BASE`, each moved exactly the count meant to notice.  Because some of those mutations edit the shipped emitter, they ran in a **scratch mirror** of `verify/c/`, which reproduced a green control run first — the classifier that guards `jpl_emit.ml` is right to refuse a weakening of a landed invariant.  *What it does NOT close*: still no collector — `origin` is written by nothing, the scan pointer does not exist yet (§6.7 design item (ii)'s driven probe is ii-b-2e's), no kernel body calls an allocator so every *kernel-attributable* `peak` is still 0, and the four rendered bodies are untouched (byte-checked).  *(The first two clauses are what **ii-b-2c**, the next row, closed: `alloc` now clears the cell it hands out and `evac` writes the pair of `origin` entries the forwarding test reads, and the scan pointer exists and is advanced by `queue_start`/`scan_one`/`drain`.  The third and fourth are still exactly as this row states them — no kernel body calls an allocator, and the driven cross-pool probe is still ii-b-2e's.)*  See §6.7 and the HISTORY entry |
| 5-B.3b-ii-b-2c · #41 | **The evacuation of one cell, the scan that walks what was copied, and the two collector bugs no report key can see.**  After 2b the runtime had a to-space, an `origin`, and a staleness test, but nothing that moved a cell into them: the 45 EDGE words had no reader, so "reachable from the roots" was still a relation over a table no C consulted.  The stage's four load-bearing choices are §6.7 ¶5bis's.  **Swap, then rewind** — `jpl_pools_swap()` before `reset()`, which makes §6.6's one allocator per pool *be* the to-space allocator instead of adding a second one (`allocators_emitted` stays **8**).  **The copy is the whole-cell structure assignment**, not a word-by-word rebuild: R7 made every cell a struct of `jpl_nat`, so a copy that split it would need a second description of the same layout.  **No arm of a word chain is a bare `else`** — a catch-all would answer the *last member's* value for an index that has no member, so `word_at(h, i)` outside the cell returns `JPL_NIL` (which already means "no child") and `word_put(h, i)` with such an index writes nothing; coverage is enforced where the arms are built — six emitter refusals plus 2a's `NPOS·4 == sizeof (cell)` typedef — not where they are printed.  **Four forwarding arms, and an `alloc` that clears `origin[h]`**, which is what makes the third arm mean *this round* rather than *ever*.  The scan pointer lands here because this is the slice that advances it | `verify/c/jpl_emit.ml` §6d (`word_arm`, `word_paths`, `cell_arms`, `arm_test`/`arm_slot`/`arm_chain`, `word_at_definition`, `word_put_definition`, `evac_definition`, `queue_start_definition`, `scan_one_definition`, `drain_definition`, `dispatch_definition`; 11 new `RUNTIME SUMMARY` keys, six word-chain refusals that exit 1), `verify/c/jpl_emit.sh` **check 9** — a drive whose *shape is derived*, since awk reads each pool's own edge-table row, finds the word whose class names that same pool, and refuses a pool with no self edge or a chain that cannot be built — plus **check 6**'s three accounting identities (`counters = 7·allocators + tag_guards + 1`, `mutable = counters + scan_pointers + space_globals`, and that total against the declarations counted in the TU, `bytes = 4·mutable`) and the vendored-evidence re-pin **moved behind check 9**, so the files compared are files the drive ran against; vendored `sh_run_jpl.h` **805 → 1176**, `sh_run_jpl_pools.c` **769 → 1834**, `layout.txt` **217 → 235** — **DONE (2026-10-06)**.  *Evidence*: gate **17/17**, exit 0, still with **no new `verify_models.sh` rung** (2e's script went **eight → nine** checks).  **Measured: 80 660 indices and 35 191 056 B of static storage, 65 interval/edge macros — the domain is unmoved, which is what a copy layer should leave it.**  `counters_emitted` **32 → 59** = 8 copied + 8 forwarded + 8 badref + **2** badtag + 1 unclassified, `mutable_globals_emitted` **33 → 68** = 59 counters + 8 scan pointers + the space indicator = **272 B / 0.3 KiB**; ¶5bis predicted 40 new globals / 74 total / 296 B / `counters 64`, and was **refuted in five places by §6.2's own rule** — `badtag` is a counter nothing would write in the six untagged pools — which is the reason predictions are written down.  `allocators_emitted` still **8** and every `EDGE SUMMARY` key unmoved; `RUNTIME SUMMARY` now **38** keys; header compile-time assertions **86 → 87**, the new one being `jpl_check_dispatch_arms_cover_every_target` (eight dispatch arms + the unclassified default == the whole EDGE target set).  **The drive**: six self-edge chains — `pair_text_text_list`, `cmd`, `text_list`, `cmd_list`, `pair_text_list_cmd_list_list`, `frame_list` — each reporting `copies 5 forwarded 1 badref 3 taken 9 peak 3` across **two** boundaries, the two tagged pools each taking exactly **1** garbage tag into `badtag` while leaving **4** (`cmd`) / **5** (`frame`) payload words exactly as written, **18** out-of-region references refused without moving a frontier, `unclassified = 0`, **0** assertion failures.  *The rung has teeth, and two of its three teeth are invisible to accounting*: **M1** (dropping the `origin[o] == h` arm from the forwarding test) gave **78** drive failures and moved exactly one report key, `origin_clears_emitted` **8 → 0**; **M2** (a bare `else` closing a word chain) gave **78** failures and moved **no** summary key at all; **M3** (the dispatch's unclassified arm incrementing nothing) gave **24** failures, `unclassified = 10`, and again **no** key.  All three ran in a scratch mirror of `verify/c/`, none in the tree, because mutating the shipped emitter is what the classifier refuses.  *What it does NOT close*: the swap still has **no caller**, so no kernel rewinds at a boundary and "cells returned" remains meaningful only within a region; forwarding is proven **per pool**, never across pools, so §6.7 design item (ii)'s graph with *known* sharing stays ii-b-2e's; `jpl_collect()` and the model's `BLimit` are ii-b-2d's; and no Coq theorem moved — the model still has no store, so the behavioural claims stay #26/#27.  See §6.7 ¶5bis and the HISTORY entry |
| JPL.5 · #25 | Tail-loop OCaml → JPL-C99 **emitter** (pure layout only: `list`→array+len, `nat`→`uint32`) | *emitter input `sh_run_c.ml` → output `.c`* — **un-blocked, and now half-built: the layout half (5-B.2, re-pinned by 5-B.2b and 5-B.2c) is gated green as `sh_run_jpl.h`, and the capacity that half was waiting on landed as 5-B.2b; the lowering half (5-B.3: the tail loops → `while`, the bounded structural recursions → copy loops, R8's monomorphization census — the loop/recursion split quoted here as "6 + 9" is 5-B.1's estimate, and 5-B.3a **re-measured** it as 7 fuel loops + 3 structural tail loops + 5 folds with no `while` at any budget) is **measured, declared, and now rendered wherever a body can exist at all**: the census is gated as block 2f, R8's closed set is gated as the `sh_run_jpl_abi.h` declaration layer (5-B.3b-i), and §6.4's renderability trial is gated together with the four scalar-leaf bodies and their exhaustive C-vs-kernel differential (5-B.3b-ii-a), leaving **5-B.3b-ii-b-2d..6 — decision 3's step-boundary copying (its edge table, its two intervals and the evacuation of one cell are done; the roots and `collect`, and the driven cross-pool collector probe are not), the two loop forms, `MAX_STACK's depth guard and the 5 model-side fold rewrites** as what remains; ii-b-0, the dual-debt measurement that fixed that order, landed first and changed no verdict, ii-b-1 landed the runtime that makes a cell exist, ii-b-2a landed the table that says which of its words are edges, ii-b-2b landed the space a copy goes into, and ii-b-2c landed the copy, the forwarding and the scan that walks it.**  5-A.5 settings + artifact, 5-A.6 kernel wired onto the proved loops, 5-A.7 no mutual fixpoint left, 5-B.1 typed closure + subset gate, **5-B.2 representation header + differential cap gate**, 5-B.3a lowering census, 5-B.3b-i ABI declarations, 5-B.3b-ii-a scalar-leaf bodies + their exhaustive differential, 5-B.3b-ii-b-0 the dual-debt columns, 5-B.3b-ii-b-1 the pool runtime, 5-B.3b-ii-b-2a the derived edge tables, 5-B.3b-ii-b-2b the two intervals + `origin` + the swap, 5-B.3b-ii-b-2c the evacuation + the scan pointer + the generated drive |
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
| ✅ DONE | JPL.1, JPL.2, JPL.3, JPL.3b, JPL.4, 5-A.1, 5-A.2, 5-A.3, 5-A.3 gap (#34), 5-A.4, 5-A.5, 5-A.6, 5-A.7, 5-B.1, 5-B.2a, 5-B.2 (#39), 5-B.2b (#40), 5-B.2c, 5-B.3a (#41), 5-B.3b-i (#41), 5-B.3b-ii-a (#42), 5-B.3b-ii-b-0 (#41), 5-B.3b-ii-b-1 (#41), 5-B.3b-ii-b-2a (#41), 5-B.3b-ii-b-2b (#41), 5-B.3b-ii-b-2c (#41) | 26 |
| 🔵 IN PROGRESS | — | 0 |
| ⏳ PENDING | JPL.5 (#25, remaining half = 5-B.3b-ii-b-2d..6 — decision 3's step-boundary copying (its edge table, its two intervals and the per-cell evacuation landed; the roots and `collect`, the driven cross-pool collector probe, and the multi-pool boundary remain), the two loop forms, `MAX_STACK`'s depth guard, the 5 model-side fold rewrites; ii-b-0 ordered them, ii-b-1 landed the runtime, ii-b-2a the table, ii-b-2b the space to copy into and ii-b-2c the copy), JPL.6 (#26), JPL.7 (#27) | 3 |
| **Total** | | **29** |

*Rollup hygiene, recorded because the table was wrong before this edit*: **5-B.2c** and
**5-B.3a** closed without ever joining this rollup or gaining a §9.1 row — each landed its
evidence, its gate rung and its HISTORY entry, and the count just froze at 17 for two stages.
That is the failure mode this section exists to prevent (a stage that reads as unnumbered reads
as unstarted), so both are recorded now, beside the §9.1 rows added for them, rather than
silently re-numbered backwards.

*The arithmetic of this table, because a slice landing changed three numbers and only two of them
are sums*: **Total is the sum of the three buckets**, as it was when DONE read 20 and Total 23.  A
landed slice therefore moves DONE and Total together, and the PENDING row stays at **3** because it
counts JPL.5's *remaining half* as one item while the slices already closed are itemised in DONE —
the two rows overlap on #25 deliberately, since a slice that is not in the rollup reads as
unstarted, which is the failure mode above.

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

**Current front:** JPL.5 (#25), and inside it **5-B.3b-ii-b-2 — step-boundary copying**, the
slice §6.6's region design deliberately leaves to a reachability rule: a cell now exists, and a word
of it says whether it is a handle, but no body may return one until a survivor is copied before the
rewind.  **Specified as §6.7** (2026-10-05), which fixes the boundary and its derived roots, derives
the per-slot edge table R7's one-word slots cannot express, splits the work into ii-b-2a..e, and
shows the two spaces cost **+0.9 %** of static storage rather than a doubling — the headroom-2
product becoming the from/to split instead of being re-guessed.  **Three of its slices have landed.**
**ii-b-2a** (2026-10-05): every sized pool publishes one class per word of its cell, so "live" has a
referent — 45 EDGE words a collector is told to follow.  **ii-b-2b** (2026-10-06): the array is now
**two intervals** (`2·cap + 2` indices, `2·(cap+1)`, each space reserving its own index 0), every pool
has the `origin` array a forward writes, `is_live` is the three-bound interval comparison, and the
whole runtime has **one** interval indicator with **one** writer — which is the rung that turned
§6.6's recorded aliasing debt into a measurement: the sweep now calls a handle from the abandoned
interval dead *while it sits below the current `next`*, a case a one-interval runtime cannot express
and, as the negative control showed, cannot even fail.
**ii-b-2c** (2026-10-06): the word between them.  Per pool the runtime now has `evac` with the
four-arm forwarding test, the `word_at`/`word_put` chains that let the scan rewrite one EDGE word of a
copied cell without a pointer or a cast, `queue_start`/`scan_one`/`drain` over a to-space **scan
pointer**, one `evac_by_class` dispatch whose 8 arms cover the whole target-id domain, and the
`origin` clear inside `alloc` that makes the test's third arm mean *this round* — plus a generated
drive that walks a three-cell chain with shared tail across **two** boundaries for each of the six
pools that have a self edge, asserts `copies 5 / forwarded 1` and the 18 refused bad references, and
catches the two collector bugs that move **no** number in the report.
The front is therefore **ii-b-2d**, the roots and the boundary: a derived root list for `cfg`/`out`,
`jpl_collect()` = evacuate the roots + drain every pool's scan + swap, and `BLimit` on overflow.  The
primitive exists and is measured; **nothing calls it**, which is why every kernel-attributable `peak`
in this tree is still the 0 the report prints.
**5-B.3a**, the measurement that had to precede the
bodies, **5-B.3b-i**, the ABI declarations that measurement already fully determined,
**5-B.3b-ii-a**, the scalar-leaf bodies §6.4 could prove renderable, **5-B.3b-ii-b-0**, the
dual-debt column that says why the loops cannot come first, **5-B.3b-ii-b-1**, the pool
runtime that makes a handle point at a cell, and **5-B.3b-ii-b-2a**, the edge table that says which
of its words one is, all landed 2026-10-05.
L1–L8 are
axiom-free and the shape JPL.5 reads is now the shape that is proved: `sh_run_c.ml`
extracts from `sh_jpl_run_c.v` + `sh_jpl_run_phase3.v` + `sh_jpl_run.v` + `sh_jpl_scan.v`
under the JPL settings, **66** parity checks bind it to the reference oracle, block 2c's
`diff -q` binds the vendored bytes to that extraction, block **2d (5-B.1)** reads those
same bytes the way the emitter has to — the typed closure from `mrun_c,step_c`, classified
construct by construct, refused if anything in it is outside the declared subset — and
block **2e (5-B.2)** now turns that closure's types into the C99 header the host will
compile against: 40 layouts, each size checked by the compiler, and all ten capacities
cross-checked between a syntactic constant fold and the OCaml runtime evaluating the same
extracted term.  5-B.2c (2026-10-05) closed the one gap the derivation left inside its own
decision 1: `cmd` and `frame` were declared pooled but the header dimensioned only their
*list* cells, so the type layer now also declares `jpl_cmd_pool` (`JPL_MAX_CMD` cells ×
headroom) and `jpl_frame_pool` (`JPL_MAX_STACK` cells × headroom) — 8 `extern` pools, bounded
total **34 049.0 KiB** *(those eight arrays are **34 051.2 KiB** of pools plus **315.1 KiB** of
`origin` tables since §6.7's ii-b-2b made each one a two-interval region — §6.7 paragraph 4's
+0.93 %, not the doubling a "two pools" reading implies)* — and the two halves of the decision are cross-checked by the emitter,
which refuses a name in `pooled_types` that `pool_cap` does not size rather than letting it
silently fall through to a by-value layout.  Block **2f (5-B.3a + 5-B.3b-i + 5-B.3b-ii-a)**
reads the same closure for *shape* rather than layout — one lowering schema per binding, R8's
instance set resolved at the call sites, the pools the closure demands, where every lambda value
sits — renders the **6** closed instances as `verify/c/sh_run_jpl_abi.h`, declarations only, and
then asks §6.4's second question of every one of the **47** members by *running* the renderer:
**4** bodies pass the trial and are emitted as `verify/c/sh_run_jpl_bodies.c`, which the gate
compiles against 2e's header so the two cannot drift into two variants of one naming rule, and
sweeps them against the extracted kernel over `0 … MAX_FUEL` — **136 450 lines, `cmp` identical**,
from two drivers the census generates from the same rows.
Of the decisions open at JPL.5's opening, two are
**settled by measurement** and one is **half-settled, with the remaining half now named by a
missing bound rather than by a design choice**:

1. ~~Which root JPL.6's Rule-6 (no-recursion) lint binds~~ — **closed 2026-10-04 by 5-B.1,
   mechanically.**  The answer was already "the shipped roots", but 5-B.1 turned that from
   an argument into a *root-sensitive* result the gate asserts in both directions: over
   `mrun_c,step_c` ⇒ **SUBSET OK**, and over the oracle roots
   `run,step,mrun` it reports `OFF-SUBSET mutual fixpoint: expand, expand_name,
   expand_brace, run, run_seq, run_for, run_case` and exits 1.  Block 2d-negative pins the
   refusal, because a lint that accepts every root is not a gate.  The measured shape:
   artifact **81** bindings / **76** signatures / **14** type declarations *(the current
   artifact reads **89 / 83 / 15**: 5-B.2a's `jpl_caps_table` export added the record type
   and its accessors → **87 / 81 / 15**, and 5-B.2b's `MAX_WORDS` added `mAX_WORDS` and
   `benv_words` → **89 / 83 / 15**.  Neither reached the shipped closure, which is still
   byte-identical over `mrun_c,step_c` — they are data outside the control flow the lowering
   pass reads; see §9.1's 5-B.1 and 5-B.2b rows)*; shipped closure
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
   are now `verify/c/sh_run_jpl.h`, gate block 2e checks it, and §6.2 numbers the choices
   the derivation could not make (three from 5-B.2; 5-B.3a added the fourth).  Two of 5-B.1's arithmetic inputs changed under
   measurement, and the header is the authority, not this paragraph: a `jpl_text` is
   **1028 B, not 260 B**, because R1 keeps every field one word and R2's codes stay
   `uint32_t` (the model *intends* each code `< 256` and never proves it, so narrowing to a
   byte would be an unproved claim — see §6's table); and the live set is **not** bounded by
   the caps once words are counted, because `MAX_CMD` nodes can each own a `MAX_LIST`-word
   list, so 5-B.1's "half a MiB" is a *sum of single-kind bounds*, not a simultaneous worst
   case.  Measured instead, from the derived pools: the bounded static total is
   **187.0 KiB** (env 3.0 KiB + three `MAX_LIST` kinds at 16.0 + 16.0 + 24.0 KiB + frame list
   128.0 KiB), every cell count printed as "n cells × headroom 2".  Three things were left
   open, and each has an owner: **(a)** the word slab had *no* capacity — CLOSED 2026-10-05
   the same way 5-B.2a closed the other nine, by the model rather than the emitter:
   `sh_jpl.v` §1's `MAX_WORDS` with §7.1/§5's proofs behind it (§4.1), exported as
   `jpl_caps_table`'s tenth field, so the header now declares
   `extern jpl_text jpl_word_pool[JPL_POOL_WORD];` and 5-B.3 can link; **(b)** the per-step
   allocation bound, which §6.2's headroom 2 explicitly holds as a placeholder, to be
   replaced by 5-B.3's allocation census and JPL.7's measured high-water mark.  **5-B.3a ran
   that census on 2026-10-05 and (b) narrowed rather than closed**: the census measures
   allocation *sites* (309 of them, demanding 7 pools), and a capacity needs cells live at
   one step boundary, i.e. sites × loop trips, which is not in the artifact's text — so the
   placeholder's only remaining owner is JPL.7's measurement, §6.2's decision 4 records the
   refusal to read the site count as an extent, and the `× 2` is unchanged for all eight
   pools.  The stages tracked here as **5-B.2 / #39**, **5-B.2b / #40** and **5-B.2c** are
   DONE, **5-B.3a** joined them the same day, and the remaining half of the lowering pass
   lives under JPL.5 (#25) as **5-B.3b**.  **(c)** is the one this section's own text
   did not foresee, and it was found by scoping 5-B.3 rather than by the layout run: decision
   1 declared `cmd` and `frame` *pooled* while the emitter dimensioned only their **list**
   cells, so the header's 6 `extern` pools allocated nothing for the nodes the two types turn
   into.  5-B.2c (2026-10-05) registered `jpl_cmd_pool` (`JPL_MAX_CMD` cells × headroom,
   16 B per node ⇒ 128.0 KiB) and `jpl_frame_pool` (`JPL_MAX_STACK` × headroom, 20 B ⇒
   320.0 KiB) from inside `node_layer`, i.e. from the same rule that emits the node struct,
   and made the two halves of decision 1 cross-check each other: a name in `pooled_types`
   that `pool_cap` does not size is a hard refusal, never a silent fall-through to the
   by-value fat layout.  Strength, restated after all three closes: the recursivity
   that forces the handle encoding is **read off the artifact's own type declarations** (a
   definition, so certain); every cell size and every cap relation is **checked by the
   compiler** (**86** `typedef char jpl_check_*[…]` array-bound assertions cover all emitted
   types — each aggregate row by itself, the one-word typedefs as a family, the cap
   relations and the word width, the two pinning `JPL_MAX_WORDS` to its named sum
   `2·MAX_STACK + 2·MAX_ENV + 2` and to `MAX_STACK ≤ MAX_WORDS ≤ GLOB_FUEL`, and since
   §6.7's ii-b-2b four per pool saying the two intervals tile the array, serve exactly the
   artifact's cap and share their index domain with `origin`); the pools'
   **34 051.2 KiB** bounded total (**34 366.3 KiB** with the eight `origin` tables ii-b-2b
   adds) is compiler-checked arithmetic on the ten artifact-carried
   caps, of which the tree half and the environment half are **proved in the model**
   (`cmd_fits_words`, `benv_words_le`) and the expanded-copy half is the **named obligation**
   "one live frame per source node"; and the per-step allocation bound is **not established
   either way**.  What closing (a) cost, printed by the same report: the slab alone is
   **33 416.0 KiB** of that 34 051.2 KiB — **98 %** of everything the type layer asks a host
   to link, and **52.6×** the seven pools beside it (635.2 KiB, counted in bytes rather
   than cells) — a number a JPL.7 host has to link, which
   is why §6 also records the `uint8_t`-codes follow-on instead of leaving it to be
   rediscovered.
   **5-B.2a (2026-10-04) closed the input side of this decision**: a layout that allocates
   against `MAX_CMD`/`MAX_STACK` needs those numbers *in the artifact*, and four of the nine
   §4.1 caps were not there because only proof code mentioned them.  `sh_jpl.v` §1.1 now
   exports the complete table as `jpl_caps_table`, field-pinned against the LOCKED literals
   by `jpl_caps_are_locked`, and the extraction driver carries it, so the emitter reads every
   cap from the same bytes it reads every function from and holds no cap of its own — a
   claim the gate now checks rather than asserts: block 2e's differential fold compares the
   emitter's *syntactic* reading of those nine literals against the OCaml runtime
   *evaluating* `jpl_caps_table`, and the emitted `#define`s must equal both.
   **5-B.2b (2026-10-05) added the tenth the same route**, so the sentence above now reads
   *nine as exported on 2026-10-04, ten as exported now*: `MAX_WORDS` is a `Definition` in
   §1, a `jpl_words` field of `jpl_caps`/`jpl_caps_table` in §1.1, pinned by the extended
   `jpl_caps_okb`/`jpl_caps_are_locked` and placed by `cap_words_order`, and the differential
   fold in block 2e pairs it by name against the runtime's value (`jpl_words 16642`) like the
   other nine — so the emitter still holds no number of its own, and that continues to be
   true only because the artifact carries it.

**Verification state (the empirical net that makes DONE credible):**

| Check | Status | Where |
|---|---|---|
| Models gate (coqc + coqchk ×8 + 3 extraction blocks + the three emitter rungs) | **17/17 green** (11/11 until 5-B.1 added block 2d + its negative control → 13/13; 5-B.2 added block 2e + 2e-negative → 15/15; 5-B.3a added block 2f + 2f-negative → **17/17**; 5-B.3b-i, 5-B.3b-ii-a and 5-B.3b-ii-b-0 added **checks** to 2f rather than rungs — that script grew from four checks to six, then eight, and ii-b-0 extended check 5 — and 5-B.3b-ii-b-1 did the same to 2e, whose four checks are now seven, and ii-b-2a's edge table made them **eight**; ii-b-2b rewrote check 5's sweep rather than adding a ninth, so the count is unchanged and what it means is wider; **ii-b-2c added the ninth check** — a generated evacuation drive, again inside 2e's script, so the runner is still 17 rungs) | `verify_models.sh` |
| A pool cell exists, is bounded, and fails loudly at the bound | **measured, and measured twice** — the emitted `sh_run_jpl_pools.c` compiles under the JPL flag set *with* code generation (`-Wconversion -Wsign-conversion -Werror`, no `-fsyntax-only`), and a sweep generated from the header's own allocator declarations drives **both intervals** of all **8** pools to each bound: `served == cap` per interval, `refused == 6` (three past each bound, one from an un-rewound region after a swap, one ending each fill), `peak == cap` **in both** intervals (so it is a per-region count, not the high-water index), a rewind that returns `cells` for the region it owns and **0** for one it does not, `0` assertion failures, and `jpl_pools_refusals()` equal to the per-pool sum (**48**).  The **38** `RUNTIME SUMMARY` keys then close against each other, the header and the TU (`runtime_names_colliding_with_prototypes = 0`, `counters_emitted = 7 × allocators_emitted + tag_guards_emitted + 1`, `mutable_globals_emitted = counters + scan_pointers + space_globals` and equal to the declarations counted in the TU, `mutable_globals_bytes = 4 × mutable_globals_emitted`, `runtime_cells_total` = the sum of the header's macros, `space_cells_served_total + allocators_emitted == runtime_cells_total / regions_per_pool` — the reserved base of every interval, made visible rather than rounded away) | gate block 2e, checks 3, 5 and 6; `verify/c/sh_run_jpl_pools.c`, §6.6 |
| A handle carried across a swap is dead, and decidable without a liveness analysis | **measured, and this is the rung §6.6 recorded as debt** — `is_live` is the three-bound interval comparison, and the sweep keeps a handle allocated in the low interval, swaps, and asserts *both* that it still sits **below** the current `next` and that the runtime calls it dead, once per interval, then requires the two counters equal and non-zero so a probe that never reached the case cannot pass it silently: **16** assertions across the eight pools.  The array is `SPACES·(cap+1)` indices with each space reserving its own index 0, `origin[]` covers the whole index domain (`sizeof` pinned against the pool's own dimension), and the interval indicator is **one** global whose **assignments are counted in the file that defines it** (2: the definition and `jpl_pools_swap()`).  Teeth: reverting the comparison to §6.6's reading moved **no report key at all** and produced exactly those 16 failures — the mutation is invisible to every accounting rung and fatal to this one | gate block 2e, checks 5 and 6; §6.7 paragraph 4 |
| Which word of a cell is a handle, and what may be forwarded through it | **measured, and measured four ways** — every sized pool publishes one class **per word** of its cell (`jpl_<stem>_edge[]`, dimensioned by `JPL_<stem>_NEDGE`) and `NPOS × 4 == sizeof (cell)` as a `jpl_check_*` typedef, so the compiler rather than a comment says a row covers the struct it describes.  **8** tables / **26** rows / **358** classes = 286 SCALAR + 27 UNUSED + 45 EDGE, partition residual **0**; an edge may name exactly the **8** pools the header declares, in both directions; the word slab's all-scalar row is *derived* from the array field its struct declares, not excepted from the walk.  Check 7 re-derives rows, widths and classes from the header's constructor comments, from the pools TU's initialiser tokens one class at a time, and from the `.mli`'s arities with **parenthesis depth counted** — three readings that never consult the table — and asserts two properties the collector depends on (a node row's first word is SCALAR, no `UNUSED` sits inside a row).  **Since ii-b-2c the table has a reader**: `jpl_<stem>_scan_one` walks exactly `NPOS` classes of the row its cell's tag names, and the drive follows 45 EDGE words' worth of them across two boundaries — so this is no longer only a data dependency, though it is still not a reachability *result* until ii-b-2d's roots make a walk start on its own | gate block 2e, checks 7 and 9; `verify/c/sh_run_jpl.h`, `verify/c/sh_run_jpl_pools.c`, §6.7 |
| One cell is evacuated, forwarded, and re-evacuated across a second boundary | **measured, by a drive whose shape is derived rather than typed** — for each of the **6** pools whose edge table names its own pool (found by awk, which records `word = col % NPOS`, `row = col / NPOS` and refuses if a table's `NPOS`/`NROWS` are missing; **`cmd` is one of the six**, at word 1 of row 3, which corrects this doc's earlier claim that it had no self edge), the generated probe builds `a → b`, `c → b`, crosses the boundary in the runtime's own order (`swap`, `reset`, `queue_start`, `evac` the roots, `drain`) and crosses back.  Every chain answers `copies 5 forwarded 1 badref 3 taken 9 peak 3`: round 1 copies three and forwards one (the shared tail — the survivor count design item (ii) asked for), the copy is structurally equal to its source word by word, `scan == next` at the fixpoint; round 2 asserts `origin[a]` still names last round's copy *and* that `alloc` hands back a cell whose own entry is nil, then copies rather than forwards, which is 5bis's third-and-fourth-arm argument made observable.  `badref` **3** per chain — a handle in the current interval (a copy of a copy), `OTHER_BASE` (the reserved zero of the region being read from), `JPL_POOL_<KIND>` (one past the array) — 18 refusals with `next` unmoved, `evac(JPL_NIL)` moving nothing; and the two tagged pools get a second test in which a garbage tag (`NROWS + 5`) stops the scan with `badtag` **1** and leaves **4** (`cmd`) / **5** (`frame`) non-nil words exactly as written, so a scan that walked slots as scalar cannot pass it.  `jpl_pools_unclassified == 0` per chain, per tag test and for the whole run; **0** assertion failures over all eight functions.  *Teeth*, in a scratch mirror: dropping `alloc`'s origin clear gives **78** failures and moves one key (`origin_clears_emitted` 8 → 0); deleting the mutual arm (`origin[o] == h` → `o < next`, arity-preserving) gives the same **78** failures and moves **no** summary key; mis-wiring one dispatch arm's class macro gives **24** failures with `unclassified = 10` and also moves **no** summary key — two of the three collector bugs here are invisible to every count in the report, and this rung is the only one that sees them | gate block 2e, check 9; `verify/c/jpl_emit.sh`, `verify/c/sh_run_jpl_pools.c`, §6.7 paragraph 5bis |
| Every shipped binding has a lowering schema, over the vendored bytes | **measured** — 47 members classified into 26 straight-line + 7 fuel tail loops + 4 one-trip fuel idioms + 3 structural tail loops + 5 non-tail folds + 2 operator aliases, with each loop's first fuel traced to a parameter; the 5 folds are printed as `BOUNDED FOLD (non-tail)` **refusals**, not as lowering targets *(this row read "6 straight-line" until 5-B.3b-i audited it — 6 + 7 + 4 + 3 + 5 + 2 is 27, not the 47 the report marks, and the row had been quoted as if it agreed)* | `verify/c/jpl_lower.sh`, gate block 2f, `verify/c/lowering.txt` |
| R8's instance set is counted, not assumed | **measured** — 5 polymorphic bindings, 29 call-site uses, **6 closed** instances (one C function each) and **6 open** (nothing to emit), each open one justified by a use point the interface cannot close | `verify/c/lowering.txt`, gate block 2f |
| A lowering cannot need a function pointer (D-60411 forbids them) | **asserted zero** — 68 first-class-function sites, each in one of the four positions a lowering absorbs, `function_value_sites_unnamed = 0`.  Since 5-B.3b-i this zero is known to be a **different statement** from "every instance is nameable": `abi_refused_no_c_type = 1`, because a value can sit in a position the control-flow rules absorb and still leave its *callee* with no C type (§6.3's ABI paragraph) | gate block 2f, checks 2 and 4 |
| The census and the shared reader agree about self-calls, and about the pools | **measured** — direct self-references agree for **47 of 47** members (`self_reference_mismatches = 0`, asserted), and every pool the census **demands** (7) is a pool 2e's header **declares** (8; the surplus `jpl_frame_pool` is printed as §6.2 decision 1's documented consequence) | gate block 2f, checks 2 and 3 |
| The lowering census is root-sensitive too (has teeth) | **measured** — roots `run,step,mrun` ⇒ `LOWER REFUSAL: no lowering schema exists for this root set` + `mutual fixpoint: …`, exit 1: the **third** independent refusal reason over the same artifact, after 2d's subset violation and 2e's function-typed layout refusal.  Since 5-B.3b-i the same run must also leave the vendored artifacts byte-identical (`cksum` before/after), because the census is handed output paths and a refusal that wrote a half-rendered header, a half-written TU or half a driver would corrupt the evidence the positive rungs compare against; since 5-B.3b-ii-a that set is **five** files, and the census writes all of them only after a complete run | gate block 2f-negative |
| R8's closed instances are rendered as an ABI, and the rendering accounts for itself | **measured** — `abi_instances == instances_closed` (6), `abi_prototypes + abi_refused_no_c_type == abi_instances` (5 + 1), `abi_bodies_expressible + abi_bodies_owed == abi_prototypes` (2 + 3), `abi_blocked_outside_fold_set = 0` (a refusal §6.3 assigns to no owner is the failure; `forallb`'s, which it does assign, is printed as a finding), and the same three counts re-taken from the rendered file's own declaration / `NOT EMITTED` / `declaration only` lines | `verify/c/jpl_lower.sh` check 4, gate block 2f, `verify/c/sh_run_jpl_abi.h` |
| The ABI header and the representation header share one value-naming rule | **measured** — a translation unit including `sh_run_jpl.h` then `sh_run_jpl_abi.h` compiles under `-std=c99 -Wall -Wextra -Wconversion -Wsign-conversion -pedantic -Werror -fsyntax-only`, so every type name the ABI prints is one 2e typedef'd and no hidden conversion fires.  Its teeth were checked separately: a scratch `value_name` that returned `jpl_wref_typo` left **all 24 SUMMARY keys identical** and failed only at the compiler, which is why the compile is a rung and the accounting is another | `verify/c/jpl_lower.sh` check 6, gate block 2f |
| The §6.4 renderability verdicts partition the closure, and are the renderer's own trial results | **measured** — `DATA + ALIAS + RENDER + OWED-REPRESENTATION + OWED-SCHEMA + OWED-CONSTRUCT == members` (11 + 2 + 4 + 13 + 15 + 2 = **47**), `render_unaccounted = 0`, and `sh_run_jpl_bodies.c` carries exactly one definition per `RENDER` row (4).  The verdict is not a second classification: §6.4's licensed set is implemented as `render_def` and *run* over every member, so a refusal is the renderer's own message naming the construct, the pooled type, or the §6.3 schema that stopped it — and `is_name`, which cites a `DATA` macro and calls two `RENDER` callees, is why the trial is a fixpoint rather than one pass | `verify/c/jpl_lower.sh` check 5, gate block 2f, `verify/c/lowering.txt` |
| Every owed row is read for **both** debts, and the verdict must be explained by them | **measured** — §6.5's columns come from the same `pool_of` walk the trial consults, asked of all 47 members: `owed_schema_also_pool + owed_schema_pool_free == owed_schema` (10 + 5 = 15), the three pool-free *reasons* sum to the pool-free count (5 var + 0 opaque + 0 scalar = 5), `dual_debt_rows == owed_schema_also_pool + owed_construct_also_pool` (10 = 10 + 0), the refused rows that touch a pool re-sum as 10 + 0 + 13 = **23**, `owed_schema_free_var_pooled_instance ≤ owed_schema_pool_free_var` (4 ≤ 5, one measurement cross-checking another), and `debt_unaccounted = 0`.  Its teeth are the *reason* column rather than the count: `owed_schema_pool_free_scalar = 0` is what says a loop form alone renders nothing, and `owed_construct_also_pool = 0` is the §6.4 rule order holding — if the pool rule ever moved behind the licensed set, that zero would become nonzero here and nowhere else | `verify/c/jpl_lower.sh` check 5, gate block 2f, `verify/c/lowering.txt` |
| A rendered body cannot cite a constant that does not exist | **measured** — the 11 `DATA` names the trial prints are resolved against `sh_run_jpl.h`'s own `#define` lines (all 11), and the emitted TU compiles under 2e's flag set, so `JPL_C_B_0`/`JPL_C_B_USCORE` cited by 2 of the 4 bodies are checked to be the same symbols the layout layer defines.  This is the only rung that sees a citation and a definition together, so a constant the renderer invented would land here rather than in JPL.7's host | `verify/c/jpl_lower.sh` checks 5 and 6, gate block 2f |
| The rendered bodies compute what the extracted kernel computes, over every bounded input | **measured** — the census generates `jpl_bodies_diff.c` and `jpl_bodies_diff.ml` from the same `RENDER` rows that wrote the bodies file; the gate builds the C half under 2e's flags minus `-fsyntax-only` and the OCaml half against the vendored extraction, runs both over `0 … MAX_FUEL` (**136 450** lines each, asserted against the report's own `sweep_domain` so neither driver picks its range), requires the swept fields to take **5** distinct values (a pair of constant transcripts would `cmp` clean for free), and `cmp`s the transcripts — identical.  `bodies_swept_exhaustive = 4`, `bodies_swept_diagonal = 0`: every rendered body takes exactly one `nat`, so the domain is covered whole rather than along a diagonal | `verify/c/jpl_lower.sh` check 7, gate block 2f |
| One C spelling rule for three layers | **measured** — `c_fn`/`c_upper`/`data_macro`/`cap_macro_of_data` moved from `jpl_emit.ml` into the shared reader, and the emitter's hand-typed seven-name cap list became derived from the artifact's own cap table; 2d and 2e were re-run and `closure.txt`, `layout.txt` and `sh_run_jpl.h` came out **byte-identical**, so the move changed the ownership of the rule and not the C it produces | `verify/c/jpl_ast.ml` §9, gate blocks 2d and 2e |
| Vendored census evidence is byte-identical to a fresh census | **measured** — `verify/c/lowering.txt` (783 lines), `verify/c/sh_run_jpl_abi.h` (50), `verify/c/sh_run_jpl_bodies.c` (49) and both generated drivers (`jpl_bodies_diff.c` 20, `jpl_bodies_diff.ml` 14) regenerated and `diff -q`'d (`JPL_REGEN=1` re-pins all five together, so a TU or a driver that drifts from its measurement cannot be vendored silently) | `verify/c/jpl_lower.sh` check 8, gate block 2f |
| The gate reads measurements, not prose | **measured** — `lowering.txt` ends with a 44-key SUMMARY, each key marked by the section that produced it, and the run **refuses** if a key is missing; `jpl_lower.sh` takes its assertions from those keys | `verify/c/jpl_lower.ml`, `verify/c/jpl_lower.sh` |
| Emitted C99 header compiles under the strict JPL flag set | **measured** — `clang -std=c99 -Wall -Wextra -Wconversion -Wsign-conversion -pedantic -Werror -fsyntax-only` clean over `verify/c/sh_run_jpl.h`; **86 compile-time assertions** cover every emitted type (each aggregate row carries its own `sizeof` check, the 13 one-word typedefs are covered by `jpl_check_one_word_families`) and every cap relation, so a wrong byte count is a build failure, not a stale comment.  36 through 5-B.2b, **53** after ii-b-2a's 8 `edge_covers_the_cell` rows, **86** after
**ii-b-2b** adds 32 interval relations (four per pool: `two_regions`, `regions_tile_the_array`, `region_serves_the_cap`, `origin_is_the_index_domain`) plus the swap's `pools_flip_cycles_the_intervals`, and **87** since **ii-b-2c**'s `jpl_check_dispatch_arms_cover_every_target`, which pins the highest target id a table can contain against the last arm the dispatch can reach — the one compile-time relation in this layer that is about a *chain of functions* rather than about a size | `verify/c/jpl_emit.sh` check 2, gate block 2e |
| The **ten** capacities agree across the artifact, the fold and the header | **measured** — a probe that carries no number reads `Sh_run_c.jpl_caps_table` at runtime; the emitter's syntactic fold of the same term must match it name-for-name, and each value must appear as `#define JPL_<NAME> <value>u` in the emitted header.  Nine until 2026-10-05, when `jpl_words = 16642` became the tenth | `verify/c/jpl_emit.sh` check 3, gate block 2e |
| Every declared pool has a capacity, including the word slab and the two node pools | **measured** for the dimension (8 `extern` pools, all array-sized from `jpl_caps_table`; since ii-b-2b each is `SPACES·(cap+1)` indices, so the pool storage is **34 051.2 KiB** — the slab 33 416.0 KiB of it, `jpl_cmd_pool` 128.0 KiB and `jpl_frame_pool` 320.0 KiB since 5-B.2c — plus **315.1 KiB** of `origin` tables for a bounded static total of **34 366.3 KiB**) · **proved** for the tree half (`cmd_fits_words`) and the environment half (`benv_words_le`) · **owed** for the expanded-copy half (the named invariant "one live frame per source node", §6) | `verify/c/layout.txt`, `sh_jpl.v` §1/§5/§7.1, gate block 2e |
| The layout layer is root-sensitive too (has teeth) | **measured** — roots `run,step,mrun` ⇒ `FATAL: tn: a function-typed value has no layout`, exit 1; the refused value is the oracle cluster's driver parameter (`type run_phi = int -> text list -> cstate -> cstate option`), a *different* reason than 2d-negative's mutual-fixpoint refusal | gate block 2e-negative |
| Vendored representation evidence is byte-identical to a fresh emit | **measured** — `verify/c/sh_run_jpl.h` (1176 lines) + `verify/c/sh_run_jpl_pools.c` (1834) + `verify/c/layout.txt` (235) regenerated and `diff -q`'d (`JPL_REGEN=1` re-pins all **three**, but the copy is **deferred to after check 9**, so a regeneration cannot vendor evidence the evacuation drive has not just approved — the pin is the last thing a green run does) | `verify/c/jpl_emit.sh` checks 8 and 9, gate block 2e |
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
representation layer, emitted the same day; **D8** was taken on 2026-10-05 by 5-B.3a's
lowering census, and the emitted-behaviour rung this row was pointing at is now
**D9**.)*  (iv) The front end reads the artifact but re-encodes no
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
*behaviour* — differential vectors against the kernel — is **D9**, still planned.  *(This
sentence pointed at **D8** when it was written; **D8** became 5-B.3a's lowering census on
2026-10-05, so the behaviour rung moved down one.)*

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
reaches is laid out and checked", not "the runtime exists".  *[Closed 2026-10-05 by
5-B.2b: the slab carries `JPL_POOL_WORD`, so 5-B.3 has an extent to lower against instead of
a declaration with no dimension (nothing links yet — limit (i), a header not a program, is
unchanged); (ii)'s "derived from caps, not from a proof the machine stays inside them" is
now half-closed — see the 5-B.2b entry's proved/owed split.]*  (v) The emitter stores no
semantics: if it ever grows a rule that changes a *behavioural* verdict rather than a
layout, it has become a second model of the kernel and must be deleted, same as 5-B.1's
limit (iv).

### JPL.5-B.2b / #40 — DONE (2026-10-05): `MAX_WORDS` in the model, the word slab sized in the header

The instruction was "sh_jpl.v §1's MAX_WORDS constant + proof + `jpl_caps_table` export,
then 5-B.3's lowering pass".  The first half is what landed; the second half is now
un-blocked in the only sense that mattered — the header has an extent to lower against.

**The number is a sum, and the sum is the argument.**  `MAX_WORDS = 2·MAX_STACK + 2·MAX_ENV
+ 2 = 16 642` cells: one `MAX_STACK` for the words a pool-admitting source tree holds, a
second `MAX_STACK` for the runtime-expanded copies an `FFor`/`FCase` frame holds, `2·MAX_ENV`
for the environment's name and value cells, and 2 for the per-step temporaries.  Three of the
four are theorems now — `cmd_words_le_count` + `cmd_fits_words` (§7.1), `benv_words_le` (§5),
`cap_words_order` + `MAX_WORDS_lt_fuel` (§1) — and the fourth is a *named* debt (§6).  The
alternative this stage rejected was to write `16642` into the model: the caps table would then
carry a literal no derivation explains, and 5-B.2's "the emitter holds no number of its own"
would have become false in spirit while staying true in the letter.

**A documentation error was found while sizing, not after.**  §6's previous paragraph asserted
the live words were bounded by `MAX_CMD × MAX_LIST` (4 194 304) and printed that range in
`layout.txt` as the honest answer.  It was a *per-node* argument wearing a *per-tree* claim: a
tree in which every node owns a full word list has `cmd_count` far above `MAX_CMD`, and
`cmd_fits` refuses it before the machine sees it.  Per tree the bound is `2 · MAX_CMD`, which
is what §7.1 now proves, and the emitter's "WHAT THIS LAYER COULD NOT SIZE" section prints
"Nothing" instead of a range.  Consequence for the budget, in both directions: the slab went
from *unmeasurable* to 33 414.0 KiB, i.e. about **179×** the five pools 5-B.2 had already
derived (187.0 KiB), because R2's `uint32_t` codes make a cell 1 028 B.  Narrowing the codes
needs a proved `code < 256`, which `sh_concrete.v` §1 only intends, so the narrowing is
recorded as a follow-on and the 32 MiB is recorded as the price of not doing it.

**Rocq 9.2 findings, all measured, kept because each cost a compile to learn.**

1. **A definitional unfolding can be quadratic in a fixpoint; a rewrite by the same equation
   is not.**  The first `cmd_fits_words` began `unfold cmd_fits in Hf` and made `sh_jpl.v`
   exceed 600 s (killed).  Bisected on copies of the file in a scratch directory: the
   §1..§7.1 prefix compiles in 4.3 s; the same prefix + a `Corollary` whose hypothesis is
   already `cmd_count MAX_CMD c <=? MAX_CMD = true` compiles in **5.4 s**; the same prefix +
   `exact Hf` at the goal `Nat.leb (cmd_count MAX_CMD c) MAX_CMD = true` from a hypothesis
   `cmd_fits c = true` is **>45 s — and >45 s with the fuel written as 128 as well as 4096**,
   so the cost is not the size of the numeral.  `sample` on the hung `rocqworker` showed the
   hot frames to be `Conversion.compare_under`, `CClosure.mk_subs`, `Esubst.push_vars_until`:
   the kernel is *reducing* the fuel-bounded `cmd_count` under all eleven `cmd` branches in
   order to compare `cmd_fits c` with its own body across an `eq bool … true`.  Writing the
   identical equation as a lemma (`cmd_fits_unfold`, by `reflexivity`, ~1.4 s, because there
   the two sides are compared as *terms* and the heads match after one delta) and reaching the
   hypothesis with `rewrite cmd_fits_unfold in Hf` is **5.1 s**.  The file carries this at
   §7.1 because the two spellings are indistinguishable from the statement.
2. **The earlier "lia over hypotheses mentioning recursive constants is the hazard"
   hypothesis was wrong, and it is corrected rather than quietly dropped.**  It came from a
   whole-file bisect that left two causes in the same proof (the `unfold` cast *and* the
   `assert … by lia`).  Isolating them: `dbl_le` proved by `lia` costs 4 ms, a `lia` step in
   the same script costs 0.012 s, and the slow variants above contain no `lia` at all.  The
   final proof still uses `Nat.mul_le_mono_l`/`Nat.le_trans` instead of `lia`, which is now a
   stated precaution rather than a measured necessity — the measured necessity is the cast.
3. `unfold A, B` does not reach constants revealed inside `B`'s body in the same command: for
   `cap_words_order` the list must be `unfold MAX_WORDS, MAX_STACK, MAX_ENV` (outermost
   first), otherwise the inequality is false for the revealed atoms and `lia` correctly
   refuses.  `lia` also cannot decide a comparison whose operand is `GLOB_FUEL` (a product
   body), so that half follows the file's existing convention, `apply Nat.leb_le. vm_compute.
   reflexivity.`
4. `vm_compute`/`reflexivity` against the literal `4294967295` **hangs** (Coq nat literals
   behave unary); `MAX_WORDS_lt_fuel` states the fit against `MAX_FUEL` symbolically instead.
   The C side has no such problem — `jpl_check_fuel_fits_the_word` compares against
   `4294967295u` and the compiler decides it.
5. Right-nested conjunctions destructure by depth, not by name: `cmd_words_le_count`'s
   `A /\ (B /\ (C /\ D))` gives conj4 alone as `[_ [_ [_ D]]]`, conj1+conj4 as
   `[A [_ [_ D]]]`, conj2+conj3 as `[_ [B [C _]]]` — one bullet per shape, and the `For`/
   `Case` bullets instantiate the *pair* slot with `(nil, nil)` because a `list text *
   list cmd` is not a `[]`.
6. `destruct pb as [pats body]` leaves `fst (pats, body)` and `snd (pats, body)` standing;
   `fst snd` has to be in the `cbn` list or the branch's `lia` fails on an unreduced pair.

**Extraction side-effects, measured rather than assumed.**  The artifact went **87 → 89**
bindings (`mAX_WORDS`, `benv_words`) while the tracked closure over roots `mrun_c,step_c`
stayed **byte-identical** — new data, no new control flow, so `closure.txt` re-pinned on its
header line alone.  Two facts about the spelling: `ExtrOcamlNatInt` hooks the `+`/`*`
*notation* to machine operators but a **qualified `Nat.add` in the source extracts as a call
of the artifact's own recursive `module Nat.add`**, written in the nat-destruct idiom and
non-tail at depth `MAX_STACK`; and `jpl_caps_table` is outside the shipped closure, so what
reaches C is the folded numeral (`JPL_MAX_WORDS 16642u`), verified against the OCaml runtime
*evaluating* that recursive `add`.  JPL.6 must not read either recursion as reachable from the
driver.

**Gate and evidence state after #40.**  `verify_models.sh` **15/15** (no new rung; block 2e's
differential fold now agrees on ten capacities and its printed digest now names the slab's
capacity instead of its absence), `coqc sh_jpl.v` 8.6 s, `coqchk -o -silent` four `<none>`
with no `Axiom`/`Parameter`/`Admitted`/`admit`, parity **66** unchanged, `conformance.sh`
**33/33**, `JPL_REGEN=1 verify/c/jpl_emit.sh` re-pinned `sh_run_jpl.h` (370 lines, 36
assertions, 6 dimensioned pools) and `layout.txt` (111 lines, PENDING 5 — R8's polymorphic
bindings only), `JPL_REGEN=1 verify/c/jpl_front.sh` re-pinned `closure.txt`.

**Harness lessons from the same day, because they wasted an hour each.**  `cmd | tail`
block-buffers, so a long compile looks silent *and* loses output; `coqc -time` prints
progressively, so a killed run's log still names the last completed command, and
`perl -e 'alarm shift; exec @ARGV' N coqc x.v` is the portable per-run timeout on macOS (no
`timeout`/`gtimeout` there); detached `&`/`nohup` jobs do not survive a tool call — use the
background-task mechanism; and `pkill -f coqc` matches the harness's own shell, which killed
three of my own compiles before it was replaced with `ps … | grep "[f]ile.v"` and explicit
PIDs.

**Honest limits after #40.**  (i) The second `MAX_STACK` is a *charged* summand: if 5-B.3
refutes "one live frame per source node", `MAX_WORDS` rises and the caps table, the header and
`layout.txt` re-pin together — the debt is named in §6 and no array dimension hides it.
(ii) The headroom factor 2 is still an admitted placeholder (decision 3's leftover (b)), and
the per-step allocation bound remains **not established either way**.  (iii) This is still a
header, not a program: nothing emitted has met JPL.6's shall-rules for function bodies.

**5-B.2c (2026-10-05) — the type layer's own bookkeeping, and one reading instead of three.**
Scoping 5-B.3 against the artifact found two defects that the layout run itself could not
find, because both are about what the header *declares but never allocates* and what a second
tool would have to recompute:

* **Decision 1 was half-implemented.**  `pooled_types = [cmd; frame]` made those two types
  handles into a node pool, and `node_layer` emitted the node struct — but nothing registered
  `jpl_cmd_pool`/`jpl_frame_pool`, so the vendored header's 6 `extern` pools dimensioned the
  word slab and five *list* pools and allocated **no cells for either node kind**.  A JPL.7
  host would have linked, and the lowering pass would have had nowhere to put a `cmd`.  Fixed
  by making `pool_cap` return `(cells, cap macro, why)` and having the *same rule that emits
  the struct* register the pool, so the two cannot drift apart again; `named_layer` now
  refuses a name in `pooled_types` that `pool_cap` does not size, because the previous
  fall-through silently chose the by-value fat layout for a type the decision calls pooled.
* **The reading lived in the wrong file.**  `of_ct` (the value-type view), the constant folder
  and the cap-table reader were sections of `jpl_emit.ml`, and 5-B.3 needs exactly those
  three.  They moved to `jpl_ast.ml` §8-§10 — the shared reader the front end already used —
  so the family is one reader with three consumers (`jpl_front.ml`, `jpl_emit.ml`, and the
  census `jpl_lower.ml`), and `jpl_emit.ml` went 1074 → 879 lines.  The move was checked the
  only way that means anything here: re-run the emitter and require the vendored bytes to be
  **identical**, which they were, so "same reading" is measured rather than claimed.

**Gate and evidence state after 5-B.2c.**  `verify_models.sh` **15/15** (still no new rung:
block 2e's four checks are unchanged in kind and the widened header is what check 2 compiles;
2e-negative still refuses the oracle roots with `a function-typed value has no layout`),
`JPL_REGEN=1 verify/c/jpl_emit.sh` re-pinned `sh_run_jpl.h` (**376** lines, 76 `typedef`s,
63 `#define`s, **8** dimensioned `extern` pools, **36** compile-time assertions) and
`layout.txt` (**118** lines, PENDING 5), bounded static total **34 049.0 KiB** with the two
new node pools contributing **448.0 KiB** (`jpl_cmd_pool` 8 192 × 16 B, `jpl_frame_pool`
16 384 × 20 B).  No Rocq file changed, so `coqc`/`coqchk`/parity/conformance keep #40's
numbers (8.6 s, four `<none>`, 66, 33/33); they are quoted as unchanged rather than re-run for
a tooling-only edit.

**Honest limits after 5-B.2c.**  (i) The two new pools inherit decision 3's headroom 2, so
they are *also* placeholders; 5-B.3a's census either justifies the factor or replaces it for
all eight pools at once.  (ii) `jpl_frame_pool` and `jpl_frame_list_pool` now both size
themselves by `MAX_STACK`, which is honest (§1.1 defines it as `max_stack_from_margin =
2 · max_cmd_from_margin`, pinned equal to the LOCKED literal by
`max_stack_from_margin_is_MAX_STACK`) but is the second pool a headroom change will double,
so the report prints both rows and the multiplication stays visible.  Reading those two rows
also turned up an obligation this section had never stated: **nothing in the model bounds the
machine's own stack length**.  `sh_jpl_run.v` §1 defines `stack := list frame` and `cfg.ck`
carries it, `sh_jpl_run_c.v` pushes onto it at every `enter_*`, and no lemma and no runtime
guard anywhere in L3–L8 compares `length ck` against `MAX_STACK` — the cap exists in the table
that sizes the pool, and the machine that fills it never checks.  That is the same debt family
as `MAX_WORDS`'s second `MAX_STACK` summand, named here rather than left for JPL.7 to discover
as a silent overwrite.  (iii) The
`pooled_types`/`pool_cap` cross-check catches a missing cap, not an unnecessary pooling claim:
a type that is pooled but never reached would still cost its pool — the census is where that
gets checked.

### JPL.5-B.3a / #41 — DONE (2026-10-05): the lowering census, and the day the plan's own numbers were wrong

The stage was scoped as a **measurement taken before any C body exists**, and it earned
that framing: the split this file quoted in four places retired itself, a soundness bug in
the census tool was found only after the two sections that consume it started agreeing, and
the census came back with a pool the header declares for no reason in the artifact.

**The measured split, which replaces the inherited one.**  Over roots `mrun_c,step_c`:
**47 members = 26 straight-line + 7 fuel tail loops + 4 fuel idioms that run one trip + 3
structural tail loops + 5 `BOUNDED FOLD`s (non-tail) + 2 operator aliases**.  The 17 the
front end reports as fixpoint-defined are exactly **7 + 3 + 5 + 2**, so the other 30 are the
non-recursive rows, and reading them is not noise: four cap constants the closure mentions
(`mAX_WORD`, `mAX_LIST`, `gLOB_FUEL`, `mAX_FUEL` — and **no** row for the other six, which
the machine never reads), the word-level predicates (`is_digit`, `is_alpha`, `is_name`,
`isz`, `b_dollar` … `b_0`), the step driver and its two helpers (`step_c`, `step_cmd_c`,
`step_ret_c` — all three non-recursive, which is what L3's "no recursion in the machine"
claim looks like from the artifact's side), and one straight-line wrapper (`expand_it`, whose
loop is `expand_go`).

Three claims retired, all of them quoted from §9.1's 5-B.1 row: *"6 fuel-bounded tail loops +
2 print-only aliases + 9 length-bounded structural recursions"*.  There are **7** fuel loops,
not 6, and the extra one comes out of the 9: `nat_digits` sits in both 5-A.7's and 5-B.1's
list of nine structural recursions, and the artifact's own text makes it a fuel-fed tail
loop.  The remaining 8 do **not** measure as 8 copy-loop rewrites: **3** are structural tail
loops the `while` handles directly (`teqb`, `getv`, `rev_append`) and **5** are non-tail
folds —
`length`, `app`, `rev`, `forallb`, `branch_need` — for which no `while` exists at any budget,
because D-60411 forbids recursion.  So the sentence "9 bounded recursions → bounded copy
loops" described work for 3 bindings and mis-described 5; §6.3 is now the normative list, and
the distinction only exists if a per-binding classification is done, which is why this stage
was scoped before the emitter.  A second consequence of the same measurement: the two
properties the estimate had merged are now separated in both directions — **4 of
the 5 non-tail folds** (`length`, `app`, `rev`, `forallb`) are polymorphic in the interface
while `branch_need` is not, and the fifth of the census's polymorphic set, `rev_append`, is a
**structural tail loop**, so it needs an instance but no rewrite.  "Monomorphize the
polymorphic helpers" is therefore not one job, and neither is "lower the recursions to
loops": the two sets overlap in four names and each has one member the other lacks.

**The four one-trip fuel idioms are a class the estimate could not have produced.**
`nat2text`, `enter_seq`, `enter_for_c`, `step_cmd_c` each contain the
`ExtrOcamlNatInt` nat-destruct value `(fun fO fS n -> if n=0 then fO () else fS (n-1))`, but
their step binder never calls the enclosing binding, so the idiom evaluates **one** trip and
lowers to `if (n == 0)` — not a loop.  `nat2text`'s step binder is *unnamed*, so the
decremented fuel is discarded; JPL.6's Rule-6 lint must not read either shape as recursion,
which is why `jpl_lower.ml` classifies them apart from the seven real loops instead of
counting 11 "fuel" bindings.

**A soundness bug in the census, found by the section that was supposed to agree with it.**
The R8 instance set pushes each binding's declared interface *freshened* down into its body
and resolves every call site against it.  The first version pushed the `.mli`'s **unfreshened**
`'a1` into the global type store.  Because `resolve` follows the store, all five polymorphic
bindings then shared one store entry, four "open instances" printed the *same* variable name,
and the instance set measured nothing except whichever binding the walk inferred last — the
`'iv38` that started this thread.  The fix instantiates one fresh set of variables per
binding; the numbers moved from a set that looked self-consistent (and passed) to
**29 use points → 6 closed + 6 open**, and the open ones became exactly the five self-uses of
a binding the interface itself declares polymorphic plus `app`'s tail use inside `rev`'s
parameter — i.e. the open set now has a *reason*.  The same fix exposed a second, quieter
inconsistency: lambda sites rendered their instance names as strings when recorded, while
the monomorphization section resolves them when printed, so a variable closed by a later
unification appeared under two different names in one report.  Recorded sites now carry
**types, not strings**, and one census has one reading of one store.

**Why the gate reads SUMMARY keys and not prose.**  The first draft of `jpl_lower.sh` scraped
the report's formatted tables instead: a pool list taken by an `awk` whose end-rule was a line
prefix, and an instance count anchored on a label that also appears per-binding.  Both failure
modes are *silent* — a scrape that stops early reports a smaller set than the artifact
contains, and a mis-anchored read reports a number that is in the file but not the one asked
for.  The shipped runner takes its inputs from the report's own **SUMMARY** keys (`key
function_value_sites_unnamed`, `key pools_demanded`, …), one line per key, each marked by the
section that measured it, and the census **refuses** if a key was never marked: an absent
measurement is not a zero.  Same reason 2e reads the emitter's own PENDING field rather than
counting `PENDING` lines — see the #39 entry's third gate-side bug.

**Cross-rung finding, reported as a finding.**  The census demands **7** pools; 5-B.2's header
declares **8**.  `jpl_frame_pool` is declared-not-demanded, and the reason is §6.2's decision
1 (which pools `frame` on the strength of §1's cap comment, not on a self-reference the
artifact shows — only `cmd` reaches itself).  Only the opposite direction would break a
build, so the gate fails on demand-without-declaration and prints the surplus with its
documented cause.  5-B.2c's defect was the same class pointing the other way — the header
*declared* pooled types whose node pools it never dimensioned — and that is why the check is
one-directional: an unused pool costs memory, a demanded pool that does not exist is a link
error in a stage nobody has scoped yet.

**Four checks the census makes against other rungs, none of them self-reports.**  (i) Its
member count and recursive count (`jpl_front.sh`) — **47 / 17**, and `closure.txt` line 52
prints the same pair for the same roots, so the two tools now bind each other's inventory
rather than each trusting its own edge rule (5-A.7's row is the cautionary case: it recorded
**45** for the same roots and the error survived three stages of being quoted).  (ii) Its
pools against the **header's** (`jpl_emit.sh`): `pools_demanded ≥ 5` and every emitted
`JPL_POOL_<KIND>` macro named by `lowering.txt`, the emitter-to-census direction — a pool
with no demand is a finding, and (iii) is the census-to-emitter one, where demand with no
declaration would break a build.  (iv) Its own per-binding self-call counts against the
**shared reader's** second reading of the same bytes, for all 47 members
(`self_reference_mismatches = 0`).

**Gate and evidence state after 5-B.3a.**  `verify_models.sh` **15/15 → 17/17**: block **2f**
builds `jpl_ast.ml` + `jpl_lower.ml` in a `mktemp -d`, runs them over the bytes block 2c
vendored, asserts the SUMMARY is complete, asserts the three zeros the report claims
(`function_value_sites_unnamed`, `unknown_site_classes`, `self_reference_mismatches`), runs the
pool demand cross-check against `sh_run_jpl.h`, byte-compares the vendored evidence, and then
**prints** the SCHEMA CENSUS, the R8 closed/open counts and "WHAT THIS CENSUS CANNOT ANSWER"
out of that evidence — so the gate's own output restates no number.  Block **2f-negative**
points the same tool at the oracle roots `run,step,mrun` and requires the **third independent
refusal reason**: `LOWER REFUSAL: no lowering schema exists for this root set.` followed by
`mutual fixpoint: … expand, expand_name, expand_brace, run, run_seq, run_for, run_case`
(38 bindings, 17 of them recursive), distinct from 2d's subset violation and 2e's
function-typed layout refusal.  New files: `verify/c/jpl_lower.ml`, `verify/c/jpl_lower.sh`,
vendored `verify/c/lowering.txt` (418 lines, byte-compared, `JPL_REGEN=1` to re-pin).  *[Re-pinned
the same day by **5-B.3b-i** at 507 lines / 24 SUMMARY keys, with `verify/c/sh_run_jpl_abi.h`
added beside it and block 2f's checks 4–5 added to gate them; the four checks described here are
unchanged in kind.]*  No Rocq
file changed, so `coqc`/`coqchk`/parity/conformance keep #40's numbers (8.6 s, four `<none>`,
66, 33/33); the emitter rungs are toolchain-only, and the two older ones re-passed on the same
bytes with their own evidence files unchanged.

**Honest limits after 5-B.3a.**  (i) **This is still not a program**: no C body is emitted,
nothing here met JPL.6's shall-rules for function bodies, and the emitted-behaviour rung
stays D9/#26/#27.  (ii) **Sites are not extent** — §6.2's decision 4 — so the headroom factor
2 is unchanged for all eight pools, with one owner left: JPL.7's measured per-step
high-water mark.  (iii) The census inherits the artifact's type aliases (`text = int list`),
so a cons of `text` prints as a demand on `jpl_word_pool` rather than on a `text` list pool;
that is §6's R2 (`text` is the inline leaf) read through the artifact's own alias, not a third
reading, and the pool table's header says which way each row is counted.  (iv) **Nothing in
the shipped code bounds the machine's stack depth** (0 bound checks consult `MAX_STACK`), and
the frame pool exists because L3 counted frames; that debt is now measured rather than
suspected, and 5-B.3b must either emit a saturating depth check or the model must prove the
bound the pool size already assumes — census **obligation 3**, whose text the report prints in
full.  (v) Five bindings are a **model-side rewrite obligation**, not an emitter job: if
5-B.3b lowers them by inventing accumulator forms in OCaml, it has become a second model of
the kernel.

### JPL.5-B.3b-i / #41 — DONE (2026-10-05): the closed instance set rendered as a C ABI header

The previous entry's "next" line asked for four things at once — the ABI, the loop bodies, the
collection decision, the depth guard.  Taking the ABI first is not a preference: it is the only
one of the four whose input the census already measured *completely*, and it is the rung that
turns §6's R1–R8 from a layout the header states into a callable surface.  So 5-B.3b was split,
and **-i is declarations and nothing else** — no body, no statement, no collection, no depth
guard.  What landed is `verify/c/sh_run_jpl_abi.h`, generated by the same census over the same
bytes, plus six new SUMMARY keys and two new gate checks.

**The rendering, and the one instance that refuses it.**  6 closed instances → **5** prototypes
and **1** refusal.  The prototypes are `jpl_length_1/2`, `jpl_rev_1`, `jpl_rev_append_1/2`; the
first three carry `/* declaration only: no body until the §6.3 rewrite for this schema lands */`,
which is §6.3's `BOUNDED FOLD` row being obeyed rather than described.  The refusal is
`jpl_forallb_1`: at its single call site (`branch_guardb`, `sh_run_c.ml:4832`) `forallb` closes
to `(text -> bool) -> text list -> bool`, so its parameter 1 is *function-typed*, no C type
names it, and the only C thing that could is the function pointer D-60411 forbids.  The header
prints a `/* NOT EMITTED — … */` comment instead of a prototype, and the gate **prints this and
does not fail on it**, because `forallb` is already one of §6.3's five rewrite obligations: the
assertion is not "no refusals", it is `abi_blocked_outside_fold_set = 0` — a refusal §6.3
assigns to *no* owner is the failure, because that is the case with nobody to fix it.

**One value-naming rule, now used by both headers.**  The ABI's parameter and result types come
from `jpl_ast.ml`'s `value_name` (`L_word → jpl_wref`, otherwise `jpl_ ^ tn t`), and `jpl_emit.ml`
was changed to call the same function where it previously hard-coded the string `"jpl_wref"`.
That is the whole of the shared-rule claim, and it needed the shared *reader* rather than a
shared convention: `jpl_ast.ml` also gained `has_fun`, the non-failing analogue of `has_var`,
because `tn` refuses a function type — which is right when choosing a typedef and wrong inside a
diagnostic that exists to explain that refusal.

**Two rungs, and the one whose teeth the other cannot substitute for.**  Check 4 makes the ABI
account for itself: `abi_instances == instances_closed`, `abi_prototypes + abi_refused_no_c_type
== abi_instances`, `abi_bodies_expressible + abi_bodies_owed == abi_prototypes`, then the same
three numbers counted *in the rendered file* (declaration lines, `NOT EMITTED` comments,
`declaration only` comments).  Check 5 compiles the pair — a translation unit that includes
`sh_run_jpl.h` then `sh_run_jpl_abi.h` — under exactly 2e's flags.  These are not redundant, and
the difference was measured rather than argued: a scratch build in which `value_name` returned
`jpl_wref_typo` for `L_word` left **all six ABI keys and every census count identical** and
failed only at the compiler (`unknown type name 'jpl_wref_typo'`).  A gate that only counted
would accept two headers that state two rules.

**The printer bug the ABI exposed, caught by reading its own output.**  `forallb`'s instance
printed as `text -> bool -> text list -> bool`, i.e. a three-argument *first-order* function —
precisely the distinction the refusal below it makes.  `pr_lt` flattened every arrow, and OCaml's
own printer parenthesises an arrow whose **left** operand is another arrow.  The rule is now one
line in the census's printer, and the report, the ABI header's comment block and the refusal text
all read `(text -> bool) -> text list -> bool`.  Nothing failed before the fix, which is the
point: a misleading type string in a diagnostic is a documentation defect the gate cannot see, so
it was found by *reading*, and it is recorded because the next refusal text a reader meets will be
written by someone who trusts the printer.

**The same audit applied to the tooling's own prose.**  Adding a third consumer had left the
ordinals lying: `jpl_ast.ml`'s header enumerates three (the front end, the layout emitter, the
lowering census), yet `jpl_emit.ml` called itself the third, `jpl_lower.ml` the fourth, `AXIOTACK.md`
D8 the fifth, and `verify_models.sh`'s `Covers:` entries the third and fourth — plus two comments
(`jpl_ast.ml`'s roots parameter, `jpl_front.sh`'s build-order note) still said "both/two consumers"
from before 5-B.3a existed.  All eight places (six ordinals plus the two "both/two consumers" notes)
now match the reader's own enumeration.  Re-running 2d/2e/2f after the edit left `closure.txt`,
`layout.txt`, `sh_run_jpl.h`, `lowering.txt` and `sh_run_jpl_abi.h` byte-identical, which is the
check that makes the correction safe: a tool's comment carries no measurement, and the gate proves
it rather than assuming it.

**Gate and evidence state after 5-B.3b-i.**  `verify_models.sh` stays **17/17** — no new rung,
block **2f** gained checks 4, 5 and the second half of 6, and its title now names both stages
(`Lowering census + ABI rendering (JPL.5-B.3a, 5-B.3b-i)`).  2f's SKIP condition now also
requires a C99 `cc`, because check 5 needs one; **2f-negative** gained a second assertion beyond
its refusal text: the census is handed an *output path*, so the oracle-roots run must leave both
vendored artifacts byte-identical (`cksum` before/after) — a refusal that wrote a half-rendered
header would corrupt the very evidence the positive rung compares against, and the renderer's
ordering (write only after a complete census) is now tested instead of trusted.  `lowering.txt`
**418 → 507 lines**, its SUMMARY **18 → 24 keys**; new vendored `verify/c/sh_run_jpl_abi.h`
(50 lines: 5 prototypes, 3 declaration-only comments, 1 refusal comment).  No Rocq file changed:
parity **66**, `conformance.sh` **33/33**, `coqchk` four `<none>` all still #40's, and blocks
2d/2e re-passed with `closure.txt` and `layout.txt` + `sh_run_jpl.h` **unchanged** — the ABI
consumes the layout, it does not modify it.

**Honest limits after 5-B.3b-i.**  (i) **Still not a program**: 5 prototypes and 0 bodies; the
declared functions are uncallable until 5-B.3b-ii emits them, and JPL.6's shall-rules for
function bodies are untouched.  (ii) **The ABI is only as wide as the closed set** — the 6 *open*
instances appear in the report and deliberately not in the header, which is the honest statement
of the situation: an open instance has no layout to name.  If a later root set closes them the
header grows and the vendored bytes re-pin, which is the intended failure mode rather than a
surprise.  (iii) **Check 5 proves resolvability, not correctness**: compiling a prototype says
every type name exists and no hidden conversion fires under `-Wconversion`; it says nothing about
whether a *body* would satisfy the declaration's contract, which is exactly the gap §6.3's rewrite
obligations own.  (iv) **The refusal is deferred, and it propagates to a binding the schema table calls
lowerable.**  `jpl_forallb_1`'s owner is §6.3's fold row, but its only shipped use is
`branch_guardb` (`sh_run_c.ml:4832`), which the schema census classifies **straight-line** —
and the argument that makes `forallb` un-nameable there is an *inline lambda*
(`fun p -> length p <= mAX_WORD`), not a named function.  So check 2's `0` and check 4's refusal
are statements about different things at the same site: the census could *position* the function
value (a known call site, one of the four places a lowering absorbs), while the ABI still cannot
*name* the callee instance it produces.  5-B.3b-ii therefore cannot emit `branch_guardb`'s body
until `forallb` is specialised model-side at that predicate — the 5-A pattern, a new bounded loop
with a proved agreement lemma — and `branch_guardb` is a §6.3 consequence the fold table does not
yet list as its own row.  (v) `value_name`'s `L_word` case is now load-bearing across two
headers, so the shared reader has grown a *naming* responsibility it did not have when only the
layout used it; the compile rung is what makes that safe, and removing it would silently undo the
one thing 5-B.3b-i proved.

Next: **5-B.3b-ii**, still under JPL.5 (#25) and #41 — the bodies: the 2 `rev_append` instances
at §6.3's structural-tail-loop schema, the fuel tail loops' `while (fuel > 0)` forms with the
fuel arriving as a parameter, the step-boundary copying collection decision 3 describes, and the
saturating stack-depth guard census obligation 3 names.  The 5 `BOUNDED FOLD` bindings and
`forallb`'s function-typed parameter stay model-side rewrites: if 5-B.3b-ii invents accumulator
forms in OCaml to fill them, it has become a second model of the kernel and must be refused here
instead.  Then JPL.6 (#26) lints the result and JPL.7 (#27) runs it against `/bin/sh`, replacing
headroom 2 with the measured high-water mark.

### JPL.5-B.3b-ii-a / #42 — DONE (2026-10-05): the renderability trial, the first four C bodies, and their differential

**The question is not §6.3's.**  A lowering schema says what *shape* a control flow has; a shape
is still not a statement.  Before any body is emitted, one more question is answerable from the
artifact's bytes and cannot be skipped: does this body need a **pool, an allocator, or a function
value**?  A `while` over a `text` walks handles the representation layer already owns, so a body
whose every construct is scalar can become C today; a body that builds a value can become nothing
until decision 3's step-boundary copying exists.  §6.4 is the normative list of the six verdicts,
and this stage is the first time any of them emitted C.

**The load-bearing design choice: the verdict IS the renderer's own trial result.**  The obvious
shape for this stage — a classifier that decides renderability, plus an emitter that renders what
the classifier approved — is §2's forbidden pattern: two models of one artifact, allowed to drift
apart, with the drift invisible because each side would print its own table.  So §6.4's licensed
scalar set is implemented **once** (`render_e`/`render_def`), and the census *runs it as a question*
over all 47 members: a body that renders becomes a `RENDER` row and a definition in the same pass,
and a body that does not is reported in the renderer's own refusal message, naming the pooled type,
the §6.3 schema, or the construct that stopped it.  Nothing in the report predicts the emitter.

**What landed.**  `verify/c/jpl_lower.ml` §8c (the trial: `base_verdict` for the rules that are not
the renderer's own, `pools_of` for both directions of the representation rule, `print_render` as a
fixpoint, the `DATA`-macro list, the partition table, the `ALIAS` finding) and §8d (the two
generated differential drivers, `write_bodies`, `c_sweep_arg`/`ml_sweep_arg`, the per-body
`EXHAUSTIVE`/`DIAGONAL` claim); `verify/c/jpl_lower.sh` checks 5–8; the C spelling rules
`c_fn`/`c_upper`/`data_macro`/`cap_data`/`cap_macro_of_data`/`is_cap_data` moved out of
`jpl_emit.ml` into `verify/c/jpl_ast.ml` §9, and the emitter's hand-typed list of seven cap
bindings became derived from the artifact's own table.  Three new vendored files:
`verify/c/sh_run_jpl_bodies.c` (49 lines, 4 definitions), `verify/c/jpl_bodies_diff.c` (20),
`verify/c/jpl_bodies_diff.ml` (14).  `lowering.txt` **507 → 659 lines**, SUMMARY **24 → 35 keys**;
`jpl_lower.ml` 2043 → 2667, `jpl_lower.sh` 330 → 558.

**Measured.**  The trial's partition is exact: **11 `DATA` + 2 `ALIAS` + 4 `RENDER` + 13
`OWED-REPRESENTATION` + 15 `OWED-SCHEMA` + 2 `OWED-CONSTRUCT` = 47**, `render_unaccounted = 0`.
The four rendered bodies are `bstat`, `is_digit`, `is_alpha`, `is_name` — two of them citing
`JPL_C_B_0` / `JPL_C_B_USCORE`, which the gate resolves against `sh_run_jpl.h`'s `#define` lines
(all 11 `DATA` names resolve), and all four compile with the ABI against the representation header
under `-std=c99 -Wall -Wextra -Wconversion -Wsign-conversion -pedantic -Werror`.  The differential
then runs the sweep: both drivers are **generated from the same rows**, built (the C half under 2e's
flags minus `-fsyntax-only`, the OCaml half against the vendored `sh_run_c.ml`), and executed —
**136 450 lines each, `cmp` identical**, `bodies_swept_exhaustive = 4`, `bodies_swept_diagonal = 0`,
and the swept fields take **5** distinct values across the domain, which is what stops the
agreement from being two constant transcripts agreeing for free.  Line counts are asserted against
the report's own `sweep_domain`, so no driver chooses the range it is tested over.

**What the trial's own shape taught, recorded because each was a bug in the tool rather than in the
model.**  (i) The trial must be a **fixpoint**, and one artifact row proves it: `is_name` cites a
`DATA` macro *and* calls `is_alpha`/`is_digit`, so it is undecided until its callees are verdicted —
the first draft let the "callee not verdicted yet" case escape as an exception and would have crashed
the pass, which is why it now leaves the row undecided for the next pass instead of refusing it.
(ii) **The rules are tried in dependency order**, and the draft documented the wrong witness: §6.4
originally named `teqb` as the binding that reads a slab without consing anything, but `teqb`'s
schema is a fuel loop and `OWED-SCHEMA` fires before the representation rule is consulted.  The true
witnesses are `raw_bword` and `expand_c`, straight-line, consing nothing, still taking or returning
a word slab — which is why `pools_of` reads the *signature* as well as the allocation sites.
(iii) A generated `printf` that joins its arguments with `" "` instead of `", "` still compiles: the
format string then consumes one argument for all its fields, and the transcript would have been
136 450 near-identical lines that `cmp` happily approved.  (iv) Symmetrically, the OCaml half needs
every application parenthesised, or `Printf.printf fmt i Sh_run_c.bstat i …` parses as six arguments
and the driver does not typecheck.  (v) The gate's `key()` reader matched a verdict label both in the
partition table and in the SUMMARY, so the first run failed on a value of `0\n0`; the reader is now
anchored to the SUMMARY section, the one place the census reserves for machine-readable keys.
(vi) `cp "$ML" "$MLI" .` inside a `( cd "$BUILD" && … )` subshell resolved the repo-relative artifact
path against the scratch directory — an input a gate reads must be named from the repo root, not from
wherever the shell happens to be.  (vii) The non-triviality guard first counted *distinct lines*,
which is vacuous: field 1 is the fuel index and varies by construction, so 136 450 copies of one
constant body would have passed it.  Dropping the first field makes the guard measure the swept
values, the only thing worth guarding.  (viii) Two OCaml-side traps: `Pexp_switch` is not a
constructor of `Parsetree.expression_desc` in 5.5.1 (the pattern forms are `Pexp_match`/`Pexp_or`),
and with `self : int ref` inside a record, `!record.self` parses as `(!record).self` — the
dereference needs the field parenthesised.

**Why the refactor's check is byte-identity, not a new assertion.**  Moving the naming rules into the
shared reader changes who *owns* a rule, not the rule, so the test is that nothing re-pinned: blocks
2d and 2e were re-run and `closure.txt`, `layout.txt` and `sh_run_jpl.h` came out unchanged, and the
emitter's cap list — now derived from `jpl_caps_table` instead of typed out — still emits the same
seven `#define`s.  A refactor that silently altered one emitted name would surface as a stale vendored
artifact, which is the failure mode the byte-compare exists for.

**Gate and evidence state after 5-B.3b-ii-a.**  `verify_models.sh` stays **17/17**, exit 0, with no
new rung: 2f's own script grew from six checks to eight, so the extra coverage lives inside block 2f.
What did change in the runner is the negative control's immutability set — the census is handed
**five** output paths now, and `cksum` silently skips a file it cannot open, so 2f-negative asserts
the count is five before it asserts the bytes are unchanged, because a refused run that left the two
older artifacts alone while rewriting the bodies file or a driver would otherwise read as a pass.
Verified by hand as well: `JPL_ROOTS=run,step,mrun ./jpl_lower.sh` exits 1, refuses with `mutual
fixpoint`, and leaves all five vendored files byte-identical.

**Honest limits after 5-B.3b-ii-a.**  (i) **Still not a program** — 4 bodies out of 47 members, none
of them the machine; the differential proves the renderer agrees with the kernel about four scalar
leaves, which is a real rung and a small one.  (ii) **The two transcripts agree as decimal text**,
which is sound only because every swept value is a `nat` below 2^31 (the domain tops out at
`MAX_FUEL` = 136 449) while the C prints `%u` and the OCaml `%d`; a rendered body that could return
≥ 2^31 would need the drivers' formats re-examined, and the assumption belongs in the plan rather
than buried in a format string.  (iii) **Nothing here measures extent**: a scalar body allocates
nothing, so §6.2's headroom factor 2 stays the placeholder decision 4 left it as, and the 13
`OWED-REPRESENTATION` rows are precisely the bindings that will pay for it.  (iv) **The `ALIAS`
finding is unresolved and belongs to two sections**: `jpl_add`/`jpl_mul` are declared in 2e's header
and defined nowhere, and §6.4 refuses to define them because their body IS a C operator; the fix is
either dropping those prototypes in 2e or having JPL.6's lint forbid the by-name call.  (v) The
`RENDER` verdict is *sufficient*, not necessary: a body that needs a pool is not unrenderable forever,
so the 13 and 15 counts mark this stage's own boundary, and 5-B.3b-ii-b is expected to convert them
rather than confirm them.

Next: **5-B.3b-ii-b**, still under JPL.5 (#25) and #41 — the loop and pool half: the 2 `rev_append`
instances at §6.3's structural-tail-loop schema, the 7 fuel tail loops' `while (fuel > 0)` forms with
the fuel arriving as a parameter, decision 3's step-boundary copying (which turns 13
`OWED-REPRESENTATION` rows into renderable ones), the saturating `MAX_STACK` depth guard census
obligation 3 names, and `branch_guardb`/`forallb`'s model-side specialisation.  The 5 `BOUNDED FOLD`
bindings stay model-side rewrites: if that stage invents accumulator forms in OCaml to fill them, it
has become a second model of the kernel and must be refused here instead.  Then JPL.6 (#26) lints the
result — including whichever answer the `ALIAS` finding gets — and JPL.7 (#27) runs it against
`/bin/sh`, replacing headroom 2 with the measured high-water mark.

### JPL.5-B.3b-ii-b-0 / #41 — DONE (2026-10-05): the second debt, and the slice order a column forced

**What opened the slice.**  5-B.3b-ii-b was scoped as "the loops and the pools", and the first
thing needed from it was a *sequence*: 15 members wait on §6.3's shape and 13 wait on decision
3.  Reading the vendored `lowering.txt` cannot say whether those sets overlap, because §6.4's
rule order gives one row one owner and the schema rule fires first — so the report prints an
`OWED-SCHEMA` row's §6.3 class and never mentions a single pool that row's own signature takes
or returns.  The overlap is what the ordering depends on (a `while` over pool handles is not
writable without the allocator), and it was not in the evidence.  The honest move was to
measure it before choosing, which is what this slice is: **a census column and a spec section,
with no licence attached**.

**The design choice.**  Two ways to get the overlap: promote `OWED-REPRESENTATION` above
`OWED-SCHEMA` — which would relabel 15 rows and move obligations §6.3 owns into a section that
does not own them — or keep the verdict and print the *second* debt beside it.  The second was
taken, and the reading it uses is not a new one: the same `pool_of` walk the renderability
trial consults, asked of every member instead of only of the rule that won.  One reading, two
columns, so §2's forbidden second model of the artifact stays forbidden, and a row cannot
report here a pool the trial declined to look at.

**What the measure has to say about "no pool".**  A zero from this walk is not freedom, and the
column therefore carries a *reason*: a genuinely scalar signature, a list-shaped position whose
element is still a **type variable**, or a position behind a **declared record or variant** whose
fields the walk does not enter.  Conflating them is how a measurement becomes a licence.  The
variable family got one more check on top, because it is the one that lies prettiest: a binding
whose interface says `'a list` has no cell in this walk, while §6.3's instance set may already
have closed that `'a` at a call site and `sh_run_jpl_abi.h` may already name the pool — so the
census re-reads its own ABI rows and counts the rows that are pool-free here and pooled there.

**What landed.**  `verify/c/jpl_lower.ml` §9e: `sight`/`sight_of` (the walk, both directions),
`opaque_ty`, `shape_debt` (the §6.3 debt read from the printed class *names*, not from a prefix —
see the lesson below), `instance_pools` (the ABI cross-check), `print_debts` (the table, the two
debt columns, the reason column, the dual rows, the ABI reading, the floor wording, the refusal
if a verdict is unexplained) and **9 new SUMMARY keys**; `verify/c/jpl_lower.sh` check 5 grew five
identities, one inequality and the printed slice finding; JPL.md gained **§6.5** (the rule, the
three-reason table, the slice table with owners, the floor wording) before any of the code was
written, plus a corrected §6.4 sentence and the §9.1/§9.2/state rows.

**Measured** (all of it re-pinned, `lowering.txt` **659 → 783 lines**, SUMMARY **35 → 44 keys**,
and **no verdict count moved by one**, which is the check that this measured rather than
re-classified): **10** of the 15 §6.3-shape rows also touch a pool — every one of them reaching
`jpl_word_pool`; the remaining **5** are pool-free *all five* by type variable
(`length`, `app`, `rev`, `rev_append`, `forallb`), **0** by the opaque-record boundary and **0**
in the plain scalar sense; **4 of those 5** are POOLED at a closed instance (`length` →
`jpl_text_list_pool` + `jpl_word_pool`, `rev`/`forallb` → `jpl_word_pool`, `rev_append` → both)
and only `app` is never closed anywhere in the shipped closure.  `owed_construct_also_pool = 0`,
`dual_debt_rows = 10`, refused-rows-touching-a-pool = **23** = 10 + 0 + 13, `debt_unaccounted = 0`.

**The scoping guess was wrong, twice, and the measurement is what caught it.**  The hand-read of
the `.mli` that opened this slice claimed *all 15* schema rows touch a pool; the walk says 10,
and the other 5 are polymorphic rather than free.  The same hand-read predicted `mrun_c` would
fall in the opaque family because its parameter is the declared type `cfg`; the walk puts it in
the dual set, because `enter_case_c`'s `stack` position unfolds through the artifact's own alias
`stack = frame list` into `jpl_frame_list_pool`.  Both corrections came from running the reading
instead of reasoning about it, which is the whole reason this slice exists before any slice that
emits code.  And the answer the slice was created to get is now printed: **`while` statement
forms, landed alone, render zero bodies** — `owed_schema_pool_free_scalar = 0` — so ii-b-1 and
ii-b-2 precede ii-b-3 and ii-b-4 by measurement.

**Tool lessons.**  (i) §6.4's schema test contained `starts cls "FUEL LOOP"` while the census
prints the class as `fuel tail loop`: the condition had never matched anything, and the rows it
was meant to catch fired `OWED-SCHEMA` anyway because each carries a self-call.  Silent for two
stages, and a trap for the next one — a fuel tail loop with `self = 0` would have been verdicted
renderable by a rule that thought it was refusing it.  `shape_debt` now names the printed classes
exactly, and `debt_unaccounted` is the assertion that the two readings still agree, so the fix is
checked rather than trusted.  (ii) The first draft of `dual_debt_rows` counted *refused rows that
touch a pool* (23), which is not "rows carrying both debts" (10) — the number and its gloss
disagreed until the printed identity 10 + 0 + 13 = 23 forced the distinction.  (iii) `Edit`
splices into a 2 900-line OCaml file leave residue: an unused local, a duplicated `mark`, a
`let … in in` that does not parse, and a section marker eaten by the replacement text.  Each was
caught by the compiler or by `grep -n` over the spliced region rather than by reading the diff,
which is the argument for building before running.

**Gate and evidence state after 5-B.3b-ii-b-0.**  `verify_models.sh` stays **17/17**, exit 0: no
new rung, and no edit to the runner — 2f's check 5 covers the new keys, so this stage lives
entirely inside block 2f.  All **five** vendored artifacts re-pinned with `JPL_REGEN=1` and
byte-identical on the following clean run (`lowering.txt` is the only one that changed; the ABI
header, the bodies TU and both drivers are untouched, which is what "no verdict changed, no body
emitted" looks like in the evidence).  2f-negative still refuses oracle roots and still leaves all
five alone.

**Honest limits after 5-B.3b-ii-b-0.**  (i) **Every pool-free count is a floor**: the walk stops
at a declared record or variant, so `isz` sits behind `cstate` and `step_c` behind `cfg`/`out`
and prints no cell although their fields are the machine's state.  Entering those fields would
move rows between §6.4's verdicts — a reader change, so a slice of its own, and §6.5 says so in
print.  (ii) The column still does not measure **extent**: a pool touch says a cell type is
involved, not how many are live at a step boundary, which stays decision 4's and JPL.7's number.
(iii) `dual_debt_rows` reads the class table for its shape debt, so it is a measurement of the
census's own classification, not an independent witness — its independence comes from
`self_reference_mismatches = 0`, which is the other walk.  (iv) A measurement rung emits no code,
so nothing here narrows the 43 members with no C body; the number that moved is the number of
*reasons* known about them.

Next: **5-B.3b-ii-b-1**, the pool **allocator and handle runtime** (bounded free-cell allocation
per declared pool, handle types, saturate-to-error on exhaustion) under JPL.5 (#25) and #41 — the
slice §6.5's ordering now puts first, because 13 `OWED-REPRESENTATION` rows need it outright and
10 of the 15 `OWED-SCHEMA` rows need it before any `while` can be written for them.  Then
ii-b-2 (decision 3's step-boundary copying), ii-b-3/4 (the two loop forms), ii-b-5 (`MAX_STACK`'s
depth guard), ii-b-6 (the 5 model-side `BOUNDED FOLD` rewrites plus `branch_guardb`/`forallb`).
Headroom 2 is not this slice's either: nothing has been emitted that allocates, so decision 4's
placeholder still has no measured replacement to become.

### JPL.5-B.3b-ii-b-1 / #41 — DONE (2026-10-05): the pool runtime, and why reclamation is a region

**What opened the slice.**  §6.5 measured that no `while` form lands a body on its own, and named
ii-b-1 as the first half of the reason: `sh_run_jpl.h` declared eight pools `extern` and promised
"definitions live in the emitted translation unit" — a unit nothing in the tree wrote.  So a
handle was a `uint32_t` with a comment behind it, and the 13 `OWED-REPRESENTATION` rows were stuck
on something smaller than a body: no operation in the emitted C could make a cell exist, or fail
to make one exist loudly.

**The design choice: a region, not a free list.**  §6.5's own wording for this slice was "a
bounded **free-cell** allocator", and the first thing the slice did was drop that.  A `release(h)`
is only meaningful with a rule saying which handles still reach a cell, and that rule is
decision 3's step-boundary collection — ii-b-2's content, not ii-b-1's.  Shipping a free list
first would have meant a allocator whose safety argument lived in a later slice, which is the
invention §6.2 refuses.  So each pool is a **bump region** with `reset` as its only reclamation,
and the region boundary is the step boundary ii-b-2 will define: the design is not simpler, it is
*justified at the boundary it actually has*.  The cost is recorded rather than hidden — a reset
does not clear cells, and `is_live` catches the handle-carried-across-a-rewind case only, which is
exactly the aliasing ii-b-2 must forbid by copying survivors.  The payoff is decision 4's: `_peak`
makes "how wide does a region ever get" a measured quantity instead of an assumption baked into
headroom 2, and the gate prints today's honest value for the kernel, which is 0 because no body
allocates yet.

**The registry's missing column.**  Every name is derived from the pool record that already sizes
it — `pool_stem` strips `jpl_` and `_pool`, and the same stem gives `JPL_POOL_<KIND>` and the seven
runtime names — so the runtime cannot name a pool the layout did not declare.  One column was
missing from that record: `p_handle`.  In C every handle is a `uint32_t`, so the language cannot
tell a word handle from a cmd handle, and an allocator that returned `jpl_ref` for all eight would
be *type-correct and wrong*; the registry can, and now does, so `jpl_word_alloc` returns
`jpl_wref` and a handle whose typedef the layout never emitted is a refusal that exits 1.  Naming
also had to be checked for collision rather than assumed: §6.3's ABI header and §6.6's runtime land
in one translation unit, and `runtime_names_colliding_with_prototypes = 0` is the assertion that
they do not overlap.  A pool with no capacity gets no runtime either, which is the same rule read
backwards.

**What the gate now measures.**  2e went from four checks to seven, and the two new kinds are both
new *for this tree*.  First, a **definition** of a mutable static is compiled rather than parsed:
the pools TU goes through `-std=c99 -Wconversion -Wsign-conversion -Werror -pedantic` without
`-fsyntax-only`, so the bound comparison and the saturating counters are checked by a compiler
rather than by reading.  Second, the runtime is **driven**: a sweep per pool, generated from the
header's own `jpl_<stem>_alloc(void);` lines and bounded by that pool's own `JPL_POOL_<KIND>`
macro, so it adds no number to the tree and cannot quietly test a different capacity than the one
shipped.  It reaches each region's edge and asserts `served == C-1`, distinctness, liveness before
and death after a reset, that an exhausted region moves nothing, and that the cumulative counters
survive the rewind — the last because they are instruments, not part of the region.  Then the 13
`RUNTIME SUMMARY` keys close against each other, against the header, against the TU and against the
sweep's own line count, with the report's table of stems and macros `diff`ed against the header's
declarations: three readings of one registry.

**A tooling trap worth recording.**  The emitter builds C text with OCaml string continuations, and
that idiom is a loaded gun here.  `"…empty \` / `· \ region */"` does not emit `empty \ region`:
the newline and the indentation are skipped, so the second backslash begins an *escape*, and `\ `
contributes a space — one more than intended, hence the doubled spaces in the emitted comments.
Worse, `\region`, `\full`, `\started` are `\r`, `\f`, `\s`-like escapes, so the emitted C carried
**carriage returns and form feeds inside comments** while still compiling clean: the compiler did
not catch it and neither did `-Werror`.  The fix is one rule — no space before the line-ending
backslash, and always a space after the continuation's backslash — now applied at 11 sites, and
the gate's byte-comparison pin is what keeps it applied.  The lesson generalises to this tree:
**an emitted comment is unverified text**, so anything load-bearing belongs in a `typedef char
jpl_check_…[…]`, which is a compile error when it is wrong.

**Gate and evidence state after 5-B.3b-ii-b-1.**  `verify_models.sh` stays **17/17**, exit 0, with
**no edit to the runner**: all three new rungs live inside `verify/c/jpl_emit.sh`, which block 2e
already calls.  The vendored pin count for this layer goes from two files to three — `sh_run_jpl.h`
(376 → 477 lines), `layout.txt`, and the new `sh_run_jpl_pools.c` (363) — and all three are
byte-identical on the clean run after `JPL_REGEN=1`.  2f is the cross-rung witness that nothing
invented a pool: its declared-pool grep (`jpl_…pool[`) still returns **eight**, all five of its
artifacts stayed byte-identical, and its own nine PASS lines are unchanged, including the
exhaustive 136 450-line differential against the kernel.  2e-negative still refuses the oracle
roots for the same documented reason.  The rung's teeth were verified the way 2d/2f's were: one
character of the emitted comparison (`next < C` → `next <= C`) turned the sweep red with five
distinct failures and a non-zero exit before the mutation was reverted; the emitter source was then
confirmed byte-identical to its pre-mutation copy.

**Honest limits after 5-B.3b-ii-b-1.**  (i) **No body exists that this runtime serves**: §6.4's four
scalar-leaf definitions are unchanged and none of them allocates, so `0` of the 43 open rows moved,
and 13 `OWED-REPRESENTATION` rows still owe the *copying* half.  (ii) Every `peak` attributable to
the kernel is **0**, so decision 4's quantity has an instrument and not yet a reading; headroom 2
is untested and stays a placeholder.  (iii) **Unsized pools: 0**, so the "no capacity ⇒ no runtime"
half of §6.6's rule is held in reserve by the gate rather than exercised.  (iv) The runtime is a
**single-thread** claim and a C-level one: the Coq model has no store, cell identity is
deliberately unmodelled, and no kernel theorem changed.  (v) `reset` not clearing cells means a
stale handle below the current `next` reads live — `is_live` is a guard rail, not a liveness
analysis, and ii-b-2's copy rule is what has to make that state unreachable.

Next: **5-B.3b-ii-b-2**, decision 3's **step-boundary copying** (values copied into pool cells at a
boundary, reads taking handles, survivors copied before the rewind) under JPL.5 (#25) and #41 — the
slice that converts "a cell exists" into "a body may return one", and the owner of the reachability
rule §6.6 declined to invent.  Then ii-b-3/4 (the two loop forms), ii-b-5 (`MAX_STACK`'s depth
guard), ii-b-6 (the 5 model-side `BOUNDED FOLD` rewrites plus `branch_guardb`/`forallb`).

### JPL.5-B.3b-ii-b-2a / #41 — DONE (2026-10-05): the edge table, and why a class belongs to a word

**What opened the slice.**  §6.6 made a cell exist and R7 made every one of its slots a
`uint32_t`, so §6.6's own debt note — "the aliasing a handle below the current `next` can still
produce is exactly what ii-b-2's copy rule must forbid" — had no vocabulary: "reachable from the
roots" named nothing, because a handle and a `nat` are one word and only the `.mli` knows which is
which.  The slice's job was therefore not to collect but to make a collector *possible*: a per-cell
statement, in data the compiler has seen, of what each word of each pooled cell may be forwarded to.

**The design choice: one class per word, not per declared field.**  R3 keeps a list's element
*inline* in the cell, so `jpl_pair_text_text_list_cell` is 12 bytes whose three words mean
length-word, element-handle, tail-handle.  A per-field table would need a second table saying how a
field splits, which is §2's forbidden second model of one artifact; flattening makes the cell's own
arithmetic the table instead, so the position list the layout rules already recorded while emitting
the structs *is* the edge table, and `NPOS × 4 == sizeof (cell)` becomes a `jpl_check_*` typedef per
pool — the compiler, not a comment, answering "does this row cover the struct?".  Three classes are
published (`JPL_EDGE_SCALAR`, `JPL_EDGE_UNUSED`, `JPL_EDGE_TO_<stem>_POOL = 3 + sorted-stem-index`)
and the target set is *derived* from the pool registry, so an edge that names no pool and a pool no
edge can name are both impossible by construction rather than by check.

**The array field, found the slow way.**  The first draft wrote the word slab's row as an
unquestioned fill — 257 `SCALAR` words under a comment claiming the emitter never asks what a leaf
cell's words are — while §6.7 claimed the emitter "refuses one rather than guessing".  Those two
sentences described different programs, and the honest fix was not the comment: the position type
gained `P_leaf of lt`, the word slab's shape now records `{ len; code[MAX_WORD] }` as
`[P_lt L_nat; P_leaf L_nat]`, and `edge_row` computes an array's element count from the words its row
leaves rather than from any declaration, because that count is the one number the `.mli` does not
state.  Two refusals came with it — an element whose classes do not *divide* the remaining words, and
an untagged row that does not fill its cell — both because the alternative is a table that stops short
and a collector that never scans the last words of a cell, i.e. a live cell freed.  Padding is legal
on a *constructor* row (it is that constructor's arity) and illegal on a cell's own row, where it
would hide a field this reading never walked.  The slab's all-scalar reading is now derived, not
excepted, and its emitted gloss is computed from the classes rather than typed.

**What the gate now measures.**  2e grew from seven checks to eight, and check 7 is four readings
meeting with no shared input: the header's constructor comments (its rows, and its widest arity as tag
+ slots), the initialiser tokens in the pools TU (one class name per word, every entry naming its
class), the `.mli`'s own alternatives with **parenthesis depth counted** — so
`Case of text * (text list * cmd list) list` answers two slots where a naive `*` count answers three
— and the report's ten `EDGE SUMMARY` keys.  Two structural properties a collector depends on are
asserted directly: every node row's first word is SCALAR (a tag is a code, not a forwarding target)
and no `UNUSED` sits inside a row.  `edge_aggregates_flattened` was the rung's last literal and is
now a derivation: the gate counts the pools whose cell is named `jpl_pair_*`, requires each to be
three words wide and every other non-node pool not to be, so §6.7's "a cons cell's element pair is
the only aggregate a pooled cell holds by value" is measured against the type layer's own names.

**Measured.**  8 tables / 26 rows / 358 word classes = **286 SCALAR + 27 UNUSED + 45 EDGE**, partition
residual 0; `cmd` 11 rows × 4 words = 12/12/20, `frame` 9 × 5 = 17/15/13, the three 2-word cons cells
0/0/2 each, the two 3-word pair cons cells 0/0/3, the word slab 1 × 257 all scalar; 8 edge targets ==
8 declared pools in both directions; `edge_width_checks_emitted == 8`.  `sh_run_jpl.h` **477 → 557**
lines, `sh_run_jpl_pools.c` **363 → 487**, `layout.txt` 185 of which 31 are the edge blocks,
`jpl_emit.sh` 784 lines.

**The rung has teeth, twice, by two readings that do not see each other.**  Retagging a node row's
first word (`P_tag → [E_edge "cmd"]`) left checks 1–6 green, still compiled under the full flag set,
and kept the partition closed — the table was well-formed, within the cell's width, and self-consistent
with the report — and check 7 answered with **20** `TAGWORD` failures and exit 1.  Reclassifying
padding as a value (`E_unused → E_scalar`) moved *every* report key along with the file, so no
self-consistency identity broke; it was caught only because the `.mli`'s arities predict `cmd` 12 and
`frame` 15 UNUSED words against a measured 0.  Both mutations were reverted, and the emitter source
confirmed byte-identical to its pre-mutation copy, before the evidence was re-pinned.

**Gate and evidence state after 5-B.3b-ii-b-2a.**  `verify_models.sh` is **17/17**, exit 0, with **no
edit to the runner**: the new rung lives inside `verify/c/jpl_emit.sh`, which block 2e already calls.
The two new arrays are `jpl_<stem>_edge[]`, not `jpl_<stem>_pool[…]`, so 2f's declared-pool grep still
returns **eight** and all five of its artifacts stayed byte-identical — including the exhaustive
136 450-line differential.  2e-negative still refuses the oracle roots for the function-typed-value
reason.  Re-pinning after the `P_leaf` derivation changed **two comment lines and no number**, which
is what a derivation that replaces a fill should look like.

**Honest limits after 5-B.3b-ii-b-2a.**  (i) This is a **data dependency, not a collector**: no
`origin` array, no two intervals, the registered capacities are still §6.6's `2·cap`, and nothing reads
a table yet — the 45 EDGE words are what a collector *will* follow, not a reachability claim.  (ii) The
six edge-layer refusals have **no rung that fires them** at these roots; a `.mli` that put an `option`
inline in a pooled cell would, so that code is read rather than measured — the same reserve §6.6's "no
capacity ⇒ no runtime" half sits in.  (iii) The row index is a *tag value* and no emitted body computes
one, so `NROWS`/`NPOS` are dimensions of a table rather than of a walk.  (iv) `UNUSED` pads a
constructor's shorter arity, so a collector that skips it is right only because the tag selected the
row — that dependency is ii-b-2c's copy rule, not this table's.  (v) The word slab's behaviour, "copy
the cell in full and follow nothing", is a consequence of its classes; the rung that shows it is
ii-b-2e's probe.

Next: **ii-b-2b**, the two intervals — per pool the capacity becoming `2·cap + 2`, the from/to bounds
derived from it, the `origin` array, and `is_live` re-expressed as "in the current interval and below
the current allocation pointer".  ii-b-2a gave "live" a referent; ii-b-2b is the rung that proves
§6.6's aliasing debt is a *comparison* rather than an analysis.  Then ii-b-2c (evacuate one cell),
ii-b-2d (roots, `jpl_collect()`, the swap, `BLimit`), ii-b-2e (the driven collector's gate), then
ii-b-3/4 (the two loop forms), ii-b-5 (`MAX_STACK`'s depth guard), ii-b-6 (the 5 model-side
`BOUNDED FOLD` rewrites plus `branch_guardb`/`forallb`).

### JPL.5-B.3b-ii-b-2b / #41 — DONE (2026-10-06): the two intervals, and the comparison staleness needed

**What opened the slice.**  After 2a the runtime could name the 45 words a collector must follow, and
still had nowhere to copy a cell *to*: §6.6's array was one region with one reserved index 0, so there
was no to-space, no `origin` for a forwarded handle to live in, and no second interval for `is_live`
to be *about*.  That last absence is the reason the swap belongs to this slice rather than to ii-b-2d,
which is its first caller: with one region, `h < next` and "inside the current interval and below
`next`" answer identically for every value of `h`, so §6.7's design item (iii) — a stale handle must
read dead *while sitting below the current `next`* — is not merely untested there, it is
**inexpressible**.  A slice that lands a comparison nobody can falsify is a slice that lands a comment.

**The three choices the slice makes.**  (i) **One array, two intervals**, dimension
`SPACES·(cap+1)` = `2·cap+2`, because §6.6's "a pool of `C` indices serves `C-1`" is a *per-region*
law: a capacity of `2·cap` would have served `cap-1` live cells, one fewer than the artifact's cap,
and the shortfall would have surfaced at runtime as a `BLimit` the model does not produce.  Each space
reserves its own index 0, so the two indices that name no cell are `0` and `cap+1`.  (ii) **One
indicator for the whole graph**: `jpl_pools_space` is a single global whose single writer is
`jpl_pools_swap()`, not eight per-pool flags — every pool moves together at a step boundary, so eight
flags are eight chances to disagree about a fact that has one cause.  (iii) **Handles stay absolute**,
which is what buys the origin array its domain (one array per pool, indexed by the handle, sized by the
same `JPL_POOL_<KIND>` as the pool so the two cannot drift) and staleness its one comparison.  The
**scan pointer is deliberately absent**: it is the to-space's queue, so it belongs to the evacuation
that advances it (ii-b-2c), and emitting a counter nothing writes yet is the invention §6.2 refuses.

**The transient the swap creates, which no single-interval runtime has.**  A bare swap leaves every
pool's `next` an absolute index in the interval that was just *abandoned*.  Two consequences, and both
are now rungs rather than observations: an allocation into the new region before its `reset` would
hand back that region's reserved index-0 nil, so the guard is `next > CUR_BASE && next < CUR_TOP` and
the probe asserts the **refusal**; and `reset`'s `next - CUR_BASE - 1u` would underflow across zero,
so the rewind is two-sided and returns `0` for an interval it does not own.  The design's answer is
the contract "a driver rewinds at the boundary", and the sweep walks exactly that sequence — fill,
swap, refuse, rewind, fill the other side, swap back — so the transient is driven, not described.
After the second swap a low-interval handle can read live again while the low region's own `next` is
still rewound; that is the contract talking, which is why the sweep does not assert `is_live` in that
window and asserts it twice in the two windows where the answer is forced.

**Gate and evidence state after 5-B.3b-ii-b-2b.**  `verify_models.sh` is **17/17**, exit 0, with **no
edit to the runner**: everything new lives inside `verify/c/jpl_emit.sh`, whose check 5 sweep was
rewritten as four phases over both intervals and whose check 6 gained the interval identities.  The
`RUNTIME SUMMARY` key set goes **13 → 25**; the header **557 → 805** lines, the pools TU **487 → 769**,
`layout.txt` 217.  2f's declared-pool grep still returns **eight**, because the arrays this slice adds
are `jpl_<stem>_origin[…]`, not `jpl_<stem>_pool[…]` — the two-interval reading stays inside one
array's index domain, which is the property §6.7 paragraph 4 chose it for.  Check 7 is untouched and
re-reads the same 8 tables / 26 rows / 358 classes, the deliberate cross-check that a word's class is a
property of its cell's type and not of the region holding it.  Two placements were found by measurement
rather than assumption: the flip-cycle assertion `jpl_check_pools_flip_cycles_the_intervals` is emitted
into the **header** beside the `SPACES` macro it reads (the first grep for it in the TU returned 0 and
would have been a false failure), and the indicator's assignment count is taken from the file that
**defines** it — 2, the definition plus the writer — which is what turns "exactly one writer" from a
sentence in this document into a rung.

**The control that says the rung has teeth.**  Reverting `is_live` to §6.6's reading (`h > CUR_BASE`
→ `h > 0u`; the same test, since `JPL_NIL` is 0) changed **no report key, no table, no other
assertion**, and produced exactly **16** probe failures — the stale-below-`next` assertion firing in
both intervals of all eight pools — before exiting non-zero.  That is the shape a good negative control
has: the mutation is invisible to every accounting rung and fatal to the one that claims to be about
intervals.  The other controls for this slice (a `SPACES × cap` dimension refused by two emitted
typedefs at compile time; a stale `2·cap` literal at a registration site, refused by the emitter's own
`INTERVAL REFUSED` before any file was written; a second writer, measured moving 2 → 3; a dropped
`JPL_<KIND>_LO_BASE`, caught by the probe generator's own missing-macro refusal) are in §6.6's
*Measured* paragraph.  All of them ran against a **scratch mirror** of `verify/c/` rather than the
tree, because mutating the shipped emitter is exactly the edit the permission classifier blocks — the
block is correct, and a mirror that first reproduces a green run measures the same thing.

**Honest limits after 5-B.3b-ii-b-2b.**  (i) Still **no collector**: `origin` is written by nothing,
no cell is copied, and the 45 EDGE words are still read by no C — the slice supplies the space and the
predicate, not the walk.  (ii) The **scan pointer does not exist**, by design, so design item (ii)
("a probe that copies a graph with *known* sharing") stays owed to ii-b-2e and no rung here can
distinguish a future correct copy from one that copies everything.  (iii) Every
*kernel-attributable* `peak` is still **0** — the number the sweep reports is a runtime driven to its
bound, which is the distinction §6.6's "instrument, not the number" paragraph exists to keep.  (iv) The
swap has **no caller**: nothing flips the interval in a lowering, so the one-writer rung currently
counts a writer nothing invokes yet, and the first caller (ii-b-2d's `jpl_collect()`) is where
"a driver rewinds at the boundary" becomes an obligation with an owner.  (v) The four rendered bodies
are untouched, which the gate checks byte-for-byte, and no `OWED-REPRESENTATION` verdict moved: a cell
now has somewhere to be copied, which is still not a body being allowed to return one.

Next: **ii-b-2c**, evacuate one cell — read a word's class, copy a SCALAR as a word, turn an EDGE into
a to-space handle through `origin`, and carry the scan pointer that lets a copied cell be walked,
fixpoint over one pool.  Then ii-b-2d (roots, `jpl_collect()`, `BLimit`), ii-b-2e (the driven
collector's gate), then ii-b-3/4 (the two loop forms), ii-b-5 (`MAX_STACK`'s depth guard), ii-b-6 (the
5 model-side `BOUNDED FOLD` rewrites plus `branch_guardb`/`forallb`).

### JPL.5-B.3b-ii-b-2c / #41 — DONE (2026-10-06): evacuating one cell, and the two collector bugs no counter can see

**What opened the slice.**  2a produced 45 EDGE words and 2b produced two intervals, an `origin` array
and a swap, and the pair of them still moved nothing: a word could be *labelled* a handle and its cell
could have a *place* to be copied to, with no C that read one to obtain the other.  §6.7's closing
sentence for two slices had been that the tables and the intervals were "honestly a data dependency".
This slice is the dependency being executed once per word: `evac`, the whole-cell copy, the word
chains that let the scan rewrite one EDGE word without a pointer or a cast, the to-space `scan`
pointer with `queue_start`/`scan_one`/`drain`, and one runtime dispatch over the whole target-id domain.

**The four choices the slice makes.**  (i) **Swap-then-rewind**, so that the allocator §6.6 already
emitted *is* the to-space allocator: `allocators_emitted` stays 8 because the boundary flips the
indicator before rewinding, and the alternative — a second family of to-space allocators — is a second
model of a bound that `CUR_BASE`/`CUR_TOP` already own.  The consequence is stated in §6.7 and measured
in check 5: after a swap, `reset` returns **0**, because one `next` per pool now names the to region
and the from region's frontier stops being tracked.  (ii) **The copy is one structure assignment**, and
the only place a word is addressed by index is the derived `word_at`/`word_put` chain — which is where
R7's "every slot is one `uint32_t`" pays for itself, together with 2a's
`NPOS * 4u == sizeof (cell)` typedef: no pointer, no cast, no strict-aliasing question, and the first
pointer in the tree stays out of the tree.  (iii) **No arm of a chain is a bare `else`.**  A catch-all
arm answers the last member's value for an index that has no member, which a collector then writes;
every arm tests its own index, a read past the end answers `JPL_NIL` (the empty list — already "no
child"), and coverage is enforced at the site where the arms are built, by five emitter refusals
(members that do not reach `NPOS`, an array that is not the cell's trailing words, a word count that
disagrees with the paths its by-value type expands to, a member wider than one word with no type to
split it, a pool that registers no members at all) plus 2a's typedef.  (iv) **Four arms on `origin`,
and the fourth is what makes the third true.**  The trace is two rounds deep: after a swap the from
region *is* the previous round's to region, so `origin[t] = h` can name an index the current interval
has already reached, all arms but the mutual one holding, and `evac` answering a cell whose words point
at the interval being abandoned.  `jpl_<s>_alloc` therefore clears `origin` for the cell it hands out —
one store, charged to a copy rather than to a region, which is §6.6's no-clearing-pass argument
applied to a second array — and the mutual arm `origin[o] == h` is what turns "below the frontier" into
"written *this* round".

**The finding that changed the doc, not the code.**  This section claimed `cmd` had no self edge; the
derivation in check 9 says otherwise — `Seq (cmd, cmd)` puts one at **word 1 of row 3**, which is why
the drive has six chains and not five.  It is worth recording that the claim was made from the node
pool's tag rows rather than from the emitted table, and that the gate now reads the table: the probe's
size is a property of the artifact, so a pool gaining or losing a self edge changes the drive without
anyone editing a literal in a shell script.  The same derivation supplies the row index a tagged
chain's cell must carry, which is why each tagged chain also measures `scan_one`'s tag→row arithmetic.

**Two of the three bugs here are invisible to every number in the report.**  The control run is green,
then three mutations, each in a scratch mirror of `verify/c/`: dropping `alloc`'s origin clear (M1)
moves one key (`origin_clears_emitted` 8 → 0) and fails **78** assertions; deleting the mutual arm's
content (M2, `origin[o] == h` → `o < next`, arity-preserving so the emitted C compiles and no tautology
warning fires) moves **no** key and fails the same **78**; mis-wiring one dispatch arm's class macro
(M3, `text_list`'s edges evacuated through `frame`) moves **no** key either and fails **24** while
`jpl_pools_unclassified` reaches **10**, i.e. the branch this section calls impossible turns out to be
reachable and the report's arm count still says 8.  That is the load-bearing result of the slice: the
accounting rungs were never going to see a forwarding test that lies, because a lie is a *relation*
between two arrays and a count measures neither array's contents.  §6.7's design item (ii) said a
collector must be driven, not read; this is the per-pool half of that claim, and it is why the drive
landed as a check rather than as a note.

**Gate and evidence state after 5-B.3b-ii-b-2c.**  `verify_models.sh` is **17/17**, exit 0, still with
**no new rung**: the ninth check lives inside `verify/c/jpl_emit.sh`, which is now **nine** checks, and
the `JPL_REGEN=1` re-pin moved to *after* it, so evidence can only be vendored by a run the drive
approved.  Vendored bytes: `sh_run_jpl.h` **805 → 1176**, `sh_run_jpl_pools.c` **769 → 1834**,
`layout.txt` **217 → 235**; 2f stays green with all five of its artifacts byte-identical and the four
rendered bodies untouched.  The storage the slice predicted and the storage it produced are recorded in
§6.7's *Measured* paragraph, including the one prediction that failed (40 new globals predicted, **35**
emitted, because `badtag` exists only where a cell has a tag word) and the third independent reading of
the tag-guard count (header `NROWS > 1`, the report key, the guards in the TU — all **2**).

**Honest limits after 5-B.3b-ii-b-2c.**  (i) **Nothing calls any of it.**  There is no root list, no
`jpl_collect()`, no loop over the eight pools and no `BLimit`, so the swap and the scan still have no
owner — ii-b-2d, exactly as the slice table says.  (ii) The chains are **one pool deep**: the dispatch
is crossed, because a self edge is routed through `evac_by_class`, but a graph that visits three
different pools is design item (ii)'s cross-pool case and waits on ii-b-2e's probe.  (iii)
`peak` is still **0** for every kernel-attributable run.  (iv) The `reset`-returns-**0** behaviour at a
boundary is a real limit of the one-`next` design, documented rather than fixed: "cells returned by
this reset" is only a meaningful quantity when the reset does not cross a boundary.  (v) `evac`'s domain
is from-space handles; the drive asserts the refusal, but the case that *matters* — a root list naming
the wrong interval — needs 2d's roots to arise.  (vi) No `OWED-REPRESENTATION` row moved: a cell can now
be copied, and §6.3's schemas still gate whether a body may return one.

Next: **ii-b-2d**, the roots and the boundary — a derived root list for `cfg`/`out`, `jpl_collect()` =
evacuate the roots + drain every pool's scan + swap, saturating to `BLimit` on any to-space overflow,
with the rung "a `collect` must not return success with a pool's `scan` behind its `next`".  Then
ii-b-2e (the driven cross-pool collector gate), ii-b-3/4 (the two loop forms), ii-b-5 (`MAX_STACK`'s
depth guard), ii-b-6 (the 5 model-side `BOUNDED FOLD` rewrites plus `branch_guardb`/`forallb`).


