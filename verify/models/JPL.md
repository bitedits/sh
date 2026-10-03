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
   migrate ush + vendored kernel only after parity + conformance pass.
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
| **R4** no recursion (direct or indirect); iteration only | control flow is a tail driver: `sh_jpl_run.v` `mloop` (single `step` per tick); `sh_jpl_scan.v` §4 `glob_it`/`match_any_iter` replace `sh_concrete.glob`'s tree recursion; `nat`→`int` via `ExtrOcamlNatInt` (kills `add`/`sub`/`divmod` fixpoints) | emitter lowers tail `let rec`→`while`; `Extract Constant Nat.div/mod/sub`→primitive ops (#33) |
| **R17** fixed-width types (unsigned here) | `sh_jpl.v` §3 `b_add`/`b_sub`/`b_mul`/`b_divmod` + `cap_order` (all values ≤ `MAX_STACK` < 2³², so the word never wraps) | `uint32_t`; `-Wconversion`-clean casts (emitter) |
| **R1** no undefined/unspecified behaviour; explicit error on breach | saturate-to-error carrier `bres`/`bbind`; `sh_jpl.v` `b_add_limit`/`b_divmod_limit` (div-by-0 ⇒ `BLimit`, not UB); `sh_jpl_scan.v` `bt_append_full` | `BLimit` ⇒ defined `LIMIT_EXHAUSTED` return (matches fuel→`None`) |
| **R3** statically-bounded loop iterations | fuel budget `b_fuel`/`b_fuel_ok` (`≤ MAX_FUEL`); machine step budget `sh_jpl_run_phase2.v` `cfg_budget`/`next_decrease`/`prec_wf` ⇒ every run terminates (`mrun_live`) | `while` with a decremented counter, no unbounded loop |
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
| `MAX_WIDTH` (nat word bits) | 32 | uint32_t; byte<=255, fuel<=65536, status<=255 all fit |
| `MAX_WORD` | 256 | expanded word / text length in bytes |
| `MAX_ARGV` | 64 | argument words per simple command |
| `MAX_ENV` | 128 | simultaneously live shell variables |
| `MAX_LIST` | 1024 | any intermediate list length (cmd-list bodies, word lists, case branches) |
| `MAX_CMD` | 4096 | node pool capacity for one lowered program's `cmd` tree |
| `MAX_FUEL` | 4096 | loop-iteration bound (matches ush's current fuel budget) |
| `MAX_STACK` | 8192 | explicit machine stack frames (>= 2*MAX_FUEL headroom) |

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
  array representation (single loop index, no self recursion; `glob`'s backtracking
  uses a bounded `(pat,str,alt)` backtrack stack of size `MAX_STACK`).
- Coq termination: measures on the (decreasing) fuel/index; still `Fixpoint`, but
  extraction yields a tail-recursive OCaml function -> a C `while`/`for`.

## 6. Extraction contract

Coq (iterative, array-based, bounded) --Extraction--> OCaml (tail loops + fixed
arrays) --simple emitter--> C99. The emitter only has to handle: tail
`let rec ... acc` -> `for`/`while`; `uint32` nat; fixed arrays + a length field;
tagged-struct `cmd`; records->structs; `match`->`switch` (exhaustive, no default);
`option`/result -> a struct `{ ok; val }` or an out-param + status. No monomorphization
(all values are concrete after the array re-encoding), no closure conversion (the
`phi` seam is data), no GC (static pools only).

### 6.1 Established extraction behaviour

A fuel-bounded tail `Fixpoint` (`scan (f:nat) (l:list) (acc:list)` with the
recursive call in tail position) extracts to OCaml `let rec scan f l acc = match f
with O -> ... | S f' -> ... scan f' r ...` — a genuine tail loop, so lowering to a
C `while` (decrement `f`, exit on `O`) is sound. Two obligations for the model/emitter:
- `List.rev`/`app` extract to NON-tail structural recursion; the source must use
  accumulator-style bounded helpers, or the emitter must lower bounded structural
  recursion (length <= MAX) to a fixed-array copy loop.
- Extraction keeps a custom `nat = O|S` and `list = Nil|Cons` (or native list under
  ExtrOcamlBasic); the emitter maps these to `uint32_t` and fixed-capacity arrays.

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
- replays the 26 parity checks (C99 == extracted iterative OCaml kernel),
- replays the /bin-sh conformance corpus (C99 == /bin/sh) for the implemented
  subset (see the `src/` boundary memory).
Added to `verify_models.sh` / a new `verify/c/conformance.sh`; all prior gates
(OCaml-free now, so: Coq properties x2, extraction parity, src conformance) stay green.

## 9. Construction order (matches task list)

This is the **normative build order**: a strictly sequential dependency chain —
each stage's deliverable is a precondition for the next, so they are *stages*, not
parallel tracks. Read an arrow `->` as "blocks". Task numbers (#N) refer to the
project tracker; file names are the Coq/build artifacts the stage delivers.

**Label scheme (decoded).** `JPL.<phase>` = a top-level pipeline phase (§9 table
below). When a phase's precondition audit shows it cannot run on the current
source, a **path** letter is appended — `JPL.5-A` = the chosen "root-cause the Coq
source first" path for phase 5 (the alternative `B`, "transpile as-is", was
rejected; see HISTORY). `<phase>-<path>.<stage>` = an ordered prerequisite stage
*inside* that path, numbered in dependency order. So `5-A.1` is "stage 1 of the A
path leading to phase JPL.5 (the emitter)".

### 9.1 Phases

| Phase | Task | Deliverable | State |
|---|---|---|---|
| JPL.1 | #21 | this design plan (`JPL.md`) | DONE |
| JPL.2 | #22 | bounded data layer, axiom-free — `sh_jpl.v` | DONE |
| JPL.3 | #23 | small-step machine + boundary lemmas — `sh_jpl_run.v` | DONE |
| JPL.3b | #28 | two-sided machine equivalence (liveness/completeness) — `sh_jpl_run_phase2.v` | DONE |
| JPL.4 | #24 | extract iterative kernel + re-run 26 parity — `sh_extract_iter.v`, `sh_run_iter.ml` | DONE |
| JPL.5-A | #29–#33 | **source-rearchitecture prerequisite stages** (§9.2 below) | IN PROGRESS |
| JPL.5 | #25 | tail-loop OCaml → JPL-C99 emitter | BLOCKED on JPL.5-A |
| JPL.6 | #26 | mechanical D-60411 *shall*-rule lint gate on emitted C | pending JPL.5 |
| JPL.7 | #27 | C host + differential conformance (C99 == kernel == /bin/sh) | pending JPL.6 |

### 9.2 JPL.5-A stages (prerequisites before the emitter can run)

Chosen path (A) after the JPL.5 precondition audit: move every *behavioral*
transform into an axiom-free Coq bounded-representation layer, re-proven to agree
with `sh_concrete.run` and re-running the 26 parity checks, so the emitter keeps
only the mechanical *layout* duty (`list`→static array+len, `nat`→`uint32`). Additive
throughout: existing gates stay green; new artifacts are wired into
`verify_models.sh` as additional gates.

| Stage | Task | Deliverable (Coq / artifact) | Depends on | State |
|---|---|---|---|---|
| 5-A.1 | #29 | bounded byte-array text `bt` (len-carrying, cap MAX_WORD); `teqb`/`nat2text`/`expand`/`expand_*` as fuel-bounded tail loops; isomorphism Examples vs `sh_concrete` — `sh_jpl_scan.v` | JPL.4 | DONE |
| 5-A.2 | #30 | tail-loop `getv`/`setv` over the `benv` array rep, agreeing with concrete `getv`/`setv` | 5-A.1 | pending |
| 5-A.3 | #31 | iterative `glob`/`match_any` (backtrack recursion → bounded forward scan); isomorphism with concrete `glob` — `sh_jpl_scan.v` | 5-A.1 | DONE |
| 5-A.4 | #32 | **phi-as-data driver**: `mloop` returns the `Oeffect` as data and takes **no** `phi` function; a host loop services the seam and re-enters; JPL.3/3b soundness + completeness restated over the new driver | 5-A.3 | pending (current) |
| 5-A.5 | #33 | extraction `sh_extract_jpl_c.v`: `ExtrOcamlNatInt` + `Nat.div`/`mod`/`sub` constant hooks → `sh_run_c.ml` (all tail loops + uint32 + length-bounded records + no closures); re-run 26 parity, re-vendor | 5-A.4 | pending |

When 5-A.1…5-A.5 are green, phase JPL.5 (#25) unblocks: the emitter maps
`sh_run_c.ml` → JPL-clean C99, then JPL.6 (#26) lints it and JPL.7 (#27) runs it
against the `/bin/sh` oracle.

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
- **Capacity defaults** (`MAX_*` in §4.1) confirmed as proposed.
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
