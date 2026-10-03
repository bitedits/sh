# JPL-compliant C99 extraction — 3d-C re-architecture plan

Status: DECISIONS LOCKED (2026-10-03) — saturate-to-error + proposed default caps.
Governs Phase 3d-C. Supersedes the earlier "transpile sh_run.ml directly" plan,
which violated the JPL rule set.

## Why re-architecture (not direct emit)

The current single source of truth, `verify/models/sh_concrete.v`, extracts (via
Coq Extraction) to OCaml (`src/kernel/sh_run.ml`) that is **fuel-bounded
recursion over heap lists** (Peano `nat`, `text = nat list`, `cmd` tree,
higher-order `obind` callbacks). A literal OCaml->C99 emit would therefore use
`malloc`, recursion, boxed unary naturals, and function pointers — each of which
breaks a mandatory canonical JPL PowerPC C rule.

Decisions locked by the user:
- Transforms that make the C JPL-clean live **in the Coq source**, not the
  emitter: re-aim the model to **iteration over bounded array structures**, then
  run a **simple, narrow** OCaml->C99 emitter.
- Target the **canonical JPL 44-rule C standard**, enforced mechanically by a lint
  gate over the emitted C.

## Design invariants

1. **Axiom-free throughout.** Every new Coq file must satisfy
   `coqchk -o -silent` four `<none>` lines. No `Axiom`/`Parameter`/`Admitted`.
2. **Behavioral isomorphism.** The new iterative kernel must reproduce the
   observable results of `sh_concrete.run` (same status/env outcomes) so the 26
   extraction-fidelity parity checks stay green when re-pointed at it.
3. **Keep existing gates green while building alongside.** Do not edit
   `sh_concrete.v` or `src/kernel/sh_run.ml` destructively. New files first;
   migrate ush + vendored kernel only after parity + conformance pass.

## Bounded representation (the budget)

`nat` (byte codes 0..255, fuel, status 0..255) maps to a fixed-width **unsigned**
machine type. All arithmetic is unsigned with an explicit bound discipline; within
the caps below, unsigned arithmetic is a bijection with Peano, so parity with the
OCaml kernel is preserved.

### Caps (LOCKED — user confirmed proposed defaults 2026-10-03)

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

### Overflow / bound-exhaustion policy — LOCKED: saturate-to-error

When an operation would exceed a cap, options:
- **(A recommended) Saturate-to-error**: return a defined `LIMIT_EXHAUSTED`
  status (the analogue of the model's fuel=0 -> `None`), surfaced to the host as a
  hard failure — never silent wraparound. Keeps the "no undefined behaviour" and
  "explicit error return" JPL spirit and matches the existing truncation semantics.
- **(B) Modular wraparound**: simpler but can mask truncation; risks diverging
  from the verified model on out-of-budget inputs.

LOCKED: **(A) saturate-to-error**, because the shell is safety-framed and
truncation must be observable, not hidden.

## Recursion elimination — the small-step machine

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

## Extraction contract

Coq (iterative, array-based, bounded) --Extraction--> OCaml (tail loops + fixed
arrays) --simple emitter--> C99. The emitter only has to handle: tail
`let rec ... acc` -> `for`/`while`; `uint32` nat; fixed arrays + a length field;
tagged-struct `cmd`; records->structs; `match`->`switch` (exhaustive, no default);
`option`/result -> a struct `{ ok; val }` or an out-param + status. No monomorphization
(all values are concrete after the array re-encoding), no closure conversion (the
`phi` seam is data), no GC (static pools only).

### Validated (live probe, 2026-10-03)

A fuel-bounded tail `Fixpoint` (`scan (f:nat) (l:list) (acc:list)` with the
recursive call in tail position) extracts to OCaml `let rec scan f l acc = match f
with O -> ... | S f' -> ... scan f' r ...` — a genuine tail loop, so lowering to a
C `while` (decrement `f`, exit on `O`) is sound. Two obligations for the model/emitter:
- `List.rev`/`app` extract to NON-tail structural recursion; the source must use
  accumulator-style bounded helpers, or the emitter must lower bounded structural
  recursion (length <= MAX) to a fixed-array copy loop.
- Extraction keeps a custom `nat = O|S` and `list = Nil|Cons` (or native list under
  ExtrOcamlBasic); the emitter maps these to `uint32_t` and fixed-capacity arrays.

## JPL lint gate (design)

`verify/c/jpl_lint.sh` audits the emitted `sh_run.c`/`.h`:
- static ban list via grep + clang: no `malloc|calloc|realloc|free`, no direct or
  indirect recursion (call-graph acyclic within the emitted file), no `float|double`,
  no `char` used in arithmetic, no `short`, no VLAs (all arrays constant-sized), no
  `goto`, no `default:` in `switch`, one `return`/early-return style, all locals
  initialized, casts are explicit (`-Wconversion -Wsign-conversion` clean), no TAB.
- compile with `clang -std=c99 -Wall -Wextra -Wconversion -Wsign-conversion
  -pedantic -Werror`.

## Differential gate (design)

`verify/c/` host supplies the real `phi` (fork/execvp/pipe/redirect, cd/exit/:)
over the C kernel, then:
- replays the 26 parity checks (C99 == extracted iterative OCaml kernel),
- replays the /bin-sh conformance corpus (C99 == /bin/sh) for the implemented
  subset (see the `src/` boundary memory).
Added to `verify_models.sh` / a new `verify/c/conformance.sh`; all prior gates
(OCaml-free now, so: Coq properties x2, extraction parity, src conformance) stay green.

## Sequencing (matches task list)

JPL.1 this plan -> JPL.2 bounded data layer (.v, axiom-free) -> JPL.3 small-step
machine + boundary lemmas -> JPL.4 extract iterative kernel + re-run 26 parity ->
JPL.5 tail-loop OCaml->C99 emitter -> JPL.6 JPL lint gate -> JPL.7 C host +
differential conformance.

## JPL.2 — DONE (2026-10-03): verify/models/sh_jpl.v

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

## JPL.3 — DONE (2026-10-03): verify/models/sh_jpl_run.v

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

DEFERRED to JPL.3b (documented, not silently dropped):
- **Completeness / step budget**: a proved `B` such that `mloop phi B` *reaches*
  the sound answer for every in-budget input (i.e. `run = Some st -> mloop = BOk st`).
  Soundness is unconditional and is what guarantees no wrong answer; completeness
  is what guarantees an answer within budget.  Empirically backed for now by the
  26 parity + 33 conformance gates.
- **Scan-level iterativity**: this machine drives `expand`/`glob`/`match_any` by
  calling the fuel-bounded concrete functions (same as §8's bounded wrappers).  The
  plan's target — those scans as iterative accumulator loops over `bword`/`benv`
  with no self recursion — is JPL.4/JPL.5 work; JPL.3 fixes the control-flow
  machine's contract that they must feed.
