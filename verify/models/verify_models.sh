#!/usr/bin/env bash
# verify_models.sh — integration check for the POSIX shell verifiable model
#
# Covers:
#   - sh_properties.v    (Rocq/Coq relational semantics + main shell theorems, axiom-free)
#   - sh_concrete.v      (Rocq/Coq concrete POSIX model: text/env/expansion/glob/control flow)
#   - sh_jpl.v           (bounded-array data layer for the JPL C99 emit: saturate-to-error,
#                         fixed-width nat, bounded text/env/cmd-pool; agrees with sh_concrete)
#   - sh_jpl_run.v       (bounded small-step machine over sh_jpl: explicit continuation stack,
#                         phi-as-data effect leaf, fuel-bounded tail driver; proven sound against
#                         sh_concrete's run — mloop BOk st -> run = Some st, axiom-free)
#   - sh_jpl_run_phase2.v (the LIVENESS/completeness half: a well-founded step budget gives
#                         cfg_run phi g = Some st -> exists B, mloop phi B g = BOk st; with
#                         sh_jpl_run's soundness this is the two-sided machine<->run
#                         equivalence (mloop_iff / mloop_sound_complete), axiom-free)
#   - sh_jpl_run_phase3.v (JPL.5-A.4 the phi-as-DATA driver: `mrun B g` is the closure-free
#                         kernel loop — it iterates sh_jpl_run's phi-free `step` and returns the
#                         seam as a plain `dres` value (DDone / DEff idx argv k s / DLim), so
#                         extraction leaves no function pointer (JPL Rules 6/29); `host phi B g`
#                         models the C main loop that services a DEff and re-enters.  Soundness
#                         (host_sound), completeness over the phase2 cfg_budget ranking
#                         (host_live, by well-founded induction), the two-sided host_iff_run, and
#                         §7 boundary Examples agreeing with concrete run — axiom-free)
#   - sh_jpl_run_c.v     (JPL.5-A.6 the REWIRED machine: `step_c`/`mrun_c`/`host_c` reach the
#                         OS seam only through sh_jpl_scan's PROVED tail loops — setv_it for the
#                         env write, branch_guardb + match_any_iter for the case site, expand_it
#                         (sh_jpl_scan §6) + expand_c for the expansion and its word cap.  The two matchers have DIFFERENT fuel laws (L2 decides
#                         at the linear branch_need, the loop needs the quadratic fuel_top), so the
#                         guard is load-bearing: the headline is the conditional step_c_ok
#                         (step_c g <> Olimit -> step_c g = step g), never an unconditional
#                         equality; soundness is transported unconditionally, completeness under
#                         no_sat.  §5 proves the budgets MINIMAL, not merely enough:
#                         case_site_fuel = 1537 is ATTAINED by an in-caps branch set, GLOB_FUEL is
#                         literally fuel_top at two full-width words, and MAX_FUEL - GLOB_FUEL is
#                         exactly MAX_CMD — axiom-free)
#   - sh_extract.v       (Coq Extraction of the concrete run -> OCaml sh_run.ml) +
#                        sh_run_parity.ml (fidelity harness: derived OCaml == kernel-verified Coq)
#   - sh_extract_iter.v  (Coq Extraction of the JPL-shaped iterative kernel — the non-recursive
#                        step dispatcher + tail driver mloop, alongside run so the module shares
#                        one set of datatypes -> OCaml sh_run_iter.ml, vendored as src/kernel's
#                        2nd artifact) + sh_run_iter_parity.ml (re-runs the 26 §7-§9 facts through
#                        mloop and asserts mloop == run == the verified literal: isomorphism)
#   - sh_extract_jpl_c.v (Coq Extraction with JPL TARGET SETTINGS — nat -> machine int
#                        (ExtrOcamlNatInt) and Nat.div/modulo/divmod/sub/max hooked to
#                        primitives —
#                        of BOTH drivers: the closure-free phase3 `mrun`/`step` AND the rewired
#                        `mrun_c`/`step_c` of sh_jpl_run_c.v, with the recursive `run` kept in the
#                        same module as the reference oracle
#                        -> OCaml sh_run_c.ml, vendored as src/kernel's 3rd artifact)
#                        + sh_run_c_parity.ml (66 checks: the 15 §7-§9 facts re-run from ONE table
#                        through both drivers + a hand-written closure-free host, asserting
#                        mrun+host == mrun_c+host == run == the verified literal; 15 tail-loop-vs-
#                        concrete checks of the emitted sh_jpl_scan loops, including two fuel x word
#                        sweeps of expand_it against L2's expand (15 words x 9 fuels each, 270
#                        comparisons over both); and the rewired
#                        kernel's own surface — expand_c admitting at MAX_WORD and saturating one
#                        byte over it, branch_guardb's thresholds and caps, and the measured case
#                        where the reference answers while mrun_c reports DLim)
#   - ../c/jpl_front.ml  (JPL.5-B.1 the EMITTER FRONT END: reads the extracted .ml/.mli with
#                        compiler-libs and reports, from the ROOTS THE C HOST CALLS, the typed
#                        closure it would have to lower — per-binding arity/recursion/fuel-idiom
#                        self-count, the expression and pattern class census, the allocation
#                        census and the type vocabulary — and PASSES only if every construct in
#                        that closure is in JPL.5's declared subset.  Root-parameterised, so the
#                        oracle cluster is provably outside the subset (its mutual expand fixpoint
#                        fails the gate) while the shipped kernel is inside it: §9.2's decision 1
#                        becomes a measurement.  Evidence: ../c/closure.txt, byte-compared anti-rot)
#   - ../c/jpl_emit.ml   (JPL.5-B.2 the REPRESENTATION LAYER: the third consumer of the shared
#                        reader jpl_ast.ml.  It reads the same shipped closure plus the artifact's
#                        OWN jpl_caps_table and writes the C99 type layer that closure must be
#                        lowered into: every capacity constant-folded out of the extracted term,
#                        every layout derived from a .mli declaration through one rule set
#                        (R1 scalars, R2 the bounded word, R3 cons-cell list pools, R4 tagged
#                        structs, R5 pairs, R6 records, R7 enum / pooled node / fat struct), every
#                        struct followed by a C99 compile-time sizeof assertion, and every cap
#                        relation sh_jpl.v §1 proved re-checked as a typedef array bound.  Where no
#                        cap bounds a pool the tool emits PENDING and NO dimension: the word slab is
#                        exactly that case, and layout.txt prints the range the locked caps do
#                        imply instead of inventing a number.
#                        Evidence: ../c/sh_run_jpl.h + ../c/layout.txt, byte-compared anti-rot;
#                        ../c/jpl_emit.sh additionally diffs the nine folded caps against the
#                        artifact EVALUATED by the OCaml runtime, and compiles the header with the
#                        JPL C99 flag set)
#   - sh_jpl_scan.v      (Rocq/Coq JPL.5-A.1/2/3 bounded-word + iterative-scan layer: the
#                        bt = bword layer with saturating bt_push/bt_append; the tail loops
#                        glob_it/glob_iter/match_any_iter, the env getv_it/setv_it, the word
#                        expander expand_go/expand_it (§6, hypothesis-free agreement at EVERY
#                        fuel) and the array API be_getv/be_setv, each proved to AGREE WITH
#                        sh_concrete IN BOTH
#                        DIRECTIONS for arbitrary input (§4.2 soundness via a declarative gmatch
#                        spec, §4.3 completeness at the loop's own quadratic budget fuel_top);
#                        §4.3.14 sizes sh_jpl's GLOB_FUEL/MAX_FUEL from that proved law
#                        (fuel_top_le_glob_fuel + the machine-facing completeness corollaries);
#                        axiom-free)
#
# The end-to-end oracle is /bin/sh itself: verify/src/conformance.sh runs the shell
# built on the extracted kernel and diffs its stdout against /bin/sh.  The former
# hand-written OCaml model (sh_model.ml) was a parallel encoding of the same
# semantics and has been retired in favour of that single source of truth.
#
# Usage:
#   ./verify_models.sh
#   ./verify_models.sh --skip-coq          # skip Coq properties and the extraction step
#   ./verify_models.sh --skip-extract      # Coq properties only, no extraction step
# The emitter rungs (2d front end, 2e representation layer) are not Coq checks: they
# read the vendored artifact and run even under --skip-coq, so a subset violation or a
# wrong byte count cannot hide behind a skipped build.
# Exit 0 only if all selected checks pass.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
SELF="$ROOT/$(basename "$0")"
cd "$ROOT"

SKIP_COQ=0
SKIP_EXTRACT=0
for arg in "$@"; do
  case "$arg" in
    --skip-coq)     SKIP_COQ=1; SKIP_EXTRACT=1 ;;
    --skip-extract) SKIP_EXTRACT=1 ;;
    -h|--help)
      # print the whole header comment, whatever its current length
      awk 'NR==1,/^# Exit 0/' "$SELF"
      exit 0
      ;;
  esac
done

COQ_PROPERTIES=("sh_properties.v" "sh_concrete.v" "sh_jpl.v" "sh_jpl_run.v" "sh_jpl_scan.v")
# The machine's proof layers, in dependency order: phase2 (liveness of mloop)
# Require Imports sh_jpl_run, phase3 (the phi-as-DATA driver: mrun + host)
# Require Imports both, and sh_jpl_run_c (the REWIRED machine) Require Imports
# phase3 + scan, so each must be compiled after the one before it.
COQ_MACHINE=("sh_jpl_run_phase2.v" "sh_jpl_run_phase3.v" "sh_jpl_run_c.v")
PASS=0
FAIL=0
# A skipped check is neither a pass nor a failure: it is reported in the summary
# so that a missing toolchain can never be mistaken for a verified stage.
SKIP=0

green() { printf '\033[32m%s\033[0m\n' "$*"; }
red()   { printf '\033[31m%s\033[0m\n' "$*"; }
bold()  { printf '\033[1m%s\033[0m\n' "$*"; }
skip()  { printf '\033[33m%s\033[0m\n' "$*"; }

# ── 1. Rocq / Coq formal properties ────────────────────────────────
coq_gate() {
  local p="$1" COQ_OUT AX MOD
  bold "==> Coq/Rocq properties ($p)"
  if COQ_OUT="$(coqc "$p" 2>&1)"; then
    if echo "$COQ_OUT" | grep -q "Error"; then
      red "FAIL: coqc reported Error in $p"
      echo "$COQ_OUT"
      FAIL=$((FAIL + 1))
    else
      # compiling is not the same as being axiom-free: re-check the .vo in
      # the kernel and refuse a non-empty axiom / unsafe-construction list.
      MOD="${p%.v}"
      if AX="$(coqchk -o -silent "$MOD" 2>&1)" \
         && echo "$AX" | grep -q "Axioms: <none>" \
         && echo "$AX" | grep -q "type-in-type: <none>" \
         && echo "$AX" | grep -q "(co)fixpoints: <none>" \
         && echo "$AX" | grep -q "positivity is assumed: <none>"; then
        green "PASS: coqc + coqchk ($p - theorems closed, no axioms)"
        PASS=$((PASS + 1))
      else
        red "FAIL: coqchk found axioms or unsafe constructions in $p"
        echo "$AX" | grep -i -A3 "axioms:\|type-in-type:\|fixpoints:\|positivity"
        FAIL=$((FAIL + 1))
      fi
    fi
  else
    red "FAIL: coqc exited non-zero for $p"
    echo "$COQ_OUT"
    FAIL=$((FAIL + 1))
  fi
  echo
}

if [[ "$SKIP_COQ" -eq 0 ]]; then
  if ! command -v coqc >/dev/null 2>&1; then
    red "FAIL: coqc not found (install Rocq/Coq or use --skip-coq)"
    FAIL=$((FAIL + 1))
  else
    for p in "${COQ_PROPERTIES[@]}" "${COQ_MACHINE[@]}"; do
      coq_gate "$p"
    done
  fi
else
  bold "==> Coq skipped"
  echo
fi

# ── 2. Coq Extraction -> OCaml, fidelity against the kernel-verified model ──
# Proves the derived OCaml `run` reproduces the §7-§9 facts sh_concrete.v verifies
# in the Rocq kernel.  This is the single-source pipeline: Coq is the truth, the
# extracted OCaml (sh_run.ml) is a build artifact, and this step checks they agree.
if [[ "$SKIP_EXTRACT" -eq 0 ]]; then
  bold "==> Extraction fidelity (sh_concrete.v -> OCaml run)"
  if ! command -v coqc >/dev/null 2>&1 || ! command -v ocamlc >/dev/null 2>&1; then
    red "FAIL: extraction needs both coqc and ocamlc"
    FAIL=$((FAIL + 1))
  else
    # sh_extract.v requires sh_concrete.vo, so build it first (idempotent).
    if coqc sh_concrete.v >/dev/null 2>&1 && coqc sh_extract.v >/dev/null 2>&1; then
      # Anti-rot: src/kernel/sh_run.ml{,i} is the vendored copy ush builds against.
      # It must be byte-identical to this fresh extraction, else the vendored kernel
      # has drifted from sh_concrete.v (the single source of truth) and ush is
      # running code we never verified.
      VEND=../../src/kernel
      if [[ -f "$VEND/sh_run.ml" && -f "$VEND/sh_run.mli" ]] \
         && diff -q sh_run.ml "$VEND/sh_run.ml" >/dev/null \
         && diff -q sh_run.mli "$VEND/sh_run.mli" >/dev/null; then
        green "PASS: vendored src/kernel/sh_run.ml is identical to fresh extraction"
      else
        red "FAIL: src/kernel/sh_run.ml{,i} is stale vs sh_concrete.v extraction"
        red "      re-run: cp sh_run.ml sh_run.mli ../../src/kernel/  (after coqc sh_extract.v)"
        diff -q sh_run.ml "$VEND/sh_run.ml" || true
        diff -q sh_run.mli "$VEND/sh_run.mli" || true
        FAIL=$((FAIL + 1))
      fi
      # Fidelity: the derived OCaml run reproduces the §7-§9 kernel facts.
      if ocamlc -w -a -o sh_run_parity sh_run.mli sh_run.ml sh_run_parity.ml >/dev/null 2>&1; then
        if EX_OUT="$(./sh_run_parity 2>&1)" && echo "$EX_OUT" | grep -q "passed successfully"; then
          echo "$EX_OUT" | tail -4
          green "PASS: extracted OCaml run matches the verified Coq model"
          PASS=$((PASS + 1))
        else
          red "FAIL: extracted OCaml run disagrees with the Coq model"
          echo "$EX_OUT" | grep -i "fail" | head -20
          FAIL=$((FAIL + 1))
        fi
      else
        red "FAIL: OCaml build of the fidelity harness failed (sh_run_parity.ml)"
        FAIL=$((FAIL + 1))
      fi
    else
      red "FAIL: extraction step failed (sh_extract.v -> sh_concrete.vo)"
      FAIL=$((FAIL + 1))
    fi
  fi
  echo

  # ── 2b. Iterative (JPL-shaped) kernel: sh_jpl_run.v -> OCaml mloop ──
  # sh_extract_iter.v extracts the non-recursive `step` + tail driver `mloop`
  # (the code JPL.5 will lower to C99) TOGETHER with the recursive `run`, so one
  # module shares a single set of datatypes.  sh_run_iter_parity.ml then re-runs
  # the same 26 §7-§9 facts through mloop and asserts, per command, that
  # mloop == run == the kernel-verified literal — design invariant #2.
  bold "==> Iterative-kernel extraction fidelity (sh_jpl_run.v -> OCaml mloop)"
  if ! command -v coqc >/dev/null 2>&1 || ! command -v ocamlc >/dev/null 2>&1; then
    red "FAIL: iterative extraction needs both coqc and ocamlc"
    FAIL=$((FAIL + 1))
  else
    if coqc sh_concrete.v >/dev/null 2>&1 && coqc sh_jpl.v >/dev/null 2>&1 \
       && coqc sh_jpl_run.v >/dev/null 2>&1 && coqc sh_extract_iter.v >/dev/null 2>&1; then
      # Anti-rot: src/kernel/sh_run_iter.ml{,i} is the vendored second artifact;
      # it must be byte-identical to this fresh extraction, else the vendored
      # iterative kernel has drifted from sh_jpl_run.v (its source of truth).
      VEND=../../src/kernel
      if [[ -f "$VEND/sh_run_iter.ml" && -f "$VEND/sh_run_iter.mli" ]] \
         && diff -q sh_run_iter.ml "$VEND/sh_run_iter.ml" >/dev/null \
         && diff -q sh_run_iter.mli "$VEND/sh_run_iter.mli" >/dev/null; then
        green "PASS: vendored src/kernel/sh_run_iter.ml is identical to fresh extraction"
      else
        red "FAIL: src/kernel/sh_run_iter.ml{,i} is stale vs sh_jpl_run.v extraction"
        red "      re-run: cp sh_run_iter.ml sh_run_iter.mli ../../src/kernel/  (after coqc sh_extract_iter.v)"
        FAIL=$((FAIL + 1))
      fi
      if ocamlc -w -a -o sh_run_iter_parity sh_run_iter.mli sh_run_iter.ml sh_run_iter_parity.ml >/dev/null 2>&1; then
        if EX_OUT="$(./sh_run_iter_parity 2>&1)" && echo "$EX_OUT" | grep -q "passed successfully"; then
          echo "$EX_OUT" | tail -4
          green "PASS: iterative OCaml mloop agrees with run and the verified Coq model"
          PASS=$((PASS + 1))
        else
          red "FAIL: iterative OCaml mloop disagrees with run / the Coq model"
          echo "$EX_OUT" | grep -i "fail" | head -20
          FAIL=$((FAIL + 1))
        fi
      else
        red "FAIL: OCaml build of the iterative fidelity harness failed (sh_run_iter_parity.ml)"
        FAIL=$((FAIL + 1))
      fi
    else
      red "FAIL: iterative extraction step failed (sh_extract_iter.v -> sh_jpl_run.vo)"
      FAIL=$((FAIL + 1))
    fi
  fi
  echo

  # ── 2c. Clean bounded kernel (JPL target settings): phase3 -> OCaml mrun ──
  # sh_extract_jpl_c.v is the only extraction that asks for the representation the
  # JPL.5 emitter will consume: ExtrOcamlNatInt (nat -> machine int, provably
  # <= MAX_FUEL so the word cannot wrap) plus primitive hooks for
  # Nat.div/modulo/divmod/sub/max (unhooked they extract as stdlib recursion — a Rule 6
  # violation nothing warns about; Nat.max matters because the branch guard's
  # branch_need calls it once per pattern).  Its root `mrun` takes no phi function, so the
  # emitted driver carries no functional argument.  The harness services the DEff
  # seam with a closure-free OCaml host and asserts mrun+host == run == the literal.
  bold "==> Clean-kernel extraction fidelity (sh_jpl_run_phase3.v + sh_jpl_run_c.v -> OCaml mrun/mrun_c)"
  if ! command -v coqc >/dev/null 2>&1 || ! command -v ocamlc >/dev/null 2>&1; then
    red "FAIL: clean-kernel extraction needs both coqc and ocamlc"
    FAIL=$((FAIL + 1))
  else
    if coqc sh_concrete.v >/dev/null 2>&1 && coqc sh_jpl.v >/dev/null 2>&1 \
       && coqc sh_jpl_run.v >/dev/null 2>&1 && coqc sh_jpl_scan.v >/dev/null 2>&1 \
       && coqc sh_jpl_run_phase2.v >/dev/null 2>&1 \
       && coqc sh_jpl_run_phase3.v >/dev/null 2>&1 \
       && coqc sh_jpl_run_c.v >/dev/null 2>&1 \
       && coqc sh_extract_jpl_c.v >/dev/null 2>&1; then
      # Anti-rot: src/kernel/sh_run_c.ml{,i} is the vendored third artifact.  It is
      # the file JPL.5 lowers, so a stale copy here would mean emitting from code
      # that drifted from phase3/scan (the sources of truth).
      VEND=../../src/kernel
      if [[ -f "$VEND/sh_run_c.ml" && -f "$VEND/sh_run_c.mli" ]] \
         && diff -q sh_run_c.ml "$VEND/sh_run_c.ml" >/dev/null \
         && diff -q sh_run_c.mli "$VEND/sh_run_c.mli" >/dev/null; then
        green "PASS: vendored src/kernel/sh_run_c.ml is identical to fresh extraction"
      else
        red "FAIL: src/kernel/sh_run_c.ml{,i} is stale vs sh_extract_jpl_c.v extraction"
        red "      re-run: cp sh_run_c.ml sh_run_c.mli ../../src/kernel/  (after coqc sh_extract_jpl_c.v)"
        FAIL=$((FAIL + 1))
      fi
      if ocamlc -w -a -o sh_run_c_parity sh_run_c.mli sh_run_c.ml sh_run_c_parity.ml >/dev/null 2>&1; then
        if EX_OUT="$(./sh_run_c_parity 2>&1)" && echo "$EX_OUT" | grep -q "passed successfully"; then
          echo "$EX_OUT" | tail -4
          green "PASS: clean OCaml mrun+host AND rewired mrun_c+host agree with run and the verified Coq model"
          PASS=$((PASS + 1))
        else
          red "FAIL: clean OCaml mrun/mrun_c + host disagree with run / the Coq model"
          echo "$EX_OUT" | grep -i "fail" | head -20
          FAIL=$((FAIL + 1))
        fi
      else
        red "FAIL: OCaml build of the clean-kernel fidelity harness failed (sh_run_c_parity.ml)"
        FAIL=$((FAIL + 1))
      fi
    else
      red "FAIL: clean-kernel extraction step failed (sh_extract_jpl_c.v -> sh_jpl_run_phase3.vo)"
      FAIL=$((FAIL + 1))
    fi
  fi
  echo
else
  bold "==> Extraction step skipped"
  echo
fi

# ── 2d. Emitter front end (JPL.5-B.1): the shipped closure is in the subset ─
# This rung reads the VENDORED artifact that block 2c byte-binds to a fresh
# Extraction, so it checks exactly the bytes the proofs describe.  It needs no
# Rocq toolchain, only ocamlfind + compiler-libs.common, so it runs even under
# --skip-coq; if the OCaml toolchain is absent the rung is recorded SKIP, which
# is neither a pass nor a failure (see the summary line).
bold "==> Emitter front end (JPL.5-B.1)"
FRONT="$ROOT/../c/jpl_front.sh"
if [[ ! -f "$FRONT" ]]; then
  red "FAIL: verify/c/jpl_front.sh is missing"
  FAIL=$((FAIL + 1))
elif ! command -v ocamlfind >/dev/null 2>&1 || ! ocamlfind query compiler-libs.common >/dev/null 2>&1; then
  skip "SKIP: emitter front end needs ocamlfind + compiler-libs.common (not installed here)"
  SKIP=$((SKIP + 1))
else
  if FRONT_OUT="$("$FRONT" 2>&1)"; then
    echo "$FRONT_OUT"
    green "PASS: shipped closure is inside the emitter's declared subset and closure.txt is current"
    PASS=$((PASS + 1))
  else
    FRONT_STATUS=$?
    echo "$FRONT_OUT"
    case $FRONT_STATUS in
      1) red "FAIL: subset violation or stale closure.txt — the fix belongs in the Rocq source,"
         red "      never in a silent fallback inside the emitter (verify/c/jpl_front.ml)"
         FAIL=$((FAIL + 1)) ;;
      *) red "FAIL: emitter front end could not run (exit $FRONT_STATUS)"
         FAIL=$((FAIL + 1)) ;;
    esac
  fi
fi
echo

# 2d-negative: the same tool, pointed at the ORACLE roots (run/step/mrun — the
# recursive cluster kept only to witness equality), MUST refuse.  This is the
# measurement behind §9.2's decision 1: the mutual expand/expand_name/
# expand_brace fixpoint is in the oracle's closure and not in the kernel's, so
# Rule 6 (no recursion) can only bind the shipped roots.  A lint that accepts
# everything is not a gate, so the gate asserts the refusal too.
bold "==> Emitter front end, negative control (oracle roots must be refused)"
if [[ -f "$FRONT" ]] && command -v ocamlfind >/dev/null 2>&1 \
   && ocamlfind query compiler-libs.common >/dev/null 2>&1; then
  if NEG_OUT="$(JPL_ROOTS=run,step,mrun "$FRONT" 2>&1)"; then
    echo "$NEG_OUT"
    red "FAIL: the front end ACCEPTED the oracle closure — the subset check has no teeth"
    red "      (the oracle reaches the mutual expand fixpoint, which JPL.5 cannot lower)"
    FAIL=$((FAIL + 1))
  else
    if echo "$NEG_OUT" | grep -q "expand_name"; then
      echo "$NEG_OUT" | grep -E "OFF-SUBSET|SUBSET VIOLATION"
      green "PASS: oracle closure refused — the subset verdict is root-sensitive, as JPL.6's lint must be"
      PASS=$((PASS + 1))
    else
      echo "$NEG_OUT"
      red "FAIL: the oracle roots were refused, but not for the documented reason (mutual fixpoint)"
      FAIL=$((FAIL + 1))
    fi
  fi
else
  skip "SKIP: negative control needs ocamlfind + compiler-libs.common"
  SKIP=$((SKIP + 1))
fi
echo

# ── 2e. Representation layer (JPL.5-B.2): the C99 type layer, derived ──────
# The emitter writes the types the shipped closure lowers into, sizes every pool
# from the artifact's own cap table, and puts a C99 compile-time assertion after
# every struct.  This rung therefore checks four things the proofs cannot:
# that the emission is repeatable byte-for-byte, that the emitted header is
# VALID C99 under the JPL flag set (so no sizeof in it is a guess), that the
# syntactic cap fold agrees with the artifact EVALUATED by the OCaml runtime
# (two independent readings of one extracted term), and that the vendored
# evidence has not drifted.  Like 2d it needs no Rocq toolchain.
bold "==> Representation layer (JPL.5-B.2): emit, compile, differential-fold, byte-compare"
EMIT="$ROOT/../c/jpl_emit.sh"
if [[ ! -f "$EMIT" ]]; then
  red "FAIL: verify/c/jpl_emit.sh is missing"
  FAIL=$((FAIL + 1))
elif ! command -v ocamlfind >/dev/null 2>&1 || ! ocamlfind query compiler-libs.common >/dev/null 2>&1; then
  skip "SKIP: representation layer needs ocamlfind + compiler-libs.common (not installed here)"
  SKIP=$((SKIP + 1))
elif [[ ! -x "${CC:-/usr/bin/clang}" ]]; then
  skip "SKIP: representation layer needs a C99 compiler (CC=${CC:-/usr/bin/clang} not executable)"
  SKIP=$((SKIP + 1))
else
  if EMIT_OUT="$("$EMIT" 2>&1)"; then
    # The runner colours its own lines, so the ANSI escapes are stripped before
    # anchoring on ^: a coloured PASS would otherwise not match and, under
    # `set -o pipefail`, an unmatched grep here would abort the whole gate.
    EMIT_PLAIN="$(printf '%s\n' "$EMIT_OUT" | sed 's/\x1b\[[0-9;]*m//g')"
    printf '%s\n' "$EMIT_PLAIN" | grep '^PASS:' | sed 's/^/    /' || true
    # Both numbers are the evidence's own, read out of the vendored report rather than
    # restated here: the emitter's FUNCTIONS AND VALUES block counts the polymorphic
    # bindings it refuses to instantiate (R8), and its pool table leaves the word slab
    # with no dimension because no LOCKED cap is the capacity of a live word.
    PENDING_N="$(awk '/^  PENDING /{print $2}' "$ROOT/../c/layout.txt")"
    printf '    %s polymorphic bindings are PENDING (no monomorphization yet), and the\n' \
      "${PENDING_N:-0}"
    printf '      word slab is declared without a capacity: what this layer could not\n'
    printf '      derive is recorded in verify/c/layout.txt, not hidden (see its\n'
    printf '      "WHAT THIS LAYER COULD NOT SIZE" section)\n'
    green "PASS: the C99 type layer is derived from the artifact, compiles under the JPL flag set, and its caps match the evaluated kernel"
    PASS=$((PASS + 1))
  else
    EMIT_STATUS=$?
    echo "$EMIT_OUT"
    case $EMIT_STATUS in
      1) red "FAIL: the representation layer refused the artifact or its evidence is stale —"
         red "      the fix belongs in the Rocq source or in the rule, never in a fallback here"
         FAIL=$((FAIL + 1)) ;;
      *) red "FAIL: the representation layer could not run (toolchain)"
         FAIL=$((FAIL + 1)) ;;
    esac
  fi
fi
echo

# 2e-negative: the same emitter, pointed at the ORACLE roots, MUST refuse, and for
# the documented reason: the oracle's driver is a FUNCTION value (run_phi), which is
# exactly what JPL.5-A.4 replaced with a data driver.  A layout tool that would emit
# anything for a higher-order value is not a gate, so the refusal is asserted too.
bold "==> Representation layer, negative control (oracle roots must be refused)"
if [[ -f "$EMIT" ]] && command -v ocamlfind >/dev/null 2>&1 \
   && ocamlfind query compiler-libs.common >/dev/null 2>&1 && [[ -x "${CC:-/usr/bin/clang}" ]]; then
  if NEG_E_OUT="$(JPL_ROOTS=run,step,mrun "$EMIT" 2>&1)"; then
    echo "$NEG_E_OUT"
    red "FAIL: the emitter LAID OUT the oracle closure — a function-typed value reached a C type,"
    red "      which JPL.5-A.4's phi-as-data rewrite is supposed to make impossible"
    FAIL=$((FAIL + 1))
  else
    if echo "$NEG_E_OUT" | grep -q "function-typed value has no layout"; then
      echo "$NEG_E_OUT" | grep -E "FAIL:|FATAL" | sed 's/^/    /' || true
      green "PASS: oracle roots refused — the layout layer is root-sensitive, for the phi-is-a-function reason"
      PASS=$((PASS + 1))
    else
      echo "$NEG_E_OUT"
      red "FAIL: the oracle roots were refused, but not for the documented reason (a function-typed value)"
      FAIL=$((FAIL + 1))
    fi
  fi
else
  skip "SKIP: representation-layer negative control needs ocamlfind + compiler-libs.common + a C99 cc"
  SKIP=$((SKIP + 1))
fi
echo

if [[ $SKIP -gt 0 ]]; then
  bold "==> Summary: $PASS passed, $FAIL failed, $SKIP skipped (a skip is not a pass)"
else
  bold "==> Summary: $PASS passed, $FAIL failed"
fi
if [[ "$FAIL" -gt 0 ]]; then
  exit 1
fi

rm -f .lia.cache
rm -f .nia.cache
rm -f *.vo *.vok *.vos
rm -f *.cmi *.cmo *.cma
rm -f *.glob
rm -f sh_run_parity sh_run_iter_parity sh_run_c_parity
rm -f .*.aux
# extraction output is a derived artifact — never kept in the tree
rm -f sh_run.ml sh_run.mli
rm -f sh_run_iter.ml sh_run_iter.mli
rm -f sh_run_c.ml sh_run_c.mli

exit 0
