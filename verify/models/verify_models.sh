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
#   - sh_extract.v       (Coq Extraction of the concrete run -> OCaml sh_run.ml) +
#                        sh_run_parity.ml (fidelity harness: derived OCaml == kernel-verified Coq)
#   - sh_extract_iter.v  (Coq Extraction of the JPL-shaped iterative kernel — the non-recursive
#                        step dispatcher + tail driver mloop, alongside run so the module shares
#                        one set of datatypes -> OCaml sh_run_iter.ml, vendored as src/kernel's
#                        2nd artifact) + sh_run_iter_parity.ml (re-runs the 26 §7-§9 facts through
#                        mloop and asserts mloop == run == the verified literal: isomorphism)
#   - sh_jpl_scan.v      (Rocq/Coq JPL.5-A.1 bounded-word foundation for the clean extraction:
#                        the bt = bword layer with saturating bt_push/bt_append and the
#                        emitter-lowerable scans kept single-source (bt_eq = teqb), plus
#                        saturation proofs and byte-agreement Examples anchoring later re-extract
#                        fidelity; axiom-free, built alongside sh_jpl, not yet consumed by the machine)
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
      sed -n '1,38p' "$SELF"
      exit 0
      ;;
  esac
done

COQ_PROPERTIES=("sh_properties.v" "sh_concrete.v" "sh_jpl.v" "sh_jpl_run.v" "sh_jpl_scan.v")
# JPL.3b: the two-sided machine equivalence lives in its own module, which
# Require Imports sh_jpl_run (so it must be compiled after it).
COQ_PHASE2=("sh_jpl_run_phase2.v")
PASS=0
FAIL=0

green() { printf '\033[32m%s\033[0m\n' "$*"; }
red()   { printf '\033[31m%s\033[0m\n' "$*"; }
bold()  { printf '\033[1m%s\033[0m\n' "$*"; }

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
    for p in "${COQ_PROPERTIES[@]}" "${COQ_PHASE2[@]}"; do
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
else
  bold "==> Extraction step skipped"
  echo
fi

bold "==> Summary: $PASS passed, $FAIL failed"
if [[ "$FAIL" -gt 0 ]]; then
  exit 1
fi

rm -f .lia.cache
rm -f *.vo *.vok *.vos
rm -f *.cmi *.cmo *.cma
rm -f *.glob
rm -f sh_run_parity sh_run_iter_parity
rm -f .*.aux
# extraction output is a derived artifact — never kept in the tree
rm -f sh_run.ml sh_run.mli
rm -f sh_run_iter.ml sh_run_iter.mli

exit 0
