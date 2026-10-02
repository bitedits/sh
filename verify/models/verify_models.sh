#!/usr/bin/env bash
# verify_models.sh — integration check for the POSIX shell verifiable model
#
# Covers:
#   - sh_model.ml        (OCaml oracle: tokenize -> parse -> fuel-bounded exec, full test coverage)
#   - sh_properties.v    (Rocq/Coq relational semantics + main shell theorems, axiom-free)
#   - sh_concrete.v      (Rocq/Coq concrete POSIX model: text/env/expansion/glob/control flow)
#   - sh_extract.v       (Coq Extraction of the concrete run -> OCaml sh_run.ml) +
#                        sh_run_parity.ml (fidelity harness: derived OCaml == kernel-verified Coq)
#
# Usage:
#   ./verify_models.sh
#   ./verify_models.sh --skip-coq          # OCaml oracle only (skips Coq + extraction)
#   ./verify_models.sh --skip-ocaml        # Coq + extraction only
#   ./verify_models.sh --skip-extract      # oracle + Coq properties, but no extraction step
# Exit 0 only if all selected checks pass.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

SKIP_OCAML=0
SKIP_COQ=0
SKIP_EXTRACT=0
for arg in "$@"; do
  case "$arg" in
    --skip-ocaml)   SKIP_OCAML=1 ;;
    --skip-coq)     SKIP_COQ=1; SKIP_EXTRACT=1 ;;
    --skip-extract) SKIP_EXTRACT=1 ;;
    -h|--help)
      sed -n '1,16p' "$0"
      exit 0
      ;;
  esac
done

OCAML_MODELS=("sh_model.ml")
COQ_PROPERTIES=("sh_properties.v" "sh_concrete.v")
PASS=0
FAIL=0

green() { printf '\033[32m%s\033[0m\n' "$*"; }
red()   { printf '\033[31m%s\033[0m\n' "$*"; }
bold()  { printf '\033[1m%s\033[0m\n' "$*"; }

# ── 1. OCaml executable oracle ─────────────────────────────────────
if [[ "$SKIP_OCAML" -eq 0 ]]; then
  for m in "${OCAML_MODELS[@]}"; do
    bold "==> OCaml model ($m)"
    bin="${m%.ml}"
    if command -v ocamlc >/dev/null 2>&1; then
      ocamlc -o "$bin" "$m"
      OUT="$("./$bin" 2>&1)" || true
    elif command -v ocaml >/dev/null 2>&1; then
      OUT="$(ocaml "$m" 2>&1)" || true
    else
      red "FAIL: ocaml/ocamlc not found"
      FAIL=$((FAIL + 1))
      continue
    fi
    echo "$OUT" | tail -8
    if echo "$OUT" | grep -qi "passed"; then
      green "PASS: OCaml oracle ($m)"
      PASS=$((PASS + 1))
    else
      red "FAIL: OCaml oracle ($m) failed invariant checks"
      FAIL=$((FAIL + 1))
    fi
    echo
  done
else
  bold "==> OCaml skipped"
  echo
fi

# ── 2. Rocq / Coq formal properties ────────────────────────────────
if [[ "$SKIP_COQ" -eq 0 ]]; then
  if ! command -v coqc >/dev/null 2>&1; then
    red "FAIL: coqc not found (install Rocq/Coq or use --skip-coq)"
    FAIL=$((FAIL + 1))
  else
    for p in "${COQ_PROPERTIES[@]}"; do
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
    done
  fi
else
  bold "==> Coq skipped"
  echo
fi

# ── 3. Coq Extraction -> OCaml, fidelity against the kernel-verified model ──
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
    if coqc sh_concrete.v >/dev/null 2>&1 && coqc sh_extract.v >/dev/null 2>&1 \
       && ocamlc -w -a -o sh_run_parity sh_run.mli sh_run.ml sh_run_parity.ml >/dev/null 2>&1; then
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
      red "FAIL: extraction or OCaml build step failed (sh_extract.v / sh_run_parity.ml)"
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
rm -f sh_model sh_run_parity
rm -f .*.aux
# extraction output is a derived artifact — never kept in the tree
rm -f sh_run.ml sh_run.mli

exit 0
