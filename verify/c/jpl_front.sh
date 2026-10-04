#!/usr/bin/env bash
# jpl_front.sh — run the JPL.5 emitter front end over the vendored extraction.
#
# What it proves, in one line: the code the shipped kernel is made of
# (mrun_c + step_c and everything they reach) uses only the OCaml constructs
# JPL.5 is specified to lower, and the inventory of what that closure allocates
# and which types it needs is recorded in closure.txt.
#
# Inputs are the VENDORED artifact (src/kernel/sh_run_c.ml{,i}), which block 2c of
# verify_models.sh already binds byte-for-byte to a fresh Coq Extraction — so this
# runs on exactly the bytes the proofs describe, not on a second copy.
#
# Exit codes
#   0  subset OK and closure.txt current
#   1  subset VIOLATION (the emitter must not run; fix the Rocq source)
#   2  usage / toolchain problem
#
# Regenerate the evidence deliberately:  JPL_REGEN=1 ./jpl_front.sh

set -u -o pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
# Run from the repo root so the report records RELATIVE paths: closure.txt is
# kept in the tree and byte-compared, and an absolute path in it would make the
# evidence machine-specific.
REPO="$(cd "$HERE/../.." && pwd)"
cd "$REPO" || exit 2
# The file operations use $HERE so the script works from any cwd, but every PRINTED
# path is repo-relative: an absolute path in the gate output would make the evidence
# machine-specific, which is the same reason the report's INPUT lines are relative.
EVID="$HERE/closure.txt"
EVID_REL="${EVID#"$REPO"/}"
ML="src/kernel/sh_run_c.ml"
MLI="src/kernel/sh_run_c.mli"
ROOTS="${JPL_ROOTS:-mrun_c,step_c}"

green() { printf '\033[32m%s\033[0m\n' "$*"; }
red()   { printf '\033[31m%s\033[0m\n' "$*"; }
bold()  { printf '\033[1m%s\033[0m\n' "$*"; }

if ! command -v ocamlfind >/dev/null 2>&1 || ! ocamlfind query compiler-libs.common >/dev/null 2>&1; then
  red "FAIL: the emitter front end needs opam/ocamlfind with the compiler-libs.common package"
  exit 2
fi
if [[ ! -f "$ML" || ! -f "$MLI" ]]; then
  red "FAIL: $ML / $MLI not found — run verify_models.sh first (it vendors the extraction)"
  exit 2
fi

# The build products go to a scratch directory and are removed on exit; nothing
# but the report is ever written into the tree.  This needs care: ocamlopt puts
# .cmi/.cmx/.o NEXT TO THE SOURCE FILE, so compiling "$HERE/jpl_ast.ml" by absolute
# path would drop build artifacts into verify/c — which is exactly what an earlier
# version of this runner did.  The build therefore happens in $BUILD with relative
# source names and cwd = $BUILD.  jpl_ast.ml compiles FIRST because jpl_front.ml
# opens Jpl_ast: the emitter (jpl_emit.ml, 5-B.2) is built against the same reader,
# one reader and two consumers rather than two AST walks.
BUILD="$(mktemp -d)"
trap 'rm -rf "$BUILD"' EXIT

bold "==> building jpl_ast.ml + jpl_front.ml (compiler-libs)"
if ! ( cd "$BUILD" \
       && cp "$HERE/jpl_ast.ml" "$HERE/jpl_front.ml" . \
       && ocamlfind ocamlopt -package compiler-libs.common -linkpkg \
            -o jpl_front jpl_ast.ml jpl_front.ml > build.log 2>&1 ); then
  red "FAIL: the emitter front end did not build"
  cat "$BUILD/build.log"
  exit 2
fi

bold "==> emitter front end: roots = $ROOTS"
"$BUILD/jpl_front" "$ML" "$MLI" "$ROOTS" > "$BUILD/report.txt"
STATUS=$?
# The full inventory lives in closure.txt; the terminal shows the identity of the
# run, the verdict, and the per-binding table header — enough to read a failure
# without burying the gate in 200 lines of output.
{ head -n 6 "$BUILD/report.txt"
  awk '/^==== SUBSET VERDICT/,/^SUBSET (OK|VIOLATION)/' "$BUILD/report.txt"
} | sed 's/^/    /'
if [[ $STATUS -ne 0 ]]; then
  red "FAIL: the closure from these roots is OUTSIDE the emitter's subset (exit $STATUS)"
  red "      grep the report above for OFF-SUBSET; the fix belongs in the Rocq source,"
  red "      not in a fallback inside the emitter."
  exit 1
fi
green "PASS: shipped closure is inside the emitter's subset"

if [[ "${JPL_REGEN:-0}" == "1" ]]; then
  cp "$BUILD/report.txt" "$EVID"
  green "PASS: regenerated $EVID_REL"
  exit 0
fi

if [[ ! -f "$EVID" ]]; then
  red "FAIL: $EVID_REL missing — generate it with: JPL_REGEN=1 $0"
  exit 1
fi
if diff -q "$EVID" "$BUILD/report.txt" > /dev/null; then
  green "PASS: $EVID_REL is identical to a fresh run over the vendored artifact"
  exit 0
fi
red "FAIL: $EVID_REL is stale vs the current artifact (the closure moved)"
diff -u "$EVID" "$BUILD/report.txt" | head -40
red "      re-run with JPL_REGEN=1 after checking the change is intended"
exit 1
