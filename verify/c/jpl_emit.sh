#!/usr/bin/env bash
# jpl_emit.sh — run the JPL.5-B.2 representation-layer emitter over the vendored
# extraction, COMPILE the header it writes, and check its numbers against the
# artifact EVALUATED by the OCaml runtime.
#
# Four checks, in this order:
#   1  the emitter runs on the shipped closure and writes a header
#   2  the header compiles clean under the JPL C99 flag set.  Every struct in it
#      is followed by a `typedef char jpl_check_<name>_is_<N>` whose array size
#      is -1 unless sizeof agrees, so a wrong byte count — padding, a mis-sized
#      pool element, a cap that drifted — fails HERE, in the compiler, and not
#      in a comment.  C99 has no _Static_assert (that is C11), so this is the
#      conforming form of the same check.
#   3  the differential fold: the ten capacities the emitter folded out of the
#      artifact's SYNTAX agree with the ten fields of jpl_caps_table as the
#      OCaml runtime EVALUATES them.  Those are two independent readings of the
#      same extracted term — a constant folder and the interpreter — so their
#      agreement is the measurement that retires "the folder is right by
#      construction".  The probe carries no numbers of its own.
#   4  the vendored evidence (sh_run_jpl.h + layout.txt) is byte-identical to
#      this run.
#
# Inputs are the VENDORED artifact (src/kernel/sh_run_c.ml{,i}) that block 2c of
# verify_models.sh already byte-binds to a fresh Coq Extraction, and the same
# roots the front end (2d) gates, so this layer describes exactly the code the
# subset verdict covers.
#
# Exit codes
#   0  all four checks pass
#   1  a check failed (violation: fix the Rocq source or the rule, never a fallback here)
#   2  usage / toolchain problem
#
# Regenerate the evidence deliberately:  JPL_REGEN=1 ./jpl_emit.sh

set -u -o pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
cd "$REPO" || exit 2
# Every PRINTED path is repo-relative, so the vendored evidence is not
# machine-specific (the same reason jpl_front.sh runs from the repo root).
ML="src/kernel/sh_run_c.ml"
MLI="src/kernel/sh_run_c.mli"
HDR="$HERE/sh_run_jpl.h"
EVID="$HERE/layout.txt"
ROOTS="${JPL_ROOTS:-mrun_c,step_c}"
# -fsyntax-only: the header declares the pools as extern, so nothing here needs a
# translation unit that defines them; JPL.5-B.3 supplies that.
CC="${CC:-/usr/bin/clang}"
CFLAGS="-std=c99 -Wall -Wextra -Wconversion -Wsign-conversion -pedantic -Werror -fsyntax-only"

green() { printf '\033[32m%s\033[0m\n' "$*"; }
red()   { printf '\033[31m%s\033[0m\n' "$*"; }
bold()  { printf '\033[1m%s\033[0m\n' "$*"; }

if ! command -v ocamlfind >/dev/null 2>&1 || ! ocamlfind query compiler-libs.common >/dev/null 2>&1; then
  red "FAIL: the emitter needs opam/ocamlfind with the compiler-libs.common package"
  exit 2
fi
if [[ ! -x "$CC" ]]; then
  red "FAIL: no C99 compiler at $CC (set CC=...)"
  exit 2
fi
if [[ ! -f "$ML" || ! -f "$MLI" ]]; then
  red "FAIL: $ML / $MLI not found — run verify_models.sh first (it vendors the extraction)"
  exit 2
fi

# Build products go to a scratch directory and are removed on exit: ocamlopt puts
# .cmi/.cmx/.o next to the SOURCE, so building in the tree would drop artifacts
# into verify/c.
BUILD="$(mktemp -d)"
trap 'rm -rf "$BUILD"' EXIT

bold "==> building jpl_ast.ml + jpl_emit.ml (compiler-libs)"
if ! ( cd "$BUILD" \
       && cp "$HERE/jpl_ast.ml" "$HERE/jpl_emit.ml" . \
       && ocamlfind ocamlopt -package compiler-libs.common -linkpkg \
            -o jpl_emit jpl_ast.ml jpl_emit.ml > build.log 2>&1 ); then
  red "FAIL: the emitter did not build"
  cat "$BUILD/build.log"
  exit 2
fi

bold "==> representation layer: roots = $ROOTS"
# The roots are passed through, exactly as jpl_front.sh does: which bindings the
# layout covers is a parameter, not a convention, so the negative control can
# point the same tool at the oracle cluster.
if ! "$BUILD/jpl_emit" "$ML" "$MLI" "$BUILD/sh_run_jpl.h" "$ROOTS" > "$BUILD/layout.txt" 2>&1 \
     || [[ ! -s "$BUILD/sh_run_jpl.h" ]]; then
  sed 's/^/    /' "$BUILD/layout.txt"
  red "FAIL: the emitter could not lay out this artifact (see its message above)"
  exit 1
fi
green "PASS: emitted $(grep -c '^typedef\|^#define' "$BUILD/sh_run_jpl.h") typedefs and macros from $(wc -l < "$BUILD/layout.txt" | tr -d ' ') report lines"

bold "==> check 2: the emitted header under $CFLAGS"
# shellcheck disable=SC2086
if "$CC" $CFLAGS "$BUILD/sh_run_jpl.h" 2> "$BUILD/clang.log"; then
  green "PASS: every sizeof and every cap relation in the header is a C99 compile-time assertion, and they hold"
else
  red "FAIL: the emitted header does not compile — a layout claim is wrong"
  sed 's/^/    /' "$BUILD/clang.log"
  exit 1
fi

bold "==> check 3: the folded caps vs the artifact evaluated by the OCaml runtime"
# probe_caps.ml reads the ten fields of the artifact's OWN jpl_caps_table record
# and prints them.  Names come from the record; values come from the runtime, so
# this is the second, independent reading of the same extracted term.
cp "$ML" "$MLI" "$BUILD"
cat > "$BUILD/probe_caps.ml" <<'PROBE'
let () =
  let t = Sh_run_c.jpl_caps_table in
  List.iter (fun (n, v) -> Printf.printf "%s %d\n" n v)
    [ ("jpl_width", t.jpl_width); ("jpl_word", t.jpl_word);
      ("jpl_argv", t.jpl_argv); ("jpl_env", t.jpl_env);
      ("jpl_list", t.jpl_list); ("jpl_cmd", t.jpl_cmd);
      ("jpl_stack", t.jpl_stack); ("jpl_words", t.jpl_words);
      ("jpl_glob_fuel", t.jpl_glob_fuel); ("jpl_fuel", t.jpl_fuel) ]
PROBE
if ! ( cd "$BUILD" \
       && ocamlfind ocamlopt -w -a -o probe_caps sh_run_c.mli sh_run_c.ml probe_caps.ml \
            > probe_build.log 2>&1 ); then
  red "FAIL: the differential probe did not build against the artifact"
  cat "$BUILD/probe_build.log"
  exit 2
fi
"$BUILD/probe_caps" | sort > "$BUILD/runtime_caps.txt"
# layout.txt's CAPACITIES section lists, per row: artifact record field, model
# name, C macro, the folded value.  Pairing is BY NAME, so the check does not
# assume the two readings enumerate the table in the same order.
awk '/^==== CAPACITIES/,/^$/' "$BUILD/layout.txt" \
  | awk '$1 ~ /^jpl_/ && NF > 3' > "$BUILD/caprows.txt"
awk '{print $1, $4}' "$BUILD/caprows.txt" | sort > "$BUILD/folded_pairs.txt"
if [[ "$(wc -l < "$BUILD/caprows.txt" | tr -d ' ')" != "10" ]]; then
  red "FAIL: the report lists $(wc -l < "$BUILD/caprows.txt" | tr -d ' ') capacities, not the ten of jpl_caps_table"
  exit 1
fi
if ! diff -q "$BUILD/runtime_caps.txt" "$BUILD/folded_pairs.txt" > /dev/null; then
  red "FAIL: the constant folder disagrees with the OCaml runtime on the cap table"
  diff -u "$BUILD/runtime_caps.txt" "$BUILD/folded_pairs.txt"
  exit 1
fi
# and the header must carry those same numbers under those same macros: the
# report, the header and the runtime have to be one story, not three.
while read -r macro value; do
  if ! grep -q "^#define ${macro} ${value}u" "$BUILD/sh_run_jpl.h"; then
    red "FAIL: $macro = $value is in the report but not in the header"
    exit 1
  fi
done < <(awk '{print $3, $4}' "$BUILD/caprows.txt")
green "PASS: ten capacities agree across the fold, the runtime and the header:"
sed 's/^/    /' "$BUILD/runtime_caps.txt"

bold "==> check 4: the vendored evidence"
if [[ "${JPL_REGEN:-0}" == "1" ]]; then
  cp "$BUILD/sh_run_jpl.h" "$HDR"
  cp "$BUILD/layout.txt" "$EVID"
  green "PASS: regenerated ${HDR#"$REPO"/} and ${EVID#"$REPO"/}"
  exit 0
fi
if [[ ! -f "$HDR" || ! -f "$EVID" ]]; then
  red "FAIL: ${HDR#"$REPO"/} or ${EVID#"$REPO"/} missing — generate with: JPL_REGEN=1 $0"
  exit 1
fi
STALE=0
if ! diff -q "$HDR" "$BUILD/sh_run_jpl.h" > /dev/null; then
  red "FAIL: ${HDR#"$REPO"/} is stale vs a fresh emission"
  diff -u "$HDR" "$BUILD/sh_run_jpl.h" | head -40
  STALE=1
fi
if ! diff -q "$EVID" "$BUILD/layout.txt" > /dev/null; then
  red "FAIL: ${EVID#"$REPO"/} is stale vs a fresh run over the vendored artifact"
  diff -u "$EVID" "$BUILD/layout.txt" | head -40
  STALE=1
fi
if [[ $STALE -ne 0 ]]; then
  red "      re-run with JPL_REGEN=1 after checking the change is intended"
  exit 1
fi
green "PASS: the header and the layout report are identical to a fresh emission"

bold "==> what this layer still cannot do"
# Read straight off the report, so the limitation is the tool's own statement and
# not a claim written into a shell script.
awk '/^==== WHAT THIS LAYER COULD NOT SIZE/{f=1;next} /^==== /{f=0} f' \
  "$BUILD/layout.txt" | sed 's/^/    /'
printf '    %s report lines are marked PENDING\n' \
  "$(grep -c PENDING "$BUILD/layout.txt")"
exit 0
