#!/usr/bin/env bash
# jpl_lower.sh — run the JPL.5-B.3a lowering census and the 5-B.3b-i ABI rendering over
# the vendored extraction, and gate what they produce.
#
# 5-B.3a is a MEASUREMENT, not a translation: it decides, before any C body is emitted,
# which lowering schema each shipped binding has, which R8 instances the call sites
# actually close, and which pools the closure demands.  5-B.3b-i renders the declaration
# half of what that measurement found — the closed R8 instances as a C ABI header.  It
# emits prototypes and nothing else: §6.3's loop-body schema has not landed, and three of
# the instances this header declares are owed a model-side rewrite before they can have a
# body.  Six checks, in this order:
#   1  the census runs on the shipped closure and writes both artifacts (a refusal here is
#      a finding about the model, never something this script works around)
#   2  the three counts a lowering cannot absorb are asserted at zero, read from the
#      report's own SUMMARY keys rather than from its prose:
#        function_value_sites_unnamed  a function value in no position a rule covers
#                                      would have to become a function pointer, which
#                                      D-60411 forbids outright
#        unknown_site_classes          a site the census could not type has no
#                                      representation, so no pool follows from it
#        self_reference_mismatches     this walk's per-binding self-call count vs the
#                                      shared reader's, over the same bytes — a
#                                      disagreement means no count here measures the
#                                      artifact
#   3  the pool cross-check, in the one direction that can break a build: every pool the
#      census DEMANDS must be a pool the representation layer DECLARED in sh_run_jpl.h.
#      The reverse difference is a finding and not a failure — §6.2's decision 1 pools
#      some values this walk derives no cell from, and `frame` is exactly that case.
#   4  the ABI is exactly the closed instance set, which the report's own SUMMARY keys have
#      to close arithmetically before any of it is worth compiling:
#        abi_instances == instances_closed
#        abi_prototypes + abi_refused_no_c_type == abi_instances
#        abi_bodies_expressible + abi_bodies_owed == abi_prototypes
#      and the header must carry that many declarations, that many refusal comments, and
#      that many declaration-only comments — the file is compared to the measurement that
#      produced it, not to an expectation written here.  abi_blocked_outside_fold_set == 0
#      is the assertion: a refusal that §6.3 assigns to no owner has nobody to fix it.  A
#      refusal that DOES have an owner is printed as a finding, not failed, because
#      refusing an instance whose argument is function-typed is the conformant answer —
#      the alternative would be to invent the function pointer D-60411 forbids.
#   5  the ABI header compiles against the representation header under 2e's own flags.
#      This is the rung that turns the shared value-naming rule (jpl_ast.ml's value_name,
#      which jpl_emit.ml now uses for the typedefs and the census uses for the prototypes)
#      from a convention into a checked claim: a type name the ABI invented would not
#      resolve, and a prototype whose parameters disagree with the layout layer would not
#      pass -Wconversion.
#   6  the vendored evidence (lowering.txt AND sh_run_jpl_abi.h) is byte-identical to this
#      run.
#
# Inputs are the VENDORED artifact (src/kernel/sh_run_c.ml{,i}) that block 2c of
# verify_models.sh already byte-binds to a fresh Coq Extraction, and the same roots the
# front end (2d) and the layout layer (2e) gate, so all three rungs describe one closure.
# The census reads the capacities out of the artifact's own jpl_caps_table through the
# shared reader (jpl_ast.ml), which is why it reports the numbers the header was built
# from instead of a second copy of them.
#
# Exit codes
#   0  all six checks pass
#   1  a check failed (violation: fix the Rocq source or the rule, never a fallback here)
#   2  usage / toolchain problem
#
# Regenerate the evidence deliberately:  JPL_REGEN=1 ./jpl_lower.sh

set -u -o pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
cd "$REPO" || exit 2
# Every PRINTED path is repo-relative, so the vendored evidence is not machine-specific.
ML="src/kernel/sh_run_c.ml"
MLI="src/kernel/sh_run_c.mli"
EVID="$HERE/lowering.txt"
HDR="$HERE/sh_run_jpl.h"
ABI="$HERE/sh_run_jpl_abi.h"
ROOTS="${JPL_ROOTS:-mrun_c,step_c}"
# The same compiler and the same flags block 2e gates the representation header with, so
# the two headers are held to one standard rather than to two that happen to agree today.
CC="${CC:-/usr/bin/clang}"
CFLAGS="-std=c99 -Wall -Wextra -Wconversion -Wsign-conversion -pedantic -Werror -fsyntax-only"

green() { printf '\033[32m%s\033[0m\n' "$*"; }
red()   { printf '\033[31m%s\033[0m\n' "$*"; }
bold()  { printf '\033[1m%s\033[0m\n' "$*"; }

if ! command -v ocamlfind >/dev/null 2>&1 || ! ocamlfind query compiler-libs.common >/dev/null 2>&1; then
  red "FAIL: the census needs opam/ocamlfind with the compiler-libs.common package"
  exit 2
fi
if [[ ! -x "$CC" ]]; then
  red "FAIL: no C99 compiler at $CC (set CC=...) — check 5 compiles the ABI against the"
  red "      representation header, which is the only rung that proves their type names are"
  red "      one rule and not two copies"
  exit 2
fi
if [[ ! -f "$ML" || ! -f "$MLI" ]]; then
  red "FAIL: $ML / $MLI not found — run verify_models.sh first (it vendors the extraction)"
  exit 2
fi
if [[ ! -f "$HDR" ]]; then
  red "FAIL: ${HDR#"$REPO"/} not found — the pool cross-check and the ABI compile both"
  red "      compare against the representation layer's own header, which block 2e emits"
  red "      and vendors"
  exit 2
fi

# Build products go to a scratch directory and are removed on exit: ocamlopt puts
# .cmi/.cmx/.o next to the SOURCE, so building in the tree would drop artifacts here.
BUILD="$(mktemp -d)"
trap 'rm -rf "$BUILD"' EXIT

bold "==> building jpl_ast.ml + jpl_lower.ml (compiler-libs)"
if ! ( cd "$BUILD" \
       && cp "$HERE/jpl_ast.ml" "$HERE/jpl_lower.ml" . \
       && ocamlfind ocamlopt -package compiler-libs.common -linkpkg \
            -o jpl_lower jpl_ast.ml jpl_lower.ml > build.log 2>&1 ); then
  red "FAIL: the census did not build"
  cat "$BUILD/build.log"
  exit 2
fi

bold "==> check 1: the lowering census, roots = $ROOTS"
# The roots are passed through, exactly as jpl_front.sh and jpl_emit.sh do: which
# bindings the census covers is a parameter, not a convention, so the negative control
# can point the same tool at the oracle cluster.  The ABI path is the census's fourth
# argument and the census writes it only after a complete census, which is why a refusal
# leaves no half-rendered header behind.
if ! "$BUILD/jpl_lower" "$ML" "$MLI" "$ROOTS" "$BUILD/sh_run_jpl_abi.h" \
     > "$BUILD/lowering.txt" 2>&1 \
     || [[ ! -s "$BUILD/lowering.txt" ]] || [[ ! -s "$BUILD/sh_run_jpl_abi.h" ]]; then
  sed 's/^/    /' "$BUILD/lowering.txt"
  red "FAIL: the census refused this root set — see its message above"
  red "      (a refusal is a statement about the model; the fix is a model-side rewrite,"
  red "      never a fallback added here)"
  exit 1
fi
green "PASS: $(wc -l < "$BUILD/lowering.txt" | tr -d ' ') report lines over $(awk '$1=="members"{print $2}' "$BUILD/lowering.txt") closure members, $(grep -cE '^[a-z_0-9]+ jpl_[a-z_0-9]+\(' "$BUILD/sh_run_jpl_abi.h") ABI declarations rendered"

bold "==> check 2: the counts a lowering cannot absorb"
# Read from the report's own SUMMARY section, which is the census's measurement of
# itself, so this script holds no number of its own.
key() { awk -v k="$1" '$1 == k { print $2 }' "$BUILD/lowering.txt"; }
# A key the section that measures it never marked is a failure, not a zero: an absent
# measurement is not a measurement that came out empty, and treating it as one would let
# the section that marks it be deleted without the gate noticing.
need() {
  local k="$1"
  local v
  v="$(key "$k")"
  if [[ -z "$v" ]]; then
    red "FAIL: the report carries no SUMMARY key '$k' — the section that marks it did not run"
    exit 1
  fi
  printf '%s' "$v"
}
UNNAMED="$(need function_value_sites_unnamed)"
UNKNOWN="$(need unknown_site_classes)"
MISMATCH="$(need self_reference_mismatches)"
for pair in "function_value_sites_unnamed:${UNNAMED}" "unknown_site_classes:${UNKNOWN}" \
            "self_reference_mismatches:${MISMATCH}"; do
  k="${pair%%:*}"; v="${pair#*:}"
  if [[ "$v" != "0" ]]; then
    red "FAIL: $k = $v, and it must be 0 for a JPL-conformant lowering:"
    case $k in
      function_value_sites_unnamed)
        red "      a function value in a position no rule covers can only become a function"
        red "      pointer, which D-60411 forbids; the site must be re-shaped in the model" ;;
      unknown_site_classes)
        red "      an untyped allocation site has no representation, so no pool capacity"
        red "      follows from it and the emitted program would be under-bounded" ;;
      *)
        red "      two readings of the same bytes disagree, so no count in this report is"
        red "      a measurement of the artifact" ;;
    esac
    exit 1
  fi
  printf '    %-30s 0\n' "$k"
done
green "PASS: every function value sits in a position the lowering handles, every allocation site has a type, and the two control-flow readings agree"

bold "==> check 3: pool demand vs the declared header"
# The census's pool table starts at its own header and ends at the first line that is
# not a pool row; the first field of each row is a pool array name.
awk '/^  pool array /{f=1;next} f{ if ($0 !~ /^  jpl_.*_pool /) exit; print $1 }' \
  "$BUILD/lowering.txt" | sort -u > "$BUILD/demanded.txt"
grep -o 'jpl_[a-z0-9_]*pool\[' "$HDR" | sed 's/\[$//' | sort -u > "$BUILD/declared.txt"
if [[ ! -s "$BUILD/demanded.txt" ]]; then
  red "FAIL: the census reported no pool demand at all — its ALLOCATION section is empty"
  exit 1
fi
MISSING="$(comm -23 "$BUILD/demanded.txt" "$BUILD/declared.txt")"
if [[ -n "$MISSING" ]]; then
  red "FAIL: the closure demands a pool the representation layer never declared:"
  printf '%s\n' "$MISSING" | sed 's/^/    /'
  red "      the emitted program would reference an undefined array, so 5-B.3b cannot"
  red "      proceed until either the census's demand or §6.2's pool set explains it"
  exit 1
fi
EXTRA="$(comm -13 "$BUILD/demanded.txt" "$BUILD/declared.txt")"
printf '    demanded by this walk: %s, declared in the header: %s\n' \
  "$(wc -l < "$BUILD/demanded.txt" | tr -d ' ')" "$(wc -l < "$BUILD/declared.txt" | tr -d ' ')"
if [[ -n "$EXTRA" ]]; then
  printf '    DECLARED BUT NOT DEMANDED — a finding, not a failure:\n'
  while read -r p; do
    [[ -n "$p" ]] || continue
    macro="$(printf '%s' "$p" | sed 's/^jpl_//; s/_pool$//' | tr 'a-z' 'A-Z' | sed 's/^/JPL_POOL_/')"
    printf '      %-34s %s\n' "$p" "$(grep -m1 -A0 "^#define ${macro} " "$HDR" \
      | sed 's/.*\/\* //; s/ \*\/$//')"
  done <<< "$EXTRA"
  printf '      §6.2 decision 1 pools some values this walk derives no cell from, so the\n'
  printf '      header may legitimately be wider than the demand; the direction that must\n'
  printf '      never happen is a demand with no declaration, and check 3 asserts it.\n'
else
  printf '    every declared pool is demanded; the two readings agree exactly\n'
fi
green "PASS: every pool the shipped closure demands exists in the emitted header"

bold "==> check 4: the ABI is exactly the closed instance set"
# The three identities are the census's own numbers against each other; the three counts
# below are the same numbers against the file they generated.  Neither half trusts prose.
CLOSED="$(need instances_closed)"
ABI_INST="$(need abi_instances)"
ABI_PROT="$(need abi_prototypes)"
ABI_REFUSED="$(need abi_refused_no_c_type)"
ABI_EXPR="$(need abi_bodies_expressible)"
ABI_OWED="$(need abi_bodies_owed)"
ABI_OUTSIDE="$(need abi_blocked_outside_fold_set)"
if [[ "$ABI_INST" != "$CLOSED" ]]; then
  red "FAIL: the ABI rendered $ABI_INST instance(s) but R8 closed $CLOSED — the declaration"
  red "      set and the monomorphization set are two readings of one call-site walk"
  exit 1
fi
if [[ "$((ABI_PROT + ABI_REFUSED))" != "$ABI_INST" ]]; then
  red "FAIL: $ABI_PROT prototype(s) + $ABI_REFUSED refusal(s) != $ABI_INST rendered instance(s)"
  red "      — an instance appeared in neither column, so the ABI lost or invented one"
  exit 1
fi
if [[ "$((ABI_EXPR + ABI_OWED))" != "$ABI_PROT" ]]; then
  red "FAIL: $ABI_EXPR expressible + $ABI_OWED owed != $ABI_PROT prototype(s) — a declared"
  red "      function has no stated answer to whether §6.3 can ever give it a body"
  exit 1
fi
if [[ "$ABI_OUTSIDE" != "0" ]]; then
  red "FAIL: abi_blocked_outside_fold_set = $ABI_OUTSIDE: an instance the ABI refuses is not"
  red "      one of §6.3's model-side rewrites, so that refusal has no owner and no path"
  red "      out of it.  Either §6.3 gains an obligation or the refusal is a bug in the"
  red "      renderer — it is not something this script can grant an exemption for."
  exit 1
fi
printf '    %-30s %s  (= instances_closed)\n' "abi_instances" "$ABI_INST"
printf '    %-30s %s  + %s refused\n' "abi_prototypes" "$ABI_PROT" "$ABI_REFUSED"
printf '    %-30s %s  expressible + %s owed\n' "abi_bodies" "$ABI_EXPR" "$ABI_OWED"
printf '    %-30s %s  (unowned refusals)\n' "abi_blocked_outside_fold_set" "$ABI_OUTSIDE"
# The file against the measurement: the same three numbers, counted where they are written.
DECLS="$(grep -cE '^[a-z_0-9]+ jpl_[a-z_0-9]+\(' "$BUILD/sh_run_jpl_abi.h")"
REFUSALS="$(grep -c '^/\* NOT EMITTED' "$BUILD/sh_run_jpl_abi.h")"
DECLONLY="$(grep -c '^/\* declaration only' "$BUILD/sh_run_jpl_abi.h")"
if [[ "$DECLS" != "$ABI_PROT" || "$REFUSALS" != "$ABI_REFUSED" \
      || "$DECLONLY" != "$ABI_OWED" ]]; then
  red "FAIL: the rendered header disagrees with the census that rendered it:"
  red "      declarations $DECLS (report says $ABI_PROT)"
  red "      refusal comments $REFUSALS (report says $ABI_REFUSED)"
  red "      declaration-only comments $DECLONLY (report says $ABI_OWED)"
  exit 1
fi
printf '    header carries %s declaration(s), %s refusal(s), %s owed body(s)\n' \
  "$DECLS" "$REFUSALS" "$DECLONLY"
if [[ "$ABI_REFUSED" != "0" ]]; then
  printf '    REFUSED, no C type exists — a finding with an owner, not a failure:\n'
  grep '^/\* NOT EMITTED' "$BUILD/sh_run_jpl_abi.h" \
    | sed 's|/\* NOT EMITTED — |      |; s/ \*\/$//'
  printf '      D-60411 forbids the only alternative (a function pointer), so refusing to\n'
  printf '      declare this instance is the conformant answer; §6.3 owns the rewrite that\n'
  printf '      removes the function-typed argument.\n'
fi
green "PASS: every closed instance is declared, refused, or accounted, and the header's own lines agree with the report"

bold "==> check 5: the ABI compiles against the representation header"
# The ABI header's types are the names the layout layer typedef'd, so the pair is only
# meaningful in this include order; a TU is the smallest thing that states that order.
printf '#include "sh_run_jpl.h"\n#include "sh_run_jpl_abi.h"\n' > "$BUILD/abi_tu.c"
cp "$HDR" "$BUILD/sh_run_jpl.h"
# shellcheck disable=SC2086
if ! ( cd "$BUILD" && "$CC" $CFLAGS abi_tu.c ) 2> "$BUILD/clang.log"; then
  red "FAIL: the ABI header does not compile against ${HDR#"$REPO"/}"
  sed 's/^/    /' "$BUILD/clang.log"
  red "      a type name here that the representation layer never typedef'd, or a"
  red "      parameter whose width disagrees with the layout, is exactly what this rung"
  red "      exists to catch — the two headers share value_name and must not diverge"
  exit 1
fi
green "PASS: the $DECLS prototype(s) resolve against the emitted layout under $CFLAGS"

bold "==> check 6: the vendored evidence"
if [[ "${JPL_REGEN:-0}" == "1" ]]; then
  cp "$BUILD/lowering.txt" "$EVID"
  cp "$BUILD/sh_run_jpl_abi.h" "$ABI"
  green "PASS: regenerated ${EVID#"$REPO"/} and ${ABI#"$REPO"/}"
  exit 0
fi
for pair in "${EVID#"$REPO"/}:$EVID:$BUILD/lowering.txt" \
            "${ABI#"$REPO"/}:$ABI:$BUILD/sh_run_jpl_abi.h"; do
  name="$(printf '%s' "$pair" | cut -d: -f1)"
  vendored="$(printf '%s' "$pair" | cut -d: -f2)"
  fresh="$(printf '%s' "$pair" | cut -d: -f3)"
  if [[ ! -f "$vendored" ]]; then
    red "FAIL: $name missing — generate with: JPL_REGEN=1 $0"
    exit 1
  fi
  if ! diff -q "$vendored" "$fresh" > /dev/null; then
    red "FAIL: $name is stale vs a fresh census over the vendored artifact"
    diff -u "$vendored" "$fresh" | head -40
    red "      re-run with JPL_REGEN=1 after checking the change is intended"
    exit 1
  fi
  printf '    %-28s byte-identical\n' "$name"
done
green "PASS: both artifacts are identical to a fresh census"

bold "==> what the census measured, read out of the vendored evidence"
# The schema split, the ABI accounting and the residue are the artifact's own shape and
# the tool's own statement of its limits, so no number here is restated in this script.
awk '/^==== SCHEMA CENSUS/{f=1;next} /^==== /{f=0} f' "$EVID" | sed 's/^/    /'
printf '    R8: %s closed instance(s) to emit, %s still open — the interface declares those\n' \
  "$(awk '$1=="instances_closed"{print $2}' "$EVID")" \
  "$(awk '$1=="instances_open"{print $2}' "$EVID")"
printf '      bindings polymorphic, so the shipped closure never decides their layout\n'
awk '/^==== ABI SUMMARY/{f=1;next} /^==== /{f=0} f' "$EVID" | sed 's/^/    /'
awk '/^==== WHAT THIS CENSUS CANNOT ANSWER/{f=1;next} /^==== /{f=0} f' "$EVID" | sed 's/^/    /'

exit 0
