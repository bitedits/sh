#!/usr/bin/env bash
# jpl_lower.sh — run the JPL.5-B.3a lowering census, the 5-B.3b-i ABI rendering and the
# 5-B.3b-ii-a renderability trial over the vendored extraction, and gate what they produce.
#
# 5-B.3a is a MEASUREMENT, not a translation: it decides, before any C body is emitted,
# which lowering schema each shipped binding has, which R8 instances the call sites
# actually close, and which pools the closure demands.  5-B.3b-i renders the declaration
# half of what that measurement found — the closed R8 instances as a C ABI header.  It
# emits prototypes and nothing else: §6.3's loop-body schema has not landed, and three of
# the instances this header declares are owed a model-side rewrite before they can have a
# body.  5-B.3b-ii-a asks the second question, which is not about shape but about whether a
# body can be written at all yet: §6.4's licensed scalar set is implemented as a renderer in
# the census itself, run as a TRIAL over all 47 members, and the bodies it accepts are
# emitted as sh_run_jpl_bodies.c.  A census that classified bodies by rules of its own and
# a renderer that followed different ones would be two models of one artifact, so the
# verdict each member carries IS the trial's result, in the trial's own words.
# Eight checks, in this order:
#   1  the census runs on the shipped closure and writes all three artifacts (a refusal
#      here is a finding about the model, never something this script works around)
#   2  the four counts a lowering cannot absorb are asserted at zero, read from the
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
#        render_unaccounted            a closure member that the renderability trial
#                                      neither rendered nor refused, so the six verdicts
#                                      would be an opinion about part of the closure
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
#   5  the renderability verdicts are exactly the closure, and the emitted C is exactly the
#      rendered part of them:
#        data + alias + render + owed-representation + owed-schema + owed-construct
#          == members
#        the DATA names the report lists are all #defines in sh_run_jpl.h — a body that
#          cites a constant the header never defined is a link error JPL.7 would pay for,
#          and this is the only rung that can see the citation and the definition together
#        the definitions in sh_run_jpl_bodies.c == bodies_renderable, and at least one
#          body rendered — a census that rendered nothing would be reporting a partition
#          and no C, which is the failure mode this whole stage exists to avoid
#   6  the ABI header compiles against the representation header, and so does the rendered
#      bodies file, both under 2e's own flags.  This is the rung that turns the shared
#      value-naming rule (jpl_ast.ml's value_name, which jpl_emit.ml now uses for the
#      typedefs, the census for the prototypes and the renderer for the definitions) from a
#      convention into a checked claim: a type name either layer invented would not resolve.
#   7  the rendered bodies are SWEPT against the extracted kernel they came from: the
#      census generates both drivers from the same RENDER rows (jpl_bodies_diff.c and
#      jpl_bodies_diff.ml), the gate builds one in each language, runs 0 … MAX_FUEL —
#      the artifact's own cap, read as JPL_MAX_FUEL by the C and as `mAX_FUEL` by the
#      OCaml — and `cmp`s the two transcripts.  This is the rung that turns "the
#      renderer wrote C" into "the C computes what the extracted kernel computes, on
#      every bounded input", and the line count is checked against the census's own
#      sweep_domain so neither driver picks the range it is testing.  The drivers are
#      host programs: <stdio.h> and printf are theirs, not the shipped kernel's, so
#      JPL.6's lint does not audit them.
#   8  the vendored evidence (lowering.txt, sh_run_jpl_abi.h, sh_run_jpl_bodies.c AND
#      both generated drivers) is byte-identical to this run.
#
# Inputs are the VENDORED artifact (src/kernel/sh_run_c.ml{,i}) that block 2c of
# verify_models.sh already byte-binds to a fresh Coq Extraction, and the same roots the
# front end (2d) and the layout layer (2e) gate, so all four rungs describe one closure.
# The census reads the capacities out of the artifact's own jpl_caps_table through the
# shared reader (jpl_ast.ml), which is why it reports the numbers the header was built
# from instead of a second copy of them, and why a rendered body cites JPL_C_* / JPL_MAX_*
# rather than a re-typed numeral.
#
# Exit codes
#   0  all eight checks pass
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
BODIES="$HERE/sh_run_jpl_bodies.c"
DIFFC="$HERE/jpl_bodies_diff.c"
DIFFML="$HERE/jpl_bodies_diff.ml"
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
  red "FAIL: no C99 compiler at $CC (set CC=...) — checks 6 and 7 compile the ABI, the"
  red "      rendered bodies and the C differential driver against the representation"
  red "      header, which is the only rung that proves their type names are"
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
# can point the same tool at the oracle cluster.  The ABI header and the rendered bodies
# are the census's fourth, fifth, sixth and seventh arguments, and it writes all four only
# after a complete census, which is why a refusal leaves no half-rendered header, no
# half-written TU and no half-generated driver behind.
if ! "$BUILD/jpl_lower" "$ML" "$MLI" "$ROOTS" "$BUILD/sh_run_jpl_abi.h" \
     "$BUILD/sh_run_jpl_bodies.c" \
     "$BUILD/jpl_bodies_diff.c" "$BUILD/jpl_bodies_diff.ml" \
     > "$BUILD/lowering.txt" 2>&1 \
     || [[ ! -s "$BUILD/lowering.txt" ]] || [[ ! -s "$BUILD/sh_run_jpl_abi.h" ]] \
     || [[ ! -s "$BUILD/sh_run_jpl_bodies.c" ]] || [[ ! -s "$BUILD/jpl_bodies_diff.c" ]] \
     || [[ ! -s "$BUILD/jpl_bodies_diff.ml" ]]; then
  sed 's/^/    /' "$BUILD/lowering.txt"
  red "FAIL: the census refused this root set — see its message above"
  red "      (a refusal is a statement about the model; the fix is a model-side rewrite,"
  red "      never a fallback added here)"
  exit 1
fi
green "PASS: $(wc -l < "$BUILD/lowering.txt" | tr -d ' ') report lines over $(awk '$1=="members"{print $2}' "$BUILD/lowering.txt") closure members, $(grep -cE '^[a-z_0-9]+ jpl_[a-z_0-9]+\(' "$BUILD/sh_run_jpl_abi.h") ABI declarations rendered, $(grep -cE '^\{$' "$BUILD/sh_run_jpl_bodies.c") bodies rendered"

bold "==> check 2: the four counts a lowering cannot absorb"
# Read from the report's own SUMMARY section, which is the census's measurement of
# itself, so this script holds no number of its own.  The anchor matters: the sections
# above SUMMARY print some of the same labels into their tables, and a key is only
# machine-readable where the census put it in the one place reserved for the gate.
key() { awk -v k="$1" '/^==== SUMMARY/{f=1} f && $1 == k { print $2 }' "$BUILD/lowering.txt"; }
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
UNADDR="$(need render_unaccounted)"
for pair in "function_value_sites_unnamed:${UNNAMED}" "unknown_site_classes:${UNKNOWN}" \
            "self_reference_mismatches:${MISMATCH}" "render_unaccounted:${UNADDR}"; do
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
      render_unaccounted)
        red "      a closure member received no renderability verdict, so the six counts"
        red "      below describe part of the shipped closure and not all of it" ;;
      *)
        red "      two readings of the same bytes disagree, so no count in this report is"
        red "      a measurement of the artifact" ;;
    esac
    exit 1
  fi
  printf '    %-30s 0\n' "$k"
done
green "PASS: every function value sits in a position the lowering handles, every allocation site has a type, the two control-flow readings agree, and every member carries a verdict"

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

bold "==> check 5: the renderability trial covers the closure, and the C matches its RENDER rows"
# The six verdict counts are the census's own, the seven lines below are what the trial
# wrote into a file, and the header is where the cited names have to exist.  Nothing here
# restates a number: the partition identity, the file's definition count and the header's
# #defines are compared to each other, exactly as check 4 compares the ABI to the census.
MEMBERS="$(need members)"
DATA="$(need data_bindings)"
ALIAS="$(need alias_bindings)"
RENDER="$(need bodies_renderable)"
OWED_REPR="$(need owed_representation)"
OWED_SCHEMA="$(need owed_schema)"
OWED_CONSTRUCT="$(need owed_construct)"
CITING="$(need bodies_citing_data)"
if [[ "$((DATA + ALIAS + RENDER + OWED_REPR + OWED_SCHEMA + OWED_CONSTRUCT))" != "$MEMBERS" ]]; then
  red "FAIL: the renderability verdicts do not partition the closure:"
  red "      data $DATA + alias $ALIAS + render $RENDER + owed-representation $OWED_REPR"
  red "      + owed-schema $OWED_SCHEMA + owed-construct $OWED_CONSTRUCT != members $MEMBERS"
  red "      — a member would be described by two verdicts or by none, and §6.4's classes"
  red "      would then be a model of part of the artifact rather than a measurement of it"
  exit 1
fi
if [[ "$RENDER" -lt 1 ]]; then
  red "FAIL: bodies_renderable = $RENDER: the trial rendered nothing, so the emitted TU is"
  red "      an empty file next to a partition that claims to be a measurement.  Either the"
  red "      licensed scalar set shrank below what the artifact actually contains, or the"
  red "      rules above RENDER are refusing everything — which is a finding to put in §6.4,"
  red "      not a gate to lower."
  exit 1
fi
DEFS="$(grep -cE '^\{$' "$BUILD/sh_run_jpl_bodies.c")"
if [[ "$DEFS" != "$RENDER" ]]; then
  red "FAIL: sh_run_jpl_bodies.c carries $DEFS definition(s) but the trial reported"
  red "      $RENDER RENDER row(s) — the file and the census that wrote it disagree"
  exit 1
fi
# Every name a rendered body can cite: the trial cites only through the same rule the DATA
# rows print here (jpl_ast.ml's cap_macro_of_data / data_macro), so resolving this list in
# 2e's header resolves every citation in the TU as well — and a JPL_C_* the representation
# layer never defined would be a compile error the census could not have predicted.
grep '^  DATA-MACRO ' "$BUILD/lowering.txt" | awk '{print $3}' | sort -u > "$BUILD/data-names.txt"
NAMES="$(wc -l < "$BUILD/data-names.txt" | tr -d ' ')"
if [[ "$NAMES" != "$DATA" ]]; then
  red "FAIL: the report lists $NAMES distinct DATA name(s) for $DATA DATA row(s) — one"
  red "      binding's C name collides with another's, so two constants would share a macro"
  exit 1
fi
UNRESOLVED=""
while read -r m; do
  [[ -n "$m" ]] || continue
  grep -q "^#define $m " "$HDR" || UNRESOLVED="$UNRESOLVED$m
"
done < "$BUILD/data-names.txt"
if [[ -n "$UNRESOLVED" ]]; then
  red "FAIL: a rendered body cites a constant the representation header never defines:"
  printf '%s' "$UNRESOLVED" | sed '/^$/d;s/^/    /'
  red "      ${HDR#"$REPO"/} must carry a #define for every name the trial is willing to"
  red "      write, or the emitted program does not link"
  exit 1
fi
printf '    %-30s %s + %s alias + %s render + %s owed-repr + %s owed-schema + %s owed-construct = %s members\n' \
  "renderability partition" "$DATA" "$ALIAS" "$RENDER" "$OWED_REPR" "$OWED_SCHEMA" \
  "$OWED_CONSTRUCT" "$MEMBERS"
printf '    %-30s %s definitions, %s of them citing a data constant\n' \
  "sh_run_jpl_bodies.c" "$DEFS" "$CITING"
printf '    %-30s all %s resolve in the emitted header\n' "DATA names" "$NAMES"
if [[ "$ALIAS" != "0" ]]; then
  printf '    ALIAS rows: a prototype exists, a definition does not — a finding, not a\n'
  printf '    failure, printed in the words the census itself used, not re-summarised here:\n'
  awk '/^  FINDING, with an owner \(not a failure\): [0-9]+ alias/{f=1}
       /^RENDERABILITY CONSISTENT/{f=0}
       f' "$BUILD/lowering.txt" | sed '/^[[:space:]]*$/d; s/^/      /'
fi
# The second debt (JPL.md §6.5, 5-B.3b-ii-b-0): the same members, read a second time for
# the obligation §6.4's rule order suppresses.  Nothing here re-derives a pool — every key
# below is marked by the census's own walk, the one the renderability trial consults — but
# the identities are what §6.5's slice order stands on, so a plan that assumed them fails
# this rung rather than failing a build three slices later.
ALSO_POOL="$(need owed_schema_also_pool)"
POOL_FREE="$(need owed_schema_pool_free)"
FREE_VAR="$(need owed_schema_pool_free_var)"
FREE_OPAQUE="$(need owed_schema_pool_free_opaque)"
FREE_SCALAR="$(need owed_schema_pool_free_scalar)"
VAR_POOLED="$(need owed_schema_free_var_pooled_instance)"
CONSTRUCT_POOL="$(need owed_construct_also_pool)"
DUAL="$(need dual_debt_rows)"
DEBT_BAD="$(need debt_unaccounted)"
if [[ "$((ALSO_POOL + POOL_FREE))" != "$OWED_SCHEMA" ]]; then
  red "FAIL: the dual-debt split does not cover the schema set: also-pool $ALSO_POOL +"
  red "      pool-free $POOL_FREE != owed_schema $OWED_SCHEMA — §6.5's slice order is"
  red "      then a statement about part of the closure, which is what §2 forbids"
  exit 1
fi
if [[ "$((FREE_VAR + FREE_OPAQUE + FREE_SCALAR))" != "$POOL_FREE" ]]; then
  red "FAIL: $POOL_FREE pool-free schema rows are explained by $FREE_VAR var + $FREE_OPAQUE"
  red "      opaque + $FREE_SCALAR scalar — a row is being called pool-free without a reason,"
  red "      and a zero that has no reason is exactly the licence §6.5 refuses to grant"
  exit 1
fi
if [[ "$DUAL" != "$((ALSO_POOL + CONSTRUCT_POOL))" ]]; then
  red "FAIL: dual_debt_rows $DUAL != owed_schema_also_pool $ALSO_POOL + owed_construct_also_pool"
  red "      $CONSTRUCT_POOL: a row carries both debts that §6.4 verdicted for neither of them,"
  red "      so the dependency order in §6.4 is not the order this census ran"
  exit 1
fi
if [[ "$CONSTRUCT_POOL" != "0" ]]; then
  red "FAIL: owed_construct_also_pool = $CONSTRUCT_POOL.  The trial consults pools BEFORE its"
  red "      licensed set, so an OWED-CONSTRUCT row cannot reach a construct refusal while"
  red "      holding a pooled value: one of the two rules moved."
  exit 1
fi
if [[ "$DEBT_BAD" != "0" ]]; then
  red "FAIL: debt_unaccounted = $DEBT_BAD — a verdict in §6.4's partition is not explained by"
  red "      the debts measured on its own row, so a refusal printed here has no measurement"
  red "      behind it (the census names each row; see THE SECOND DEBT above)"
  exit 1
fi
if [[ "$VAR_POOLED" -gt "$FREE_VAR" ]]; then
  red "FAIL: owed_schema_free_var_pooled_instance $VAR_POOLED exceeds the $FREE_VAR variable-"
  red "      classified rows it cross-checks: the ABI would be reporting a pooled instance for"
  red "      a binding this walk did not classify as pool-free-by-variable, which means the"
  red "      two readings of the same signature disagree"
  exit 1
fi
printf '    %-30s %s + %s = %s owed-schema\n' "dual-debt split" "$ALSO_POOL" "$POOL_FREE" "$OWED_SCHEMA"
printf '    %-30s %s var + %s opaque + %s scalar\n' "pool-free reasons" "$FREE_VAR" "$FREE_OPAQUE" "$FREE_SCALAR"
printf '    %-30s %s rows carry BOTH debts; %s construct rows touch a pool (must be 0)\n' \
  "both debts" "$DUAL" "$CONSTRUCT_POOL"
printf '    %-30s %s of the %s variable rows are POOLED at a closed instance in the ABI header\n' \
  "abi cross-check" "$VAR_POOLED" "$FREE_VAR"
if [[ "$FREE_SCALAR" == "0" ]]; then
  printf '    SLICE FINDING: no §6.3-shape row is pool-free in the plain sense — the %s that\n' "$ALSO_POOL"
  printf '    carry a pool need the allocator and the step-boundary copying, and the %s that\n' "$POOL_FREE"
  printf '    look free are polymorphic (%s of them already pooled at a closed instance, so the\n' "$VAR_POOLED"
  printf '    cell exists and only this walk cannot see it).  JPL.md §6.5 therefore puts ii-b-1\n'
  printf '    and ii-b-2 before ii-b-3 and ii-b-4, and this rung is what keeps that ordering\n'
  printf '    measured rather than assumed.\n'
fi
green "PASS: every member carries exactly one renderability verdict, the emitted TU has one definition per RENDER row, and every DATA name those bodies cite is a #define in the header"

bold "==> check 6: the ABI and the rendered bodies compile against the representation header"
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

# The rendered bodies are a translation unit, not a header: they answer prototypes 2e
# emitted, so compiling them against the same header under the same flags is the rung that
# proves the renderer's type rule, the prototype layer's type rule and the layout layer's
# type rule are one rule.  A parameter the renderer typed differently from the interface,
# a comparison that yields int where a jpl_bool is declared, or a macro it invented would
# all fail here — and -Wconversion is what turns "the C looks like the OCaml" into a claim
# a compiler checks.
# shellcheck disable=SC2086
if ! ( cd "$BUILD" && "$CC" $CFLAGS sh_run_jpl_bodies.c ) 2> "$BUILD/bodies.log"; then
  red "FAIL: ${BODIES#"$REPO"/} does not compile against ${HDR#"$REPO"/}"
  sed 's/^/    /' "$BUILD/bodies.log"
  red "      the renderer emits a definition for a prototype 2e printed, so a disagreement"
  red "      here is a second value-naming or width rule, not a C detail to paper over"
  exit 1
fi
green "PASS: the $DEFS rendered body(s) compile against the emitted layout under $CFLAGS"

bold "==> check 7: the rendered bodies are swept against the extracted kernel they came from"
# Both drivers are GENERATED by the census from the same RENDER rows, over the domain the
# artifact names for itself (JPL_MAX_FUEL read by the C, mAX_FUEL read by the OCaml), so the
# range is not an expectation written here: the report marks it as sweep_domain, and what
# each driver ACTUALLY printed is compared to that.  A compile-only rung proves the emitted
# C is legal; only this rung proves it computes what the extraction computes.
SWEEP="$(need sweep_domain)"
SWEPT_EXH="$(need bodies_swept_exhaustive)"
SWEPT_DIAG="$(need bodies_swept_diagonal)"
cp "$HDR" "$BUILD/sh_run_jpl.h"
# The drivers are HOST programs: <stdio.h> and printf belong to them, not to the shipped
# kernel, so they take 2e's flag set minus the syntax-only pass that made check 6 a check
# rather than a build.
DIFF_CFLAGS="${CFLAGS% -fsyntax-only}"
# shellcheck disable=SC2086
if ! ( cd "$BUILD" \
       && "$CC" $DIFF_CFLAGS -o diff_c jpl_bodies_diff.c sh_run_jpl_bodies.c ) \
     2> "$BUILD/diff_c.build.log"; then
  red "FAIL: the generated C driver (${DIFFC#"$REPO"/}) did not build"
  sed 's/^/    /' "$BUILD/diff_c.build.log"
  red "      the census writes it from the RENDER rows it also wrote into"
  red "      ${BODIES#"$REPO"/}, so a failure here is the driver disagreeing with the"
  red "      bodies file rather than a C detail to paper over"
  exit 1
fi
# The OCaml half is compiled against the VENDORED extraction — the same bytes the census
# read and the same artifact block 2c byte-binds to a fresh Coq Extraction — so the two
# transcripts are the same closure read through two toolchains.
if ! ( cd "$BUILD" \
       && cp "$REPO/$ML" "$REPO/$MLI" . \
       && ocamlfind ocamlc -w -a -o diff_ml \
            "${MLI##*/}" "${ML##*/}" jpl_bodies_diff.ml ) \
     2> "$BUILD/diff_ml.build.log"; then
  red "FAIL: the generated OCaml driver (${DIFFML#"$REPO"/}) did not build against ${ML#"$REPO"/}"
  sed 's/^/    /' "$BUILD/diff_ml.build.log"
  red "      the census emits a call per RENDER row from the extracted interfaces, so a"
  red "      mismatch here is a second naming rule between the renderer and the extraction"
  exit 1
fi
if ! "$BUILD/diff_c" > "$BUILD/diff_c.out" 2> "$BUILD/diff_c.run.log"; then
  red "FAIL: the C driver exited non-zero"
  sed 's/^/    /' "$BUILD/diff_c.run.log"
  exit 1
fi
if ! "$BUILD/diff_ml" > "$BUILD/diff_ml.out" 2> "$BUILD/diff_ml.run.log"; then
  red "FAIL: the OCaml driver exited non-zero"
  sed 's/^/    /' "$BUILD/diff_ml.run.log"
  exit 1
fi
# Neither driver picks its own range: each must have printed exactly sweep_domain + 1 lines
# (0 through MAX_FUEL inclusive), which is the census's own number read back out of the
# transcript rather than a count this script asserts out of thin air.
LINES_C="$(wc -l < "$BUILD/diff_c.out" | tr -d ' ')"
LINES_ML="$(wc -l < "$BUILD/diff_ml.out" | tr -d ' ')"
for pair in "jpl_bodies_diff.c:$LINES_C" "jpl_bodies_diff.ml:$LINES_ML"; do
  name="${pair%%:*}"; got="${pair#*:}"
  if [[ "$got" != "$((SWEEP + 1))" ]]; then
    red "FAIL: $name printed $got line(s) but the census swept 0 … $SWEEP, i.e. $((SWEEP + 1))"
    red "      — the driver and the report disagree about the domain, so the comparison below"
    red "        would cover a different range than the one the census claims to have checked"
    exit 1
  fi
  printf '    %-24s %s lines over 0 … %s\n' "$name" "$got" "$SWEEP"
done
# A pair of identical constant transcripts would cmp clean and prove nothing.  The fuel
# index is the first field of every line and varies by construction, so the test is on the
# SWEPT fields only: the rendered bodies must actually disagree somewhere over the domain.
DISTINCT="$(awk '{ $1=""; print }' "$BUILD/diff_c.out" | sort -u | wc -l | tr -d ' ')"
if [[ "$DISTINCT" -lt 2 ]]; then
  red "FAIL: the C driver printed $DISTINCT distinct body tuple(s) over $SWEEP fuel values — the"
  red "      swept bodies are constant, so byte-for-byte agreement would be a tautology"
  exit 1
fi
printf '    %-24s %s distinct body tuples, %s swept exhaustively + %s diagonally\n' \
  "transcript variety" "$DISTINCT" "$SWEPT_EXH" "$SWEPT_DIAG"
if ! cmp "$BUILD/diff_c.out" "$BUILD/diff_ml.out"; then
  red "FAIL: the C transcript differs from the OCaml transcript — the rendered bodies do NOT"
  red "      compute what the extracted kernel computes.  Diff the two:"
  diff "$BUILD/diff_c.out" "$BUILD/diff_ml.out" | head -20 | sed 's/^/    /'
  red "      this is the rung the whole stage exists for; the fix belongs in the renderer or"
  red "      in §6.4's licensed set, never in a tolerance added here"
  exit 1
fi
green "PASS: the rendered bodies and the extracted kernel agree byte-for-byte on all $((SWEEP + 1)) swept inputs"

bold "==> check 8: the vendored evidence"
if [[ "${JPL_REGEN:-0}" == "1" ]]; then
  cp "$BUILD/lowering.txt" "$EVID"
  cp "$BUILD/sh_run_jpl_abi.h" "$ABI"
  cp "$BUILD/sh_run_jpl_bodies.c" "$BODIES"
  cp "$BUILD/jpl_bodies_diff.c" "$DIFFC"
  cp "$BUILD/jpl_bodies_diff.ml" "$DIFFML"
  green "PASS: regenerated ${EVID#"$REPO"/}, ${ABI#"$REPO"/}, ${BODIES#"$REPO"/}, ${DIFFC#"$REPO"/} and ${DIFFML#"$REPO"/}"
  exit 0
fi
for pair in "${EVID#"$REPO"/}:$EVID:$BUILD/lowering.txt" \
            "${ABI#"$REPO"/}:$ABI:$BUILD/sh_run_jpl_abi.h" \
            "${BODIES#"$REPO"/}:$BODIES:$BUILD/sh_run_jpl_bodies.c" \
            "${DIFFC#"$REPO"/}:$DIFFC:$BUILD/jpl_bodies_diff.c" \
            "${DIFFML#"$REPO"/}:$DIFFML:$BUILD/jpl_bodies_diff.ml"; do
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
green "PASS: all five artifacts are identical to a fresh census"

bold "==> what the census measured, read out of the vendored evidence"
# The schema split, the ABI accounting, the renderability partition and the residue are the
# artifact's own shape and the tool's own statement of its limits, so no number here is
# restated in this script.
awk '/^==== SCHEMA CENSUS/{f=1;next} /^==== /{f=0} f' "$EVID" | sed 's/^/    /'
printf '    R8: %s closed instance(s) to emit, %s still open — the interface declares those\n' \
  "$(awk '$1=="instances_closed"{print $2}' "$EVID")" \
  "$(awk '$1=="instances_open"{print $2}' "$EVID")"
printf '      bindings polymorphic, so the shipped closure never decides their layout\n'
awk '/^==== ABI SUMMARY/{f=1;next} /^==== /{f=0} f' "$EVID" | sed 's/^/    /'
awk '/^  RENDER PARTITION/{f=1;next} /^  THE DATA NAMES/{f=0} f' "$EVID" | sed 's/^/    /'
awk '/^==== WHAT THIS CENSUS CANNOT ANSWER/{f=1;next} /^==== /{f=0} f' "$EVID" | sed 's/^/    /'

exit 0
