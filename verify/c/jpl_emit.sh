#!/usr/bin/env bash
# jpl_emit.sh — run the JPL.5-B.2 representation-layer emitter over the vendored
# extraction, COMPILE the header and the pool translation unit it writes, drive
# that runtime at its bounds, and check its numbers against the artifact
# EVALUATED by the OCaml runtime.
#
# Eight checks, in this order:
#   1  the emitter runs on the shipped closure and writes a header + the pools TU
#   2  the header compiles clean under the JPL C99 flag set.  Every struct in it
#      is followed by a `typedef char jpl_check_<name>_is_<N>` whose array size
#      is -1 unless sizeof agrees, so a wrong byte count — padding, a mis-sized
#      pool element, a cap that drifted — fails HERE, in the compiler, and not
#      in a comment.  C99 has no _Static_assert (that is C11), so this is the
#      conforming form of the same check.
#   3  the pool translation unit (§6.6) COMPILES under the same flags — not
#      -fsyntax-only: this is the first C in the tree that owns a mutable static,
#      so -Wconversion and -Wsign-conversion now apply to real definitions.
#   4  the differential fold: the ten capacities the emitter folded out of the
#      artifact's SYNTAX agree with the ten fields of jpl_caps_table as the
#      OCaml runtime EVALUATES them.  Those are two independent readings of the
#      same extracted term — a constant folder and the interpreter — so their
#      agreement is the measurement that retires "the folder is right by
#      construction".  The probe carries no numbers of its own.
#   5  the runtime DRIVEN AT ITS BOUNDS (§6.6): one sweep per declared allocator,
#      generated from the header's own `_alloc(void);` lines so it carries no
#      capacity literal either.  It is this gate that turns §6.6's prose into a
#      measurement — that a region of C cells serves exactly C-1, that index 0
#      stays reserved, that exhaustion answers with the nil handle and counts it
#      rather than wrapping, and that a reset rewinds the region but not the
#      instruments.
#   6  the accounting closes: the report's RUNTIME SUMMARY keys agree with each
#      other arithmetically, with the names the header declares, and with the
#      arrays the translation unit defines.  A missing key is a failure, not a 0.
#   7  §6.7's per-word edge tables: every table's rows, width and class census are
#      re-derived by three readings that never look at a table — the header's own
#      constructor comments, the artifact's .mli alternatives with parenthesis
#      depth counted (so `Case of text * (text list * cmd list) list` is two slots),
#      and the initialiser tokens — plus the two properties a collector needs: a
#      node row's first word is its tag, and an UNUSED word is trailing, never a
#      hole an "width minus the tail" reading would walk past.
#   8  the vendored evidence (sh_run_jpl.h + sh_run_jpl_pools.c + layout.txt) is
#      byte-identical to this run.
#
# Inputs are the VENDORED artifact (src/kernel/sh_run_c.ml{,i}) that block 2c of
# verify_models.sh already byte-binds to a fresh Coq Extraction, and the same
# roots the front end (2d) gates, so this layer describes exactly the code the
# subset verdict covers.
#
# Exit codes
#   0  all eight checks pass
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
POOLS="$HERE/sh_run_jpl_pools.c"
EVID="$HERE/layout.txt"
ROOTS="${JPL_ROOTS:-mrun_c,step_c}"
# -fsyntax-only is enough for the HEADER: it declares the pools as extern.  The
# translation unit that DEFINES them is check 3, and it is compiled to an object.
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

bold "==> check 1: representation layer, roots = $ROOTS"
# The roots are passed through, exactly as jpl_front.sh does: which bindings the
# layout covers is a parameter, not a convention, so the negative control can
# point the same tool at the oracle cluster.
if ! "$BUILD/jpl_emit" "$ML" "$MLI" "$BUILD/sh_run_jpl.h" "$BUILD/sh_run_jpl_pools.c" \
       "$ROOTS" > "$BUILD/layout.txt" 2>&1 \
     || [[ ! -s "$BUILD/sh_run_jpl.h" ]] || [[ ! -s "$BUILD/sh_run_jpl_pools.c" ]]; then
  sed 's/^/    /' "$BUILD/layout.txt"
  red "FAIL: the emitter could not lay out this artifact (see its message above)"
  exit 1
fi
green "PASS: emitted $(grep -c '^typedef\|^#define' "$BUILD/sh_run_jpl.h") typedefs and macros, plus $(grep -c '^[a-z_0-9]* jpl_[a-z0-9_]*_pool\[' "$BUILD/sh_run_jpl_pools.c") pool definitions, from $(wc -l < "$BUILD/layout.txt" | tr -d ' ') report lines"

bold "==> check 2: the emitted header under $CFLAGS"
# shellcheck disable=SC2086
if "$CC" $CFLAGS "$BUILD/sh_run_jpl.h" 2> "$BUILD/clang.log"; then
  green "PASS: every sizeof and every cap relation in the header is a C99 compile-time assertion, and they hold"
else
  red "FAIL: the emitted header does not compile — a layout claim is wrong"
  sed 's/^/    /' "$BUILD/clang.log"
  exit 1
fi

bold "==> check 3: the pool translation unit, compiled (not merely parsed) under the JPL flags"
# The -fsyntax-only set cannot see a defined object at all: here the same flags
# run over real definitions, so a cap that overflowed its counter, a signed/unsigned
# mix in an allocator, or an uninitialised static becomes a compile error.  This is
# the only C in the tree that owns a mutable static, which is why it is compiled and
# not just linted (§6.6).
ALLOC_N="$(grep -c '^[a-z_0-9]* jpl_[a-z0-9_]*_alloc(void);' "$BUILD/sh_run_jpl.h")"
# shellcheck disable=SC2086
if "$CC" ${CFLAGS%-fsyntax-only} -c "$BUILD/sh_run_jpl_pools.c" \
     -o "$BUILD/sh_run_jpl_pools.o" 2> "$BUILD/clang_pools.log"; then
  green "PASS: the generated pools TU compiles clean — $ALLOC_N allocators declared in the header are defined here"
else
  red "FAIL: the generated pools TU does not compile"
  sed 's/^/    /' "$BUILD/clang_pools.log"
  exit 1
fi

bold "==> check 4: the folded caps vs the artifact evaluated by the OCaml runtime"
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

bold "==> check 5: the pool runtime driven at its bounds (JPL.md §6.6)"
# The sweep is GENERATED from the emitted header rather than written out: one
# function per `jpl_<stem>_alloc(void);` declaration, and every bound inside it is
# that pool's own JPL_POOL_* macro.  So the probe asserts §6.6's properties against
# the same constants the allocators compare with, and carries no capacity number of
# its own — the same discipline as the cap probe above.  This is gate scaffolding,
# not emitted code: it prints, which the shipped runtime never does.
if ! grep '^[a-z_0-9]* jpl_[a-z0-9_]*_alloc(void);' "$BUILD/sh_run_jpl.h" \
     | awk '{ h = $1; s = $2; sub(/^jpl_/, "", s); sub(/_alloc\(void\);$/, "", s); print s, h }' \
       > "$BUILD/pool_stems.txt"; then
  red "FAIL: the header declares no allocator at all"
  exit 1
fi
# Pair every stem with the capacity macro §6.6 says it must be sized from; the
# naming rule is checked here, not assumed: a pool whose macro is absent fails.
if ! awk 'NR == FNR { if ($1 == "#define" && $2 ~ /^JPL_POOL_/) { v = $3; sub(/u$/, "", v); cap[$2] = v } next }
         { m = "JPL_POOL_" toupper($1)
           if (!(m in cap)) { printf "MISSING: pool %s has no %s in the header\n", $1, m > "/dev/stderr"; exit 1 }
           print $1, $2, m, cap[m] }' \
       "$BUILD/sh_run_jpl.h" "$BUILD/pool_stems.txt" > "$BUILD/pool_list.txt"; then
  red "FAIL: a declared allocator has no capacity macro of the derived name"
  exit 1
fi
{
  cat <<'PROBE_HEAD'
/* GENERATED by verify/c/jpl_emit.sh (check 5) from the emitted header's own
   allocator declarations.  No capacity number is written below: every bound is
   that pool's JPL_POOL_* macro, so the sweep measures §6.6 against the same
   constants the allocators compare with. */
#include "sh_run_jpl.h"
#include <stdio.h>

static unsigned long failures;
static jpl_nat refused_sum;

static void bad(const char *pool, const char *what) {
  printf("  FAIL: pool %s: %s\n", pool, what);
  failures = failures + 1u;
}

PROBE_HEAD
while read -r stem handle macro cap; do
  cat <<PROBE_ONE
/* ${stem}: ${cap} cells of the header's own measure, handled as ${handle} */
static void sweep_${stem}(void) {
  const char *p = "${stem}";
  jpl_ref cap = ${macro};
  jpl_ref first;
  jpl_ref h;
  jpl_ref prev;
  jpl_ref returned;
  jpl_ref extra;
  jpl_ref served = 0u;
  jpl_ref attempts = 0u;

  first = jpl_${stem}_alloc();
  attempts = attempts + 1u;
  served = 1u;
  prev = first;
  if (first != 1u) { bad(p, "a fresh region did not begin at 1 (index 0 is JPL_NIL)"); }
  if (jpl_${stem}_is_live(first) != JPL_TRUE) { bad(p, "the cell just served reported dead"); }
  if (jpl_${stem}_is_live(JPL_NIL) != JPL_FALSE) { bad(p, "JPL_NIL reported live"); }
  h = jpl_${stem}_alloc();
  attempts = attempts + 1u;
  while (h != JPL_NIL) {
    if (h != prev + 1u) { bad(p, "two successive handles were not distinct"); }
    if (jpl_${stem}_is_live(h) != JPL_TRUE) { bad(p, "a live handle reported dead"); }
    served = served + 1u;
    prev = h;
    h = jpl_${stem}_alloc();
    attempts = attempts + 1u;
  }
  if (served != cap - 1u) { bad(p, "the region served a count other than capacity minus one"); }
  if (jpl_${stem}_next != cap) { bad(p, "next stopped somewhere other than the capacity"); }
  if (jpl_${stem}_peak != cap - 1u) { bad(p, "peak did not record the region's widest point"); }
  if (jpl_${stem}_taken != served) { bad(p, "taken counted other than the cells served"); }
  if (jpl_${stem}_refused != attempts - served) { bad(p, "refused did not count the attempts that found no cell"); }
  for (extra = 0u; extra < 3u; extra = extra + 1u) {
    (void) jpl_${stem}_alloc();
    attempts = attempts + 1u;
  }
  if (jpl_${stem}_next != cap) { bad(p, "an exhausted region moved its next: a wrapped counter"); }
  if (jpl_${stem}_refused != attempts - served) { bad(p, "refused stopped following the attempts"); }
  returned = jpl_${stem}_reset();
  if (returned != cap - 1u) { bad(p, "reset returned other than the live cells"); }
  if (jpl_${stem}_next != 1u) { bad(p, "reset did not rewind the region to empty"); }
  if (jpl_${stem}_is_live(first) != JPL_FALSE) { bad(p, "a handle from the returned region still reported live"); }
  if (jpl_${stem}_taken != served) { bad(p, "reset rewound a cumulative instrument"); }
  if (jpl_${stem}_peak != cap - 1u) { bad(p, "reset rewound the peak"); }
  refused_sum = refused_sum + jpl_${stem}_refused;
  h = jpl_${stem}_alloc();
  if (h != 1u) { bad(p, "the next region did not reuse the region from 1"); }
  if (jpl_${stem}_is_live(h) != JPL_TRUE) { bad(p, "a reused handle reported dead"); }
  (void) jpl_${stem}_reset();
  printf("    %-32s capacity %10lu  served %10lu  refused %6lu  peak %10lu\\n", p,
         (unsigned long) cap, (unsigned long) served, (unsigned long) jpl_${stem}_refused,
         (unsigned long) jpl_${stem}_peak);
}

PROBE_ONE
done < "$BUILD/pool_list.txt"
  awk '{ print "  sweep_" $1 "();" }' "$BUILD/pool_list.txt" > "$BUILD/pool_calls.inc"
  cat <<'PROBE_TAIL'
int main(void) {
PROBE_TAIL
  cat "$BUILD/pool_calls.inc"
  cat <<'PROBE_TAIL'
  if (jpl_pools_refusals() != refused_sum) {
    bad("(every pool)", "jpl_pools_refusals is not the saturating sum of the refusals");
  }
  if (jpl_pools_refusals() == 0u) {
    bad("(every pool)", "nothing was refused, so no sweep reached the bound at all");
  }
  printf("  PROBE: %lu assertion failures; refusals() = %lu, per-pool sum = %lu\n",
         failures, (unsigned long) jpl_pools_refusals(), (unsigned long) refused_sum);
  return (failures == 0u) ? 0 : 1;
}
PROBE_TAIL
} > "$BUILD/probe_pools.c"
# shellcheck disable=SC2086
if ! "$CC" ${CFLAGS%-fsyntax-only} -I"$BUILD" "$BUILD/probe_pools.c" \
       "$BUILD/sh_run_jpl_pools.o" -o "$BUILD/probe_pools" \
       2> "$BUILD/probe_cc.log"; then
  red "FAIL: the bounds probe did not build — the runtime's own declarations are unusable"
  sed 's/^/    /' "$BUILD/probe_cc.log"
  exit 1
fi
printf '    %-32s %s\n' "pool" "what a sweep of one whole region must show"
if ! "$BUILD/probe_pools" > "$BUILD/probe_out.txt" 2>&1; then
  sed 's/^/    /' "$BUILD/probe_out.txt"
  red "FAIL: the emitted pool runtime violated §6.6 at its own bound (see above)"
  exit 1
fi
sed 's/^/    /' "$BUILD/probe_out.txt"
green "PASS: every declared allocator served capacity-1, refused at the bound without wrapping, and rewound only its region"

bold "==> check 6: the runtime's own accounting closes"
# The emitter's RUNTIME SUMMARY is the only numeric input here; a missing key is a
# failure, never a zero.  Then the keys are checked against each other, against the
# header they describe, and against the translation unit that defines them — so a
# pool that gained an allocator without a counter, or a counter without an array,
# is caught as an arithmetic gap rather than as a line someone forgot to read.
RUNTIME_KEYS="pools_declared pools_with_capacity pools_without_capacity allocators_emitted
  resets_emitted live_checks_emitted counters_emitted pool_arrays_defined
  refusals_sum_terms allocator_handles_defined_in_layout
  runtime_names_colliding_with_prototypes runtime_cells_total runtime_bytes_total"
summary_key() {
  awk -v k="$1" '/^==== RUNTIME SUMMARY/ { f = 1; next }
                 f && /^$/ { exit }
                 f && $1 == k { print $2; exit }' "$BUILD/layout.txt"
}
missing=""
K_N=0
for k in $RUNTIME_KEYS; do
  v="$(summary_key "$k")"
  case "$v" in ''|*[!0-9]*) missing="$missing $k";; esac
  eval "K_$k=\${v:-}"
  K_N=$((K_N + 1))
done
if [[ -n "$missing" ]]; then
  red "FAIL: the report is missing its runtime keys:$missing — a missing measurement is not a zero"
  exit 1
fi
ACC_FAIL=0
acc() { # <expression> <what it asserts>
  # shellcheck disable=SC2086
  if ! (( $1 )); then
    red "FAIL: $2  (pools_declared=$K_pools_declared with_capacity=$K_pools_with_capacity \
without=$K_pools_without_capacity alloc=$K_allocators_emitted reset=$K_resets_emitted \
live=$K_live_checks_emitted counters=$K_counters_emitted arrays=$K_pool_arrays_defined \
terms=$K_refusals_sum_terms handles=$K_allocator_handles_defined_in_layout \
collisions=$K_runtime_names_colliding_with_prototypes cells=$K_runtime_cells_total)"
    ACC_FAIL=1
  fi
}
acc "K_pools_declared == K_pools_with_capacity + K_pools_without_capacity" \
    "the sized and unsized pools do not add up to the declared ones"
acc "K_allocators_emitted == K_pools_with_capacity" \
    "an allocator is not one per sized pool (§6.6: no capacity without an allocator)"
acc "K_resets_emitted == K_pools_with_capacity && K_live_checks_emitted == K_pools_with_capacity" \
    "a sized pool lacks its reset or its liveness check"
acc "K_counters_emitted == 4 * K_allocators_emitted" \
    "the four counters (next, peak, taken, refused) are not one set per allocator"
acc "K_pool_arrays_defined == K_allocators_emitted" \
    "a defined array has no allocator, or an allocator has no array"
acc "K_refusals_sum_terms == K_allocators_emitted" \
    "jpl_pools_refusals does not sum every pool's refusals"
acc "K_allocator_handles_defined_in_layout == K_allocators_emitted" \
    "an allocator returns a type the layout never defined"
acc "K_runtime_names_colliding_with_prototypes == 0" \
    "a §6.6 runtime name shadows a closure symbol in one translation unit"
acc "ALLOC_N == K_allocators_emitted" \
    "the header declares a different number of allocators than the emitter counted"
# cells_total against the header's own macros, and the summary against the files.
CELLS_FROM_HDR="$(awk '{ s += $4 } END { print s + 0 }' "$BUILD/pool_list.txt")"
acc "CELLS_FROM_HDR == K_runtime_cells_total" \
    "the capacities the header publishes do not sum to the report's cell count"
acc "$(grep -c '^[a-z_0-9]* jpl_[a-z0-9_]*_alloc(void) {' "$BUILD/sh_run_jpl_pools.c") == K_allocators_emitted" \
    "the translation unit defines a different number of allocators than the report counts"
acc "$(grep -c '^jpl_ref jpl_[a-z0-9_]*_next = 1u;' "$BUILD/sh_run_jpl_pools.c") == K_allocators_emitted" \
    "the translation unit does not start every region at the reserved index"
acc "$(grep -c 'jpl_pools_add_saturating(r, jpl_' "$BUILD/sh_run_jpl_pools.c") == K_refusals_sum_terms" \
    "the emitted refusals sum has a different number of terms than the report counts"
# and the probe must have swept exactly the pools the report counts.
acc "$(grep -c '^    [a-z]' "$BUILD/probe_out.txt") == K_allocators_emitted" \
    "the bounds sweep covered a different number of pools than the runtime emits"
# Three readings of the runtime: the report's table, the header's declarations, and
# the sweep generated from them.  Stem and capacity macro must agree across all three,
# so a pool cannot be sized in one artifact and named differently in another.
awk '/^==== POOL RUNTIME/,/^$/' "$BUILD/layout.txt" \
  | awk '$5 ~ /^_alloc/ { print $1, $2 }' | sort > "$BUILD/report_pools.txt"
awk '{ print $1, $3 }' "$BUILD/pool_list.txt" | sort > "$BUILD/header_pools.txt"
if [[ "$(wc -l < "$BUILD/report_pools.txt" | tr -d ' ')" != "$K_allocators_emitted" ]] \
   || ! diff -q "$BUILD/report_pools.txt" "$BUILD/header_pools.txt" > /dev/null; then
  red "FAIL: the report's pool-runtime table and the header's allocator declarations are not the same $K_allocators_emitted pools"
  diff -u "$BUILD/report_pools.txt" "$BUILD/header_pools.txt"
  ACC_FAIL=1
fi
if [[ $ACC_FAIL -eq 0 ]]; then
  green "PASS: $K_N runtime keys, the header's $ALLOC_N allocators and the TU's $K_pool_arrays_defined arrays are one account"
  printf '    %s cells across %s sized pools; %s unsized pools get no runtime, as §6.6 requires\n' \
    "$K_runtime_cells_total" "$K_pools_with_capacity" "$K_pools_without_capacity"
else
  # §6.6's own accounting is not advisory: a report that does not add up describes a
  # runtime nobody can trust, so the run stops here rather than continuing to print PASS
  # lines below it.
  red "FAIL: the runtime accounting did not close (see the FAIL lines above)"
  exit 1
fi

bold "==> check 7: the edge tables, re-derived by paths that never read a table (JPL.md §6.7)"
# §6.7's first slice is a DERIVATION, so a rung that reads the emitted table and agrees with
# itself proves nothing — a table hand-written to match the layout would pass that and still
# be wrong for a constructor nobody re-checked.  Four readings that meet only here must agree:
#   (a) the header's OWN tag comments.  node_layer prints `#define JPL_CMD_EXT 1u  /* Ext of
#       nat, text_list */` from the constructor's own argument list, so re-counting rows and
#       arities there is a second reading of the declarations that never saw the edge section;
#   (b) the artifact's `.mli` text, for every pool whose cell is a `*_node`: the number of
#       alternatives, and their arity with the PARENTHESIS DEPTH counted, so `Case of text *
#       (text list * cmd list) list` is two slots and not three;
#   (c) the generated translation unit's initialiser, token by token — including the two
#       structural claims a collector depends on: a node row's FIRST word is its tag and so is
#       SCALAR, and a row's UNUSED words are its trailing words, never a hole in the middle
#       that an "arity = width minus the tail" reading would walk straight past;
#   (d) the report's EDGE SUMMARY keys, which must equal (a), (b) and (c) and satisfy the
#       partition identity scalar + unused + edge == entries.
# A missing key is a failure, never a zero — the same convention as check 6.
EDGE_KEYS="edge_tables_emitted edge_rows_derived edge_entries_derived edge_class_scalars
  edge_class_unuseds edge_class_edges edge_target_pools edge_aggregates_flattened
  edge_width_checks_emitted edge_class_partition_residual"
edge_key() {
  awk -v k="$1" '/^==== EDGE SUMMARY/ { f = 1; next }
                 f && /^$/ { exit }
                 f && $1 == k { print $2; exit }' "$BUILD/layout.txt"
}
E_FAIL=0
E_MISSING=""
for k in $EDGE_KEYS; do
  v="$(edge_key "$k")"
  case "$v" in
    ''|*[!0-9]*) E_MISSING="$E_MISSING $k";;
  esac
  eval "E_$k=\${v:-0}"
done
if [[ -n "$E_MISSING" ]]; then
  red "FAIL: the report is missing its edge keys:$E_MISSING — a missing measurement is not a zero"
  exit 1
fi

# (a) the tag comments, read out of the header.
cat > "$BUILD/edges_from_tags.awk" <<'AWK_TAGS'
# Prints "STEM rows width sum_arity" for every macro family whose tag lines carry a
# constructor comment.  The comment must LOOK like a constructor — `Ext of nat,
# text_list`, `Skip (no payload)` — which excludes the capacity, edge-class and JPL_C_*
# defines without an exception list; the macro's own suffix must still equal the
# upper-cased name the comment opens with, so a stray comment cannot invent a family.
$1 == "#define" && $0 ~ /\/\* [A-Z][A-Za-z0-9_]* (of |\(no payload\))/ {
  name = $2
  up = toupper($5)
  if (length(name) > length(up) + 5 && substr(name, length(name) - length(up)) == "_" up) {
    cmt = $0
    sub(/^.*\/\* /, "", cmt)
    arity = (cmt ~ /no payload/) ? 0 : 1
    if (arity == 1) {
      args = cmt
      sub(/^[A-Za-z0-9_]+ of /, "", args)
      arity = gsub(/,/, ",", args) + 1
    }
    stem = substr(name, 5, length(name) - length(up) - 5)
    rows[stem]++
    if (arity + 1 > width[stem]) width[stem] = arity + 1
    sum[stem] += arity
  }
}
END { for (s in rows) printf "%s %d %d %d\n", s, rows[s], width[s], sum[s] }
AWK_TAGS
awk -f "$BUILD/edges_from_tags.awk" "$BUILD/sh_run_jpl.h" | sort > "$BUILD/tagrows.txt"

# (c) the initialisers, token by token, with the header's own NPOS/NROWS and target set.
cat > "$BUILD/edges_from_table.awk" <<'AWK_TAB'
function flushrow(   P, i, t, n, k, sawu) {
  if (!inrow) return
  inrow = 0
  n = split(buf, P, ",")
  k = 0
  sawu = 0
  for (i = 1; i <= n; i++) {
    t = P[i]
    gsub(/^[ \t]+|[ \t]+$/, "", t)
    if (t == "") continue
    k++
    if (t == "JPL_EDGE_SCALAR") sc_here++
    else if (t == "JPL_EDGE_UNUSED") un_here++
    else if (t ~ /^JPL_EDGE_TO_[A-Z0-9_]+_POOL$/) {
      ed_here++
      u = t
      sub(/^JPL_EDGE_TO_/, "", u)
      sub(/_POOL$/, "", u)
      if (!(u in target)) { printf "BADTARGET %s\n", u; badtarget++ }
    }
    else { printf "BARENTRY %s [%s]\n", cur, t; bare++ }
    if (k == 1 && isnode[cur] == 1 && t != "JPL_EDGE_SCALAR") {
      printf "TAGWORD %s [%s]\n", cur, t; badfirst++
    }
    if (t == "JPL_EDGE_UNUSED") sawu = 1
    else if (sawu) { printf "HOLE %s\n", cur; badhole++; break }
  }
  if (k == 0) { printf "EMPTYROW %s\n", cur; badrow++ ; return }
  rows_here++
  ent_here += k
  if (k != npos[cur]) { printf "WIDTH %s row %d has %d entries, NPOS is %d\n", cur, rows_here, k, npos[cur]; badwidth++ }
  buf = ""
}
FNR == NR {
  if ($1 == "#define") {
    name = $2
    if (name ~ /^JPL_[A-Z0-9_]+_NPOS$/) {
      s = name; sub(/^JPL_/, "", s); sub(/_NPOS$/, "", s)
      v = $3; sub(/u$/, "", v); npos[tolower(s)] = v
    } else if (name ~ /^JPL_[A-Z0-9_]+_NROWS$/) {
      s = name; sub(/^JPL_/, "", s); sub(/_NROWS$/, "", s)
      v = $3; sub(/u$/, "", v); nrows[tolower(s)] = v
    } else if (name ~ /^JPL_EDGE_TO_[A-Z0-9_]+_POOL$/) {
      s = name; sub(/^JPL_EDGE_TO_/, "", s); sub(/_POOL$/, "", s)
      target[s] = 1
    }
  } else if ($1 == "extern" && $3 ~ /^jpl_[a-z0-9_]*_pool\[JPL_POOL_/) {
    s = $3; sub(/^jpl_/, "", s); sub(/_pool\[.*$/, "", s)
    cell[s] = $2
    isnode[s] = ($2 ~ /_node$/) ? 1 : 0
  }
  next
}
/^const jpl_nat jpl_[a-z0-9_]*_edge\[JPL_[A-Z0-9_]+_NEDGE\] = \{$/ {
  cur = $3; sub(/^jpl_/, "", cur); sub(/_edge\[.*$/, "", cur)
  inrow = 0; buf = ""
  rows_here = 0; ent_here = 0; sc_here = 0; un_here = 0; ed_here = 0
  if (!(cur in npos) || !(cur in nrows)) { printf "NOMACRO %s\n", cur; badmacro++ }
  next
}
cur != "" {
  if ($0 == "};") {
    flushrow()
    printf "STEM %s %d %d %d %d %d %d %d %d %s\n", cur, npos[cur], nrows[cur], rows_here, ent_here, sc_here, un_here, ed_here, isnode[cur], cell[cur]
    cur = ""
    next
  }
  if ($0 ~ /^  \/\* /) { flushrow(); inrow = 1; next }
  if (inrow) buf = buf " " $0
  next
}
AWK_TAB
awk -f "$BUILD/edges_from_table.awk" "$BUILD/sh_run_jpl.h" "$BUILD/sh_run_jpl_pools.c" \
  > "$BUILD/tablerows.txt" 2>&1
grep '^STEM ' "$BUILD/tablerows.txt" | sort > "$BUILD/table_stems.txt"
VIOL="$(grep -v '^STEM ' "$BUILD/tablerows.txt" || true)"
if [[ -n "$VIOL" ]]; then
  printf '%s\n' "$VIOL" | sed 's/^/    /'
  red "FAIL: an edge table is not well-formed (a bare entry, a hole, a tag word read as an edge, or a row that is not NPOS wide)"
  E_FAIL=1
fi
# Reading (a) only counts families it found; a family nobody declared would be silently
# absent.  So the tag-comment families must be exactly the pools whose cell is a node —
# one set the emitter's struct layer published, the other its edge layer read.
awk '{ print $1 }' "$BUILD/tagrows.txt" | sort > "$BUILD/tag_families.txt"
awk '$1 == "STEM" && $10 == 1 { print $2 }' "$BUILD/table_stems.txt" \
  | tr 'a-z' 'A-Z' | sort > "$BUILD/node_families.txt"
if ! diff -q "$BUILD/tag_families.txt" "$BUILD/node_families.txt" > /dev/null; then
  red "FAIL: the header's constructor-comment families are not the pools whose cells are nodes"
  diff -u "$BUILD/node_families.txt" "$BUILD/tag_families.txt"
  E_FAIL=1
fi

# (b) the artifact's own declaration, for the pools whose cells are nodes.
cat > "$BUILD/ctors_from_mli.awk" <<'AWK_CTOR'
# rows, sum of top-level arities, widest arity — read from the .mli's own alternatives.
BEGIN { f = 0; rows = 0; sum = 0; max = 0 }
$0 ~ "^type[ \t]+" T "[ \t]*=[ \t]*$" { f = 1; next }
f && !/^\|/ { f = 0 }
f {
  line = $0
  arity = 0
  if (line ~ /^\| ?[A-Za-z0-9_]+ of /) {
    sub(/^\| ?[A-Za-z0-9_]+ of /, "", line)
    d = 0
    arity = 1
    for (i = 1; i <= length(line); i++) {
      c = substr(line, i, 1)
      if (c == "(") d++
      else if (c == ")") d--
      else if (c == "*" && d == 0) arity++
    }
  }
  rows++
  sum += arity
  if (arity > max) max = arity
}
END { printf "%d %d %d\n", rows, sum, max }
AWK_CTOR

printf '    %-30s %5s %5s %6s %7s %7s %7s  %s\n' "pool" "NPOS" "rows" "entries" "scalar" \
  "unused" "edges" "re-derived from the tag comments and the .mli"
FLAT_FROM_CELLS=0
while read -r stem _handle _macro _cap; do
  u="$(printf '%s' "$stem" | tr 'a-z' 'A-Z')"
  line="$(awk -v s="$stem" '$1 == "STEM" && $2 == s { print $3, $4, $5, $6, $7, $8, $9, $10, $11 }' "$BUILD/table_stems.txt")"
  if [[ -z "$line" ]]; then
    red "FAIL: pool $stem is declared and sized but has no edge table in the translation unit"
    E_FAIL=1
    continue
  fi
  read -r np nr rws ents scs uns eds isnode cellname <<< "$line"
  # §6.7's flattened-aggregate claim, derived rather than quoted: the only aggregate a
  # pooled cell holds BY VALUE is a pair-list's element, and the layout names exactly
  # those cells jpl_pair_*.  One pair per such cell, and the cell's width is the pair's
  # two words plus the tail — so the cell's NAME predicts both the count and the width,
  # and a table that is 3 words wide for a cell that names no pair is a cell this
  # reading cannot explain.
  case "$cellname" in
    jpl_pair_*)
      FLAT_FROM_CELLS=$((FLAT_FROM_CELLS + 1))
      if [[ "$np" != "3" ]]; then
        red "FAIL: $cellname holds a by-value pair but its row is $np words, not the pair's two plus the tail"
        E_FAIL=1
      fi
      ;;
    *)
      if [[ "$isnode" != "1" && "$np" == "3" ]]; then
        red "FAIL: $stem's row is 3 words but its cell $cellname declares no by-value aggregate: width 3 without a jpl_pair_* cell is a word nobody can say the meaning of"
        E_FAIL=1
      fi
      ;;
  esac
  tg="$(awk -v s="$u" '$1 == s { print $2, $3, $4 }' "$BUILD/tagrows.txt")"
  if [[ -n "$tg" ]]; then
    read -r trows twidth tsum <<< "$tg"
    if [[ "$trows" != "$nr" ]]; then
      red "FAIL: $stem declares NROWS $nr but the header's tag comments count $trows constructors"
      E_FAIL=1
    fi
    if [[ "$twidth" != "$np" ]]; then
      red "FAIL: $stem declares NPOS $np but its widest constructor in the tag comments is $twidth words (tag plus arity)"
      E_FAIL=1
    fi
    if [[ "$isnode" == "1" ]]; then
      read -r mrows msum mmax <<< "$(awk -v T="$stem" -f "$BUILD/ctors_from_mli.awk" "$MLI")"
      # A row is the tag word PLUS the constructor's slots, so the cell is one word
      # wider than its widest arity.
      if [[ "$mrows" != "$nr" || "$((mmax + 1))" != "$np" ]]; then
        red "FAIL: $stem's node cell does not match sh_run_c.mli: $mrows alternatives of widest arity $mmax (tag + arity = $((mmax + 1))), table says NROWS $nr NPOS $np"
        E_FAIL=1
      fi
      # The padding is then arithmetic, not judgement: every row loses (width - 1 - arity)
      # words to UNUSED, so the .mli's own arities predict the unused count exactly.
      expect_un="$(( nr * np - nr - msum ))"
      if [[ "$uns" != "$expect_un" ]]; then
        red "FAIL: $stem has $uns UNUSED words but the .mli's arities predict $expect_un"
        E_FAIL=1
      fi
    fi
  elif [[ "$nr" != "1" ]]; then
    red "FAIL: $stem declares NROWS $nr but the header carries no tag comments for it: an untagged cell is one row"
    E_FAIL=1
  fi
  if [[ "$rws" != "$nr" ]]; then
    red "FAIL: $stem's table holds $rws labelled rows for a header that declares $nr"
    E_FAIL=1
  fi
  if [[ "$ents" != "$(( nr * np ))" ]]; then
    red "FAIL: $stem's table holds $ents entries, not NROWS x NPOS = $(( nr * np ))"
    E_FAIL=1
  fi
  if [[ "$(( scs + uns + eds ))" != "$ents" ]]; then
    red "FAIL: $stem's classes do not partition its entries: $scs + $uns + $eds != $ents"
    E_FAIL=1
  fi
  printf '    %-30s %5s %5s %6s %7s %7s %7s  %s\n' "$stem" "$np" "$nr" "$ents" "$scs" "$uns" \
    "$eds" "$([[ "$isnode" == "1" ]] && echo node || echo cell)"
done < "$BUILD/pool_list.txt"

# (d) the three readings against the report's own keys.
T_ROWS="$(awk '{ s += $5 } END { print s + 0 }' "$BUILD/table_stems.txt")"
T_ENT="$(awk '{ s += $6 } END { print s + 0 }' "$BUILD/table_stems.txt")"
T_SC="$(awk '{ s += $7 } END { print s + 0 }' "$BUILD/table_stems.txt")"
T_UN="$(awk '{ s += $8 } END { print s + 0 }' "$BUILD/table_stems.txt")"
T_ED="$(awk '{ s += $9 } END { print s + 0 }' "$BUILD/table_stems.txt")"
T_N="$(( $(wc -l < "$BUILD/table_stems.txt" | tr -d ' ') ))"
edge_acc() { # <expression> <what it asserts>
  # shellcheck disable=SC2086
  if ! (( $1 )); then
    red "FAIL: $2  (report: tables=$E_edge_tables_emitted rows=$E_edge_rows_derived entries=$E_edge_entries_derived scalar=$E_edge_class_scalars unused=$E_edge_class_unuseds edges=$E_edge_class_edges targets=$E_edge_target_pools | files: tables=$T_N rows=$T_ROWS entries=$T_ENT scalar=$T_SC unused=$T_UN edges=$T_ED)"
    E_FAIL=1
  fi
}
edge_acc "T_N == E_edge_tables_emitted" "a table is emitted that the report does not count, or the reverse"
edge_acc "T_N == K_pools_with_capacity" "the tables do not cover exactly the pools §6.6 sized"
edge_acc "T_ROWS == E_edge_rows_derived" "the report's row count is not the initialisers' row count"
edge_acc "T_ENT == E_edge_entries_derived" "the report's entry count is not the initialisers' entry count"
edge_acc "T_SC == E_edge_class_scalars && T_UN == E_edge_class_unuseds && T_ED == E_edge_class_edges" \
    "the report's class census is not the census written into the translation unit"
edge_acc "E_edge_entries_derived == E_edge_class_scalars + E_edge_class_unuseds + E_edge_class_edges" \
    "the three classes are not a partition of the entries"
edge_acc "E_edge_class_partition_residual == 0" "the emitter itself measured a partition gap"
edge_acc "E_edge_width_checks_emitted == E_edge_tables_emitted" \
    "a table has no jpl_check_<stem>_edge_covers_the_cell typedef"
# The target set and the pool set must be the same eight names, in both directions: an edge
# that names no pool is a dangling forwarding target, and a pool no edge can name is a cell
# nothing reaches, which is §6.6's rule re-cut against §6.7's table.
awk '$1 == "#define" && $2 ~ /^JPL_EDGE_TO_/ { s = $2; sub(/^JPL_EDGE_TO_/, "", s); sub(/_POOL$/, "", s); print tolower(s) }' \
  "$BUILD/sh_run_jpl.h" | sort > "$BUILD/edge_targets.txt"
awk '{ print $1 }' "$BUILD/pool_list.txt" | sort > "$BUILD/edge_pools.txt"
if ! diff -q "$BUILD/edge_targets.txt" "$BUILD/edge_pools.txt" > /dev/null; then
  red "FAIL: the pools an edge may name are not the pools the header declares"
  diff -u "$BUILD/edge_pools.txt" "$BUILD/edge_targets.txt"
  E_FAIL=1
fi
edge_acc "E_edge_target_pools == K_pools_declared" "an edge may name a different number of pools than the layout declares"
# The width of a table is a property of its cell, and §6.7 says so in C: every table sits
# under a `jpl_check_<stem>_edge_covers_the_cell`.  Counting those typedefs in the header is
# a third reading of the same claim — the report, the file, and the row widths parsed above.
WCHK="$(grep -c '^typedef char jpl_check_[a-z0-9_]*_edge_covers_the_cell' "$BUILD/sh_run_jpl.h")"
edge_acc "WCHK == E_edge_width_checks_emitted && WCHK == T_N" \
    "an edge table's width is not pinned to its cell's sizeof by a typedef the compiler reads"
edge_acc "E_edge_aggregates_flattened == FLAT_FROM_CELLS" \
    "the emitter flattened a different number of by-value aggregates than the cells the header names jpl_pair_*: the claim this key measures is §6.7's 'the only aggregate a pooled cell holds by value is a cons cell's element pair', and the two readings of it moved apart"
if [[ $E_FAIL -ne 0 ]]; then
  # §6.7's first slice is a derivation, so an edge table that any one of the four readings
  # refuses is not a data dependency the collector can be built on: stop here.
  red "FAIL: the edge tables are not the four readings' common answer (see above)"
  exit 1
fi
green "PASS: $E_edge_tables_emitted tables, $E_edge_rows_derived rows and $E_edge_entries_derived classes agree with the header's tag comments, the .mli's own arities, and the initialisers written per word"
printf '    %s scalar + %s unused + %s edges; %s by-value aggregate position(s) flattened, one per jpl_pair_* cell; every row is NPOS wide, every node row starts at its tag, no UNUSED sits inside a row\n' \
  "$E_edge_class_scalars" "$E_edge_class_unuseds" "$E_edge_class_edges" "$E_edge_aggregates_flattened"

bold "==> check 8: the vendored evidence"
if [[ "${JPL_REGEN:-0}" == "1" ]]; then
  cp "$BUILD/sh_run_jpl.h" "$HDR"
  cp "$BUILD/sh_run_jpl_pools.c" "$POOLS"
  cp "$BUILD/layout.txt" "$EVID"
  green "PASS: regenerated ${HDR#"$REPO"/}, ${POOLS#"$REPO"/} and ${EVID#"$REPO"/}"
  exit 0
fi
if [[ ! -f "$HDR" || ! -f "$POOLS" || ! -f "$EVID" ]]; then
  red "FAIL: ${HDR#"$REPO"/}, ${POOLS#"$REPO"/} or ${EVID#"$REPO"/} missing — generate with: JPL_REGEN=1 $0"
  exit 1
fi
STALE=0
for ev in "$HDR:sh_run_jpl.h" "$POOLS:sh_run_jpl_pools.c" "$EVID:layout.txt"; do
  if ! diff -q "${ev%:*}" "$BUILD/${ev#*:}" > /dev/null; then
    red "FAIL: ${ev%:*} is stale vs a fresh emission"
    diff -u "${ev%:*}" "$BUILD/${ev#*:}" | head -40
    STALE=1
  fi
done
if [[ $STALE -ne 0 ]]; then
  red "      re-run with JPL_REGEN=1 after checking the change is intended"
  exit 1
fi
green "PASS: the header, the pools TU and the layout report are identical to a fresh emission"

bold "==> what this layer still cannot do"
# Read straight off the report, so the limitation is the tool's own statement and
# not a claim written into a shell script.
awk '/^==== WHAT THIS LAYER COULD NOT SIZE/{f=1;next} /^==== /{f=0} f' \
  "$BUILD/layout.txt" | sed 's/^/    /'
printf '    %s report lines are marked PENDING\n' \
  "$(grep -c PENDING "$BUILD/layout.txt")"
exit 0
