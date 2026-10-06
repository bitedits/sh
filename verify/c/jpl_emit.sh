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
#      so -Wconversion and -Wsign-conversion now apply to real definitions.  Since
#      §6.7's ii-b-2b it owns a second one, the current-interval indicator, and the
#      one function allowed to write it.
#   4  the differential fold: the ten capacities the emitter folded out of the
#      artifact's SYNTAX agree with the ten fields of jpl_caps_table as the
#      OCaml runtime EVALUATES them.  Those are two independent readings of the
#      same extracted term — a constant folder and the interpreter — so their
#      agreement is the measurement that retires "the folder is right by
#      construction".  The probe carries no numbers of its own.
#   5  the runtime DRIVEN AT ITS BOUNDS (§6.6, two intervals since §6.7's ii-b-2b):
#      one sweep per declared allocator, generated from the header's own
#      `_alloc(void);` lines so it carries no capacity literal either.  It is this
#      gate that turns §6.6's prose into a measurement — that a region of C cells
#      serves exactly C-1, that index 0 stays reserved, that exhaustion answers with
#      the nil handle and counts it rather than wrapping, and that a reset rewinds
#      the region but not the instruments.  The same sweep is also the ONLY place
#      §6.7's design item (iii) is measured: it keeps a handle from the interval it
#      swaps away and asserts the runtime calls it dead while that handle still sits
#      BELOW the current `next` — a case no single-interval runtime can even express.
#   6  the accounting closes: the report's RUNTIME SUMMARY keys agree with each
#      other arithmetically, with the names the header declares, and with the
#      arrays the translation unit defines.  A missing key is a failure, not a 0.
#      Since ii-b-2b this includes the interval arithmetic — the index domain must
#      divide back into cap-per-interval, the origin domain must be the index
#      domain, and the indicator must have exactly one writer in the file that
#      defines it.
#   7  §6.7's per-word edge tables: every table's rows, width and class census are
#      re-derived by three readings that never look at a table — the header's own
#      constructor comments, the artifact's .mli alternatives with parenthesis
#      depth counted (so `Case of text * (text list * cmd list) list` is two slots),
#      and the initialiser tokens — plus the two properties a collector needs: a
#      node row's first word is its tag, and an UNUSED word is trailing, never a
#      hole an "width minus the tail" reading would walk past.
#   8  the vendored evidence (sh_run_jpl.h + sh_run_jpl_pools.c + layout.txt) is
#      byte-identical to this run; under JPL_REGEN=1 the re-pin is DEFERRED until
#      every check below has passed.
#   9  §6.7 paragraph 5bis's evacuation DRIVEN: a probe GENERATED from the emitted edge
#      tables — awk finds, for every pool, the word of the cell whose class names that
#      same pool — builds a chain of three cells in the interval a boundary reads from,
#      crosses the boundary in the runtime's own order (swap, rewind, queue, evacuate,
#      drain) and crosses it BACK.  That second round is the measurement the static
#      account cannot make: last round's forwarding pointers are still in the origin
#      table, the rewound interval hands the same indices out again, and only alloc's
#      clear plus evac's fourth arm keep a parent from being handed a cell that this
#      round re-allocated for something else.
#
# Inputs are the VENDORED artifact (src/kernel/sh_run_c.ml{,i}) that block 2c of
# verify_models.sh already byte-binds to a fresh Coq Extraction, and the same
# roots the front end (2d) gates, so this layer describes exactly the code the
# subset verdict covers.
#
# Exit codes
#   0  all nine checks pass
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
REGEN_PIN=0   # set by check 8 under JPL_REGEN=1; the copy happens only once check 9 has passed
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

bold "==> check 5: the pool runtime driven at its bounds (JPL.md §6.6, §6.7 paragraph 4)"
# The sweep is GENERATED from the emitted header rather than written out: one
# function per `jpl_<stem>_alloc(void);` declaration, and every bound inside it is
# that pool's own JPL_* macro.  So the probe asserts §6.6's and §6.7's properties
# against the same constants the allocators compare with, and carries no capacity
# number of its own — the same discipline as the cap probe above.  This is gate
# scaffolding, not emitted code: it prints, which the shipped runtime never does.
if ! grep '^[a-z_0-9]* jpl_[a-z0-9_]*_alloc(void);' "$BUILD/sh_run_jpl.h" \
     | awk '{ h = $1; s = $2; sub(/^jpl_/, "", s); sub(/_alloc\(void\);$/, "", s); print s, h }' \
       > "$BUILD/pool_stems.txt"; then
  red "FAIL: the header declares no allocator at all"
  exit 1
fi
# Pair every stem with the capacity macro §6.6 says it must be sized from, and with
# the EIGHT interval macros §6.7 paragraph 4 says its bounds are derived through —
# since ii-b-2c that includes the OTHER pair, because the evacuation test's domain is
# the interval being read FROM and no existing bound names it.  The naming rule is
# checked here, not assumed: a pool whose macro is absent fails.
if ! awk 'BEGIN { s[1] = "_CAP"; s[2] = "_SPACE"; s[3] = "_LO_BASE"; s[4] = "_HI_BASE"; s[5] = "_CUR_BASE"; s[6] = "_CUR_TOP"; s[7] = "_OTHER_BASE"; s[8] = "_OTHER_TOP" }
         NR == FNR {
           if ($1 == "#define") {
             def[$2] = 1
             if ($2 ~ /^JPL_POOL_/ && $2 != "JPL_POOL_SPACES") { v = $3; sub(/u$/, "", v); cap[$2] = v }
           }
           next
         }
         { m = "JPL_POOL_" toupper($1); pre = "JPL_" toupper($1)
           if (!(m in cap)) { printf "MISSING: pool %s has no %s in the header\n", $1, m > "/dev/stderr"; exit 1 }
           for (i = 1; i <= 8; i++) {
             if (!((pre s[i]) in def)) {
               printf "MISSING: pool %s has no %s%s, the interval bound it must be read through\n", $1, pre, s[i] > "/dev/stderr"
               exit 1
             }
           }
           print $1, $2, m, cap[m], pre }' \
       "$BUILD/sh_run_jpl.h" "$BUILD/pool_stems.txt" > "$BUILD/pool_list.txt"; then
  red "FAIL: a declared allocator has no capacity macro or no interval macro of the derived name"
  exit 1
fi
{
  cat <<'PROBE_HEAD'
/* GENERATED by verify/c/jpl_emit.sh (check 5) from the emitted header's own
   allocator declarations.  No capacity number is written below: every bound is
   that pool's JPL_* macro, so the sweep measures §6.6 and §6.7 paragraph 4
   against the same constants the allocators compare with.  Each sweep walks BOTH
   intervals of its pool and returns the single jpl_pools_space to where it found
   it, because one flipped indicator would make the next pool's bounds a different
   question than the one its own macros describe. */
#include "sh_run_jpl.h"
#include <stdio.h>

static unsigned long failures;
static jpl_nat refused_sum;

static void bad(const char *pool, const char *what) {
  printf("  FAIL: pool %s: %s\n", pool, what);
  failures = failures + 1u;
}

PROBE_HEAD
while read -r stem handle macro cap pre; do
  cat <<PROBE_ONE
/* ${stem}: ${cap} indices of ${handle}, which the header says is ${pre}_SPACE indices
   per interval x JPL_POOL_SPACES intervals, each interval serving ${pre}_CAP cells. */
static void sweep_${stem}(void) {
  const char *p = "${stem}";
  jpl_ref dim = ${macro};
  jpl_ref cells = ${pre}_CAP;
  jpl_ref region = ${pre}_SPACE;
  jpl_ref spaces = JPL_POOL_SPACES;
  jpl_ref first;
  jpl_ref h;
  jpl_ref prev;
  jpl_ref returned;
  jpl_ref extra;
  jpl_ref low_h;
  jpl_ref last_high;
  jpl_ref served = 0u;
  jpl_ref hserved = 0u;
  jpl_ref attempts = 0u;
  jpl_ref stale_below = 0u;
  jpl_ref stale_dead = 0u;
  jpl_nat before;
  jpl_nat after;

  if (jpl_pools_space != 0u) { bad(p, "a previous sweep left the interval indicator flipped"); }
  if (dim != spaces * region) { bad(p, "the array's measure is not the interval count times one interval's indices"); }

  /* 1. fill the LOW interval to exhaustion, then rewind it: §6.6's sweep, now read
      against the interval's own base instead of against 1u. */
  first = jpl_${stem}_alloc();
  attempts = attempts + 1u;
  served = 1u;
  prev = first;
  if (first != (${pre}_LO_BASE + 1u)) { bad(p, "the low interval did not begin above its own reserved index"); }
  if (jpl_${stem}_is_live(first) != JPL_TRUE) { bad(p, "the cell just served reported dead"); }
  if (jpl_${stem}_is_live(JPL_NIL) != JPL_FALSE) { bad(p, "JPL_NIL reported live"); }
  if (jpl_${stem}_is_live(${pre}_CUR_TOP) != JPL_FALSE) { bad(p, "an interval's own top index reported live with no cell at it"); }
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
  if (served != cells) { bad(p, "the low interval served a count other than its own capacity"); }
  if (served != (dim / spaces) - 1u) { bad(p, "the served count is not the array's measure over the interval count, minus one reserved index"); }
  if (jpl_${stem}_next != (${pre}_CUR_TOP)) { bad(p, "next stopped somewhere other than the current interval's top"); }
  if (jpl_${stem}_peak != cells) { bad(p, "peak did not record the interval's widest point"); }
  if (jpl_${stem}_taken != served) { bad(p, "taken counted other than the cells served"); }
  if (jpl_${stem}_refused != attempts - served) { bad(p, "refused did not count the attempts that found no cell"); }
  for (extra = 0u; extra < 3u; extra = extra + 1u) {
    (void) jpl_${stem}_alloc();
    attempts = attempts + 1u;
  }
  if (jpl_${stem}_next != (${pre}_CUR_TOP)) { bad(p, "an exhausted interval moved its next: a wrapped counter"); }
  if (jpl_${stem}_refused != attempts - served) { bad(p, "refused stopped following the attempts"); }
  returned = jpl_${stem}_reset();
  if (returned != cells) { bad(p, "reset returned other than the live cells of the low interval"); }
  if (jpl_${stem}_next != (${pre}_LO_BASE + 1u)) { bad(p, "reset did not rewind the low interval to its own reserved index"); }
  if (jpl_${stem}_is_live(first) != JPL_FALSE) { bad(p, "a handle from the returned interval still reported live"); }
  if (jpl_${stem}_taken != served) { bad(p, "reset rewound a cumulative instrument"); }
  if (jpl_${stem}_peak != cells) { bad(p, "reset rewound the peak"); }

  /* 2. §6.7's design item (iii): keep a handle from the interval the swap abandons.
      It sits BELOW the current next, so the single-interval test of §6.6 called it
      live — the aliasing debt this slice exists to discharge. */
  low_h = jpl_${stem}_alloc();
  attempts = attempts + 1u;
  served = served + 1u;
  if (low_h != (${pre}_LO_BASE + 1u)) { bad(p, "the rewound low interval did not reuse its own first index"); }
  before = jpl_pools_space;
  after = jpl_pools_swap();
  if (after != (before + 1u) % spaces) { bad(p, "the swap returned something other than the next interval index"); }
  if (jpl_pools_space != after) { bad(p, "the swap returned a value its own global does not hold"); }
  if (low_h < jpl_${stem}_next) { stale_below = stale_below + 1u; }
  if (jpl_${stem}_is_live(low_h) != JPL_FALSE) { bad(p, "a handle from the abandoned interval reported live"); }
  stale_dead = stale_dead + 1u;
  /* the allocator refuses until the driver rewinds, rather than serving the new
     interval's reserved index out of an abandoned region. */
  h = jpl_${stem}_alloc();
  attempts = attempts + 1u;
  if (h != JPL_NIL) { bad(p, "after a swap and before the rewind an allocator served a handle"); }
  if (jpl_${stem}_next != (low_h + 1u)) { bad(p, "the refusal moved next into the current interval without serving a cell"); }
  if (jpl_${stem}_refused != attempts - served) { bad(p, "the refusal at the abandoned region was not counted"); }
  returned = jpl_${stem}_reset();
  if (returned != 0u) { bad(p, "reset on the abandoned interval returned a cell count, i.e. its subtraction wrapped"); }
  if (jpl_${stem}_next != (${pre}_HI_BASE + 1u)) { bad(p, "reset did not rewind to the CURRENT interval's base"); }
  /* the origin table: zero means "not copied from anywhere", and its domain is
     every index of BOTH intervals, including the two reserved slots. */
  if (sizeof (jpl_${stem}_origin) != (dim * sizeof (jpl_ref))) { bad(p, "the origin table is not one entry per index of the array"); }
  if (jpl_${stem}_origin[low_h] != JPL_NIL) { bad(p, "an origin entry was not zero-initialised to JPL_NIL"); }
  if (jpl_${stem}_origin[${pre}_LO_BASE] != JPL_NIL) { bad(p, "a reserved index gained an origin"); }
  jpl_${stem}_origin[low_h] = (${pre}_CUR_TOP - 1u);
  if (jpl_${stem}_origin[low_h] != (${pre}_CUR_TOP - 1u)) { bad(p, "an origin written for a handle in the previous interval did not read back"); }
  jpl_${stem}_origin[dim - 1u] = low_h;
  if (jpl_${stem}_origin[dim - 1u] != low_h) { bad(p, "the last index of the origin domain is not addressable"); }

  /* 3. fill the HIGH interval: the SAME cap at twice the indices, and the SAME peak,
      because peak counts a region's cells and not positions in one big array. */
  hserved = 0u;
  first = jpl_${stem}_alloc();
  attempts = attempts + 1u;
  hserved = 1u;
  served = served + 1u;
  prev = first;
  if (first != (${pre}_HI_BASE + 1u)) { bad(p, "the high interval did not begin above its own reserved index"); }
  if (jpl_${stem}_is_live(first) != JPL_TRUE) { bad(p, "a cell of the current interval reported dead"); }
  h = jpl_${stem}_alloc();
  attempts = attempts + 1u;
  while (h != JPL_NIL) {
    if (h != prev + 1u) { bad(p, "two successive handles in the high interval were not distinct"); }
    if (jpl_${stem}_is_live(h) != JPL_TRUE) { bad(p, "a live handle in the high interval reported dead"); }
    hserved = hserved + 1u;
    served = served + 1u;
    prev = h;
    h = jpl_${stem}_alloc();
    attempts = attempts + 1u;
  }
  last_high = prev;
  if (hserved != cells) { bad(p, "the high interval served a different number of cells than the low one"); }
  if (jpl_${stem}_next != (${pre}_CUR_TOP)) { bad(p, "next stopped below the high interval's top"); }
  if (jpl_${stem}_peak != cells) { bad(p, "peak grew with the index instead of staying a per-region count"); }
  if (jpl_${stem}_taken != served) { bad(p, "taken did not follow the cells served across both intervals"); }
  if (jpl_${stem}_refused != attempts - served) { bad(p, "refused did not follow the attempts across both intervals"); }
  if (low_h < jpl_${stem}_next) { stale_below = stale_below + 1u; }
  if (jpl_${stem}_is_live(low_h) != JPL_FALSE) { bad(p, "a handle from the previous interval went live as the current region grew past it"); }
  stale_dead = stale_dead + 1u;

  /* 4. cycle back, so the next pool is measured on the interval its macros name. */
  before = jpl_pools_space;
  after = jpl_pools_swap();
  if (after != (before + 1u) % spaces) { bad(p, "the second swap did not advance the cycle"); }
  if (jpl_pools_space != after) { bad(p, "the second swap returned a value its own global does not hold"); }
  if (jpl_${stem}_is_live(last_high) != JPL_FALSE) { bad(p, "a handle of the interval just abandoned reported live"); }
  returned = jpl_${stem}_reset();
  if (returned != 0u) { bad(p, "reset returned the abandoned interval's high-water index as a cell count"); }
  if (jpl_${stem}_next != (${pre}_LO_BASE + 1u)) { bad(p, "reset did not rewind the current low interval to its own base"); }
  h = jpl_${stem}_alloc();
  attempts = attempts + 1u;
  served = served + 1u;
  if (h != (${pre}_LO_BASE + 1u)) { bad(p, "the low interval did not reuse its own first index when the cycle came back"); }
  if (jpl_${stem}_is_live(h) != JPL_TRUE) { bad(p, "a reused handle reported dead"); }
  if (stale_below == 0u) { bad(p, "no stale handle ever sat below the current next, so the interval test never had to reject one"); }
  if (stale_below != stale_dead) { bad(p, "a stale handle below the current next was not rejected as stale"); }
  (void) jpl_${stem}_reset();
  if (jpl_pools_space != 0u) { bad(p, "the sweep left the single interval indicator flipped"); }
  refused_sum = refused_sum + jpl_${stem}_refused;
  printf("    %-32s dim %8lu  cells/interval %8lu  served %10lu  stale %2lu  refused %6lu  peak %8lu\\n", p,
         (unsigned long) dim, (unsigned long) cells, (unsigned long) served,
         (unsigned long) stale_dead, (unsigned long) jpl_${stem}_refused, (unsigned long) jpl_${stem}_peak);
}

PROBE_ONE
done < "$BUILD/pool_list.txt"
  awk '{ print "  sweep_" $1 "();" }' "$BUILD/pool_list.txt" > "$BUILD/pool_calls.inc"
  cat <<'PROBE_TAIL'
int main(void) {
PROBE_TAIL
  cat "$BUILD/pool_calls.inc"
  cat <<'PROBE_TAIL'
  if (sizeof (jpl_ref) != 4u) {
    bad("(every pool)", "jpl_ref is not 4 bytes, so the report's origin byte price is measured in a unit this ABI does not use");
  }
  if (jpl_pools_space != 0u) {
    bad("(every pool)", "the sweeps ended on the second interval: the indicator is ONE global, so a pool that left it flipped is a finding about the runtime, not about this pool");
  }
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
printf '    %-32s %s\n' "pool" "what a sweep of BOTH intervals of one pool must show"
if ! "$BUILD/probe_pools" > "$BUILD/probe_out.txt" 2>&1; then
  sed 's/^/    /' "$BUILD/probe_out.txt"
  red "FAIL: the emitted pool runtime violated §6.6/§6.7 at its own bounds (see above)"
  exit 1
fi
sed 's/^/    /' "$BUILD/probe_out.txt"
green "PASS: every declared allocator served its cap in BOTH intervals, refused at each bound without wrapping, kept peak a per-region count, and called a handle from the abandoned interval dead while it sat below the current next"

bold "==> check 6: the runtime's own accounting closes"
# The emitter's RUNTIME SUMMARY is the only numeric input here; a missing key is a
# failure, never a zero.  Then the keys are checked against each other, against the
# header they describe, and against the translation unit that defines them — so a
# pool that gained an allocator without a counter, or a counter without an array,
# is caught as an arithmetic gap rather than as a line someone forgot to read.
# Since ii-b-2b the same holds of the TWO intervals: the report claims a number of
# regions, of interval macros, of origin entries and of the writers of the one
# indicator, and every one of those claims is closed against the files it describes.
RUNTIME_KEYS="pools_declared pools_with_capacity pools_without_capacity allocators_emitted
  resets_emitted live_checks_emitted counters_emitted pool_arrays_defined
  refusals_sum_terms allocator_handles_defined_in_layout
  runtime_names_colliding_with_prototypes runtime_cells_total runtime_bytes_total
  regions_per_pool space_cells_served_total interval_arithmetics_checked
  interval_macros_emitted interval_typedefs_emitted flip_typedefs_emitted
  origin_arrays_emitted origin_indices_total origin_bytes_total
  space_globals_emitted swap_functions_emitted static_bytes_total_with_origins
  mutable_globals_emitted mutable_globals_bytes scan_pointers_emitted
  word_accessors_emitted evac_functions_emitted evac_forward_arms_checked
  origin_clears_emitted queue_start_functions_emitted scan_step_functions_emitted
  drain_functions_emitted tag_guards_emitted dispatch_functions_emitted
  dispatch_arms_emitted"
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
# set before the first acc call, because acc's failure line prints it (set -u).
SPACE_ASSIGNMENTS=0
acc() { # <expression> <what it asserts>
  # shellcheck disable=SC2086
  if ! (( $1 )); then
    red "FAIL: $2  (pools_declared=$K_pools_declared with_capacity=$K_pools_with_capacity \
without=$K_pools_without_capacity alloc=$K_allocators_emitted reset=$K_resets_emitted \
live=$K_live_checks_emitted counters=$K_counters_emitted arrays=$K_pool_arrays_defined \
terms=$K_refusals_sum_terms handles=$K_allocator_handles_defined_in_layout \
collisions=$K_runtime_names_colliding_with_prototypes cells=$K_runtime_cells_total \
regions=$K_regions_per_pool per-space=$K_space_cells_served_total origins=$K_origin_arrays_emitted \
macros=$K_interval_macros_emitted space_assignments=$SPACE_ASSIGNMENTS)"
    ACC_FAIL=1
  fi
}
acc "K_pools_declared == K_pools_with_capacity + K_pools_without_capacity" \
    "the sized and unsized pools do not add up to the declared ones"
acc "K_allocators_emitted == K_pools_with_capacity" \
    "an allocator is not one per sized pool (§6.6: no capacity without an allocator)"
acc "K_resets_emitted == K_pools_with_capacity && K_live_checks_emitted == K_pools_with_capacity" \
    "a sized pool lacks its reset or its liveness check"
acc "K_counters_emitted == 7 * K_allocators_emitted + K_tag_guards_emitted + 1" \
    "the counters are not next/peak/taken/refused/copied/forwarded/badref per allocator, plus badtag per TAGGED pool, plus the dispatch's unclassified (§6.2: a counter nothing writes is refused)"
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
# ii-b-2b's own arithmetic.  Two intervals are not a comment about the pools: the
# report claims a number of regions, a macro set, a typedef per pool, an origin
# domain and ONE global with ONE writer, and each claim has to close against the
# files it describes — otherwise a pool that gained an interval in the prose and not
# in the array would still print a plausible total.
acc "K_regions_per_pool == 2" \
    "§6.7 paragraph 4 sizes every pool with TWO intervals; the report says otherwise"
acc "K_interval_arithmetics_checked == K_allocators_emitted" \
    "an allocator's pool has no dimension of SPACES x (cap + 1)"
acc "K_interval_typedefs_emitted == 4 * K_allocators_emitted" \
    "a sized pool is missing one of the four interval compile-time checks"
acc "K_interval_macros_emitted == (8 * K_allocators_emitted) + K_space_globals_emitted" \
    "the eight interval macros are not one set per sized pool plus the single JPL_POOL_SPACES"
acc "K_origin_arrays_emitted == K_allocators_emitted" \
    "an allocator has no origin table, or an origin table has no allocator"
acc "K_origin_indices_total == K_runtime_cells_total" \
    "the origin domain is not the whole index domain of both intervals"
acc "K_origin_bytes_total == K_origin_indices_total * 4" \
    "the origin tables are not 4 B per index (jpl_ref is uint32_t)"
acc "K_space_cells_served_total + K_allocators_emitted == K_runtime_cells_total / K_regions_per_pool" \
    "the intervals do not divide the index domain back into the artifact's own caps plus one reserved index each"
acc "K_static_bytes_total_with_origins == K_runtime_bytes_total + K_origin_bytes_total" \
    "the static price with origins is not the pools plus the origin tables"
acc "K_space_globals_emitted == 1 && K_swap_functions_emitted == 1" \
    "the current interval is not exactly ONE global with exactly ONE writer"
acc "K_flip_typedefs_emitted == 1" \
    "the swap's cycle length is not pinned against JPL_POOL_SPACES at compile time"
acc "$(grep -c '^jpl_ref jpl_[a-z0-9_]*_origin\[JPL_POOL_' "$BUILD/sh_run_jpl_pools.c") == K_origin_arrays_emitted" \
    "the translation unit defines a different number of origin tables than the report counts"
acc "$(grep -c '^#define \(JPL_POOL_SPACES\|JPL_[A-Z0-9_]*_\(CAP\|SPACE\|LO_BASE\|HI_BASE\|CUR_BASE\|CUR_TOP\|OTHER_BASE\|OTHER_TOP\)\) ' "$BUILD/sh_run_jpl.h") == K_interval_macros_emitted" \
    "the header publishes a different number of interval macros than the report counts"
# ii-b-2c's own arithmetic.  The copy is the rung where a counter stops being a
# measurement of an allocator and becomes a measurement of a collector, so every
# claim above is closed a second time against the two generated files: the report
# counts a function, the header declares it, the translation unit defines it, and
# the three numbers must be one number.  The tag guards are the exception that
# proves the rule — they exist only under a pool whose cell HAS a tag word, so the
# count is read from the header rather than derived from the pool count, and a
# report that emitted badtag for an untagged cell would disagree with the file.
EVAC_FUNCS="$(grep -c '^jpl_ref jpl_[a-z0-9_]*_evac(jpl_ref h) {' "$BUILD/sh_run_jpl_pools.c")"
MUTABLE_DECLS="$(grep -c '^jpl_[a-z]* jpl_[a-z0-9_]*_[a-z]* = [01]u;' "$BUILD/sh_run_jpl_pools.c")"
EDGE_TARGETS_FROM_HDR="$(grep -c '^#define JPL_EDGE_TO_[A-Z0-9_]*_POOL ' "$BUILD/sh_run_jpl.h")"
ORIGIN_MUTUAL_ARMS="$(grep -c 'origin\[o\] == h' "$BUILD/sh_run_jpl_pools.c")"
STRUCT_ASSIGNMENTS="$(grep -c '_pool\[t\] = jpl_[a-z0-9_]*_pool\[h\];' "$BUILD/sh_run_jpl_pools.c")"
acc "K_scan_pointers_emitted == K_allocators_emitted && K_evac_functions_emitted == K_allocators_emitted" \
    "an allocator has no scan pointer or no evacuation function (§6.7 paragraph 5bis: every pool is a copy target)"
acc "K_evac_functions_emitted == EVAC_FUNCS" \
    "the translation unit defines a different number of evac functions than the report counts"
acc "K_evac_forward_arms_checked == K_evac_functions_emitted" \
    "an evac is missing the four-arm forwarding test"
acc "K_evac_forward_arms_checked == ORIGIN_MUTUAL_ARMS" \
    "the mutual arm (origin[o] == h) does not appear exactly once per evac — the fourth arm is what makes the third mean THIS round"
acc "K_evac_functions_emitted == STRUCT_ASSIGNMENTS" \
    "a copy is not exactly one C99 structure assignment (5bis refuses a word-by-word copy loop and a pointer cast alike)"
acc "K_origin_clears_emitted == K_allocators_emitted" \
    "an allocator does not clear the origin of the cell it hands out"
acc "K_origin_clears_emitted == $(grep -c '^    jpl_[a-z0-9_]*_origin\[h\] = JPL_NIL;$' "$BUILD/sh_run_jpl_pools.c")" \
    "the clear the fourth arm depends on is not in the file that allocates"
acc "K_word_accessors_emitted == 2 * K_allocators_emitted" \
    "a pool lacks its word_at/word_put pair, which is the scan's only route to a cell's words"
acc "$(grep -c '^jpl_ref jpl_[a-z0-9_]*_word_at(jpl_ref h, jpl_ref i) {' "$BUILD/sh_run_jpl_pools.c") \
   + $(grep -c '^void jpl_[a-z0-9_]*_word_put(jpl_ref h, jpl_ref i, jpl_ref v) {' "$BUILD/sh_run_jpl_pools.c") \
     == K_word_accessors_emitted" \
    "the accessor pair counted in the report is not the pair defined in the translation unit"
acc "K_queue_start_functions_emitted == K_scan_step_functions_emitted && K_scan_step_functions_emitted == K_drain_functions_emitted && K_drain_functions_emitted == K_allocators_emitted" \
    "the queue is not one start/step/drain triplet per pool"
acc "$(grep -c '^void jpl_[a-z0-9_]*_queue_start(void) {' "$BUILD/sh_run_jpl_pools.c") == K_queue_start_functions_emitted" \
    "a queue_start counted in the report is not defined in the file"
acc "$(grep -c '^void jpl_[a-z0-9_]*_scan_one(void) {' "$BUILD/sh_run_jpl_pools.c") == K_scan_step_functions_emitted" \
    "a scan step counted in the report is not defined in the file"
acc "$(grep -c '^void jpl_[a-z0-9_]*_drain(void) {' "$BUILD/sh_run_jpl_pools.c") == K_drain_functions_emitted" \
    "a drain counted in the report is not defined in the file"
acc "K_tag_guards_emitted == $(grep -c '^  if (row >= JPL_[A-Z0-9_]*_NROWS) {' "$BUILD/sh_run_jpl_pools.c")" \
    "a tag guard counted in the report is not the guard the scan walks its row behind"
acc "K_tag_guards_emitted == $(grep -c '^extern jpl_ref jpl_[a-z0-9_]*_badtag;' "$BUILD/sh_run_jpl.h")" \
    "badtag is declared for a different number of pools than the ones with tag guards — §6.2's rule is a declaration pattern, not a prose promise"
acc "K_dispatch_functions_emitted == 1 && K_dispatch_arms_emitted == EDGE_TARGETS_FROM_HDR" \
    "the dispatch is not ONE function whose arms cover exactly the target ids the header publishes"
acc "K_dispatch_functions_emitted == $(grep -c '^jpl_ref jpl_pools_evac_by_class(jpl_nat cls, jpl_ref h) {' "$BUILD/sh_run_jpl_pools.c")" \
    "the one dispatch counted in the report is not the one defined in the translation unit"
acc "K_dispatch_arms_emitted == $(grep -c '== JPL_EDGE_TO_[A-Z0-9_]*_POOL) { r = jpl_[a-z0-9_]*_evac(h); }' "$BUILD/sh_run_jpl_pools.c")" \
    "the arms written into the dispatch do not number the targets the report counts"
acc "$(grep -c '^typedef char jpl_check_dispatch_arms_cover_every_target' "$BUILD/sh_run_jpl.h") == 1" \
    "the target-id domain is not pinned to the dispatch's last arm by a typedef the compiler reads"
acc "K_mutable_globals_emitted == K_counters_emitted + K_scan_pointers_emitted + K_space_globals_emitted" \
    "the mutable statics are not the counters, one scan pointer per pool, and the one interval indicator"
acc "K_mutable_globals_emitted == MUTABLE_DECLS" \
    "the translation unit defines a different number of mutable statics than the report counts — §6.6's claim that THIS file is the only C owning one is a countable claim"
acc "K_mutable_globals_bytes == K_mutable_globals_emitted * 4" \
    "the mutable storage is not 4 B per global (jpl_ref and jpl_nat are uint32_t)"
acc "$(grep -c '^typedef char jpl_check_pools_flip_cycles_the_intervals' "$BUILD/sh_run_jpl.h") == K_flip_typedefs_emitted" \
    "the header does not carry the one typedef that pins the swap's cycle length"
acc "$(grep -c '^jpl_nat jpl_pools_swap(void) {' "$BUILD/sh_run_jpl_pools.c") == K_swap_functions_emitted" \
    "the translation unit defines a different number of swap functions than the report counts"
# "exactly one writer" is the load-bearing claim about the global, so it is counted
# in the file that defines it: the definition plus one assignment and no more.
SPACE_ASSIGNMENTS="$(grep -c 'jpl_pools_space[[:space:]]*=[^=]' "$BUILD/sh_run_jpl_pools.c")"
acc "SPACE_ASSIGNMENTS == 1 + K_space_globals_emitted" \
    "the interval indicator has more assignments than its own definition plus its one writer"
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
  printf '    %s indices = %s sized pools x %s intervals, serving %s cells per interval summed\n' \
    "$K_runtime_cells_total" "$K_pools_with_capacity" "$K_regions_per_pool" "$K_space_cells_served_total"
  printf '    %s B of pools + %s B of origin tables = %s B static; %s unsized pools get no runtime, as §6.6 requires\n' \
    "$K_runtime_bytes_total" "$K_origin_bytes_total" "$K_static_bytes_total_with_origins" "$K_pools_without_capacity"
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
while read -r stem _handle _macro _cap _pre; do
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
# The byte-comparison runs on every invocation; the RE-PIN is deferred to the end of this
# script, because a copied file is only evidence once every check that reads it has passed —
# and check 9 drives the emission this very run wrote, so pinning before it would let a
# failing evacuation be vendored as though it had been measured.
if [[ "${JPL_REGEN:-0}" == "1" ]]; then
  REGEN_PIN=1
  bold "    JPL_REGEN=1: ${HDR#"$REPO"/}, ${POOLS#"$REPO"/} and ${EVID#"$REPO"/} will be re-pinned only if all nine checks pass"
else
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
fi

bold "==> check 9: the evacuation DRIVEN across two step boundaries (JPL.md §6.7 paragraph 5bis)"
# The edge tables say which word of a cell is an edge; only a DRIVE can say whether the
# runtime collects with it.  The probe below is GENERATED, and what it generates from is
# the emitted tables themselves: awk walks every `jpl_<stem>_edge[]` row, finds the entry
# that names its OWN pool, and takes that word index and that row index — so the chain
# sweep's shape is a property of the table it reads, not of a number written here.  For a
# tagged cell the row index doubles as the tag word's value, which is what makes the sweep
# also measure the tag-to-row arithmetic scan_one does.
if ! awk '
  NR == FNR {
    if ($1 == "#define" && $2 ~ /^JPL_[A-Z0-9_]+_NPOS$/) { k = $2; sub(/^JPL_/, "", k); sub(/_NPOS$/, "", k); pos[k] = $3 + 0 }
    if ($1 == "#define" && $2 ~ /^JPL_[A-Z0-9_]+_NROWS$/) { k = $2; sub(/^JPL_/, "", k); sub(/_NROWS$/, "", k); rowc[k] = $3 + 0 }
    next
  }
  /^const jpl_nat jpl_/ {
    s = $0; sub(/^const jpl_nat jpl_/, "", s); sub(/_edge\[.*$/, "", s)
    up = toupper(s); stem = s; width = pos[up]; nrows = rowc[up]
    if (width == 0 || nrows == 0) { printf "DERIVE: the edge table for %s has no NPOS or NROWS in the header\n", s > "/dev/stderr"; exit 1 }
    col = 0; selfc = -1; selfr = -1
    next
  }
  stem != "" && /^[ \t]*\/\*/ { next }
  stem != "" && /^\};/ { if (selfc >= 0) print stem, selfc, selfr, width, nrows; stem = ""; next }
  stem != "" {
    n = split($0, t, ",")
    for (j = 1; j <= n; j++) {
      v = t[j]; gsub(/[ \t]/, "", v)
      if (v == "") next
      if (selfc < 0 && v == ("JPL_EDGE_TO_" up "_POOL")) { selfc = col % width; selfr = int(col / width) }
      col = col + 1
    }
  }' "$BUILD/sh_run_jpl.h" "$BUILD/sh_run_jpl_pools.c" > "$BUILD/self_edge.txt"; then
  red "FAIL: an edge table's width is not published as NPOS/NROWS, so the sweep cannot be derived"
  exit 1
fi
SELF_N="$(wc -l < "$BUILD/self_edge.txt" | tr -d ' ')"
if [[ "$SELF_N" -lt 1 ]]; then
  red "FAIL: no pool's edge table names its own pool — a chain sweep would have no self edge to follow"
  exit 1
fi
# The tagged pools are the ones whose scan reads a row out of the cell: the bad-tag arm is
# measured once per such pool, and their number is a SUMMARY key, so the probe's size and
# the emitter's own count of tag guards have to agree.
: > "$BUILD/tagged_pools.txt"
while read -r stem handle; do
  U="$(printf '%s' "$stem" | tr '[:lower:]' '[:upper:]')"
  nr="$(awk -v m="JPL_${U}_NROWS" '$1 == "#define" && $2 == m { print $3 + 0 }' "$BUILD/sh_run_jpl.h")"
  np="$(awk -v m="JPL_${U}_NPOS" '$1 == "#define" && $2 == m { print $3 + 0 }' "$BUILD/sh_run_jpl.h")"
  if [[ -z "$nr" || -z "$np" ]]; then
    red "FAIL: the header publishes no NROWS/NPOS for $stem, so the tag guard cannot be derived"
    exit 1
  fi
  if (( nr > 1 )); then printf '%s %s %s\n' "$stem" "$nr" "$np" >> "$BUILD/tagged_pools.txt"; fi
done < "$BUILD/pool_stems.txt"
TAG_N="$(wc -l < "$BUILD/tagged_pools.txt" | tr -d ' ')"
if [[ "$TAG_N" != "${K_tag_guards_emitted:-}" ]]; then
  red "FAIL: the header publishes NROWS > 1 for $TAG_N pools but the report counts ${K_tag_guards_emitted:-nothing} tag guards"
  exit 1
fi
{
  cat <<'EVAC_HEAD'
/* GENERATED by verify/c/jpl_emit.sh (check 9) from the emitted edge tables.  It builds a
   two-cell chain and one shared tail in the interval a boundary reads FROM, crosses the
   boundary in §6.7 paragraph 5bis's order — swap, rewind, queue, evacuate the roots,
   drain — and crosses it BACK, which is the round that makes evac's fourth arm carry its
   weight.  No capacity, index or word number is written below: every one is that pool's
   own JPL_* macro, or a value awk read out of its table.  Gate scaffolding, not emitted
   code: it prints. */
#include "sh_run_jpl.h"
#include <stdio.h>

static unsigned long failures;

static void bad(const char *pool, const char *what) {
  printf("  FAIL: %s: %s\n", pool, what);
  failures = failures + 1u;
}

EVAC_HEAD
while read -r stem iw row np nr; do
  U="$(printf '%s' "$stem" | tr '[:lower:]' '[:upper:]')"
  cat <<EVAC_ONE
/* ${stem}: its own edge table puts a ${stem} edge at word ${iw} of row ${row} (of ${nr}
   rows, ${np} words per cell), so the chain sets exactly that word and the drain must find
   exactly that class.  For an untagged cell the row is 0 and word 0 is JPL_NIL either way;
   for a tagged one the row IS the tag, which is what makes this sweep a measurement of
   scan_one's row arithmetic and not only of evac's. */
static void chain_${stem}(void) {
  const char *p = "${stem}";
  const jpl_ref iw = ${iw}u;
  const jpl_ref rw = ${row}u;
  const jpl_ref np = ${np}u;
  jpl_ref a, b, c;     /* three cells built by hand in the interval the boundary reads from */
  jpl_ref ta, tb, tc;  /* their copies: the to interval of the first boundary */
  jpl_ref f, u2, vv;   /* the second boundary's root, the copy of ta, the copy of tb */
  jpl_ref x, i, r;
  jpl_ref copied, fwd, bref, taken, frontier;

  if (jpl_pools_space != 0u) { bad(p, "entered with the single interval indicator flipped"); }

  /* ── build a -> b and c -> b: the shared tail is what a forwarding pointer is FOR ── */
  a = jpl_${stem}_alloc();
  b = jpl_${stem}_alloc();
  c = jpl_${stem}_alloc();
  if (a != (JPL_${U}_LO_BASE + 1u)) { bad(p, "the first hand-built cell is not the low interval's own first index"); }
  if (b != (JPL_${U}_LO_BASE + 2u)) { bad(p, "the second hand-built cell is not the low interval's second index"); }
  if (c != (JPL_${U}_LO_BASE + 3u)) { bad(p, "the third hand-built cell is not the low interval's third index"); }
  if (jpl_${stem}_origin[a] != JPL_NIL) { bad(p, "a cell nothing has copied has a non-nil origin"); }
  for (i = 0u; i < np; i = i + 1u) {
    jpl_${stem}_word_put(a, i, JPL_NIL);
    jpl_${stem}_word_put(b, i, JPL_NIL);
    jpl_${stem}_word_put(c, i, JPL_NIL);
  }
  /* the edge this table names, and NOTHING else: every other word is JPL_NIL, so evac of
     it is inert and the whole sweep stays inside one pool — cross-pool chains are 2e. */
  jpl_${stem}_word_put(a, 0u, rw);
  jpl_${stem}_word_put(b, 0u, rw);
  jpl_${stem}_word_put(c, 0u, rw);
  jpl_${stem}_word_put(a, iw, b);
  jpl_${stem}_word_put(c, iw, b);
  if (jpl_${stem}_word_at(a, iw) != b) { bad(p, "word_put and word_at do not agree on the same word"); }

  /* ── boundary 1 ── */
  copied = jpl_${stem}_copied;
  fwd = jpl_${stem}_forwarded;
  bref = jpl_${stem}_badref;
  taken = jpl_${stem}_taken;
  r = jpl_pools_swap();
  if (r != 1u || jpl_pools_space != 1u) { bad(p, "the first swap did not make the high interval current"); }
  r = jpl_${stem}_reset();
  if (r != 0u) { bad(p, "reset of a to interval nothing had queued returned a cell count"); }
  if (jpl_${stem}_next != (JPL_${U}_HI_BASE + 1u)) { bad(p, "reset rewound somewhere other than the CURRENT interval's base"); }
  jpl_${stem}_queue_start();
  if (jpl_${stem}_scan != (JPL_${U}_CUR_BASE + 1u)) { bad(p, "queue_start did not put the scan on the current interval's own reserved successor"); }

  ta = jpl_${stem}_evac(a);
  /* what the COPY alone owes, before the scan touches anything */
  if (ta != (JPL_${U}_HI_BASE + 1u)) { bad(p, "the first copy did not land at the to interval's first index"); }
  if (jpl_${stem}_is_live(ta) != JPL_TRUE) { bad(p, "the copy in the current interval reported dead"); }
  if (jpl_${stem}_is_live(a) != JPL_FALSE) { bad(p, "the source in the abandoned interval reported live"); }
  if (jpl_${stem}_origin[ta] != a) { bad(p, "the copy does not name the handle it was copied from"); }
  if (jpl_${stem}_origin[a] != ta) { bad(p, "the source does not forward to its copy"); }
  if (jpl_${stem}_copied != copied + 1u) { bad(p, "the first evacuate did not copy exactly one cell"); }
  if (jpl_${stem}_forwarded != fwd) { bad(p, "a cell never evacuated before was answered by a forwarding pointer"); }
  if (jpl_${stem}_taken != taken + 1u) { bad(p, "the copy took an allocation the allocator did not count"); }
  for (i = 0u; i < np; i = i + 1u) {
    if (jpl_${stem}_word_at(ta, i) != jpl_${stem}_word_at(a, i)) { bad(p, "one structure assignment did not move the whole cell"); }
  }
  if (jpl_${stem}_word_at(ta, iw) != b) { bad(p, "the copy's self edge is not the source's yet, i.e. the copy is not a copy"); }
  if (jpl_${stem}_is_live(jpl_${stem}_word_at(ta, iw)) != JPL_FALSE) { bad(p, "the unscanned copy's edge already named a live cell — the drain would have nothing to fix"); }
  tc = jpl_${stem}_evac(c);
  if (tc != (JPL_${U}_HI_BASE + 2u)) { bad(p, "the second root's copy did not extend the queue"); }
  if (jpl_${stem}_copied != copied + 2u) { bad(p, "the second root was not copied"); }

  jpl_${stem}_drain();
  /* what the SCAN owes: the edge rewritten, the tail copied ONCE, the second parent
     forwarded to it — and every step of that route went through jpl_pools_evac_by_class,
     because scan_one knows only the class its table holds. */
  if (jpl_${stem}_copied != copied + 3u) { bad(p, "a three-cell chain copied a number of cells other than three"); }
  if (jpl_${stem}_forwarded != fwd + 1u) { bad(p, "the shared tail was copied twice, or reached without the origin table"); }
  if (jpl_${stem}_badref != bref) { bad(p, "a well-formed chain took a bad reference"); }
  if (jpl_${stem}_taken != taken + 3u) { bad(p, "three copies took a number of allocations other than three"); }
  tb = jpl_${stem}_origin[b];
  if (tb != (JPL_${U}_HI_BASE + 3u)) { bad(p, "the shared tail's copy is not the third cell of the to interval"); }
  if (jpl_${stem}_origin[tb] != b) { bad(p, "the tail's copy does not name its source"); }
  if (jpl_${stem}_word_at(ta, iw) != tb) { bad(p, "the first parent's edge still names the abandoned interval after the drain"); }
  if (jpl_${stem}_word_at(tc, iw) != tb) { bad(p, "the second parent kept its own duplicate of the shared tail"); }
  if (jpl_${stem}_is_live(tb) != JPL_TRUE) { bad(p, "the fixed-up edge names a dead cell"); }
  if (jpl_${stem}_scan != jpl_${stem}_next) { bad(p, "the drain stopped before the frontier"); }
  if (jpl_${stem}_next != (JPL_${U}_HI_BASE + 4u)) { bad(p, "the drain reached a frontier other than the three cells it queued"); }
  if (jpl_${stem}_peak != 3u) { bad(p, "peak is not the to interval's own three cells"); }
  if (jpl_${stem}_is_live(a) != JPL_FALSE) { bad(p, "a source handle survived the boundary"); }

  /* ── boundary 2, the round the fourth arm exists for ──
     Last round's forwarding pointers are STILL in the table, and the rewound interval
     hands the same indices out again for different cells.  A three-arm "already copied?"
     test would read origin[ta] = a and forward the new parent to a cell this round has
     already re-allocated for something else; only the mutual arm, plus alloc's clear,
     makes "below the frontier" mean "written THIS round". */
  r = jpl_pools_swap();
  if (r != 0u || jpl_pools_space != 0u) { bad(p, "the second swap did not complete the cycle"); }
  /* One frontier for two intervals means this rewind reports 0: the pool's 'next' still
     names the interval the FIRST round collected into, so the guard rightly refuses to
     subtract.
     The cells a, b, c are freed anyway — the rewind below is what the second round
     allocates into — but "cells returned" is only a count when reset does not cross a
     boundary, which is check 5's sweep, not this one. */
  r = jpl_${stem}_reset();
  if (r != 0u) { bad(p, "the rewind after a swap reported cells freed from a frontier in the OTHER interval"); }
  if (jpl_${stem}_next != (JPL_${U}_LO_BASE + 1u)) { bad(p, "the rewind did not free the low interval for the second round"); }
  if (jpl_${stem}_origin[a] != ta) { bad(p, "the first round left no stale back-pointer, so this round cannot measure the rejection of one"); }
  jpl_${stem}_queue_start();
  f = jpl_${stem}_alloc();
  if (f != a) { bad(p, "the rewound interval did not reuse its own first index"); }
  if (jpl_${stem}_origin[f] != JPL_NIL) { bad(p, "alloc handed out a cell whose origin still names LAST round's copy — nothing below the frontier means this round any more"); }
  for (i = 0u; i < np; i = i + 1u) { jpl_${stem}_word_put(f, i, JPL_NIL); }
  u2 = jpl_${stem}_evac(ta);
  if (u2 == f) { bad(p, "evac forwarded a stale origin into the cell this round built by hand"); }
  if (u2 != (JPL_${U}_LO_BASE + 2u)) { bad(p, "the second boundary did not copy to the current interval's own next index"); }
  if (jpl_${stem}_copied != copied + 4u) { bad(p, "the second boundary's root copy is not the fourth cell copied"); }
  if (jpl_${stem}_forwarded != fwd + 1u) { bad(p, "the second boundary forwarded on a stale origin instead of copying"); }
  if (jpl_${stem}_origin[u2] != ta) { bad(p, "the second boundary's copy does not name its source"); }
  if (jpl_${stem}_origin[ta] != u2) { bad(p, "the second boundary left ta forwarding to last round's copy"); }
  if (jpl_${stem}_word_at(u2, iw) != tb) { bad(p, "the second boundary copied the pre-scan cell rather than the scanned one"); }
  if (jpl_${stem}_is_live(tb) != JPL_FALSE) { bad(p, "the edge the second boundary inherited already names a live cell"); }
  jpl_${stem}_drain();
  vv = jpl_${stem}_origin[tb];
  if (vv != (JPL_${U}_LO_BASE + 3u)) { bad(p, "the tail's second copy is not at the frontier the drain stopped on"); }
  if (jpl_${stem}_word_at(u2, iw) != vv) { bad(p, "the second drain did not rewrite the copied edge"); }
  if (jpl_${stem}_origin[vv] != tb) { bad(p, "the second round's tail copy does not name the interval it came from"); }
  if (jpl_${stem}_is_live(vv) != JPL_TRUE) { bad(p, "the second round's fix-up points at a dead cell"); }
  if (jpl_${stem}_scan != jpl_${stem}_next) { bad(p, "the second drain stopped before the frontier"); }
  if (jpl_${stem}_next != (JPL_${U}_LO_BASE + 4u)) { bad(p, "the second round's frontier is not four indices deep in the low interval"); }
  if (jpl_${stem}_copied != copied + 5u) { bad(p, "two boundaries served a different total of copies than five"); }
  if (jpl_${stem}_forwarded != fwd + 1u) { bad(p, "the second round forwarded where a stale origin only LOOKS valid"); }
  if (jpl_${stem}_taken != taken + 6u) { bad(p, "since the first boundary began, six allocations were not the five copies plus the reused root f"); }

  /* ── what evacuate REFUSES: the domain test, and the empty list ── */
  copied = jpl_${stem}_copied;
  fwd = jpl_${stem}_forwarded;
  bref = jpl_${stem}_badref;
  taken = jpl_${stem}_taken;
  frontier = jpl_${stem}_next;
  x = jpl_${stem}_evac(f);   /* a handle of the CURRENT interval: there is no copy to make of a live cell */
  if (x != JPL_NIL) { bad(p, "evacuating a handle of the current interval returned a cell"); }
  if (jpl_${stem}_badref != bref + 1u) { bad(p, "a current-interval evacuate was not counted as a bad reference"); }
  x = jpl_${stem}_evac(JPL_${U}_OTHER_BASE);   /* the abandoned interval's reserved index */
  if (x != JPL_NIL) { bad(p, "the reserved index of the interval being read from was copied"); }
  if (jpl_${stem}_badref != bref + 2u) { bad(p, "the reserved base was not counted as a bad reference"); }
  x = jpl_${stem}_evac(JPL_POOL_${U});   /* one past the whole array: refused BEFORE origin is read */
  if (x != JPL_NIL) { bad(p, "an index past the array returned a cell"); }
  if (jpl_${stem}_badref != bref + 3u) { bad(p, "an out-of-array index was not counted as a bad reference"); }
  if (jpl_${stem}_next != frontier) { bad(p, "a refused evacuate moved the frontier, i.e. it wrote outside the domain test"); }
  x = jpl_${stem}_evac(JPL_NIL);   /* the empty list is not a cell: nothing moves at all */
  if (x != JPL_NIL) { bad(p, "evac(JPL_NIL) returned a cell"); }
  if (jpl_${stem}_badref != bref + 3u) { bad(p, "evac(JPL_NIL) was counted as a bad reference"); }
  if (jpl_${stem}_copied != copied || jpl_${stem}_forwarded != fwd) { bad(p, "evac(JPL_NIL) copied or forwarded"); }
  if (jpl_${stem}_taken != taken) { bad(p, "a refused evacuate, or the empty list, allocated a cell"); }
  if (jpl_pools_unclassified != 0u) { bad(p, "the dispatch fell through an arm while this pool's chain was being collected"); }

  /* leave the pool as the next sweep found it: both intervals rewound, indicator at 0 */
  (void) jpl_${stem}_reset();
  (void) jpl_pools_swap();
  (void) jpl_${stem}_reset();
  (void) jpl_pools_swap();
  (void) jpl_${stem}_reset();
  if (jpl_pools_space != 0u) { bad(p, "the chain left the single indicator flipped"); }
  if (jpl_${stem}_next != (JPL_${U}_LO_BASE + 1u)) { bad(p, "the chain left an interval unrewound"); }
  printf("    chain %-32s copies %2lu  forwarded %2lu  badref %2lu  taken %2lu  peak %2lu  edge word %2lu of row %2lu\\n",
         p, (unsigned long) jpl_${stem}_copied, (unsigned long) jpl_${stem}_forwarded,
         (unsigned long) jpl_${stem}_badref, (unsigned long) jpl_${stem}_taken,
         (unsigned long) jpl_${stem}_peak, (unsigned long) iw, (unsigned long) rw);
}

EVAC_ONE
done < "$BUILD/self_edge.txt"
while read -r stem nr np; do
  U="$(printf '%s' "$stem" | tr '[:lower:]' '[:upper:]')"
  cat <<EVAC_TAG
/* ${stem}: a NODE cell — the header's own JPL_${U}_NROWS says ${nr} rows, ${np} words each —
   so scan_one reads the row FROM the cell and a tag with no row has no classes to trust.
   The bad tag below is NROWS+5, and the claim measured is that the scan stops without
   rewriting a word and without evacuating a slot it was not allowed to read. */
static void tagtest_${stem}(void) {
  const char *p = "${stem} tag";
  const jpl_ref np = ${np}u;
  const jpl_ref garbage = JPL_${U}_NROWS + 5u;
  jpl_ref g, t, i, copied, badtag;

  if (jpl_pools_space != 0u) { bad(p, "entered with the single interval indicator flipped"); }
  g = jpl_${stem}_alloc();
  if (g != (JPL_${U}_LO_BASE + 1u)) { bad(p, "the tagged cell is not the low interval's own first index"); }
  for (i = 0u; i < np; i = i + 1u) { jpl_${stem}_word_put(g, i, JPL_NIL); }
  jpl_${stem}_word_put(g, 0u, garbage);
  /* every other word is set to an index of the interval about to be abandoned, so a scan
     that WALKED the slots would have to rewrite them — and the copy below would differ
     from the source.  Zeros everywhere would make this a tautology. */
  for (i = 1u; i < np; i = i + 1u) { jpl_${stem}_word_put(g, i, g + i); }
  if (jpl_${stem}_word_at(g, 0u) != garbage) { bad(p, "the tag word does not read back what it was given"); }

  copied = jpl_${stem}_copied;
  badtag = jpl_${stem}_badtag;
  (void) jpl_pools_swap();
  if (jpl_${stem}_reset() != 0u) { bad(p, "the to interval was not empty when the queue started"); }
  jpl_${stem}_queue_start();
  t = jpl_${stem}_evac(g);
  if (t != (JPL_${U}_HI_BASE + 1u)) { bad(p, "the tagged cell's copy did not land at the to interval's first index"); }
  if (jpl_${stem}_copied != copied + 1u) { bad(p, "the tagged cell's copy is not the cell copied"); }
  if (jpl_${stem}_badtag != badtag) { bad(p, "a badtag counted before the scan ever ran"); }
  jpl_${stem}_drain();
  if (jpl_${stem}_badtag != badtag + 1u) { bad(p, "a tag with no row did not reach the guard that counts it"); }
  if (jpl_${stem}_scan != jpl_${stem}_next) { bad(p, "the drain stopped on an unreadable tag instead of charging it one cell"); }
  if (jpl_${stem}_next != (JPL_${U}_HI_BASE + 2u)) { bad(p, "a bad tag made the drain evacuate cells it was never allowed to read"); }
  if (jpl_${stem}_copied != copied + 1u) { bad(p, "the scan walked a garbage row and evacuated a cell through it"); }
  /* NO word rewritten: the copy is still, word for word, the cell that was handed to it —
     including the bad tag itself, which the scan does not silently repair. */
  for (i = 0u; i < np; i = i + 1u) {
    if (jpl_${stem}_word_at(t, i) != jpl_${stem}_word_at(g, i)) { bad(p, "the scan rewrote a word of a cell whose row it could not read"); }
  }
  if (jpl_${stem}_word_at(t, 0u) != garbage) { bad(p, "the copy lost the bad tag instead of preserving it"); }
  for (i = 1u; i < np; i = i + 1u) {
    if (jpl_${stem}_is_live(jpl_${stem}_word_at(t, i)) != JPL_FALSE) { bad(p, "a word the scan refused to read reports a live edge"); }
  }
  (void) jpl_${stem}_reset();
  (void) jpl_pools_swap();
  (void) jpl_${stem}_reset();
  if (jpl_pools_space != 0u) { bad(p, "the tag test left the single indicator flipped"); }
  if (jpl_${stem}_next != (JPL_${U}_LO_BASE + 1u)) { bad(p, "the tag test left an interval unrewound"); }
  printf("    tag %-32s badtag %2lu  rows %2lu  words left alone %2lu\\n", p,
         (unsigned long) (jpl_${stem}_badtag - badtag), (unsigned long) JPL_${U}_NROWS,
         (unsigned long) np);
}

EVAC_TAG
done < "$BUILD/tagged_pools.txt"
  awk '{ print "  chain_" $1 "();" }' "$BUILD/self_edge.txt" > "$BUILD/chain_calls.inc"
  awk '{ print "  tagtest_" $1 "();" }' "$BUILD/tagged_pools.txt" > "$BUILD/tag_calls.inc"
  cat <<'EVAC_TAIL'
int main(void) {
EVAC_TAIL
  cat "$BUILD/chain_calls.inc"
  cat "$BUILD/tag_calls.inc"
  cat <<'EVAC_TAIL'
  if (jpl_pools_space != 0u) {
    bad("(every pool)", "a sweep ended on the second interval: the indicator is ONE global, so a pool that left it flipped is a finding about the runtime, not about that pool");
  }
  if (jpl_pools_unclassified != 0u) {
    bad("(every pool)", "jpl_pools_evac_by_class fell through its arms — an edge class the tables name has no evacuate branch, and a word was collected by leaving it pointing at the abandoned interval");
  }
  printf("  EVAC PROBE: %lu assertion failures; unclassified = %lu\n",
         failures, (unsigned long) jpl_pools_unclassified);
  return (failures == 0u) ? 0 : 1;
}
EVAC_TAIL
} > "$BUILD/probe_evac.c"
EVAC_CHAINS="$(grep -c '^static void chain_' "$BUILD/probe_evac.c")"
EVAC_TAGTESTS="$(grep -c '^static void tagtest_' "$BUILD/probe_evac.c")"
if [[ "$EVAC_CHAINS" != "$SELF_N" || "$EVAC_TAGTESTS" != "$TAG_N" ]]; then
  red "FAIL: the probe generated $EVAC_CHAINS chain sweeps for $SELF_N self-edge pools and $EVAC_TAGTESTS tag tests for $TAG_N tagged pools"
  exit 1
fi
# shellcheck disable=SC2086
if ! "$CC" ${CFLAGS%-fsyntax-only} -I"$BUILD" "$BUILD/probe_evac.c" \
       "$BUILD/sh_run_jpl_pools.o" -o "$BUILD/probe_evac" \
       2> "$BUILD/evac_cc.log"; then
  red "FAIL: the evacuation probe did not build — the runtime's own declarations are unusable"
  sed 's/^/    /' "$BUILD/evac_cc.log"
  exit 1
fi
printf '    %-32s %s\n' "pool" "what one chain of that cell, driven across TWO boundaries, must show"
if ! "$BUILD/probe_evac" > "$BUILD/probe_evac_out.txt" 2>&1; then
  sed 's/^/    /' "$BUILD/probe_evac_out.txt"
  red "FAIL: the emitted evacuation broke §6.7 paragraph 5bis across a boundary (see above)"
  exit 1
fi
sed 's/^/    /' "$BUILD/probe_evac_out.txt"
EVAC_RUN="$(grep -c '^    chain [a-z]' "$BUILD/probe_evac_out.txt")"
TAG_RUN="$(grep -c '^    tag [a-z]' "$BUILD/probe_evac_out.txt")"
if [[ "$EVAC_RUN" != "$SELF_N" || "$TAG_RUN" != "$TAG_N" ]]; then
  red "FAIL: the probe ran $EVAC_RUN chain sweeps of $SELF_N self-edge pools and $TAG_RUN tag tests of $TAG_N tagged pools"
  exit 1
fi
green "PASS: $EVAC_RUN self-edge chains collected across two boundaries — the copy is whole, the shared tail forwarded once, the second round refused the stale origin and copied, $((3 * EVAC_RUN)) bad references refused without moving a frontier, and $TAG_RUN garbage tags stopped the scan without rewriting a word"

# The deferred re-pin: only now, with every check above green, does the emission this run
# produced become the vendored evidence — check 9 drives exactly these files.
if [[ $REGEN_PIN -eq 1 ]]; then
  cp "$BUILD/sh_run_jpl.h" "$HDR"
  cp "$BUILD/sh_run_jpl_pools.c" "$POOLS"
  cp "$BUILD/layout.txt" "$EVID"
  green "PASS: regenerated ${HDR#"$REPO"/}, ${POOLS#"$REPO"/} and ${EVID#"$REPO"/} — every check above, the evacuation drive included, ran on the emission just copied"
  exit 0
fi
bold "==> what this layer still cannot do"
# Read straight off the report, so the limitation is the tool's own statement and
# not a claim written into a shell script.
awk '/^==== WHAT THIS LAYER COULD NOT SIZE/{f=1;next} /^==== /{f=0} f' \
  "$BUILD/layout.txt" | sed 's/^/    /'
printf '    %s report lines are marked PENDING\n' \
  "$(grep -c PENDING "$BUILD/layout.txt")"
exit 0
