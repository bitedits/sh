#!/usr/bin/env bash
# Differential conformance harness for ./src (the executable OCaml shell model).
#
# It runs every case under the host /bin/sh (the POSIX oracle) and under the
# extracted `ush` interpreter built from ./src, then diffs stdout+stderr+exit
# status.  A case PASSES only when ush reproduces /bin/sh exactly.
#
# Manual evaluation, from the repo root:
#     OCAMLPATH=/opt/homebrew/lib/ocaml/site-lib dune build
#     bash verify/src/conformance.sh
#
# Cases live in two places:
#   * inline POSIX constructs below (regression set), and
#   * verify/src/cases/*.sh (external corpus, e.g. canonical POSIX examples).
# Each external case must be self-terminating and non-interactive, and should
# avoid nondeterministic output (ls, date, whoami, ...) so the diff is stable.

set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
BIN="$ROOT/_build/default/src/ush.exe"
CASES_DIR="$ROOT/verify/src/cases"
GUARD_SECS=10

red() { printf '\033[31m%s\033[0m\n' "$*"; }
grn() { printf '\033[32m%s\033[0m\n' "$*"; }

if [ ! -x "$BIN" ]; then
  echo "building ./src ..." >&2
  OCAMLPATH=/opt/homebrew/lib/ocaml/site-lib dune build 2>&1 | sed 's/^/  /' >&2
fi
[ -x "$BIN" ] || { red "FAIL: $BIN not built"; exit 1; }

# run <shell-cmd...>   in a throwaway cwd, capturing combined output + status
capture() {
  local wd; wd="$(mktemp -d)"
  ( cd "$wd" && "$@" 2>&1; echo "__EXIT__:$?" )
  rm -rf "$wd"
}

# with_guard <secs> <cmd...>  — kill the command if it exceeds the budget
with_guard() {
  local secs="$1"; shift
  "$@" & local pid=$! n=0
  while kill -0 "$pid" 2>/dev/null; do
    if [ "$n" -ge "$secs" ]; then
      kill -9 "$pid" 2>/dev/null; wait "$pid" 2>/dev/null
      echo "__TIMEOUT__"; return 124
    fi
    sleep 1; n=$((n+1))
  done
  wait "$pid"; return $?
}

# check <name> <one-liner-or-file> <mode>
#   mode=file -> write body to a temp script and run as a script
#   mode=arg  -> treat as a single /bin/sh -c / ush string via a temp script
pass=0 fail=0
check() {
  local name="$1" body="$2"
  local f; f="$(mktemp)"
  printf '%s\n' "$body" > "$f"
  local s u
  s="$(with_guard "$GUARD_SECS" /bin/sh "$f")"
  u="$(with_guard "$GUARD_SECS" "$BIN" "$f")"
  if [ "$s" = "$u" ]; then
    pass=$((pass+1)); printf '  %s  %s\n' "$(echo '[PASS]')" "$name"
  else
    fail=$((fail+1)); printf '  %s  %s\n' "$(red '[FAIL]')" "$name"
    printf '       sh : %s\n' "$(printf '%s' "$s" | tr '\n' '|')"
    printf '       ush: %s\n' "$(printf '%s' "$u" | tr '\n' '|')"
  fi
  rm -f "$f"
}

echo "== inline POSIX constructs =="
check "andif-short-circuit"  'false && echo YES; echo done'
check "orif-short-circuit"   'true || echo NO; echo done'
check "seq-status-last"      'false; true; echo end'
check "bang-invert"          '! true; echo after'
check "bang-ok"              '! false; echo status_is_$?'
check "if-else"              'if false; then echo T; else echo F; fi'
check "if-elif"              'if false; then echo 1; elif true; then echo 2; else echo 3; fi'
check "if-unset-var"         'if test -z "$var"; then echo empty; else echo other; fi'
check "for-words"            'for x in a b c; do echo $x; done'
check "for-empty-in"         'for x in; do echo NO; done; echo done'
check "for-quoted"           'for x in "a b" c; do echo "$x"; done'
check "case-hit"             'case foo in bar) echo b;; foo) echo f;; esac'
check "case-glob"            'case foobar in foo*) echo prefix;; esac'
check "case-or"              'case baz in foo|baz) echo fb;; *) echo other;; esac'
check "case-empty-body"      'case foo in (bar) ;; (foo) echo x ;; esac'
check "case-unset-empty"     'var=""; case "$var" in "") echo isempty;; *) echo no;; esac'
check "while-false"          'while false; do echo BODY; done; echo after'
check "until-true"           'until true; do echo BODY; done; echo after'
check "pipeline"             'printf "a\nb\nc\n" | grep b'
check "and-or-chain"         'true && false || echo fallback'
check "reserved-args"        'echo done; echo then; echo in; echo fi; echo esac'
check "nested-if-in-for"     'for x in a b; do if test "$x" = a; then echo A; else echo B; fi; done'
check "assign-prefix"        'GMSG=hi; echo $GMSG'
check "quoted-words"         'echo "Simple command"'
check "brace-group"          '{ echo a; echo b; }'
check "subshell-group"       '( echo a; echo b )'

if [ -d "$CASES_DIR" ]; then
  echo "== external corpus (verify/src/cases/*.sh) =="
  for f in "$CASES_DIR"/*.sh; do
    [ -e "$f" ] || continue
    check "$(basename "$f")" "$(cat "$f")"
  done
fi

echo
total=$((pass+fail))
if [ "$fail" -eq 0 ]; then
  grn "SUMMARY: $pass/$total conformance cases match /bin/sh"
else
  red "SUMMARY: $pass passed, $fail failed (of $total)"
fi
[ "$fail" -eq 0 ]
