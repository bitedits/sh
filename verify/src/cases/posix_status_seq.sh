# Canonical POSIX: $? status threading across statements.
echo hi >/dev/null
echo "after_ok:$?"
false
echo "after_false:$?"
true
echo "after_true:$?"
nonexistent_command_zzz
echo "after_missing:$?"
