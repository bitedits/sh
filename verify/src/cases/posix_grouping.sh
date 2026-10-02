# Canonical POSIX: command grouping - brace group (current shell) vs subshell.
{ echo one; echo two; }
( echo three; echo four )
echo outer
{ echo inner_group; }
( echo inner_subshell )
