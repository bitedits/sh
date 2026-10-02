# Canonical POSIX: string tests via [ ] / test, fed into if/elif/else.
a=hello
b=hello
if [ "$a" = "$b" ]; then echo eq; fi
if [ "$a" != "world" ]; then echo ne; fi
if test -z "$empty"; then echo unset_is_empty; fi
if test -n "$a"; then echo nonempty; fi
if [ "$a" ]; then echo nonzero_string_true; fi
if [ "" ]; then echo empty_string; else echo empty_false; fi
