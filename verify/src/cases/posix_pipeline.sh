# Canonical POSIX: multi-stage pipelines over fixed input.
printf "red\ngreen\nblue\n" | grep "ee"
printf "1\n2\n3\n4\n" | grep -v 2 | grep 3
printf "x\ny\nz\n" | grep q || echo "no-match"
