# Canonical POSIX: && and || short-circuit truth table.
true && echo TT
false && echo FT
true || echo TO
false || echo FO
true && false && echo chain_no
false || true || echo chain_no2
true && echo yes1 && echo yes2
false || echo no1 || echo no2
