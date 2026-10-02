# Canonical POSIX: case with glob patterns, char classes, alternation, default.
for v in apple banana cherry abc1; do
  case "$v" in
    apple) echo "exact:apple" ;;
    banana|cherry) echo "alt:$v" ;;
    a*b*) echo "glob:ab" ;;
    [abc]*) echo "class:first-abc" ;;
    *) echo "default:$v" ;;
  esac
done
