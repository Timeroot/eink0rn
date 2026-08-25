#!/usr/bin/env bash
# Run eink0rn over a corpus laid out as <root>/good/**.ndjson and <root>/bad/**.ndjson.
#
#   tools/run-tests.sh [root] [-v] [-t seconds] [filter]
#
# Exit status is 0 only when every file gets the verdict its directory demands.
set -uo pipefail

ROOT=${1:-refs/tests}
shift || true

VERBOSE=0
TIMEOUT=60
FILTER=""
while [ $# -gt 0 ]; do
  case "$1" in
    -v) VERBOSE=1 ;;
    -t) TIMEOUT=$2; shift ;;
    *)  FILTER=$1 ;;
  esac
  shift
done

[ -f "$HOME/.ghcup/env" ] && . "$HOME/.ghcup/env"
BIN=$(cabal list-bin eink0rn 2>/dev/null) || { echo "build first: cabal build"; exit 2; }

pass=0; fail=0
declare -a failures=()

check() {  # $1 = file, $2 = expected verdict
  local f=$1 want=$2 got err rc
  err=$(mktemp)
  got=$(timeout "$TIMEOUT" "$BIN" "$f" 2>"$err"); rc=$?
  if [ $rc -eq 124 ]; then got="TIMEOUT"; fi
  if [ "$got" = "$want" ]; then
    pass=$((pass+1))
    if [ $VERBOSE -eq 1 ]; then printf '  ok   %-60s %s\n' "${f#"$ROOT"/}" "$got"; fi
    # A rejection is only interesting if it is for the right reason; print it.
    if [ $VERBOSE -eq 1 ] && [ "$want" = REJECT ]; then
      sed 's/^/         /' "$err" | head -3
    fi
  else
    fail=$((fail+1))
    failures+=("${f#"$ROOT"/}")
    printf '  FAIL %-60s want %s got %s\n' "${f#"$ROOT"/}" "$want" "$got"
    if [ $VERBOSE -eq 1 ]; then sed 's/^/         /' "$err" | head -8; fi
  fi
  rm -f "$err"
}

for want in ACCEPT REJECT; do
  case $want in ACCEPT) dir=good ;; REJECT) dir=bad ;; esac
  [ -d "$ROOT/$dir" ] || continue
  echo "== $ROOT/$dir (expect $want)"
  while IFS= read -r f; do
    [ -n "$FILTER" ] && [[ "$f" != *"$FILTER"* ]] && continue
    check "$f" "$want"
  done < <(find "$ROOT/$dir" -name '*.ndjson' | sort)
done

echo
echo "passed $pass, failed $fail"
if [ ${#failures[@]} -gt 0 ]; then
  printf '%s\n' "${failures[@]}" | sed 's/^/  /'
fi
[ "$fail" -eq 0 ]
