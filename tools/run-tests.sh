#!/usr/bin/env bash
# Run eink0rn over a corpus laid out as <root>/good/**.ndjson, <root>/bad/**.ndjson
# and <root>/either/**.ndjson -- the last for cases the arena itself scores
# `outcome: either`, where any verdict but a hang or a crash is correct.
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
# EINK0RN_BIN names a binary to test instead of the cabal build -- arena/eink0rn,
# say, which tools/arena-build.sh puts there.
BIN=${EINK0RN_BIN:-$(cabal list-bin eink0rn 2>/dev/null)} \
  || { echo "build first: cabal build"; exit 2; }

pass=0; fail=0
declare -a failures=()

check() {  # $1 = file, $2 = expected verdict
  local f=$1 want=$2 got err rc
  err=$(mktemp)
  got=$(timeout "$TIMEOUT" "$BIN" "$f" 2>"$err"); rc=$?
  if [ $rc -eq 124 ]; then got="TIMEOUT"; fi
  # An EITHER case wants a verdict, not a particular one: rc 0 or 1, never a
  # timeout (124) and never the checker declining to answer (2, 3).
  if [ "$got" = "$want" ] || { [ "$want" = EITHER ] && [ $rc -lt 2 ]; }; then
    pass=$((pass+1))
    # Which way an EITHER case fell is the whole of what it tells you, so say so
    # even without -v.
    if [ $VERBOSE -eq 1 ] || [ "$want" = EITHER ]; then
      printf '  ok   %-60s %s\n' "${f#"$ROOT"/}" "$got"
    fi
    # A rejection is only interesting if it is for the right reason; print it.
    if [ $VERBOSE -eq 1 ] && [ "$got" = REJECT ]; then
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

for want in ACCEPT REJECT EITHER; do
  case $want in ACCEPT) dir=good ;; REJECT) dir=bad ;; EITHER) dir=either ;; esac
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
