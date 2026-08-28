#!/usr/bin/env bash
# Build eink0rn for the Lean Kernel Arena.  Run from the repository root; the
# binary lands in arena/eink0rn, which is what tools/arena-checker.yaml runs.
#
# The arena builds each checker on a stock Ubuntu image inside its own nix
# shell, and neither is promised to carry a Haskell toolchain.  So this tries
# every GHC it can find, in the order most likely to already be installed, and
# installs one itself if none of them can build the checker.  There is nothing
# to resolve and no package index to fetch: the checker depends on the GHC boot
# libraries and nothing else, so the build is one `ghc --make`.
set -euo pipefail

out=arena
mkdir -p "$out/obj"

# Kept the same as the ghc-options in eink0rn.cabal, so that the binary the
# arena runs is the binary the tests were run against.  -A1g is the default
# nursery for a one-core run and is overridden on the command line for the
# arena, which has eight of them and sixteen gigabytes to fit them in.
build_with() {
  echo "== building with $1 ($("$1" --numeric-version))"
  "$1" -O2 -threaded -rtsopts "-with-rtsopts=-K512m -A1g -Mgrace=256m" \
       -j"$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)" \
       -isrc -iapp -outputdir "$out/obj" -o "$out/eink0rn" app/Main.hs
}

# 9.2 is where base 4.16 starts, which is what the cabal file asks for.  A
# newer compiler than the 9.6 this was developed against is worth trying rather
# than ruling out -- if it cannot build it, the next candidate gets a go.
usable() {
  local v
  v=$("$1" --numeric-version 2>/dev/null) || return 1
  [ "$(printf '%s\n9.2\n' "$v" | sort -V | head -1)" = 9.2 ]
}

candidates=(
  "${GHC:-}"                       # an explicit choice wins
  ghc                              # whatever is on PATH
  "$PWD/.ghcup/bin/ghc"            # installed by an earlier run of this script
  "$HOME/.ghcup/bin/ghc"
  /usr/local/.ghcup/bin/ghc        # where the GitHub runner images put it
  /opt/ghc/bin/ghc
)

for c in "${candidates[@]}"; do
  [ -n "$c" ] || continue
  ghc=$(command -v "$c" 2>/dev/null) || continue
  usable "$ghc" || { echo "== skipping $ghc: too old"; continue; }
  if build_with "$ghc"; then
    "./$out/eink0rn" --help >/dev/null
    echo "== built $out/eink0rn with $ghc"
    exit 0
  fi
  echo "== $ghc could not build it; trying the next compiler"
done

# Nothing on the machine worked.  Install the compiler this was developed
# against, under the checker's own directory rather than in $HOME, and use
# that.  BOOTSTRAP_HASKELL_MINIMAL installs ghcup alone: cabal is not wanted.
echo "== no usable GHC found; installing 9.6.6 with ghcup"
export GHCUP_INSTALL_BASE_PREFIX="$PWD"
export BOOTSTRAP_HASKELL_NONINTERACTIVE=1
export BOOTSTRAP_HASKELL_MINIMAL=1
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
"$PWD/.ghcup/bin/ghcup" install ghc 9.6.6
build_with "$PWD/.ghcup/bin/ghc-9.6.6"
echo "== built $out/eink0rn with ghcup's 9.6.6"
"./$out/eink0rn" --help >/dev/null
