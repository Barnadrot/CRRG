#!/usr/bin/env bash
# Build the classical slice. Needs lean/lake v4.30.0 and network access for the Mathlib cache.
# Mathlib is pinned to c5ea00351c (lakefile.lean). crrg-core is built by path.
set -eu
cd "$(dirname "$0")"
export ELAN_TOOLCHAIN="$(cat lean-toolchain)"   # pin the toolchain for every lean/lake call
{
  echo "# crrg-classical build log"
  echo "# lean: $(lean --version)"
  lake exe cache get > /dev/null 2>&1 || echo "(cache get failed; building Mathlib from source)"
  echo "## lake build"
  lake build 2>&1 | grep -v '^trace\|^✔' | tail -3; echo "exit: ${PIPESTATUS[0]}"
  echo "## axioms (lake env lean CRRGClassical/Axioms.lean)"
  lake env lean CRRGClassical/Axioms.lean 2>&1
} > BUILD.log 2>&1
cat BUILD.log
