#!/bin/bash
# Build the native tools (tools/, one lean_exe per scripts/*.lean tool) with the library's toolchain, in a
# memory-capped scope. Rerun after editing any scripts/*.lean tool. Native exes need ~0.2 GB per process where
# `lean --run` needs ~1.9 GB when the library imports Mathlib (core oleans are read twice).
set -e
D=$(cd "$(dirname "$0")/.." && pwd)
cp "$(source "$D/hc.env"; echo "$HC_LIBDIR")/lean-toolchain" "$D/tools/lean-toolchain"
cd "$D/tools"
LEAN_NUM_THREADS=2 systemd-run --user --scope --quiet -p MemoryMax=${MEM:-3G} -p MemorySwapMax=0 lake build
