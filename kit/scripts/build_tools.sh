#!/bin/bash
# Build the native tools (tools/, one lean_exe per scripts/*.lean tool) with the library's toolchain, in a
# memory-capped scope. Rerun after editing any scripts/*.lean tool. Native exes need ~0.2 GB per process where
# `lean --run` needs ~1.9 GB when the library imports Mathlib (core oleans are read twice).
set -e
D=$(cd "$(dirname "$0")/.." && pwd)
cp "$(source "$D/hc.env"; echo "$HC_LIBDIR")/lean-toolchain" "$D/tools/lean-toolchain"
cd "$D/tools"
LEAN_NUM_THREADS=2 systemd-run --user --scope --quiet -p MemoryMax=${MEM:-3G} -p MemorySwapMax=0 lake build
# HCRepair (proof repair, v12) as a standalone module for stored proof files (scripts/repair_proofs.py), compiled
# with the library's lean into tools/hcrepair, which scripts/hclean puts on LEAN_PATH.
# Compiled from a copy: scripts/HCRepair.lean is a symlink into kit/, and lean wants the real file under its -R root.
mkdir -p "$D/tools/hcrepair"
cp "$D/scripts/HCRepair.lean" "$D/tools/hcrepair/HCRepair.lean"
systemd-run --user --scope --quiet -p MemoryMax=${MEM:-3G} -p MemorySwapMax=0 \
  "$D/scripts/hclean" -R "$D/tools/hcrepair" -o "$D/tools/hcrepair/HCRepair.olean" -i "$D/tools/hcrepair/HCRepair.ilean" "$D/tools/hcrepair/HCRepair.lean"
