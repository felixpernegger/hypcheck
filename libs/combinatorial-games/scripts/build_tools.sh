#!/bin/bash
# Build the native tools (tools/, one lean_exe per scripts/*.lean tool) with the library's toolchain, in a
# memory-capped scope (scripts/capped). Rerun after editing any scripts/*.lean tool. Native exes need ~0.2 GB per process where
# `lean --run` needs ~1.9 GB when the library imports Mathlib (core oleans are read twice).
set -e
D=$(cd "$(dirname "$0")/.." && pwd)
HC_CAP=$("$D/scripts/capped" --backend) || exit 1; export HC_CAP  # detect (and warn) once
cp "$(source "$D/hc.env"; echo "$HC_LIBDIR")/lean-toolchain" "$D/tools/lean-toolchain"
cd "$D/tools"
LEAN_NUM_THREADS=2 "$D/scripts/capped" --mem "${MEM:-3G}" -- lake build
# HCRepair (proof repair, v12) as a standalone module for stored proof files (scripts/repair_proofs.py), compiled
# with the library's lean into tools/hcrepair, which scripts/hclean puts on LEAN_PATH.
mkdir -p "$D/tools/hcrepair"
"$D/scripts/capped" --mem "${MEM:-3G}" -- \
  "$D/scripts/hclean" -R "$D/scripts" -o "$D/tools/hcrepair/HCRepair.olean" -i "$D/tools/hcrepair/HCRepair.ilean" "$D/scripts/HCRepair.lean"
