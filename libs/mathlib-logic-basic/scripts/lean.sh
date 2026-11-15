#!/bin/bash
# Memory-capped library Lean for agents and checks: each call ≤ ${MEM:-3000M}, no swap, ${TMO:-900} s timeout.
# mathlib-data (2026-11-14): default 3000M. Agent files import HCHeaderM (all Mathlib.Data, ~2.2 GB of mmapped oleans, shared
# in the slice, own memory ~0.15 GB); `import Mathlib` (runs/probe/Header_mathlib.lean, 4.9 GB) needs MEM=6000M.
# All calls share $HC_SLICE; the main session caps the slice, sized by min(60% RAM, MemAvailable − 2.5 GB):
#   systemctl --user set-property --runtime $HC_SLICE MemoryMax=5000M MemorySwapMax=0
# Usage: scripts/lean.sh FILE.lean [lean args]
# Compiles of full files under checks/ or with a raised MEM take big.lock, so only one runs at a time.
# Waits (up to 10 min) until MemAvailable ≥ ${MINFREE:-2500} MB before starting.
D=$(cd "$(dirname "$0")" && pwd)
source "$D/../hc.env"
for _ in $(seq 120); do
  (( $(awk '/MemAvailable/ {print int($2/1024)}' /proc/meminfo) >= ${MINFREE:-2500} )) && break
  sleep 5
done
CMD=(systemd-run --user --scope --quiet --slice="$HC_SLICE" -p MemoryMax=${MEM:-3000M} -p MemorySwapMax=0 \
  timeout ${TMO:-900} "$D/hclean" "$@")
if [[ " $* " == *checks/* ]] || [ "${MEM:-3000M}" != 3000M ]; then exec flock "$D/big.lock" "${CMD[@]}"; fi
exec "${CMD[@]}"
