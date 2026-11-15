#!/bin/bash
# Memory-capped CSLib Lean for agents and checks: each call ≤ ${MEM:-2500M}, no swap, ${TMO:-900} s timeout;
# all calls share hcslib.slice (the main session caps the slice, e.g.
#   systemctl --user set-property --runtime hcslib.slice MemoryMax=5000M MemorySwapMax=0
# sized by min(60% RAM, MemAvailable − 2.5 GB)). Usage: scripts/lean.sh FILE.lean [lean args]
# Compiles of full files under checks/ or with a raised MEM take big.lock, so only one runs at a time.
# Waits (up to 10 min) until MemAvailable ≥ ${MINFREE:-2500} MB before starting.
D=$(cd "$(dirname "$0")" && pwd)
for _ in $(seq 120); do
  (( $(awk '/MemAvailable/ {print int($2/1024)}' /proc/meminfo) >= ${MINFREE:-2500} )) && break
  sleep 5
done
CMD=(systemd-run --user --scope --quiet --slice=hcslib.slice -p MemoryMax=${MEM:-2500M} -p MemorySwapMax=0 \
  timeout ${TMO:-900} "$D/cslean" "$@")
if [[ " $* " == *checks/* ]] || [ "${MEM:-2500M}" != 2500M ]; then exec flock "$D/big.lock" "${CMD[@]}"; fi
exec "${CMD[@]}"
