#!/bin/bash
# Memory-capped library Lean for agents and checks: each call ≤ ${MEM:-2500M}, no swap, ${TMO:-900} s timeout.
# All calls share $HC_SLICE; the main session caps the slice, sized by min(60% RAM, MemAvailable − 2.5 GB):
#   systemctl --user set-property --runtime $HC_SLICE MemoryMax=5000M MemorySwapMax=0
# Without a systemd user session there is no cap (scripts/capped); the memory wait below still applies.
# Usage: scripts/lean.sh FILE.lean [lean args]
# Compiles of full files under checks/ or with a raised MEM take big.lock, so only one runs at a time.
# Waits (up to 10 min) until MemAvailable ≥ ${MINFREE:-2500} MB before starting.
D=$(cd "$(dirname "$0")" && pwd)
source "$D/../hc.env"
for _ in $(seq 120); do
  mi=$("$D/capped" --meminfo) || break  # memory size unknown on this platform: do not wait
  (( ${mi#* } >= ${MINFREE:-2500} )) && break
  sleep 5
done
LOCK=()
if [[ " $* " == *checks/* ]] || [ "${MEM:-2500M}" != 2500M ]; then LOCK=(--lock "$D/big.lock"); fi
exec "$D/capped" "${LOCK[@]}" --slice "$HC_SLICE" --mem "${MEM:-2500M}" --timeout "${TMO:-900}" -- "$D/hclean" "$@"
