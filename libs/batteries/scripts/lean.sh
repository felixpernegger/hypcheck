#!/bin/bash
# Memory-capped pinned-toolchain Lean (via ./blean) for agents and hand files. Merged from hypcheck
# the core workspace's agent wrappers. Each call ≤ ${MEM:-1500M}; all calls share
# bat.slice (cap it once: systemctl --user set-property bat.slice MemoryMax=…  MemorySwapMax=0), no swap,
# ${TMO:-900} s timeout. Full-file compiles (paths containing checks/) or a raised MEM take big.lock (one at a time).
# Usage (any cwd): hypcheck/scripts/lean.sh FILE.lean [lean args]
D=$(dirname "$(readlink -f "$0")")
avail=$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo)
if [ "$avail" -lt 1500 ]; then echo "lean.sh: MemAvailable ${avail} MB < 1500 MB, refusing to start" >&2; exit 75; fi
CMD=(systemd-run --user --scope --quiet --slice=bat.slice -p MemoryMax=${MEM:-1500M} -p MemorySwapMax=0 \
  timeout ${TMO:-900} "$D/blean" "$@")
if [[ " $* " == *checks/* ]] || [ "${MEM:-1500M}" != 1500M ]; then exec flock "$D/big.lock" "${CMD[@]}"; fi
exec "${CMD[@]}"
