#!/bin/bash
# peak.sh CAP CMD... : run CMD in a capped scope (no swap, OOMPolicy=continue) and print the scope's peak memory.
cap=$1; shift
exec systemd-run --user --scope --quiet -p MemoryMax=$cap -p MemorySwapMax=0 -p OOMPolicy=continue bash -c '
"$@"; rc=$?; cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
echo "[peak.sh] rc=$rc peak=$(( $(cat $cg/memory.peak) / 1048576 )) MiB events: $(tr "\n" " " < $cg/memory.events)" >&2; exit $rc' _ "$@"
