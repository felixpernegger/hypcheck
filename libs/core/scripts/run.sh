#!/usr/bin/env bash
# Runs HypCheck.lean with N worker processes that share a work queue, then merges their output.
# Usage: run.sh N OUT.jsonl [HypCheck options...]
# All workers run in one systemd scope capped at $MEM_MAX (default: min(60% of RAM, available - 2.5 GB), no swap), so if
# they need too much memory the kernel kills a worker instead of freezing the machine.
# Each worker also writes its proofs as Lean source; they end up in OUT.proofs/part_K.lean and are
# compiled once more with $lean at the end (skip with NO_COMPILE=1), log in OUT.proofs/compile.log.
set -euo pipefail
if [[ -z "${HYPCHECK_SCOPED:-}" ]]; then
  total_kb=$(awk '/MemTotal/ {print $2}' /proc/meminfo)
  avail_kb=$(awk '/MemAvailable/ {print $2}' /proc/meminfo)
  # Default: 60% of RAM, but never more than what is available now minus 2.5 GB headroom for the
  # rest of the system. A cap at 60% of total RAM alone froze a machine whose editor and Lean servers
  # already held ~6 GB: the system ran out of memory before the scope's cap was reached.
  cap_kb=$(( total_kb * 6 / 10 ))
  room_kb=$(( avail_kb - 2560 * 1024 ))
  (( room_kb < cap_kb )) && cap_kb=$room_kb
  if (( cap_kb < 1536 * 1024 )); then
    echo "run.sh: only $(( avail_kb / 1024 )) MiB available; refusing to start (set MEM_MAX to override)" >&2
    [[ -z "${MEM_MAX:-}" ]] && exit 1
  fi
  mem=${MEM_MAX:-$(( cap_kb / 1024 ))M}
  exec systemd-run --user --scope --quiet -p MemoryMax="$mem" -p MemorySwapMax=0 -p OOMPolicy=continue \
    env HYPCHECK_SCOPED=1 MEM_MAX="$mem" "$0" "$@"
fi
n=$1; out=$2; shift 2
here=$(cd "$(dirname "$0")" && pwd)
lean=${LEAN:-${LEAN4_DIR:?set LEAN4_DIR to a lean4 checkout built at commit a2ec8251 (see README.md)}/build/release/stage1/bin/lean}
claims=$(mktemp -d)
parts=$(mktemp -d)
pids=()
# A worker killed by the memory cap is restarted with fresh output files (output is flushed per
# theorem, so only the theorem it was working on is lost; the claim directory keeps it from being
# claimed again).
for k in $(seq 1 "$n"); do
  (
    a=0
    while :; do
      a=$((a + 1))
      if nice -n 10 "$lean" --run "$here/HypCheck.lean" "$@" --claim-dir "$claims" \
          -o "$parts/out_${k}_$a.jsonl" --proofs "$parts/proofs_${k}_$a.lean" 2> "$parts/err_${k}_$a.txt"; then
        exit 0
      else
        echo "worker $k attempt $a exited with $?" >> "$parts/restarts.txt"
      fi
      (( a >= 50 )) && exit 1
    done
  ) &
  pids+=($!)
done
failed=0
for p in "${pids[@]}"; do wait "$p" || failed=$((failed + 1)); done
shopt -s nullglob
cat /dev/null "$parts"/out_*.jsonl > "$out"
cat /dev/null "$parts"/err_*.txt > "${out%.jsonl}.log"
pdir="${out%.jsonl}.proofs"
mkdir -p "$pdir"
for f in "$parts"/proofs_*.lean; do b=$(basename "$f" .lean); mv "$f" "$pdir/part_${b#proofs_}.lean"; done
restarts=0; [[ -f "$parts/restarts.txt" ]] && restarts=$(wc -l < "$parts/restarts.txt")
claimed=$(ls "$claims" | wc -l)
done_thms=$(grep -c '^\[' "${out%.jsonl}.log" || true)
cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
peak=$(( $(cat "$cg/memory.peak" 2>/dev/null || echo 0) / 1024 / 1024 ))
echo "$(wc -l < "$out") results for $done_thms of $claimed claimed theorems -> $out"
echo "workers failed: $failed of $n; worker restarts after a kill/crash: $restarts; peak memory ${peak} MiB (cap $MEM_MAX)"
if (( done_thms < claimed )); then
  echo "WARNING: $(( claimed - done_thms )) claimed theorems have no result (worker killed mid-theorem)"
fi
rm -rf "$claims" "$parts"
okd=$(grep -c '"proof_ok":true' "$out" || true)
bad=$(grep -c '"proof_ok":false' "$out" || true)
echo "proofs: $okd checked in-process, $bad failed (kept as comments) -> $pdir"
if [[ -z "${NO_COMPILE:-}" ]]; then
  : > "$pdir/compile.log"
  cpids=()
  for f in "$pdir"/part_*.lean; do
    ( if nice -n 10 "$lean" "$f" > "$f.out" 2>&1; then echo "OK   $f"; else echo "FAIL $f (see $f.out)"; fi ) >> "$pdir/compile.log" &
    cpids+=($!)
  done
  for p in "${cpids[@]}"; do wait "$p"; done
  sort -o "$pdir/compile.log" "$pdir/compile.log"
  cat "$pdir/compile.log"
fi
