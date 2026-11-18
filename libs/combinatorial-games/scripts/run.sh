#!/usr/bin/env bash
# Runs HypCheck (native exe tools/.lake/build/bin/hypcheck) with N worker processes that share a work queue, then merges their output.
# Usage: run.sh N OUT.jsonl [HypCheck options...]   (env: MEM_MAX cap, HC_UNIT scope name, PROGRESS=SECS, NO_COMPILE=1)
# All workers run in one memory-capped scope (scripts/capped) of $MEM_MAX (default: min(60% of RAM, available - 2.5 GB),
# no swap), so if they need too much memory the kernel kills a worker instead of freezing the machine. Without a
# systemd user session (macOS, containers) there is no cap: choose N by hand (measure one worker with measure.sh).
# Each worker also writes its proofs as Lean source; they end up in OUT.proofs/part_K.lean and are
# compiled once more with $lean at the end (skip with NO_COMPILE=1), log in OUT.proofs/compile.log.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
if [[ -z "${HYPCHECK_SCOPED:-}" ]]; then
  HC_CAP=$("$here/capped" --backend) || exit 1; export HC_CAP
  # Default cap: 60% of RAM, but never more than what is available now minus 2.5 GB headroom for the
  # rest of the system. A cap at 60% of total RAM alone froze a machine whose editor and Lean servers
  # already held ~6 GB: the system ran out of memory before the scope's cap was reached.
  if mi=$("$here/capped" --meminfo); then
    total_mb=${mi% *}; avail_mb=${mi#* }
    cap_mb=$(( total_mb * 6 / 10 ))
    room_mb=$(( avail_mb - 2560 ))
    (( room_mb < cap_mb )) && cap_mb=$room_mb
    if (( cap_mb < 1536 )); then
      echo "run.sh: only $avail_mb MiB available; refusing to start (set MEM_MAX to override)" >&2
      [[ -z "${MEM_MAX:-}" ]] && exit 1
    fi
  else
    cap_mb=4096; echo "run.sh: cannot read the memory size here; default cap 4096M" >&2
  fi
  mem=${MEM_MAX:-${cap_mb}M}
  unit=${HC_UNIT:-hc-$$}
  if [[ $HC_CAP == systemd ]]; then
    # Named unit, so a run is stopped with `systemctl --user stop $HC_UNIT.scope` (no process grepping).
    echo "run.sh: unit $unit.scope, cap $mem; stop with: systemctl --user stop $unit.scope" >&2
  else
    echo "run.sh: no memory cap (no systemd user session); stop with Ctrl-C or: kill -- -$$" >&2
  fi
  exec "$here/capped" --unit "$unit" --mem "$mem" --oom-continue -- env HYPCHECK_SCOPED=1 MEM_MAX="$mem" "$0" "$@"
fi
n=$1; out=$2; shift 2
lean=${LEAN:-$here/hclean}
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
      # Native worker (tools/); `lean --run` costs ~1.6 GB more per worker when Mathlib is imported.
      if nice -n 10 "$here/hcrun" hypcheck "$@" --claim-dir "$claims" \
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
# PROGRESS=SECS: print "done of total theorems" to stderr every SECS seconds (tool/hypcheck sets it).
prog=
if [[ -n "${PROGRESS:-}" ]]; then
  (
    while sleep "$PROGRESS"; do
      shopt -s nullglob; e=("$parts"/err_*.txt)
      (( ${#e[@]} )) || continue
      tot=$(sed -n 's/^\([0-9]*\) theorems selected.*/\1/p' "${e[@]}" | head -1)
      dn=$(cat "${e[@]}" | grep -c '^\[')
      echo "run.sh: $(date +%H:%M) ${dn} of ${tot:-?} theorems done" >&2
    done
  ) &
  prog=$!
fi
failed=0
for p in "${pids[@]}"; do wait "$p" || failed=$((failed + 1)); done
[[ -n "$prog" ]] && kill "$prog" 2> /dev/null
shopt -s nullglob
cat /dev/null "$parts"/out_*.jsonl > "$out"
cat /dev/null "$parts"/err_*.txt > "${out%.jsonl}.log"
pdir="${out%.jsonl}.proofs"
mkdir -p "$pdir"
for f in "$parts"/proofs_*.lean; do b=$(basename "$f" .lean); mv "$f" "$pdir/part_${b#proofs_}.lean"; done
restarts=0; [[ -f "$parts/restarts.txt" ]] && restarts=$(wc -l < "$parts/restarts.txt")
claimed=$(ls "$claims" | wc -l)
done_thms=$(grep -c '^\[' "${out%.jsonl}.log" || true)
peak=n/a
if [[ $HC_CAP == systemd && -r /proc/self/cgroup ]]; then
  cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
  [[ -r "$cg/memory.peak" ]] && peak=$(( $(cat "$cg/memory.peak") / 1024 / 1024 ))
fi
echo "$(wc -l < "$out") results for $done_thms of $claimed claimed theorems -> $out"
echo "workers failed: $failed of $n; worker restarts after a kill/crash: $restarts; peak memory ${peak} MiB (cap $MEM_MAX, backend $HC_CAP)"
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
