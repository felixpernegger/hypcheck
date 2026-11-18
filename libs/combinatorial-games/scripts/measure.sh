#!/bin/bash
# Run one command in a capped scope and report wall time, cgroup memory.peak, and the max anon/file RSS of
# its largest process (sampled every 0.5 s). Usage: MEM=3G scripts/measure.sh LOG -- CMD ARGS...
# Without a systemd user session (scripts/capped) the command runs uncapped and the report has wall time and the
# peak resident memory of its largest process (getrusage; includes mapped .olean pages, so it reads higher).
log=$1; shift; [[ $1 == -- ]] && shift
D=$(cd "$(dirname "$0")" && pwd)
HC_CAP=$("$D/capped" --backend) || exit 1; export HC_CAP
if [[ $HC_CAP != systemd ]]; then
  python3 - "$log" "$@" <<'PY'
import resource, subprocess, sys, time
log, cmd = sys.argv[1], sys.argv[2:]
t = time.time()
with open(log + '.out', 'w') as o, open(log + '.err', 'w') as e:
    rc = subprocess.call(cmd, stdout=o, stderr=e, stdin=subprocess.DEVNULL)
wall = time.time() - t
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss  # KiB on Linux, bytes on macOS
mb = rss / 1048576 if sys.platform == 'darwin' else rss / 1024
line = f'rc={rc} wall={wall:.1f}s max_rss={mb:.0f}MB (no cgroup: uncapped, peak RSS of the largest process)\n'
sys.stdout.write(line); open(log + '.mem', 'w').write(line)
sys.exit(rc)
PY
  exit $?
fi
unit=hcm-$$-$RANDOM
start=$(date +%s.%N)
"$D/capped" --unit "$unit" --mem "${MEM:-3G}" --oom-continue -- \
  bash -c 'exec "$@"' _ "$@" > "$log.out" 2> "$log.err" &
pid=$!
maxa=0; maxf=0; peak=0
cg=/sys/fs/cgroup/user.slice/user-$(id -u).slice/user@$(id -u).service/app.slice/$unit.scope
while kill -0 $pid 2>/dev/null; do
  for p in $(cat $cg/cgroup.procs 2>/dev/null); do
    a=$(awk '/RssAnon/ {print $2}' /proc/$p/status 2>/dev/null); f=$(awk '/RssFile/ {print $2}' /proc/$p/status 2>/dev/null)
    (( ${a:-0} > maxa )) && maxa=$a; (( ${f:-0} > maxf )) && maxf=$f
  done
  pk=$(cat $cg/memory.peak 2>/dev/null); (( ${pk:-0} > peak )) && peak=$pk
  sleep 0.5
done
wait $pid; rc=$?
end=$(date +%s.%N)
printf 'rc=%s wall=%.1fs cgroup_peak=%dMB max_RssAnon=%dMB max_RssFile=%dMB\n' $rc $(echo "$end - $start" | bc) $((peak/1048576)) $((maxa/1024)) $((maxf/1024)) | tee "$log.mem"
