#!/bin/bash
# Run one command in a capped scope and report wall time, cgroup memory.peak, and the max anon/file RSS of
# its largest process (sampled every 0.5 s). Usage: MEM=3G scripts/measure.sh LOG -- CMD ARGS...
log=$1; shift; [[ $1 == -- ]] && shift
unit=hcm-$$-$RANDOM
start=$(date +%s.%N)
systemd-run --user --scope --quiet --unit=$unit -p MemoryMax=${MEM:-3G} -p MemorySwapMax=0 -p OOMPolicy=continue \
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
