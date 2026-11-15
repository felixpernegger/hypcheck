#!/bin/bash
# rss_sampler.sh OUT: every 2 s append "epoch pid rss_kb anon_kb file_kb args" for every hypcheck worker, plus MemAvailable.
while :; do
  t=$(date +%s); a=$(awk '/MemAvailable/{print $2}' /proc/meminfo)
  for p in $(pgrep -f '[t]ool/.lake/build/bin/'); do
    s=/proc/$p/status; [ -r $s ] || continue
    echo "$t $p $(awk '/^VmRSS/{r=$2}/^RssAnon/{a=$2}/^RssFile/{f=$2}END{print r,a,f}' $s) avail=$a $(tr '\0' ' ' < /proc/$p/cmdline | cut -c1-80)"
  done >> "$1"
  sleep 2
done
