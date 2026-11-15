#!/usr/bin/env bash
# Recompiles every stored proof file with stage1 (run after rebuilding stage1): checks/*.lean and the tool proofs
# under proofs/tool/ (public runs; the private runs are recompiled per module with scripts/priv/compile_priv.py,
# the 5 module copies under proofs/reproof/ with scripts/reproof_run.py). One summary line per file:
# "rc errors sorries seconds file" in runs/recheck_proofs/summary.txt, full logs next to it.
cd "$(dirname "$0")/.."
L=${LEAN:-${LEAN4_DIR:?set LEAN4_DIR to a lean4 checkout built at commit a2ec8251 (see README.md)}/build/release/stage1/bin/lean}
out=runs/recheck_proofs; mkdir -p $out
{ ls checks/*.lean; find proofs/tool -path proofs/tool/private -prune -o -name 'part_*.lean' -print | sort; } > $out/files.txt
check() {
  f=$1; key=$(echo "$f" | tr '/' '_')
  start=$(date +%s)
  timeout 3600 nice -n 10 $L "$f" > "$2/log_$key.txt" 2>&1; rc=$?
  errs=$(grep -c ": error" "$2/log_$key.txt")
  sorr=$(grep -c "declaration uses 'sorry'" "$2/log_$key.txt")
  echo "$rc $errs $sorr $(( $(date +%s) - start ))s $f"
}
export -f check; export L
xargs -P ${LANES:-3} -I{} bash -c 'check {} '"$out" < $out/files.txt > $out/summary.txt
echo done >> $out/summary.txt
