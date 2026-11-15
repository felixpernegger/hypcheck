#!/bin/bash
# Check one agent cluster and print VERIFY PASS / VERIFY FAIL (reasons) as the last line.
# Usage (from the workspace root): scripts/verify.sh DIR C   e.g. runs/waves/W1 W1c0, runs/probe Probe1
# Inputs: checks/<C>Hand.lean, DIR/todo_<C>.jsonl, DIR/<C>_verdicts.jsonl, optional DIR/<C>_independent.jsonl.
# Pass = header copy unchanged, keyword grep empty, check_hand 0 Lean errors / 0 not covered, axioms 0 other /
# 0 missing, coverage extra 0 / dup 0. One full compile (check_hand.py compiles the file and reports Lean errors),
# in the shared slice under big.lock. check_hand's kernel-level axiom check is authoritative; the grep is a backstop.
D=$1; C=$2; F=checks/${C}Hand.lean; H=runs/probe/Header.lean
source hc.env
fail=()
echo "== header"
if [ "$(head -c $(stat -c %s $H) $F)" == "$(cat $H)" ]; then echo "header prefix unchanged"; else echo "HEADER CHANGED"; fail+=(header); fi
echo "== grep"
g=$(tail -n +$(( $(wc -l < $H) + 1 )) $F | grep -nE '\bsorry\b|native_decide|^\s*(@\[[^]]*\]\s*)?(private |protected |noncomputable )*axiom\s|implemented_by|^\s*opaque\s|^import ' | grep -v 'hasSorry')
[ -n "$g" ] && { echo "$g" | head; fail+=(grep); }
echo "== check_hand (+ axioms)"
out=$(HANDCHECK_AXIOMS=1 flock scripts/big.lock systemd-run --user --scope --quiet --slice="$HC_SLICE" \
  -p MemoryMax=${MEM:-3000M} -p MemorySwapMax=0 python3 scripts/check_hand.py $F $D/${C}_verdicts.jsonl 2>&1 \
  | grep -E "lean errors|NOT COVERED|not covered|^axioms:|AXIOMS (OTHER|MISSING)|error" | head -20)
echo "$out"
echo "$out" | grep -q 'lean errors: 0;' || fail+=(lean-errors)
echo "$out" | grep -q 'not covered: 0' || fail+=(not-covered)
echo "$out" | grep -qE 'axioms: [0-9]+ standard, 0 other, 0 missing' || fail+=(axioms)
echo "== coverage"
cov=$(python3 - "$D" "$C" <<'PY'
import json, sys, os, collections
D, C = sys.argv[1:]
todo = {(r['theorem'], r['idx']) for r in map(json.loads, open(f'{D}/todo_{C}.jsonl'))}
V = [json.loads(l) for l in open(f'{D}/{C}_verdicts.jsonl')] if os.path.exists(f'{D}/{C}_verdicts.jsonl') else []
v = [(r['theorem'], r['idx']) for r in V]
f = f'{D}/{C}_independent.jsonl'
i = {(r['theorem'], r['idx']) for r in map(json.loads, open(f))} if os.path.exists(f) else set()
print(C, 'todo', len(todo), 'verdicts', len(set(v)), dict(collections.Counter(r['status'] for r in V)), 'indep', len(i),
      'left', len(todo - set(v) - i), 'extra', len((set(v) | i) - todo), 'dup', len(v) - len(set(v)))
PY
)
echo "$cov"
echo "$cov" | grep -q 'extra 0 dup 0' || fail+=(coverage)
if (( ${#fail[@]} == 0 )); then echo "VERIFY PASS $C"; else echo "VERIFY FAIL $C: ${fail[*]}"; fi
