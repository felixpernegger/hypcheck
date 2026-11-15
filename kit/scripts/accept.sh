#!/bin/bash
# Accept one finished agent cluster: scripts/verify.sh must end in VERIFY PASS -> merge public + private -> flow rounds (transitive necessity +
# twins) until a round merges nothing -> totals. Serialized by runs/accept.lock; safe to start in the background.
# Usage (from the workspace root): scripts/accept.sh DIR C   e.g. runs/waves/W1 W1c0
set -o pipefail
cd "$(dirname "$0")/.."
exec 9> runs/accept.lock; flock 9
D=$1; C=$2
out=$(scripts/verify.sh $D $C 2>&1); echo "$out" > $D/${C}_verify_main.txt; echo "$out"
echo "$out" | tail -1 | grep -q "^VERIFY PASS" || { echo "ACCEPT $C: verify FAILED, not merged"; exit 1; }
python3 scripts/merge_hand.py $D $C hand && python3 scripts/merge_hand.py --private $D $C hand || { echo "ACCEPT $C: merge failed"; exit 1; }
scripts/flow.sh
python3 scripts/status.py | tail -3
echo "ACCEPT $C: merged"
