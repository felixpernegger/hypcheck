#!/bin/bash
# Flow (P5 and after every merge), repeated until a full pass adds nothing:
#  - necessary by transitivity (cand_rem.py) and twins (twins_cand.py) -> chain_proofs.py -> merge_chain.py
#  - removable by transitivity (rem_trans.py)
# Each new verdict can enable the other direction, hence the outer loop. A necessary round that keeps nothing is
# not repeated (cand_rem.py has no memory of failed candidates; in Std one failing candidate looped for 30 min).
# Usage (from the workspace root): scripts/flow.sh
cd "$(dirname "$0")/.."
source hc.env
HC_CAP=$(scripts/capped --backend) || exit 1; export HC_CAP  # detect (and warn) once for all steps
mkdir -p runs/flow
last() { ls checks/$1*.lean 2>/dev/null | sed -E "s/.*$1([0-9]+).*\.lean/\1/" | sort -n | tail -1; }
K=$(last ChainProofs); K=${K:-0}
R=$(last RemTrans); R=${R:-0}
for pass in $(seq 1 50); do
  progress=0
  K=$((K+1))
  python3 scripts/cand_rem.py runs/struct/edges_all.jsonl $K >/dev/null; python3 scripts/twins_cand.py $K >/dev/null
  if [ -s runs/flow/cand_$K.jsonl ] || [ -s runs/flow/twins_$K.jsonl ]; then
    scripts/capped --slice "$HC_SLICE" --mem "${MEM:-3G}" -- \
      python3 scripts/chain_proofs.py runs/flow/cand_$K.jsonl runs/flow/twins_$K.jsonl checks/ChainProofs$K.lean > runs/flow/chain_$K.log 2>&1
    m=$(python3 -u scripts/merge_chain.py $K); echo "flow $K: $m" | tr '\n' ' '; echo
    echo "$m" | grep -qE "'(necessary|twin [a-z]+)': [1-9]" && progress=1
  else
    rm -f runs/flow/cand_$K.jsonl runs/flow/twins_$K.jsonl; K=$((K-1))
  fi
  R=$((R+1))
  m=$(python3 -u scripts/rem_trans.py $R 2>&1 | tee runs/flow/remtrans_$R.log | tail -1); echo "$m"
  echo "$m" | grep -qE "'removable': [1-9]" && progress=1 || R=$((R-1))
  (( progress )) || break
done
