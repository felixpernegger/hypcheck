#!/bin/bash
# One round of transitive necessity over Std (from the repository root): scripts/flow/round.sh K
set -e
K=$1; D=runs/flow; mkdir -p $D; L=${LEAN:-${LEAN4_DIR:?set LEAN4_DIR to a lean4 checkout built at commit a2ec8251 (see README.md)}/build/release/stage1/bin/lean}
python3 - $K <<'PY'
import json,sys
K=sys.argv[1]
rows=[json.loads(l) for l in open('results/std.jsonl')]
with open(f'runs/flow/nec_{K}.jsonl','w') as f:
    for r in rows:
        if r['status']=='necessary' and not r.get('dependent'): f.write(json.dumps({'theorem':r['theorem'],'idx':r['idx']})+'\n')
PY
systemd-run --user --scope --quiet -p MemoryMax=${MEM:-3500M} -p MemorySwapMax=0 $L --run scripts/NecTrans.lean Std $D/nec_$K.jsonl $D/nectrans_$K.jsonl
python3 - $K <<'PY'
import json,sys
K=sys.argv[1]
unres={(r['theorem'],r['idx']):r for r in map(json.loads,open('results/std.jsonl')) if r['status']=='unresolved'}
seen=set(); n=0
with open(f'runs/flow/cand_{K}.jsonl','w') as f:
    for r in map(json.loads,open(f'runs/flow/nectrans_{K}.jsonl')):
        ts={(a,i) for a,i in r['targets']}
        if len(ts)!=1: continue
        (a,i),=ts
        if (a,i) in unres and (a,i) not in seen:
            seen.add((a,i)); n+=1
            f.write(json.dumps({'A':a,'i':i,'B':r['B'],'j':r['j'],'moduleA':unres[(a,i)]['module']})+'\n')
print('round',K,'candidates',n)
PY
: > $D/twins_empty.jsonl
systemd-run --user --scope --quiet -p MemoryMax=${MEM:-3500M} -p MemorySwapMax=0 python3 scripts/chain_proofs.py $D/cand_$K.jsonl $D/twins_empty.jsonl checks/ChainProofsStd$K.lean
