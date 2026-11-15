#!/bin/bash
# merge_wave.sh WAVE CLUSTER: split the cluster's verdicts into public/private and merge each with merge_hand.py
W=$1; C=$2; D=runs/waves/$W
mkdir -p $D/merge_pub $D/merge_priv
python3 - "$D" "$C" <<'PY'
import json,sys
D,C=sys.argv[1:]
for kind in ('verdicts','independent'):
    try: V=[json.loads(l) for l in open(f'{D}/{C}_{kind}.jsonl')]
    except FileNotFoundError: continue
    for sub,priv in (('merge_pub',False),('merge_priv',True)):
        with open(f'{D}/{sub}/{C}_{kind}.jsonl','w') as f:
            for v in V:
                if v['theorem'].startswith('_private.')==priv: f.write(json.dumps(v,ensure_ascii=False)+'\n')
PY
python3 scripts/merge_hand.py $D/merge_pub $C hand
python3 scripts/merge_hand.py --priv $D/merge_priv $C hand
