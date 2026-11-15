#!/bin/bash
# P2, second half: turn the detector hits of scripts/struct.sh into stored, checked, merged removable verdicts.
#   unused + transitively unused -> checks/UnusedHand.lean (`drop_unused%`, recursive), found_by unused-proof
#   instance-derivable           -> checks/InstDerivHand.lean (`derive_inst%`),        found_by inst-derivable
# Each file is generated (failing declarations dropped), checked by check_hand.py with axioms, and merged only if
# check_hand reports 0 errors, 0 not covered and standard axioms. Usage (from the workspace root): scripts/struct_proofs.sh
set -e
source hc.env
HC_CAP=$(scripts/capped --backend) || exit 1; export HC_CAP  # detect (and warn) once for all steps
S=runs/struct
python3 - <<'PY'
import json
def hits(f, k, v): return [r for r in map(json.loads, open(f'runs/struct/{f}.jsonl')) if str(r.get(k)).lower() == v]
drop = {(r['theorem'], r['idx']): r for r in hits('pub_unused', 'unused_check', 'unused') + hits('pub_unusedtrans', 'droppable', 'true')}
der = {(r['theorem'], r['idx']): r for r in hits('pub_instderivable', 'inst_derivable', 'derivable') if (r['theorem'], r['idx']) not in drop}
for name, rs in (('Unused', drop), ('InstDeriv', der)):
    with open(f'runs/struct/{name}_in.jsonl', 'w') as f:
        for r in rs.values(): f.write(json.dumps(dict(r, unused_check='unused'), ensure_ascii=False) + '\n')  # UnusedEmit's filter
    print(name, len(rs), 'hits')
PY
for C in Unused InstDeriv; do
  [ -s $S/${C}_in.jsonl ] || continue
  scripts/hcrun unusedemit "$HC_ROOT" $S/${C}_in.jsonl $S/${C}_stmts.jsonl
  if [ $C = Unused ]; then gen="scripts/unused_proofs.py $S/${C}_stmts.jsonl checks/${C}Hand.lean $HC_ROOT --rec"; fb=unused-proof; der=False
  else gen="scripts/derive_proofs.py $S/${C}_stmts.jsonl checks/${C}Hand.lean $HC_ROOT"; fb=inst-derivable; der=True; fi
  scripts/capped --slice "$HC_SLICE" --mem "${MEM:-3G}" -- python3 $gen | tail -2
  python3 - $C $der <<'PY'
import json, sys
C, der = sys.argv[1], sys.argv[2] == 'True'
rows = {(r['theorem'], r['idx']): r for r in map(json.loads, open(f'runs/struct/{C}_in.jsonl'))}
note = 'derivable by instance resolution from the other binders' if der else "unused in the library's proof (directly or transitively)"
with open(f'runs/struct/{C}_verdicts.jsonl', 'w') as f:
    for o in map(json.loads, open(f'checks/{C}Hand.lean.ok.jsonl')):
        r = dict(rows[(o['theorem'], o['idx'])], status='removable', derivable=der, note=note)
        f.write(json.dumps(r, ensure_ascii=False) + '\n')
PY
  out=$(HANDCHECK_AXIOMS=1 scripts/capped --slice "$HC_SLICE" --mem "${MEM:-3G}" -- \
        python3 scripts/check_hand.py checks/${C}Hand.lean $S/${C}_verdicts.jsonl 2>&1 | grep -E "lean errors|NOT COVERED|^axioms:|AXIOMS")
  echo "$out"
  if echo "$out" | grep -q 'lean errors: 0;.*not covered: 0' && echo "$out" | grep -qE 'axioms: [0-9]+ standard, 0 other, 0 missing'; then
    python3 scripts/merge_hand.py $S $C $fb
  else echo "$C: check failed, not merged"; fi
done
