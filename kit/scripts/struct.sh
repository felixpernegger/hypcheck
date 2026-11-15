#!/bin/bash
# P2 cheap kernel-checked detectors over all public rows, plus the transitive-necessity edges for flow (P5) and
# for the `unlocks` field of agent todo rows. Usage (from the workspace root): scripts/struct.sh
# Outputs in runs/struct/: pub_unused, pub_unusedtrans, pub_instderivable, pub_twins, edges_all (+ .mem/.err).
# Hits only count as verdicts once their proof files are generated, checked and merged (see PLAYBOOK.md P2).
set -e
source hc.env
mkdir -p runs/struct
IN=runs/inventory/rows_public.jsonl
for t in unused unusedtrans instderivable twins; do
  MEM=${MEM:-4G} scripts/measure.sh runs/struct/$t -- scripts/hcrun $t "$HC_ROOT" $IN runs/struct/pub_$t.jsonl
done
MEM=${MEM:-4G} scripts/measure.sh runs/struct/nectrans -- scripts/hcrun nectrans "$HC_ROOT" $IN runs/struct/edges_all.jsonl
python3 - <<'PY'
import json, collections
def c(f, k): return dict(collections.Counter(str(json.loads(l).get(k)) for l in open(f'runs/struct/{f}.jsonl')))
print('unused         ', c('pub_unused', 'unused_check'))
print('unused (trans.)', c('pub_unusedtrans', 'droppable'))
print('inst-derivable ', c('pub_instderivable', 'inst_derivable'))
print('twin groups    ', sum(1 for _ in open('runs/struct/pub_twins.jsonl')))
rows = {(r['theorem'], r['idx']) for r in map(json.loads, open('runs/inventory/rows_public.jsonl'))}
E = [json.loads(l) for l in open('runs/struct/edges_all.jsonl')]
single = [e for e in E if len({tuple(t) for t in e['targets']}) == 1]
usable = [e for e in single if tuple(e['targets'][0]) in rows]
print(f'nectrans edges {len(E)}; single-target {len(single)}, onto in-scope rows {len(usable)} '
      f'({len({tuple(e["targets"][0]) for e in usable})} distinct targets)')
PY
