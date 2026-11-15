"""Random sample of open rows, for tool pilots (P3) and agent probes (P6a).
Usage (from the workspace root):
  python3 scripts/sample_rows.py N SEED OUT.jsonl              # N random unresolved rows (public + private)
  python3 scripts/sample_rows.py N SEED --probe K [DIR]        # same, sorted by module and split into K todo files
  (--dependent anywhere: only dependent rows, the input of scripts/gen_drive.py; N = 0: all of them)
                                                               # DIR/todo_Probe<k>.jsonl (default DIR runs/probe)
Rows carry `private` (true for rows of results/private*.jsonl)."""
import json, sys, os, random
sys.path.insert(0, 'scripts')
import results_io as io
n, seed = int(sys.argv[1]), int(sys.argv[2])
DEP = '--dependent' in sys.argv
if DEP: sys.argv.remove('--dependent')
rows = [dict(r, private=(b == 'private')) for b in io.BASES for r in io.load(b) if r['status'] == 'unresolved']
if DEP: rows = [r for r in rows if r.get('dependent')]
random.Random(seed).shuffle(rows)
rows = sorted(rows[:n] if n else rows, key=lambda r: (r['module'], r['line'], r['idx']))
if sys.argv[3] == '--probe':
    k = int(sys.argv[4]); d = sys.argv[5] if len(sys.argv) > 5 else 'runs/probe'
    os.makedirs(d, exist_ok=True)
    for j in range(k):
        part = rows[j * len(rows) // k:(j + 1) * len(rows) // k]
        p = f'{d}/todo_Probe{j + 1}.jsonl'
        assert not os.path.exists(p), f'{p} exists'
        with open(p, 'w') as f:
            for r in part: f.write(json.dumps(r, ensure_ascii=False) + '\n')
        print(p, len(part), 'rows', len({r['module'] for r in part}), 'modules')
else:
    with open(sys.argv[3], 'w') as f:
        for r in rows: f.write(json.dumps(r, ensure_ascii=False) + '\n')
    print(sys.argv[3], len(rows), 'rows')
