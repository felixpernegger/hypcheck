"""Summarize a pilot run: statuses, tactics, reason classes, per-theorem times.
Usage: python3 scripts/pilot_summary.py OUT.jsonl [OUT.log]"""
import json, sys, re, collections
rs = [json.loads(l) for l in open(sys.argv[1])]
print('status:', collections.Counter((r['status'], r.get('proof_ok')) for r in rs))
for r in rs:
    if r['status'] != 'unresolved':
        print(f"  {r['status']:10} {r['theorem']} #{r['idx']} {r['name']}: {r.get('tactic')} "
              f"{(r.get('witness') or '')[:70]} dep={r.get('dependent', False)}")
def rclass(s):
    s = s or ''
    if s.startswith('non-enumerable'): return 'non-enumerable data'
    if s.startswith('no counterexample among 0'): return 'no cex: 0 instantiations'
    if s.startswith('no counterexample'): return 'no cex: >0 instantiations'
    if s.startswith('evaluation stuck'): return 'evaluation stuck'
    return s[:50]
print('unresolved reasons:', collections.Counter(rclass(r.get('reason')) for r in rs if r['status'] == 'unresolved'))
if len(sys.argv) > 2:
    ts = [int(m.group(1)) for l in open(sys.argv[2]) if (m := re.search(r'\((\d+) ms\)', l))]
    ts.sort()
    if ts: print(f'theorem times ms: n={len(ts)} median={ts[len(ts)//2]} p90={ts[int(len(ts)*.9)]} max={ts[-1]} sum={sum(ts)/1000:.0f}s')
