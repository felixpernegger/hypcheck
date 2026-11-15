"""Compare cluster agents run on different models (cost, speed, decided share) and apply the decision rule.

Usage: python3 scripts/model_compare.py SPEC.json
SPEC: {"baseline": "claude-opus-5-5",            # model the others are judged against
       "clusters": [{"name": "W8c1", "stratum": "Hash small",
                     "todo": "runs/.../todo_W8c1.jsonl", "verdicts": "runs/.../W8c1_verdicts.jsonl",
                     "transcript": "~/.claude/projects/.../subagents/agent-<id>.jsonl"}, ...]}
Paths are relative to the spec file's directory unless absolute or starting with ~.
Cost is what the API list price would charge; it comes from the transcript's per-message usage, not from
`subagent_tokens` (which ignores cache reads, the largest item). See Methods.md, "Model comparison".
"""
import collections, datetime, json, os, sys

# $/MTok: input, 5-min cache write, 1-h cache write, cache read, output. Update when prices change
# (check the claude-api skill's model table); a model missing here is an error, not a guess.
PRICES = {
    'claude-opus-5-5':   (4.0, 5.0, 8.0, 0.20, 20.0),
    'claude-sonnet-5-5': (2.0, 2.5, 4.0, 0.10, 10.0),
}
RULE = {'min_saving': 0.25, 'max_time_ratio': 1.2}  # vs baseline, per stratum


def path(base, p):
    p = os.path.expanduser(p)
    return p if os.path.isabs(p) else os.path.join(base, p)


def transcript_stats(p):
    """Usage summed over distinct API messages; wall time up to the agent's first hand-back."""
    seen, u, models, tools = set(), collections.Counter(), collections.Counter(), 0
    t0 = t_end = t_last = None
    for line in open(p):
        try:
            e = json.loads(line)
        except ValueError:
            continue
        ts = e.get('timestamp')
        if ts:
            t = datetime.datetime.fromisoformat(ts.replace('Z', '+00:00'))
            t0 = t0 or t
            t_last = t
        m = e.get('message')
        if not isinstance(m, dict):
            continue
        for b in m.get('content') if isinstance(m.get('content'), list) else []:
            if isinstance(b, dict) and b.get('type') == 'tool_use':
                tools += 1
                if b.get('name') == 'SubagentHandback' and t_end is None:
                    t_end = t_last
        if 'usage' not in m or m.get('id') in seen:
            continue
        seen.add(m.get('id'))
        models[m.get('model')] += 1
        us = m['usage']
        cc = us.get('cache_creation') or {}
        w1h = cc.get('ephemeral_1h_input_tokens') or 0
        u['in'] += us.get('input_tokens') or 0
        u['w1h'] += w1h
        u['w5m'] += (us.get('cache_creation_input_tokens') or 0) - w1h
        u['read'] += us.get('cache_read_input_tokens') or 0
        u['out'] += us.get('output_tokens') or 0
    model = models.most_common(1)[0][0]
    if model not in PRICES:
        sys.exit(f'{p}: no prices for {model}; add it to PRICES')

    pi, p5, p1, pr, po = PRICES[model]
    cost = (u['in'] * pi + u['w5m'] * p5 + u['w1h'] * p1 + u['read'] * pr + u['out'] * po) / 1e6
    minutes = ((t_end or t_last) - t0).total_seconds() / 60
    return model, cost, minutes, tools, u


def main(spec_path):
    spec = json.load(open(spec_path))
    base = os.path.dirname(os.path.abspath(spec_path))
    baseline = spec.get('baseline', 'claude-opus-5-5')
    rows = []
    for c in spec['clusters']:
        todo = sum(1 for l in open(path(base, c['todo'])) if l.strip())
        st = collections.Counter(json.loads(l).get('status') for l in open(path(base, c['verdicts'])) if l.strip())
        model, cost, minutes, tools, u = transcript_stats(path(base, c['transcript']))
        dec = sum(st.values())
        rows.append(dict(name=c['name'], stratum=c['stratum'], model=model, rows=todo, dec=dec, open=todo - dec,
                         rem=st.get('removable', 0), cost=cost, min=minutes, tools=tools,
                         read=u['read'], out=u['out']))
    print(f"{'cluster':8} {'stratum':16} {'model':18} {'rows':>5} {'dec':>5} {'open':>4} {'rem':>4} "
          f"{'min':>5} {'tools':>5} {'readM':>6} {'outK':>5} {'$':>6} {'$/dec':>6}")
    for r in rows:
        print(f"{r['name']:8} {r['stratum']:16} {r['model']:18} {r['rows']:5} {r['dec']:5} {r['open']:4} {r['rem']:4} "
              f"{r['min']:5.1f} {r['tools']:5} {r['read']/1e6:6.1f} {r['out']/1e3:5.0f} {r['cost']:6.2f} "
              f"{r['cost']/max(r['dec'], 1):6.3f}")
    # Per stratum and model: $ per decided row, with each open row charged at the baseline's $ per row
    # (it has to be redone), and minutes per row.
    agg = collections.defaultdict(lambda: collections.Counter())
    for r in rows:
        a = agg[(r['stratum'], r['model'])]
        for k in ('rows', 'dec', 'open', 'cost', 'min'):
            a[k] += r[k]
    print('\nper stratum (open rows charged at the baseline rate):')
    for stratum in sorted({s for s, _ in agg}):
        b = agg.get((stratum, baseline))
        if not b or not b['dec']:
            print(f'  {stratum}: no baseline cluster, skipped')
            continue
        b_row, b_min = b['cost'] / b['dec'], b['min'] / b['rows']
        for (s, model), a in sorted(agg.items()):
            if s != stratum:
                continue
            per_row = (a['cost'] + a['open'] * b_row) / a['rows']
            saving, tr = 1 - per_row / b_row, (a['min'] / a['rows']) / b_min
            open_ok = a['open'] / a['rows'] <= b['open'] / b['rows']
            verdict = '' if model == baseline else (
                ' -> USE' if saving >= RULE['min_saving'] and tr <= RULE['max_time_ratio'] and open_ok else ' -> keep baseline')
            print(f"  {stratum:16} {model:18} ${per_row:.4f}/row  saving {saving:+.0%}  time {tr:.2f}x  "
                  f"open {a['open']}/{a['rows']}{verdict}")


if __name__ == '__main__':
    main(sys.argv[1])
