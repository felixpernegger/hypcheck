#!/usr/bin/env python3
"""P3b driver: scripts/gen_dep.py over chunks of a row file, in parallel lanes under a memory budget.

Usage (from the workspace root): python3 scripts/gen_drive.py ROWS.jsonl WORKDIR
Env: LANES (default 3), CHUNK (25), MINFREE_MB (MemAvailable needed to start a lane, 4500), PANIC_MB (below this
the newest lane is killed and requeued, 1200), plus HB/MODE/MEM/TMO for gen_dep.py.
Chunks: WORKDIR/chunks/<name>.jsonl; a chunk is done when <name>_verdicts.jsonl.failed.jsonl exists, so a
restarted driver resumes. A chunk whose compile is killed (exit 3) is split in halves and requeued; a single killed
row is recorded as failed. Exit 1 of gen_dep.py (errors outside the theorems: header or Models.lean broken) stops
new starts. Progress: WORKDIR/status.txt (every 20 s) and WORKDIR/drive.log; watch both (alert if status.txt goes
stale for 20 min). Then: python3 scripts/gen_accept.py WORKDIR."""
import json, os, signal, subprocess, sys, time

rows_f, work = sys.argv[1], sys.argv[2]
LANES = int(os.environ.get('LANES', 3)); CHUNK = int(os.environ.get('CHUNK', 25))
MINFREE = int(os.environ.get('MINFREE_MB', 4500)); PANIC = int(os.environ.get('PANIC_MB', 1200))
cdir = os.path.join(work, 'chunks'); os.makedirs(cdir, exist_ok=True)
logf = open(os.path.join(work, 'drive.log'), 'a')


def log(msg):
    logf.write(time.strftime('%H:%M:%S ') + msg + '\n'); logf.flush()


def mem_avail():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable:'): return int(l.split()[1]) // 1024
    return 0


def path(name, suf): return os.path.join(cdir, name + suf)
def done(name): return os.path.exists(path(name, '_verdicts.jsonl.failed.jsonl'))


def write_chunk(name, rs):
    with open(path(name, '.jsonl'), 'w') as f:
        for r in rs: f.write(json.dumps(r, ensure_ascii=False) + '\n')


if not any(n.endswith('.jsonl') for n in os.listdir(cdir)):
    rows = [json.loads(l) for l in open(rows_f)]
    for k in range(0, len(rows), CHUNK): write_chunk(f'c{k // CHUNK:04d}', rows[k:k + CHUNK])
queue = sorted(n[:-6] for n in os.listdir(cdir) if n.endswith('.jsonl') and '_verdicts' not in n and not done(n[:-6]))
running = {}
fatal = False; t0 = time.time()
log(f'start: {len(queue)} chunks queued, lanes {LANES}')


def finish(name, p):
    global fatal
    rc = p.returncode
    rs = [json.loads(l) for l in open(path(name, '.jsonl'))]
    if rc == 0:
        log(f'{name}: {sum(1 for _ in open(path(name, "_verdicts.jsonl")))}/{len(rs)} kept')
    elif rc == 3 or rc < 0:
        if len(rs) == 1:
            open(path(name, '_verdicts.jsonl'), 'w').close()
            with open(path(name, '_verdicts.jsonl.failed.jsonl'), 'w') as f: f.write(json.dumps(rs[0]) + '\n')
            log(f'{name}: single row killed, recorded as failed')
        else:
            h = len(rs) // 2
            write_chunk(name + 'a', rs[:h]); write_chunk(name + 'b', rs[h:])
            os.rename(path(name, '.jsonl'), path(name, '.split'))
            queue[0:0] = [name + 'a', name + 'b']
            log(f'{name}: killed (rc {rc}), split into {h} + {len(rs) - h}')
    else:
        fatal = True
        log(f'{name}: FATAL rc {rc}, see {name}.log; no new starts')


def status():
    ds = [n[:-len('_verdicts.jsonl.failed.jsonl')] for n in os.listdir(cdir) if n.endswith('.failed.jsonl')]
    kept = sum(sum(1 for _ in open(path(n, '_verdicts.jsonl'))) for n in ds)
    failed = sum(sum(1 for _ in open(path(n, '_verdicts.jsonl.failed.jsonl'))) for n in ds)
    with open(os.path.join(work, 'status.txt'), 'w') as f:
        f.write(f'{time.strftime("%H:%M:%S")}  elapsed {(time.time() - t0) / 60:.0f} min  mem avail {mem_avail()} MB  fatal {fatal}\n')
        f.write(f'chunks done {len(ds)}, queued {len(queue)}, running {len(running)}\nrows kept {kept}, failed {failed}\n')
        for n, (p, st) in running.items(): f.write(f'  running {n} for {(time.time() - st) / 60:.1f} min\n')


last = 0
while queue or running:
    for n, (p, st) in list(running.items()):
        if p.poll() is not None:
            del running[n]; finish(n, p)
    m = mem_avail()
    if m < PANIC and running:
        n = max(running, key=lambda k: running[k][1])
        log(f'mem avail {m} MB: killing newest lane {n}')
        os.killpg(running[n][0].pid, signal.SIGKILL); running[n][0].wait(); del running[n]
        queue.insert(0, n)
    elif not fatal and queue and len(running) < LANES and m >= MINFREE:
        n = queue.pop(0)
        p = subprocess.Popen([sys.executable, 'scripts/gen_dep.py', path(n, '.jsonl'), path(n, '.lean'),
                              path(n, '_verdicts.jsonl')], stdout=open(path(n, '.log'), 'w'), stderr=subprocess.STDOUT,
                             start_new_session=True)
        running[n] = (p, time.time()); log(f'{n}: started (mem avail {m} MB)')
        time.sleep(20)
    if time.time() - last > 20:
        status(); last = time.time()
    if fatal and not running: break
    time.sleep(5)
status(); log('driver finished' + (' (fatal)' if fatal else ''))
