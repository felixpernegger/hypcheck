"""Workspace configuration (hc.env) for the Python scripts. Scripts run from the workspace root."""
import os, sys

WS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _load():
    p = os.path.join(WS, 'hc.env')
    c = {}
    for line in open(p):
        line = line.strip()
        if line and not line.startswith('#'):
            k, v = line.split('=', 1)
            c[k] = v
    return c


C = _load()
NAME = C['HC_NAME']
LIBDIR = C['HC_LIBDIR']
ROOTS = [m for m in C['HC_ROOT'].split(',') if m]
MODULES = [m for m in C['HC_MODULES'].split(',') if m]
SLICE = C['HC_SLICE']
LEAN = os.path.join(WS, 'scripts', 'hclean')
CAPPED = os.path.join(WS, 'scripts', 'capped')
IMPORTS = '\n'.join(f'import {m}' for m in ROOTS)


def cap(mem=None, slice=True, timeout=None, default='3G'):
    """Command prefix that runs a command memory-capped (scripts/capped; MEM overrides the default). The backend is
    detected once per script and exported, so children inherit it and the no-cap warning appears once."""
    if 'HC_CAP' not in os.environ or os.environ['HC_CAP'] == 'auto':
        import subprocess
        os.environ['HC_CAP'] = subprocess.run([CAPPED, '--backend'], stdout=subprocess.PIPE, text=True,
                                              check=True).stdout.strip()
    p = [CAPPED, '--mem', mem or os.environ.get('MEM', default)]
    if slice: p += ['--slice', SLICE]
    if timeout: p += ['--timeout', str(timeout)]
    return p + ['--']


def mem_avail_mb():
    """Available memory in MB, or None where the platform does not say (scripts/capped --meminfo)."""
    import subprocess
    r = subprocess.run([CAPPED, '--meminfo'], stdout=subprocess.PIPE, text=True)
    return int(r.stdout.split()[1]) if r.returncode == 0 else None


def in_scope(module):
    return any(module == m or module.startswith(m + '.') for m in MODULES)


if os.path.abspath(os.getcwd()) != WS:
    sys.exit(f'run this from the workspace root {WS}')
