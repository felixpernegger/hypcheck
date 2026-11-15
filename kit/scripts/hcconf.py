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
LIBDIR = os.path.expanduser(C['HC_LIBDIR'])
ROOTS = [m for m in C['HC_ROOT'].split(',') if m]
MODULES = [m for m in C['HC_MODULES'].split(',') if m]
SLICE = C['HC_SLICE']
LEAN = os.path.join(WS, 'scripts', 'hclean')
IMPORTS = '\n'.join(f'import {m}' for m in ROOTS)


def in_scope(module):
    return any(module == m or module.startswith(m + '.') for m in MODULES)


if os.path.abspath(os.getcwd()) != WS:
    sys.exit(f'run this from the workspace root {WS}')
