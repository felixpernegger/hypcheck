#!/bin/bash
# Create a hypcheck workspace for a Lean library (a built Lake project).
# Usage: new_target.sh NAME LIBDIR ROOT [MODULES] [WORKSPACE]
#   NAME       short name, e.g. foundation (workspace workspaces/NAME of this repository, slice hc-NAME.slice)
#   LIBDIR     Lake project root of the library, already built (`lake build` / `lake exe cache get`)
#   ROOT       root module(s) to import, comma-separated, e.g. Foundation or Mathlib
#   MODULES    module prefixes in scope, comma-separated (default: ROOT), e.g. Mathlib.Order
#   WORKSPACE  default: workspaces/NAME next to this tool/ directory
# Env: BUILD=0 skips building the native tools; POINTER=1 also writes a pointer into <LIBDIR>/CLAUDE.local.md
# (link_repo.sh: tells Claude sessions opened in the repo where the workspace is; git-ignored via .git/info/exclude).
# Without POINTER=1 nothing is written into the library.
set -euo pipefail
[[ $# -ge 3 ]] || { sed -n 2,11p "$0"; exit 1; }
KIT=$(cd "$(dirname "$0")" && pwd)
NAME=$1; LIBDIR=$(cd "$2" && pwd); ROOT=$3; MODULES=${4:-$3}; WS=${5:-$(cd "$(dirname "$0")/.." && pwd)/workspaces/$NAME}
[[ -e "$WS" ]] && { echo "$WS exists; refusing to overwrite" >&2; exit 1; }
[[ -f "$LIBDIR/lean-toolchain" ]] || { echo "$LIBDIR has no lean-toolchain (not a Lake project?)" >&2; exit 1; }
for m in ${ROOT//,/ }; do
  f="$LIBDIR/.lake/build/lib/lean/${m//.//}.olean"
  [[ -f "$f" ]] || f=$(find "$LIBDIR/.lake/packages" -path "*/.lake/build/lib/lean/${m//.//}.olean" 2>/dev/null | head -1)
  [[ -n "$f" && -f "$f" ]] || { echo "no olean for $m: build the library first (lake build $m)" >&2; exit 1; }
done
KITREV=$(git -C "$KIT" rev-parse --short HEAD 2>/dev/null || echo unversioned)
mkdir -p "$(dirname "$WS")"
cp -r "$KIT/template" "$WS"
export NAME LIBDIR ROOT MODULES WS KITREV KIT
python3 - <<'PY'
import os, pathlib, datetime
e = os.environ
imports = '\n'.join(f'import {m}' for m in e['ROOT'].split(','))
sub = {'@NAME@': e['NAME'], '@LIBDIR@': e['LIBDIR'], '@ROOT@': e['ROOT'], '@MODULES@': e['MODULES'], '@WS@': e['WS'],
       '@KIT@': e['KITREV'], '@KITDIR@': e['KIT'], '@DATE@': datetime.date.today().isoformat(),
       '@SLICE@': 'hc-' + e['NAME'] + '.slice',
       '@TOOLCHAIN@': open(os.path.join(e['LIBDIR'], 'lean-toolchain')).read().strip(), '@IMPORTS@': imports}
ws = pathlib.Path(e['WS'])
(ws / 'hc.env.in').rename(ws / 'hc.env')
for p in ws.rglob('*'):
    top = p.relative_to(ws).parts[0]
    if p.is_file() and top not in ('scripts', 'tools') and p.suffix in ('.md', '.env', '.lean'):
        try: s = p.read_text()
        except UnicodeDecodeError: continue
        t = s
        for k, v in sub.items(): t = t.replace(k, v)
        if t != s: p.write_text(t)
PY
"$WS/scripts/hclean" --refresh > /dev/null
echo "workspace $WS for $NAME ($(cat "$LIBDIR/lean-toolchain")), tool $KITREV"
echo "lean: $(cat "$WS/scripts/.leanbin")"
if [[ "${BUILD:-1}" == 1 ]]; then
  (cd "$WS" && scripts/build_tools.sh) && echo "native tools built: $(ls "$WS/tools/.lake/build/bin" | tr '\n' ' ')"
fi
if [[ "${POINTER:-0}" == 1 ]]; then "$KIT/link_repo.sh" "$WS"; fi
echo "next: cd $WS && tests/selftest.sh; then tool/hypcheck for the mechanical run, AGENTS.md and Plan.md for the agent stage"
