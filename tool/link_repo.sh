#!/bin/bash
# Point Claude sessions opened in the analysed repo to its hypcheck workspace.
# Usage: link_repo.sh WORKSPACE        (optional; new_target.sh calls it with POINTER=1)
# Writes a marked block into <repo>/CLAUDE.local.md (Claude Code loads it like CLAUDE.md; personal, never committed)
# and lists that file in <repo>/.git/info/exclude so git ignores it locally. Re-running replaces the block.
# These are the only writes into the repo; remove the block (or the file) to undo.
set -euo pipefail
WS=$(cd "$1" && pwd)
source "$WS/hc.env"
KIT=$(cd "$(dirname "$0")" && pwd)
F="$HC_LIBDIR/CLAUDE.local.md"
BEGIN="<!-- hypcheck:$HC_NAME begin (written by $KIT/link_repo.sh) -->"
END="<!-- hypcheck:$HC_NAME end -->"
block="$BEGIN
## Unneeded-hypotheses analysis ($HC_NAME)

This repo is being analysed for unneeded hypotheses (scope: \`$HC_MODULES\`). The work lives outside the repo, in the workspace \`$WS\`:
- Read \`$WS/AGENTS.md\` first, then \`$WS/Plan.md\`: its Log at the end says where the analysis stands. \"Execute the plan\" means continue from there.
- Run every workspace command from \`$WS\` (the scripts refuse other working directories).
- For that work this repo is read-only: no source edits, no commits; building it is fine. This block and the exclude entry are the only files it writes here.
- Method, phases and pitfalls: \`$KIT/PLAYBOOK.md\`.
$END"
python3 - "$F" "$BEGIN" "$END" "$block" <<'PY'
import os, re, sys
f, begin, end, block = sys.argv[1:]
s = open(f).read() if os.path.exists(f) else ''
name = begin.split()[1]  # hypcheck:<name>
pat = re.compile(re.escape(f'<!-- {name} begin') + r'.*?' + re.escape(end), re.S)
s = pat.sub(lambda _: block, s) if pat.search(s) else (s.rstrip('\n') + '\n\n' if s.strip() else '') + block + '\n'
open(f, 'w').write(s)
PY
if git -C "$HC_LIBDIR" rev-parse --git-dir >/dev/null 2>&1; then
  ex="$(git -C "$HC_LIBDIR" rev-parse --absolute-git-dir)/info/exclude"
  mkdir -p "$(dirname "$ex")"; touch "$ex"
  pat="/$(git -C "$HC_LIBDIR" rev-parse --show-prefix)CLAUDE.local.md"  # Lake project may be a subfolder (iris-lean: Iris/)
  grep -qxF "$pat" "$ex" || echo "$pat" >> "$ex"
  if git -C "$HC_LIBDIR" ls-files --error-unmatch CLAUDE.local.md >/dev/null 2>&1; then
    echo "note: CLAUDE.local.md is tracked in this repo, so the exclude has no effect; don't commit the block" >&2
  fi
fi
echo "pointer -> $F"
