# The hypcheck tool

This directory is the tool, not a workspace. Workspaces are created by `hypcheck` (the mechanical run; it calls `new_target.sh`) and live in `../workspaces/<name>` (git-ignored). To analyse a library, follow `NEW_LIBRARY.md`; the analysis happens in the workspace (read its `AGENTS.md`). Read `README.md` and `PLAYBOOK.md` first. This file is about changing the tool.

## Changing the tool

- `template/` is copied verbatim into new workspaces; `@NAME@`-style placeholders are filled in `.md`/`.lean`/`hc.env` files outside `template/scripts/` and `template/tools/` (`new_target.sh` lists them). Scripts read `hc.env` at run time instead (`scripts/hcconf.py` for Python, `source hc.env` for shell).
- Lean code that is compiled *together with the library* (agent header, `check_hand.py`'s checker, `derive_proofs.py`/`unused_proofs.py`/`chain_proofs.py` headers) must not use syntax a library might shadow: no `xs[i]!` (Foundation declares a `]!` token; use `xs.getD i default`), no `a || b` (Iris declares `infix:60 " || "` for disjointness, so `n > 1 || b` parses as `n > (1 || b)`; use `or a b`). This includes `runs/gen/RefuteCore.lean` and `check_pairs.py`.
- The tools in `template/scripts/*.lean` import only `Lean`; Mathlib/Aesop tactics are parsed at run time (`parsedTacs` in `HypCheck.lean`), so the same source builds against any toolchain the library uses.
- Improvements made in a workspace that are not library-specific get folded back here.
- Platform: start every Lean process through `scripts/capped` (memory cap, `--lock`, `--timeout`; `hcconf.cap()` in Python), never `systemd-run`, `flock`, `timeout` or `/proc/meminfo` directly, so the tool keeps running without systemd (README "Platforms"). Keep shell scripts bash-3.2-compatible (macOS) and free of GNU-only flags (`sed -i`, `stat -c`, `date +%N` outside the systemd branch).

## Testing a change (required before committing)

1. Disk: each native tool build takes 2.9 GB (13 static executables). If no `template/scripts/*.lean` tool changed, use `BUILD=0` (selftest, checkers and snippets need only the library's `lean`). Create throwaway workspaces in a scratch directory, e.g. `BUILD=1 ./new_target.sh foundation <Foundation checkout> Foundation Foundation <scratch>/hc-foundation` (an older toolchain and library notation that clashes) and the same for CSLib (`Cslib`; tools can be copied between workspaces with the same toolchain).
2. In each: `tests/selftest.sh` must print `SELFTEST OK`.
3. For changes to `scripts/capped` or the scripts that call it, repeat the self-test and a small `run.sh` without systemd: a `PATH` directory that links everything in `/usr/bin` except `systemd-run`, `flock` and `timeout`, plus elan's `bin` directory.
4. Exercise what you changed (e.g. `scripts/inventory.sh`, `scripts/struct.sh && scripts/struct_proofs.sh`, a 100-row pilot with `run.sh`, `flow.sh`, `cut_clusters.py plan/freeze/next`, `accept.sh` on `runs/selftest SelfTestPos`).
5. Regression for the checker: `template/scripts/check_hand.py` on `../libs/cslib/checks/W1c4Hand.lean`, with as verdicts the rows of `../libs/cslib/results/*.jsonl` whose `tactic` names that file, gives (with `HANDCHECK_AXIOMS=1`, CSLib checkout at `98f9a62a`) `lean errors: 0; verdicts checked: 126; not covered: 0` and `axioms: 184 standard, 0 other, 0 missing`. Run it on a copy in the scratch directory: the checker writes `<file>.map.jsonl` next to its input, and `../libs/` stays untouched.

Every multi-process Lean run goes in a memory-capped scope (see `PLAYBOOK.md` §5). Never write into the published workspaces under `../libs/` or into the analysed libraries.
