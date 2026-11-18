# Finding unneeded hypotheses in Lean libraries

Goal: for every Prop-valued hypothesis of every theorem in a library, decide whether it is **removable** (the theorem
stays true without it: proof of `T'`), **necessary** (proof of `¬T'`) or **independent**, and store a kernel-checked
Lean proof for every verdict.

## Analysing a library

When the user asks for the hypothesis analysis of a library (e.g. "Do the hypothesis analysis for X with hypcheck"),
follow `tool/NEW_LIBRARY.md`. In short: build the library, run `tool/hypcheck` (the mechanical checks) in
`workspaces/<name>/`, report `report.md`, and **ask the user** before long runs and before starting any AI agents on
what remains. Never edit or commit in the analysed library. Everything under `libs/` is the published results and
stays read-only.

## Layout

| Path | What it is |
|---|---|
| `README.md`, `Methods.md` | Public overview with all results; the method (verdicts, how they are found, stored proofs, checks, caveats) |
| `tool/` | The tool: `hypcheck` (mechanical run), `NEW_LIBRARY.md` (procedure for agents), `PLAYBOOK.md` (method and measured rates), `template/` (copied into each new workspace), `AGENTS.md` (changing the tool). `template/scripts/capped` is the only platform-specific file (`tool/README.md` "Platforms") |
| `workspaces/` | New analyses (`tool/hypcheck`, `tool/new_target.sh`); git-ignored |
| `libs/core/` | **The Lean 4 core library (Init, Std, Lean, Lake, private theorems).** Its `AGENTS.md` (layout, running, pitfalls), `Results.md`, `Findings.md`, and `results/`, `checks/`, `proofs/`, `certs/`, `scripts/`, `seeds/`. Run its scripts from `libs/core` |
| `libs/batteries/`, `libs/cslib/` | Batteries and CSLib, set up by hand before the tool existed |
| `libs/iris-lean/`, `libs/mathlib-data/`, `libs/mathlib-logic-basic/`, `libs/sampcert/` | Made with earlier versions of the tool; each has its own `AGENTS.md` |
| `libs/combinatorial-games/` | Made with the current tool (v12.3, module system); its own `AGENTS.md` |
| `scripts/verify_rows.py` | Fast check (seconds) that every decided row of every workspace points to an existing proof; run it after moving or deleting files |
| `kit/` | Tool files shared by several published workspaces, in the versions they were run with; the workspaces hold relative symlinks to them (`kit/README.md`) |

**Every published workspace has the same shape:** `results/` (`public.jsonl`, `private.jsonl` and their
`_removable`/`_independent` splits; core: `init_all.jsonl`, `std.jsonl`, `lean_lake.jsonl`,
`internal_names_and_lake_unimported.jsonl`, `private/private_all.jsonl`), `checks/` (hand, chain and unused proofs),
`proofs/tool/<run>/` (proofs found by the tool), `scripts/`. A row points to its proof through `proofs_file` or a `checks/…` path in `tactic`, relative to its
workspace.
