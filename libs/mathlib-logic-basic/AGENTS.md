# Workspace: Mathlib.Logic and Mathlib.Basic

Hypothesis analysis of `Mathlib.Logic,Mathlib.Basic` (library checkout set in `hc.env`; Mathlib commit `bbff2954fe5` (same checkout as `../mathlib-data`), toolchain `leanprover/lean4:v4.36.0-rc2`). 2,685 necessary / 49 removable / 0 independent / 0 unresolved of 2,734 hypotheses (fully decided). Results in `Results.md`, method in
`../../Methods.md`, library defects in `Findings.md`. Made with an earlier version of the tool in `../../tool/`; run every command from this
directory (the scripts refuse other working directories).

The library checkout is analysis-only: no source edits, no commits. Building it is fine. If it moves (pull, toolchain
bump), rebuild it, run `scripts/hclean --refresh` and `scripts/build_tools.sh`, and re-check before merging new runs.

## Layout

| Path | What it is |
|---|---|
| `hc.env` | Configuration read by all scripts: library dir, root import(s), modules in scope, memory slice name |
| `results/` | `public.jsonl`, `private.jsonl` and their `_removable`/`_independent`/`_unresolved` splits; written only by `merge_tool.py`, `merge_hand.py`, `merge_chain.py` (via `results_io.py`) |
| `checks/` | Hand, chain, repair and structural proof files; rows name their file in `tactic` |
| `proofs/tool/<run>/` | Proofs found by `HypCheck.lean` (rows: `proofs_file` + `proof`) |
| `scripts/` | Tools (many are symlinks into `../../kit/`, shared with the other kit workspaces) |
| `tools/` | Lake project that builds the scripts as native executables (`scripts/build_tools.sh`) |
| `runs/` | Tooling the scripts read (`gen/` for the generated `refute_dep` tactic, `probe/Header*.lean` for hand files, `hcimports/` for the slim import module); new run outputs go here too |
| `tests/selftest.sh` | Pipeline self-test (one positive cluster, four negative controls); must print `SELFTEST OK` |

Proof file names in `checks/`: `W<w>c<c>Hand.lean` agent wave w, cluster c; `T<w>c<c>Hand.lean` tail cluster (rows the
waves left open, done by agents or the main session); `ChainProofs<k>.lean` transitive necessity.

## Running

Lean here is the library's own toolchain with `lake env`'s search path (`scripts/hclean`, cached in
`scripts/.leanpath`/`.leanbin`); tools run natively (`scripts/hcrun`).

```bash
tests/selftest.sh
scripts/hcrun hypcheck --import HCImportsM --module Mathlib.Logic --module Mathlib.Basic --ns <Some.theorem>        # one theorem, JSON lines
HC_UNIT=hc-run scripts/run.sh N runs/x.jsonl --import HCImportsM --module Mathlib.Logic --module Mathlib.Basic --level search --models M.txt
python3 scripts/merge_tool.py runs/x.jsonl TAG                 # merge proof_ok verdicts
python3 scripts/repair_proofs.py K runs/x.jsonl                # proof-repair verdicts: store, check, merge
scripts/flow.sh                                                # transitive necessity, twins, removable by transitivity
scripts/verify.sh C && scripts/accept.sh C                     # check, then merge a hand cluster
python3 scripts/status.py                                      # current numbers
python3 scripts/recheck.py                                     # recompile every stored proof file (LANES=N)
```

Models for `--models`: `scripts/models.txt` + `scripts/models_mathlib-data.txt` + `scripts/models_mathlib-logic-basic.txt` (concatenate). Stop a run with `systemctl --user stop $HC_UNIT.scope`.
HypCheck options are listed in the header of `scripts/HypCheck.lean` (`--module`, `--ns`, `--redo ROWS`,
`--models FILE`, `--level fast|search|thorough`, `--goal both|removable`, `--only-private`, `--hb`, `--cex-time`).

## Pitfalls

- **Memory:** never start several Lean processes without a cap. `run.sh`, `lean.sh` and `measure.sh` run inside a
  systemd scope sized by available memory, min(60% RAM, available − 2.5 GB).
- Removable proofs must keep the theorem's universes (`drop%`, not `drop0%`).
- In hand files, put only theorem names in backticks in the comment above a declaration (`check_hand.py` reads them);
  private names are written `_private.M.0.x` in comments but with `«0»` in terms.
- Lean reports at most ~100 errors per compile; never edit a shell script while it runs.
- Slim imports as in `../mathlib-data` (`HCImportsM` = its import set plus the 9 Logic/Basic modules it misses); `scripts/inventory.sh` also imports `Mathlib.Logic.Hydra` so that PropParams scans `Mathlib.*` modules.
