# Workspace: iris-lean

Hypothesis analysis of `Iris` (library checkout set in `hc.env`; commit `8293092f`, toolchain `leanprover/lean4:v4.35.0`). 6,035 necessary / 195 removable / 5 independent / 25 unresolved of 6,260 hypotheses. Results in `Results.md`, method in
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
| `runs/` | Tooling the scripts read (`gen/` for the generated `refute_dep` tactic, `probe/Header*.lean` for hand files); new run outputs go here too |
| `tests/selftest.sh` | Pipeline self-test (one positive cluster, four negative controls); must print `SELFTEST OK` |

Proof file names in `checks/`: `Probe<k>Hand.lean` random-row agent probe; `W<w>c<c>Hand.lean` agent wave w, cluster
c; `T<w>c<c>Hand.lean` tail cluster (rows the waves left open, done by agents or the main session); `J<k>c0Hand.lean`
joint removal of pairs; `ChainProofs<k>.lean` transitive necessity; `RemTrans<k>…Hand.lean` transitive removability;
`UnusedHand.lean`/`InstDerivHand.lean` structural detectors.

## Running

Lean here is the library's own toolchain with `lake env`'s search path (`scripts/hclean`, cached in
`scripts/.leanpath`/`.leanbin`); tools run natively (`scripts/hcrun`).

```bash
tests/selftest.sh
scripts/hcrun hypcheck --module Iris --ns <Some.theorem>        # one theorem, JSON lines
HC_UNIT=hc-run scripts/run.sh N runs/x.jsonl --module Iris --level search --models M.txt
python3 scripts/merge_tool.py runs/x.jsonl TAG                 # merge proof_ok verdicts
scripts/flow.sh                                                # transitive necessity, twins, removable by transitivity
scripts/verify.sh C && scripts/accept.sh C                     # check, then merge a hand cluster
python3 scripts/status.py                                      # current numbers
python3 scripts/recheck.py                                     # recompile every stored proof file (LANES=N)
```

Models for `--models`: `scripts/models.txt` + `scripts/models_iris-lean.txt` (concatenate). Stop a run with `systemctl --user stop $HC_UNIT.scope`.
HypCheck options are listed in the header of `scripts/HypCheck.lean` (`--module`, `--ns`, `--redo ROWS`,
`--models FILE`, `--level fast|search|thorough`, `--goal both|removable`, `--only-private`, `--hb`, `--cex-time`).

## Pitfalls

- **Memory:** never start several Lean processes without a cap. `run.sh`, `lean.sh` and `measure.sh` run inside a
  systemd scope sized by available memory, min(60% RAM, available − 2.5 GB).
- Removable proofs must keep the theorem's universes (`drop%`, not `drop0%`).
- In hand files, put only theorem names in backticks in the comment above a declaration (`check_hand.py` reads them);
  private names are written `_private.M.0.x` in comments but with `«0»` in terms.
- Lean reports at most ~100 errors per compile; never edit a shell script while it runs.
- Iris declares `infix " || "` (disjointness) globally: in any Lean file importing `Iris`, write Boolean or as `or a b`, never `||`.
- Some refutations only work with type binders at `Type`: `drop0%`/`indep0%` put them at `Prop`, where the weakened statement can be true by proof irrelevance.
