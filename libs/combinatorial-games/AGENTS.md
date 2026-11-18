# Workspace: combinatorial-games

Hypothesis analysis of `CombinatorialGames` (library checkout set in `hc.env`; commit `e8c9538`, toolchain
`leanprover/lean4:v4.36.0-rc2`). 2,392 necessary / 146 removable / 0 independent / 59 unresolved of 2,597 hypotheses
(97.7% decided). Results in `Results.md`, method in `../../Methods.md` (what differs here: `Methods.md`), library
defects in `Findings.md`. Made with the tool in `../../tool/` (HypCheck v12.3); run every command from this directory
(the scripts refuse other working directories).

The library checkout is analysis-only: no source edits, no commits. Building it is fine. If it moves (pull, toolchain
bump), rebuild it, run `scripts/hclean --refresh` and `scripts/build_tools.sh`, and re-check before merging new runs.

The library uses the Lean module system: public rows run at olean level `server`, private rows at `private`, and the
agent header `runs/probe/Header.lean` is a module that imports `HCHeaderM` and `HCRefute` (sources in
`runs/hcimports/`, built into `tools/hcrepair/`).

## Layout

| Path | What it is |
|---|---|
| `hc.env` | Configuration read by all scripts: library dir, root import(s), modules in scope, memory slice name |
| `results/` | `public.jsonl`, `private.jsonl` and their `_removable`/`_independent`/`_unresolved` splits; `removable_review.md` and `unresolved_review.md` list them with reasons and obstructions |
| `checks/` | Hand and chain proof files; rows name their file in `tactic` |
| `proofs/tool/<run>/` | Proofs found by `HypCheck.lean` (rows: `proofs_file` + `proof`); private ones also as `bymod/` module files |
| `scripts/` | Tools, as run for this analysis (`scripts/recheck.py` is shared, in `../../kit/`) |
| `tools/` | Lake project that builds the scripts as native executables (`scripts/build_tools.sh`) |
| `runs/` | Sources the scripts and proofs read: `hcimports/` (header modules), `gen/` (the `refute_dep` generator core and this library's models), `probe/Header*.lean` (agent header, module and plain) |
| `tests/selftest.sh` | Pipeline self-test (one positive cluster, four negative controls); must print `SELFTEST OK` |

Proof file names in `checks/`: `Probe<k>Hand.lean` random-row agent probe; `W<w>c<c>Hand.lean` agent wave w, cluster
c; `T<w>c<c>Hand.lean` tail rounds (rows the waves left open); `G<k>c<n>Hand.lean` generated `refute_dep`
refutations; `ChainProofs<k>.lean` transitive necessity and twins.

## Running

Lean here is the library's own toolchain with `lake env`'s search path (`scripts/hclean`, cached in
`scripts/.leanpath`/`.leanbin`); tools run natively (`scripts/hcrun`). Header modules in `tools/hcrepair/` are found
through `HC_EXTRA_PATH=$PWD/tools/hcrepair`.

```bash
tests/selftest.sh
scripts/hcrun hypcheck --module CombinatorialGames --ns <Some.theorem> --olean-level server   # one theorem
HC_UNIT=hc-run scripts/run.sh N runs/x.jsonl --module CombinatorialGames --level search --olean-level server \
  --models scripts/models_combinatorial-games.txt --extra-tacs scripts/tactics_combinatorial-games.txt
python3 scripts/merge_tool.py runs/x.jsonl TAG                 # merge proof_ok verdicts
scripts/flow.sh                                                # transitive necessity, twins, removable by transitivity
scripts/verify.sh runs/waves/W1 C && scripts/accept.sh runs/waves/W1 C   # check, then merge a hand cluster
python3 scripts/status.py                                      # current numbers
python3 scripts/recheck.py                                     # recompile every stored proof file (LANES=N)
```

## Pitfalls

- **Memory:** never start several Lean processes without a cap, and run agents' own programs (Python searches)
  under `scripts/capped --mem 1500M` too. `run.sh`, `lean.sh` and `measure.sh` run inside a systemd scope sized by
  available memory, min(60% RAM, available − 2.5 GB). Private-level workers need ~2.2 GB each.
- Removable proofs must keep the theorem's universes (`drop%`, not `drop0%`). `Small.{u}` rows are trivially true
  at universe 0; state them at universe 1 (`dropU%` in `checks/W1c3Hand.lean`).
- `game_cmp` on products of games: prove each product once as its own lemma and combine in `Game` (see `Methods.md`).
- In hand files, put only theorem names in backticks in the comment above a declaration (`check_hand.py` reads them);
  private names are written `_private.M.0.x` in comments but with `«0»` in terms.
- Lean reports at most ~100 errors per compile; never edit a shell script while it runs.
