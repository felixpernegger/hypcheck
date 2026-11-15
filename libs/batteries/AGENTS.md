# Workspace: Batteries

Hypothesis analysis of Batteries at commit `4af7237` (`main`, toolchain `leanprover/lean4:v4.36.0-rc2`). **Fully
decided:** 1,259 necessary / 66 removable / 1 independent of 1,326 hypotheses. Results and the full removable list in
`Results.md`, method in `../../Methods.md`, issues in `Findings.md`. Set up by hand before the kit existed; run every
command from this directory.

The Batteries checkout (`BATTERIES_DIR`, required) is analysis-only here. The stored
proofs refer to the original statements at `4af7237`: check out and build that commit before re-checking them.
`removals.patch` applies all 66 removals to `4af7237`.

## Layout

| Path | What it is |
|---|---|
| `results/` | `public.jsonl`, `private.jsonl` and their `_removable`/`_independent` splits (written by `scripts/results_io.py`) |
| `checks/` | Hand proofs (`{Heap,Ordered,Control,Rest}Hand.lean`), `InstDerivBat.lean`, `IndepFixHand.lean`, `JointHand.lean` |
| `proofs/tool/full/{public,private}/` | Proofs found by `HypCheck.lean` (private ones per module under `bymod/`) |
| `scripts/` | Tools, see below |
| `tools/` | Lake project that builds `HypCheck.lean` and the detectors as native executables (`lake build` there) |
| `removals.patch` | The 66 removals as one diff against `4af7237` (17 files, +440/−198) |
| `runs/waves/Header.lean` | Hand-file header (`drop%`, `indep%`, `drop0%`, `indep0%`, `priv%`) |

## Tools

| Script | Use |
|---|---|
| `scripts/blean` | The pinned toolchain's `lean` with Batteries' build on `LEAN_PATH` (never the lean4 checkout) |
| `python3 scripts/recheck.py` | Recompile every stored proof file (`checks/`, `proofs/tool/`, private ones per module; `LANES=N`); summary in `runs/recheck/summary.txt` |
| `scripts/hc`, `scripts/hx NAME` | Run the native `hypcheck` or another native tool from `tools/` |
| `scripts/run.sh N OUT.jsonl [options]` | Memory-capped multi-worker HypCheck run (workers use `scripts/hc`); proofs in `OUT.proofs/` |
| `scripts/build_results.py` | Build `results/` from the inventory and the tool runs (only `proof_ok` verdicts) |
| `scripts/check_hand.py HAND.lean VERDICTS.jsonl` | Verify a hand file (`HANDCHECK_AXIOMS=1`; `HANDCHECK_MODULE=M` for private theorems) |
| `scripts/merge_hand.py [--priv]`, `scripts/merge_wave.sh W C` | Merge checked verdicts (the wave script splits public and private) |
| `scripts/Unused.lean`, `UnusedTrans.lean`, `InstDerivable.lean`, `NecTrans.lean`, `Twins.lean`, `cand_rem.py`, `chain_proofs.py`, `merge_chain.py` | Structural detectors and flow |
| `scripts/Scope.lean`, `Scope2.lean` | Coverage check of the inventory |
| `scripts/lean.sh` | `blean` in a memory-capped scope (shared slice, `big.lock` for full-file compiles) |

## Pitfalls

- `lean --run HypCheck.lean` with a Batteries import needs more than 1.3 GB per process: use the native tools.
- Never start several Lean processes without a memory cap (`run.sh`, `lean.sh` do this).
- Some refutations need universe 1 (`drop1%`/`indep1%`): at universe 0 every `Sort` is `Prop`.
