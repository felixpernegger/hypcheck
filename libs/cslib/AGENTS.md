# Workspace: CSLib

Hypothesis analysis of CSLib at commit `f8acdb37` (toolchain `leanprover/lean4:v4.36.0-rc2`, Mathlib from its
lakefile). **Fully decided:** 2,593 necessary / 105 removable / 1 independent of 2,699 hypotheses. Results in
`Results.md`, method in `../../Methods.md`. Set up by hand before the kit existed; run every command from this
directory.

The CSLib checkout (`CSLIB_DIR`, required) is analysis-only: no source edits, no commits.
Building it is fine (`lake exe cache get`, `lake build Cslib`, in a memory-capped scope with `LEAN_NUM_THREADS=4`).

## Layout

| Path | What it is |
|---|---|
| `results/` | `public.jsonl`, `private.jsonl` and their `_removable`/`_independent` splits (via `scripts/results_io.py`); `removable_review.md`, `removable_pairs.jsonl` |
| `checks/` | Hand proofs (`Probe*`, `W*`, `T*`, `F1c0`, `P1c0`, `M1c0`, `A1c0`), chain proofs (`ChainProofs<K>.lean`), joint removal (`J1c0Hand.lean`, which defines `drop2%`/`indep2%`) |
| `proofs/tool/full/{public,private}/` | Proofs found by `HypCheck.lean` (private ones per module under `bymod/`) |
| `scripts/` | Tools, see below |
| `tools/` | Lake project building the scripts as native executables (`cd tools && lake build`, in a capped scope) |

Proof file names in `checks/`: `Probe<k>Hand.lean` random-row agent probe; `W<w>c<c>Hand.lean` agent wave w, cluster
c; `T<w>c<c>Hand.lean` tail cluster (rows the waves left open, done by agents or the main session); `F1c0`, `P1c0`,
`M1c0`, `A1c0` the last deep rows (FLP, PAC learning, measurability, applicative; `Results.md`, "Necessary hypotheses
that took large constructions"); `J1c0Hand.lean` joint removal of pairs; `ChainProofs<k>.lean` transitive necessity.

## Tools

| Script | Use |
|---|---|
| `scripts/cslean` | CSLib's toolchain `lean` with `lake env`'s search path (cached in `scripts/.leanpath`; `--refresh` after `lake update`) |
| `python3 scripts/recheck.py` | Recompile every stored proof file (`checks/`, `proofs/tool/`, private ones per module; `LANES=N`); summary in `runs/recheck/summary.txt` |
| `scripts/csrun NAME ARGS` | Run a native tool from `tools/` (`hypcheck`, `propparams`, `unused`, …) |
| `scripts/run.sh N OUT.jsonl [options]` | Memory-capped multi-worker HypCheck run (`HC_UNIT=name` to stop it with `systemctl --user stop name.scope`) |
| `scripts/merge_tool.py OUT.jsonl TAG [--private]` | Merge a tool run (`proof_ok` verdicts that recompile) |
| `scripts/check_hand.py`, `scripts/merge_hand.py [--private]` | Verify a hand file (`HANDCHECK_AXIOMS=1`), then merge it |
| `scripts/check_pairs.py HAND PAIRS.jsonl` | Verify joint-removal proofs |
| `scripts/cand_rem.py`, `twins_cand.py`, `chain_proofs.py`, `merge_chain.py`, `rem_trans_cand.py` | Flow rounds (transitive necessity, twins, removable by transitivity) |
| `scripts/{Unused,UnusedTrans,UnusedEmit,InstDerivable,NecTrans,Twins}.lean`, `scripts/priv/` | Structural detectors (private-aware copies in `priv/`) |
| `scripts/lean.sh`, `scripts/measure.sh` | Memory-capped `cslean` (shared slice, `big.lock`); one-process memory and time measurement |

Models for `--models`: `scripts/models.txt` + `scripts/models_cslib.txt` (concatenate).

## Pitfalls

- Use the native tools, never `lean --run` for anything importing `Cslib` (1.6–1.9 GB vs. about 0.2 GB per process).
- Never start several Lean processes without a memory cap; stop runs by unit (`systemctl --user stop`), never by a
  `kill`/`pkill` pattern, which can match the calling shell.
- Term-elaborating tactics (`nofun`, `exact`, `aesop`) can recover from errors with a hidden `sorry`; only verdicts
  with `proof_ok: true` count, and every new tactic class needs a negative control.
- Removable proofs must keep the theorem's universes; in hand files, put only theorem names in backticks in the
  comment above a declaration; private names use `.0.` in comments and `«0»` in terms.
