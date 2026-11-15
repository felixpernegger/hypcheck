# Finding unneeded hypotheses in @NAME@

Goal: for every Prop-valued parameter of every theorem in `@MODULES@` (library `@LIBDIR@`), decide whether it is **removable** (prove `T'` = `T` without it), **necessary** (prove `¬T'`), or **independent**, else leave it **unresolved** with a reason. Every removable/necessary verdict is a stored, kernel-checked Lean proof. Workspace created @DATE@ with the hypcheck tool (`@KITDIR@`, commit `@KIT@`); toolchain `@TOOLCHAIN@`.

**Current state:** not started (update this line after every phase).

**Read next:** `Plan.md` (phases and Log: where we are), then `@KITDIR@/PLAYBOOK.md` (the method, gates, measured rates, pitfalls). `Methods.md` records only what differs for this library; `Results.md` holds results; `Findings.md` holds library defects worth reporting upstream. Keep this file to goal, constraints, layout and running.

## Hard constraints

- The library checkout `@LIBDIR@` is **analysis-only**: no source edits, never commit (the user handles git). The one exception is the optional pointer block in `@LIBDIR@/CLAUDE.local.md` (git-ignored via `.git/info/exclude`), written by `@KITDIR@/link_repo.sh @WS@`, which sends Claude sessions opened in the library here. Building it is fine. If it moves (pull, toolchain bump), rebuild, `scripts/hclean --refresh`, rebuild the tools, and re-check before merging new runs.
- The published workspaces under `@KITDIR@/../libs/` (finished analyses, useful as references) and the tool are read-only from here; copy what you need.
- **Memory:** parallel Lean runs can exhaust memory and freeze the machine. Every multi-process Lean run goes inside a memory-capped systemd scope sized by *available* memory, `min(60% RAM, MemAvailable − 2.5 GB)` (`scripts/run.sh`, `scripts/lean.sh`, `scripts/measure.sh` do this, all through `scripts/capped`). Where `scripts/capped --backend` prints `none` (no systemd user session) there is no cap: use fewer parallel workers and agents, sized from a measured process. Measure one process before any new kind of run.
- Every subagent is spawned with `model: "opus"`, at most 6 at a time.
- **Ask the user before** every agent wave, every full-library tool run, and any change to `scripts/HypCheck.lean` beyond tactics/models (keep a copy `runs/HypCheck_<version>.lean` first).

## Process rules

1. **Measure before claiming.** Plans and estimates list their assumptions and test the uncertain ones; report measured numbers with source and range, and say which are unmeasured. A user-set minimum effort is a hard lower bound.
2. **Before any long run:** pilot → classify every failure → fix classes ≥ 5% (≤ 2 re-pilots) → cost-model ETA told to the user → stop rule (a pass below ~20 verdicts per lane-hour for 30 min stops; strata below ~10% pilot yield go to agents).
3. **Memory-gated parallel lanes** with split/requeue of killed chunks; single Lean compiles ≤ ~50 short theorems / ≤ ~15 min.
4. **Actively monitor long runs:** alert on cap kills, exit, and a status file that stops changing (~20 min). Bracketed process patterns (`grep '[h]ypcheck'`) or `kill -0 PID`; never `pkill -f` a pattern in your own command line.
5. **Re-evaluate the plan after every step:** rates, shares, costs, surprises vs. assumptions; Log entry in `Plan.md` before continuing.
6. **Agents never merge.** The main session re-runs `scripts/verify.sh` and merges only on `VERIFY PASS` (`scripts/accept.sh` does both, then flow).

## Layout

| Path | What it is |
|---|---|
| `hc.env` | Workspace config: library dir, root import(s), modules in scope, slice name (read by all scripts) |
| `AGENTS.md` (`CLAUDE.md` points here), `Plan.md`, `Methods.md`, `Results.md`, `Findings.md` | This file; roadmap + Log; library-specific methods; results; upstream-worthy defects |
| `scripts/HypCheck.lean` and the other `scripts/*.lean` tools | Tool sources; built as native executables in `tools/` by `scripts/build_tools.sh` (rebuild after editing) |
| `scripts/hclean`, `scripts/hcrun`, `scripts/lean.sh`, `scripts/measure.sh` | Library `lean` with `lake env` search path; run a native tool; memory-capped Lean for agents and checks (shared slice, `big.lock`); one-process memory/time measurement |
| `scripts/capped` | Memory cap, lock and time limit for every Lean process (systemd scope, or no cap without systemd; `HC_CAP`) |
| `scripts/run.sh` | All multi-worker HypCheck runs (capped scope, restart on kill, stored proofs recompiled) |
| `scripts/inventory.sh`, `make_rows.py`, `inventory.py` | P1: rows and report in `runs/inventory/` |
| `scripts/struct.sh`, `struct_proofs.sh` | P2: detectors + edges in `runs/struct/`; proofs `checks/{Unused,InstDeriv}Hand.lean` |
| `runs/gen/RefuteCore.lean`, `runs/gen/Models.lean`, `scripts/gen_dep.py`, `gen_drive.py`, `gen_accept.py` | P3b: `refute_dep` for dependent rows (generic core; this library's models and registrations in `Models.lean`); chunked memory-gated driver; check + merge |
| `scripts/sample_rows.py`, `pilot_summary.py`, `merge_tool.py` | P3/P4 pilot sample, summary, merge of tool runs (`proof_ok` only) |
| `scripts/HCRepair.lean`, `repair_proofs.py` | Proof repair: the module shared by HypCheck and the stored proofs `checks/Repair<K>Hand.lean` (`hc_repair% T i`); `repair_proofs.py K OUT.jsonl` stores, checks and merges the `tactic: repair` verdicts of a run |
| `scripts/hand_modules.py` | Optional after agent waves: hand files as modules (`runs/reuse/mods`) for a search-level rerun that reuses the agents' helper lemmas |
| `scripts/flow.sh` (+ `cand_rem.py`, `twins_cand.py`, `chain_proofs.py`, `merge_chain.py`, `rem_trans.py`) | P5 flow: necessary/twins (`checks/ChainProofs<K>.lean`) and removable by transitivity (`checks/RemTrans<K>g<n>Hand.lean`; keep `runs/remtrans/mods/`, the reused proof files compiled as modules) |
| `scripts/cut_clusters.py`, `verify.sh`, `accept.sh` | P6: cut / freeze / emit clusters; check one cluster (VERIFY PASS/FAIL); accept = verify → merge → flow |
| `scripts/check_hand.py`, `check_pairs.py`, `merge_hand.py`, `results_io.py`, `status.py` | Hand-file checker, pair checker, merge, result IO, dashboard (`--save` snapshots) |
| `scripts/models.txt`, `models_examples_cslib.txt` | Counterexample models (`TYPE := TERM`); add `scripts/models_@NAME@.txt` for this library and concatenate for `--models` |
| `runs/probe/Header.lean` | Agent toolkit header (`drop%`, `indep%`, `drop0%`, `indep0%`, private names); agents copy it unchanged |
| `runs/probe/BRIEF.md`, `runs/waves/{BRIEF,RUNBOOK,NOTES,TAILS}.md` | Probe brief; wave brief, main-session runbook, shared helpers, gave-up rows |
| `results/{public,private}.jsonl` (+ `_removable`, `_unresolved`, `_independent` splits) | **Merged verdicts.** Write only via `merge_tool.py`, `merge_hand.py`, `merge_chain.py`; backups next to each run |
| `checks/` | Every stored proof file that backs a merged verdict |
| `tests/selftest.sh` | Pipeline self-test (positive cluster + 4 negative controls) |

## Running

Lean here is the library's toolchain run with `lake env`'s search path (`scripts/hclean`); tools run natively (`scripts/hcrun`).

```bash
cd @WS@
tests/selftest.sh                                             # must print SELFTEST OK
scripts/hcrun hypcheck --module @ROOT@ --ns <Some.theorem>     # smoke test (prints JSON lines)
scripts/inventory.sh                                          # P1
scripts/struct.sh && scripts/struct_proofs.sh                 # P2
python3 scripts/sample_rows.py 100 <seed> runs/pilot/rows100.jsonl
HC_UNIT=hc-pilot scripts/run.sh 3 runs/pilot/v.jsonl --module @ROOT@ --redo runs/pilot/rows100.jsonl --level search --models scripts/models.txt
python3 scripts/pilot_summary.py runs/pilot/v.jsonl runs/pilot/v.log
HC_UNIT=hc-full scripts/run.sh N runs/full/pub.jsonl --module @ROOT@ --level search --models M.txt   # P4 (ask first)
python3 scripts/merge_tool.py runs/full/pub.jsonl v12             # merges proof_ok verdicts
python3 scripts/repair_proofs.py 1 runs/full/pub.jsonl           # proof-repair verdicts: store, check, merge
scripts/flow.sh                                               # P5, and after every merge
python3 scripts/status.py --save
```

Stop a `run.sh` run with `systemctl --user stop $HC_UNIT.scope` (without systemd: Ctrl-C or `kill -- -<pid>`). HypCheck options: `scripts/HypCheck.lean` header (`--module`, `--ns`, `--redo ROWS`, `--models FILE`, `--level fast|search|thorough`, `--goal both|removable`, `--only-private`, `--hb`, `--cex-time`, …).

## Pitfalls

See `@KITDIR@/PLAYBOOK.md` §5. The ones that bite first: removable proofs must keep universes (`drop%`, not `drop0%`); only theorem names in backticks above verdicts; private names `_private.M.0.x` in comments but `«0»` in terms; Lean reports at most ~100 errors per compile; never edit a running shell script.
