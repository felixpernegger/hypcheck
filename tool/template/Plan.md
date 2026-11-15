# Roadmap: unneeded hypotheses in @NAME@

Living document (started @DATE@), the per-library instance of `@KITDIR@/PLAYBOOK.md` §2. Re-plan after every step; each phase has a pilot gate. Results go to `Results.md`, library-specific techniques to `Methods.md`; this file keeps the plan, the decisions and the Log.

## 0. How to execute

You are the main session: you run the tools, brief and check subagents, and merge. Work in `@WS@`; read `AGENTS.md` first.
1. Find where you are in the Log below. The first phase without a "done" entry is next.
2. Per phase: pilot first, classify every failure, write measured yield, cost-model ETA and gate decision into the Log **before** scaling.
3. **Ask the user** before every agent wave, every full-library tool run, and any change to `scripts/HypCheck.lean` beyond tactics/models.
4. Subagents: `model: "opus"`, at most 6, Lean only through `scripts/lean.sh`; agents never merge.
5. Merging: tool runs `scripts/merge_tool.py` (then `scripts/repair_proofs.py K OUT` for proof-repair verdicts); agent clusters `scripts/accept.sh DIR C`; generated proof files `check_hand.py` (0 errors / 0 not covered / standard axioms) then `merge_hand.py`.
6. Stop and report to the user at the end of each phase.

## Phases (checklist)

The mechanical stage, `tool/hypcheck` (the usual way this workspace is made), already did P0, P1, P2, P4 and P5 at `--level search` (P4 on private theorems only with `--private`; it picks up `scripts/models_@NAME@.txt` when present): `report.md` and `runs/mech/` (a `.done` marker and a log per step) show what ran. Record its counts in the Log, then continue with P3b or P6a; a P3 pilot and a P4 rerun are worth it only after adding library models (to rerun through `tool/hypcheck`, delete the `tool-*`, `merge-*` and `repair-*` markers in `runs/mech/`).

- **P0 Setup:** `tests/selftest.sh` → SELFTEST OK; smoke test one theorem; one-worker measurement (`MEM=3G scripts/measure.sh runs/smoke/m -- scripts/hcrun hypcheck --module @ROOT@ --ns …`). Record toolchain, library commit, memory per worker.
- **P1 Inventory:** `scripts/inventory.sh`; Log rows (public/private), dependent and instance shares, top folders, rows with value generators. **Scope decision** (PLAYBOOK §2 P1, §6): all rows, or which `HC_MODULES`; agent-cost estimate (PLAYBOOK §4) told to the user.
- **P2 Structural:** `scripts/struct.sh`, `scripts/struct_proofs.sh`; Log counts (unused, transitive, instance-derivable, twins, usable edges).
- **P3 Tool pilot:** 100 random rows; failure taxonomy; models file `scripts/models_@NAME@.txt` for the biggest "missing value" classes; ≤ 2 re-pilots. **STOP: report to the user** (yield, taxonomy, cost model for P4, proposed next steps).
- **P3b Generator for dependent rows** (if the dependent share is large; PLAYBOOK §2 P3b): models for the big hypothesis shapes in `runs/gen/Models.lean`; 50-row pilot with `gen_drive.py`; failure taxonomy; cost model; scale with the user's go; `gen_accept.py`, flow.
- **P4 Full tool run** (user's go): public, then private; merge `proof_ok` verdicts.
- **P5 Flow:** `scripts/flow.sh` until 0.
- **P6a Agent probe** (user's go): 2 agents × 50 random open rows, `runs/probe/BRIEF.md`; gate ≥ 90% decided; metrics: decided, removable share, agent-min/row, tokens/row, slice peak. Reusable helpers → `runs/waves/NOTES.md`.
- **P6b Cluster waves** (user's go): `cut_clusters.py plan` → `freeze` → rolling pool per `runs/waves/RUNBOOK.md`; cost model from P6a; re-assess after every batch of ~6.
- **P7 Tails, independence, pairs, review:** tail clusters from `TAILS.md`; deep rows with the user; independent rows with kind and argument; joint removal for theorems with two removable hypotheses; `results/removable_review.md`; `Findings.md`.

## Log

- @DATE@: workspace created with the hypcheck tool, commit `@KIT@`.
