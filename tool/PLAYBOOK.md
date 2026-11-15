# Playbook: deciding every hypothesis of a Lean library

This is the method that decided all 66,633 Prop hypotheses of Lean core (`Init`, `Std`, `Lean`, `Lake`; workspace `libs/core`), all 2,699 of CSLib at its first analysed commit (`libs/cslib`), and 99.6% of the 6,260 of iris-lean (`libs/iris-lean`, a separation logic), written so that it can be applied to another library with this tool. `README.md` covers setup; this file covers *what to do, in which order, and what to expect*. The workspace's `Plan.md` is the per-library checklist built from it.

## 1. The question and the verdicts

For a theorem `T : ∀ xs, C` and a Prop-valued parameter `hᵢ : Hᵢ` (explicit, implicit or instance, e.g. `(h : 0 < n)`, `[Nonempty α]`, `[IsDomain R]`), let `T'` be `T` without `hᵢ`. One row = one (theorem, idx). Classically exactly one of `T'`, `¬T'` holds.

| Verdict | Meaning | Lean evidence (stored, kernel-checked) |
|---|---|---|
| **removable** | `T'` holds | a proof of `T'` stated as `drop% T i`, universe-polymorphic (each universe of `T` mapped to a distinct universe parameter) |
| **necessary** | `¬T'` | a proof of `¬T'`, usually `¬ drop0% T i` (universes set to 0 are fine: one counterexample refutes the polymorphic `T'`) |
| **independent** | neither is provable from Lean's axioms | an argument, plus Lean support lemmas where possible; kinds below |
| **unresolved** | not decided yet | `reason` says why |

**Dependent hypotheses** (`dependent: true`): `hᵢ` occurs in a later binder or in `C` (`l[i]'h`, `⟨i, h⟩`, `[Fact p]` used by an instance). It cannot simply be deleted, but it is unneeded if it follows from the parameters that don't depend on it (proof irrelevance). So the verdict is about `∀ indep, Hᵢ`: removable = prove `indep% T i`, necessary = prove `¬ indep0% T i` (all other independent hypotheses must hold at the witness; always use the full `indep0%`, never a hand-narrowed variant). Some removable dependent rows are the subject of the lemma (`proof_irrel`, `cast_eq`); they are recorded but flagged in the review.

**Independence kinds** seen so far: `platform` (true for one value of an opaque constant such as `System.Platform.numBits`, false for the other; both halves proved), `opaque-fixpoint` (both sides are `opaqueFix` values without a structural link), `opaque-constant` (an equation between opaque families no axiom fixes), `type-identity` (a refutation needs an unprovable type disequality such as `List β ≠ Array β`; iris-lean: `h_fun : F₁ = F₂` next to `HEq RF₁ RF₂` with `RF : RFunctorContractive F` needs injectivity of the type family, which holds in the set model and fails where equinumerous types are identified). In Init/Std, 183 platform rows were made **provably independent** by swap certificates (`libs/core/scripts/SwapCheck.lean`: the opaque constant replaced by each of two definitions, both halves kernel-checked); that checker is specific to the lean4 build and not part of the tool.

**Soundness rules (non-negotiable).**
- Every removable/necessary verdict has a stored Lean proof that a fresh process recompiles; a tool verdict counts only with `proof_ok: true`. In CSLib, a new tactic (`nofun`) produced 32 bogus "necessary" verdicts that only the stored-proof check caught (it logged an error and recovered with `sorry` inside an auxiliary `match`). Every new tactic class needs a negative control.
- Every hand/agent file passes `scripts/check_hand.py`: each proved statement is definitionally equal to the library's `T'`/`¬T'`/`∀ indep, Hᵢ` (rebuilt independently of the file's elaborators), every verdict is covered, removable proofs keep their universes, and with `HANDCHECK_AXIOMS=1` only `propext`, `Classical.choice`, `Quot.sound` appear.
- Goals are built in an empty local context (the very first hypcheck scan leaked the dropped hypothesis and produced false "removable" verdicts).
- Agents never merge; the main session re-runs `scripts/verify.sh` itself and merges only on `VERIFY PASS`.

## 2. Phases

Each phase has a **pilot gate**: run it small, measure, classify failures, then decide to scale, fix or skip. Record measured numbers and the decision in the workspace's `Plan.md` Log *before* scaling.

| Phase | What | Tooling | Cost | Yield seen |
|---|---|---|---|---|
| P0 setup | workspace, native tools, smoke test, self-test | `new_target.sh`, `tests/selftest.sh` | minutes | |
| P1 inventory | every row, dependent share, instance share, binder types without counterexample values | `scripts/inventory.sh` | < 1 min (Foundation 22 s) | |
| P2 structural | hypotheses the library proof doesn't use (directly / transitively), instances derivable by resolution, twins; transitive-necessity edges | `scripts/struct.sh`, `scripts/struct_proofs.sh` | ~1 min | unused+derivable: Init 515+6, Std 613+54, CSLib 0, Foundation 9+2 |
| P3 tool pilot | HypCheck on ~100 random rows; failure taxonomy | `sample_rows.py`, `run.sh --redo` | ~1–5 worker-min | CSLib 20%, Foundation 6%, Iris 12% with library models (Init high, Std low) |
| P3b generator | `refute_dep` over the dependent rows, with library models registered once | `runs/gen/{RefuteCore,Models}.lean`, `gen_drive.py`, `gen_accept.py` | Std: 8,107 rows in ~13 h (3 lanes) | Std 65% pilot, 17% of all Std verdicts |
| P4 full tool run | all rows (public, then private) | `run.sh N` | CSLib 2,551 rows in 15 min with 10 workers | CSLib 17%, Iris 8.5% |
| P5 flow | transitive necessity, twins, transitive removability, until 0 | `scripts/flow.sh` | seconds per round | CSLib +4% of verdicts; Std 0.04–0.78 per necessary verdict; removable by transitivity: 2,549 Std/Init rows (agents did them by hand) |
| P6a agent probe | 2 agents × 50 random open rows | `sample_rows.py --probe 2`, probe brief | ~20 min | CSLib 98%, Std 100%, Iris 90% |
| P6b cluster waves | frozen cut, rolling pool of ≤ 6 Opus agents | `cut_clusters.py`, wave brief, `accept.sh` | see §4 | CSLib 97.4%, Std 99%+, Iris 95% |
| P7 tails, review | hard rows (main session or tail agents), independence, joint removal of pairs, removable review | `check_pairs.py`, `Findings.md` | hours | |

**Ask the user** before every agent wave, every full-library tool run, and any change to `HypCheck.lean` beyond tactics/models (keep a copy first). Stop and report at the end of every phase.

### P0 Setup
- The library must be built (`lake build`, or `lake exe cache get` for Mathlib-based projects). `tool/hypcheck LIBDIR ROOT` (through `new_target.sh NAME LIBDIR ROOT [MODULES]`) creates `workspaces/NAME`, builds the tools with the library's toolchain (1.5 min), and fills in the docs.
- Long projects span many chats: the workspace `AGENTS.md` + `Plan.md` Log carry the state, and the optional pointer block that `link_repo.sh` writes into `<repo>/CLAUDE.local.md` (git-ignored) sends sessions opened in the repo there. Keep the Log current after every step; it is what the next chat resumes from.
- `tests/selftest.sh` (8 s): one positive cluster and four negative controls through Header → verify → check_hand. Run it after any change to the scripts or the header.
- **Module system: use it whenever the library has it** (check `head -1` of the library's sources for `module`, e.g. Mathlib). Agent header and import modules are then module files, as built for mathlib-data and mathlib-logic-basic (`libs/mathlib-data/runs/hcimports/`, `runs/probe/Header.lean`):
  - `runs/hcimports/HCImportsM.lean`: `module` + `public import` of the modules in scope (plus what their rows need); `HCHeaderM.lean`: `module`, `public import HCImportsM`, `public meta import Lean.Elab.Command`, `public section`, the header elaborators as `meta def`/`elab`. Compile both into `tools/hcrepair` with `scripts/hclean -R runs/hcimports -o X.olean -i X.ilean runs/hcimports/X.lean`; set `HC_ROOT=HCImportsM` and put `tools/hcrepair` on `LEAN_PATH` in `scripts/hcrun` too.
  - Agent header `runs/probe/Header.lean`: `module`, `public import HCHeaderM`, then `import all M` for every non-deprecated module in scope (private constants and non-exposed definition bodies become visible), and **no `public section`**: agent declarations stay private, so their statements may mention private library constants. Tell agents this in the brief.
  - `check_hand.py` turns a `module` file into a plain one before checking (`import all`/`public import` → `import`); a plain importer sees strictly more, so this is sound.
  - Measured (mathlib-data): header 1.1–1.4 GB mmapped vs 2.2 GB as a plain file, anon ~0.15 GB; compile 1–1.6 s. Pitfalls: `@[expose] public section` breaks statements with private constants; without `import all`, private rows and `simp [someDef]` on non-exposed defs fail ("Expected a definition with an exposed body"). PropParams only scans modules whose root is an import root, so for inventory add one real library module next to `HCImportsM` (`--import Mathlib.Logic.Hydra`).
- Smoke test: `scripts/hcrun hypcheck --module ROOT --ns <some theorem>`; measure one worker with `scripts/measure.sh` (Foundation/CSLib: ~0.2 GB anonymous memory, plus shared page cache for the oleans).

### P1 Inventory
`scripts/inventory.sh` writes `runs/inventory/rows_{public,private}.jsonl` (the universe of rows; results files are initialised from them, all unresolved) and `report.txt`. Read the report for: rows per folder (cluster cut and budget), dependent share (Foundation 47%, CSLib 7%, Std ~26% of the open rows), instance hypotheses and their classes (refutation needs a model type lacking the class), and the share of rows whose data binders have value generators (CSLib 20%, Foundation 22%: the tool can only try those). Compiler-generated lemmas without source position (`inj`, `congr_simp`, `match_k.congr_eq_k`) are excluded; private theorems go to their own result file.

**Scope decision here.** Estimate agent cost from the row count (§4). Below ~10k rows: everything. Above: choose folders, or sample to estimate rates per area first (Mathlib: see §6).

### P2 Structural passes
`scripts/struct.sh` (detectors + edges), then `scripts/struct_proofs.sh` (generates `checks/UnusedHand.lean` with `drop_unused%` and `checks/InstDerivHand.lean` with `derive_inst%`, checks, merges). Libraries whose CI runs the `unusedArguments` linter (Mathlib, CSLib, Batteries) give ~0 unused hypotheses; core Lean gave 515 in Init and 613 in Std. The edges (`runs/struct/edges_all.jsonl`) feed flow and the `unlocks` field of agent todo rows. Private rows: detectors exist as `*priv` executables; write their proofs by hand (the core analysis used a script not included here) only if they find hits.

### P3 Tool pilot and failure taxonomy
`python3 scripts/sample_rows.py 100 SEED runs/pilot/rows100.jsonl`, then `scripts/run.sh 3 runs/pilot/v.jsonl --module ROOT --redo runs/pilot/rows100.jsonl --level search --models scripts/models.txt` and `scripts/pilot_summary.py`. Classify **every** failure: missing value/model for a type, missing closer, tool bug, or "no small model exists / conclusion undecidable". Fix classes ≥ 5% (new models in a `models_<lib>.txt`, new closers), at most two re-pilots. In CSLib all big classes were "needs a domain model and a non-decidable conclusion", so the right call was a cheap full run, then agents. HypCheck knows values for `Nat`/`Int`/`Bool`/`Fin`/`BitVec`/`List`/`Array`/`Option`/`String`/`Char`/products/sums/subtypes/sigma, library types by their constructors (depth ≤ 2) or `0`/`1`/`2`/`∅`/`⊥`/`⊤`/`default` (v12), type variables as `Nat`/`Bool` or, under class constraints `Nat` does not meet, a fitting carrier from a small pool and the instance index (`ℚ`, `Unit`, `ZMod 2`, …; v12), functions as constants or one-point updates, plus hand models from `--models` (`TYPE := TERM` lines; `scripts/models.txt` has unlawful `BEq`/`Ord`/`LT`, broken monads, non-associative operations; `models_examples_cslib.txt` shows domain models for λ-terms, LTS, relations, `Set`/`Finset`).

### P3b Generator for dependent rows
Dependent rows (`∀ indep, Hᵢ`) are usually refuted by one broken model per law plus small values, which is mechanical once the models exist: in Std, the generated tactic `refute_dep` decided 8,107 of 9,110 dependent rows (none were removable). `runs/gen/RefuteCore.lean` is that tactic made generic: strategies (models whose law fails), values, types and closers are extension points (`macro_rules` for `refute_strategy`, `refute_value`, `refute_type`, `refute_closer`); the tool's defaults cover small values and standard closers, and `runs/gen/Models.lean` holds the library's models.
- Group the dependent rows by hypothesis shape (`report.txt`, "hypothesis heads"); for the big shapes write a model and its `¬ Law` lemma once (main session or one agent), register it, and test on a pilot chunk (`REFUTE_DEBUG=1` names the premise or binder that blocks a row).
- Pilot: `python3 scripts/sample_rows.py 50 SEED runs/gen/G1/rows.jsonl --dependent`, `LANES=2 python3 scripts/gen_drive.py runs/gen/G1/rows.jsonl runs/gen/G1`, then `python3 scripts/gen_accept.py runs/gen/G1` (check_hand + merge) and `scripts/flow.sh`. Classify every failure before scaling (Std's pilot failures already contained every fix made 7–10 h later).
- Cost: a success takes 2–4 s, a failure 35–110 s, and stored `by refute_dep` proofs rerun the search when checked, so checking costs about as much as generating. Chunks of ~25 rows (~10 for failure-heavy strata), ≤ 3 lanes with 15 GB RAM, stop strata below ~10% yield.
- Baselines with only the tool's generic defaults: CSLib 13 of 50 dependent rows (26%, 3.5 min), Foundation 0 of 50 (its binders are first-order languages and structures). The yield comes from the library models.
- `MODE=rem` (env for `gen_dep.py`) instead tries `indep% T i` by `simp_all`/`grind`: dependent rows derivable from the others.

### P4 Full tool run
Worth it when the pilot yield is ≥ ~10% or the run is cheap (it usually is: CSLib 15 min).
**Levels and goal (v12).** `--level fast` (the default of `HypCheck.lean` itself; `tool/hypcheck` passes `search`) runs the cheap removal pool; `--level search` adds `exact?` and **proof repair** (the library proof of `T` with the uses of `hᵢ` replaced by proofs found in the local context there — `infer_instance`, assumption, trivial, omega, simp_all, solve_by_elim, grind — or the lemma `hᵢ` is passed to unfolded and repaired; kernel-checked); `--level thorough` repairs deeper. `--goal removable` skips the counterexample search (in core it is ~90% of the tool time: 0.10 vs 1.33 s per row). Recommended: `--level search` (it doubled CSLib's tool finds); `--goal removable` for a quick first pass when only redundant hypotheses matter. Repair verdicts (`tactic: repair`) carry no stored proof in the run output, so `merge_tool.py` skips them: run `python3 scripts/repair_proofs.py K OUT.jsonl` after the run. It writes `checks/Repair<K>Hand.lean` (`hc_repair% T i`, the repair code from module `HCRepair`), drops declarations that fail, checks with `check_hand.py` (axioms) and merges as `found_by: proof-repair`. Cost model: `rows × pilot worker-seconds per row / workers`. Merge with `scripts/merge_tool.py OUT TAG [--private]` (only `proof_ok` verdicts; private stored proofs need `scripts/priv/compile_priv.py OUT.proofs` first). The tool almost never finds removable rows in linted libraries (CSLib 7 of 2,551).

### P5 Flow
`scripts/flow.sh` after every merge: if the library proof of a necessary `B` passes its hypothesis `h_j` only to `A`'s hypothesis `i`, then `A' → B'` and so `¬A'` (kernel-checked `hc_nec_trans`; removable side targets become premises). Twins (identical statements) copy verdicts. **Removable by transitivity** is the same edge the other way: if every use of `h_j` in B's proof goes to removable non-dependent targets A, substituting A's stored proof of `A'` proves `B'` (`scripts/rem_trans.py`; the target's proof is found through the `proof_file`/`proof_decl` that `merge_hand.py` records from `check_hand.py`'s declaration map, and source files are compiled as modules into `runs/remtrans/mods`, which must be kept). On the decided Std/Init data 2,549 removable rows that agents proved by hand follow this way (e.g. `Std.HashMap.getElem_ofList_of_mem` from `Std.DHashMap.Const.get_ofList_of_mem`), CSLib 7. Dependent rows never qualify (their removability is `∀ indep, Hᵢ`, not a dropped binder). Flow is free, so always run it after every merge; `accept.sh` does.

### P6a Agent probe
2 Opus agents × 50 random open rows (`sample_rows.py 100 SEED --probe 2`), brief `runs/probe/BRIEF.md`, 60-min box. Measures decided share, removable share, agent-min/row, tokens/row, memory. Gate: ≥ 90% decided. Collect the reusable models the agents report into `runs/waves/NOTES.md`.

### P6b Cluster waves
- `cut_clusters.py plan 120` (default by module; `--by stem` when the library repeats one lemma across many wrapper types), then **`freeze`** before the first wave, and `next K` to emit each cluster from the frozen cut (clusters never overlap as rows get decided elsewhere).
- Rolling pool of ≤ 6 Opus agents: when one reports, `scripts/accept.sh DIR C` (verify → merge → flow), add its reusable helpers to `NOTES.md`, launch the next cluster. Every ~6 clusters: rates vs model, decided/removable share, tokens vs budget, ETA, Log entry, short status to the user.
- Rows an agent gives up on go to `runs/waves/TAILS.md` grouped by obstruction; build tail clusters from them (75-min box, the earlier agents' leads in the prompt).
- Procedure details: `runs/waves/RUNBOOK.md` in the workspace.

**Reuse after a wave (optional, v12).** `python3 scripts/hand_modules.py` compiles the agents' hand files as modules (the shared header once as `RUHeader`); a search-level run with them imported (`HC_EXTRA_PATH=$PWD/runs/reuse/mods scripts/run.sh … --level search --goal removable --import RU_…`, see the script) lets `exact?` use the agents' helper lemmas on the open rows. iris-lean (all 73 wave files): 6 rows through another file's helper, 3 of them beyond `rem_trans.py`; cheap, small. Keep `runs/reuse/mods` once verdicts from it are merged (their stored proofs import it).

### P7 Tails, independence, review
- What remains after tails is usually deep: CSLib's last 40 rows needed a Paxos-style algorithm (1,426 lines), a No-Free-Lunch lower bound (871 lines), a non-measurable-map construction; iris-lean's last ~30 needed new models of the logic itself (fancy updates with dead tokens, one-shot invariants, non-affine exact-resource models). The main session did these with the user, designing the counterexample from the properties it must have and formalising step statements with `sorry` first.
- **Deep rows: work directly, not through an agent.** For one row or a small family whose obstruction is a missing construction, the main session builds the model itself (iris-lean: 6 such clusters, up to ~600 lines each, 2–4 compile rounds). An agent adds a briefing round-trip and returns only a summary, while the main session already holds the obstruction history.
- **Reduce before attacking.** A short Lean-checked reduction often turns a vague row into a crisp question. iris-lean: dropping `[BIAffine]` from `fupd_keep_plainly` is *equivalent* to the class law `keep` with an implication in place of the wand. The reduction also showed which easy cases already hold, so the counter-model had to avoid them.
- **External model for paper mathematics (with the user's go; the user pastes the brief).** For deep rows after ≥ 2 failed agent attempts, write a self-contained brief for a strong external model that cannot run Lean:
  - the exact statement and every law the model must satisfy, field by field as in the library's classes;
  - the library proof, marking where the hypothesis is used;
  - what is known: models tried and why each fails, and Lean-checked reductions;
  - the answer required: counter-model, proof or "stuck", with a law-by-law check and the failing entailment at an explicit point.

  Re-derive every answer on paper against the library's actual definitions before any Lean. In iris-lean, one answer silently read `⊢ X` as `True ⊢ X`, which assumes affinity, and was rejected. Then build the answer in the main session and credit the source in the Log. iris-lean: 3 briefs (not part of this repository) gave 3 counter-models and 1 removability proof, all kernel-checked, deciding 7 rows. The brief contains only library mathematics.
- Independence: only after real refutation and proof attempts; record kind, argument and support lemmas (`<C>_independent.jsonl`, merged by `merge_hand.py`).
- Joint removal: theorems with two removable hypotheses get a pair verdict (`drop2%`/`indep2%` macros and `scripts/check_pairs.py`; CSLib: 7 of 12 pairs jointly removable).
- Removable review: list every removable row with a one-line reason (`results/removable_review.md`); library defects beyond that go to `Findings.md`. Nothing goes upstream without the user.

## 3. What makes agents effective (put this in every brief)

- **Build a few reusable broken models first** (a relation that is not transitive, a monad that breaks one law, a type with exactly the wrong cardinality, a stuck term), prove once which laws they do satisfy, then refute theorem by theorem by specialising the hypothetical `T'` to them. Give each model its own type so instance search fills the remaining instance arguments and `Decidable` instances.
- **State every verdict with the header elaborators** (`drop%`, `indep%`, `drop0%`, `indep0%`), never by retyping statements. The comment above each verdict names the original theorem in backticks, and nothing else in backticks.
- **Generators for repeated shapes:** one representative per (stem, hypothesis) by hand, then a small Python generator for the siblings (Std: 238 of 391 rows in one probe came from generators; stem clusters ran 3.7× faster than random rows).
- **Removable verdicts are findings:** before a hand proof, search the library for a sibling lemma without the hypothesis. Typical removable patterns: boundary hypotheses where small cases hold anyway (`0 < n`, `1 < b`), instances implied by others or unused in meaning (`[Nonempty β]` derivable from `[Nonempty α]` and a function), well-formedness premises that only matter for lookups.
- **Libraries that axiomatise a logic (separation/modal logics, class hierarchies of laws):** build **one lawful construction with a small parameter** and prove its laws once. Each refutation then only chooses the parameter. iris-lean: `|={E1,E2}=> P := ownE E1 -∗ M (ownE E2 ∗ P)` is a lawful fancy update for *every* closure modality `M` (intro, join, frame, mono, ◇-absorbing, non-expansive). So refuting a fancy-update law meant finding the right `M`: a step-dropping "dead token" closure, reachability under irreversible steps, or "now, or at step 1 after adding an idempotent junk element". Useful knobs:
  - an **equality order** on resources gives non-affine models, where leftover resources cannot be dropped;
  - **duplicable marks** make steps irreversible (o → d is frame-preserving, d → o is not);
  - **resource-independent** propositions are those whose truth depends only on the step index.
- **Ports from another prover:** when a port generalises the original's setting (Rocq's always-affine `uPred` → any ordered resource algebra), it sometimes adds a hypothesis to keep the original proof working. Try a different proof before accepting it as necessary. iris-lean `fupd_vs_trans`: `[IncOrd M]` is removable by taking the whole left side as the new existential witness.
- **Typical refuting models:** an empty or infinite type for `Finite`/`Nonempty`/`IsEmpty`; `fun _ => none` or a bind-counting state monad for monad laws; `if a = b then .eq else .lt` for transitivity of comparisons; `a/2 == b/2` for `LawfulBEq`; stuck or non-locally-closed terms for reduction relations.
- **Shared knowledge:** `NOTES.md` (helpers with file:line, maintained only by the main session) made later CSLib clusters 2–3× faster than the probe. Agents copy helpers into their own namespace; hand files never import each other.
- **Breadth over completeness:** ~10 minutes per resisting row, then `gave_up` with the precise obstruction.
- **Honest logs:** one log line per todo row (outcome, minutes, technique, obstruction); the main session plans from them.
- **Memory discipline:** Lean only via `scripts/lean.sh` (≤ 2.5 GB per call, shared slice, `big.lock` for full-file compiles), one Lean process per agent, no lean-lsp MCP tools (uncapped servers), small scratch files.

## 4. Cost model and measured rates

| Library | Rows | Tool share | Agent rate (clustered) | Tokens/row | Removable share | Notes |
|---|---|---|---|---|---|---|
| Init (core) | 18,424 | high (Nat/Int/BitVec evaluate) | 0.15–0.2 min | – | 7.6% | 515 unused (no linter in core) |
| Std (core) | 46,916 | low (maps don't evaluate) | 0.06–0.15 min (stem clusters) | 0.85–1.4 k | 14.6% | 116 clusters, 30.5 M tokens |
| CSLib | 2,699 | 17% | 0.075–0.24 min (median 0.16) | 1.6–2.5 k | 3.9% | 17 clusters, 74 min wall, 5.1 M tokens |
| iris-lean | 6,260 | 8.5% (13.5% with detectors and flow) | Algebra 0.14 min; BI/HeapLang/ProgramLogic 2–4× slower | ~2 k (Algebra) | 3.1% | 47 clusters, ~1,200 agent-min, ≥ 15 M tokens in all; probe 0.46 min and 5.4 k tokens per row; 25 rows left open (deep, low value), 5 type-identity |
| Foundation (tool test) | 7,871 | pilot 6% | not run | – | – | 47% dependent rows |

- **Random-row probes** cost 0.37–0.55 agent-min and 4.8–5.5 k tokens per row; clustered waves 2–4× less.
- **Agent time is mostly a fixed cost per cluster:** Std fit `agent-min ≈ 9.5 + 0.059 × rows` (residual sd 5 min); hence clusters of 120–300 rows, not 50.
- **Wall-clock** with a rolling pool of 6: `Σ agent-min / 6` plus ~1–2 min of main-session verify/merge per cluster (overlapping).
- **Budget before scaling:** `lane-hours = rows × (yield × t_ok + (1 − yield) × t_fail) + checking` for tool passes; `agent-hours = clusters × 10 min + rows × rate` and `tokens = rows × tokens/row` for waves. Tell the user the ETA and token estimate before each phase and re-estimate after each batch.
- **Stop rules:** a tool pass or stratum below ~20 verdicts per lane-hour for 30 min stops; strata below ~10% pilot yield go straight to agents.

## 5. Operations and pitfalls

- **Memory:** every multi-process Lean run goes in a memory-capped systemd scope sized by *available* memory, `min(60% RAM, MemAvailable − 2.5 GB)`, never by total RAM; `OOMPolicy=continue` so one worker dies instead of the machine. All scripts start Lean through `scripts/capped`, the only platform-specific file: a systemd scope where `systemd-run --user` works, otherwise no cap (one warning; macOS, containers, WSL2 without systemd; README "Platforms"). Size the agent slice with `systemctl --user set-property --runtime <slice> MemoryMax=… MemorySwapMax=0` (systemd only; without it, run fewer agents at once). Measure one worker before any new kind of run.
- **cgroup peaks include page cache:** importing Mathlib maps ~5 GB of oleans; a scope's `memory.peak` can sit at its cap while anonymous memory is 0.3 GB. That is reclaimable and harmless; judge workers by `RssAnon` (`scripts/measure.sh`) and by `oom_kill` events.
- **Native tools, not `lean --run`:** a script importing Mathlib under `lean --run` costs 1.6–1.9 GB anonymous memory (core oleans read twice); the native executable ~0.2 GB.
- **Monitoring:** watch long runs (Monitor tool or a status file), alert on cap kills, exit and stale progress (20 min). Process checks use bracket patterns (`grep '[h]ypcheck'`) or `kill -0 PID`; `pkill -f PATTERN` kills the shell that runs it when PATTERN is in its own command line. Stop `run.sh` runs with `systemctl --user stop $HC_UNIT.scope`.
- **Never edit a running shell script** (`accept.sh`, `verify.sh`): bash reads scripts incrementally.
- **Lean reports at most ~100 errors per compile:** attribute errors to declarations in batches of ≤ 50.
- **Library notation can break tool snippets:** Foundation declares a `]!` token, so `xs[i]!` stops parsing in any file that imports it; Iris declares `infix:60 " || "` (disjointness), so `n > 1 || b` becomes `n > (1 || b)` and fails with `Disjoint Bool`. The tool's header, generator core and checkers avoid both (`xs.getD i default`, `or a b`). If a header compile fails with a parse error, suspect a library token.
- **Private names:** in Lean terms `_private.Mod.«0».x` (see `hcConst`), but `_private.Mod.0.x` in the backticked comment for `check_hand.py`.
- **Long names** wrap in `#print axioms` output; short declaration names (`<c>_<n>`).
- **Removable proofs must keep universes** (`drop%`, declared universe variables); `drop0%` is for refutations only.
- **The library checkout is read-only:** no edits, no commits; rebuild and re-check if it moves.

## 6. Scaling to Mathlib-sized libraries

Measured with this tool (Mathlib commit `04aba383281`, v4.36.0-rc2): **310,526 public + 4,956 private rows** (Algebra 50.7k, Analysis 41.1k, Topology 35.0k, CategoryTheory 32.5k, MeasureTheory 26.4k, RingTheory 24.1k, Order 14.3k, Data 12.2k, Combinatorics 6.1k; details in §8). At the clustered rates measured so far (~0.14 agent-min per row including the fixed cost per 120-row cluster, 1.3–2.5 k tokens per row) all of Mathlib would be ~720 agent-hours (~120 h wall with 6 agents) and ~400–800 M subagent tokens, before any tool or flow savings, and Mathlib's analysis-heavy rows are likely slower than CSLib's. So choose scope:
- run P1–P3 over everything (cheap), then pick folders by interest and by pilot yield;
- probe each candidate area (2 × 50 rows) before committing a wave budget;
- prefer areas with computational content (combinatorics, order, data structures) where small models exist; analysis/topology rows need constructions that cost more per row;
- set `HC_MODULES` to the chosen prefixes so results, cuts and status stay inside the scope.

## 7. Tool version

The current `HypCheck.lean` is v12.2. Compared with v11 (the CSLib port: removal by `omega`/`simp_all`/`grind`/`decide`, counterexample search over value generators and `--models`, dependent rows, stored proofs, private names, Mathlib/Aesop tactics parsed at run time), v12 came from a benchmark of the mechanical checks on labelled samples of core, CSLib and iris-lean and unlabelled Mathlib rows:
- removal pool ordered cheapest first and extended (`assumption`, `trivial`, `infer_instance`, `rfl`, `decide`, `solve_by_elim`, `simp`; `lia` replaces `omega`; `aesop` dropped: expensive, nothing unique; a 4× heartbeat budget found nothing more);
- `--level`/`--goal`; `exact?` and proof repair at level search (`HCRepair.lean`, stored proofs by `repair_proofs.py`), with `infer_instance` as the first hole tactic (an instance hypothesis implied by the other instances, the case of Mathlib's `droppableHypotheses` linter);
- necessity: carrier discovery for constrained type variables, constructor and notation values for library types;
- an exception while checking one theorem no longer stops the worker: its hypotheses are reported unresolved with `reason: "tool error: …"` (seen once, iris-lean `Relation.Iterate.head_induction_on`, "unexpected bound variable #0").

Measured on the rows the fast level left open: necessary verdicts CSLib 12 → 25 of 100 labelled, Mathlib 36 → 57 of 500, iris 4 → 7, core 96 → 100 (3 tree-map rows lost to the 10 s limit); removable recall with detectors (fast level) core 31%, iris 17%, CSLib 6%, plus `exact?` and repair core 34%, CSLib 12%, iris 18%; 0 contradictions with the labels. On the 81 rows of Mathlib PRs #45525/#45526 that the fast level missed, repair with `infer_instance` first found 36 instead of 27 (recall on those PRs 94%).

Known printer limits: a counterexample at universe 0 for a universe-polymorphic `T'` sometimes prints a statement at the wrong level, and some removable blocks fail with "unused universe parameter". Both show up as `proof_ok: false` and are not merged (CSLib 1, Foundation pilot 2 of 100 rows); agents decide those rows.

## 8. Tool tests

### Libraries the tool was run on

| Library | Toolchain | What ran | Result |
|---|---|---|---|
| Foundation | v4.33.1 | P0–P5, P3b pilot, cut/freeze/next, probe sampling, `accept.sh`, self-test | tools build in 1.5 min with no API drift; 7,786 public + 85 private rows (22 s); P2 9 unused + 2 instance-derivable rows proved, checked and merged; pilot 100 rows in 55 s with 4 workers (peak 1.1 GB): 3 necessary + 3 removable confirmed, 2 unconfirmed not merged; P3b with only the generic defaults: 0 of 50 dependent rows (~1 min; the binders need Foundation models: languages, structures, arithmetic models); self-test OK |
| CSLib | v4.36.0-rc2 | regression against the original port; removable by transitivity | self-test OK; smoke test agrees with the port; the tool's `check_hand.py` reproduces the port's checks of `Probe2Hand.lean` (50 verdicts, 91 standard axioms) and `W1c4Hand.lean` (120 / 184); `rem_trans.py` re-derived all 7 removable rows that CSLib agents had proved by hand although their target was already removable (reset to unresolved in a copy; 16 s, standard axioms); generic `refute_dep` (P3b, no CSLib models) re-derived 13 of 50 reset dependent necessary rows in 3.5 min with 2 lanes (9 of them done by agents in the port), checked and merged by `gen_accept.py` |
| iris-lean (`Iris`) | v4.35.0 | full P0–P7 (workspace `libs/iris-lean`) | 6,260 rows: 6,035 necessary / 195 removable / 5 independent / 25 unresolved (99.6%), every verdict kernel-checked; tool 8.5% (13.5% with detectors and flow), agents ~5,390 rows; deep rows by new models of the logic (main session, 3 with an external model's paper answers); 5 upstream defects in its `Findings.md`, results in `libs/iris-lean/Results.md`. Tool fixes from this run: `a \|\| b` avoided in library-compiled Lean (Iris's `\|\|` notation), `cut_clusters.py` splits oversized modules |
| iris-lean, v12 (scratch workspace) | v4.35.0 | HypCheck v12 end to end: `new_target.sh` + build (with `HCRepair`), inventory, `run.sh --level search` on 24 rows, `merge_tool.py`, `repair_proofs.py`, `hand_modules.py` + a run with `--import RU_…` and `--goal removable`, self-test | 7 necessary + 9 removable by tactics (8 `proof_ok`, 1 known `unused universe parameter` printer failure, not merged), 8 by proof repair: all 8 stored as `hc_repair%`, check_hand 0 errors / 0 not covered / 8 standard-axiom declarations, merged; self-test OK. Tool fixes from this run: repair code as module `HCRepair` (Iris declares `>` syntax, so source copied into library files does not parse), `no_implicit_lambda%` around `hc_repair%` |
| Mathlib | v4.36.0-rc2 | P1 inventory (tools copied from the CSLib workspace) | 310,526 public + 4,956 private rows in 4.4 min; see below |

Bug found by the Foundation test and fixed: Foundation declares a `]!` token, which broke `xs[i]!` in the agent header and in `check_hand.py`'s checker; the tool no longer uses that syntax in code compiled with the library.

### Measured on Mathlib

P1 inventory of Mathlib (commit `04aba383281`, v4.36.0-rc2), `scripts/inventory.sh` with tools copied from the CSLib workspace: **310,526 public rows** in 151,069 theorems (+ 26,867 rows in compiler-generated lemmas, excluded) and **4,956 private rows**; 29.8% dependent, 48.7% instance hypotheses, 27.9% with value generators for all data binders. PropParams took 265 s at 0.3 GB anonymous memory (the 5 GB cgroup peak is olean page cache, reclaimable; nothing was killed). Largest folders (rows): Algebra 50,651, Analysis 41,141, Topology 34,982, CategoryTheory 32,537, MeasureTheory 26,357, RingTheory 24,080, Order 14,331, Data 12,202, LinearAlgebra 11,018, Geometry 9,876, Probability 8,962, NumberTheory 8,277, GroupTheory 6,510, Combinatorics 6,062. Cost implications: `PLAYBOOK.md` §6.

### Not included in the tool

- The Std-specific machinery of hypcheck (hash/tree map evaluation and models, the Std toolkit and `genlib.py` wrapper tables; `refute_dep` itself is in the tool in generic form): working files of the core analysis, not part of this repository.
- Swap certificates for provable independence (`libs/core/scripts/SwapCheck.lean`): lean4-stage1-specific.
- Proof generation for structural hits on *private* theorems (the detectors are there; the core analysis wrote them with a script that is not part of this repository).

## Sources

`Methods.md` and `libs/core/Results.md` (Init/Std: methods, results), `libs/cslib/Results.md` (the first port: P0–P7 with metrics), `libs/iris-lean/Results.md`, and the tool tests in §8.
