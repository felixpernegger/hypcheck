# Which hypotheses do iris-lean's lemmas actually need?

Hypothesis analysis of [iris-lean](https://github.com/leanprover-community/iris-lean) (the Lean 4 port of the Iris separation logic), 2026-11-12 to 2026-11-14. How verdicts are defined, found and checked: `../../Methods.md`.

- **Library version:** commit `8293092f` (2026-11-05).
- **Toolchain:** `leanprover/lean4:v4.35.0`.
- **Analysis only:** no file of the library was changed, and nothing has been reported upstream yet.

## Summary

Every Prop-valued hypothesis of every theorem in `Iris` was examined: 6,260 hypotheses in 4,179 theorems, of which 108 are in private theorems. For each one, we asked whether the theorem still holds without it.

| Verdict | Rows | Meaning |
|---|---|---|
| **Necessary** | 6,035 | Lean proof that the theorem fails without it |
| **Removable** | 195 | Lean proof of the theorem without it (147 theorems) |
| **Independent** | 5 | Neither provable nor refutable in Lean (argued, not formally certified) |
| **Unresolved** | 25 | Open; each tried at least twice, with a recorded obstruction |

**99.6% decided.** Every necessary and removable verdict is backed by a stored Lean proof, recompiled by a checker before it was accepted. The checker:
- compares the proved statement with the original theorem minus the hypothesis, up to definitional equality;
- requires the removable proofs to keep the theorem's universe parameters;
- rejects any proof that uses axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

Highlights:
- **Five library defects worth reporting upstream** (section 4). The most substantive one: `fupd_vs_trans` needs neither `[IncOrd M]` nor `vs_impl`, with a replacement proof.
- **195 removable hypotheses** (section 3), mostly instance arguments that hold in every model of the other assumptions, or side conditions implied by other premises.
- **Several hypotheses that look redundant are necessary.** Proving this took new counter-models of Iris's logic (section 5). Examples: `fupd_keep_siPure` is a genuine extra axiom, `[BIAffine]` is needed for `fupd_keep_plain(ly)`, and both `[Persistent P]` and `[Absorbing P]` are needed for `aupd_intro`.

## 1. Scope and method

**Rows.** One row is one Prop-valued binder of one theorem: explicit hypotheses, instance arguments of Prop-valued classes, and implicit Prop binders. Compiler-generated lemmas without a source position are excluded (825 rows). Of the 6,260 rows:
- 46% are instance hypotheses;
- 7% are dependent, meaning later binders or the conclusion mention them;
- for a dependent row, "removable" means the hypothesis follows from the other binders.

**Pipeline.** Each stage only handled the rows the earlier stages left open:

1. **Structural detectors (19 removable).** These find hypotheses the library's own proof never uses, and instance hypotheses that type-class resolution derives from the other binders.
2. **Automatic tool, HypCheck (532 verdicts).** For each row it:
   - tries to prove the theorem without the hypothesis using tactics;
   - otherwise searches small instantiations, plus hand-written models of Iris's algebraic structures, for a counterexample.

   One full run took 25 min on 6 workers.
3. **Flow (291 verdicts).** Verdicts that follow from stored ones:
   - transitive necessity: if `A'` is used to prove `B'`, refuting `B'` refutes `A'`;
   - identical statements;
   - removability by transitivity.

   Flow re-ran after every merge.
4. **Agent clusters (about 5,390 verdicts).** Opus subagents, at most 6 at a time, each got a cluster of related open rows with a brief. They wrote Lean proof files, which the main session re-verified before merging. The runs were:
   - a probe;
   - 47 clusters;
   - two "tail" rounds, which revisited rows that had resisted, each with its previous obstruction.
5. **Deep rows (31 rows → 25).** These were handled in the main session. Some models were built from scratch. In three rounds, a written brief went to an external model (GPT) for paper mathematics only. That produced three counter-models and one proof, all re-derived and kernel-checked here.
6. **Pairs.** For theorems with two individually removable hypotheses, joint removal was checked: 75 pairs, 61 jointly removable.

**Cost.** About 1,200 agent-minutes and at least 15 M subagent tokens are recorded. Two runs stopped at a usage pause have no token record. Wall clock was about 2.5 days.

## 2. Results by folder

| Folder | Necessary | Removable | Independent | Unresolved |
|---|---|---|---|---|
| Algebra | 2,318 | 38 | 0 | 0 |
| BI | 1,572 | 108 | 0 | 16 |
| ProofMode | 928 | 7 | 0 | 0 |
| Std | 327 | 12 | 0 | 0 |
| ProgramLogic | 332 | 9 | 0 | 6 |
| Instances | 267 | 9 | 5 | 3 |
| HeapLang | 290 | 11 | 0 | 0 |
| Examples | 1 | 1 | 0 | 0 |
| **Total** | **6,035** | **195** | **5** | **25** |

Public and private theorems are combined. Private: 98 necessary, 10 removable.

## 3. Removable hypotheses

All 195 are listed in `results/removable_review.md`, with the reason and the proof location for each. 164 can be dropped from the statement outright. 31 are dependent; each of those follows from the other binders, so it holds automatically wherever the theorem is used.

| Pattern | Examples |
|---|---|
| Instance hypotheses that hold in every model of the kept ones | `[IsTotal α]` on 8 core lemmas of `Algebra.CMRA` (`core x` falls back to `x`); `[BIFUpdateSbi]`/`[BIBUpdateSbi]` on the `*_plain_forall*` family (SiProp is a well-ordered chain); `[NonExpansive₂ R]` on 15 rtc/tc lemmas of `BI/Lib/Relations`; `[OrdInc]` on `Auth` updates; `[BILoeb]` on `impl/wand/wandIff_timeless`; `[IncOrd M]` on `fupd_vs_trans` |
| Derivable instances | `NonExpansive`/`Contractive` from `f = g` (funext); `[OFE.Discrete A]` ⇒ non-expansive; `Increasing` tokens of (Dyn)ReservationMap/View |
| Side conditions implied by other premises | `wp_base_pure`/`wp_base_atomic*` in `HeapLang.Completeness`; `toVal e₁ = none` in `wp_lift_pure_det_base_step_no_fork`; `↑N ⊆ E` in `slice_insert_full`; injectivity in `bigOpM_filterMap_eq`; `Ei ## Ef` in `step_fupd_mask_frame_right` |
| Unused assumptions of the paradox theorems | 43 rows in `BI/Lib/Counterexamples` (`SavedProp.contradiction`, `Inv.*_alloc`, `inv_fupd'`, `LaterCreditsPlain`, `Linear.leak`, `[BIAffine]` on `Inv.contradiction(')`) |

The paradox theorems in `BI/Lib/Counterexamples` are demonstrations: weaker assumptions make them stronger results, but nothing else in the library uses them.

**Caution:** a removable hypothesis on a public lemma cannot simply be deleted. Callers pass it explicitly, so removing it changes the API.

## 4. Library defects worth reporting upstream

Full text, evidence and suggested fixes are in `Findings.md`. None has been reported.

1. **`fupd_vs_trans` (`Instances/Lib/FUpdFromViewShift.lean:65`) needs neither `[IncOrd M]` nor `vs_impl`.**
   - The Rocq original lives in an always-affine `uPred`. The port generalises to any UORA and adds `IncOrd` (affinity), which this lemma does not need.
   - The replacement proof takes the whole left-hand resource `A ∗ vs₁₂ A Q` as the new existential witness. Then `persistent_intro_r`, `vs_exists` and `trans` all work under `emp`.
   - Kernel-checked with both hypotheses dropped together. The other three hypotheses (`Persistent vs`, `vs_exists`, `vs_persistent_intro_r`) are necessary, and `IncOrd` stays necessary for the sibling `fupd_vs_mono`.
2. **`[NonExpansive₂ R]` is unneeded on 15 lemmas of `BI/Lib/Relations.lean`.** It comes from a section variable. The introduction rules hold for every `R` when proved by unfolding the impredicative definition, instead of via `bi_least_fixpoint_unfold`.
3. **`FromMathlib.Pairwise.forall` (`Std/FromMathlib.lean:20`) carries three unneeded hypotheses.** With `hR : R a b ↔ a ≠ b`, the conclusion holds outright. The Mathlib original takes `Symmetric R`.
4. **`OrdCommMonoidLike.instCancelable` (`Algebra/Numbers.lean:215`) can only apply to one-element types.** An idempotent, commutative, left-cancellative operation forces `x = y`. The instance was copied from the `(ℕ, +)` section.
5. **`Linear.leak` (`BI/Lib/Counterexamples.lean:482–533`) quantifies over auto-bound `M0 M1`** instead of the `Mask` constructors, because `open Mask` is missing. The lemma still holds, but it is not the intended statement.

## 5. Necessary hypotheses that took new models

Most necessary verdicts came from small counterexamples: two- to four-element resource algebras, unlawful OFEs, and the like. A few hypotheses looked redundant, and refuting them needed new models of Iris's logic. These say something about Iris's axioms, beyond this library.

| Hypothesis | What the model shows | Proof file |
|---|---|---|
| `[BIFUpdateSbi]` on 7 lemmas, incl. the class field `fupd_keep_siPure` | `fupd_keep_siPure` is **independent of the `BIFUpdate` laws**. A lawful fancy update may drop the step index by irreversibly killing a held token ("dead tokens"), so `\|={{1},∅}=>` proves anything true at step 1 while `\|={{1}}=>` cannot | `checks/T3c2Hand.lean` |
| `[BIAffine]` on `fupd_keep_plainly`, `fupd_keep_plain` | Without affinity, `fupd_keep_plainly` is equivalent to `keep` with an **implication** in place of the wand (reduction checked in Lean). A model with an idempotent "junk" resource satisfies all three `BIFUpdateSbi` laws but not the implication form | `checks/T3c5Hand.lean` |
| `[Persistent P]` and `hsplit`/`hI` on `aupd_intro`/`tac_aupd_intro` | A one-shot invariant (fresh → open → sealed, irreversible) gives one `atomic_acc` round but no `atomic_update` | `checks/T3c3Hand.lean` |
| `[Absorbing P]` on `aupd_intro` | A non-affine exact-resource model with an irreversible store: `P := emp ∨ own f₀` is persistent but not absorbing | `checks/T3c4Hand.lean` |
| `[BiEmbedSbi]` on `fromModal_plainly_embed` | `■` is **determined by the BI** (`siPure` is fixed by `▷`), so a type synonym with another `Sbi` structure cannot help; the counter-model uses a step-delaying pullback of `MonPred` | `checks/T3c1Hand.lean` |
| `Persistent vs`, `vs_exists`, `vs_persistent_intro_r` on `fupd_vs_trans` | View-shift relations on a 4-element algebra, comparing the sets of resources where P and Q hold, with preorders that depend on the resource or are not closed under unions; and `vs A B := ▷(A → B)`, where `fupd P = ▷P` | `checks/T3c6Hand.lean` |

The models for `[BIAffine]` on `fupd_keep_plain(ly)`, `[Absorbing P]` on `aupd_intro`, and `fupd_vs_trans` (including the `IncOrd` removal proof) were proposed on paper by GPT ("Astra"), from written briefs. Each was re-checked on paper here and then built and kernel-checked in Lean. One earlier answer was wrong: it treated `⊢ X` as `True ⊢ X`, which assumes affinity. It was rejected.

## 6. Independent (5)

The five rows are `h_fun : F₁ = F₂` in `OFE.transpAp_{eqv,validN,op,pcore}_mp` and `validN_transpAp_mp` (`Instances/IProp/Instance.lean`).
- `h_fun` occurs in the conclusion, so the question is whether it follows from the other binders: does `HEq RF₁ RF₂` (for `RF₁ : RFunctorContractive F₁`) imply `F₁ = F₂`?
- That needs the type former `RFunctorContractive` to be injective. Lean can neither prove nor refute this. It holds in the set model, but fails in models that identify types with the same cardinality. This is the same situation as "is `Fin` injective?".
- The argument is recorded, not certified. No certificate method applies to type-constructor injectivity.
- In practice `h_fun` is morally redundant but cannot be removed, since the statement's type mentions it.

## 7. Unresolved (25)

Each row has its last obstruction in `results/unresolved_review.md`. They were left open deliberately, because the cost of deciding them is high and the value is low:

| Group | Rows | Obstruction | Likely answer |
|---|---|---|---|
| `BI/Lib/Counterexamples` (invariant paradox: fupd laws, `start`/`finished` token laws, persistence of `inv`/`finished`, `[BIAffine]` on `saved_A`/`saved_cast`) | 16 | Honest and cancellation invariants satisfy every conclusion. A refutation needs impredicative, dishonest persistent invariants consistent with the other assumptions | Mixed; these are demonstration theorems that nothing else uses |
| ProgramLogic mask inclusions `E₂ ⊆ E₁` (`wp_step_fupd`, `wp_frame_step_l/r`, `wp_step_fupdN_strong`, `twp.to_wp_fupdN_strong`, `inv_open_maybe_ectxlang`) | 6 | A refutation needs an update to `E₂ ⊄ E₁` that produces the tokens of `E₂∖E₁`, inside a full weakest-precondition model | Necessary, as in Rocq |
| Slices `↑N ⊆ E` (`slice_split`, `slice_combine`, `slice_iff`) | 3 | A refutation must use the stuck copy of the old slice, which is only reachable by opening the old invariant | Necessary, as in Rocq |

## 8. Caveats

- **Hypotheses are checked one at a time.** Two individually removable hypotheses need not be jointly removable; joint removal was checked only for the 75 pairs listed in `results/removable_pairs.jsonl` (61 jointly removable).
- **"Necessary" is relative to the other hypotheses.** It means the theorem with all other binders kept is false without this one. It does not mean the hypothesis is the best possible.
- **Unresolved says nothing either way.**
- **Results are tied to commit `8293092f`.** If the library moves, the stored proofs must be recompiled before reuse.

## 9. Library-specific method notes

- Tool: kit `HypCheck.lean` v11.1. Extra models in `scripts/models_iris-lean.txt` (always used together with `scripts/models.txt`): the discrete CMRA `Iris.DFrac` with non-unital, non-cancellative elements (refutes ORA/CMRA/OFE inclusion and validity laws), `Iris.SiProp` (a BI and a non-discrete OFE), `Unit`, `Iris.Qp`, and small values for them.
- Reusable models built by the agents, found in the hand files: SiProp semantics, a non-affine Boolean BI (`checks/W4c4Hand.lean`), BIs with a non-timeless `emp`, Kripke BIs without `BIPersistentlyExist`, small hand-built ORAs/UORAs and non-discrete OFEs, toy languages with a weakest-precondition toolkit, a verified HeapLang stepper (`checks/T1c3Hand.lean`), and lawful mask-sensitive fancy updates.
- Some refutations only work with type binders at `Type`: at `Prop` the weakened statement is true by proof irrelevance. Those are stated by hand instead of with `drop0%`/`indep0%`.
- Joint removal of pairs: elaborators `drop2%`/`indep2%` (defined in `checks/J1c0Hand.lean`), checker `scripts/check_pairs.py`, results in `results/removable_pairs.jsonl`.

## 10. Where things are

| What | Where |
|---|---|
| All verdicts | `results/public.jsonl`, `results/private.jsonl`, plus `_removable`, `_unresolved` and `_independent` splits |
| Review lists | `results/removable_review.md`, `results/unresolved_review.md`, `results/removable_pairs.jsonl` |
| Upstream defects | `Findings.md` |
| Stored proofs | `checks/*.lean` (one file per cluster); tool proofs in `proofs/tool/` |
| Live numbers | `python3 scripts/status.py` |
