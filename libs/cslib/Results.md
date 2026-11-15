# Results: CSLib

Which Prop-valued hypotheses of the theorems in [CSLib](https://github.com/leanprover/cslib) are needed? How verdicts
are defined, found and checked: `../../Methods.md`.

- **Library version:** CSLib commit `f8acdb37` (`main`, 2026-11-10), Mathlib `887bb849` as pinned by its lakefile.
- **Toolchain:** `leanprover/lean4:v4.36.0-rc2`.
- **Scope:** all theorems with a Prop-valued parameter in the library `Cslib` (not `CslibTests`); 863 public and
  45 private hypotheses of compiler-generated lemmas without source position excluded.
- **Analysis only:** no file of the library was changed, and nothing has been reported upstream yet.

## Summary

All 2,699 hypotheses (2,551 in 1,577 public theorems, 148 in 94 private ones) are decided, every removable and
necessary verdict with a kernel-checked Lean proof using only the standard axioms: **2,593 necessary, 105 removable,
1 independent, 0 unresolved.**

| Folder | Theorems | Hypotheses | Necessary | Removable | Independent |
|---|---|---|---|---|---|
| Foundations | 546 | 864 | 851 | 12 | 1 |
| Computability | 483 | 765 | 732 | 33 | 0 |
| Languages | 380 | 633 | 610 | 23 | 0 |
| Logics | 106 | 156 | 152 | 4 | 0 |
| Crypto | 64 | 121 | 101 | 20 | 0 |
| MachineLearning | 45 | 89 | 81 | 8 | 0 |
| Algorithms | 35 | 55 | 53 | 2 | 0 |
| Probability | 12 | 16 | 13 | 3 | 0 |
| **total** | **1,671** | **2,699** | **2,593** | **105** | **1** |

## How the verdicts were reached

| Source | Necessary | Removable |
|---|---|---|
| hand proofs by AI agents (a random-row probe, 17 cluster agents, tails) and the main session | 2,074 | 98 |
| `HypCheck.lean` v11.1 (with Mathlib tactics and CSLib models) | 451 | 7 |
| transitive necessity and twins | 68 | |

Only 20% of the hypotheses have counterexample values for all their data binders (λ-terms, labelled transition
systems, sets, ω-sequences, circuits, … have none built in), so most verdicts needed hand proofs.

## Removable hypotheses (105)

Full list with a one-line reason each: `results/removable_review.md`. Patterns:
- boundary hypotheses where the small cases hold anyway (`1 < n`, `0 < n`, `f 0 = 0`, `k ≤ n − m`);
- `Finite`, `Nonempty`, `IsOrderedRing`, `MeasurableSingletonClass`, `IsTrans` instances that are unneeded or
  derivable; notably 15 × `[Nonempty Output]` in `Cslib.Crypto.PRG.Generator`, derivable from `[Nonempty Seed]` and
  the generator, and `[IsOrderedRing R]` in `Polynomial.monotone_eval`/`eval_mono`;
- local-closure premises in the locally nameless λ-calculus (a term that is not locally closed has no reduction
  step);
- Fsub context well-formedness premises (`Ty.Wf` depends only on lookups);
- pairs where each hypothesis implies the other (`Fsub.Ty.Wf.perm_env`, `URM.evalState_toStandardForm_regs`,
  `uniformOfFintype_map_equiv`, `hypothesisError_eq_add`): each removable on its own, not both.

**Pairs.** 12 of the 93 theorems with a removable hypothesis have two; every pair is decided by a kernel-checked proof
(`checks/J1c0Hand.lean`, `results/removable_pairs.jsonl`, checker `scripts/check_pairs.py`). 7 are jointly removable
(`Nat.segment_zero`, `nfa_single_start_accept_eq_regex`, `Shannon.exists_hard_function`, `omega_forall_actions`,
`sn_abs_app_multiApp`, `Standard.abs_subst`, `Standard.subst`), 5 are not (`unique_minimal`,
`evalState_toStandardForm_regs`, `uniformOfFintype_map_equiv`, `Fsub.Ty.Wf.perm_env`, `hypothesisError_eq_add`).

## Necessary hypotheses that took large constructions

- **16 FLP rows keeping `OnePseudoConsensus`** (`checks/F1c0Hand.lean`, about 1,400 lines): a concrete algorithm with
  `PseudoConsensus 1`, single-decree Paxos on `Fin 3`, with safety by an invariant and liveness by ticking past the
  partner's promise.
- **19 PAC-learning rows** (`checks/P1c0Hand.lean`): one construction on ℕ × Bool for all of them; no randomized
  learner succeeds at (ε, δ) = (1/8, 1/3) for any sample size (No-Free-Lunch, averaging over tail labellings).
- **3 measure rows** (`map_graph_eq_one`, `pi_map_graph_eq_one`, `ae_mem_versionSpace_of_realizable`;
  `checks/M1c0Hand.lean`): ℝ with the Borel and with the discrete σ-algebra; the graph of `x ↦ x + t₀` is measurable
  but the map `x ↦ (x, x + t₀)` is not a.e. measurable, so `P.map` is Mathlib's junk Dirac mass.
- **`IsApplicativeHom.map_seqRight_of_map_seq_map_map`** idx 7 (private; `checks/A1c0Hand.lean`): `m = Id`,
  `n = Const (Function.End Bool)`, every type sent to the constant map "the type is not a subsingleton".

## Independent (1)

`IsApplicativeHom.map_seqLeft_of_map_seq_map_map` idx 7 (`map_map`, private), kind `type-identity`, argument only.
Lean support: `A1c0.msl7_of_weight` (any type weight with c(A → B) = c(B) − c(A) and c(Unit) ≠ 0 refutes `T'`) and
`A1c0.seqLeft_of_unit_eqs` (`T'` follows from the type equalities `(PUnit → α) = α` and `(α → PUnit) = PUnit`, which
hold in a modified set model). The consistency of `T'` is argued, not proved.

## Library-specific method notes

- Tools run natively (`tools/`): under `lean --run`, importing `Cslib` cost 1.6–1.9 GB per process, natively about
  0.15 GB.
- `HypCheck.lean` v11.1 adds Mathlib/Aesop tactics parsed at run time (`aesop`, `tauto`, `linarith`, `positivity`,
  `norm_num`; `nofun` for refutations) and the models `scripts/models_cslib.txt` (λ-terms, SKI, transition systems on
  ℕ/Bool, relations, sets and finsets, ω-sequences).
- **Soundness fix in v11.1:** a term-elaborating tactic such as `nofun` can log an error and recover with `sorry` inside
  an auxiliary declaration. v11 reported 32 bogus necessary verdicts this way; all were caught by the stored-proof
  recheck (`proof_ok: false`). v11.1 rejects any tactic result that logs an error or contains `sorry`.

## Caveats

- Each hypothesis is checked on its own, except the 12 pairs above.
- Removing a hypothesis from a public lemma breaks its callers.
- No CSLib defect beyond unneeded hypotheses was found (`Findings.md`).

## Where things are

| What | Where |
|---|---|
| All verdicts | `results/public.jsonl`, `results/private.jsonl` (+ `_removable`, `_independent`) |
| Removable list and pairs | `results/removable_review.md`, `results/removable_pairs.jsonl` |
| Stored proofs | `checks/*.lean`; tool proofs in `proofs/tool/full/` |
