# Results: Mathlib.Logic and Mathlib.Basic

Which Prop-valued hypotheses of the theorems in `Mathlib.Logic` and `Mathlib.Basic` are needed? How verdicts are
defined, found and checked: `../../Methods.md`.

- **Library version:** Mathlib `master` at commit `bbff2954fe5` (2026-11-14), the same checkout as
  `libs/mathlib-data`.
- **Toolchain:** `leanprover/lean4:v4.36.0-rc2`.
- **Scope:** all theorems with a Prop-valued parameter in modules under `Mathlib.Logic` and `Mathlib.Basic`.
- **Analysis only:** no file of the library was changed.

## Summary

All 2,734 hypotheses (2,728 in 1,917 public theorems, 6 in 6 private ones) are decided, every verdict with a
kernel-checked Lean proof using only the standard axioms: **2,685 necessary, 49 removable, 0 independent,
0 unresolved.**

## Results by folder

| Folder | Theorems | Hypotheses | Necessary | Removable |
|---|---|---|---|---|
| Basic.ENNReal | 369 | 580 | 576 | 4 |
| Logic.Function | 268 | 356 | 352 | 4 |
| Logic.Equiv | 264 | 348 | 338 | 10 |
| Basic.Real | 179 | 265 | 241 | 24 |
| Logic.Relation | 113 | 167 | 167 | 0 |
| Basic.Logic | 106 | 160 | 160 | 0 |
| Basic.NNReal | 92 | 112 | 111 | 1 |
| Basic.Rel | 80 | 109 | 109 | 0 |
| Basic.Finite | 60 | 93 | 92 | 1 |
| Basic.Countable | 54 | 73 | 73 | 0 |
| Logic.Small | 47 | 70 | 70 | 0 |
| Basic.Nontrivial | 28 | 40 | 40 | 0 |
| 20 smaller folders | 263 | 361 | 356 | 5 |
| **total** | **1,923** | **2,734** | **2,685** | **49** |

## How the verdicts were reached

| Source | Necessary | Removable |
|---|---|---|
| hand proofs by AI agents (one wave of 9 clusters) and the main session | 1,400 | 32 |
| `HypCheck.lean` (fast pass, then a pass with models) | 1,214 | 17 |
| transitive necessity and twins | 71 | |

## Removable hypotheses (49)

- Found by the tool (17): mostly dependent hypotheses that always hold (`Nonempty α` in `invFun_eq` and the
  `sometimes_*` lemmas, optional parameters, `0 ≤ ↑a`, `↑x ∈ p`), and `p.HolderTriple q r` in six
  `NNReal.HolderTriple.*nonneg*` lemmas whose conclusion holds for all non-negative reals.
- Found by agents (32): `Function.Injective.extend_comp`, `Unique.ext`, `EquivLike.coe_injective'` (two hypotheses,
  each removable alone but not both), `Equiv.optionSubtype_apply_apply`, `[NeZero n]` next to a `Fin n` binder
  (5 lemmas), scalar-tower instances in `ENNReal.coe_smul`/`smul_top`, `y ≠ ⊤` in
  `ENNReal.exists_mem_Ico_zpow`/`Ioc_zpow`, `IsStrictOrderedRing α` in the eight `Real.*smul*_of_nonneg/nonpos`
  lemmas.

## Necessary hypotheses worth noting

`IsOrderedModule α ℝ` in `Real.sInf_smul_of_nonpos`, `Real.sSup_smul_of_nonpos`, `Real.smul_iSup_of_nonpos` and
`Real.smul_iInf_of_nonpos`: refuted with α = ℚ(√2), ordered via √2 but acting on ℝ via −√2 (`checks/T1c0Hand.lean`).

## Library-specific method notes

- Tool: kit `HypCheck.lean` v12 with the kit models, `scripts/models_mathlib-data.txt` and
  `scripts/models_mathlib-logic-basic.txt`.
- Tools and hand files import a slim module set (`HCImportsM`: the import set of `../mathlib-data` plus the 9 Logic/Basic
  modules it misses, built from `runs/hcimports/`) instead of all of Mathlib.

## Caveats

- Each hypothesis is checked on its own; joint removal is not checked for the 4 theorems with two or more removable
  hypotheses (`EquivLike.coe_injective'`, `finAddFlip_apply_mk_left`, `Archimedean.embedRealFun_add`,
  `Archimedean.embedRealFun_zero`).
- Removing a hypothesis from a public lemma breaks its callers.

## Where things are

| What | Where |
|---|---|
| All verdicts | `results/public.jsonl`, `results/private.jsonl` (+ `_removable`) |
| Stored proofs | `checks/*.lean`; tool proofs in `proofs/tool/` |
