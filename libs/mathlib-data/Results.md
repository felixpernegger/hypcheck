# Results: Mathlib.Data

Which Prop-valued hypotheses of the theorems in `Mathlib.Data` are needed? How verdicts are defined, found and
checked: `../../Methods.md`.

- **Library version:** Mathlib `master` at commit `bbff2954fe5` (2026-11-14).
- **Toolchain:** `leanprover/lean4:v4.36.0-rc2`.
- **Scope:** all theorems with a Prop-valued parameter in modules under `Mathlib.Data`.
- **Analysis only:** no file of the library was changed, and nothing has been reported upstream yet.

## Summary

All 12,276 hypotheses (12,202 in 8,078 public theorems, 74 in 37 private ones) are decided, every removable and
necessary verdict with a kernel-checked Lean proof using only the standard axioms.

| Verdict | Hypotheses |
|---|---|
| **Necessary** | 11,844 |
| **Removable** | 428 (190 that can be dropped outright, 238 dependent ones that follow from the other binders) |
| **Independent** | 4 |
| **Unresolved** | 0 |

## Results by folder

Public and private theorems combined (private: 69 necessary, 5 removable).

| Folder | Theorems | Hypotheses | Necessary | Removable | Independent |
|---|---|---|---|---|---|
| Set | 1,601 | 2,484 | 2,435 | 48 | 1 |
| Finset | 1,129 | 1,754 | 1,704 | 50 | 0 |
| Nat | 1,041 | 1,656 | 1,587 | 69 | 0 |
| List | 1,004 | 1,548 | 1,497 | 51 | 0 |
| Multiset | 315 | 446 | 443 | 3 | 0 |
| Fin | 309 | 401 | 346 | 55 | 0 |
| Finsupp | 275 | 390 | 365 | 25 | 0 |
| Int | 235 | 366 | 343 | 23 | 0 |
| Fintype | 218 | 345 | 340 | 3 | 2 |
| EReal | 155 | 312 | 312 | 0 | 0 |
| Ordmap | 124 | 276 | 262 | 14 | 0 |
| DFinsupp | 159 | 234 | 227 | 7 | 0 |
| Rat | 180 | 229 | 219 | 10 | 0 |
| Seq | 141 | 209 | 203 | 6 | 0 |
| ZMod | 142 | 186 | 182 | 4 | 0 |
| ENat | 126 | 178 | 168 | 10 | 0 |
| 36 smaller folders | 961 | 1,262 | 1,211 | 50 | 1 |
| **total** | **8,115** | **12,276** | **11,844** | **428** | **4** |

## How the verdicts were reached

| Source | Necessary | Removable |
|---|---|---|
| `HypCheck.lean` (a fast pass over all theorems, then a pass with Finset/Multiset/Finsupp/WithBot/Sym2/Seq models) | 6,221 | 142 |
| hand proofs by AI agents (a random-row probe, then 30 cluster waves) | 5,382 | 280 |
| transitive necessity and twins | 241 | 2 |
| unused in the library's own proof, instance derivable | | 4 |

Mathlib is linted, so the structural detectors find almost nothing. Data evaluates well: small `ℕ`/`List`/`Finset`
values plus `decide +kernel` refute half of the hypotheses mechanically.

## Removable hypotheses

The 190 non-dependent ones are listed in `results/public_removable.jsonl` and `results/private_removable.jsonl`; a
selection worth an upstream change, grouped by area with the proof file, is in `Findings.md`. The 238 dependent ones follow from the other binders, e.g. `[NeZero n]` from an element of `Fin n`, or an
optional parameter that is proved by its own default. Typical non-dependent patterns:
- base conditions `1 < b` in 17 `Nat.Digits` lemmas, and `n < p ^ a` in Lucas' theorem;
- divisibility hypotheses in `Int` floor-division lemmas (`Int.div_le_iff_of_dvd_of_neg` and siblings);
- order and algebra classes a lemma does not use: `CharZero` in `Rat.cast_inv`/`cast_zpow`, `IsStrictOrderedRing`,
  `OrderedSub`, `IsOrderedCancelAddMonoid`, `[LawfulBEq]` in `List.IsPrefix.idxOf_le`;
- finiteness hypotheses that follow from others or are not used (`Set.ncard_union_lt`, `Set.Finite.ncard_biUnion`);
- hypotheses that follow from the other ones (`Finset.noncommProd_eq_pow_card` `comm`, `Sym2.other_invol` `hb`).

## Independent (4)

`Fintype.induction_empty_option` and `Finite.induction_empty_option` (`of_equiv`), `Subtype.heq_iff_coe_heq`
(`α = β`), `set_coe_cast` (dependent `s = t`): deciding them needs (dis)equalities of equinumerous types or
injectivity of type formers, which Lean can neither prove nor refute (kind `type-identity`, argument only; Lean
reductions between them in `checks/W2c3Hand.lean`).

## Library-specific method notes

- Tool: kit `HypCheck.lean` v12 with `scripts/models_mathlib-data.txt` (Finset, Multiset, Finsupp, WithBot, Sym2 and
  Seq values; 42 lines, 1,218 extra necessary verdicts).
- The tools and hand files import only the Data modules (`HCImportsM`, built from `runs/hcimports/`) instead of all of
  Mathlib: about 1.2 GB instead of 4.9 GB per process, which let eight agents run at once.

## Caveats

- Each hypothesis is checked on its own. 54 theorems have two or more removable hypotheses; joint removal is not
  checked (`Finsupp.sum_update_add` needs one of its two, so they are not jointly removable).
- Some candidates in `Findings.md` are deprecated aliases, and some generalisations would change lemma names or simp
  behaviour; review before opening pull requests.
- Removing a hypothesis from a public lemma breaks its callers.

## Where things are

| What | Where |
|---|---|
| All verdicts | `results/public.jsonl`, `results/private.jsonl` (+ `_removable`, `_independent`) |
| Upstream candidates | `Findings.md` |
| Stored proofs | `checks/*.lean`; tool proofs in `proofs/tool/` |
