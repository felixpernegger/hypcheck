# Results: the Lean 4 core library

Which Prop-valued hypotheses of the theorems in `Init`, `Std`, `Lean` and `Lake` are needed? How the verdicts are
defined, found and checked: `../../Methods.md`.

- **Library version:** lean4 at commit `a2ec8251` (2026-11-05), analysed with its own stage1 build.
- **Analysis only:** no file of the library was changed.
- **Data:** `results/init_all.jsonl`, `results/std.jsonl`, `results/lean_lake.jsonl`,
  `results/internal_names_and_lake_unimported.jsonl`, private theorems in `results/private/private_all.jsonl`;
  `*_removable.jsonl` and `*_independent.jsonl` are the same rows filtered by status.

## Summary

Every hypothesis is decided, and every removable and necessary verdict has a kernel-checked Lean proof in the
repository (`checks/`, `proofs/`).

| Part | Theorems | Hypotheses | Necessary | Removable | Independent | Unresolved |
|---|---|---|---|---|---|---|
| Init | 11,159 | 18,424 | 16,643 | 1,398 | 383 | 0 |
| Std | 18,094 | 46,916 | 40,006 | 6,864 | 46 | 0 |
| Lean and Lake | 40 | 50 | 46 | 1 | 3 | 0 |
| **public total** | **29,293** | **65,390** | **56,695** | **8,263** | **432** | **0** |
| private theorems (counted separately) | 613 | 1,243 | 1,126 | 106 | 11 | 0 |

"Lean and Lake" includes 2 private theorems in Lake modules that the `Lake` root does not import (3 hypotheses, all
necessary; `results/internal_names_and_lake_unimported.jsonl`). Compiler-generated lemmas with a source position, such
as the 4 `Std.DTreeMap.Internal.Impl.*.match_1.congr` lemmas, are counted with their library part.

## Init by folder

| Area | Theorems | Hypotheses | Necessary | Removable | Independent |
|---|---|---|---|---|---|
| Init.Grind | 861 | 2,382 | 2,251 | 130 | 1 |
| Init.Data.Range | 831 | 2,089 | 1,575 | 509 | 5 |
| Init.Data.List | 1,340 | 1,867 | 1,764 | 103 | 0 |
| Init.Data.Iterators | 583 | 1,641 | 1,134 | 323 | 184 |
| Init.Data.String | 1,030 | 1,406 | 1,357 | 46 | 3 |
| Init.Data.Int | 849 | 1,290 | 1,259 | 31 | 0 |
| Init.Data.Array | 836 | 1,163 | 1,110 | 52 | 1 |
| Init.Data.SInt | 529 | 867 | 775 | 0 | 92 |
| Init.Data.Nat | 660 | 848 | 833 | 15 | 0 |
| Init.Data.Vector | 593 | 787 | 762 | 25 | 0 |
| Init.Data.UInt | 641 | 785 | 692 | 2 | 91 |
| Init.Data.Order | 356 | 581 | 576 | 5 | 0 |
| Init.Data.BitVec | 412 | 480 | 444 | 36 | 0 |
| Init.Data.Option | 222 | 271 | 258 | 13 | 0 |
| Init.Data.Fin | 157 | 187 | 149 | 38 | 0 |
| Init.Data.Rat | 90 | 144 | 140 | 4 | 0 |
| other Init.Data folders (20) | 252 | 372 | 345 | 24 | 3 |
| Init outside Data and Grind | 917 | 1,264 | 1,219 | 42 | 3 |

## Std by folder

| Area | Theorems | Hypotheses | Necessary | Removable | Independent |
|---|---|---|---|---|---|
| Std.Data | 17,086 | 44,543 | 37,934 | 6,566 | 43 |
| Std.Do | 273 | 746 | 640 | 103 | 3 |
| Std.WP | 126 | 433 | 396 | 37 | 0 |
| Std.Tactic | 218 | 426 | 371 | 55 | 0 |
| Std.Sat | 202 | 395 | 338 | 57 | 0 |
| Std.Internal | 169 | 344 | 299 | 45 | 0 |
| Std.Time, Std.Http, Std.Sync | 20 | 29 | 28 | 1 | 0 |

## How the verdicts were reached

| Source | Necessary | Removable |
|---|---|---|
| hand proofs by AI agents (cluster passes) | 27,389 | 6,848 |
| `HypCheck.lean` tool runs | 18,480 | 304 |
| generated tactic `refute_dep` (dependent Std.Data rows) | 8,107 | |
| transitive necessity and twins | 3,845 | |
| unused and transitively unused in the library's own proof | | 1,146 |
| instance derivable from the other binders | | 60 |
| reproof (library proof minus the binder) | | 11 |

Counts include the private theorems. 18,544 of the decided hypotheses are dependent (17,599 necessary, 799 removable,
146 independent).

## Removable hypotheses

The full lists are `results/init_all_removable.jsonl`, `results/std_removable.jsonl` and the removable rows of
`results/private/private_all.jsonl`, each with the proof's location. 1,128 of the public ones (1,146 with private theorems) are hypotheses that the library's
own proof does not use (directly or only by passing them to other unused hypotheses), mostly lawfulness instances.
Typical patterns:

**Init**
- Arithmetic side conditions: `Nat.lcm_le_mul` (`hm` and `hn`, each alone; also jointly removable),
  `Nat.mul_sub_mul_div_of_dvd`, `Nat.div_lt_div_right`, `Int.toNat_sub''`, `Int.neg_tdiv_of_dvd`,
  `Nat.Simproc.le_add_ge`, BitVec width conditions.
- Dependent index bounds that follow from other hypotheses: `List.getElem_append_left` (`h'`) and its `Array` and
  `ByteArray` versions, the `eraseIdx`/`insertIdx` lemmas of `Array` and `Vector`, `List.getElem_cons_zero`.
- Non-emptiness conditions visible from the form of the list: `h : a :: l ≠ []` in `List.head_cons`,
  `List.getLast_eq_getLastD`, `List.min_cons`, `List.max_cons`; `l ++ l' ≠ []` when one part is non-empty;
  `scanl`/`scanr` head and last lemmas; `xs ≠ []` in the `minIdxOn`/`maxIdxOn` lemmas.
- `Option`/`Sum` accessors whose `isSome`/`isLeft` hypothesis is visible from the form (`Option.get_some`,
  `Sum.getLeft_inl`); the eight `String.Pos`/`String.Slice.Pos` `*_slice_*` lemmas (`p₀ ≤ p₁` is derivable).
- Range finiteness that the other hypotheses imply (most of the 509 in Init.Data.Range), and `[LawfulMonad n]` in the
  three `Rxc/Rxo/Rxi.Iterator.instLawfulIteratorLoop` instances.
- Class assumptions a lemma does not need: `[Std.Trichotomous (· < ·)]` in `List`/`Array`/`Vector.append_left_le`,
  `[Std.LeftIdentity …]` in `Vector.sum_append`/`prod_append`, `[LawfulUpwardEnumerable …]` in several range lemmas,
  `[LawfulGetElem]` in `of_getElem_eq`.
- Removable by design only (the hypothesis is the lemma's subject): `proof_irrel`, `cast_eq`, `Subtype.eta`,
  `Fin.eta`, `Fin.cast_refl`, `imp_intro`, `Lean.Grind.nestedProof_congr`.

**Std** (most families come in up to six variants: `HashMap`, `DHashMap`, `TreeMap`, `DTreeMap`, `TreeSet`, each
plain, `Raw` and `Ext`)
- Lookups that follow the same search path for any comparison: `isEmpty`, `get!`, `getKey!`, `contains` do not need
  `TransCmp`; `length_keys`, `size_keysArray` neither.
- `head?_keys`, `head?_toList`: each of `[LawfulOrderCmp cmp]`, `[LawfulOrderMin α]`,
  `[LawfulOrderLeftLeaningMin α]`, `[LawfulEqCmp cmp]` is removable on its own (joint removal not checked).
- `mem_of_get_eq`: `m.get k w = v` is unneeded, the conclusion `k ∈ m` already follows from `w`.
- `insertIfNew` never lowers the size field, `map`/`filter` keep the buckets, `diff` works with any second map.
- Dependent membership premises that follow from list membership (`k' ∈ t.insertMany l`, `k' ∈ ofList l`) and
  derivable keys in `getKey_minKey`/`getKey_maxKey`, `get_min`/`get_max`.
- `Std.Internal.List.*_of_isEmpty` and most other `Std.Internal.List` lemmas do not need `DistinctKeys`.
- `TransCmp` derived from `LawfulOrderCmp` + `LawfulOrderMin` + `LawfulOrderLeftLeaningMin`; `TransOrd` likewise.
- Dependent bounds such as `curr ≤ w`, `idx < aig.decls.size` in `Std.Sat.AIG` and `bv_decide` internals.

**Private theorems:** `Int.Internal.Linear` sign conditions (`k > 0`, `d > 0`, `d > 1` in `poly_eq_zero_eq_false`,
`cooper_unsat'_helper`, `ex_of_dvd`, `cooper_unsat'`); range finiteness, `wf` and `[LawfulMonad n]` of `loopWf_eq`;
`Duration.ofNanoseconds.mod_nonpos` (`b ≥ 0`); both msb hypotheses of
`BitVec.neg_udiv_eq_intMin_iff_eq_intMin_eq_one_of_msb_eq_true`; the `omega` hypothesis of
`Std.Sat.AIG.CNF.*.IsExtensionBy_rfl`, which is a slip in the source (`Findings.md`).

## Independent hypotheses (443)

| Kind | Init | Std | Lean/Lake | private | Lean evidence |
|---|---|---|---|---|---|
| `platform` (`numBits` = 32 or 64) | 183 | | | | both halves proved, and a swap certificate for each (`certs/platform/`) |
| `opaque-fixpoint` | 195 | 40 | | 11 | support lemma; consistency by a model argument |
| `type-identity` | 5 | 6 | | | argument only |
| `opaque-constant` (Lake `ConfigDecl`) | | | 3 | | argument only |

The platform rows are mostly `USize`/`ISize` lemmas in Init.Data.UInt and Init.Data.SInt whose statement holds on one
word size only. The opaque-fixpoint rows are iterator lemmas (Init.Data.Iterators, Std.Data.Iterators) where dropping
`Finite` or `Productive` leaves both sides as unrelated values of the opaque fixpoint.

## Caveats and open points

- Each hypothesis is checked on its own; joint removal was checked only for `Nat.lcm_le_mul` (jointly removable) and
  `Nat.mul_add_mul_div_of_dvd` (not).
- Stored proofs were checked one file at a time when they were merged. All proof files were last recompiled together
  on 2026-11-07; later files were each checked at merge time, and a sample of 40 of the 721 proof files in `proofs/` and `checks/` was recompiled
  on 2026-11-14/15 (all clean, standard axioms only). `scripts/audit_proofs.py` runs the full row-to-proof audit
  (about 2.5 hours on three lanes); it has not been run to the end.
- The narrow-variant caveat for dependent necessary verdicts (`../../Methods.md`, Caveats) applies.
- Library defects found along the way: `Findings.md`.
