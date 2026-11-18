# Results: combinatorial-games

Which Prop-valued hypotheses of the theorems in
[combinatorial-games](https://github.com/vihdzp/combinatorial-games) are needed? How verdicts are defined, found and
checked: `../../Methods.md`; what differs for this library: `Methods.md`.

- **Library version:** commit `e8c9538` (2026-11-07, "feat: successor and predecessor functions on sign sequences
  (#521)"). Upstream has moved on since; the results refer to this commit.
- **Toolchain:** `leanprover/lean4:v4.36.0-rc2`.
- **Scope:** every theorem with a Prop-valued parameter in `CombinatorialGames`, public and private theorems counted
  separately; compiler-generated lemmas without a source position excluded.
- **Analysis only:** no file of the library was changed, and nothing has been reported upstream yet.

## Summary

Of 2,597 hypotheses (2,196 in 1,192 public theorems, 401 in 160 private ones), **2,538 are decided (97.7%): 2,392
necessary, 146 removable, 0 independent; 59 are unresolved.** Every removable and necessary verdict has a
kernel-checked Lean proof that uses only the standard axioms.

| Folder | Theorems | Hypotheses | Necessary | Removable | Unresolved |
|---|---|---|---|---|---|
| Surreal | 413 | 973 | 845 | 77 | 51 |
| Game | 432 | 784 | 762 | 22 | 0 |
| Nimber | 318 | 558 | 521 | 29 | 8 |
| SignExpansion | 95 | 126 | 117 | 9 | 0 |
| Mathlib (the library's Mathlib additions) | 60 | 111 | 102 | 9 | 0 |
| NatOrdinal | 34 | 45 | 45 | 0 | 0 |
| **total** | **1,352** | **2,597** | **2,392** | **146** | **59** |
| of which public | 1,192 | 2,196 | 2,081 | 83 | 32 |
| of which private | 160 | 401 | 311 | 63 | 27 |

## How the verdicts were reached

| Source | Necessary | Removable |
|---|---|---|
| hand proofs by AI agents (probe, 17 cluster agents, three rounds of tail agents) | 1,728 | 110 |
| `HypCheck.lean` v12.3 (tactics, small values, the library's models, `game_cmp`) | 608 | 36 |
| `refute_dep` generator for dependent hypotheses | 13 | |
| transitive necessity and twins | 43 | |

Before any agent ran, the mechanical stage had decided 676 hypotheses (26%); the rest needed hand proofs. Most hypotheses here are about games
(`Numeric`, `Short`, `Impartial`, `Small`, ordinal and nimber field conditions), whose counterexamples are specific
games, cuts or nimbers that a generic tool does not build.

Run history (measured):

| Phase | What ran | Cost | Decided |
|---|---|---|---|
| Mechanical (module system, `server` olean level) | inventory, structural checks, HypCheck on all rows (public: 38 min with 6 workers; private: 6 workers, then a rerun of the killed part with 2), proof repair, flow | machine time only | 663 |
| `refute_dep` | generated refutations of the 499 dependent rows | minutes | 13 |
| Probe | 2 agents × 50 random rows | 475k tokens | 85 |
| Cluster waves | 17 clusters by module, ≤ 6 agents at once, 3–36 min each | 3.59M tokens (2.2k per decided row) | 1,665 |
| Tail rounds | 3 + 2 + 3 agents on the rows earlier agents gave up on | 1.66M tokens | 96 |

## Removable hypotheses (146)

The full list, with a one-line reason each, is in `results/removable_review.md`. Patterns:
- **Instance hypotheses that hold anyway or follow from the others.** Examples: `Small` instances on graphs and move
  sets (`GameGraph.neg_toLGame` and siblings, `LGame.hom_unique`/`hom_unique_apply`, where uniqueness follows by a
  bisimulation), `[Numeric (toIGame x)]` on dyadics, `[Nonempty α]` in `Order.IsEta.infinite` (it follows from
  `1 < c` and `IsEta c α`), and `WellFoundedLT α` in `Pi.Lex.neg_le_neg_iff`, `neg_le_iff` and `le_neg_iff`.
- **Impartiality of products.** `x * y` is impartial as soon as one factor is (new lemma, `checks/W1c2Hand.lean`
  `key`: its Grundy value is `symG x * grundy y`). Hence one of the two `Impartial` hypotheses of
  `IGame.Impartial.mul`, `mulOption`, `mul_congr_left` and `mul_congr_right` is unneeded.
- **Nimber field hypotheses implied by the others.**
  - A new lemma (`checks/T1c0Hand.lean` `fieldOf`): `1 < x` together with `X² ≤ leastNoRoots x` already makes x a
    field. It removes `IsRing`/`IsField` hypotheses from 10 lemmas (`IsRing.eval_eq_of_lt`, `IsRing.pow_eq`,
    `IsField.sqrt_lt`, `IsField.root_lt`, the degree-four lemmas, …).
  - `IsGroup x` in `IsGroup.mul_eq_of_lt`: the other hypotheses force x to be a power of 4 (`checks/T3c2Hand.lean`).
  - `IsField.eq_prod_roots_of_lt_leastNoRoots`: the nimbers are algebraically closed, so every polynomial splits.
- **Sign expansions.** The `[x.Small]` instance of `Small.length_eq`, `succ_apply_of_gt` and `pred_apply_of_gt`
  follows from the length hypothesis.
- **Surreal powers.** In `numeric_of_forall_mk_ne_mk`, one of `Hl`/`Hr` suffices and `0 < x` is not needed.
  `mul_wpow_lt_mul_wpow_add_mul_wpow` also holds for summands of either sign.
- **Private proof machinery** (63 rows): induction hypotheses and side conditions that are instances of results
  proved later (`Numeric.inv`, `mul_inv_cancel`, `wpow_add_equiv`), or follow from the other hypotheses.

Removing a hypothesis from a public lemma changes its callers, and some hypotheses are there by design. Joint removal
was not checked: 34 theorems have two or more removable hypotheses, and each is removable only on its own.

## Necessary hypotheses that took real constructions

- **Multiplication of games does not respect equivalence.**
  - Non-numeric factor: `W = {↑ | }` is equivalent to 1, but `W · ½` is not equivalent to ½ (`checks/W3c2Hand.lean`).
  - Even both factors numeric and equivalent: `{∅ | 2}` is equivalent to 0, but its product with ⋆ is equivalent to ⋆
    (`checks/W3c1Hand.lean`).
  - Sign rule: `{-1, 0 | }` is numeric and equivalent to 1, but its product with ↑ is fuzzy with 0.

  These refute the `Numeric` instance hypotheses of the congruence, sign and monotonicity lemmas of `Surreal.Multiplication`.
- **A Cut that is not Small** (`checks/W2c4Hand.lean` `notSmallX`): the gap of the sign sequence that is + at limit
  and − at successor ordinals. It decides every row that needs `¬ x.Small` for cuts.
- **∗ω is not algebraically closed** (`checks/T2c1Hand.lean` `mainY`): X³ + X + 1 has no root below any ∗(2^2^n), and
  each ∗(2^2^n) is a field. This proves the library's `proof_wanted IsField.two_two_pow` (see `Findings.md`).
- **Galois theory**: ℚ(∛2) inside ℝ for a finite non-Galois extension, and the Frobenius subgroup of Gal(F̄₂/F₂) for a
  non-closed subgroup of an infinite Galois group (`finrank_fixedField_eq_index`).
- **Infinite nimber rings that are not fields**: ∗(T^ω) for T the least algebraically closed nimber, and the Laurent
  ring above it (`checks/T1c0Hand.lean`).

## Unresolved (59)

Listed with the obstruction each in `results/unresolved_review.md`.

| Group | Rows | What a decision would need |
|---|---|---|
| Surreal powers: dyadic-coefficient variants, `mulOption_lt_wpow`-type induction steps | 21 | order estimates for k·ω^y with general dyadic k and non-numeric y |
| Surreal powers: `wpow_pos`, `wpow_nonneg`, private `wpow_pos'` | 3 | likely removable: needs 0 < r·ω^z for every positive dyadic r and every game z |
| Surreal division: `div_lt_iff` family, `div_congr*`, `inv_pos`/`inv_neg`, `mul_inv_self` | 16 | products with y⁻¹ for numeric y with a positive option, which has infinitely many options |
| Private surreal multiplication/division induction steps and identities | 11 | models satisfying the induction hypotheses with a non-numeric factor; one is a 4-factor regrouping identity |
| Nimber: `SmallDegree.Inseparable` | 6 | the field above ∗ω: that its first extension is cubic (the library's `proof_wanted leastNoRoots_omega0`) and an Artin–Schreier-type lemma |
| Nimber: `IsGroup.mul_le_of_forall_lt` idx 6, `IsField.sq_of_pow_four` idx 1 | 2 | probably removable: a leading-term theory of nim products of powers of 2, resp. that degrees of `leastNoRoots` are prime (Lenstra) |

## Caveats

- Each hypothesis is checked on its own; joint removal was not checked (see above).
- "Unresolved" says nothing either way.
- A removable verdict for a dependent hypothesis means it follows from the others, so it can be replaced by a derived
  proof; the statement may still mention it.
- Private theorems are part of the library's proof machinery; their removable hypotheses matter only to its authors.

## Files

- `results/public.jsonl`, `results/private.jsonl`: one JSON line per hypothesis (`theorem`, `idx` = position among the
  binders from 0, `name`, `type`, `status`, `found_by`, and where the proof is: `proofs_file` with the declaration in
  `proof`, or `proof_file`/`proof_decl`); `*_removable.jsonl` and `*_unresolved.jsonl` hold the subsets.
- `results/removable_review.md`, `results/unresolved_review.md`: the lists above.
- `checks/`: every stored proof file that backs a hand or flow verdict. `python3 scripts/check_hand.py FILE.lean
  VERDICTS.jsonl` checks that each declaration proves exactly the stated verdict with standard axioms only.
- `python3 scripts/recheck.py`: recompile every stored proof file against the library (set `HC_LIBDIR` in `hc.env` first).
