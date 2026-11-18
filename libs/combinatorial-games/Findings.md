# Findings: combinatorial-games

Library issues beyond unneeded hypotheses, found during the analysis of commit `e8c9538`. The removable hypotheses
themselves are listed in `results/removable_review.md`. Nothing has been reported upstream yet.

## Statement typos (copy-paste)

Each statement is true and proved, but says something other than its name.

| Declaration | Where | What it says | Probably meant |
|---|---|---|---|
| `SignExpansion.pred_apply_of_gt` | `SignExpansion/Basic.lean:790` | `succ x o = -1` (a verbatim copy of `succ_apply_of_gt`, line 695) | a statement about `pred x o` |
| `IGame.Short.wsubposition` | `Game/Classes.lean:541` | `[Numeric x] … : Numeric y` (copied from `Numeric.wsubposition`, line 372) | `[Short x] … : Short y` |
| `IGame.Dicotic.sub` | `Game/Classes.lean:132` | `Dicotic (x + y)` (the same as `Dicotic.add`) | `Dicotic (x - y)`, as in `Impartial.sub` (line 219) |

## A `proof_wanted` that can be filled

- `proof_wanted IsField.two_two_pow (n : ℕ) : IsField (∗(2 ^ 2 ^ n))` (`Nimber/SimplestExtension/Basic.lean:683`).
  It is proved in `checks/T2c1Hand.lean` (`mainY`, line 182) by an elementary induction.
  - A finite field of characteristic 2 misses some value of t² + t, so `leastNoRoots` has degree 2, and
    `pow_natDegree_leastNoRoots` gives the next field ∗(y²).
  - Every element below ∗(y²) is b·y + a.
  - The same induction shows X³ + X + 1 has no root below ∗ω, so ∗ω is not algebraically closed. This is a weaker form
    of `proof_wanted leastNoRoots_omega0` (`Nimber/SimplestExtension/Algebraic.lean:168`): it gives degree ≤ 3, not
    the exact polynomial.

  The proof uses only the library's own lemmas and could be upstreamed after cleanup.

## Removable hypotheses worth an upstream look

Public lemmas whose hypothesis is unneeded in a way that generalises the lemma (full list: `results/removable_review.md`):
- `IGame.Impartial.mul`, `mulOption`, `mul_congr_left`, `mul_congr_right`: only one factor has to be impartial, since
  x · y is impartial whenever y is (`checks/W1c2Hand.lean` `key`; there is no such sibling in the library).
- `LGame.hom_unique`, `hom_unique_apply`: the `Small` instances on `mov` are unneeded (bisimulation argument,
  `checks/W1c3Hand.lean` `homUnique`).
- `Surreal.numeric_of_forall_mk_ne_mk` (`Surreal/Pow.lean:905`): each of `0 < x`, `Hl`, `Hr` is unneeded on its own (one of `Hl`/`Hr` suffices).
- `Pi.Lex.neg_le_neg_iff`, `neg_le_iff`, `le_neg_iff`: `WellFoundedLT α` is unneeded (the `lt` versions already lack it).
- Nimber: a new lemma `fieldOf` (`checks/T1c0Hand.lean:704`) shows that `1 < x` and `X² ≤ leastNoRoots x` imply
  `IsField x`. With it, the `IsRing`/`IsField` hypotheses of `IsRing.eval_eq_of_lt`, `IsRing.pow_mul_eq`,
  `IsRing.pow_eq`, `IsField.sqrt_lt`, `IsField.root_lt` and the degree-four lemmas of `SmallDegree.Quartic` are
  unneeded.
- `Nimber.IsGroup.mul_eq_of_lt`/`mul_eq_of_lt'`: each of `hx : IsGroup x` (the other hypotheses force x to be a
  power of 4), `hz`, `hyx`, `hyz` is unneeded on its own (`checks/T1c0Hand.lean` `mulEqGen`, `checks/T3c2Hand.lean`
  `mulEqNoHx`).
- `Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots`: each of `IsField x`, `p < leastNoRoots x` and the coefficient
  bound is unneeded on its own: the nimbers are algebraically closed, so every polynomial splits.
