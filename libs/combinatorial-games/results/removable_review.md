# Removable hypotheses (combinatorial-games)

146 hypotheses are removable: the theorem stays true without them, and a kernel-checked proof of the weakened statement is stored. Each is checked on its own: two removable hypotheses of one theorem need not be removable together (joint removal was not checked). *Private* marks a private theorem (the name is shown without its `_private.…0.` prefix). A *dependent* hypothesis is one that later parts of the statement mention; removable then means it follows from the other hypotheses.

## Game.Basic

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `IGame.Impartial.fuzzy_iff_add_fuzzy_zero` :403 | `hx` (idx 2) | x ‖ y ↔ x + y ‖ y + y and y + y ≈ 0 for impartial y; x need not be impartial (m_6) | `checks/W1c0Hand.lean` (`W1c0.m_6`) |
| `IGame.Impartial.fuzzy_iff_add_fuzzy_zero` :403 | `hy` (idx 3) | symmetric to idx 2 (fuzzy symmetric, add commutative), only x impartial needed (m_7) | `checks/W1c0Hand.lean` (`W1c0.m_7`) |

## Game.Confusion

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Game.confusionInterval_switch_of_numeric` :87 | `h` (idx 1) | for numeric x < 0, ±x ≈ 0 so confusionInterval = ∅ = Icc (-x) x (empty since x < -x) (m_12) | `checks/W1c0Hand.lean` (`W1c0.m_12`) |

## Game.Graph

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `GameGraph.neg_toLGame` :76 | `Hl` (idx 2, dependent) | the weakened statement is proved by `simp_all` | `runs/mech/search-both-server/public.proofs` |
| `GameGraph.neg_toLGame` :76 | `Hr` (idx 3, dependent) | the weakened statement is proved by `simp_all` | `runs/mech/search-both-server/public.proofs` |
| `GameGraph.neg_toIGame` :148 | `Hl` (idx 2, dependent) | the weakened statement is proved by `simp_all` | `runs/mech/search-both-server/public.proofs` |
| `GameGraph.neg_toIGame` :148 | `Hr` (idx 3, dependent) | the weakened statement is proved by `simp_all` | `runs/mech/search-both-server/public.proofs` |
| `GameGraph.impartial_toIGame` :152 | `Hl` (idx 2, dependent) | the weakened statement is proved by `simp_all` | `runs/mech/search-both-server/public.proofs` |
| `GameGraph.impartial_toIGame` :152 | `Hr` (idx 3, dependent) | the weakened statement is proved by `simp_all` | `runs/mech/search-both-server/public.proofs` |

## Game.Impartial.Multiplication

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `IGame.Impartial.mul` :65 | `inst` (idx 2) | x*y is impartial whenever y is: induction as in mul', with grundyAux p (x*y) = symG x * grundy y where symG is the Grundy value of x with all moves open to both players (helper key) | `checks/W1c2Hand.lean` (`w1c2_3`) |
| `IGame.Impartial.mul` :65 | `inst` (idx 3) | symmetric to idx 2 via mul_comm: x*y impartial whenever x is (helper key) | `checks/W1c2Hand.lean` (`w1c2_4`) |
| `IGame.Impartial.mulOption` :87 | `inst` (idx 4) | a*y, x*b, a*b each have an impartial factor, so impartial by helper key; then Impartial.sub | `checks/W1c2Hand.lean` (`w1c2_9`) |
| `IGame.Impartial.mulOption` :87 | `inst` (idx 5) | a*y (a impartial), x*b, a*b each have an impartial factor (helper key + mul_comm); then Impartial.sub | `checks/W1c2Hand.lean` (`w1c2_10`) |
| `IGame.Impartial.mulOption` :87 | `inst` (idx 6) | a*y (y impartial), x*b, a*b (b impartial) impartial by helper key; then Impartial.sub | `checks/W1c2Hand.lean` (`w1c2_11`) |
| `IGame.Impartial.mulOption` :87 | `inst` (idx 7) | a*y, x*b (x impartial), a*b (a impartial) impartial by helper key + mul_comm; then Impartial.sub | `checks/W1c2Hand.lean` (`w1c2_12`) |
| `IGame.Impartial.mul_congr_left` :92 | `inst` (idx 3) | y arbitrary: y*x1, y*x2 impartial with Grundy symG y * grundy x_i (helper key), equal since x1 ≈ x2 | `checks/W1c2Hand.lean` (`w1c2_13`) |
| `IGame.Impartial.mul_congr_right` :97 | `inst` (idx 3) | x arbitrary: x*y1, x*y2 impartial with Grundy symG x * grundy y_i (helper key), equal since y1 ≈ y2 | `checks/W1c2Hand.lean` (`w1c2_17`) |

## Game.Loopy.Basic

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `LGame.hom_unique_apply` :265 | `inst` (idx 2) | uniqueness holds by a bisimulation (eq_of_bisim with r a b := ∃ y, f y = a ∧ g y = b); smallness of mov is not used | `checks/W1c3Hand.lean` (`W1c3.c3_136`) |
| `LGame.hom_unique_apply` :265 | `inst` (idx 3) | uniqueness holds by a bisimulation (eq_of_bisim with r a b := ∃ y, f y = a ∧ g y = b); smallness of mov is not used | `checks/W1c3Hand.lean` (`W1c3.c3_137`) |
| `LGame.hom_unique` :283 | `inst` (idx 2) | uniqueness holds by a bisimulation (eq_of_bisim with r a b := ∃ y, f y = a ∧ g y = b); smallness of mov is not used | `checks/W1c3Hand.lean` (`W1c3.c3_138`) |
| `LGame.hom_unique` :283 | `inst` (idx 3) | uniqueness holds by a bisimulation (eq_of_bisim with r a b := ∃ y, f y = a ∧ g y = b); smallness of mov is not used | `checks/W1c3Hand.lean` (`W1c3.c3_139`) |

## Game.Loopy.StoppingTime

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `LGame.le_of_finite` (private) :78 | `hi` (idx 6) | the weakened statement is proved by `simp_all` | `runs/mech/search-both-server/private.proofs` |

## Mathlib.Dyadic

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Dyadic.mkRat_one` :221 | `h` (idx 1, dependent) | the weakened statement is proved by `solve_by_elim` | `runs/mech/search-both-server/public.proofs` |
| `Dyadic.mkRat_lt_mkRat` :225 | `h₁` (idx 3, dependent) | the weakened statement is proved by `assumption` | `runs/mech/search-both-server/public.proofs` |
| `Dyadic.mkRat_lt_mkRat` :225 | `h₂` (idx 4, dependent) | the weakened statement is proved by `assumption` | `runs/mech/search-both-server/public.proofs` |
| `Dyadic.mkRat_le_mkRat` :245 | `h₁` (idx 3, dependent) | the weakened statement is proved by `assumption` | `runs/mech/search-both-server/public.proofs` |
| `Dyadic.mkRat_le_mkRat` :245 | `h₂` (idx 4, dependent) | the weakened statement is proved by `assumption` | `runs/mech/search-both-server/public.proofs` |
| `Dyadic.mkRat_add_mkRat_self` :249 | `h₁` (idx 3, dependent) | the weakened statement is proved by `assumption` | `runs/mech/search-both-server/public.proofs` |
| `Dyadic.mkRat_add_mkRat_self` :249 | `h₂` (idx 4, dependent) | the weakened statement is proved by `assumption` | `runs/mech/search-both-server/public.proofs` |

## Mathlib.EtaSet

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Order.IsEta.infinite` :92 | `inst` (idx 5) | derivable: 1 < c and IsEta c alpha give Nonempty alpha (Order.IsEta.nonempty) | `checks/W1c5Hand.lean` (`w5_19`) |
| `Order.IsEta.f_mem` (private) :171 | `hsep` (idx 11) | the separation hypothesis always holds by the private lemma f_sep | `checks/W1c5Hand.lean` (`w5_70`) |

## Nimber.NatOrdinal

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Ordinal.isPrincipal_mul_opow_omega0` (private) :28 | `hx` (idx 1) | for x = 0, 0^omega = 0 (vacuous); for x = 1, 1^omega = 1 and 0 * 0 < 1 | `checks/W1c5Hand.lean` (`w5_134`) |

## Nimber.SimplestExtension.Algebraic

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Nimber.IsField.eval_eq_of_lt` (private) :63 | `h` (idx 2) | as IsRing.eval_eq_of_lt (X^2 <= leastNoRoots x with 1 < x forces a field) (t_29) | `checks/T1c0Hand.lean` (`t_29`) |
| `Nimber.IsRing.eval_eq_of_lt` :139 | `h` (idx 2) | new lemma: 1 < x and X^2 <= leastNoRoots x imply IsField x (Iio x closed under division forces closure under addition); x <= 1 or lnr < X^2 make p constant (t_28) | `checks/T1c0Hand.lean` (`t_28`) |
| `Nimber.IsRing.pow_mul_eq` :152 | `h` (idx 3) | x <= 1 forces y = 0, n = 0 trivial, else X^2 <= leastNoRoots x forces a field (t_30) | `checks/T1c0Hand.lean` (`t_30`) |
| `Nimber.IsRing.pow_eq` :162 | `h` (idx 2) | x <= 1 by cases, else pow_mul_eq without IsRing at y = 1 (t_31) | `checks/T1c0Hand.lean` (`t_31`) |
| `Nimber.IsField.degree_leastNoRoots_le_of_isField_pow` :480 | `hx` (idx 3) | x <= 1 and n = 0 contradict IsField *(x^n); X^2 <= lnr forces a field; else deg lnr < 2 <= n (t_38) | `checks/T1c0Hand.lean` (`t_38`) |
| `Nimber.IsField.sqrt_lt` :788 | `h` (idx 2) | x <= 1 forces y = 0; else X^2 <= X^2 + C y < leastNoRoots x forces a field (t_32) | `checks/T1c0Hand.lean` (`t_32`) |

## Nimber.SimplestExtension.Basic

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Nimber.IsGroup.mul_eq_of_lt'` :413 | `hx` (idx 4) | for w >= 2, y is a group > *2 so *3 < y <= z and H' makes Iio x closed under *2; then x = 4^(log 4 x) (else an element e < x has e * *2 = x or >= x via the base-4 expansion), so x is a group and the library proof applies; w <= 1 is trivial | `checks/T3c2Hand.lean` (`T3c2.c_1`) |
| `Nimber.IsGroup.mul_eq_of_lt'` :413 | `hz` (idx 6) | hz only gives b + w < z; follows from hy (b, w < y) and hyz; library proof re-run without hz/hyx (t_14) | `checks/T1c0Hand.lean` (`t_14`) |
| `Nimber.IsGroup.mul_eq_of_lt'` :413 | `hyx` (idx 7) | hyx is only passed to the recursive calls of the library proof (t_15) | `checks/T1c0Hand.lean` (`t_15`) |
| `Nimber.IsGroup.mul_eq_of_lt'` :413 | `hyz` (idx 8) | H forces y <= z: if z < y then (*z)^-1 < *z and z = ((*z)^-1)^-1 < z (t_26) | `checks/T1c0Hand.lean` (`t_26`) |
| `Nimber.IsGroup.mul_eq_of_lt` :441 | `hx` (idx 4) | as the Ordinal version (Iio x closed under *2 forces x to be a power of 4) | `checks/T3c2Hand.lean` (`T3c2.c_2`) |
| `Nimber.IsGroup.mul_eq_of_lt` :441 | `hz` (idx 6) | as the Ordinal version (hz replaced by hy + hyz) (t_16) | `checks/T1c0Hand.lean` (`t_16`) |
| `Nimber.IsGroup.mul_eq_of_lt` :441 | `hyx` (idx 7) | as the Ordinal version (hyx unused) (t_17) | `checks/T1c0Hand.lean` (`t_17`) |
| `Nimber.IsGroup.mul_eq_of_lt` :441 | `hyz` (idx 8) | H forces y <= z (as the Ordinal version) (t_27) | `checks/T1c0Hand.lean` (`t_27`) |
| `Nimber.IsRing.mul_eq_of_lt'` :447 | `hyx` (idx 5) | H forces y <= x (as for the Nimber version) (t_11) | `checks/T1c0Hand.lean` (`t_11`) |
| `Nimber.IsRing.mul_eq_of_lt` :451 | `hyx` (idx 5) | H forces y <= x: if x < y then x^-1 < x < y and x = (x^-1)^-1 < x (t_10) | `checks/T1c0Hand.lean` (`t_10`) |
| `Nimber.IsField.inv_lt'` :467 | `hy₀` (idx 3) | the weakened statement is proved by `simp_all` | `runs/mech/search-both-server/public.proofs` |

## Nimber.SimplestExtension.Polynomial

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Nimber.oeval_lt_oeval` :641 | `hqk` (idx 5) | library proof adapted: the coefficient bound of the larger polynomial q is never used (c_38) | `checks/W2c2Hand.lean` (`c_38`) |
| `Nimber.oeval_le_oeval` :716 | `hqk` (idx 5) | from the removable oeval_lt_oeval without hqk (c_41) | `checks/W2c2Hand.lean` (`c_41`) |
| `Nimber.eq_oeval_of_lt_oeval` :775 | `hx₀` (idx 3) | the weakened statement is proved by `simp_all` | `runs/mech/search-both-server/public.proofs` |
| `Nimber.IsField.root_lt` :948 | `h` (idx 2) | x <= 1 forces p = 0; X^2 <= lnr with 1 < x forces a field; else p linear with its unique root below x (t_37) | `checks/T1c0Hand.lean` (`t_37`) |
| `Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots` :953 | `h` (idx 1) | Nimber is algebraically closed: C_leadingCoeff_mul_prod_multiset_X_sub_C with card_roots_eq_natDegree (c_73) | `checks/W2c2Hand.lean` (`c_73`) |
| `Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots` :953 | `hpn` (idx 3) | Nimber is algebraically closed: C_leadingCoeff_mul_prod_multiset_X_sub_C with card_roots_eq_natDegree (c_74) | `checks/W2c2Hand.lean` (`c_74`) |
| `Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots` :953 | `hpk` (idx 4) | Nimber is algebraically closed: C_leadingCoeff_mul_prod_multiset_X_sub_C with card_roots_eq_natDegree (c_75) | `checks/W2c2Hand.lean` (`c_75`) |

## Nimber.SmallDegree.Quartic

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Nimber.IsField.degree_leastNoRoots_ne_four` :133 | `hx` (idx 1) | degree 4 gives X^2 < leastNoRoots x (and x > 1 by ht), hence a field (t_35) | `checks/T1c0Hand.lean` (`t_35`) |
| `Nimber.IsField.natDegree_leastNoRoots_ne_four` :155 | `hx` (idx 1) | as the degree version (t_36) | `checks/T1c0Hand.lean` (`t_36`) |
| `Nimber.IsField.X_pow_five_lt_leastNoRoots_of_X_pow_four_le_leastNoRoots` :161 | `hx` (idx 1) | x <= 1 gives leastNoRoots = top; else X^4 <= lnr forces a field (t_33) | `checks/T1c0Hand.lean` (`t_33`) |
| `Nimber.IsField.leastNoRoots_lt_X_pow_four_of_leastNoRoots_le_X_pow_five` :171 | `hx` (idx 1) | contrapositive of the previous row (t_34) | `checks/T1c0Hand.lean` (`t_34`) |

## SignExpansion.Basic

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Pi.Lex.neg_le_neg_iff` :69 | `inst` (idx 2) | ≤ on Lex is lt-or-eq; neg_lt_neg_iff needs no well-foundedness (c_1) | `checks/W2c3Hand.lean` (`c_1`) |
| `Pi.Lex.neg_le_iff` :81 | `inst` (idx 2) | from the WellFoundedLT-free neg_le_neg_iff (c_2) | `checks/W2c3Hand.lean` (`c_2`) |
| `Pi.Lex.le_neg_iff` :85 | `inst` (idx 2) | from the WellFoundedLT-free neg_le_neg_iff (c_3) | `checks/W2c3Hand.lean` (`c_3`) |
| `SignExpansion.Small.length_eq` :216 | `inst` (idx 1, dependent) | x.length = ↑o forces x.length ≠ ⊤, i.e. x.Small (c_10) | `checks/W2c3Hand.lean` (`c_10`) |
| `SignExpansion.succ_apply_of_eq` :691 | `inst` (idx 1, dependent) | [x.Small] follows from x.length = ↑o (small_iff_length_ne_top) | `checks/Probe1Hand.lean` (`Probe1.p1_26`) |
| `SignExpansion.succ_apply_of_gt` :695 | `inst` (idx 1, dependent) | x.length < ↑o forces x.length ≠ ⊤, i.e. x.Small (c_53) | `checks/W2c3Hand.lean` (`c_53`) |
| `SignExpansion.pred_apply_of_eq` :786 | `inst` (idx 1, dependent) | x.length = ↑o forces x.length ≠ ⊤, i.e. x.Small (c_55) | `checks/W2c3Hand.lean` (`c_55`) |
| `SignExpansion.pred_apply_of_gt` :790 | `inst` (idx 1, dependent) | x.length < ↑o forces x.length ≠ ⊤, i.e. x.Small (c_54) | `checks/W2c3Hand.lean` (`c_54`) |

## SignExpansion.Simplicity

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Simplicity.exists_of_sSup_apply_ne_zero` (private) :245 | `hs` (idx 1) | for a non-chain s, sSup s = ⊥ so sSup s o ≠ 0 is false (c_79) | `checks/W2c3Hand.lean` (`c_79`) |

## Surreal.Birthday.Basic

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Surreal.birthday_ofSets_le_of_btwn'` :137 | `H` (idx 4, dependent) | the weakened statement is proved by `grind` | `runs/mech/fix1/pub.proofs` |
| `Surreal.birthday_ofSets_lt_of_btwn'` :145 | `H` (idx 4, dependent) | the weakened statement is proved by `grind` | `runs/mech/fix1/pub.proofs` |
| `Surreal.birthday_ofSets_le_of_btwn` :155 | `H` (idx 5, dependent) | the weakened statement is proved by `grind` | `runs/mech/fix1/pub.proofs` |
| `Surreal.birthday_ofSets_lt_of_btwn` :160 | `H` (idx 5, dependent) | the weakened statement is proved by `grind` | `runs/mech/fix1/pub.proofs` |
| `Surreal.ofSets_eq_of_forall_birthday_le'` :166 | `H` (idx 4, dependent) | the weakened statement is proved by `grind` | `runs/mech/fix1/pub.proofs` |
| `Surreal.ofSets_eq_of_forall_birthday_le` :175 | `H` (idx 5, dependent) | the weakened statement is proved by `grind` | `runs/mech/fix1/pub.proofs` |

## Surreal.Division

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `instNumericInvOptionOfInvIGame` (private) :45 | `inst` (idx 5) | the weakened statement is proved by `infer_instance` | `runs/mech/search-both-server/private.proofs` |
| `one_neg_mul_invOption` (private) :58 | `inst` (idx 6) | the weakened statement is proved by `solve_by_elim` | `runs/mech/search-both-server/private.proofs` |
| `mulOption_self_inv` (private) :66 | `inst` (idx 5) | the weakened statement is proved by `solve_by_elim` | `runs/mech/search-both-server/private.proofs` |
| `mulOption_self_inv` (private) :66 | `inst` (idx 7) | the weakened statement is proved by `solve_by_elim` | `runs/mech/search-both-server/private.proofs` |
| `numeric_option_inv` (private) :99 | `hx` (idx 2) | x⁻¹ is numeric (Numeric.inv), so its options are | `checks/W2c5Hand.lean` (`c5_40`) |
| `numeric_option_inv` (private) :99 | `hl` (idx 3) | x⁻¹ is numeric (Numeric.inv), so its options are | `checks/W2c5Hand.lean` (`c5_41`) |
| `numeric_option_inv` (private) :99 | `hr` (idx 4) | x⁻¹ is numeric (Numeric.inv), so its options are | `checks/Probe2Hand.lean` (`Probe2.p2_19`) |
| `mul_inv_option_mem` (private) :111 | `hl` (idx 3) | for numeric 0 < x, x * x⁻¹ ≈ 1 gives the bounds (Numeric.mul_inv_cancel) | `checks/W2c5Hand.lean` (`c5_44`) |
| `mul_inv_option_mem` (private) :111 | `hr` (idx 4) | for numeric 0 < x, x * x⁻¹ ≈ 1 gives the bounds (Numeric.mul_inv_cancel) | `checks/W2c5Hand.lean` (`c5_45`) |
| `mul_inv_option_mem` (private) :111 | `hl'` (idx 5) | for numeric 0 < x, x * x⁻¹ ≈ 1 gives the bounds (Numeric.mul_inv_cancel) | `checks/W2c5Hand.lean` (`c5_46`) |
| `mul_inv_option_mem` (private) :111 | `hr'` (idx 6) | for numeric 0 < x, x * x⁻¹ ≈ 1 gives the bounds (Numeric.mul_inv_cancel) | `checks/W2c5Hand.lean` (`c5_47`) |
| `numeric_inv` (private) :157 | `hx` (idx 2) | the weakened statement is proved by `infer_instance` | `runs/mech/search-both-server/private.proofs` |
| `numeric_inv` (private) :157 | `hl` (idx 3) | the weakened statement is proved by `infer_instance` | `runs/mech/search-both-server/private.proofs` |
| `numeric_inv` (private) :157 | `hr` (idx 4) | the weakened statement is proved by `infer_instance` | `runs/mech/search-both-server/private.proofs` |
| `numeric_inv` (private) :157 | `hl'` (idx 5) | the weakened statement is proved by `infer_instance` | `runs/mech/search-both-server/private.proofs` |
| `numeric_inv` (private) :157 | `hr'` (idx 6) | the weakened statement is proved by `infer_instance` | `runs/mech/search-both-server/private.proofs` |
| `option_mul_inv_lt` (private) :168 | `hx` (idx 2) | for numeric x, options of x * x⁻¹ are numeric and x * x⁻¹ ≈ 1 or = 0 | `checks/W2c5Hand.lean` (`c5_50`) |
| `option_mul_inv_lt` (private) :168 | `hl` (idx 3) | for numeric x, options of x * x⁻¹ are numeric and x * x⁻¹ ≈ 1 or = 0 | `checks/W2c5Hand.lean` (`c5_51`) |
| `option_mul_inv_lt` (private) :168 | `hr` (idx 4) | for numeric x, options of x * x⁻¹ are numeric and x * x⁻¹ ≈ 1 or = 0 | `checks/W2c5Hand.lean` (`c5_52`) |
| `option_mul_inv_lt` (private) :168 | `hl'` (idx 5) | for numeric x, options of x * x⁻¹ are numeric and x * x⁻¹ ≈ 1 or = 0 | `checks/W2c5Hand.lean` (`c5_53`) |
| `option_mul_inv_lt` (private) :168 | `hr'` (idx 6) | for numeric x, options of x * x⁻¹ are numeric and x * x⁻¹ ≈ 1 or = 0 | `checks/W2c5Hand.lean` (`c5_54`) |
| `mul_inv_self` (private) :214 | `hl` (idx 3) | Numeric.mul_inv_cancel | `checks/W2c5Hand.lean` (`c5_55`) |
| `mul_inv_self` (private) :214 | `hr` (idx 4) | Numeric.mul_inv_cancel | `checks/W2c5Hand.lean` (`c5_56`) |
| `mul_inv_self` (private) :214 | `hl'` (idx 5) | Numeric.mul_inv_cancel | `checks/W2c5Hand.lean` (`c5_57`) |
| `mul_inv_self` (private) :214 | `hr'` (idx 6) | Numeric.mul_inv_cancel | `checks/W2c5Hand.lean` (`c5_58`) |

## Surreal.Dyadic

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Dyadic.numeric_lower` (private) :261 | `hx` (idx 1) | the weakened statement is proved by `infer_instance` | `runs/mech/search-both-server/private.proofs` |
| `Dyadic.numeric_upper` (private) :269 | `hx` (idx 1) | the weakened statement is proved by `infer_instance` | `runs/mech/search-both-server/private.proofs` |
| `Dyadic.lower_lt_aux` (private) :274 | `hx` (idx 1) | every Dyadic toIGame is numeric; follows from public toIGame_lt_toIGame and lower_lt (w3_9) | `checks/W3c0Hand.lean` (`W3c0.w3_9`) |
| `Dyadic.lt_upper_aux` (private) :283 | `hx` (idx 1) | every Dyadic toIGame is numeric; follows from public toIGame_lt_toIGame and lt_upper (w3_10) | `checks/W3c0Hand.lean` (`W3c0.w3_10`) |
| `Dyadic.toIGame_lt_toIGame_aux` (private) :288 | `inst` (idx 2) | Numeric instance derivable (IGame.Numeric.dyadic); follows from public toIGame_lt_toIGame (w3_11) | `checks/W3c0Hand.lean` (`W3c0.w3_11`) |
| `Dyadic.toIGame_lt_toIGame_aux` (private) :288 | `inst` (idx 3) | Numeric instance derivable (IGame.Numeric.dyadic); follows from public toIGame_lt_toIGame (w3_12) | `checks/W3c0Hand.lean` (`W3c0.w3_12`) |

## Surreal.Leading

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Surreal.leadingTerm_mono'` (private) :275 | `hx` (idx 2) | Surreal.leadingTerm_mono: leadingTerm is monotone everywhere | `checks/Probe2Hand.lean` (`Probe2.p2_17`) |

## Surreal.Multiplication

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `mulOption_lt` (private) :250 | `ihxy` (idx 4) | for numeric x,y the left option mulOption x y a b of x*y is < its right option mulOption x y c (-d) since x*y is numeric (Numeric.mul) (w3c1_57) | `checks/W3c1Hand.lean` (`w3c1_57`) |
| `mulOption_lt` (private) :250 | `ihyx` (idx 5) | same as idx 4, only Numeric x, Numeric y and the memberships are used (w3c1_58) | `checks/W3c1Hand.lean` (`w3c1_58`) |
| `P1_of_IH` (private) :262 | `IH` (idx 2) | the weakened statement is proved by `infer_instance` | `runs/mech/search-both-server/private.proofs` |
| `IGame.Numeric.mulOption_congr₁` :618 | `inst` (idx 7) | y only occurs in a·y, the same on both sides (w3c2_66) | `checks/W3c2Hand.lean` (`w3c2_66`) |
| `IGame.Numeric.mulOption_congr₁` :618 | `inst` (idx 8) | a only occurs in a·y and a·b, the same on both sides (w3c2_67) | `checks/W3c2Hand.lean` (`w3c2_67`) |
| `IGame.Numeric.mulOption_congr₂` :623 | `inst` (idx 5) | x only occurs in x·b, the same on both sides (w3c2_69) | `checks/W3c2Hand.lean` (`w3c2_69`) |
| `IGame.Numeric.mulOption_congr₂` :623 | `inst` (idx 9) | b only occurs in x·b and a·b, the same on both sides (w3c2_71) | `checks/W3c2Hand.lean` (`w3c2_71`) |
| `IGame.Numeric.mulOption_congr₃` :628 | `inst` (idx 5) | x only occurs in x·b, the same on both sides (w3c2_72) | `checks/W3c2Hand.lean` (`w3c2_72`) |
| `IGame.Numeric.mulOption_congr₄` :633 | `inst` (idx 6) | y only occurs in a·y, the same on both sides (w3c2_76) | `checks/W3c2Hand.lean` (`w3c2_76`) |

## Surreal.Pow

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `IGame.Numeric.wpow_strictMono_aux` (private) :167 | `inst` (idx 2) | Numeric x follows from Numeric (ω^ x) (induction: options 1 * ω^ y, ω^ a < ω^ b) (w3c3_45) | `checks/W3c3Hand.lean` (`W3c3.w3c3_45`) |
| `IGame.Numeric.wpow_strictMono_aux` (private) :167 | `inst` (idx 3) | Numeric y follows from Numeric (ω^ y) (w3c3_46) | `checks/W3c3Hand.lean` (`W3c3.w3c3_46`) |
| `IGame.Numeric.wpow_strictMono_aux` (private) :167 | `inst` (idx 4) | the weakened statement is proved by `solve_by_elim` | `runs/mech/search-both-server/private.proofs` |
| `IGame.Numeric.wpow_strictMono_aux` (private) :167 | `inst` (idx 5) | the weakened statement is proved by `solve_by_elim` | `runs/mech/search-both-server/private.proofs` |
| `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow` :277 | `hx` (idx 11) | r ω^x < t ω^z (from x < z) and s ω^y > 0 (w3c3_29) | `checks/W3c3Hand.lean` (`W3c3.w3c3_29`) |
| `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow` :277 | `hy` (idx 12) | r ω^x < s ω^y (from x < y) and t ω^z > 0 (w3c3_30) | `checks/W3c3Hand.lean` (`W3c3.w3c3_30`) |
| `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow'` :284 | `hx` (idx 11) | r ω^x < t ω^z (from x < z) and s ω^y > 0 (w3c3_31) | `checks/W3c3Hand.lean` (`W3c3.w3c3_31`) |
| `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow'` :284 | `hy` (idx 12) | s ω^y > r ω^x already (x < y, s > 0) and t ω^z > 0 | `checks/Probe2Hand.lean` (`Probe2.p2_27`) |
| `IGame.Numeric.mulOption_lt_wpow` (private) :360 | `IH₁` (idx 14) | the IH equivalence is an instance of wpow_add_equiv for numeric games (w3c3_97) | `checks/W3c3Hand.lean` (`W3c3.w3c3_97`) |
| `IGame.Numeric.mulOption_lt_wpow` (private) :360 | `IH₂` (idx 15) | the IH equivalence is an instance of wpow_add_equiv for numeric games (w3c3_98) | `checks/W3c3Hand.lean` (`W3c3.w3c3_98`) |
| `IGame.Numeric.mulOption_lt_wpow` (private) :360 | `IH₃` (idx 16) | the IH equivalence is an instance of wpow_add_equiv for numeric games (w3c3_99) | `checks/W3c3Hand.lean` (`W3c3.w3c3_99`) |
| `IGame.Numeric.mulOption_lt_wpow'` (private) :370 | `hr` (idx 10) | all three terms have exponents below x + y, so any sign of r works (w3c3_37) | `checks/W3c3Hand.lean` (`W3c3.w3c3_37`) |
| `IGame.Numeric.mulOption_lt_wpow'` (private) :370 | `hs` (idx 11) | all three terms have exponents below x + y, so any sign of s works (w3c3_38) | `checks/W3c3Hand.lean` (`W3c3.w3c3_38`) |
| `IGame.Numeric.mulOption_lt_wpow'` (private) :370 | `IH₁` (idx 14) | the IH equivalence is an instance of wpow_add_equiv for numeric games (w3c3_100) | `checks/W3c3Hand.lean` (`W3c3.w3c3_100`) |
| `IGame.Numeric.mulOption_lt_wpow'` (private) :370 | `IH₂` (idx 15) | the IH equivalence is an instance of wpow_add_equiv for numeric games (w3c3_101) | `checks/W3c3Hand.lean` (`W3c3.w3c3_101`) |
| `IGame.Numeric.mulOption_lt_wpow'` (private) :370 | `IH₃` (idx 16) | the IH equivalence is an instance of wpow_add_equiv for numeric games (w3c3_102) | `checks/W3c3Hand.lean` (`W3c3.w3c3_102`) |
| `IGame.Numeric.wpow_lt_mulOption` (private) :380 | `hs` (idx 11) | leading term r ω^(z+y) dominates for any sign of s (w3c3_42) | `checks/W3c3Hand.lean` (`W3c3.w3c3_42`) |
| `IGame.Numeric.wpow_lt_mulOption` (private) :380 | `IH₁` (idx 14) | the IH equivalence is an instance of wpow_add_equiv for numeric games (w3c3_103) | `checks/W3c3Hand.lean` (`W3c3.w3c3_103`) |
| `IGame.Numeric.wpow_lt_mulOption` (private) :380 | `IH₂` (idx 15) | the IH equivalence is an instance of wpow_add_equiv for numeric games (w3c3_104) | `checks/W3c3Hand.lean` (`W3c3.w3c3_104`) |
| `Surreal.mk_lt_mk_of_ne` (private) :609 | `h` (idx 2) | 0 < x follows from a positive left option (w3c3_60) | `checks/W3c3Hand.lean` (`W3c3.w3c3_60`) |
| `Surreal.numeric_of_forall_mk_ne_mk'` (private) :627 | `h` (idx 2) | 0 < x follows from any positive left option (w3c3_70) | `checks/W3c3Hand.lean` (`W3c3.w3c3_70`) |
| `Surreal.numeric_of_forall_mk_ne_mk'` (private) :627 | `Hl` (idx 7) | f, g are wlog by hf, hg; Hr alone gives wlog a ≤ wlog x < wlog b (w3c3_68) | `checks/W3c3Hand.lean` (`W3c3.w3c3_68`) |
| `Surreal.numeric_of_forall_mk_ne_mk'` (private) :627 | `Hr` (idx 8) | f, g are wlog by hf, hg; Hl alone gives wlog a < wlog x ≤ wlog b (w3c3_69) | `checks/W3c3Hand.lean` (`W3c3.w3c3_69`) |
| `Surreal.numeric_of_forall_mk_ne_mk` :905 | `h` (idx 2) | 0 < x follows from any positive left option; without one the left side is empty (w3c3_67) | `checks/W3c3Hand.lean` (`W3c3.w3c3_67`) |
| `Surreal.numeric_of_forall_mk_ne_mk` :905 | `Hl` (idx 3) | Hr alone gives wlog a ≤ wlog x < wlog b (wlog monotone on positives) (w3c3_65) | `checks/W3c3Hand.lean` (`W3c3.w3c3_65`) |
| `Surreal.numeric_of_forall_mk_ne_mk` :905 | `Hr` (idx 4) | Hl alone gives wlog a < wlog x ≤ wlog b (w3c3_66) | `checks/W3c3Hand.lean` (`W3c3.w3c3_66`) |

## Surreal.Real

| Theorem | Hypothesis | Why it is not needed | Proof |
|---|---|---|---|
| `Real.dyadic_lt_mul_toIGame'` (private) :544 | `hx` (idx 3) | follows from the sign-free dyadic_lt_mul_toIGame (w34_11) | `checks/W3c4Hand.lean` (`W3c4.w34_11`) |
| `Real.dyadic_lt_mul_toIGame'` (private) :544 | `hy` (idx 4) | follows from the sign-free dyadic_lt_mul_toIGame (w34_12) | `checks/W3c4Hand.lean` (`W3c4.w34_12`) |
| `Real.mul_toIGame_lt_dyadic'` (private) :559 | `hx` (idx 3) | private sibling Real.mul_toIGame_lt_dyadic needs no sign hypotheses | `checks/Probe2Hand.lean` (`Probe2.p2_18`) |
| `Real.mul_toIGame_lt_dyadic'` (private) :559 | `hy` (idx 4) | follows from the sign-free mul_toIGame_lt_dyadic (w34_14) | `checks/W3c4Hand.lean` (`W3c4.w34_14`) |
