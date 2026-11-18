# Unresolved hypotheses (combinatorial-games)

59 hypotheses are undecided: neither the weakened statement nor its negation was proved. Each was tried by the mechanical checks and by at least one AI agent (most by two or three); the obstruction is the last agent's account of what a proof or counterexample would need. Unresolved says nothing either way.

## Nimber.SimplestExtension.Basic

| Theorem | Hypothesis | Obstruction |
|---|---|---|
| `Nimber.IsGroup.mul_le_of_forall_lt` :393 | `hrl` (idx 6) | reduced to y, z powers of 2 (if z is not a group, z = a + b with a, b < z and y*z = y*a + y*b < x by hyl; same for y); then needs r*l < x for r<y, l<z, which holds in every finite case (x <= 512), in the F16(omega) model with omega^3 = 2, and in the bit-OR leading-term model, but no proof: needs a leading-term theory of nim products of powers of 2 … |

## Nimber.SmallDegree.Inseparable

| Theorem | Hypothesis | Obstruction |
|---|---|---|
| `Nimber.IsAlgClosed.isField_fieldClosure_succ_pow_two_pow` :95 | `ht` (idx 1) | necessary in truth (t=*omega, n=1: *(omega^6) is not a field); every successor field F=fieldClosure(succ t) we can compute (t finite: F=*(2^2^k); t in [T,F_T)) has a quadratic next extension, making the statement true; the only candidate t=*omega needs d(F)!=2 for F=fieldClosure(succ *omega)=*(omega^d0): (a) d0=3, i.e. every X^2+X+c over Iio *omega… |
| `Nimber.IsAlgClosed.degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux` (private) :108 | `ht` (idx 1) | necessary in truth (t=*omega, n=0: deg leastNoRoots *(omega^3) = 3); every successor field F=fieldClosure(succ t) we can compute (t finite: F=*(2^2^k); t in [T,F_T)) has a quadratic next extension, making the statement true; the only candidate t=*omega needs d(F)!=2 for F=fieldClosure(succ *omega)=*(omega^d0): (a) d0=3, i.e. every X^2+X+c over Iio … |
| `Nimber.IsAlgClosed.enumField_add_natCast_add_one` :234 | `ht` (idx 1) | necessary in truth (t=*omega, x=omega, n=1: enumField(omega+2)=*(omega^9) != *(omega^6)); every successor field F=fieldClosure(succ t) we can compute (t finite: F=*(2^2^k); t in [T,F_T)) has a quadratic next extension, making the statement true; the only candidate t=*omega needs d(F)!=2 for F=fieldClosure(succ *omega)=*(omega^d0): (a) d0=3, i.e. ev… |
| `Nimber.IsAlgClosed.enumField_add_omega0` :246 | `ht` (idx 1) | believed removable: for a field t the chain of next fields F^(m_k) (m_k finite, >= 2^k) has sup F^omega, but only if no finite stage F^m is algebraically closed; that needs an Artin-Schreier-type theorem (an alg. closed nimber is never x^d for a smaller non-alg-closed field x). Proved on paper only for imperfect x (Frobenius maps Iio x^2 into Iio x… |
| `Nimber.IsAlgClosed.isField_fieldClosure_succ_pow_omega0` :260 | `ht` (idx 1) | believed removable (library todo: true for every non-alg-closed field): F^omega = sup of the next-field chain, IsField.iSup; same missing lemma as enumField_add_omega0 (no alg. closed nimber equals F^m, m finite); if one did, F^omega would be a ring but not a field (T1c0 notFieldR) |
| `Nimber.IsAlgClosed.exists_fieldClosure_succ_pow_two_pow_eq_of_isField_of_btwn` :266 | `ht` (idx 1) | necessary in truth (t=*omega, x=fieldClosure(succ F)=*(omega^9) is not F^(2^n)); every successor field F=fieldClosure(succ t) we can compute (t finite: F=*(2^2^k); t in [T,F_T)) has a quadratic next extension, making the statement true; the only candidate t=*omega needs d(F)!=2 for F=fieldClosure(succ *omega)=*(omega^d0): (a) d0=3, i.e. every X^2+X… |

## Nimber.SmallDegree.Quartic

| Theorem | Hypothesis | Obstruction |
|---|---|---|
| `Nimber.IsField.sq_of_pow_four` :177 | `hx` (idx 1) | needs x field from *(x^4) field; with l = largest field <= x (exists_isField_between'), l < x < N = fieldClosure (succ l) <= x^4; non-alg-closed l: x^4 = l^(n*j) with n = deg leastNoRoots l, j <= 3, which needs n prime (Lenstra) to refute; alg-closed l: needs the size of fieldClosure (succ l) (e.g. for T), unknown to the library. Likely removable, … |

## Surreal.Division

| Theorem | Hypothesis | Obstruction |
|---|---|---|
| `inv_pos'` (private) :49 | `inst` (idx 1) | needs 0 < x with a right option of inv x that is ≤ 0; right options start with inv y for positive left options y (never ≤ 0), later ones are (1 + (y - x) a) inv y with an infinite generation; not constructed |
| `one_neg_mul_invOption` (private) :58 | `inst` (idx 4) | Candidate x = up, y = 1, a = -1 is NOT a counterexample: with y = 1 (y⁻¹ = 1) the statement is a polynomial identity provable in Game. In general, expanding both sides with mk_mul_add/mk_sub_mul/mk_mul_assoc/mul_comm (valid for all games) and hy leaves exactly LHS ≈ RHS ⟺ mk(y*(a*(x*y⁻¹))) = mk(x*(a*(y*y⁻¹))), a 4-fold rearrangement not reachable b… |
| `one_neg_mul_invOption` (private) :58 | `inst` (idx 5) | Game-level ring identities (distributivity, associativity) hold for all games, so a counterexample needs a congruence failure inside the literal products (e.g. (1 + (-2))*a vs (-1)*a); not found with y = 1, {0,star\|}; y⁻¹ for other numeric y is infinite |
| `one_neg_mul_invOption` (private) :58 | `inst` (idx 7) | Game-level ring identities (distributivity, associativity) hold for all games, so a counterexample needs a congruence failure inside the literal products (e.g. (1 + (-2))*a vs (-1)*a); not found with y = 1, {0,star\|}; y⁻¹ for other numeric y is infinite |
| `mulOption_self_inv` (private) :66 | `inst` (idx 6) | Game-level ring identities (distributivity, associativity) hold for all games, so a counterexample needs a congruence failure inside the literal products (e.g. (1 + (-2))*a vs (-1)*a); not found with y = 1, {0,star\|}; y⁻¹ for other numeric y is infinite |
| `mul_inv_self` (private) :214 | `inst` (idx 1) | x must have no positive option for a finite inverse (then x has no right option relevant and x ≈ 1, x*1 ≈ 1 holds); right options fuzzy with 0 have inverse 0 and break hr'; otherwise infinite inverse |
| `IGame.Numeric.div_congr_left` :276 | `inst` (idx 3) | needs numeric x1 ≈ x2 whose quotients by y differ: y⁻¹ is 0, ±1 or infinite for every y, and the congruence failures (W*1/2, Z0*star, XP*star) need a factor 1/2 or star that no finite inverse provides |
| `IGame.Numeric.div_congr_left` :276 | `inst` (idx 4) | needs numeric x1 ≈ x2 whose quotients by y differ: y⁻¹ is 0, ±1 or infinite for every y, and the congruence failures (W*1/2, Z0*star, XP*star) need a factor 1/2 or star that no finite inverse provides |
| `IGame.Numeric.div_congr_left` :276 | `inst` (idx 5) | needs numeric x1 ≈ x2 whose quotients by y differ: y⁻¹ is 0, ±1 or infinite for every y, and the congruence failures (W*1/2, Z0*star, XP*star) need a factor 1/2 or star that no finite inverse provides |
| `IGame.Numeric.div_congr_right` :280 | `inst` (idx 3) | needs numeric x1 ≈ x2 whose quotients by y differ: y⁻¹ is 0, ±1 or infinite for every y, and the congruence failures (W*1/2, Z0*star, XP*star) need a factor 1/2 or star that no finite inverse provides |
| `IGame.Numeric.div_congr` :284 | `inst` (idx 4) | needs numeric x1 ≈ x2 whose quotients by y differ: y⁻¹ is 0, ±1 or infinite for every y, and the congruence failures (W*1/2, Z0*star, XP*star) need a factor 1/2 or star that no finite inverse provides |
| `IGame.Numeric.div_congr` :284 | `inst` (idx 5) | needs numeric x1 ≈ x2 whose quotients by y differ: y⁻¹ is 0, ±1 or infinite for every y, and the congruence failures (W*1/2, Z0*star, XP*star) need a factor 1/2 or star that no finite inverse provides |
| `IGame.Numeric.inv_pos` :317 | `inst` (idx 1) | needs 0 < x with a right option of inv x that is ≤ 0; right options start with inv y for positive left options y (never ≤ 0), later ones are (1 + (y - x) a) inv y with an infinite generation; not constructed |
| `IGame.Numeric.inv_neg` :321 | `inst` (idx 1) | needs 0 < x with a right option of inv x that is ≤ 0; right options start with inv y for positive left options y (never ≤ 0), later ones are (1 + (y - x) a) inv y with an infinite generation; not constructed |
| `IGame.Numeric.lt_div_iff` :341 | `inst` (idx 4) | inverse of a numeric game with a positive option has an infinite option set (generated by invOption), so products y*z⁻¹ with non-numeric y cannot be computed by game_cmp; games with no positive option have inverse 1 (only value-1 or the XH trick); no abstract argument found |
| `IGame.Numeric.lt_div_iff'` :345 | `inst` (idx 4) | inverse of a numeric game with a positive option has an infinite option set (generated by invOption), so products y*z⁻¹ with non-numeric y cannot be computed by game_cmp; games with no positive option have inverse 1 (only value-1 or the XH trick); no abstract argument found |
| `IGame.Numeric.div_lt_iff` :349 | `inst` (idx 3) | inverse of a numeric game with a positive option has an infinite option set (generated by invOption), so products y*z⁻¹ with non-numeric y cannot be computed by game_cmp; games with no positive option have inverse 1 (only value-1 or the XH trick); no abstract argument found |
| `IGame.Numeric.div_lt_iff'` :353 | `inst` (idx 3) | inverse of a numeric game with a positive option has an infinite option set (generated by invOption), so products y*z⁻¹ with non-numeric y cannot be computed by game_cmp; games with no positive option have inverse 1 (only value-1 or the XH trick); no abstract argument found |
| `IGame.Numeric.lt_div_iff_of_neg` :357 | `inst` (idx 4) | inverse of a numeric game with a positive option has an infinite option set (generated by invOption), so products y*z⁻¹ with non-numeric y cannot be computed by game_cmp; games with no positive option have inverse 1 (only value-1 or the XH trick); no abstract argument found |
| `IGame.Numeric.div_lt_iff_of_neg` :361 | `inst` (idx 3) | inverse of a numeric game with a positive option has an infinite option set (generated by invOption), so products y*z⁻¹ with non-numeric y cannot be computed by game_cmp; games with no positive option have inverse 1 (only value-1 or the XH trick); no abstract argument found |

## Surreal.Multiplication

| Theorem | Hypothesis | Obstruction |
|---|---|---|
| `mulOption_lt_of_lt` (private) :244 | `inst` (idx 2) | needs IH1 x y and IH1 y x with a non-numeric x or y: IH1 y x forces left options of x to be < x and right options > x, IH1 x y forces P3 among options of x with y (W*1/2 ≈ 1 breaks it for x = {W, 3/2 \| 2}); for star-like y P4 needs a*star < c*star, impossible as x*star is impartial |
| `mulOption_lt_of_lt` (private) :244 | `h` (idx 9) | needs IH1 x y and IH1 y x with a non-numeric x or y: IH1 y x forces left options of x to be < x and right options > x, IH1 x y forces P3 among options of x with y (W*1/2 ≈ 1 breaks it for x = {W, 3/2 \| 2}); for star-like y P4 needs a*star < c*star, impossible as x*star is impartial |
| `mulOption_lt` (private) :250 | `inst` (idx 2) | needs IH1 x y and IH1 y x with a non-numeric x or y: IH1 y x forces left options of x to be < x and right options > x, IH1 x y forces P3 among options of x with y (W*1/2 ≈ 1 breaks it for x = {W, 3/2 \| 2}); for star-like y P4 needs a*star < c*star, impossible as x*star is impartial |
| `P1_of_IH` (private) :262 | `inst` (idx 3) | IH over all ArgsRel-smaller argument lists includes P1 x1 y, i.e. Numeric (x1*y) for the non-numeric factor x1 (and products of its subpositions); every non-numeric x1 tried (W, XP = {pm1\|}, {star\|}) has non-numeric products with the y needed for the congruence failure |
| `P1_of_IH` (private) :262 | `inst` (idx 4) | IH over all ArgsRel-smaller argument lists includes P1 x1 y, i.e. Numeric (x1*y) for the non-numeric factor x1 (and products of its subpositions); every non-numeric x1 tried (W, XP = {pm1\|}, {star\|}) has non-numeric products with the y needed for the congruence failure |
| `P2_of_IH` (private) :371 | `inst` (idx 4) | IH over all ArgsRel-smaller argument lists includes P1 x1 y, i.e. Numeric (x1*y) for the non-numeric factor x1 (and products of its subpositions); every non-numeric x1 tried (W, XP = {pm1\|}, {star\|}) has non-numeric products with the y needed for the congruence failure |
| `P2_of_IH` (private) :371 | `inst` (idx 5) | IH over all ArgsRel-smaller argument lists includes P1 x1 y, i.e. Numeric (x1*y) for the non-numeric factor x1 (and products of its subpositions); every non-numeric x1 tried (W, XP = {pm1\|}, {star\|}) has non-numeric products with the y needed for the congruence failure |

## Surreal.Pow

| Theorem | Hypothesis | Obstruction |
|---|---|---|
| `IGame.wpow_pos'` (private) :156 | `inst` (idx 1) | same as wpow_pos idx 1 (private twin) |
| `IGame.Numeric.wpow_pos` :219 | `inst` (idx 1) | T' (0 < ω^ x for all x) needs 0 ⧏ k·ω^ z for every positive dyadic k: for k without left option 0 (k = 3/4, 2, …) the right options k_L·G + k·G_R − k_L·G_R have no algebraic handle (product congruence fails); no counterexample: k·ω^ z ≤ 0 needs some ω^ z' ≱ 0 first, no base case |
| `IGame.Numeric.wpow_nonneg` :220 | `inst` (idx 1) | same as wpow_pos idx 1 |
| `IGame.Numeric.mul_wpow_lt_wpow` :222 | `inst` (idx 3) | y non-numeric > x numeric needs ω^ y ≤ r·ω^ x: y > x forces a left option yL ≥ x (unbounded k·ω^ yL) or, for y without left options, a right option with a left option ≥ 0; no small ω^ y found |
| `IGame.Numeric.mul_wpow_lt_wpow'` :229 | `inst` (idx 3) | dyadic version with the non-numeric exponent on the larger side and positive dyadic coefficient: no y > x found with s·ω^ y small (y > x forces unbounded left options or ω^ y ≈ 1); the real-coefficient witnesses use negative dyadic options of Real.toIGame, absent here |
| `IGame.Numeric.wpow_lt_mul_wpow'` :237 | `inst` (idx 3) | dyadic version with the non-numeric exponent on the larger side and positive dyadic coefficient: no y > x found with s·ω^ y small (y > x forces unbounded left options or ω^ y ≈ 1); the real-coefficient witnesses use negative dyadic options of Real.toIGame, absent here |
| `IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos'` :249 | `inst` (idx 3) | dyadic version with the non-numeric exponent on the larger side and positive dyadic coefficient: no y > x found with s·ω^ y small (y > x forces unbounded left options or ω^ y ≈ 1); the real-coefficient witnesses use negative dyadic options of Real.toIGame, absent here |
| `IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg'` :259 | `inst` (idx 2) | x non-numeric with negative dyadic r: r·ω^ x = −(\|r\|·ω^ x) and \|r\|·ω^ ⋆, \|r\|·ω^ {⋆\|} exceed every positive infinitesimal, so r·ω^ x < s·ω^ y holds for all tried y < x |
| `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow'` :272 | `inst` (idx 5) | dyadic version with the non-numeric exponent on the larger side and positive dyadic coefficient: no y > x found with s·ω^ y small (y > x forces unbounded left options or ω^ y ≈ 1); the real-coefficient witnesses use negative dyadic options of Real.toIGame, absent here |
| `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow'` :284 | `inst` (idx 4) | dyadic version with the non-numeric exponent on the larger side and positive dyadic coefficient: no y > x found with s·ω^ y small (y > x forces unbounded left options or ω^ y ≈ 1); the real-coefficient witnesses use negative dyadic options of Real.toIGame, absent here |
| `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow'` :284 | `inst` (idx 5) | dyadic version with the non-numeric exponent on the larger side and positive dyadic coefficient: no y > x found with s·ω^ y small (y > x forces unbounded left options or ω^ y ≈ 1); the real-coefficient witnesses use negative dyadic options of Real.toIGame, absent here |
| `IGame.Numeric.mulOption_lt_wpow` (private) :360 | `inst` (idx 4) | IH hypotheses tie x/w and z/y,z/w: one of each pair must be 0 for IH to hold with a non-numeric factor, which leaves ω^ (x + y) with x + y non-numeric (e.g. {⋆\|} − 1: left options k·ω^ (⋆ − 1) whose right options k'·ω^ ⋆ make k·ω^ (⋆ − 1) unbounded-uncertain); no bound found |
| `IGame.Numeric.mulOption_lt_wpow` (private) :360 | `inst` (idx 5) | IH hypotheses tie x/w and z/y,z/w: one of each pair must be 0 for IH to hold with a non-numeric factor, which leaves ω^ (x + y) with x + y non-numeric (e.g. {⋆\|} − 1: left options k·ω^ (⋆ − 1) whose right options k'·ω^ ⋆ make k·ω^ (⋆ − 1) unbounded-uncertain); no bound found |
| `IGame.Numeric.mulOption_lt_wpow` (private) :360 | `inst` (idx 6) | IH hypotheses tie x/w and z/y,z/w: one of each pair must be 0 for IH to hold with a non-numeric factor, which leaves ω^ (x + y) with x + y non-numeric (e.g. {⋆\|} − 1: left options k·ω^ (⋆ − 1) whose right options k'·ω^ ⋆ make k·ω^ (⋆ − 1) unbounded-uncertain); no bound found |
| `IGame.Numeric.mulOption_lt_wpow` (private) :360 | `inst` (idx 7) | IH hypotheses tie x/w and z/y,z/w: one of each pair must be 0 for IH to hold with a non-numeric factor, which leaves ω^ (x + y) with x + y non-numeric (e.g. {⋆\|} − 1: left options k·ω^ (⋆ − 1) whose right options k'·ω^ ⋆ make k·ω^ (⋆ − 1) unbounded-uncertain); no bound found |
| `IGame.Numeric.mulOption_lt_wpow'` (private) :370 | `inst` (idx 4) | as mulOption_lt_wpow idx 4–7 |
| `IGame.Numeric.mulOption_lt_wpow'` (private) :370 | `inst` (idx 5) | as mulOption_lt_wpow idx 4–7 |
| `IGame.Numeric.mulOption_lt_wpow'` (private) :370 | `inst` (idx 6) | as mulOption_lt_wpow idx 4–7 |
| `IGame.Numeric.mulOption_lt_wpow'` (private) :370 | `inst` (idx 7) | as mulOption_lt_wpow idx 4–7 |
| `IGame.Numeric.wpow_lt_mulOption` (private) :380 | `inst` (idx 4) | as mulOption_lt_wpow idx 4–7 |
| `IGame.Numeric.wpow_lt_mulOption` (private) :380 | `inst` (idx 5) | as mulOption_lt_wpow idx 4–7 |
| `IGame.Numeric.wpow_lt_mulOption` (private) :380 | `inst` (idx 6) | as mulOption_lt_wpow idx 4–7 |
| `IGame.Numeric.wpow_lt_mulOption` (private) :380 | `inst` (idx 7) | as mulOption_lt_wpow idx 4–7 |
| `IGame.Numeric.wpow_sub_equiv` :442 | `inst` (idx 2) | x non-numeric, y numeric ≠ 0: needs (ω^ y)⁻¹ (only left options for y = -1, ≈ ω, non-canonical options like (½)⁻¹, 1 + (1 − ε)·a) times ω^ ⋆; products of ω^ ⋆ with non-canonical numbers have no handle |
