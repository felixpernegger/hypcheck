/-!
Hand resolution of the 45 hypotheses in `Init.Data.Int.Linear` (namespace
`Int.Internal.Linear`: the cutsat certificate lemmas `cooper_*`, `dvd_*`, `eq_dvd_subst`,
`orOver_*`, …) that `HypCheck.lean` left unresolved. For each hypothesis `hᵢ` of theorem `T`,
this file proves either `T'` (the theorem without `hᵢ`: removable) or `¬T'` (necessary).
None of the 45 is dependent, and all turned out to be necessary.

The witnesses use the one-variable context `.leaf v` (every variable denotes `v`) and choose the
polynomials so that the remaining certificate checks pass (checked by `decide`) while the
conclusion fails. Certificates, `cooper_*_split` and `OrOver` are kernel-reducible.

Run with the lean4 repo's stage1 binary: `lean checks/IntLinearHand.lean`.
-/

open Int.Internal.Linear

-- The restated theorems keep all original binders, some of which the statement no longer uses.
set_option linter.unusedVariables false

section

/-! ## `eq_of_dvd_ediv`, `eq_def'_norm`, `of_var_eq_mul` -/

-- `eq_of_dvd_ediv` (`a : d ∣ p`): `d = 2`, `e = p = 1`, `x = 0 = 1 / 2`, `p' = 1 - 2x = 1`.
example : ¬ ∀ (ctx : Context) (d : Int) (e : Int.Internal.Linear.Expr) (p p' : Poly) (x : Var),
    x.denote ctx = e.denote_k ctx / d → eq_of_dvd_ediv_cert d e p p' x = true →
      p'.denote' ctx = 0 :=
  fun h => absurd (h (.leaf 0) 2 (.num 1) (.num 1) (.add (-2) 0 (.num 1)) 0 (by decide)
    (by decide)) (by decide)

-- `eq_def'_norm` (`a : ePoly = ePoly'`): `x = e = 0`, `ePoly = 0`, `ePoly' = 1`, `p = -x + 1`.
example : ¬ ∀ (ctx : Context) (x : Var) (e : Int.Internal.Linear.Expr) (ePoly ePoly' p : Poly),
    eq_def'_norm_cert x e ePoly ePoly' p = true → x.denote ctx = e.denote_k ctx →
      p.denote' ctx = 0 :=
  fun h => absurd (h (.leaf 0) 0 (.num 0) (.num 0) (.num 1) (.add (-1) 0 (.num 1)) (by decide)
    (by decide)) (by decide)

-- `of_var_eq_mul` (`a : x = k * y`): `x = y = 1`, `k = 0`, `p = x - 0*y = 1`.
example : ¬ ∀ (ctx : Context) (x : Var) (k : Int) (y : Var) (p : Poly),
    of_var_eq_mul_cert x k y p = true → p.denote' ctx = 0 :=
  fun h => absurd (h (.leaf 1) 0 0 0 (.add 1 0 (.add 0 0 (.num 0))) (by decide)) (by decide)

/-! ## `dvd_elim`, `dvd_solve_*`, `eq_dvd_subst`, `dvd_le_tight_mod` -/

-- `dvd_elim` (`a : k₁ ∣ p₁`): `p₁ = 2x + 1`, `k₁ = k₂ = 2`, `p₂ = 1`.
example : ¬ ∀ (ctx : Context) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (p₂ : Poly),
    dvd_elim_cert k₁ p₁ k₂ p₂ = true → k₂ ∣ p₂.denote' ctx :=
  fun h => absurd (h (.leaf 0) 2 (.add 2 0 (.num 1)) 2 (.num 1) (by decide)) (by decide)

-- `dvd_solve_elim` (`a : d₁ ∣ p₁`): `2 ∣ x + 1`, `2 ∣ x` at `x = 0`; `d = 2`, `p = 1`.
example : ¬ ∀ (ctx : Context) (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly),
    dvd_solve_elim_cert d₁ p₁ d₂ p₂ d p = true → d₂ ∣ p₂.denote' ctx → d ∣ p.denote' ctx :=
  fun h => absurd (h (.leaf 0) 2 (.add 1 0 (.num 1)) 2 (.add 1 0 (.num 0)) 2 (.num 1) (by decide)
    (by decide)) (by decide)

-- `dvd_solve_elim` (`a : d₂ ∣ p₂`): `2 ∣ x`, `2 ∣ x + 1` at `x = 0`; `d = 2`, `p = -1`.
example : ¬ ∀ (ctx : Context) (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly),
    dvd_solve_elim_cert d₁ p₁ d₂ p₂ d p = true → d₁ ∣ p₁.denote' ctx → d ∣ p.denote' ctx :=
  fun h => absurd (h (.leaf 0) 2 (.add 1 0 (.num 0)) 2 (.add 1 0 (.num 1)) 2 (.num (-1))
    (by decide) (by decide)) (by decide)

-- `dvd_solve_combine` (`a : d₁ ∣ p₁`): `2 ∣ x + 1`, `1 ∣ x`, `α = 1`, `β = 0`, so `g = 1`,
-- `d = 2`, `p = x + 1`, at `x = 0`.
example : ¬ ∀ (ctx : Context) (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly)
    (g α β : Int),
    dvd_solve_combine_cert d₁ p₁ d₂ p₂ d p g α β = true → d₂ ∣ p₂.denote' ctx →
      d ∣ p.denote' ctx :=
  fun h => absurd (h (.leaf 0) 2 (.add 1 0 (.num 1)) 1 (.add 1 0 (.num 0)) 2 (.add 1 0 (.num 1))
    1 1 0 (by decide) (by decide)) (by decide)

-- `dvd_solve_combine` (`a : d₂ ∣ p₂`): `1 ∣ x`, `2 ∣ x + 1`, `α = 0`, `β = 1`, so `g = 1`,
-- `d = 2`, `p = x + 1`, at `x = 0`.
example : ¬ ∀ (ctx : Context) (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly)
    (g α β : Int),
    dvd_solve_combine_cert d₁ p₁ d₂ p₂ d p g α β = true → d₁ ∣ p₁.denote' ctx →
      d ∣ p.denote' ctx :=
  fun h => absurd (h (.leaf 0) 1 (.add 1 0 (.num 0)) 2 (.add 1 0 (.num 1)) 2 (.add 1 0 (.num 1))
    1 0 1 (by decide) (by decide)) (by decide)

-- `eq_dvd_subst` (`a : p₁ = 0`): `x + 1 = 0`, `2 ∣ x` at `x = 0`; `d₃ = 2`, `p₃ = -1`.
example : ¬ ∀ (ctx : Context) (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d₃ : Int) (p₃ : Poly),
    eq_dvd_subst_cert x p₁ d₂ p₂ d₃ p₃ = true → d₂ ∣ p₂.denote' ctx → d₃ ∣ p₃.denote' ctx :=
  fun h => absurd (h (.leaf 0) 0 (.add 1 0 (.num 1)) 2 (.add 1 0 (.num 0)) 2 (.num (-1))
    (by decide) (by decide)) (by decide)

-- `eq_dvd_subst` (`a : d₂ ∣ p₂`): `x = 0`, `2 ∣ x + 1` at `x = 0`; `d₃ = 2`, `p₃ = 1`.
example : ¬ ∀ (ctx : Context) (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d₃ : Int) (p₃ : Poly),
    eq_dvd_subst_cert x p₁ d₂ p₂ d₃ p₃ = true → p₁.denote' ctx = 0 → d₃ ∣ p₃.denote' ctx :=
  fun h => absurd (h (.leaf 0) 0 (.add 1 0 (.num 0)) 2 (.add 1 0 (.num 1)) 2 (.num 1)
    (by decide) (by decide)) (by decide)

-- `dvd_le_tight_mod` (`a : d ∣ p₁`): `d = g = 2`, `t = 1`, `p₁ = 1`, `p₂ = 0`; then
-- `p₂ - p₁ = -1` and `p₃ = p₂ - cmod (-1) 2 = 1`.
example : ¬ ∀ (ctx : Context) (d : Int) (p₁ p₂ p₃ : Poly) (t g : Int),
    dvd_le_tight_mod_cert d p₁ p₂ p₃ t g = true → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 :=
  fun h => absurd (h (.leaf 0) 2 (.num 1) (.num 0) (.num 1) 1 2 (by decide) (by decide))
    (by decide)

/-! ## `cooper_unsat`: `-x + a ≤ 0`, `x + b ≤ 0`, `2 ∣ x` (`d = 2`, `α = 1`, `β = 0`) -/

-- `cooper_unsat` (`a : p₁ ≤ 0`): `x ≥ 1`, `x ≤ 0`, `x` even; at `x = 0` only `p₁` fails.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d α β : Int),
    cooper_unsat_cert p₁ p₂ p₃ d α β = true → p₂.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx → False :=
  fun h => h (.leaf 0) (.add (-1) 0 (.num 1)) (.add 1 0 (.num 0)) (.add 1 0 (.num 0)) 2 1 0
    (by decide) (by decide) (by decide)

-- `cooper_unsat` (`a : p₂ ≤ 0`): same system at `x = 2`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d α β : Int),
    cooper_unsat_cert p₁ p₂ p₃ d α β = true → p₁.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx → False :=
  fun h => h (.leaf 2) (.add (-1) 0 (.num 1)) (.add 1 0 (.num 0)) (.add 1 0 (.num 0)) 2 1 0
    (by decide) (by decide) (by decide)

-- `cooper_unsat` (`a : d ∣ p₃`): `x ≥ 1`, `x ≤ 1`, `x` even; at `x = 1` only `2 ∣ x` fails.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d α β : Int),
    cooper_unsat_cert p₁ p₂ p₃ d α β = true → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → False :=
  fun h => h (.leaf 1) (.add (-1) 0 (.num 1)) (.add 1 0 (.num (-1))) (.add 1 0 (.num 0)) 2 1 0
    (by decide) (by decide) (by decide)

/-! ## `cooper_left`, `cooper_right`, `cooper_dvd_left`, `cooper_dvd_right`

Dropping the certificate: `n = 0` and all polynomials `0`, so the conclusion is `OrOver 0 _ = False`.
Dropping an inequality or the divisibility: an unsatisfiable system in `x` whose other constraints
hold at the chosen `x`; `n` is the value the certificate demands, and every split case is false. -/

-- `cooper_left` (`a : cooper_left_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (n : Nat),
    p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → OrOver n (cooper_left_split ctx p₁ p₂) :=
  fun h => h (.leaf 0) (.num 0) (.num 0) 0 (by decide) (by decide)

-- `cooper_left` (`a : p₁ ≤ 0`): `-x + 1 ≤ 0`, `x ≤ 0` at `x = 0`, `n = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (n : Nat),
    cooper_left_cert p₁ p₂ n = true → p₂.denote' ctx ≤ 0 →
      OrOver n (cooper_left_split ctx p₁ p₂) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 1)) (.add 1 0 (.num 0)) 1 (by decide)
    (by decide)) (by simp only [OrOver, cooper_left_split]; decide)

-- `cooper_left` (`a : p₂ ≤ 0`): `-x ≤ 0`, `x + 1 ≤ 0` at `x = 0`, `n = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (n : Nat),
    cooper_left_cert p₁ p₂ n = true → p₁.denote' ctx ≤ 0 →
      OrOver n (cooper_left_split ctx p₁ p₂) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 0)) (.add 1 0 (.num 1)) 1 (by decide)
    (by decide)) (by simp only [OrOver, cooper_left_split]; decide)

-- `cooper_right` (`a : cooper_right_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (n : Nat),
    p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → OrOver n (cooper_right_split ctx p₁ p₂) :=
  fun h => h (.leaf 0) (.num 0) (.num 0) 0 (by decide) (by decide)

-- `cooper_right` (`a : p₁ ≤ 0`): `-x + 1 ≤ 0`, `x ≤ 0` at `x = 0`, `n = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (n : Nat),
    cooper_right_cert p₁ p₂ n = true → p₂.denote' ctx ≤ 0 →
      OrOver n (cooper_right_split ctx p₁ p₂) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 1)) (.add 1 0 (.num 0)) 1 (by decide)
    (by decide)) (by simp only [OrOver, cooper_right_split]; decide)

-- `cooper_right` (`a : p₂ ≤ 0`): `-x ≤ 0`, `x + 1 ≤ 0` at `x = 0`, `n = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (n : Nat),
    cooper_right_cert p₁ p₂ n = true → p₁.denote' ctx ≤ 0 →
      OrOver n (cooper_right_split ctx p₁ p₂) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 0)) (.add 1 0 (.num 1)) 1 (by decide)
    (by decide)) (by simp only [OrOver, cooper_right_split]; decide)

-- `cooper_dvd_left` (`a : cooper_dvd_left_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat),
    p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx →
      OrOver n (cooper_dvd_left_split ctx p₁ p₂ p₃ d) :=
  fun h => h (.leaf 0) (.num 0) (.num 0) (.num 0) 1 0 (by decide) (by decide) (by decide)

-- `cooper_dvd_left` (`a : p₁ ≤ 0`): `-x + 1 ≤ 0`, `x ≤ 0`, `1 ∣ x` at `x = 0`, `n = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat),
    cooper_dvd_left_cert p₁ p₂ p₃ d n = true → p₂.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx →
      OrOver n (cooper_dvd_left_split ctx p₁ p₂ p₃ d) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 1)) (.add 1 0 (.num 0)) (.add 1 0 (.num 0)) 1 1
    (by decide) (by decide) (by decide)) (by simp only [OrOver, cooper_dvd_left_split]; decide)

-- `cooper_dvd_left` (`a : p₂ ≤ 0`): `-x ≤ 0`, `x + 1 ≤ 0`, `1 ∣ x` at `x = 0`, `n = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat),
    cooper_dvd_left_cert p₁ p₂ p₃ d n = true → p₁.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx →
      OrOver n (cooper_dvd_left_split ctx p₁ p₂ p₃ d) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 0)) (.add 1 0 (.num 1)) (.add 1 0 (.num 0)) 1 1
    (by decide) (by decide) (by decide)) (by simp only [OrOver, cooper_dvd_left_split]; decide)

-- `cooper_dvd_left` (`a : d ∣ p₃`): `-x ≤ 0`, `x ≤ 0`, `2 ∣ x + 1` at `x = 0`, `n = 2`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat),
    cooper_dvd_left_cert p₁ p₂ p₃ d n = true → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 →
      OrOver n (cooper_dvd_left_split ctx p₁ p₂ p₃ d) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 0)) (.add 1 0 (.num 0)) (.add 1 0 (.num 1)) 2 2
    (by decide) (by decide) (by decide)) (by simp only [OrOver, cooper_dvd_left_split]; decide)

-- `cooper_dvd_right` (`a : cooper_dvd_right_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat),
    p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx →
      OrOver n (cooper_dvd_right_split ctx p₁ p₂ p₃ d) :=
  fun h => h (.leaf 0) (.num 0) (.num 0) (.num 0) 1 0 (by decide) (by decide) (by decide)

-- `cooper_dvd_right` (`a : p₁ ≤ 0`): `-x + 1 ≤ 0`, `x ≤ 0`, `1 ∣ x` at `x = 0`, `n = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat),
    cooper_dvd_right_cert p₁ p₂ p₃ d n = true → p₂.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx →
      OrOver n (cooper_dvd_right_split ctx p₁ p₂ p₃ d) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 1)) (.add 1 0 (.num 0)) (.add 1 0 (.num 0)) 1 1
    (by decide) (by decide) (by decide)) (by simp only [OrOver, cooper_dvd_right_split]; decide)

-- `cooper_dvd_right` (`a : p₂ ≤ 0`): `-x ≤ 0`, `x + 1 ≤ 0`, `1 ∣ x` at `x = 0`, `n = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat),
    cooper_dvd_right_cert p₁ p₂ p₃ d n = true → p₁.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx →
      OrOver n (cooper_dvd_right_split ctx p₁ p₂ p₃ d) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 0)) (.add 1 0 (.num 1)) (.add 1 0 (.num 0)) 1 1
    (by decide) (by decide) (by decide)) (by simp only [OrOver, cooper_dvd_right_split]; decide)

-- `cooper_dvd_right` (`a : d ∣ p₃`): `-x ≤ 0`, `x ≤ 0`, `2 ∣ x + 1` at `x = 0`, `n = 2`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat),
    cooper_dvd_right_cert p₁ p₂ p₃ d n = true → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 →
      OrOver n (cooper_dvd_right_split ctx p₁ p₂ p₃ d) :=
  fun h => absurd (h (.leaf 0) (.add (-1) 0 (.num 0)) (.add 1 0 (.num 0)) (.add 1 0 (.num 1)) 2 2
    (by decide) (by decide) (by decide)) (by simp only [OrOver, cooper_dvd_right_split]; decide)

/-! ## The `cooper_*_split_*` projections

Dropping the split hypothesis: the certificate only fixes `p'` (and the coefficient) from the
polynomials, e.g. `p₁ = 2x + 1` gives `a = 2`, `p' = 1`, and `2 ∤ 1`.
Dropping the certificate: all polynomials `0` and `k = 0` make the split hold (leading
coefficients of constants are `1`), and `p' = 1` with coefficient `2` (or `0` for `≤`) fails. -/

-- `cooper_left_split_ineq` (`a : cooper_left_split_ineq_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (b : Int) (p' : Poly),
    cooper_left_split ctx p₁ p₂ k → p'.denote' ctx ≤ 0 :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) 0 0 (.num 1)
    (by unfold cooper_left_split; decide)) (by decide)

-- `cooper_right_split_ineq` (`a : cooper_right_split_ineq_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (a : Int) (p' : Poly),
    cooper_right_split ctx p₁ p₂ k → p'.denote' ctx ≤ 0 :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) 0 0 (.num 1)
    (by unfold cooper_right_split; decide)) (by decide)

-- `cooper_dvd_left_split_ineq` (`a : cooper_dvd_left_split_ineq_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (b : Int) (p' : Poly),
    cooper_dvd_left_split ctx p₁ p₂ p₃ d k → p'.denote' ctx ≤ 0 :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) (.num 0) 1 0 0 (.num 1)
    (by unfold cooper_dvd_left_split; decide)) (by decide)

-- `cooper_dvd_right_split_ineq` (`a : cooper_dvd_right_split_ineq_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (a : Int) (p' : Poly),
    cooper_dvd_right_split ctx p₁ p₂ p₃ d k → p'.denote' ctx ≤ 0 :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) (.num 0) 1 0 0 (.num 1)
    (by unfold cooper_dvd_right_split; decide)) (by decide)

-- `cooper_left_split_dvd` (`a : cooper_left_split ctx p₁ p₂ k`): `p₁ = 2x + 1`, `a = 2`, `p' = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (a : Int) (p' : Poly),
    cooper_left_split_dvd_cert p₁ p' a k = true → a ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.add 2 0 (.num 1)) (.num 0) 0 2 (.num 1) (by decide)) (by decide)

-- `cooper_left_split_dvd` (`a : cooper_left_split_dvd_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (a : Int) (p' : Poly),
    cooper_left_split ctx p₁ p₂ k → a ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) 0 2 (.num 1)
    (by unfold cooper_left_split; decide)) (by decide)

-- `cooper_right_split_dvd` (`a : cooper_right_split ctx p₁ p₂ k`): `p₂ = 2x + 1`, `b = 2`, `p' = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (b : Int) (p' : Poly),
    cooper_right_split_dvd_cert p₂ p' b k = true → b ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.add 2 0 (.num 1)) 0 2 (.num 1) (by decide)) (by decide)

-- `cooper_right_split_dvd` (`a : cooper_right_split_dvd_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (b : Int) (p' : Poly),
    cooper_right_split ctx p₁ p₂ k → b ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) 0 2 (.num 1)
    (by unfold cooper_right_split; decide)) (by decide)

-- `cooper_dvd_left_split_dvd1` (`a : cooper_dvd_left_split …`): `p₁ = 2x + 1`, `a = 2`, `p' = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (a : Int) (p' : Poly),
    cooper_dvd_left_split_dvd1_cert p₁ p' a k = true → a ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.add 2 0 (.num 1)) (.num 0) (.num 0) 1 0 2 (.num 1) (by decide))
    (by decide)

-- `cooper_dvd_left_split_dvd1` (`a : cooper_dvd_left_split_dvd1_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (a : Int) (p' : Poly),
    cooper_dvd_left_split ctx p₁ p₂ p₃ d k → a ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) (.num 0) 1 0 2 (.num 1)
    (by unfold cooper_dvd_left_split; decide)) (by decide)

-- `cooper_dvd_right_split_dvd1` (`a : cooper_dvd_right_split …`): `p₂ = 2x + 1`, `b = 2`, `p' = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (b : Int) (p' : Poly),
    cooper_dvd_right_split_dvd1_cert p₂ p' b k = true → b ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.add 2 0 (.num 1)) (.num 0) 1 0 2 (.num 1) (by decide))
    (by decide)

-- `cooper_dvd_right_split_dvd1` (`a : cooper_dvd_right_split_dvd1_cert …`)
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (b : Int) (p' : Poly),
    cooper_dvd_right_split ctx p₁ p₂ p₃ d k → b ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) (.num 0) 1 0 2 (.num 1)
    (by unfold cooper_dvd_right_split; decide)) (by decide)

-- `cooper_dvd_left_split_dvd2` (`a : cooper_dvd_left_split_dvd2_cert …`): split holds for all
-- polynomials `0`, `d = 1`, `k = 0`; `d' = 2`, `p' = 1`.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (d' : Int) (p' : Poly),
    cooper_dvd_left_split ctx p₁ p₂ p₃ d k → d' ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) (.num 0) 1 0 2 (.num 1)
    (by unfold cooper_dvd_left_split; decide)) (by decide)

-- `cooper_dvd_right_split_dvd2` (`a : cooper_dvd_right_split_dvd2_cert …`): as above.
example : ¬ ∀ (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (d' : Int) (p' : Poly),
    cooper_dvd_right_split ctx p₁ p₂ p₃ d k → d' ∣ p'.denote' ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 0) (.num 0) 1 0 2 (.num 1)
    (by unfold cooper_dvd_right_split; decide)) (by decide)

/-! ## `OrOver` -/

-- `orOver_cases` (`a : OrOver (n+1) p`): `n = 0`, `p := fun _ => False`; `OrOver_cases_type 0 p`
-- is `p 0`.
example : ¬ ∀ {n : Nat} {p : Nat → Prop}, OrOver_cases_type n p :=
  fun h => h (n := 0) (p := fun _ => False)

-- `orOver_resolve` (`a : OrOver (n+1) p`): `n = 0`, `p := fun _ => False`; `OrOver 0 p` is `False`.
example : ¬ ∀ {n : Nat} {p : Nat → Prop}, ¬ p n → OrOver n p :=
  fun h => h (n := 0) (p := fun _ => False) id

-- `orOver_resolve` (`a : ¬ p n`): `n = 0`, `p := fun _ => True`; `OrOver 1 p` holds.
example : ¬ ∀ {n : Nat} {p : Nat → Prop}, OrOver (n + 1) p → OrOver n p :=
  fun h => h (n := 0) (p := fun _ => True) (Or.inl trivial)

end
