import Lean

/-!
Hand pass `Adapter` (hand12): the 60 unresolved hypotheses of `Init.Grind.Ring.CommSemiringAdapter`
(32 theorems). For hypothesis `hᵢ` of `T`, each declaration proves `¬T'` (`drop0% T i`, universes set
to `0`) or `T'` (`drop% T i`, universes kept). 55 necessary, 5 removable, 0 independent.

Reusable models and helpers (namespace `AdapterHand`):
* `not_nn`: refutes `p.NonnegCoeffs` from `p.nonneg_k = false`, which `decide +kernel` evaluates for
  any concrete result of `addConst`/`insert`/`mulConst`/`mulMon`/`mulMon_nc`/`combine`/`mul`/`pow`/
  `pairs_k`/`foldr_k`/`sumB_k`/… (`nonneg_k_of_nn` is the converse of the library's
  `nonnegCoeffs_of_nonneg_k`). `nn0`, `nn1`: `NonnegCoeffs` of the constants `0`, `1`.
* Cancellation in a non-normalized polynomial: `x₀ + (-1)·x₀` (`cancelPoly`) has `denoteS = x₀`
  (the negative coefficient counts as `0`), but every operation that merges equal monomials (`insert`
  in `mulMon_nc.go`, `combine` in `mul.go`/`mul_nc.go`) cancels it to `0`. Refutes dropping a
  `NonnegCoeffs` premise of the multiplicative lemmas that accumulate (`denoteS_mulMon_nc`, `denoteS_mul`,
  `denoteS_mul_nc`); over `Nat` with `ctx = .leaf 1`, `decide +kernel`.
* `BS`: the Boolean semiring (`||`, `&&`) on a copy of `Bool`, a `Semiring` without
  `AddRightCancel`: `true + true = false + true`, so `toQ false = toQ true` in the ring envelope
  (`BS.toQ_eq`).
* `natRightCancel`: `AddRightCancel Nat`, to separate `Nat` values in `Ring.OfSemiring.Q Nat`.
* Order models over `Nat`: `LE` as `<` (not a preorder), `LT` as `True` (not lawful).
* Removable (multiplicative sign lemmas): `CoeffsAll P p` (every coefficient satisfies `P`);
  `denoteS_mulConst_gen`/`denoteS_mulMon_gen` need only `(k * c).toNat = k.toNat * c.toNat` for the
  coefficients `c`, which holds as soon as `k ≥ 0` or `c ≥ 0` (`toNat_mul_left/right`);
  `denoteS_nonpos`/`insert_nonpos`/`mulMon_nc_go_nonpos`: a polynomial with only non-positive
  coefficients denotes `0`, and `mulMon_nc.go` with `k < 0` on a non-negative polynomial keeps them so.

Run with the lean4 repo's stage1 binary: `runs/hand12/lean.sh checks/AdapterHand.lean`.
-/

set_option linter.unusedVariables false

open Lean Meta Elab Term in
/-- `drop% T i` (universes kept) resp. `drop0% T i` (universes `0`): `T` with its non-dependent Prop binder `i` dropped. -/
def AdapterHand.dropType (T : Syntax) (i : Nat) (zero : Bool) : TermElabM Expr := do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => Level.zero) else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i]!
    unless ← isProp (← inferType x) do throwError "binder {i} of {n} is not a Prop"
    for j in [i+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i) body

elab "drop% " T:ident i:num : term => AdapterHand.dropType T i.getNat false
elab "drop0% " T:ident i:num : term => AdapterHand.dropType T i.getNat true

open Lean.Grind CommRing
attribute [local instance] Semiring.natCast Ring.intCast
open AddCommMonoid AddCommGroup
open Semiring hiding add_zero add_comm add_assoc
open CommSemiring

namespace AdapterHand

/-! ## Helpers: refuting `NonnegCoeffs`, cancellation, `BS`, order models -/

theorem nonneg_k_of_nn {p : Poly} (h : p.NonnegCoeffs) : p.nonneg_k = true := by
  induction h with
  | num c hc =>
    show Bool.rec (motive := fun _ => Bool) true false (Int.blt' c (Int.ofNat 0)) = true
    rw [show Int.blt' c (Int.ofNat 0) = false by simp; omega]
  | add a m p ha _ ih =>
    show Bool.rec (motive := fun _ => Bool) p.nonneg_k false (Int.blt' a (Int.ofNat 0)) = true
    rw [show Int.blt' a (Int.ofNat 0) = false by simp; omega]; exact ih

theorem not_nn {p : Poly} (h : p.nonneg_k = false) : ¬ p.NonnegCoeffs :=
  fun hp => by rw [nonneg_k_of_nn hp] at h; cases h

theorem nn0 : (Poly.num 0).NonnegCoeffs := .num 0 (by decide)
theorem nn1 : (Poly.num 1).NonnegCoeffs := .num 1 (by decide)

/-- The monomial `x₀`. -/
abbrev x0 : Mon := .mult ⟨0, 1⟩ .unit
/-- `x₀ + (-1)·x₀ + 0`, not normalized. -/
abbrev cancelPoly : Poly := .add 1 x0 (.add (-1) x0 (.num 0))

/-- The Boolean semiring on a copy of `Bool`. -/
def BS : Type := Bool

instance : DecidableEq BS := inferInstanceAs (DecidableEq Bool)
instance : Add BS := ⟨Bool.or⟩
instance : Mul BS := ⟨Bool.and⟩
instance : NatCast BS := ⟨fun n => decide (n ≠ 0)⟩
instance (n : Nat) : OfNat BS n := ⟨decide (n ≠ 0)⟩
instance : SMul Nat BS := ⟨fun n a => Bool.and (decide (n ≠ 0)) a⟩
instance : HPow BS Nat BS := ⟨fun a n => Bool.or (decide (n = 0)) a⟩

instance BS.semiring : Semiring BS where
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  pow_zero a := by cases a <;> rfl
  pow_succ a n := by
    show Bool.or (decide (n + 1 = 0)) a = Bool.and (Bool.or (decide (n = 0)) a) a
    cases a <;> simp
  ofNat_succ n := by
    show decide (n + 1 ≠ 0) = Bool.or (decide (n ≠ 0)) (decide (1 ≠ 0))
    simp

theorem BS.toQ_eq : Ring.OfSemiring.toQ (α := BS) false = Ring.OfSemiring.toQ (α := BS) true :=
  Quot.sound ⟨true, rfl⟩

instance natRightCancel : AddRightCancel Nat := ⟨fun _ _ _ h => Nat.add_right_cancel h⟩


/-! ## Necessary: `NonnegCoeffs` closure lemmas (`not_nn`) -/

-- `Lean.Grind.CommRing.Poly.addConst_NonnegCoeffs`: `k = -1`, `p = 0` gives `num (-1)`.
theorem addConst_NonnegCoeffs_h2 : ¬ drop0% Lean.Grind.CommRing.Poly.addConst_NonnegCoeffs 2 :=
  fun h => not_nn (by decide +kernel) (h (p := .num 0) (k := -1) nn0)

-- `Lean.Grind.CommRing.Poly.addConst_NonnegCoeffs`: `k = 0` returns `p = num (-1)`.
theorem addConst_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.addConst_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (p := .num (-1)) (k := 0) (by decide))

-- `Lean.Grind.CommRing.Poly.insert_Nonneg`: `k = -1` at the unit monomial into `0` gives `num (-1)`.
theorem insert_Nonneg_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.insert_Nonneg 3 :=
  fun h => not_nn (by decide +kernel) (h (-1) .unit (.num 0) nn0)

-- `Lean.Grind.CommRing.Poly.insert_Nonneg`: `k = 0` returns `p = num (-1)`.
theorem insert_Nonneg_h4 : ¬ drop0% Lean.Grind.CommRing.Poly.insert_Nonneg 4 :=
  fun h => not_nn (by decide +kernel) (h 0 .unit (.num (-1)) (by decide))

-- `Lean.Grind.CommRing.Poly.mulConst_NonnegCoeffs`: `-1 * 1`.
theorem mulConst_NonnegCoeffs_h2 : ¬ drop0% Lean.Grind.CommRing.Poly.mulConst_NonnegCoeffs 2 :=
  fun h => not_nn (by decide +kernel) (h (p := .num 1) (k := -1) nn1)

-- `Lean.Grind.CommRing.Poly.mulConst_NonnegCoeffs`: `1 * (-1)`.
theorem mulConst_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.mulConst_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (p := .num (-1)) (k := 1) (by decide))

-- `Lean.Grind.CommRing.Poly.mulMon_NonnegCoeffs`: `-1 * 1` at the unit monomial.
theorem mulMon_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.mulMon_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (p := .num 1) (k := -1) .unit nn1)

-- `Lean.Grind.CommRing.Poly.mulMon_NonnegCoeffs`: `1 * (-1)` at the unit monomial.
theorem mulMon_NonnegCoeffs_h4 : ¬ drop0% Lean.Grind.CommRing.Poly.mulMon_NonnegCoeffs 4 :=
  fun h => not_nn (by decide +kernel) (h (p := .num (-1)) (k := 1) .unit (by decide))

-- `Lean.Grind.CommRing.Poly.mulMon_nc_go_NonnegCoeffs`: `k = -1`, `p = 1`, `acc = 0`.
theorem mulMon_nc_go_NonnegCoeffs_h4 : ¬ drop0% Lean.Grind.CommRing.Poly.mulMon_nc_go_NonnegCoeffs 4 :=
  fun h => not_nn (by decide +kernel) (h (p := .num 1) (k := -1) .unit (acc := .num 0) nn1 nn0)

-- `Lean.Grind.CommRing.Poly.mulMon_nc_go_NonnegCoeffs`: `k = 1`, `p = -1`, `acc = 0`.
theorem mulMon_nc_go_NonnegCoeffs_h5 : ¬ drop0% Lean.Grind.CommRing.Poly.mulMon_nc_go_NonnegCoeffs 5 :=
  fun h => not_nn (by decide +kernel) (h (p := .num (-1)) (k := 1) .unit (acc := .num 0) (by decide) nn0)

-- `Lean.Grind.CommRing.Poly.mulMon_nc_go_NonnegCoeffs`: `p = 0` leaves `acc = -1`.
theorem mulMon_nc_go_NonnegCoeffs_h6 : ¬ drop0% Lean.Grind.CommRing.Poly.mulMon_nc_go_NonnegCoeffs 6 :=
  fun h => not_nn (by decide +kernel) (h (p := .num 0) (k := 0) .unit (acc := .num (-1)) (by decide) nn0)

-- `Lean.Grind.CommRing.Poly.mulMon_nc_NonnegCoeffs`: `-1 * 1` at the unit monomial.
theorem mulMon_nc_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.mulMon_nc_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (p := .num 1) (k := -1) .unit nn1)

-- `Lean.Grind.CommRing.Poly.mulMon_nc_NonnegCoeffs`: `1 * (-1)` at the unit monomial.
theorem mulMon_nc_NonnegCoeffs_h4 : ¬ drop0% Lean.Grind.CommRing.Poly.mulMon_nc_NonnegCoeffs 4 :=
  fun h => not_nn (by decide +kernel) (h (p := .num (-1)) (k := 1) .unit (by decide))

-- `Lean.Grind.CommRing.Poly.concat_NonnegCoeffs`: `-1` and `0`.
theorem concat_NonnegCoeffs_h2 : ¬ drop0% Lean.Grind.CommRing.Poly.concat_NonnegCoeffs 2 :=
  fun h => not_nn (by decide +kernel) (h (p₁ := .num (-1)) (p₂ := .num 0) nn0)

-- `Lean.Grind.CommRing.Poly.concat_NonnegCoeffs`: `0` and `-1`.
theorem concat_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.concat_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (p₁ := .num 0) (p₂ := .num (-1)) nn0)

-- `Lean.Grind.CommRing.Poly.combine_NonnegCoeffs`: `-1` and `0`.
theorem combine_NonnegCoeffs_h2 : ¬ drop0% Lean.Grind.CommRing.Poly.combine_NonnegCoeffs 2 :=
  fun h => not_nn (by decide +kernel) (h (p₁ := .num (-1)) (p₂ := .num 0) nn0)

-- `Lean.Grind.CommRing.Poly.combine_NonnegCoeffs`: `0` and `-1`.
theorem combine_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.combine_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (p₁ := .num 0) (p₂ := .num (-1)) nn0)

-- `Lean.Grind.CommRing.Poly.mul_go_NonnegCoeffs`: `p₁ = -1`, `p₂ = 1`, `acc = 0`.
theorem mul_go_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_go_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (.num (-1)) (.num 1) (.num 0) nn1 nn0)

-- `Lean.Grind.CommRing.Poly.mul_go_NonnegCoeffs`: `p₁ = 1`, `p₂ = -1`, `acc = 0`.
theorem mul_go_NonnegCoeffs_h4 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_go_NonnegCoeffs 4 :=
  fun h => not_nn (by decide +kernel) (h (.num 1) (.num (-1)) (.num 0) nn1 nn0)

-- `Lean.Grind.CommRing.Poly.mul_go_NonnegCoeffs`: `p₁ = p₂ = 0`, `acc = -1`.
theorem mul_go_NonnegCoeffs_h5 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_go_NonnegCoeffs 5 :=
  fun h => not_nn (by decide +kernel) (h (.num 0) (.num 0) (.num (-1)) nn0 nn0)

-- `Lean.Grind.CommRing.Poly.mul_NonnegCoeffs`: `-1 * 1`.
theorem mul_NonnegCoeffs_h2 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_NonnegCoeffs 2 :=
  fun h => not_nn (by decide +kernel) (h (p₁ := .num (-1)) (p₂ := .num 1) nn1)

-- `Lean.Grind.CommRing.Poly.mul_NonnegCoeffs`: `1 * (-1)`.
theorem mul_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (p₁ := .num 1) (p₂ := .num (-1)) nn1)

-- `Lean.Grind.CommRing.Poly.mul_nc_go_NonnegCoeffs`: `p₁ = -1`, `p₂ = 1`, `acc = 0`.
theorem mul_nc_go_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_nc_go_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (.num (-1)) (.num 1) (.num 0) nn1 nn0)

-- `Lean.Grind.CommRing.Poly.mul_nc_go_NonnegCoeffs`: `p₁ = 1`, `p₂ = -1`, `acc = 0`.
theorem mul_nc_go_NonnegCoeffs_h4 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_nc_go_NonnegCoeffs 4 :=
  fun h => not_nn (by decide +kernel) (h (.num 1) (.num (-1)) (.num 0) nn1 nn0)

-- `Lean.Grind.CommRing.Poly.mul_nc_go_NonnegCoeffs`: `p₁ = p₂ = 0`, `acc = -1`.
theorem mul_nc_go_NonnegCoeffs_h5 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_nc_go_NonnegCoeffs 5 :=
  fun h => not_nn (by decide +kernel) (h (.num 0) (.num 0) (.num (-1)) nn0 nn0)

-- `Lean.Grind.CommRing.Poly.mul_nc_NonnegCoeffs`: `-1 * 1`.
theorem mul_nc_NonnegCoeffs_h2 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_nc_NonnegCoeffs 2 :=
  fun h => not_nn (by decide +kernel) (h (p₁ := .num (-1)) (p₂ := .num 1) nn1)

-- `Lean.Grind.CommRing.Poly.mul_nc_NonnegCoeffs`: `1 * (-1)`.
theorem mul_nc_NonnegCoeffs_h3 : ¬ drop0% Lean.Grind.CommRing.Poly.mul_nc_NonnegCoeffs 3 :=
  fun h => not_nn (by decide +kernel) (h (p₁ := .num 1) (p₂ := .num (-1)) nn1)

-- `Lean.Grind.CommRing.Poly.pow_NonnegCoeffs`: `(-1) ^ 1`.
theorem pow_NonnegCoeffs_h2 : ¬ drop0% Lean.Grind.CommRing.Poly.pow_NonnegCoeffs 2 :=
  fun h => not_nn (by decide +kernel) (h (p := .num (-1)) 1)

-- `Lean.Grind.CommRing.Poly.pow_nc_NonnegCoeffs`: `(-1) ^ 1`.
theorem pow_nc_NonnegCoeffs_h2 : ¬ drop0% Lean.Grind.CommRing.Poly.pow_nc_NonnegCoeffs 2 :=
  fun h => not_nn (by decide +kernel) (h (p := .num (-1)) 1)

-- `Lean.Grind.CommRing.Poly.nonnegCoeffs_of_nonneg_k`: `num (-1)`.
theorem nonnegCoeffs_of_nonneg_k_h1 : ¬ drop0% Lean.Grind.CommRing.Poly.nonnegCoeffs_of_nonneg_k 1 :=
  fun h => not_nn (by decide +kernel) (h (p := .num (-1)))

/-! ## Necessary: balanced sums (`NonnegList` conjunct fails) -/

-- `Lean.Grind.CommRing.Poly.pairs_k_nonneg`: `ps = [-1]`, `pend = none`.
theorem pairs_k_nonneg_h5 : ¬ drop0% Lean.Grind.CommRing.Poly.pairs_k_nonneg 5 :=
  fun h => not_nn (by decide +kernel) ((h (α := Nat) (.leaf 0) [.num (-1)] none (fun _ h => nomatch h)).1.1)

-- `Lean.Grind.CommRing.Poly.pairs_k_nonneg`: `ps = []`, `pend = some (-1)`.
theorem pairs_k_nonneg_h6 : ¬ drop0% Lean.Grind.CommRing.Poly.pairs_k_nonneg 6 :=
  fun h => not_nn (by decide +kernel) ((h (α := Nat) (.leaf 0) [] (some (.num (-1))) trivial).1.1)

-- `Lean.Grind.CommRing.Poly.foldr_k_nonneg`: `ps = [-1]`.
theorem foldr_k_nonneg_h4 : ¬ drop0% Lean.Grind.CommRing.Poly.foldr_k_nonneg 4 :=
  fun h => not_nn (by decide +kernel) ((h (α := Nat) (.leaf 0) [.num (-1)]).1)

-- `Lean.Grind.CommRing.Poly.sumGo_k_nonneg`: no fuel, `ps = [-1]`.
theorem sumGo_k_nonneg_h5 : ¬ drop0% Lean.Grind.CommRing.Poly.sumGo_k_nonneg 5 :=
  fun h => not_nn (by decide +kernel) ((h (α := Nat) (.leaf 0) [] [.num (-1)]).1)

-- `Lean.Grind.CommRing.Poly.sumB_k_nonneg`: `ps = [-1]`.
theorem sumB_k_nonneg_h4 : ¬ drop0% Lean.Grind.CommRing.Poly.sumB_k_nonneg 4 :=
  fun h => not_nn (by decide +kernel) ((h (α := Nat) (.leaf 0) [.num (-1)]).1)

-- `Lean.Grind.CommRing.Expr.sumsSB_k_nonneg`: `e = 0`, `acc = [-1]`.
theorem sumsSB_k_nonneg_h5 : ¬ drop0% Lean.Grind.CommRing.Expr.sumsSB_k_nonneg 5 :=
  fun h => not_nn (by decide +kernel) ((h (α := Nat) (.leaf 0) (.num 0) [.num (-1)]).1.2.1)

/-! ## Necessary: denotation lemmas (`Nat`, `decide +kernel`) -/

-- `Lean.Grind.CommRing.Poly.denoteS_mulMon_nc`: `2·x₀ * (x₀ + (-1)·x₀)` cancels to `0`, but the
-- right side is `2 * 1 * 1` (`ctx = .leaf 1`).
theorem denoteS_mulMon_nc_h7 : ¬ drop0% Lean.Grind.CommRing.Poly.denoteS_mulMon_nc 7 := by
  intro h
  have := h (α := Nat) (.leaf 1) 2 x0 cancelPoly (by decide)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Poly.denoteS_mul`: `(x₀ + (-1)·x₀) * 1` is `0`, the right side `1`.
theorem denoteS_mul_h5 : ¬ drop0% Lean.Grind.CommRing.Poly.denoteS_mul 5 := by
  intro h
  have := h (α := Nat) (.leaf 1) cancelPoly (.num 1) nn1
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Poly.denoteS_mul`: `(x₀ + 1) * (x₀ - 1) = x₀² - 1` denotes `1`, the right
-- side `2 * 1` (`-1` counts as `0`).
theorem denoteS_mul_h6 : ¬ drop0% Lean.Grind.CommRing.Poly.denoteS_mul 6 := by
  intro h
  have := h (α := Nat) (.leaf 1) (.add 1 x0 (.num 1)) (.add 1 x0 (.num (-1)))
    (.add _ _ _ (by decide) (.num _ (by decide)))
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Poly.denoteS_mul_nc`: as for `Lean.Grind.CommRing.Poly.denoteS_mul`.
theorem denoteS_mul_nc_h5 : ¬ drop0% Lean.Grind.CommRing.Poly.denoteS_mul_nc 5 := by
  intro h
  have := h (α := Nat) (.leaf 1) cancelPoly (.num 1) nn1
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Poly.denoteS_mul_nc`: `(x₀ + 1) * (x₀ - 1)`.
theorem denoteS_mul_nc_h6 : ¬ drop0% Lean.Grind.CommRing.Poly.denoteS_mul_nc 6 := by
  intro h
  have := h (α := Nat) (.leaf 1) (.add 1 x0 (.num 1)) (.add 1 x0 (.num (-1)))
    (.add _ _ _ (by decide) (.num _ (by decide)))
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_toExpr`: `a = p = 0`, `b = 1`.
theorem eq_of_denoteS_eq_toExpr_h7 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_toExpr 7 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 0) (.num 1) (.num 0) ⟨rfl, nn0⟩
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr`: everything `0` but `b = 1`.
theorem eq_of_denoteS_eq_add_toExpr_h9 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr 9 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 0) (.num 1) (.num 0) (.num 0) (.num 0) ⟨rfl, nn0⟩ rfl rfl
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr`: `a = p = 0`, `q = 1`, `r = 0`, so
-- `b = 1 + 0` although `p ≠ q + r`.
theorem eq_of_denoteS_eq_add_toExpr_h10 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr 10 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 0) _ (.num 0) (.num 1) (.num 0) ⟨rfl, nn0⟩ rfl rfl
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr`: `q = -1`, `r = 1`, `p = q + r = 0`, but
-- `b = num (-1) + num 1` denotes `1 + 1` (the semiring denotation of a numeral takes `natAbs`).
theorem eq_of_denoteS_eq_add_toExpr_h11 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr 11 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 0) _ (.num 0) (.num (-1)) (.num 1) ⟨rfl, nn0⟩ rfl rfl
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_denoteS_eq`: `lhs = 1`, `rhs = p = 0`.
theorem eq_true_of_denoteS_eq_h6 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_denoteS_eq 6 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 1) (.num 0) (.num 0) ⟨rfl, nn0⟩
  exact absurd (of_eq_true this) (by decide)

-- `Lean.Grind.CommRing.eq_true_of_denoteS_eq`: `lhs = p = 0`, `rhs = 1`.
theorem eq_true_of_denoteS_eq_h7 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_denoteS_eq 7 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 0) (.num 1) (.num 0) ⟨rfl, nn0⟩
  exact absurd (of_eq_true this) (by decide)

-- `Lean.Grind.CommRing.le_true_of_denoteS_eq`: `LE Nat` as `<` (not reflexive), all sides `0`.
theorem le_true_of_denoteS_eq_h3 : ¬ drop0% Lean.Grind.CommRing.le_true_of_denoteS_eq 3 := by
  intro h
  have := @h Nat _ ⟨fun a b => a < b⟩ (.leaf 0) (.num 0) (.num 0) (.num 0) ⟨rfl, nn0⟩ ⟨rfl, nn0⟩
  exact Nat.lt_irrefl _ (of_eq_true this)

-- `Lean.Grind.CommRing.le_true_of_denoteS_eq`: `lhs = 1`, `rhs = p = 0`.
theorem le_true_of_denoteS_eq_h8 : ¬ drop0% Lean.Grind.CommRing.le_true_of_denoteS_eq 8 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 1) (.num 0) (.num 0) ⟨rfl, nn0⟩
  exact absurd (of_eq_true this) (by decide)

-- `Lean.Grind.CommRing.le_true_of_denoteS_eq`: `lhs = p = 1`, `rhs = 0`.
theorem le_true_of_denoteS_eq_h9 : ¬ drop0% Lean.Grind.CommRing.le_true_of_denoteS_eq 9 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 1) (.num 0) (.num 1) ⟨rfl, nn1⟩
  exact absurd (of_eq_true this) (by decide)

-- `Lean.Grind.CommRing.lt_false_of_denoteS_eq`: `LT Nat` as `True` (not lawful), all sides `0`.
theorem lt_false_of_denoteS_eq_h4 : ¬ drop0% Lean.Grind.CommRing.lt_false_of_denoteS_eq 4 := by
  intro h
  have := @h Nat _ _ ⟨fun _ _ => True⟩ _ (.leaf 0) (.num 0) (.num 0) (.num 0) ⟨rfl, nn0⟩ ⟨rfl, nn0⟩
  exact of_eq_false this trivial

-- `Lean.Grind.CommRing.lt_false_of_denoteS_eq`: `lhs = 0`, `rhs = p = 1`.
theorem lt_false_of_denoteS_eq_h10 : ¬ drop0% Lean.Grind.CommRing.lt_false_of_denoteS_eq 10 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 0) (.num 1) (.num 1) ⟨rfl, nn1⟩
  exact of_eq_false this (by decide)

-- `Lean.Grind.CommRing.lt_false_of_denoteS_eq`: `lhs = p = 0`, `rhs = 1`.
theorem lt_false_of_denoteS_eq_h11 : ¬ drop0% Lean.Grind.CommRing.lt_false_of_denoteS_eq 11 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 0) (.num 1) (.num 0) ⟨rfl, nn0⟩
  exact of_eq_false this (by decide)

/-! ## Necessary: the ring envelope -/

-- `Lean.Grind.Ring.OfSemiring.of_eq`: over `Nat`, `toQ 0 ≠ toQ 1` (`toQ` is injective for
-- cancellative semirings).
theorem of_eq_h5 : ¬ drop0% Lean.Grind.Ring.OfSemiring.of_eq 5 := by
  intro h
  have := h (α := Nat) (.leaf 0) (.num 0) (.num 1)
  rw [Expr.denoteAsRing_eq, Expr.denoteAsRing_eq] at this
  exact absurd (Ring.OfSemiring.toQ_inj this) (by decide)

-- `Lean.Grind.Ring.OfSemiring.of_diseq`: in the Boolean semiring `BS`, `0 ≠ 1` but
-- `toQ 0 = toQ 1`.
theorem of_diseq_h2 : ¬ drop0% Lean.Grind.Ring.OfSemiring.of_diseq 2 := by
  intro h
  have := h (α := BS) (.leaf false) (.num 0) (.num 1) (by decide)
  rw [Expr.denoteAsRing_eq, Expr.denoteAsRing_eq] at this
  exact this BS.toQ_eq


/-! ## Helpers for the removable verdicts -/

/-- Every coefficient of the polynomial satisfies `P`. -/
def CoeffsAll (P : Int → Prop) : Poly → Prop
  | .num c => P c
  | .add c _ p => P c ∧ CoeffsAll P p

theorem coeffsAll_of_nn {p : Poly} (h : p.NonnegCoeffs) : CoeffsAll (0 ≤ ·) p := by
  induction h with
  | num c hc => exact hc
  | add a m p ha _ ih => exact ⟨ha, ih⟩

theorem coeffsAll_mono {P Q : Int → Prop} (hPQ : ∀ c, P c → Q c) : ∀ {p : Poly}, CoeffsAll P p → CoeffsAll Q p
  | .num c, h => hPQ c h
  | .add c _ p, h => ⟨hPQ c h.1, coeffsAll_mono hPQ h.2⟩

theorem coeffsAll_true {P : Int → Prop} (hP : ∀ c, P c) : ∀ {p : Poly}, CoeffsAll P p
  | .num c => hP c
  | .add c _ p => ⟨hP c, coeffsAll_true hP⟩

theorem toNat_mul_left {a b : Int} (ha : 0 ≤ a) : (a * b).toNat = a.toNat * b.toNat := by
  by_cases hb : 0 ≤ b
  · exact Int.toNat_mul ha hb
  · rw [Int.toNat_of_nonpos (Int.mul_nonpos_of_nonneg_of_nonpos ha (by omega)),
      Int.toNat_of_nonpos (z := b) (by omega), Nat.mul_zero]

theorem toNat_mul_right {a b : Int} (hb : 0 ≤ b) : (a * b).toNat = a.toNat * b.toNat := by
  rw [Int.mul_comm, toNat_mul_left hb, Nat.mul_comm]

attribute [local simp] natCast_one natCast_zero zero_mul mul_zero one_mul mul_one add_zero zero_add denoteSInt_eq

/-- `Poly.denoteS_mulConst` for every `k` and `p` whose coefficients `c` satisfy
`(k * c).toNat = k.toNat * c.toNat`. -/
theorem denoteS_mulConst_gen {α} [Semiring α] (ctx : Context α) (k : Int) (p : Poly)
    (h : CoeffsAll (fun c => (k * c).toNat = k.toNat * c.toNat) p) :
    (Poly.mulConst k p).denoteS ctx = k.toNat * p.denoteS ctx := by
  simp only [Poly.mulConst, Bool.cond_eq_ite]
  split
  · next h0 => simp at h0; subst h0; simp [Poly.denoteS]
  · split
    · next h1 => simp at h1; subst h1; simp
    · induction p with
      | num c => simp only [Poly.mulConst.go, Poly.denoteS, denoteSInt_eq]; rw [show (k * c).toNat = _ from h, Semiring.natCast_mul]
      | add c m p ih =>
        simp only [Poly.mulConst.go, Poly.denoteS, denoteSInt_eq]
        rw [h.1, Semiring.natCast_mul, left_distrib, mul_assoc, ih h.2]

theorem denoteS_mulMon_gen {α} [CommSemiring α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    (h : CoeffsAll (fun c => (k * c).toNat = k.toNat * c.toNat) p) :
    (Poly.mulMon k m p).denoteS ctx = k.toNat * m.denote ctx * p.denoteS ctx := by
  simp only [Poly.mulMon, Bool.cond_eq_ite]
  split
  · next h0 => simp at h0; subst h0; simp [Poly.denoteS]
  · split
    · next hm => simp at hm; subst hm; rw [denoteS_mulConst_gen ctx k p h]; simp [Mon.denote]
    · induction p with
      | num c =>
        simp only [Poly.mulMon.go, Bool.cond_eq_ite]
        split
        · next hc => simp at hc; subst hc; simp [Poly.denoteS]
        · simp only [Poly.denoteS, denoteSInt_eq]
          rw [show (k * c).toNat = _ from h, Semiring.natCast_mul]
          simp [CommSemiring.mul_comm, CommSemiring.mul_left_comm, mul_assoc]
      | add c m' p ih =>
        simp only [Poly.mulMon.go, Poly.denoteS, denoteSInt_eq]
        rw [h.1, ih h.2]
        simp [Mon.denote_mul, Semiring.natCast_mul, left_distrib, mul_assoc]
        congr 2
        rw [← mul_assoc, CommSemiring.mul_comm (c.toNat : α), mul_assoc]

theorem denoteS_nonpos {α} [Semiring α] (ctx : Context α) : ∀ {p : Poly}, CoeffsAll (· ≤ 0) p → p.denoteS ctx = 0
  | .num c, h => by simp [Poly.denoteS, Int.toNat_of_nonpos (show c ≤ 0 from h)]
  | .add c m p, h => by
    simp [Poly.denoteS, Int.toNat_of_nonpos (show c ≤ 0 from h.1), denoteS_nonpos ctx h.2]

theorem addConst_nonpos {k : Int} (hk : k ≤ 0) {p : Poly} (h : CoeffsAll (· ≤ 0) p) :
    CoeffsAll (· ≤ 0) (p.addConst k) := by
  simp only [Poly.addConst, Bool.cond_eq_ite]
  split
  · exact h
  · induction p with
    | num c => show c + k ≤ 0; have : c ≤ 0 := h; omega
    | add c m p ih => exact ⟨h.1, ih h.2⟩

theorem insert_nonpos {k : Int} (hk : k ≤ 0) (m : Mon) {p : Poly} (h : CoeffsAll (· ≤ 0) p) :
    CoeffsAll (· ≤ 0) (p.insert k m) := by
  simp only [Poly.insert, Bool.cond_eq_ite]
  split
  · exact h
  · split
    · exact addConst_nonpos hk h
    · induction p with
      | num c => exact ⟨hk, h⟩
      | add c m' p ih =>
        simp only [Poly.insert.go]
        split
        · simp only [Bool.cond_eq_ite]; split
          · exact h.2
          · exact ⟨by have : c ≤ 0 := h.1; omega, h.2⟩
        · exact ⟨hk, h⟩
        · exact ⟨h.1, ih h.2⟩

theorem mulMon_nc_go_nonpos {k : Int} (hk : k ≤ 0) (m : Mon) :
    ∀ {p acc : Poly}, CoeffsAll (0 ≤ ·) p → CoeffsAll (· ≤ 0) acc →
      CoeffsAll (· ≤ 0) (Poly.mulMon_nc.go k m p acc)
  | .num c, acc, hp, hacc => insert_nonpos (Int.mul_nonpos_of_nonpos_of_nonneg hk hp) _ hacc
  | .add c m' p, acc, hp, hacc =>
    mulMon_nc_go_nonpos hk m (p := p) hp.2 (insert_nonpos (Int.mul_nonpos_of_nonpos_of_nonneg hk hp.1) _ hacc)


/-! ## Removable: multiplicative sign lemmas (one sign condition suffices) -/

-- `Lean.Grind.CommRing.Poly.denoteS_mulConst`: without `k ≥ 0`. Each coefficient `c` of `p` is
-- non-negative, so `(k * c).toNat = k.toNat * c.toNat` for every `k`.
theorem denoteS_mulConst_h5 : drop% Lean.Grind.CommRing.Poly.denoteS_mulConst 5 :=
  fun ctx k p hp => denoteS_mulConst_gen ctx k p
    (coeffsAll_mono (fun _ hc => toNat_mul_right hc) (coeffsAll_of_nn hp))

-- `Lean.Grind.CommRing.Poly.denoteS_mulConst`: without the non-negativity of p. `k ≥ 0`, so
-- `(k * c).toNat = k.toNat * c.toNat` for every coefficient `c`; mulConst works coefficientwise.
theorem denoteS_mulConst_h6 : drop% Lean.Grind.CommRing.Poly.denoteS_mulConst 6 :=
  fun ctx k p hk => denoteS_mulConst_gen ctx k p (coeffsAll_true (fun _ => toNat_mul_left hk))

-- `Lean.Grind.CommRing.Poly.denoteS_mulMon`: without `k ≥ 0`. mulMon.go works termwise and each
-- coefficient `c` of `p` is non-negative, so `(k * c).toNat = k.toNat * c.toNat` for every `k`.
theorem denoteS_mulMon_h6 : drop% Lean.Grind.CommRing.Poly.denoteS_mulMon 6 :=
  fun ctx k m p hp => denoteS_mulMon_gen ctx k m p
    (coeffsAll_mono (fun _ hc => toNat_mul_right hc) (coeffsAll_of_nn hp))

-- `Lean.Grind.CommRing.Poly.denoteS_mulMon`: without the non-negativity of p. mulMon.go works termwise
-- (no merging, so no cancellation) and `k ≥ 0` gives `(k * c).toNat = k.toNat * c.toNat` for every `c`.
theorem denoteS_mulMon_h7 : drop% Lean.Grind.CommRing.Poly.denoteS_mulMon 7 :=
  fun ctx k m p hk => denoteS_mulMon_gen ctx k m p (coeffsAll_true (fun _ => toNat_mul_left hk))

-- `Lean.Grind.CommRing.Poly.denoteS_mulMon_nc`: without `k ≥ 0`. For `k < 0` all products
-- `k * c` are `≤ 0`, insert keeps an accumulator with non-positive coefficients so, and such a
-- polynomial denotes `0 = k.toNat * …`.
theorem denoteS_mulMon_nc_h6 : drop% Lean.Grind.CommRing.Poly.denoteS_mulMon_nc 6 := by
  intro α _ ctx k m p hp
  by_cases hk : k ≥ 0
  · exact Poly.denoteS_mulMon_nc ctx k m p hk hp
  · have hk0 : k.toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hk0]; simp only [natCast_zero, zero_mul]
    simp only [Poly.mulMon_nc, Bool.cond_eq_ite]
    have h0 : (k == 0) = false := by simp; omega
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    split
    · rw [denoteS_mulConst_gen ctx k p
        (coeffsAll_mono (fun _ hc => toNat_mul_right hc) (coeffsAll_of_nn hp)), hk0]
      simp
    · exact denoteS_nonpos ctx (mulMon_nc_go_nonpos (by omega) m (coeffsAll_of_nn hp) (show (0 : Int) ≤ 0 by decide))

end AdapterHand
