import Lean

/-!
Hand pass `GrindMisc` (hand13): 114 unresolved hypotheses of `Init.Omega.Constraint`,
`Init.Omega.{LinearCombo,Int,IntList}`, `Init.Grind.Module.{OfNatModule,NatModuleNorm,Envelope,Basic}`,
`Init.Grind.{Lemmas,FieldNormNum,Injective,Util,Norm}` and `Init.GrindInstances.Ring.Fin`.
For hypothesis `hᵢ` of `T` each declaration proves `¬T'` (`drop0% T i` / `drop1% T i`, universes set
to `0` resp. `1`), `T'` (`drop% T i`, universes kept), `¬ ∀ indep, Hᵢ` (`indep0%`/`indep1%`/`indep%`)
or `∀ indep, Hᵢ` (`indep%`, a removable dependent hypothesis).

98 necessary, 15 removable, 1 independent, 0 left unresolved.

Reusable models (namespace `GrindMiscHand`):
* Omega: concrete constraints (`exact 0`, `exact 1`, `trivial`) and coefficient lists, all certificates
  evaluate with `decide +kernel`; `div_zero_sat`: dividing a constraint by `0` gives bounds `0`.
* `getElemFalse` (no index valid), `getElemBool` (`Bool` collection, validity = `c = true`).
* `F2`: `Fin 2` as a field (`0⁻¹ = 0`, characteristic 2), copied from `KronBHand.F2`.
* `BS`: the Boolean semiring (copied from `AdapterHand.BS`), a `NatModule` without `AddRightCancel`
  (`BS.toQ_eq : toQ false = toQ true` in the envelope `Q BS`); `nat_toQ_ne : toQ 0 ≠ toQ 1` in `Q Nat`.
* `NL` / `NA`: `Nat` with its semiring and order but `<` always false / always true (not
  `LawfulOrderLT`); `toQ_lt_01`: `toQ 0 < toQ 1` from the order on `Q` (defined by `≤`).
* `fin2RightCancel`: `AddRightCancel (Fin 2)`; `Fin 2` refutes `NoNatZeroDivisors` (`2 • 1 = 2 • 0`).
* Linarith polynomials `pPos = [1·x₀]`, `pNeg = [-1·x₀]` over `Nat` with `ctx = leaf 1`: `denoteN`
  stops at the first negative coefficient, and `insert`/`combine` cancel `x₀ - x₀`.

Removable (15):
* `k ≠ 0` of `Constraint.div_sat` and `gcd x ≠ 0` of `Constraint.div_sat'`: dividing by `0` makes every
  bound `0` and the value `t / 0 = 0`, so the conclusion holds outright.
* `IsCharP α 0` of `ofRat_npow`, `ofRat_zpow`, `npow_eq`, `zpow_eq`: `(a ^ n).num = a.num ^ n`,
  `(a ^ n).den = a.den ^ n` and `(x ^ n)⁻¹ = x⁻¹ ^ n` hold in every field (unlike `ofRat_add`/`ofRat_mul`).
* `AddRightCancel α` of the instance `NoNatZeroDivisors (Q α)`: multiply the witness `k'` along
  instead of cancelling it (`nsmul_shift`).
* `p₂.NonnegCoeffs` of `Poly.denoteN_append` (`denoteN` of `p₁ ++ p₂` is computed along `p₁`) and
  `p.NonnegCoeffs` of `Poly.denoteN_mul'`, `Poly.denoteN_mul` (multiplying by `k > 0` keeps signs,
  by `k = 0` zeroes all coefficients).
* Dependent, derivable: `Nonempty α` of `leftInv_eq` (from `a : α`) and `NeZero n` of the four
  `Lean.Grind.Fin` ring lemmas (from `a : Fin n`).

Independent (1): `p = q` of `nestedDecidable_congr`; `nestedDecidable_congr_h2_iff` shows the
statement without it is equivalent to `Decidable True = Decidable False` (type-identity).

Run with the lean4 repo's stage1 binary: `runs/hand13/lean.sh checks/GrindMiscHand.lean`.
Scratch sections in `runs/hand13/scratch_GrindMisc/`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open Lean Meta Elab Term in
/-- `T` with its non-dependent Prop binder `i` dropped; universes kept (`lvl = none`) or all set to `lvl`. -/
def dropStmt (T : Ident) (i : Nat) (lvl : Option Level) : TermElabM Expr := do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← match lvl with
    | none => ci.levelParams.mapM fun _ => mkFreshLevelMVar
    | some l => pure (ci.levelParams.map fun _ => l)
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i]!
    unless ← isProp (← inferType x) do throwError "binder {i} of {n} is not a Prop"
    for j in [i+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i) body

open Lean Meta Elab Term in
/-- `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T`; universes kept or all set to `lvl`. -/
def indepStmt (T : Ident) (i : Nat) (lvl : Option Level) : TermElabM Expr := do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← match lvl with
    | none => ci.levelParams.mapM fun _ => mkFreshLevelMVar
    | some l => pure (ci.levelParams.map fun _ => l)
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i]!
    unless ← isProp (← inferType x) do throwError "binder {i} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => dropStmt T i.getNat none
/-- `drop0% T i`: like `drop% T i`, with all universes set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => dropStmt T i.getNat (some .zero)
/-- `drop1% T i`: like `drop% T i`, with all universes set to `1` (for refutations). -/
elab "drop1% " T:ident i:num : term => dropStmt T i.getNat (some .one)
/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => indepStmt T i.getNat none
/-- `indep0% T i`: like `indep% T i`, with all universes set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => indepStmt T i.getNat (some .zero)
/-- `indep1% T i`: like `indep% T i`, with all universes set to `1` (for refutations). -/
elab "indep1% " T:ident i:num : term => indepStmt T i.getNat (some .one)

namespace GrindMiscHand
open Lean.Omega Lean.Omega.Constraint

-- `Lean.Omega.Constraint.translate_sat`: exact 0 is not satisfied at 1.
theorem translate_sat_h3 : ¬ drop0% Lean.Omega.Constraint.translate_sat 3 := fun h =>
  absurd (@h 0 (exact 0) 1) (by decide +kernel)

-- `Lean.Omega.Constraint.neg_sat`
theorem neg_sat_h2 : ¬ drop0% Lean.Omega.Constraint.neg_sat 2 := fun h =>
  absurd (@h (exact 0) 1) (by decide +kernel)

-- `Lean.Omega.Constraint.not_sat_of_isImpossible`: the trivial constraint is satisfied.
theorem not_sat_of_isImpossible_h1 : ¬ drop0% Lean.Omega.Constraint.not_sat_of_isImpossible 1 := fun h =>
  @h trivial 0 (by decide +kernel)

-- `Lean.Omega.Constraint.scale_sat`
theorem scale_sat_h3 : ¬ drop0% Lean.Omega.Constraint.scale_sat 3 := fun h =>
  absurd (@h 1 (exact 0) 1) (by decide +kernel)

-- `Lean.Omega.Constraint.add_sat`
theorem add_sat_h4 : ¬ drop0% Lean.Omega.Constraint.add_sat 4 := fun h =>
  absurd (@h (exact 0) (exact 0) 1 0 (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.Constraint.add_sat`
theorem add_sat_h5 : ¬ drop0% Lean.Omega.Constraint.add_sat 5 := fun h =>
  absurd (@h (exact 0) (exact 0) 0 1 (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.Constraint.combo_sat`
theorem combo_sat_h5 : ¬ drop0% Lean.Omega.Constraint.combo_sat 5 := fun h =>
  absurd (@h (exact 0) (exact 0) 1 0 1 1 (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.Constraint.combo_sat`
theorem combo_sat_h7 : ¬ drop0% Lean.Omega.Constraint.combo_sat 7 := fun h =>
  absurd (@h (exact 0) (exact 0) 0 1 1 (by decide +kernel) 1) (by decide +kernel)

-- `Lean.Omega.Constraint.div_sat`: t = 1 is not divisible by k = 2; exact 1 becomes [1, 0].
theorem div_sat_h4 : ¬ drop0% Lean.Omega.Constraint.div_sat 4 := fun h =>
  absurd (@h (exact 1) 1 2 (by decide) (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.Constraint.div_sat`
theorem div_sat_h5 : ¬ drop0% Lean.Omega.Constraint.div_sat 5 := fun h =>
  absurd (@h (exact 1) 0 1 (by decide) (by decide)) (by decide +kernel)

/-- Dividing by `0` turns every bound into `0`, and `t / 0 = 0`. -/
theorem div_zero_sat (c : Constraint) (t : Int) : (c.div 0).sat (t / ↑(0 : Nat)) = true := by
  rcases c with ⟨_ | l, _ | u⟩ <;> simp [Constraint.sat, Constraint.div]

-- `Lean.Omega.Constraint.div_sat`: for k = 0 the conclusion holds outright (div_zero_sat).
theorem div_sat_h3 : drop% Lean.Omega.Constraint.div_sat 3 := by
  intro c t k h w
  by_cases hk : k = 0
  · subst hk; exact div_zero_sat c t
  · exact div_sat c t k hk h w

-- `Lean.Omega.Constraint.combine_sat'`
theorem combine_sat'_h4 : ¬ drop0% Lean.Omega.Constraint.combine_sat' 4 := fun h =>
  absurd (@h (exact 1) trivial [] [] (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.Constraint.combine_sat'`
theorem combine_sat'_h5 : ¬ drop0% Lean.Omega.Constraint.combine_sat' 5 := fun h =>
  absurd (@h trivial (exact 1) [] [] (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.Constraint.div_sat'`: for gcd x = 0 the library proof goes through with div_sat_h3.
theorem div_sat'_h3 : drop% Lean.Omega.Constraint.div_sat' 3 := by
  intro c x y w
  dsimp [sat']
  rw [Coeffs.dot_sdiv_left _ _ (Int.dvd_refl _)]
  exact div_sat_h3 c _ (Coeffs.gcd x) (Coeffs.gcd_dvd_dot_left x y) w

-- `Lean.Omega.Constraint.div_sat'`
theorem div_sat'_h4 : ¬ drop0% Lean.Omega.Constraint.div_sat' 4 := fun h =>
  absurd (@h (exact 1) [1] [0] (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.Constraint.not_sat'_of_isImpossible`
theorem not_sat'_of_isImpossible_h1 : ¬ drop0% Lean.Omega.Constraint.not_sat'_of_isImpossible 1 := fun h =>
  @h trivial [] [] (by decide +kernel)

-- `Lean.Omega.normalize?_eq_some`: normalize (trivial, []) keeps the coefficients [].
theorem normalize?_eq_some_h4 : ¬ drop0% Lean.Omega.normalize?_eq_some 4 := fun h =>
  absurd (@h trivial [] trivial [1]).2 (by decide +kernel)

-- `Lean.Omega.normalize_sat`: exact 1 at the empty dot product 0 normalizes to impossible.
theorem normalize_sat_h3 : ¬ drop0% Lean.Omega.normalize_sat 3 := fun h =>
  absurd (@h (exact 1) [] []) (by decide +kernel)

-- `Lean.Omega.positivize?_eq_some`
theorem positivize?_eq_some_h4 : ¬ drop0% Lean.Omega.positivize?_eq_some 4 := fun h =>
  absurd (@h trivial [] trivial [1]).2 (by decide +kernel)

-- `Lean.Omega.positivize_sat`
theorem positivize_sat_h3 : ¬ drop0% Lean.Omega.positivize_sat 3 := fun h =>
  absurd (@h (exact 1) [] []) (by decide +kernel)

-- `Lean.Omega.tidy_sat`
theorem tidy_sat_h3 : ¬ drop0% Lean.Omega.tidy_sat 3 := fun h =>
  absurd (@h (exact 1) [] []) (by decide +kernel)

-- `Lean.Omega.combo_sat'`
theorem combo_sat'_h7 : ¬ drop0% Lean.Omega.combo_sat' 7 := fun h =>
  absurd (@h (exact 1) (exact 0) 1 [] 1 [] [] (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.combo_sat'`
theorem combo_sat'_h8 : ¬ drop0% Lean.Omega.combo_sat' 8 := fun h =>
  absurd (@h (exact 0) (exact 1) 1 [] 1 [] [] (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.bmod_sat`: m = 2, x = [-3], i = 0, v = [-1]: the new coefficient overwrites
-- x[0], so the result is -2 ≠ bmod 3 2 = -1.
theorem bmod_sat_h5 : ¬ drop0% Lean.Omega.bmod_sat 5 := fun h =>
  absurd (@h 2 3 0 [-3] [-1] (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Omega.Prod.of_lex`: empty relations, p = q.
theorem of_lex_h6 : ¬ drop0% Lean.Omega.Prod.of_lex 6 := fun h =>
  absurd (@h Unit (fun _ _ => False) Unit (fun _ _ => False) ((), ()) ((), ())) (by simp)

-- `Lean.Omega.Prod.of_not_lex`: full relations.
theorem of_not_lex_h7 : ¬ drop0% Lean.Omega.Prod.of_not_lex 7 := fun h =>
  (@h Unit (fun _ _ => True) _ Unit (fun _ _ => True) ((), ()) ((), ())).1 trivial

-- `Lean.Omega.IntList.get_map`: f = 1, xs = [].
theorem get_map_h3 : ¬ drop0% Lean.Omega.IntList.get_map 3 := fun h =>
  absurd (@h (fun _ => 1) 0 []) (by decide +kernel)

-- `Lean.Omega.LinearCombo.ext`
theorem LinearCombo_ext_h2 : ¬ drop0% Lean.Omega.LinearCombo.ext 2 := fun h =>
  absurd (congrArg LinearCombo.const (@h ⟨0, []⟩ ⟨1, []⟩ rfl)) (by decide)

-- `Lean.Omega.LinearCombo.ext`
theorem LinearCombo_ext_h3 : ¬ drop0% Lean.Omega.LinearCombo.ext 3 := fun h =>
  absurd (congrArg LinearCombo.coeffs (@h ⟨0, []⟩ ⟨0, [1]⟩ rfl)) (by decide)

-- `Lean.Omega.LinearCombo.mul_eval_of_const_left`: x₀ * x₀ at x₀ = 1.
theorem mul_eval_of_const_left_h3 : ¬ drop0% Lean.Omega.LinearCombo.mul_eval_of_const_left 3 := fun h =>
  absurd (@h ⟨0, [1]⟩ ⟨0, [1]⟩ [1]) (by decide +kernel)

-- `Lean.Omega.LinearCombo.mul_eval_of_const_right`
theorem mul_eval_of_const_right_h3 : ¬ drop0% Lean.Omega.LinearCombo.mul_eval_of_const_right 3 := fun h =>
  absurd (@h ⟨0, [1]⟩ ⟨0, [1]⟩ [1]) (by decide +kernel)

-- `Lean.Omega.LinearCombo.mul_eval`
theorem mul_eval_h3 : ¬ drop0% Lean.Omega.LinearCombo.mul_eval 3 := fun h =>
  absurd (@h ⟨0, [1]⟩ ⟨0, [1]⟩ [1]) (by decide +kernel)

end GrindMiscHand

namespace GrindMiscHand

-- `Lean.Grind.beq_eq_true_of_eq`: Bool, a = true, b = false.
theorem beq_eq_true_of_eq_h5 : ¬ drop0% Lean.Grind.beq_eq_true_of_eq 5 := fun h =>
  absurd (@h Bool inferInstance inferInstance true false) (by decide)

-- `Lean.Grind.beq_eq_false_of_diseq`
theorem beq_eq_false_of_diseq_h5 : ¬ drop0% Lean.Grind.beq_eq_false_of_diseq 5 := fun h =>
  absurd (@h Bool inferInstance inferInstance true true) (by decide)

-- `Lean.Grind.eq_of_beq_eq_true`
theorem eq_of_beq_eq_true_h5 : ¬ drop0% Lean.Grind.eq_of_beq_eq_true 5 := fun h =>
  absurd (@h Bool inferInstance inferInstance true false) (by decide)

-- `Lean.Grind.ne_of_beq_eq_false`
theorem ne_of_beq_eq_false_h5 : ¬ drop0% Lean.Grind.ne_of_beq_eq_false 5 := fun h =>
  absurd (@h Bool inferInstance inferInstance true true) (by simp)

-- `Lean.Grind.forall_propagator`: p = False.
theorem forall_propagator_h3 : ¬ indep0% Lean.Grind.forall_propagator 3 := fun h =>
  absurd (h False (fun _ => True) True) (by simp)

-- `Lean.Grind.forall_propagator`: p = True, q = True, q' = False.
theorem forall_propagator_h4 : ¬ drop0% Lean.Grind.forall_propagator 4 := fun h =>
  absurd (h True (fun _ => True) False (by simp)) (by simp)

-- `Lean.Grind.dite_cond_eq_true'`: c = False.
theorem dite_cond_eq_true'_h6 : ¬ indep0% Lean.Grind.dite_cond_eq_true' 6 := fun h =>
  absurd (@h True False inferInstance (fun _ => trivial) (fun _ => trivial) trivial) (by simp)

-- `Lean.Grind.dite_cond_eq_true'`: α = Bool, a = true, r = false.
theorem dite_cond_eq_true'_h7 : ¬ drop1% Lean.Grind.dite_cond_eq_true' 7 := fun h =>
  absurd (@h Bool True inferInstance (fun _ => true) (fun _ => true) false (by simp)) (by simp)

-- `Lean.Grind.dite_cond_eq_false'`: c = True.
theorem dite_cond_eq_false'_h6 : ¬ indep0% Lean.Grind.dite_cond_eq_false' 6 := fun h =>
  absurd (@h True True inferInstance (fun _ => trivial) (fun _ => trivial) trivial) (by simp)

-- `Lean.Grind.dite_cond_eq_false'`: α = Bool, b = true, r = false.
theorem dite_cond_eq_false'_h7 : ¬ drop1% Lean.Grind.dite_cond_eq_false' 7 := fun h =>
  absurd (@h Bool False inferInstance (fun _ => true) (fun _ => true) false (by simp)) (by simp)

-- `Lean.Grind.eqRec_heq`: a = true, b = false in Bool.
theorem eqRec_heq_h5 : ¬ indep1% Lean.Grind.eqRec_heq 5 := fun h =>
  absurd (@h Bool true (fun _ _ => PUnit) PUnit.unit false) (by decide)

-- `Lean.Grind.eqRecOn_heq`
theorem eqRecOn_heq_h4 : ¬ indep1% Lean.Grind.eqRecOn_heq 4 := fun h =>
  absurd (@h Bool true (fun _ _ => PUnit) false PUnit.unit) (by decide)

-- `Lean.Grind.eqNDRec_heq`
theorem eqNDRec_heq_h5 : ¬ indep1% Lean.Grind.eqNDRec_heq 5 := fun h =>
  absurd (@h Bool true (fun _ => PUnit) PUnit.unit false) (by decide)

-- `Lean.Grind.of_decide_eq_false`: p = True.
theorem of_decide_eq_false_h2 : ¬ drop0% Lean.Grind.of_decide_eq_false 2 := fun h =>
  absurd (@h True inferInstance) (by simp)

-- `Lean.Grind.decide_eq_true`: p = False.
theorem decide_eq_true_h2 : ¬ drop0% Lean.Grind.decide_eq_true 2 := fun h =>
  absurd (@h False inferInstance) (by decide)

-- `Lean.Grind.decide_eq_false`: p = True.
theorem decide_eq_false_h2 : ¬ drop0% Lean.Grind.decide_eq_false 2 := fun h =>
  absurd (@h True inferInstance) (by decide)

/-- A collection type whose indices are never valid. -/
instance getElemFalse : GetElem Unit Unit Unit (fun _ _ => False) := ⟨fun _ _ h => h.elim⟩

/-- `Bool` as a collection of `Bool`s: index `i` is valid in `c` iff `c = true`; every entry is `true`. -/
instance getElemBool : GetElem Bool Bool Bool (fun c _ => c = true) := ⟨fun _ _ _ => true⟩

-- `Lean.Grind.getElem_congr`: no index is valid.
theorem getElem_congr_h9 : ¬ indep0% Lean.Grind.getElem_congr 9 := fun h =>
  @h Unit Unit Unit (fun _ _ => False) getElemFalse () () () () () rfl rfl (fun w => w.elim)

-- `Lean.Grind.getElem_congr`: as = true, bs = false (no index valid in bs), a = false.
theorem getElem_congr_h11 : ¬ drop0% Lean.Grind.getElem_congr 11 := fun h =>
  absurd (@h Bool Bool Bool (fun c _ => c = true) getElemBool true false true true rfl false rfl
    (fun w => absurd w (by decide))) (by decide)

-- `Lean.Grind.getElem_congr`: validity depends on the index: i = true is valid, j = false is not
-- (so h₃ is vacuous); every entry is true, a = false.
theorem getElem_congr_h12 : ¬ drop0% Lean.Grind.getElem_congr 12 := fun h =>
  absurd (@h Bool Bool Bool (fun _ i => i = true) ⟨fun _ _ _ => true⟩ true true true false rfl false rfl
    (fun w => absurd w (by decide))) (by decide)

-- `Lean.Grind.getElem_congr`: every entry is true, a = false.
theorem getElem_congr_h13 : ¬ drop0% Lean.Grind.getElem_congr 13 := fun h =>
  absurd (@h Bool Bool Bool (fun c _ => c = true) getElemBool true true true true rfl false rfl rfl)
    (by decide)

-- `Lean.Grind.exists_const`: α = False, b = True.
theorem exists_const_h1 : ¬ drop0% Lean.Grind.exists_const 1 := fun h =>
  absurd (@h False True) (by simp)

-- `Lean.Grind.leftInv_eq`: Bool → Unit is not injective.
theorem leftInv_eq_h3 : ¬ indep1% Lean.Grind.leftInv_eq 3 := fun h =>
  absurd (@h Bool Unit (fun _ => ()) ⟨true⟩ true (a₁ := true) (a₂ := false) rfl) (by decide)

-- `Lean.Grind.leftInv_eq`: removable (derivable), the point a : α makes α nonempty.
theorem leftInv_eq_h4 : indep% Lean.Grind.leftInv_eq 4 := by
  intro _ _ _ _ a; exact ⟨a⟩

-- `Lean.Grind.Fin.add_zero`: removable (derivable), an element a : Fin n forces n ≠ 0.
theorem Fin_add_zero_h1 : indep% Lean.Grind.Fin.add_zero 1 := by
  intro _ a; exact ⟨Nat.ne_zero_of_lt a.isLt⟩

-- `Lean.Grind.Fin.neg_add_cancel`: removable (derivable), as for Lean.Grind.Fin.add_zero.
theorem Fin_neg_add_cancel_h1 : indep% Lean.Grind.Fin.neg_add_cancel 1 := by
  intro _ a; exact ⟨Nat.ne_zero_of_lt a.isLt⟩

-- `Lean.Grind.Fin.zero_mul`: removable (derivable), as for Lean.Grind.Fin.add_zero.
theorem Fin_zero_mul_h1 : indep% Lean.Grind.Fin.zero_mul 1 := by
  intro _ a; exact ⟨Nat.ne_zero_of_lt a.isLt⟩

-- `Lean.Grind.Fin.mul_one`: removable (derivable), as for Lean.Grind.Fin.add_zero.
theorem Fin_mul_one_h1 : indep% Lean.Grind.Fin.mul_one 1 := by
  intro _ a; exact ⟨Nat.ne_zero_of_lt a.isLt⟩

end GrindMiscHand

namespace GrindMiscHand

/-- `Fin 2` as a field (`0⁻¹ = 0`, characteristic 2); copied from `KronBHand.F2`. -/
instance F2 : Lean.Grind.Field (Fin 2) := { (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) }

-- `Lean.Grind.Field.NormNum.ofRat_add'`: in Fin 2, ofRat (1/2) = 1 * 2⁻¹ = 0, so
-- ofRat (1/2 + 1) = ofRat (3/2) = 0 but ofRat (1/2) + ofRat 1 = 1.
theorem ofRat_add'_h4 : ¬ drop0% Lean.Grind.Field.NormNum.ofRat_add' 4 := fun h =>
  absurd (@h (Fin 2) F2 (1/2) 1 (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.NormNum.ofRat_add'`: a = 1, b = 1/2 in Fin 2.
theorem ofRat_add'_h5 : ¬ drop0% Lean.Grind.Field.NormNum.ofRat_add' 5 := fun h =>
  absurd (@h (Fin 2) F2 1 (1/2) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.NormNum.ofRat_mul'`: a = 1/2, b = 2 in Fin 2: ofRat 1 = 1 ≠ 0 * 0.
theorem ofRat_mul'_h4 : ¬ drop0% Lean.Grind.Field.NormNum.ofRat_mul' 4 := fun h =>
  absurd (@h (Fin 2) F2 (1/2) 2 (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.NormNum.ofRat_mul'`: a = 2, b = 1/2 in Fin 2.
theorem ofRat_mul'_h5 : ¬ drop0% Lean.Grind.Field.NormNum.ofRat_mul' 5 := fun h =>
  absurd (@h (Fin 2) F2 2 (1/2) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.NormNum.ofRat_npow`: removable; (a ^ n).num = a.num ^ n, (a ^ n).den = a.den ^ n
-- and (x ^ n)⁻¹ = x⁻¹ ^ n hold in every field.
theorem ofRat_npow_h2 : drop% Lean.Grind.Field.NormNum.ofRat_npow 2 := by
  intro α _ a n
  simp only [Lean.Grind.Field.NormNum.ofRat, Rat.num_pow, Rat.den_pow, Lean.Grind.Ring.intCast_pow,
    Lean.Grind.Semiring.natCast_pow, Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Field.inv_pow,
    Lean.Grind.CommSemiring.mul_pow]

-- `Lean.Grind.Field.NormNum.ofRat_zpow`: removable; the library proof with ofRat_npow_h2
-- (ofRat_inv needs no characteristic).
theorem ofRat_zpow_h2 : drop% Lean.Grind.Field.NormNum.ofRat_zpow 2 := by
  intro α _ a n
  cases n
  next => rw [Int.ofNat_eq_natCast, Rat.zpow_natCast, Lean.Grind.Field.zpow_natCast, ofRat_npow_h2]
  next =>
    rw [Int.negSucc_eq, Rat.zpow_neg, Lean.Grind.Field.zpow_neg, Lean.Grind.Field.NormNum.ofRat_inv]
    congr 1
    have : (1 : Int) = (1 : Nat) := rfl
    rw [this, ← Int.natCast_add, Rat.zpow_natCast, Lean.Grind.Field.zpow_natCast, ofRat_npow_h2]

-- `Lean.Grind.Field.NormNum.npow_eq`: removable; the library proof with ofRat_npow_h2.
theorem npow_eq_h2 : drop% Lean.Grind.Field.NormNum.npow_eq 2 := by
  intro α _ a n v₁ v; simp; intros; subst v a; rw [ofRat_npow_h2]

-- `Lean.Grind.Field.NormNum.zpow_eq`: removable; the library proof with ofRat_zpow_h2.
theorem zpow_eq_h2 : drop% Lean.Grind.Field.NormNum.zpow_eq 2 := by
  intro α _ a n v₁ v; simp; intros; subst v a; rw [ofRat_zpow_h2]

end GrindMiscHand

namespace GrindMiscHand
open Lean.Grind Lean.Grind.IntModule.OfNatModule

/-- The Boolean semiring on a copy of `Bool` (copied from `AdapterHand.BS`): `+` is `||`, so it
is a `NatModule` without `AddRightCancel` (`true + true = false + true`). -/
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

/-- In `BS`, `false` and `true` have the same image in the envelope `Q BS`. -/
theorem BS.toQ_eq : toQ (α := BS) false = toQ (α := BS) true := Quot.sound ⟨true, rfl⟩

/-- `toQ` separates `0` and `1` in `Nat`. -/
theorem nat_toQ_ne : toQ (α := Nat) 0 ≠ toQ 1 := fun h => by
  obtain ⟨k, hk⟩ := Q.exact h
  change 0 + 0 + k = 0 + 1 + k at hk; omega

/-- `Nat` with its semiring and order, but `<` is always false (copied from `PackedHand.NL`). -/
def NL := Nat
instance : Semiring NL := inferInstanceAs (Semiring Nat)
instance : LE NL := inferInstanceAs (LE Nat)
instance : LT NL := ⟨fun _ _ => False⟩
instance : Std.IsPreorder NL := inferInstanceAs (Std.IsPreorder Nat)
instance : OrderedAdd NL := inferInstanceAs (OrderedAdd Nat)

/-- `Nat` with its semiring and order, but `<` is always true. -/
def NA := Nat
instance : Semiring NA := inferInstanceAs (Semiring Nat)
instance : LE NA := inferInstanceAs (LE Nat)
instance : LT NA := ⟨fun _ _ => True⟩
instance : Std.IsPreorder NA := inferInstanceAs (Std.IsPreorder Nat)
instance : OrderedAdd NA := inferInstanceAs (OrderedAdd Nat)

-- `Lean.Grind.AddRightCancel.add_right_cancel`: Nat, a = 0, b = 1.
theorem add_right_cancel_h6 : ¬ drop0% Lean.Grind.AddRightCancel.add_right_cancel 6 := fun h =>
  absurd (@h Nat inferInstance inferInstance 0 1 0) (by decide)

-- `Lean.Grind.AddRightCancel.add_right_cancel_iff`: BS, true + true = false + true.
theorem add_right_cancel_iff_h2 : ¬ drop0% Lean.Grind.AddRightCancel.add_right_cancel_iff 2 := fun h =>
  absurd ((@h BS inferInstance true false true).mp rfl) (by intro e; cases e)

-- `Lean.Grind.NoNatZeroDivisors.no_nat_zero_divisors`: k = 0 in Nat.
theorem no_nat_zero_divisors_h6 : ¬ drop0% Lean.Grind.NoNatZeroDivisors.no_nat_zero_divisors 6 := fun h =>
  absurd (@h Nat inferInstance inferInstance 0 0 1 (by decide)) (by decide)

-- `Lean.Grind.NoNatZeroDivisors.no_nat_zero_divisors`: k = 1 in Nat.
theorem no_nat_zero_divisors_h7 : ¬ drop0% Lean.Grind.NoNatZeroDivisors.no_nat_zero_divisors 7 := fun h =>
  absurd (@h Nat inferInstance inferInstance 1 0 1 (by decide)) (by decide)

-- `Lean.Grind.IntModule.OfNatModule.r_sym`: (0, 0) and (1, 0) in Nat.
theorem r_sym_h4 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.r_sym 4 := fun h => by
  obtain ⟨k, hk⟩ := @h Nat inferInstance (0, 0) (1, 0)
  change 1 + 0 + k = 0 + 0 + k at hk; omega

-- `Lean.Grind.IntModule.OfNatModule.r_trans`
theorem r_trans_h5 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.r_trans 5 := fun h => by
  obtain ⟨k, hk⟩ := @h Nat inferInstance (1, 0) (0, 0) (0, 0) ⟨0, rfl⟩
  change 1 + 0 + k = 0 + 0 + k at hk; omega

-- `Lean.Grind.IntModule.OfNatModule.r_trans`
theorem r_trans_h6 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.r_trans 6 := fun h => by
  obtain ⟨k, hk⟩ := @h Nat inferInstance (0, 0) (0, 0) (1, 0) ⟨0, rfl⟩
  change 0 + 0 + k = 0 + 1 + k at hk; omega

-- `Lean.Grind.IntModule.OfNatModule.Q.ind`: the empty predicate.
theorem Q_ind_h3 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.Q.ind 3 := fun h =>
  @h Nat inferInstance (fun _ => False) (Q.mk (0, 0))

-- `Lean.Grind.IntModule.OfNatModule.Q.exact`
theorem Q_exact_h4 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.Q.exact 4 := fun h => by
  obtain ⟨k, hk⟩ := @h Nat inferInstance (0, 0) (1, 0)
  change 0 + 0 + k = 0 + 1 + k at hk; omega

-- `Lean.Grind.IntModule.OfNatModule.toQ_inj`: BS.toQ_eq.
theorem toQ_inj_h2 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.toQ_inj 2 := fun h =>
  absurd (@h BS inferInstance false true BS.toQ_eq) (by intro e; cases e)

/-- `AddRightCancel (Fin 2)`. -/
instance fin2RightCancel : AddRightCancel (Fin 2) := ⟨by decide⟩

-- `Lean.Grind.IntModule.OfNatModule.instNoNatZeroDivisorsQOfAddRightCancel`: Fin 2 cancels, and
-- 2 • toQ 1 = toQ 0 = 2 • toQ 0 in Q (Fin 2) although toQ 1 ≠ toQ 0.
theorem instNoNatZeroDivisorsQ_h3 :
    ¬ drop0% Lean.Grind.IntModule.OfNatModule.instNoNatZeroDivisorsQOfAddRightCancel 3 := fun h => by
  have := (@h (Fin 2) inferInstance fin2RightCancel).no_nat_zero_divisors 2 (toQ 1) (toQ 0) (by decide)
    (Quot.sound ⟨0, by decide⟩)
  obtain ⟨k, hk⟩ := Q.exact this
  revert k; decide

section
variable {α : Type u} [NatModule α]
local instance : Std.Associative (· + · : α → α → α) := ⟨AddCommMonoid.add_assoc⟩
local instance : Std.Commutative (· + · : α → α → α) := ⟨AddCommMonoid.add_comm⟩

/-- `(m+1) • x + k' = (m+1) • y + k'` implies `(m+1) • (x + k') = (m+1) • (y + k')`
(add `m • k'` on both sides). -/
theorem nsmul_shift (m : Nat) (x y k' : α) (h : (m+1) • x + k' = (m+1) • y + k') :
    (m+1) • (x + k') = (m+1) • (y + k') := by
  have e : ∀ z : α, (m+1) • (z + k') = ((m+1) • z + k') + m • k' := by
    intro z; rw [NatModule.nsmul_add, NatModule.add_nsmul m 1 k', NatModule.one_nsmul]; ac_rfl
  rw [e, e, h]
end

-- `Lean.Grind.IntModule.OfNatModule.instNoNatZeroDivisorsQOfAddRightCancel`: removable. From
-- k • (a₁ + b₂) + k' = k • (a₂ + b₁) + k' add (k - 1) • k' instead of cancelling k':
-- k • (a₁ + b₂ + k') = k • (a₂ + b₁ + k'), so a₁ + b₂ + k' = a₂ + b₁ + k' by NoNatZeroDivisors α.
theorem instNoNatZeroDivisorsQ_h2 :
    drop% Lean.Grind.IntModule.OfNatModule.instNoNatZeroDivisorsQOfAddRightCancel 2 := by
  intro α _ _
  constructor
  intro k a b h₁ h₂
  replace h₂ : k • a = k • b := h₂
  obtain ⟨⟨a₁, a₂⟩⟩ := a
  obtain ⟨⟨b₁, b₂⟩⟩ := b
  obtain ⟨k', h₂⟩ := Q.exact h₂
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [← NatModule.nsmul_add, ← NatModule.nsmul_add] at h₂
  exact Quot.sound ⟨k', NoNatZeroDivisors.no_nat_zero_divisors (m+1) _ _ h₁ (nsmul_shift m _ _ k' h₂)⟩

end GrindMiscHand

namespace GrindMiscHand
open Lean.Grind Lean.Grind.IntModule.OfNatModule

-- `Lean.Grind.IntModule.OfNatModule.of_eq`: a = b = 0, a' = toQ 1, b' = toQ 0 in Nat.
theorem of_eq_h6 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_eq 6 := fun h =>
  nat_toQ_ne (@h Nat _ 0 0 (toQ 1) (toQ 0) rfl rfl).symm

-- `Lean.Grind.IntModule.OfNatModule.of_eq`
theorem of_eq_h7 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_eq 7 := fun h =>
  nat_toQ_ne (@h Nat _ 0 0 (toQ 0) (toQ 1) rfl rfl)

-- `Lean.Grind.IntModule.OfNatModule.of_eq`
theorem of_eq_h8 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_eq 8 := fun h =>
  nat_toQ_ne (@h Nat _ 0 1 (toQ 0) (toQ 1) rfl rfl)

-- `Lean.Grind.IntModule.OfNatModule.of_diseq`: BS.toQ_eq.
theorem of_diseq_h2 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_diseq 2 := fun h =>
  @h BS _ false true (toQ false) (toQ true) rfl rfl (by intro e; cases e) BS.toQ_eq

-- `Lean.Grind.IntModule.OfNatModule.of_diseq`: a = 0, b = 1, a' = b' = toQ 1.
theorem of_diseq_h7 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_diseq 7 := fun h =>
  @h Nat _ _ 0 1 (toQ 1) (toQ 1) rfl (by decide) rfl

-- `Lean.Grind.IntModule.OfNatModule.of_diseq`: a = 0, b = 1, a' = b' = toQ 0.
theorem of_diseq_h8 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_diseq 8 := fun h =>
  @h Nat _ _ 0 1 (toQ 0) (toQ 0) rfl (by decide) rfl

-- `Lean.Grind.IntModule.OfNatModule.of_le`: a = b = 0, a' = toQ 1, b' = toQ 0.
theorem of_le_h9 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_le 9 := fun h => by
  have := @h Nat _ _ _ _ 0 0 (toQ 1) (toQ 0) rfl (Nat.le_refl 0)
  change 1 + 0 ≤ 0 + 0 at this; omega

-- `Lean.Grind.IntModule.OfNatModule.of_le`: a = b = 1, a' = toQ 1, b' = toQ 0.
theorem of_le_h10 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_le 10 := fun h => by
  have := @h Nat _ _ _ _ 1 1 (toQ 1) (toQ 0) rfl (Nat.le_refl 1)
  change 1 + 0 ≤ 0 + 0 at this; omega

-- `Lean.Grind.IntModule.OfNatModule.of_le`: a = 1, b = 0.
theorem of_le_h11 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_le 11 := fun h => by
  have := @h Nat _ _ _ _ 1 0 (toQ 1) (toQ 0) rfl rfl
  change 1 + 0 ≤ 0 + 0 at this; omega

-- `Lean.Grind.IntModule.OfNatModule.of_not_le`: a = 1, b = 0, a' = b' = toQ 0.
theorem of_not_le_h9 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_not_le 9 := fun h =>
  @h Nat _ _ _ _ 1 0 (toQ 0) (toQ 0) rfl (by decide) (show 0 + 0 ≤ 0 + 0 from Nat.le_refl _)

-- `Lean.Grind.IntModule.OfNatModule.of_not_le`: a = 1, b = 0, a' = b' = toQ 1.
theorem of_not_le_h10 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_not_le 10 := fun h =>
  @h Nat _ _ _ _ 1 0 (toQ 1) (toQ 1) rfl (by decide) (show 1 + 0 ≤ 0 + 1 from Nat.le_refl _)

-- `Lean.Grind.IntModule.OfNatModule.of_lt`: NA (< always true), a = 1, b = 0.
theorem of_lt_h4 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_lt 4 := fun h => by
  have := (@h NA _ _ _ _ _ (1 : Nat) (0 : Nat) (toQ (1 : Nat)) (toQ (0 : Nat)) rfl rfl trivial).1
  change (1 : Nat) + 0 ≤ 0 + 0 at this; omega

-- `Lean.Grind.IntModule.OfNatModule.of_lt`: a = 0, b = 1, a' = b' = toQ 1.
theorem of_lt_h11 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_lt 11 := fun h => by
  have := @h Nat _ _ _ _ _ _ 0 1 (toQ 1) (toQ 1) rfl (by decide)
  exact this.2 this.1

-- `Lean.Grind.IntModule.OfNatModule.of_lt`: a = 0, b = 1, a' = b' = toQ 0.
theorem of_lt_h12 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_lt 12 := fun h => by
  have := @h Nat _ _ _ _ _ _ 0 1 (toQ 0) (toQ 0) rfl (by decide)
  exact this.2 this.1

-- `Lean.Grind.IntModule.OfNatModule.of_lt`: a = b = 0.
theorem of_lt_h13 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_lt 13 := fun h => by
  have := @h Nat _ _ _ _ _ _ 0 0 (toQ 0) (toQ 0) rfl rfl
  exact this.2 this.1

/-- `toQ 0 < toQ 1` in `Q Nat` (and in `Q NL`), from the order on `Q` alone. -/
theorem toQ_lt_01 {α : Type} [Semiring α] [LE α] [Std.IsPreorder α] [OrderedAdd α]
    (h01 : (0 : α) + 0 ≤ 0 + 1) (h10 : ¬ (1 : α) + 0 ≤ 0 + 0) : toQ (0 : α) < toQ 1 := ⟨h01, h10⟩

-- `Lean.Grind.IntModule.OfNatModule.of_not_lt`: NL (< always false), a = 0, b = 1.
theorem of_not_lt_h4 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_not_lt 4 := fun h =>
  @h NL _ _ _ _ _ (0 : Nat) (1 : Nat) (toQ (0 : Nat)) (toQ (1 : Nat)) rfl rfl id
    (toQ_lt_01 (α := NL) (show (0 : Nat) + 0 ≤ 0 + 1 by decide) (show ¬ (1 : Nat) + 0 ≤ 0 + 0 by decide))

-- `Lean.Grind.IntModule.OfNatModule.of_not_lt`: a = b = 1, a' = toQ 0, b' = toQ 1.
theorem of_not_lt_h11 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_not_lt 11 := fun h =>
  @h Nat _ _ _ _ _ _ 1 1 (toQ 0) (toQ 1) rfl (by decide)
    (toQ_lt_01 (show (0 : Nat) + 0 ≤ 0 + 1 by decide) (show ¬ (1 : Nat) + 0 ≤ 0 + 0 by decide))

-- `Lean.Grind.IntModule.OfNatModule.of_not_lt`: a = b = 0, a' = toQ 0, b' = toQ 1.
theorem of_not_lt_h12 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_not_lt 12 := fun h =>
  @h Nat _ _ _ _ _ _ 0 0 (toQ 0) (toQ 1) rfl (by decide)
    (toQ_lt_01 (show (0 : Nat) + 0 ≤ 0 + 1 by decide) (show ¬ (1 : Nat) + 0 ≤ 0 + 0 by decide))

-- `Lean.Grind.IntModule.OfNatModule.of_not_lt`: a = 0, b = 1.
theorem of_not_lt_h13 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.of_not_lt 13 := fun h =>
  @h Nat _ _ _ _ _ _ 0 1 (toQ 0) (toQ 1) rfl rfl
    (toQ_lt_01 (show (0 : Nat) + 0 ≤ 0 + 1 by decide) (show ¬ (1 : Nat) + 0 ≤ 0 + 0 by decide))

-- `Lean.Grind.IntModule.OfNatModule.add_congr`: a = b = 0, a' = toQ 1, b' = toQ 0.
theorem add_congr_h6 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.add_congr 6 := fun h =>
  nat_toQ_ne (@h Nat _ 0 0 (toQ 1) (toQ 0) rfl)

-- `Lean.Grind.IntModule.OfNatModule.add_congr`: a = b = 0, a' = toQ 0, b' = toQ 1.
theorem add_congr_h7 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.add_congr 7 := fun h =>
  nat_toQ_ne (@h Nat _ 0 0 (toQ 0) (toQ 1) rfl)

-- `Lean.Grind.IntModule.OfNatModule.smul_congr`: n = 1, a = 0, a' = toQ 1.
theorem smul_congr_h5 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.smul_congr 5 := fun h =>
  nat_toQ_ne (@h Nat _ 1 0 (toQ 1))

-- `Lean.Grind.IntModule.OfNatModule.toQ_lt`: NL (< always false), toQ 0 < toQ 1.
theorem toQ_lt_h4 : ¬ drop0% Lean.Grind.IntModule.OfNatModule.toQ_lt 4 := fun h =>
  (@h NL _ _ _ _ _ (0 : Nat) (1 : Nat)).mp
    (toQ_lt_01 (α := NL) (show (0 : Nat) + 0 ≤ 0 + 1 by decide) (show ¬ (1 : Nat) + 0 ≤ 0 + 0 by decide))

end GrindMiscHand

namespace GrindMiscHand
open Lean.Grind Lean.Grind.Linarith

/-- `[1·x₀]` and `[-1·x₀]`; over `Nat` with `ctx = leaf 1` every variable denotes `1`. -/
abbrev pPos : Poly := .add 1 0 .nil
abbrev pNeg : Poly := .add (-1) 0 .nil
theorem pPos_nn : pPos.NonnegCoeffs := .add 1 0 .nil (by decide) .nil

-- `Lean.Grind.Linarith.Poly.denoteN_insert`: insert (-1) x₀ [1·x₀] = [] denotes 0, the right side 1.
theorem denoteN_insert_h6 : ¬ drop0% Lean.Grind.Linarith.Poly.denoteN_insert 6 := fun h =>
  absurd (@h Nat _ (.leaf 1) (-1) 0 pPos pPos_nn) (by decide +kernel)

-- `Lean.Grind.Linarith.Poly.denoteN_append`: denoteN stops at a negative coefficient, so
-- [-1·x₀] ++ [1·x₀] denotes 0.
theorem denoteN_append_h5 : ¬ drop0% Lean.Grind.Linarith.Poly.denoteN_append 5 := fun h =>
  absurd (@h Nat _ (.leaf 1) pNeg pPos pPos_nn) (by decide +kernel)

-- `Lean.Grind.Linarith.Poly.denoteN_append`: removable; for non-negative p₁ the denotation of
-- p₁ ++ p₂ is computed term by term along p₁, whatever p₂ is.
theorem denoteN_append_h6 : drop% Lean.Grind.Linarith.Poly.denoteN_append 6 := by
  intro α _ ctx p₁ p₂ h₁
  induction h₁ with
  | nil => simp only [Poly.append, Poly.denoteN_nil, AddCommMonoid.zero_add]
  | add a x p ha hp ih =>
    simp only [Poly.append]
    rw [Poly.denoteN_add _ _ _ _ ha, Poly.denoteN_add _ _ _ _ ha, ih, AddCommMonoid.add_assoc]

-- `Lean.Grind.Linarith.Poly.denoteN_combine`: combine [-1·x₀] [1·x₀] = [].
theorem denoteN_combine_h5 : ¬ drop0% Lean.Grind.Linarith.Poly.denoteN_combine 5 := fun h =>
  absurd (@h Nat _ (.leaf 1) pNeg pPos pPos_nn) (by decide +kernel)

-- `Lean.Grind.Linarith.Poly.denoteN_combine`: combine [1·x₀] [-1·x₀] = [].
theorem denoteN_combine_h6 : ¬ drop0% Lean.Grind.Linarith.Poly.denoteN_combine 6 := fun h =>
  absurd (@h Nat _ (.leaf 1) pPos pNeg pPos_nn) (by decide +kernel)

-- `Lean.Grind.Linarith.Poly.denoteN_mul'`: removable; for k > 0 multiplying keeps the signs (and
-- denoteN stops at the same term), for k = 0 all coefficients become 0.
theorem denoteN_mul'_h5 : drop% Lean.Grind.Linarith.Poly.denoteN_mul' 5 := by
  intro α _ ctx p k
  induction p with
  | nil => simp only [Poly.mul', Poly.denoteN_nil, NatModule.nsmul_zero]
  | add c v p ih =>
    simp only [Poly.mul']
    by_cases hc : c < 0
    · by_cases hk : k = 0
      · subst hk
        rw [Poly.denoteN_add _ _ _ _ (by simp), ih]
        simp [NatModule.zero_nsmul, AddCommMonoid.zero_add]
      · have h1 : (k : Int) * c < 0 := Int.mul_neg_of_pos_of_neg (by omega) hc
        simp [Poly.denoteN, h1, hc, NatModule.nsmul_zero]
    · have hc' : c ≥ 0 := by omega
      rw [Poly.denoteN_add _ _ _ _ (Int.mul_nonneg (by omega) hc'), Poly.denoteN_add _ _ _ _ hc', ih,
        Int.toNat_mul, NatModule.mul_nsmul, Int.toNat_natCast, NatModule.nsmul_add]
      all_goals omega

-- `Lean.Grind.Linarith.Poly.denoteN_mul`: removable; the library proof with denoteN_mul'_h5.
theorem denoteN_mul_h5 : drop% Lean.Grind.Linarith.Poly.denoteN_mul 5 := by
  intro α _ ctx p k
  simp only [Poly.mul]
  split
  next h =>
    have : k = 0 := by simpa using h
    subst this; simp [Poly.denoteN_nil, NatModule.zero_nsmul]
  next => exact denoteN_mul'_h5 ctx p k

-- `Lean.Grind.Linarith.Poly.mul'_Nonneg`: p = [-1·x₀], k = 1.
theorem mul'_Nonneg_h2 : ¬ drop0% Lean.Grind.Linarith.Poly.mul'_Nonneg 2 := fun h => by
  have := h pNeg 1; cases this; omega

-- `Lean.Grind.Linarith.Poly.mul_Nonneg`: p = [-1·x₀], k = 1.
theorem mul_Nonneg_h2 : ¬ drop0% Lean.Grind.Linarith.Poly.mul_Nonneg 2 := fun h => by
  have := h pNeg 1; simp [Poly.mul, Poly.mul'] at this; cases this; omega

-- `Lean.Grind.Linarith.Poly.combine_Nonneg`: combine [-1·x₀] [] = [-1·x₀].
theorem combine_Nonneg_h2 : ¬ drop0% Lean.Grind.Linarith.Poly.combine_Nonneg 2 := fun h => by
  have := h pNeg .nil .nil; simp [Poly.combine] at this; cases this; omega

-- `Lean.Grind.Linarith.Poly.combine_Nonneg`: combine [] [-1·x₀] = [-1·x₀].
theorem combine_Nonneg_h3 : ¬ drop0% Lean.Grind.Linarith.Poly.combine_Nonneg 3 := fun h => by
  have := h .nil pNeg .nil; simp [Poly.combine] at this; cases this; omega

end GrindMiscHand

namespace GrindMiscHand

/-- Elements of two equal types, the second a subsingleton, are heterogeneously equal. -/
theorem heq_of_type_eq {A B : Type} (e : A = B) [Subsingleton B] (a : A) (b : B) : a ≍ b := by
  subst e; exact heq_of_eq (Subsingleton.elim a b)

/-- Independence support for `nestedDecidable_congr`, hypothesis 2 (`p = q`): the statement without
it is equivalent to the type equation `Decidable True = Decidable False`, which Lean can neither prove nor refute
(two singleton types). -/
theorem nestedDecidable_congr_h2_iff :
    drop% Lean.Grind.nestedDecidable_congr 2 ↔ (Decidable True = Decidable False) := by
  constructor
  · intro h; exact type_eq_of_heq (h True False (isTrue trivial) (isFalse id))
  · intro e p q hp hq
    unfold Lean.Grind.nestedDecidable
    cases hp with
    | isTrue hp' => cases hq with
      | isTrue hq' => exact heq_of_type_eq (by rw [eq_true hp', eq_true hq']) _ _
      | isFalse hq' => exact heq_of_type_eq (by rw [eq_true hp', eq_false hq']; exact e) _ _
    | isFalse hp' => cases hq with
      | isTrue hq' => exact heq_of_type_eq (by rw [eq_false hp', eq_true hq']; exact e.symm) _ _
      | isFalse hq' => exact heq_of_type_eq (by rw [eq_false hp', eq_false hq']) _ _

end GrindMiscHand
