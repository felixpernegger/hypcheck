import Lean.Elab.Command
import Mathlib
-- hypkit toolkit header: drop%/indep%/drop0%/indep0% state T' and ∀ indep, Hᵢ straight from the library.
-- Agents copy this file unchanged as the start of their output file (scripts/verify.sh checks it).
-- No `xs[i]!` here: libraries may declare a `]!` token (Foundation does), which breaks that syntax.


set_option linter.unusedVariables false

open Lean Meta Elab Term

/-- `_private.M.«0».x` ↦ `_private.M.0.x`: all-digit string components become numeric. -/
def hcFixName : Name → Name
  | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (hcFixName p) s.toNat! else .str (hcFixName p) s
  | .num p k => .num (hcFixName p) k
  | .anonymous => .anonymous

/-- The constant named by `T`: a public name (resolved as usual) or a private one written in full
as `_private.Mod.«0».x` (private names are not reachable by their short name from another module). -/
def hcConst (T : Ident) : TermElabM Name := do
  let n := hcFixName T.getId
  if isPrivateName n then
    unless (← getEnv).contains n do throwError "unknown private constant {n}"
    return n
  realizeGlobalConstNoOverloadWithInfo T

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

namespace T1c0
/-- dropL% T i [l₁, …]: drop% T i with the universe parameters of T set to the given numerals (copied from W1c6). -/
elab "dropL% " T:ident i:num "[" ls:num,* "]" : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := (ls.getElems.toList.map fun l => Level.ofNat l.getNat)
  unless us.length == ci.levelParams.length do throwError "need {ci.levelParams} levels"
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body


/-- ℚ(√2). -/
abbrev Q2 := QuadraticAlgebra ℚ 2 0

theorem not_sq_two : ¬ IsSquare (2 : ℚ) := by
  rintro ⟨r, hr⟩
  apply irrational_sqrt_two.ne_rat |r|
  have : ((2 : ℚ) : ℝ) = (r : ℝ) * r := by exact_mod_cast hr
  rw [show (2 : ℝ) = ((2 : ℚ) : ℝ) by norm_num, this, Real.sqrt_mul_self_eq_abs]
  push_cast; rfl

instance : Fact (¬ IsSquare (2 : ℚ)) := ⟨not_sq_two⟩

theorem sq2 : √2 * √2 = (2 : ℚ) • (1 : ℝ) + (0 : ℚ) • √2 := by
  simp
theorem sq2' : -√2 * -√2 = (2 : ℚ) • (1 : ℝ) + (0 : ℚ) • -√2 := by
  simp

/-- ω ↦ √2 (order-defining embedding). -/
noncomputable def ιp : Q2 →ₐ[ℚ] ℝ := QuadraticAlgebra.lift ⟨√2, sq2⟩
/-- ω ↦ -√2 (conjugate embedding, used for the module structure). -/
noncomputable def ιm : Q2 →ₐ[ℚ] ℝ := QuadraticAlgebra.lift ⟨-√2, sq2'⟩

theorem ιp_inj : Function.Injective ιp := (ιp : Q2 →+* ℝ).injective

@[instance_reducible] noncomputable def lo : LinearOrder Q2 := LinearOrder.lift' ιp ιp_inj

theorem sor : @IsStrictOrderedRing Q2 _ lo.toPartialOrder :=
  @Function.Injective.isStrictOrderedRing ℝ Q2 _ _ _ _ lo.toPartialOrder ιp (map_zero _) (map_one _)
    (map_add _) (map_mul _) Iff.rfl Iff.rfl

@[instance_reducible] noncomputable def md : Module Q2 ℝ := Module.compHom ℝ (ιm : Q2 →+* ℝ)

/-- a = -ω: negative in the order (ιp a = -√2) but acting on ℝ as multiplication by √2. -/
theorem ιp_negω : ιp (-QuadraticAlgebra.omega) = -√2 := by simp [ιp]
theorem ιm_negω : ιm (-QuadraticAlgebra.omega) = √2 := by simp [ιm]


theorem bI (f : Bool → ℝ) : ⨅ i, f i = min (f true) (f false) :=
  le_antisymm (le_min (ciInf_le (Set.finite_range _).bddBelow true)
    (ciInf_le (Set.finite_range _).bddBelow false)) (le_ciInf fun i => by cases i <;> simp)
theorem bS (f : Bool → ℝ) : ⨆ i, f i = max (f true) (f false) :=
  le_antisymm (ciSup_le fun i => by cases i <;> simp)
    (max_le (le_ciSup (Set.finite_range _).bddAbove true) (le_ciSup (Set.finite_range _).bddAbove false))

/-- The witness `a = -ω`. -/
noncomputable abbrev aw : Q2 := -QuadraticAlgebra.omega

theorem aw_nonpos : @LE.le Q2 lo.toLE aw 0 := by
  show ιp aw ≤ ιp 0
  rw [ιp_negω, map_zero]; simp

theorem aw_smul (x : ℝ) : @HSMul.hSMul Q2 ℝ ℝ (@instHSMul Q2 ℝ md.toSMul) aw x = √2 * x := by
  show ιm aw • x = _
  rw [ιm_negω, smul_eq_mul]

theorem s2pos : (0 : ℝ) < √2 := by positivity

end T1c0

namespace T1c0

-- `Real.sInf_smul_of_nonpos` idx 5: necessary (α = ℚ(√2) ordered via ω ↦ √2, acting on ℝ via ω ↦ -√2; a = -ω, s = {0, 1})
theorem t1_1 : ¬ drop0% Real.sInf_smul_of_nonpos 5 := by
  intro h
  letI := lo; letI := md
  have := @h Q2 _ lo sor md aw aw_nonpos {0, 1}
  rw [Set.smul_set_insert, Set.smul_set_singleton, aw_smul, aw_smul, csInf_pair, csSup_pair,
    aw_smul] at this
  simp at this
  linarith [s2pos]

-- `Real.sSup_smul_of_nonpos` idx 5: necessary (same model; s = {-1, 0})
theorem t1_2 : ¬ drop0% Real.sSup_smul_of_nonpos 5 := by
  intro h
  letI := lo; letI := md
  have := @h Q2 _ lo sor md aw aw_nonpos {-1, 0}
  rw [Set.smul_set_insert, Set.smul_set_singleton, aw_smul, aw_smul, csSup_pair, csInf_pair,
    aw_smul] at this
  simp at this

-- `Real.smul_iSup_of_nonpos` idx 6: necessary (same model; ι = Bool, f = (1, 0))
theorem t1_3 : ¬ dropL% Real.smul_iSup_of_nonpos 6 [1, 0] := by
  intro h
  have := @h Bool Q2 _ lo sor md aw aw_nonpos (fun b => if b then 1 else 0)
  rw [bS, bI] at this
  simp only [aw_smul, ite_true, Bool.false_eq_true, ite_false] at this
  simp at this

-- `Real.smul_iInf_of_nonpos` idx 6: necessary (same model; ι = Bool, f = (-1, 0))
theorem t1_4 : ¬ dropL% Real.smul_iInf_of_nonpos 6 [1, 0] := by
  intro h
  have := @h Bool Q2 _ lo sor md aw aw_nonpos (fun b => if b then -1 else 0)
  rw [bS, bI] at this
  simp only [aw_smul, ite_true, Bool.false_eq_true, ite_false] at this
  simp at this

end T1c0
