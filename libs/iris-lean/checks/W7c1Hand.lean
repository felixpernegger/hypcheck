import Lean.Elab.Command
import Iris
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

namespace W7c1
open Iris Iris.ProgramLogic

/-- Toy ectx-item language: expressions Nat, 0 the only value, one context item filling `e ↦ 2e+2`;
base steps 2 → 0 (pure) and 1 → 1. -/
def eTV (e : Nat) : Option Unit := if e = 0 then some () else none

def eBS (c : Nat × Unit) (obs : List Unit) (c' : Nat × Unit × List Nat) : Prop :=
  obs = [] ∧ c'.2.2 = [] ∧ ((c.1 = 2 ∧ c'.1 = 0) ∨ (c.1 = 1 ∧ c'.1 = 1))

instance eL : EctxItemLanguage Nat Unit Unit Unit Unit where
  toVal := eTV
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases he : e = 0 <;> simp_all [eTV]
  toVal_coe := fun _ => rfl
  baseStep := eBS
  fillItem := fun _ e => 2 * e + 2
  fillItem_inj := by intro _ a b h; have : 2 * a + 2 = 2 * b + 2 := h; omega
  fillItem_val := by intro e _ h; simp [eTV] at h
  fillItem_no_val_inj := by intros; rfl
  val_stuck := by
    intro e σ obs e' σ' eₜ h; simp only [eBS] at h
    rcases h with ⟨_, _, ⟨h1, _⟩ | ⟨h1, _⟩⟩ <;> subst h1 <;> rfl
  base_ctx_step_val := by
    intro _ e σ obs e' σ' eₜ h; simp only [eBS] at h
    rcases h with ⟨_, _, ⟨h1, _⟩ | ⟨h1, _⟩⟩
    · have : e = 0 := by omega
      subst this; rfl
    · omega

abbrev EC := List Unit

def P3 (n : Nat) : Prop := n = 1 ∨ n = 2 ∨ (4 ≤ n ∧ n % 2 = 0)

theorem fill_P3 (K : EC) (x : Nat) (h : P3 x) : P3 (fill K x) := by
  induction K generalizing x with
  | nil => exact h
  | cons k K ih =>
    show P3 (fill K (2 * x + 2))
    apply ih; unfold P3 at h ⊢; omega

theorem bs_P3 {e : Nat} {σ obs e' σ' eₜ} (h : BaseStep.baseStep (e, (σ : Unit)) obs (e', (σ' : Unit), eₜ)) : P3 e := by
  change eBS _ _ _ at h; simp only [eBS] at h
  rcases h with ⟨_, _, ⟨h1, _⟩ | ⟨h1, _⟩⟩ <;> simp [P3, h1]

theorem ps_P3 {e : Nat} {σ obs e' σ' eₜ}
    (h : PrimStep.primStep (Expr := Nat) (e, (σ : Unit)) obs (e', (σ' : Unit), eₜ)) : P3 e := by
  rcases h with ⟨bs⟩
  exact fill_P3 _ _ (bs_P3 bs)

theorem no_ps0 {σ obs e' σ' eₜ} : ¬ PrimStep.primStep (Expr := Nat) ((0:Nat), (σ : Unit)) obs (e', (σ' : Unit), eₜ) :=
  fun h => by have := ps_P3 h; simp [P3] at this

theorem no_ps3 {σ obs e' σ' eₜ} : ¬ PrimStep.primStep (Expr := Nat) ((3:Nat), (σ : Unit)) obs (e', (σ' : Unit), eₜ) :=
  fun h => by have := ps_P3 h; simp [P3] at this

theorem bs2 : BaseStep.baseStep ((2:Nat), ()) ([] : List Unit) ((0:Nat), (), ([] : List Nat)) := ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩
theorem bs1 : BaseStep.baseStep ((1:Nat), ()) ([] : List Unit) ((1:Nat), (), ([] : List Nat)) := ⟨rfl, rfl, .inr ⟨rfl, rfl⟩⟩
theorem ps4 : PrimStep.primStep (Expr := Nat) ((4:Nat), ()) ([] : List Unit) ((4:Nat), (), ([] : List Nat)) :=
  BaseStep.ContextStep.ofBaseStep (Ectx := EC) [()] bs1
theorem no_bs {e e' : Nat} {σ obs σ' eₜ} (h : BaseStep.baseStep (e, (σ:Unit)) obs (e', (σ':Unit), eₜ)) :
    (e = 2 ∧ e' = 0) ∨ (e = 1 ∧ e' = 1) := by
  change eBS _ _ _ at h; exact h.2.2

theorem sub2 : EctxLanguage.SubredexesAreValues (Ectx := EC) (2:Nat) :=
  EctxItemLanguage.subredexes_are_values (fun _ e' h => by
    change 2 = 2 * e' + 2 at h; have : e' = 0 := by omega
    subst this; rfl)
theorem sub1 : EctxLanguage.SubredexesAreValues (Ectx := EC) (1:Nat) :=
  EctxItemLanguage.subredexes_are_values (fun _ e' h => by change 1 = 2 * e' + 2 at h; omega)
theorem sub0 : EctxLanguage.SubredexesAreValues (Ectx := EC) (0:Nat) :=
  EctxItemLanguage.subredexes_are_values (fun _ e' h => by change 0 = 2 * e' + 2 at h; omega)

end W7c1

namespace W7c1
open Iris Iris.ProgramLogic

-- `Iris.ProgramLogic.BaseStep.reducible_of_reducibleNoObs` idx 6: necessary (e = 0 has no base step)
theorem w7c1_74 : ¬ drop0% Iris.ProgramLogic.BaseStep.reducible_of_reducibleNoObs 6 := fun h => by
  obtain ⟨_, _, _, _, hs⟩ := @h Nat Unit Unit _ (0:Nat) ()
  rcases no_bs hs with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.fill_val` idx 8: necessary (e = 1 is not a value)
theorem w7c1_75 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.fill_val 8 := fun h => by
  have := @h Nat EC Unit Unit Unit _ [] (1:Nat)
  simp [toVal, eTV] at this

-- `Iris.ProgramLogic.EctxLanguage.step_by_val` idx 15: necessary (K' = [()], K_redex = [], e₁' = 1, redex 2)
theorem w7c1_76 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.step_by_val 15 := fun h => by
  obtain ⟨K'', hK⟩ := @h Nat EC Unit Unit Unit _ [()] [] (1:Nat) (2:Nat) () [] (0:Nat) () [] rfl bs2
  change ([] : List Unit) = K'' ++ [()] at hK; simp at hK

-- `Iris.ProgramLogic.EctxLanguage.step_by_val` idx 16: necessary (fill [()] 0 = 2 = fill [] 2, e₁' = 0 a value)
theorem w7c1_77 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.step_by_val 16 := fun h => by
  obtain ⟨K'', hK⟩ := @h Nat EC Unit Unit Unit _ [()] [] (0:Nat) (2:Nat) () [] (0:Nat) () [] rfl bs2
  change ([] : List Unit) = K'' ++ [()] at hK; simp at hK

-- `Iris.ProgramLogic.EctxLanguage.step_by_val` idx 17: necessary (fill [()] 1 = 4 = fill [] 4, 4 has no base step)
theorem w7c1_78 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.step_by_val 17 := fun h => by
  obtain ⟨K'', hK⟩ := @h Nat EC Unit Unit Unit _ [()] [] (1:Nat) (4:Nat) () [] (0:Nat) () [] rfl rfl
  change ([] : List Unit) = K'' ++ [()] at hK; simp at hK

-- `Iris.ProgramLogic.EctxLanguage.val_stuck` idx 12: necessary (e = 0 is a value)
theorem w7c1_79 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.val_stuck 12 := fun h => by
  have := @h Nat EC Unit Unit Unit _ (0:Nat) () [] (0:Nat) () []
  simp [toVal, eTV] at this

-- `Iris.ProgramLogic.EctxLanguage.base_ctx_step_val` idx 13: necessary (K = [()], e = 1)
theorem w7c1_80 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.base_ctx_step_val 13 := fun h => by
  rcases @h Nat EC Unit Unit Unit _ [()] (1:Nat) () [] (0:Nat) () [] with h1 | h1
  · simp [toVal, eTV] at h1
  · change [()] = ([] : List Unit) at h1; simp at h1

-- `Iris.ProgramLogic.EctxLanguage.fill_not_val` idx 8: necessary (e = 0 a value, K = [])
theorem w7c1_81 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.fill_not_val 8 := fun h => by
  have := @h Nat Unit Unit Unit EC _ [] (0:Nat)
  simp [fill, toVal, eTV] at this

-- `Iris.ProgramLogic.EctxLanguage.base_redex_unique` idx 12: necessary (e = 1, e' = 2 both reducible, K = K' = [])
theorem w7c1_82 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.base_redex_unique 12 := fun h => by
  have := (@h Nat Unit Unit Unit EC _ (1:Nat) (2:Nat) () () [] [] ⟨_, _, _, _, bs1⟩ ⟨_, _, _, _, bs2⟩).2
  simp at this

-- `Iris.ProgramLogic.EctxLanguage.base_redex_unique` idx 13: necessary (fill [()] 0 = fill [] 2, e = 0 not reducible)
theorem w7c1_83 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.base_redex_unique 13 := fun h => by
  have := (@h Nat Unit Unit Unit EC _ (0:Nat) (2:Nat) () () [()] [] rfl ⟨_, _, _, _, bs2⟩).2
  simp at this

-- `Iris.ProgramLogic.EctxLanguage.base_redex_unique` idx 14: necessary (fill [] 2 = fill [()] 0, e' = 0 not reducible)
theorem w7c1_84 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.base_redex_unique 14 := fun h => by
  have := (@h Nat Unit Unit Unit EC _ (2:Nat) (0:Nat) () () [] [()] rfl ⟨_, _, _, _, bs2⟩).2
  simp at this

-- `Iris.ProgramLogic.EctxLanguage.primStep_of_baseStep` idx 12: necessary (0 has no prim step)
theorem w7c1_85 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.primStep_of_baseStep 12 := fun h =>
  no_ps0 (@h Nat Unit Unit Unit EC _ (0:Nat) () [] (0:Nat) () [])

-- `Iris.ProgramLogic.EctxLanguage.baseStep_of_primStep` idx 12: necessary (e₁ = 0 has redexes-are-values, no base step)
theorem w7c1_86 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.baseStep_of_primStep 12 := fun h => by
  rcases no_bs (@h Nat Unit Unit Unit EC _ (0:Nat) () [] (0:Nat) () [] sub0) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.baseStep_of_primStep` idx 13: necessary (4 = fill [()] 1 prim-steps, no base step)
theorem w7c1_87 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.baseStep_of_primStep 13 := fun h => by
  rcases no_bs (@h Nat Unit Unit Unit EC _ (4:Nat) () [] (4:Nat) () [] ps4) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.baseStep_iff_primStep_of_subredexesAreValues` idx 12: necessary (e₁ = 4)
theorem w7c1_88 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.baseStep_iff_primStep_of_subredexesAreValues 12 := fun h => by
  rcases no_bs ((@h Nat Unit Unit Unit EC _ (4:Nat) () [] (4:Nat) () []).1 ps4) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.base_step_not_stuck` idx 12: necessary (3 is stuck)
theorem w7c1_89 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.base_step_not_stuck 12 := fun h => by
  rcases @h Nat Unit Unit Unit EC _ (3:Nat) () [] (0:Nat) () [] with h1 | ⟨_, _, _, _, h1⟩
  · simp [toVal, eTV] at h1
  · exact no_ps3 h1

-- `Iris.ProgramLogic.EctxLanguage.fill_primStep` idx 13: necessary (K = [], e = 0)
theorem w7c1_90 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.fill_primStep 13 := fun h =>
  no_ps0 (@h Nat Unit Unit Unit EC _ [] (0:Nat) () [] (0:Nat) () [])

-- `Iris.ProgramLogic.EctxLanguage.fill_reducible` idx 9: necessary (K = [], e = 0)
theorem w7c1_91 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.fill_reducible 9 := fun h => by
  obtain ⟨_, _, _, _, h1⟩ := @h Nat Unit Unit Unit EC _ [] (0:Nat) ()
  exact no_ps0 h1

-- `Iris.ProgramLogic.EctxLanguage.reducibleNoObs_fill` idx 9: necessary (K = [], e = 0)
theorem w7c1_92 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.reducibleNoObs_fill 9 := fun h => by
  obtain ⟨_, _, _, h1⟩ := @h Nat Unit Unit Unit EC _ [] (0:Nat) ()
  exact no_ps0 h1

-- `Iris.ProgramLogic.EctxLanguage.primStep_reducible_of_baseStep_reducible` idx 8: necessary (e = 0)
theorem w7c1_93 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.primStep_reducible_of_baseStep_reducible 8 := fun h => by
  obtain ⟨_, _, _, _, h1⟩ := @h Nat Unit Unit Unit EC _ (0:Nat) ()
  exact no_ps0 h1

-- `Iris.ProgramLogic.EctxLanguage.primStep_reducible_fill_of_baseStep_reducible` idx 9: necessary (e = 0, K = [])
theorem w7c1_94 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.primStep_reducible_fill_of_baseStep_reducible 9 := fun h => by
  obtain ⟨_, _, _, _, h1⟩ := @h Nat Unit Unit Unit EC _ (0:Nat) () []
  exact no_ps0 h1

-- `Iris.ProgramLogic.EctxLanguage.primStep_reducibleNoObs_of_baseStep_reducibleNoObs` idx 8: necessary (e = 0)
theorem w7c1_95 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.primStep_reducibleNoObs_of_baseStep_reducibleNoObs 8 := fun h => by
  obtain ⟨_, _, _, h1⟩ := @h Nat Unit Unit Unit EC _ (0:Nat) ()
  exact no_ps0 h1

-- `Iris.ProgramLogic.EctxLanguage.primStep_reducibleNoObs_fill_of_baseStep_reducibleNoObs` idx 9: necessary (e = 0, K = [])
theorem w7c1_96 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.primStep_reducibleNoObs_fill_of_baseStep_reducibleNoObs 9 := fun h => by
  obtain ⟨_, _, _, h1⟩ := @h Nat Unit Unit Unit EC _ (0:Nat) () []
  exact no_ps0 h1

-- `Iris.ProgramLogic.EctxLanguage.baseStep_irreducible_of_primStep_irreducible` idx 8: necessary (e = 2 base-steps)
theorem w7c1_97 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.baseStep_irreducible_of_primStep_irreducible 8 := fun h =>
  @h Nat Unit Unit Unit EC _ (2:Nat) () [] (0:Nat) () [] bs2

-- `Iris.ProgramLogic.EctxLanguage.baseStep_reducible_of_primStep_reducible` idx 8: necessary (e = 0)
theorem w7c1_98 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.baseStep_reducible_of_primStep_reducible 8 := fun h => by
  obtain ⟨_, _, _, _, h1⟩ := @h Nat Unit Unit Unit EC _ (0:Nat) () sub0
  rcases no_bs h1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.baseStep_reducible_of_primStep_reducible` idx 9: necessary (e = 4 = fill [()] 1)
theorem w7c1_99 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.baseStep_reducible_of_primStep_reducible 9 := fun h => by
  obtain ⟨_, _, _, _, h1⟩ := @h Nat Unit Unit Unit EC _ (4:Nat) () ⟨_, _, _, _, ps4⟩
  rcases no_bs h1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.primStep_irreducible_of_baseStep_irreducible` idx 8: necessary (e = 2)
theorem w7c1_100 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.primStep_irreducible_of_baseStep_irreducible 8 := fun h =>
  @h Nat Unit Unit Unit EC _ (2:Nat) () sub2 [] (0:Nat) () [] (EctxLanguage.primStep_of_baseStep bs2)

-- `Iris.ProgramLogic.EctxLanguage.primStep_irreducible_of_baseStep_irreducible` idx 9: necessary (e = 4)
theorem w7c1_101 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.primStep_irreducible_of_baseStep_irreducible 9 := fun h =>
  @h Nat Unit Unit Unit EC _ (4:Nat) ()
    (fun _ _ _ _ h1 => by rcases no_bs h1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1) [] (4:Nat) () [] ps4

-- `Iris.ProgramLogic.EctxLanguage.primStep_stuck_of_baseStep_stuck` idx 8: necessary (e = 2)
theorem w7c1_102 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.primStep_stuck_of_baseStep_stuck 8 := fun h =>
  (@h Nat Unit Unit Unit EC _ (2:Nat) () sub2).2 [] (0:Nat) () [] (EctxLanguage.primStep_of_baseStep bs2)

-- `Iris.ProgramLogic.EctxLanguage.primStep_stuck_of_baseStep_stuck` idx 9: necessary (e = 4)
theorem w7c1_103 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.primStep_stuck_of_baseStep_stuck 9 := fun h =>
  (@h Nat Unit Unit Unit EC _ (4:Nat) ()
    ⟨rfl, fun _ _ _ _ h1 => by rcases no_bs h1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1⟩).2 [] (4:Nat) () [] ps4

-- `Iris.ProgramLogic.EctxLanguage.Atomic.ofBaseAtomic` idx 8: necessary (e = 1 steps to the non-value 1)
theorem w7c1_104 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.Atomic.ofBaseAtomic 8 := fun h => by
  have := (@h Nat Unit Unit Unit EC _ (1:Nat) .StronglyAtomic sub1).atomic (EctxLanguage.primStep_of_baseStep bs1)
  simp [toVal, eTV] at this

-- `Iris.ProgramLogic.EctxLanguage.Atomic.ofBaseAtomic` idx 9: necessary (e = 4: no base step, prim step to 4)
theorem w7c1_105 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.Atomic.ofBaseAtomic 9 := fun h => by
  have := (@h Nat Unit Unit Unit EC _ (4:Nat) .StronglyAtomic
    (fun _ _ _ _ _ h1 => by rcases no_bs h1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1)).atomic ps4
  simp [toVal, eTV] at this

-- `Iris.ProgramLogic.EctxLanguage.exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible` idx 13: necessary (e₁ = 0, K = [()])
theorem w7c1_106 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible 13 := fun h => by
  obtain ⟨e₂, he, _⟩ := @h Nat Unit Unit Unit EC _ (0:Nat) (0:Nat) () () [()] [] []
    (EctxLanguage.primStep_of_baseStep bs2)
  change 0 = 2 * e₂ + 2 at he; omega

-- `Iris.ProgramLogic.EctxLanguage.exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible` idx 14: necessary (e₁ = 2, e' = 7)
theorem w7c1_107 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible 14 := fun h => by
  obtain ⟨e₂, he, h1⟩ := @h Nat Unit Unit Unit EC _ (7:Nat) (2:Nat) () () [] [] [] ⟨_, _, _, _, bs2⟩
  change 7 = e₂ at he; subst he
  rcases no_bs h1 with ⟨_, h1⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.baseStep_of_primStep_of_baseStep_reducible` idx 12: necessary (e₁ = 4)
theorem w7c1_108 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.baseStep_of_primStep_of_baseStep_reducible 12 := fun h => by
  rcases no_bs (@h Nat Unit Unit Unit EC _ (4:Nat) (4:Nat) () () [] [] ps4) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.baseStep_of_primStep_of_baseStep_reducible` idx 13: necessary (e₁ = 2, e₂ = 7)
theorem w7c1_109 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.baseStep_of_primStep_of_baseStep_reducible 13 := fun h => by
  rcases no_bs (@h Nat Unit Unit Unit EC _ (2:Nat) (7:Nat) () () [] [] ⟨_, _, _, _, bs2⟩) with ⟨_, h1⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.PureBaseStep.safe` idx 8: necessary (e₁ = 0)
theorem w7c1_110 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.PureBaseStep.safe 8 := fun h => by
  obtain ⟨_, _, _, h1⟩ := @h Nat Unit Unit Unit EC _ (0:Nat) (0:Nat) ()
  rcases no_bs h1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1

-- `Iris.ProgramLogic.EctxLanguage.PureBaseStep.deterministic` idx 8: necessary (e₁ = 2, e₂ = 5)
theorem w7c1_111 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.PureBaseStep.deterministic 8 := fun h => by
  have := (@h Nat Unit Unit Unit EC _ (2:Nat) (5:Nat) () () [] (0:Nat) [] bs2).2.2.1
  simp at this

theorem pbs20 : EctxLanguage.PureBaseStep (Ectx := EC) (2:Nat) (0:Nat) :=
  ⟨fun _ => ⟨_, _, _, bs2⟩, fun h1 => by
    rcases h1 with ⟨h1, h2, h3 | h3⟩
    · exact ⟨h1, rfl, h3.2.symm, h2⟩
    · simp at h3⟩

-- `Iris.ProgramLogic.EctxLanguage.PureBaseStep.deterministic` idx 14: necessary (PureBaseStep 2 0, e₂' = 7)
theorem w7c1_112 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.PureBaseStep.deterministic 14 := fun h => by
  have := (@h Nat Unit Unit Unit EC _ (2:Nat) (0:Nat) pbs20 () () [] (7:Nat) []).2.2.1
  simp at this

-- `Iris.ProgramLogic.EctxLanguage.purePrimStep_of_pureBaseStep` idx 8: necessary (e₁ = 0)
theorem w7c1_113 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.purePrimStep_of_pureBaseStep 8 := fun h => by
  obtain ⟨_, _, _, h1⟩ := (@h Nat Unit Unit Unit EC _ (0:Nat) (0:Nat)).safe ()
  exact no_ps0 h1

-- `Iris.ProgramLogic.EctxLanguage.pureExec_fill` idx 11: necessary (n = 0, e₁ = 0, e₂ = 1)
theorem w7c1_114 : ¬ drop0% Iris.ProgramLogic.EctxLanguage.pureExec_fill 11 := fun h => by
  have := (@h Nat Unit Unit Unit EC _ (0:Nat) (1:Nat) [] True 0).pureExec trivial
  cases this

end W7c1

namespace W7c1
open Iris Iris.ProgramLogic

/-- Toy threaded language on Fin 3 (after Probe3's tl): 0 the only value, 1 stuck,
2 steps to itself and forks a thread 2. -/
instance tlV : ToVal (Fin 3) Unit where
  toVal n := if n = 0 then some () else none
  ofVal _ := 0
  coe_of_toVal_eq_some {e v} h := by cases v; revert h; revert e; decide
  toVal_coe _ := rfl

instance tlL : Language (Fin 3) Unit Unit Unit where
  primStep c _ c' := c.1 = 2 ∧ c'.1 = 2 ∧ c'.2.2 = [2]
  val_stuck {e} := by intro _ _ _ _ _ ⟨h, _⟩; simp only at h; subst h; rfl

theorem tl_noErased (e : Fin 3) (he : e ≠ 2) {c : List (Fin 3) × Unit} :
    ¬ Language.ErasedStep ([e], ()) c := by
  rintro ⟨_, hs⟩
  generalize hb : (([e] : List (Fin 3)), ()) = b at hs
  cases hs with
  | @atomic e0 σ obs e' σ' eₜ H t₁ t₂ =>
    obtain ⟨he0, _⟩ := H
    have h1 : [e] = t₁ ++ e0 :: t₂ := congrArg Prod.fst hb
    have hm : e0 ∈ t₁ ++ e0 :: t₂ := List.mem_append_right t₁ List.mem_cons_self
    rw [← h1] at hm
    simp at hm he0
    exact absurd (hm ▸ he0) he

theorem tl_stays (e : Fin 3) (he : e ≠ 2) {c : List (Fin 3) × Unit} :
    FromMathlib.Relation.ReflTransGen Language.ErasedStep ([e], ()) c → c = ([e], ()) := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact (tl_noErased e he hs).elim

theorem tl_noStep (e : Fin 3) (he : e ≠ 2) {σ obs e' σ' eₜ} :
    ¬ PrimStep.primStep (Expr := Fin 3) (e, (σ : Unit)) obs (e', (σ' : Unit), eₜ) :=
  fun h => he h.1

theorem tl_notStuck1 : ¬ PrimStep.NotStuck ((1 : Fin 3), ()) := by
  rintro (h | ⟨_, _, _, _, h⟩)
  · simp [toVal, ToVal.toVal] at h
  · exact tl_noStep 1 (by decide) h

theorem tl_adeqNF (φ : Unit → Unit → Prop) : AdequateNoFork .MaybeStuck (1 : Fin 3) () φ where
  no_fork h := by have := congrArg Prod.fst (tl_stays 1 (by decide) h); simp at this; simp [this]
  result h := by have := congrArg Prod.fst (tl_stays 1 (by decide) h); simp [ToVal.ofVal] at this
  not_stuck hs := by cases hs

theorem tl_adeq (φ : Unit → Unit → Prop) : adequate .MaybeStuck (1 : Fin 3) () φ where
  adequate_result _ _ _ h := by have := congrArg Prod.fst (tl_stays 1 (by decide) h); simp [ToVal.ofVal] at this
  adequate_not_stuck _ _ _ hs := by cases hs

theorem tl_adeq0 : adequate .NotStuck (0 : Fin 3) () (fun _ _ => True) where
  adequate_result _ _ _ _ := trivial
  adequate_not_stuck _ _ e2 _ h hm := by
    have := congrArg Prod.fst (tl_stays 0 (by decide) h); simp at this; subst this
    simp at hm; subst hm; left; rfl

theorem tl_adeqNF0 : AdequateNoFork .NotStuck (0 : Fin 3) () (fun _ _ => True) where
  no_fork h := by have := congrArg Prod.fst (tl_stays 0 (by decide) h); simp at this; simp [this]
  result _ := trivial
  not_stuck _ h hm := by
    have := congrArg Prod.fst (tl_stays 0 (by decide) h); simp at this; subst this
    simp at hm; subst hm; left; rfl

theorem tl_step2 : PrimStep.primStep (Expr := Fin 3) ((2 : Fin 3), ()) [] ((2 : Fin 3), (), [(2 : Fin 3)]) :=
  ⟨rfl, rfl, rfl⟩

theorem tl_fork : FromMathlib.Relation.ReflTransGen Language.ErasedStep (([2] : List (Fin 3)), ()) ([2, 2], ()) :=
  .tail .refl ⟨[], by simpa using Language.Step.atomic (t₁ := []) (t₂ := []) tl_step2⟩

-- `Iris.ProgramLogic.adequate.adequate_result` idx 9: necessary (e₁ = 0 a value, φ = False)
theorem w7c1_45 : ¬ drop0% Iris.ProgramLogic.adequate.adequate_result 9 := fun h =>
  @h (Fin 3) Unit Unit Unit _ .MaybeStuck 0 () (fun _ _ => False) [] () () .refl

-- `Iris.ProgramLogic.adequate.adequate_result` idx 13: necessary (stuck program 1 adequate for False)
theorem w7c1_46 : ¬ drop0% Iris.ProgramLogic.adequate.adequate_result 13 := fun h =>
  @h (Fin 3) Unit Unit Unit _ .MaybeStuck 1 () (fun _ _ => False) (tl_adeq _) [] () ()

-- `Iris.ProgramLogic.adequate.adequate_not_stuck` idx 9: necessary (stuck program 1)
theorem w7c1_47 : ¬ drop0% Iris.ProgramLogic.adequate.adequate_not_stuck 9 := fun h =>
  tl_notStuck1 (@h (Fin 3) Unit Unit Unit _ .NotStuck 1 () (fun _ _ => True) [1] () 1 rfl .refl (by simp))

-- `Iris.ProgramLogic.adequate.adequate_not_stuck` idx 13: necessary (MaybeStuck-adequate stuck program 1)
theorem w7c1_48 : ¬ drop0% Iris.ProgramLogic.adequate.adequate_not_stuck 13 := fun h =>
  tl_notStuck1 (@h (Fin 3) Unit Unit Unit _ .MaybeStuck 1 () (fun _ _ => False) (tl_adeq _) [1] () 1 .refl (by simp))

-- `Iris.ProgramLogic.adequate.adequate_not_stuck` idx 14: necessary (value 0 adequate; unreachable pool [1])
theorem w7c1_49 : ¬ drop0% Iris.ProgramLogic.adequate.adequate_not_stuck 14 := fun h =>
  tl_notStuck1 (@h (Fin 3) Unit Unit Unit _ .NotStuck 0 () _ tl_adeq0 [1] () 1 rfl (by simp))

-- `Iris.ProgramLogic.adequate.adequate_not_stuck` idx 15: necessary (value 0 adequate; thread 1 not in the pool)
theorem w7c1_50 : ¬ drop0% Iris.ProgramLogic.adequate.adequate_not_stuck 15 := fun h =>
  tl_notStuck1 (@h (Fin 3) Unit Unit Unit _ .NotStuck 0 () _ tl_adeq0 [0] () 1 rfl .refl)

-- `Iris.ProgramLogic.AdequateNoFork.no_fork` idx 9: necessary (2 forks)
theorem w7c1_51 : ¬ drop0% Iris.ProgramLogic.AdequateNoFork.no_fork 9 := fun h => by
  have := @h (Fin 3) Unit Unit Unit _ .MaybeStuck 2 () (fun _ _ => True) [2, 2] () tl_fork
  simp at this

-- `Iris.ProgramLogic.AdequateNoFork.no_fork` idx 12: necessary (t₂ = [])
theorem w7c1_52 : ¬ drop0% Iris.ProgramLogic.AdequateNoFork.no_fork 12 := fun h => by
  have := @h (Fin 3) Unit Unit Unit _ .MaybeStuck 1 () (fun _ _ => False) (tl_adeqNF _) [] ()
  simp at this

-- `Iris.ProgramLogic.AdequateNoFork.result` idx 9: necessary (e₁ = 0 a value, φ = False)
theorem w7c1_53 : ¬ drop0% Iris.ProgramLogic.AdequateNoFork.result 9 := fun h =>
  @h (Fin 3) Unit Unit Unit _ .MaybeStuck 0 () (fun _ _ => False) [] () () .refl

-- `Iris.ProgramLogic.AdequateNoFork.not_stuck` idx 9: necessary (stuck program 1)
theorem w7c1_54 : ¬ drop0% Iris.ProgramLogic.AdequateNoFork.not_stuck 9 := fun h =>
  tl_notStuck1 (@h (Fin 3) Unit Unit Unit _ .NotStuck 1 () (fun _ _ => True) [1] () 1 rfl .refl (by simp))

-- `Iris.ProgramLogic.AdequateNoFork.not_stuck` idx 13: necessary (MaybeStuck stuck program 1)
theorem w7c1_55 : ¬ drop0% Iris.ProgramLogic.AdequateNoFork.not_stuck 13 := fun h =>
  tl_notStuck1 (@h (Fin 3) Unit Unit Unit _ .MaybeStuck 1 () (fun _ _ => False) (tl_adeqNF _) [1] () 1 .refl (by simp))

-- `Iris.ProgramLogic.AdequateNoFork.not_stuck` idx 14: necessary (value 0; unreachable pool [1])
theorem w7c1_56 : ¬ drop0% Iris.ProgramLogic.AdequateNoFork.not_stuck 14 := fun h =>
  tl_notStuck1 (@h (Fin 3) Unit Unit Unit _ .NotStuck 0 () _ tl_adeqNF0 [1] () 1 rfl (by simp))

-- `Iris.ProgramLogic.AdequateNoFork.not_stuck` idx 15: necessary (value 0; thread 1 not in the pool)
theorem w7c1_57 : ¬ drop0% Iris.ProgramLogic.AdequateNoFork.not_stuck 15 := fun h =>
  tl_notStuck1 (@h (Fin 3) Unit Unit Unit _ .NotStuck 0 () _ tl_adeqNF0 [0] () 1 rfl .refl)

theorem tl_bad1 : ¬ ((∀ (e : Fin 3), e ∈ [1] → ∃ (v : Unit), toVal e = some v) ∨
    ∃ (t3 : List (Fin 3)), ∃ (σ3 : Unit), Language.ErasedStep ([1], ()) (t3, σ3)) := by
  rintro (h | ⟨t3, σ3, hs⟩)
  · obtain ⟨_, hv⟩ := h 1 (by simp); simp [toVal, ToVal.toVal] at hv
  · exact tl_noErased 1 (by decide) hs

-- `Iris.ProgramLogic.adequate_tp_safe` idx 10: necessary (stuck program 1)
theorem w7c1_58 : ¬ drop0% Iris.ProgramLogic.adequate_tp_safe 10 := fun h =>
  tl_bad1 (@h (Fin 3) Unit Unit Unit _ 1 [1] () () (fun _ _ => True) .refl)

-- `Iris.ProgramLogic.adequate_tp_safe` idx 11: necessary (value 0 adequate; unreachable pool [1])
theorem w7c1_59 : ¬ drop0% Iris.ProgramLogic.adequate_tp_safe 11 := fun h =>
  tl_bad1 (@h (Fin 3) Unit Unit Unit _ 0 [1] () () _ tl_adeq0)

-- `Iris.ProgramLogic.adequateNoFork_step` idx 11: necessary (from stuck 1 to forking 2)
theorem w7c1_60 : ¬ drop0% Iris.ProgramLogic.adequateNoFork_step 11 := fun h => by
  have := (@h (Fin 3) Unit Unit Unit _ 1 2 () () .MaybeStuck (fun _ _ => True) (tl_adeqNF _)).no_fork tl_fork
  simp at this

-- `Iris.ProgramLogic.adequateNoFork_step` idx 12: necessary (value 0 with Q = False)
theorem w7c1_61 : ¬ drop0% Iris.ProgramLogic.adequateNoFork_step 12 := fun h =>
  (@h (Fin 3) Unit Unit Unit _ 0 0 () () .MaybeStuck (fun _ _ => False) .refl).result (t₂ := []) (v₂ := ()) .refl

-- `Iris.ProgramLogic.adequateNoFork_primStep` idx 12: necessary (from stuck 1 to value 0, Q = False)
theorem w7c1_62 : ¬ drop0% Iris.ProgramLogic.adequateNoFork_primStep 12 := fun h =>
  (@h (Fin 3) Unit Unit Unit _ 1 0 [] () () .MaybeStuck (fun _ _ => False) (tl_adeqNF _)).result
    (t₂ := []) (v₂ := ()) .refl

-- `Iris.ProgramLogic.adequateNoFork_primStep` idx 13: necessary (ectx toy language: 2 steps to the value 0, Q = False)
theorem w7c1_63 : ¬ drop0% Iris.ProgramLogic.adequateNoFork_primStep 13 := fun h =>
  (@h Nat Unit Unit Unit (EctxLanguage.instLanguage (Ectx := EC)) 2 0 [] () () .MaybeStuck (fun _ _ => False)
    (EctxLanguage.primStep_of_baseStep bs2)).result (t₂ := []) (v₂ := ()) .refl

-- `Iris.ProgramLogic.adequateNoFork_efs_nil` idx 9: necessary (2 forks)
theorem w7c1_64 : ¬ drop0% Iris.ProgramLogic.adequateNoFork_efs_nil 9 := fun h => by
  have := @h (Fin 3) Unit Unit Unit _ 2 () .MaybeStuck (fun _ _ => True) [2] () 2 .refl (by simp) [] 2 () [2] tl_step2
  simp at this

-- `Iris.ProgramLogic.adequateNoFork_efs_nil` idx 13: necessary (stuck 1 adequate; thread 2 of an unreachable pool forks)
theorem w7c1_65 : ¬ drop0% Iris.ProgramLogic.adequateNoFork_efs_nil 13 := fun h => by
  have := @h (Fin 3) Unit Unit Unit _ 1 () .MaybeStuck (fun _ _ => False) (tl_adeqNF _) [2] () 2 (by simp) [] 2 () [2] tl_step2
  simp at this

-- `Iris.ProgramLogic.adequateNoFork_efs_nil` idx 19: necessary (efs = [1] arbitrary)
theorem w7c1_66 : ¬ drop0% Iris.ProgramLogic.adequateNoFork_efs_nil 19 := fun h => by
  have := @h (Fin 3) Unit Unit Unit _ 1 () .MaybeStuck (fun _ _ => False) (tl_adeqNF _) [1] () 1 .refl (by simp) [] 1 () [1]
  simp at this

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF

/-- IProp soundness: `⊢ |={⊤}=> False` under every IrisGS_gen (trivial state interpretation) is impossible. -/
theorem soundIG {Expr State Obs Val : Type} [Language Expr State Obs Val]
    (H : ∀ (ι : IrisGS_gen .hasNoLC Expr CGF), ⊢ (iprop(|={⊤}=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun x =>
      letI ι : IrisGS_gen .hasNoLC Expr CGF :=
        { invGS := x, stateInterp := fun _ _ _ _ => iprop(True), numLatersPerStep := fun _ => 0,
          forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }
      wand_intro (sep_elim_left.trans (H ι)))

theorem soundF {Expr State Obs Val : Type} [Language Expr State Obs Val]
    (H : ∀ (ι : IrisGS_gen .hasNoLC Expr CGF), ⊢ (iprop(⌜False⌝) : IProp CGF)) : False :=
  soundIG (Expr := Expr) fun ι => (H ι).trans fupd_intro

/-- `(|={⊤}=> False) ⊢ False` under every IrisGS_gen is impossible (Löb on `|={⊤}=> False`). -/
theorem soundL {Expr State Obs Val : Type} [Language Expr State Obs Val]
    (H : ∀ (ι : IrisGS_gen .hasNoLC Expr CGF), (iprop(|={⊤}=> ⌜False⌝) : IProp CGF) ⊢ iprop(⌜False⌝)) : False :=
  soundIG (Expr := Expr) fun ι => true_intro.trans (loeb_weak ((later_mono (H ι)).trans
    ((or_intro_l (Q := iprop(|={⊤}=> ⌜False⌝))).trans BIFUpdate.except0)))

theorem at2 : Language.Atomic (Expr := Nat) .WeaklyAtomic 2 :=
  EctxLanguage.Atomic.ofBaseAtomic (Ectx := EC) .WeaklyAtomic (fun _ _ _ _ _ h => by
    rcases no_bs h with ⟨_, h1⟩ | ⟨h1, _⟩
    · subst h1; exact fun _ _ _ _ h2 => no_ps0 h2
    · simp at h1) sub2

theorem at0 : Language.Atomic (Expr := Fin 3) .WeaklyAtomic 0 :=
  ⟨fun h => by obtain ⟨h1, _⟩ := h; simp at h1⟩

-- `Iris.InvOpenAbstractWP.inv_open_maybe` idx 9: necessary (ectx toy language, wp E e Φ := ⌜e = 2⌝, e = 6 = fill [()] 2: left disjunct holds, ⌜6 = 2⌝ fails; fupd soundness)
theorem w7c1_23 : ¬ drop0% Iris.InvOpenAbstractWP.inv_open_maybe 9 := fun h => soundF (Expr := Nat) fun ι => by
  have H := @h Nat Unit Unit Unit _ CGF .hasNoLC ι (fun _ e _ => iprop(⌜e = 2⌝)) 6 ⊤ ⊤ (fun _ => iprop(True))
    LawfulSet.subset_refl
  refine Entails.trans ?_ (H.trans (pure_mono (fun e => absurd e (by decide))))
  iintro _
  imodintro
  ileft
  iexists (fill (Expr := Nat) ([()] : EC)), (2:Nat)
  isplitr
  · ipureintro; exact EctxLanguage.instContextFill _
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact at2
  · ipureintro; rfl

-- `Iris.LawfulAbstractWP.fupd_wp` idx 9: necessary (wp := ⌜False⌝: (|={⊤}=> False) ⊢ False contradicts Löb + fupd soundness)
theorem w7c1_25 : ¬ drop0% Iris.LawfulAbstractWP.fupd_wp 9 := fun h => soundL (Expr := Fin 3) fun ι =>
  @h (Fin 3) Unit Unit Unit _ CGF .hasNoLC ι (fun _ _ _ => iprop(⌜False⌝)) ⊤ 0 (fun _ => iprop(True))

-- `Iris.LawfulAbstractWP.wp_value` idx 9: necessary (wp := ⌜False⌝, Φ := True)
theorem w7c1_26 : ¬ drop0% Iris.LawfulAbstractWP.wp_value 9 := fun h => soundF (Expr := Fin 3) fun ι =>
  true_intro.trans <| fupd_intro.trans (@h (Fin 3) Unit Unit Unit _ CGF .hasNoLC ι (fun _ _ _ => iprop(⌜False⌝)) ⊤ (fun _ => iprop(True)) ()).2

-- `Iris.LawfulAbstractWP.wp_wand` idx 9: necessary (antitone wp E e Φ := Φ () -∗ False, Φ := False, Ψ := True)
theorem w7c1_27 : ¬ drop0% Iris.LawfulAbstractWP.wp_wand 9 := fun h => soundF (Expr := Fin 3) fun ι => by
  have H := @h (Fin 3) Unit Unit Unit _ CGF .hasNoLC ι (fun _ _ Φ => iprop(Φ () -∗ ⌜False⌝)) ⊤ 0
    (fun _ => iprop(⌜False⌝)) (fun _ => iprop(True))
  iintro
  ihave H1 := H $$ []
  · iintro %hf; exact hf.elim
  iapply H1
  · iintro %_ %hf; exact hf.elim
  · itrivial

-- `Iris.LawfulAbstractWP.wp_atomic` idx 9: necessary (wp := ⌜False⌝, value 0 atomic, E₁ = E₂ = ⊤; Löb + fupd soundness)
theorem w7c1_28 : ¬ drop0% Iris.LawfulAbstractWP.wp_atomic 9 := fun h => soundL (Expr := Fin 3) fun ι =>
  @h (Fin 3) Unit Unit Unit _ CGF .hasNoLC ι (fun _ _ _ => iprop(⌜False⌝)) ⊤ ⊤ (fun _ => iprop(True)) 0 at0

-- `Iris.BindAbstractWP.toLawfulAbstractWP` idx 9: necessary (wp := ⌜False⌝ violates wp_value)
theorem w7c1_30 : ¬ drop0% Iris.BindAbstractWP.toLawfulAbstractWP 9 := fun h => soundF (Expr := Fin 3) fun ι =>
  true_intro.trans <| fupd_intro.trans ((@h (Fin 3) Unit Unit Unit _ CGF .hasNoLC ι (fun _ _ _ => iprop(⌜False⌝))).wp_value
    (E := ⊤) (Φ := fun _ => iprop(True)) (v := ())).2

-- `Iris.BindAbstractWP.wp_bind` idx 9: necessary (antitone wp E e Φ := Φ () -∗ False, K = id, Φ := False)
theorem w7c1_31 : ¬ drop0% Iris.BindAbstractWP.wp_bind 9 := fun h => soundF (Expr := Fin 3) fun ι => by
  have H := (@h (Fin 3) Unit Unit Unit _ CGF .hasNoLC ι (fun _ _ Φ => iprop(Φ () -∗ ⌜False⌝)) id ⊤ 0
    (fun _ => iprop(⌜False⌝)) (Language.instContext_id)).2
  iintro
  ihave H1 := H $$ []
  · iintro %hf; exact hf.elim
  iapply H1
  iintro %hf; exact hf.elim

-- `Iris.inv_open_maybe_ectxlang` idx 10: necessary (wp E e Φ := ⌜e = 2⌝, e = 6 = fill [()] 2)
theorem w7c1_33 : ¬ drop0% Iris.inv_open_maybe_ectxlang 10 := fun h => soundF (Expr := Nat) fun ι => by
  have H := @h Nat Unit Unit Unit EC _ CGF .hasNoLC ι (fun _ e _ => iprop(⌜e = 2⌝)) 6 ⊤ ⊤ (fun _ => iprop(True))
    LawfulSet.subset_refl ⟨(), _, _, _, _, BaseStep.ContextStep.ofBaseStep (Ectx := EC) [()] bs2⟩
  refine Entails.trans ?_ (H.trans (pure_mono (fun e => absurd e (by decide))))
  iintro _
  imodintro
  ileft
  iexists ([()] : EC), (2:Nat)
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact at2
  isplitr
  · ipureintro; exact ⟨(), _, _, _, _, bs2⟩
  · ipureintro; rfl

-- `Iris.wp_inv_open_maybe_of_not_val` idx 12: removable (the library's `Iris.wp_inv_open_maybe` states the same without the hypothesis)
theorem w7c1_39 : drop% Iris.wp_inv_open_maybe_of_not_val 12 := by
  intro Expr State Obs Val _ GF HLC _ e E₁ E₂ Φ
  exact wp_inv_open_maybe e E₁ E₂ Φ

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- IrisGS_gen with state interpretation constantly False. -/
@[reducible] noncomputable def igF (Expr : Type) {State Obs Val : Type} [Language Expr State Obs Val]
    (x : InvGS_gen .hasNoLC CGF) : IrisGS_gen .hasNoLC Expr CGF :=
  { invGS := x, stateInterp := fun _ _ _ _ => iprop(⌜False⌝), numLatersPerStep := fun _ => 0,
    forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => false_elim }

theorem soundX (H : ∀ (x : InvGS_gen .hasNoLC CGF), ⊢ (iprop(|={⊤}=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun x =>
      wand_intro (sep_elim_left.trans (H x)))

theorem sF {P Q : IProp CGF} : P ∗ iprop(⌜False⌝) ⊢ Q := sep_elim_right.trans false_elim


-- `Rocq.wp_lift_base_step_fupd` idx 13: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l1 : ¬ drop0% Rocq.wp_lift_base_step_fupd 13 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_base_step_fupd` idx 13: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l2 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_base_step_fupd 13 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `Rocq.wp_lift_base_step` idx 13: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l3 : ¬ drop0% Rocq.wp_lift_base_step 13 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_base_step` idx 13: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l4 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_base_step 13 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `Rocq.wp_lift_atomic_base_step_fupd` idx 14: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l5 : ¬ drop0% Rocq.wp_lift_atomic_base_step_fupd 14 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_atomic_base_step_fupd` idx 14: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l6 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_atomic_base_step_fupd 14 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `Rocq.wp_lift_atomic_base_step` idx 13: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l7 : ¬ drop0% Rocq.wp_lift_atomic_base_step 13 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_atomic_base_step` idx 13: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l8 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_atomic_base_step 13 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `Rocq.wp_lift_atomic_base_step_no_fork_fupd` idx 14: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l9 : ¬ drop0% Rocq.wp_lift_atomic_base_step_no_fork_fupd 14 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_atomic_base_step_no_fork_fupd` idx 14: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l10 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_atomic_base_step_no_fork_fupd 14 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `Rocq.wp_lift_atomic_base_step_no_fork` idx 13: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l11 : ¬ drop0% Rocq.wp_lift_atomic_base_step_no_fork 13 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_atomic_base_step_no_fork` idx 13: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l12 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_atomic_base_step_no_fork 13 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `Rocq.wp_lift_base_stuck` idx 12: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l13 : ¬ drop0% Rocq.wp_lift_base_stuck 12 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι ⊤ 0 (fun _ => iprop(⌜False⌝)) sub0
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .MaybeStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_base_stuck` idx 12: necessary (ectx toy language, e = 0 a value; state interpretation False makes the premise trivial and WP 0 {{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_l14 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_base_stuck 12 := fun h => soundX fun x => by
  letI ι := igF Nat x
  have H := @h .hasNoLC Nat EC Unit Unit Unit _ CGF ι ⊤ 0 (fun _ => iprop(⌜False⌝)) sub0
  refine Entails.trans ?_ (H.trans (wp_value_fupd' (s := .MaybeStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => wand_intro sF

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

-- `Iris.inv_open_maybe_ectxlang` idx 16: removable (without reducibility of e, the left disjunct is impossible since e = fill K e' with e' base-reducible; the right disjunct closes by fupd_wp)
theorem w7c1_35 : drop% Iris.inv_open_maybe_ectxlang 16 := by
  intro Expr State Obs Val Ectx _ GF HLC _ wp IWP e E₁ E₂ Φ Hsub
  by_cases Hred : ∃ σ, PrimStep.Reducible (e, σ)
  · exact inv_open_maybe_ectxlang Hsub Hred
  · iintro H
    iapply IWP.toLawfulAbstractWP.fupd_wp
    imod H with (⟨%K, %e', %He, %Hat, %Hr, _⟩ | H')
    · obtain ⟨σ, hr⟩ := Hr
      exact absurd ⟨σ, by rw [He]; exact EctxLanguage.primStep_reducible_fill_of_baseStep_reducible hr⟩ Hred
    · iexact H'

-- `Iris.inv_open_maybe_ectxlang_inv` idx 17: removable (the library proof goes through with the hypothesis-free version of inv_open_maybe_ectxlang above)
theorem w7c1_38 : drop% Iris.inv_open_maybe_ectxlang_inv 17 := by
  intro Expr State Obs Val Ectx _ GF HLC _ wp IWP e E N P Φ Hsub
  iintro ⟨#Hinv, H⟩
  iapply (w7c1_35 (E₂ := E \ nclose N) LawfulSet.diff_subset_left)
  imod inv_acc Hsub $$ Hinv with ⟨HP, Hclose⟩
  imod H $$ HP with (⟨%K, %e', %He, %Hat, %Hred, H⟩|⟨HP, H⟩)
  · imodintro
    ileft
    iexists K, e'
    iframe %He %Hat %Hred
    iapply IWP.wp_wand $$ H
    iintro %v ⟨HP, Hwp⟩
    imod Hclose $$ HP with -
    itrivial
  · iright
    imod Hclose $$ HP with -
    iapply fupd_mask_intro_subseteq LawfulSet.diff_subset_left $$ [$]

theorem hv_of_red {Expr Ectx State Obs Val : Type _} [EctxLanguage Expr Ectx State Obs Val] [Inhabited State]
    {e₁ : Expr} (Hbred : ∀ σ₁ : State, BaseStep.Reducible (e₁, σ₁)) : toVal e₁ = none := by
  obtain ⟨_, _, _, _, hs⟩ := Hbred default
  exact EctxLanguage.val_stuck hs

-- `Rocq.wp_lift_pure_det_base_step_no_fork` idx 16: removable (toVal e₁ = none follows from Hbred at the default state by val_stuck)
theorem w7c1_137 : drop% Rocq.wp_lift_pure_det_base_step_no_fork 16 := by
  intro hlc Expr Ectx State Obs Val Λ GF ι s E e₁ e₂ Φ _ E₂ Hbred Hpure
  exact (priv% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork) E₂ (hv_of_red Hbred) Hbred Hpure

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork` idx 16: removable (toVal e₁ = none follows from Hbred at the default state by val_stuck)
theorem w7c1_140 : drop% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork 16 := by
  intro hlc Expr Ectx State Obs Val Λ GF ι s E e₁ e₂ Φ _ E₂ Hbred Hpure
  exact (priv% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork) E₂ (hv_of_red Hbred) Hbred Hpure

-- `Rocq.wp_lift_pure_det_base_step_no_fork'` idx 15: removable (toVal e₁ = none follows from Hbred at the default state by val_stuck)
theorem w7c1_143 : drop% Rocq.wp_lift_pure_det_base_step_no_fork' 15 := by
  intro hlc Expr Ectx State Obs Val Λ GF ι s E e₁ e₂ Φ _ Hbred Hpure
  exact (priv% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork') (hv_of_red Hbred) Hbred Hpure

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork'` idx 15: removable (toVal e₁ = none follows from Hbred at the default state by val_stuck)
theorem w7c1_146 : drop% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork' 15 := by
  intro hlc Expr Ectx State Obs Val Λ GF ι s E e₁ e₂ Φ _ Hbred Hpure
  exact (priv% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork') (hv_of_red Hbred) Hbred Hpure

end W7c1

namespace W7c1
open Iris Iris.BI


/-- Two-element commutative monoid (e unit, a idempotent) with the equality order: a non-affine UORA. -/
inductive NA | e | a deriving DecidableEq

def NA.op : NA → NA → NA
  | .e, y => y
  | .a, _ => .a

instance naOFE : OFE NA := OFE.ofDiscrete NA
instance naDisc : OFE.Discrete NA := ⟨id⟩

instance instORA : ORA NA := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := NA.op
  Valid := fun _ => True
  Order := Eq
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; rfl
  increasing_closed := by intro x y _ h; cases h; assumption }

instance naRefl : OrderRefl NA := ⟨fun x => show x = x from rfl⟩

instance instUORA : UORA NA where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

-- `UPred.fromSep_ownM` idx 5: necessary (UPred NA (Probe3), a = a, b1 = b2 = e: ownM e ⊢ ownM a fails at e)
theorem w7c1_0 : ¬ drop0% UPred.fromSep_ownM 5 := fun h => by
  have H := (UPred.ownM_op NA.e NA.e).mp.trans (@h NA _ .a .e .e).from_sep 0 ⟨.e, trivial⟩ rfl
  cases H

-- `UPred.combineSepAs_ownM` idx 5: necessary (UPred NA, a = a, b1 = b2 = e)
theorem w7c1_1 : ¬ drop0% UPred.combineSepAs_ownM 5 := fun h => by
  have H := (UPred.ownM_op NA.e NA.e).mp.trans (@h NA _ .a .e .e).combine_sep_as 0 ⟨.e, trivial⟩ rfl
  cases H

-- `UPred.fromAnd_ownM_coreId` idx 5: necessary (UPred NA, a = a, b1 = b2 = e (core-id))
theorem w7c1_2 : ¬ drop0% UPred.fromAnd_ownM_coreId 5 := fun h => by
  have H := (@h NA _ .a .e .e (Iris.Std.TCOr.l (t := ⟨rfl⟩))).from_and 0 ⟨.e, trivial⟩ ⟨rfl, rfl⟩
  cases H

-- `UPred.intoAnd_ownM` idx 6: necessary (UPred NA, p = false, a = a, b1 = b2 = e (increasing))
theorem w7c1_3 : ¬ drop0% UPred.intoAnd_ownM 6 := fun h => by
  have H := (@h NA _ false .a .e .e ⟨fun _ => rfl⟩ ⟨fun _ => rfl⟩).into_and 0 ⟨.a, trivial⟩ rfl
  cases H.1

-- `UPred.intoAnd_ownM` idx 7: necessary (UPred NA, p = false, a = a = a • e, b1 = a, b2 = e)
theorem w7c1_4 : ¬ drop0% UPred.intoAnd_ownM 7 := fun h => by
  have H := (@h NA _ false .a .a .e ⟨rfl⟩ ⟨fun _ => rfl⟩).into_and 0 ⟨.a, trivial⟩ rfl
  cases H.2

-- `UPred.intoSep_ownM` idx 5: necessary (UPred NA, a = e, b1 = b2 = a: ownM e ⊢ ownM (a • a) fails at e)
theorem w7c1_5 : ¬ drop0% UPred.intoSep_ownM 5 := fun h => by
  have H := ((@h NA _ .e .a .a).into_sep.trans (UPred.ownM_op NA.a NA.a).mpr) 0 ⟨.e, trivial⟩ rfl
  cases H

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- The IrisGS_gen instance wp_adequacy_gen builds, with trivial state interpretation and fork postcondition. -/
noncomputable abbrev igT (x : InvGS_gen .hasNoLC CGF) (Expr : Type) {State Obs Val : Type}
    [Language Expr State Obs Val] : IrisGS_gen .hasNoLC Expr CGF :=
  .mk (toStateInterp := ⟨fun _ _ _ _ => iprop(True)⟩) (fun _ => 0) (fun _ => iprop(True)) (fun _ _ _ _ => fupd_intro)

/-- Adequacy for that instance. -/
theorem adeqT {Expr State Obs Val : Type} [Language Expr State Obs Val] (s : Stuckness) (e : Expr) (σ : State)
    (φ : Val → Prop)
    (H : ∀ (x : InvGS_gen .hasNoLC CGF),
      (letI := igT x Expr; ⊢ (WP e @ s ; ⊤ {{ fun v => (iprop(⌜φ v⌝) : IProp CGF) }} : IProp CGF))) : adequate s e σ (fun v _ => φ v) :=
  wp_adequacy_gen (hlc := .hasNoLC) (GF := CGF) s e σ φ (by
    intro x κs
    iapply fupd_intro
    iexists (fun _ _ => iprop(True)), (fun _ => iprop(True))
    isplitr
    · itrivial
    · iapply (H x))

theorem st20 : FromMathlib.Relation.ReflTransGen Language.ErasedStep (([2] : List Nat), ()) (((ToVal.ofVal () : Nat) :: []), ()) :=
  .tail .refl ⟨[], Language.Step.atomic (t₁ := []) (t₂ := []) (EctxLanguage.primStep_of_baseStep (Ectx := EC) bs2)⟩

-- `Rocq.wp_lift_pure_base_stuck` idx 14: necessary (e = 2 reduces to the value 0; WP 2 ?{{False}} contradicts adequacy)
theorem w7c1_125 : ¬ drop0% Rocq.wp_lift_pure_base_stuck 14 := fun h => by
  have A := adeqT (Expr := Nat) .MaybeStuck 2 () (fun _ => False) fun x =>
    @h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) ⊤ 2 (fun _ => iprop(⌜False⌝)) rfl sub2
  exact A.adequate_result [] () () st20

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

theorem stuck6 : ∀ σ : Unit, BaseStep.Stuck ((6 : Nat), σ) := fun _ =>
  ⟨rfl, fun _ _ _ _ h => by rcases no_bs h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1⟩

theorem st620 : FromMathlib.Relation.ReflTransGen Language.ErasedStep (([6] : List Nat), ()) (((ToVal.ofVal () : Nat) :: []), ()) :=
  .tail (.tail .refl ⟨[], Language.Step.atomic (t₁ := []) (t₂ := [])
    (BaseStep.ContextStep.ofBaseStep (Ectx := EC) [()] bs2 : PrimStep.primStep ((6 : Nat), ()) [] ((2 : Nat), (), []))⟩)
    ⟨[], Language.Step.atomic (t₁ := []) (t₂ := []) (EctxLanguage.primStep_of_baseStep (Ectx := EC) bs2)⟩

theorem ns3 : ¬ PrimStep.NotStuck ((3 : Nat), ()) := by
  rintro (h | ⟨_, _, _, _, h⟩)
  · simp [toVal, eTV] at h
  · exact no_ps3 h

theorem wp0T (x : InvGS_gen .hasNoLC CGF) :
    (letI := igT x Nat; ⊢ (WP (0 : Nat) @ Stuckness.NotStuck ; ⊤ {{ fun _ => (iprop(⌜True⌝) : IProp CGF) }} : IProp CGF)) := by
  letI := igT x Nat
  refine Entails.trans ?_ (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => (iprop(⌜True⌝) : IProp CGF)) (v := ())).2
  iintro _
  imodintro
  ipureintro
  trivial

-- `Rocq.wp_lift_base_stuck` idx 13: necessary (ectx toy language, e = 6 = fill [()] 2 is base-stuck but reduces 6 → 2 → 0; WP 6 ?{{False}} contradicts adequacy)
theorem w7c1_q1 : ¬ drop0% Rocq.wp_lift_base_stuck 13 := fun h => by
  have A := adeqT (Expr := Nat) .MaybeStuck 6 () (fun _ => False) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) ⊤ 6 (fun _ => iprop(⌜False⌝)) rfl)
    iintro _ %σ %ns %obs' %nt _
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro -
    ipureintro
    exact stuck6 σ
  exact A.adequate_result [] () () st620

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_base_stuck` idx 13: necessary (ectx toy language, e = 6 = fill [()] 2 is base-stuck but reduces 6 → 2 → 0; WP 6 ?{{False}} contradicts adequacy)
theorem w7c1_q2 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_base_stuck 13 := fun h => by
  have A := adeqT (Expr := Nat) .MaybeStuck 6 () (fun _ => False) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) ⊤ 6 (fun _ => iprop(⌜False⌝)) rfl)
    iintro _ %σ %ns %obs' %nt _
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro -
    ipureintro
    exact stuck6 σ
  exact A.adequate_result [] () () st620

-- `Rocq.wp_lift_pure_base_stuck` idx 13: necessary (ectx toy language, e = 6 = fill [()] 2 is base-stuck but reduces 6 → 2 → 0; WP 6 ?{{False}} contradicts adequacy)
theorem w7c1_q3 : ¬ drop0% Rocq.wp_lift_pure_base_stuck 13 := fun h => by
  have A := adeqT (Expr := Nat) .MaybeStuck 6 () (fun _ => False) fun x =>
    @h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) ⊤ 6 (fun _ => iprop(⌜False⌝)) rfl stuck6
  exact A.adequate_result [] () () st620

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_base_stuck` idx 13: necessary (ectx toy language, e = 6 = fill [()] 2 is base-stuck but reduces 6 → 2 → 0; WP 6 ?{{False}} contradicts adequacy)
theorem w7c1_q4 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_base_stuck 13 := fun h => by
  have A := adeqT (Expr := Nat) .MaybeStuck 6 () (fun _ => False) fun x =>
    @h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) ⊤ 6 (fun _ => iprop(⌜False⌝)) rfl stuck6
  exact A.adequate_result [] () () st620

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_base_stuck` idx 14: necessary (e = 2 reduces to the value 0; WP 2 ?{{False}} contradicts adequacy)
theorem w7c1_q5 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_base_stuck 14 := fun h => by
  have A := adeqT (Expr := Nat) .MaybeStuck 2 () (fun _ => False) fun x =>
    @h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) ⊤ 2 (fun _ => iprop(⌜False⌝)) rfl sub2
  exact A.adequate_result [] () () st20

-- `Rocq.wp_lift_pure_det_base_step_no_fork` idx 17: necessary (ectx toy language, stuck e₁ = 3 (Hpure vacuous), e₂ = 0 with Φ = True: the premise holds, WP 3 {{True}} contradicts adequacy (not stuck))
theorem w7c1_q6 : ¬ drop0% Rocq.wp_lift_pure_det_base_step_no_fork 17 := fun h => by
  have A := adeqT (Expr := Nat) .NotStuck 3 () (fun _ => True) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) .NotStuck ⊤ 3 0
      (fun _ => iprop(⌜True⌝)) _ ⊤ rfl (fun _ _ _ _ _ hs => by rcases no_bs hs with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1))
    exact (wand_intro (sep_elim_left.trans (wp0T x))).trans (later_intro.trans (step_fupd_intro Std.LawfulSet.subset_refl))
  exact ns3 (A.adequate_not_stuck [3] () 3 rfl .refl (by simp))

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork` idx 17: necessary (ectx toy language, stuck e₁ = 3 (Hpure vacuous), e₂ = 0 with Φ = True: the premise holds, WP 3 {{True}} contradicts adequacy (not stuck))
theorem w7c1_q7 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork 17 := fun h => by
  have A := adeqT (Expr := Nat) .NotStuck 3 () (fun _ => True) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) .NotStuck ⊤ 3 0
      (fun _ => iprop(⌜True⌝)) _ ⊤ rfl (fun _ _ _ _ _ hs => by rcases no_bs hs with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1))
    exact (wand_intro (sep_elim_left.trans (wp0T x))).trans (later_intro.trans (step_fupd_intro Std.LawfulSet.subset_refl))
  exact ns3 (A.adequate_not_stuck [3] () 3 rfl .refl (by simp))

-- `Rocq.wp_lift_pure_det_base_step_no_fork'` idx 16: necessary (ectx toy language, stuck e₁ = 3 (Hpure vacuous), e₂ = 0 with Φ = True: the premise holds, WP 3 {{True}} contradicts adequacy (not stuck))
theorem w7c1_q8 : ¬ drop0% Rocq.wp_lift_pure_det_base_step_no_fork' 16 := fun h => by
  have A := adeqT (Expr := Nat) .NotStuck 3 () (fun _ => True) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) .NotStuck ⊤ 3 0
      (fun _ => iprop(⌜True⌝)) _ rfl (fun _ _ _ _ _ hs => by rcases no_bs hs with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1))
    exact (wand_intro (sep_elim_left.trans (wp0T x))).trans (later_intro)
  exact ns3 (A.adequate_not_stuck [3] () 3 rfl .refl (by simp))

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork'` idx 16: necessary (ectx toy language, stuck e₁ = 3 (Hpure vacuous), e₂ = 0 with Φ = True: the premise holds, WP 3 {{True}} contradicts adequacy (not stuck))
theorem w7c1_q9 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork' 16 := fun h => by
  have A := adeqT (Expr := Nat) .NotStuck 3 () (fun _ => True) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) .NotStuck ⊤ 3 0
      (fun _ => iprop(⌜True⌝)) _ rfl (fun _ _ _ _ _ hs => by rcases no_bs hs with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1))
    exact (wand_intro (sep_elim_left.trans (wp0T x))).trans (later_intro)
  exact ns3 (A.adequate_not_stuck [3] () 3 rfl .refl (by simp))

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

theorem pure1 : ∀ (σ₁ : Unit) (obs : List Unit) (e₂' : Nat) (σ₂ : Unit) (eₜ' : List Nat),
    BaseStep.baseStep ((1 : Nat), σ₁) obs (e₂', σ₂, eₜ') → obs = [] ∧ σ₂ = σ₁ ∧ e₂' = 1 ∧ eₜ' = [] := by
  intro σ obs e' σ' eₜ hs
  change eBS _ _ _ at hs
  obtain ⟨h1, h2, ⟨h3, _⟩ | ⟨_, h4⟩⟩ := hs
  · simp at h3
  · exact ⟨h1, rfl, h4, h2⟩

/-- The diverging program 1 (base step 1 → 1) has WP {{False}}, by Löb and the library lifting lemma. -/
theorem wp1F (x : InvGS_gen .hasNoLC CGF) :
    (letI := igT x Nat; ⊢ (WP (1 : Nat) @ Stuckness.NotStuck ; ⊤ {{ fun _ => (iprop(⌜False⌝) : IProp CGF) }} : IProp CGF)) := by
  letI := igT x Nat
  exact true_intro.trans (loeb_weak ((later_mono (wand_intro sep_elim_left)).trans
    ((priv% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork')
      (Ectx := EC) (e₁ := (1 : Nat)) (e₂ := (1 : Nat)) rfl (fun _ => ⟨_, _, _, _, bs1⟩) pure1)))

theorem wp0F (x : InvGS_gen .hasNoLC CGF) :
    (letI := igT x (Fin 3); ⊢ (WP (0 : Fin 3) @ Stuckness.NotStuck ; ⊤ {{ fun _ => (iprop(⌜True⌝) : IProp CGF) }} : IProp CGF)) := by
  letI := igT x (Fin 3)
  refine Entails.trans ?_ (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => (iprop(⌜True⌝) : IProp CGF)) (v := ())).2
  iintro _
  imodintro
  ipureintro
  trivial

-- `Iris.BindAbstractWP.wp_bind` idx 14: necessary (iris WP, threaded toy language, K = const 0 (not a context), e = 1 stuck: WP 0 holds, so WP 1 would hold, contradicting adequacy)
theorem w7c1_32 : ¬ drop0% Iris.BindAbstractWP.wp_bind 14 := fun h => by
  have A := adeqT (Expr := Fin 3) .NotStuck 1 () (fun _ => True) fun x => by
    letI := igT x (Fin 3)
    exact (wp0F x).trans ((@h (Fin 3) Unit Unit Unit _ CGF .hasNoLC (igT x (Fin 3))
      (Wp.wp (PROP := IProp CGF) Stuckness.NotStuck) _ (fun _ => 0) ⊤ 1 (fun _ => iprop(⌜True⌝))).2.trans
      (wp_mono fun _ => pure_intro trivial))
  exact tl_notStuck1 (A.adequate_not_stuck [1] () 1 rfl .refl (by simp))

-- `Rocq.wp_lift_pure_det_base_step_no_fork` idx 18: necessary (ectx toy language, e₁ = 2 (base step to 0), e₂ = 1 diverging so WP 1 {{False}} holds by Löb; WP 2 {{False}} contradicts adequacy)
theorem w7c1_q21 : ¬ drop0% Rocq.wp_lift_pure_det_base_step_no_fork 18 := fun h => by
  have A := adeqT (Expr := Nat) .NotStuck 2 () (fun _ => False) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) .NotStuck ⊤ 2 1
      (fun _ => iprop(⌜False⌝)) _ ⊤ rfl (fun _ => ⟨_, _, _, _, bs2⟩))
    exact (wand_intro (sep_elim_left.trans (wp1F x))).trans (later_intro.trans (step_fupd_intro Std.LawfulSet.subset_refl))
  exact A.adequate_result [] () () st20

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork` idx 18: necessary (ectx toy language, e₁ = 2 (base step to 0), e₂ = 1 diverging so WP 1 {{False}} holds by Löb; WP 2 {{False}} contradicts adequacy)
theorem w7c1_q22 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork 18 := fun h => by
  have A := adeqT (Expr := Nat) .NotStuck 2 () (fun _ => False) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) .NotStuck ⊤ 2 1
      (fun _ => iprop(⌜False⌝)) _ ⊤ rfl (fun _ => ⟨_, _, _, _, bs2⟩))
    exact (wand_intro (sep_elim_left.trans (wp1F x))).trans (later_intro.trans (step_fupd_intro Std.LawfulSet.subset_refl))
  exact A.adequate_result [] () () st20

-- `Rocq.wp_lift_pure_det_base_step_no_fork'` idx 17: necessary (ectx toy language, e₁ = 2 (base step to 0), e₂ = 1 diverging so WP 1 {{False}} holds by Löb; WP 2 {{False}} contradicts adequacy)
theorem w7c1_q23 : ¬ drop0% Rocq.wp_lift_pure_det_base_step_no_fork' 17 := fun h => by
  have A := adeqT (Expr := Nat) .NotStuck 2 () (fun _ => False) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) .NotStuck ⊤ 2 1
      (fun _ => iprop(⌜False⌝)) _ rfl (fun _ => ⟨_, _, _, _, bs2⟩))
    exact (wand_intro (sep_elim_left.trans (wp1F x))).trans (later_intro)
  exact A.adequate_result [] () () st20

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork'` idx 17: necessary (ectx toy language, e₁ = 2 (base step to 0), e₂ = 1 diverging so WP 1 {{False}} holds by Löb; WP 2 {{False}} contradicts adequacy)
theorem w7c1_q24 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork' 17 := fun h => by
  have A := adeqT (Expr := Nat) .NotStuck 2 () (fun _ => False) fun x => by
    letI := igT x Nat
    refine Entails.trans ?_ (@h .hasNoLC Nat EC Unit Unit Unit _ CGF (igT x Nat) .NotStuck ⊤ 2 1
      (fun _ => iprop(⌜False⌝)) _ rfl (fun _ => ⟨_, _, _, _, bs2⟩))
    exact (wand_intro (sep_elim_left.trans (wp1F x))).trans (later_intro)
  exact A.adequate_result [] () () st20

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

-- `Iris.ProgramLogic.wp_strong_adequacy_gen` idx 17: necessary (zero steps, φ = False)
theorem w7c1_43 : ¬ drop0% Iris.ProgramLogic.wp_strong_adequacy_gen 17 := fun h =>
  @h .hasNoLC (Fin 3) Unit Unit Unit _ CGF _ .NotStuck [0] () 0 [] [0] () False (fun _ => 0) (.refl _)

-- `Iris.ProgramLogic.wp_invariance_gen` idx 14: necessary (zero steps, φ = False)
theorem w7c1_67 : ¬ drop0% Iris.ProgramLogic.wp_invariance_gen 14 := fun h =>
  @h .hasNoLC (Fin 3) Unit Unit Unit _ CGF _ .NotStuck 0 () () [0] False .refl

-- `Iris.ProgramLogic.wp_invariance_gen` idx 15: necessary (stateI σ κs n := ⌜n = 0⌝, value e₁ = 0, unreachable pool t₂ = [0,0,0] makes the final state interpretation false; φ = False)
theorem w7c1_68 : ¬ drop0% Iris.ProgramLogic.wp_invariance_gen 15 := fun h =>
  @h .hasNoLC (Fin 3) Unit Unit Unit _ CGF _ .NotStuck 0 () () [0, 0, 0] False (by
    intro x κs
    letI : IrisGS_gen .hasNoLC (Fin 3) CGF :=
      .mk (toStateInterp := ⟨fun _ _ _ n => iprop(⌜n = 0⌝)⟩) (fun _ => 0) (fun _ => iprop(True))
        (fun _ _ _ _ => fupd_intro)
    iapply fupd_intro
    iexists (fun _ _ n => iprop(⌜n = 0⌝)), (fun _ => iprop(True))
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply (wp_value_fupd' (s := .NotStuck) (E := ⊤) (Φ := fun _ => (iprop(True) : IProp CGF)) (v := ())).2
      imodintro
      itrivial
    · iintro %hn
      exact absurd hn (by decide))

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

-- `Iris.ProgramLogic.wp_strong_adequacy_gen` idx 18: necessary (stateI σ ns κs nt := ⌜nt = 0⌝, es = [0] a value, unreachable pool t₂ = [0,0] leaves one forked thread so the final state interpretation is false; φ = False)
theorem w7c1_44 : ¬ drop0% Iris.ProgramLogic.wp_strong_adequacy_gen 18 := fun h =>
  @h .hasNoLC (Fin 3) Unit Unit Unit _ CGF _ .MaybeStuck [0] () 0 [] [0, 0] () False (fun _ => 0) (by
    intro x
    letI : IrisGS_gen .hasNoLC (Fin 3) CGF :=
      { stateInterp := fun _ _ _ nt => iprop(⌜nt = 0⌝), invGS := x, numLatersPerStep := fun _ => 0,
        forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }
    iapply fupd_intro
    iexists (fun _ _ _ nt => iprop(⌜nt = 0⌝)), [fun _ => iprop(True)], (fun _ => iprop(True)),
      (fun _ _ _ _ => fupd_intro)
    dsimp only
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply BigSepL2.bigSepL2_singleton.2
      iapply (wp_value_fupd' (s := .MaybeStuck) (E := ⊤) (Φ := fun _ => (iprop(True) : IProp CGF)) (v := ())).2
      imodintro
      itrivial
    · iintro %es' %t2' %Heq %Hlen _ %hn
      have := congrArg List.length Heq
      simp at this Hlen
      omega)

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- The ectx toy language with an empty state type and no base steps. -/
@[reducible] def eLE : EctxItemLanguage Nat Unit Empty Unit Unit where
  toVal := eTV
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases he : e = 0 <;> simp_all [eTV]
  toVal_coe := fun _ => rfl
  baseStep := fun _ _ _ => False
  fillItem := fun _ e => 2 * e + 2
  fillItem_inj := by intro _ a b h; have : 2 * a + 2 = 2 * b + 2 := h; omega
  fillItem_val := by intro e _ h; simp [eTV] at h
  fillItem_no_val_inj := by intros; rfl
  val_stuck := fun h => h.elim
  base_ctx_step_val := fun h => h.elim

@[reducible] def eLEc : EctxLanguage Nat (List Unit) Empty Unit Unit := EctxItemLanguage.instEctxLanguage (Λ := eLE)

theorem sub0E : @EctxLanguage.SubredexesAreValues Nat Unit Empty Unit (List Unit) eLEc (0:Nat) :=
  @EctxItemLanguage.subredexes_are_values Nat Unit Empty Unit Unit eLE 0 (fun _ e' h => by
    change 0 = 2 * e' + 2 at h; omega)

-- `Rocq.wp_lift_pure_base_stuck` idx 12: necessary (ectx toy language with empty state type: ∀ σ, Stuck holds vacuously for the value e = 0; WP 0 ?{{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_q41 : ¬ drop0% Rocq.wp_lift_pure_base_stuck 12 := fun h => soundX fun x => by
  letI L : Language Nat Empty Unit Unit := @EctxLanguage.instLanguage Nat Unit Empty Unit (List Unit) eLEc
  letI ι := @igF Nat Empty Unit Unit (@EctxLanguage.instLanguage Nat Unit Empty Unit (List Unit) eLEc) x
  exact (@h .hasNoLC Nat (List Unit) Empty Unit Unit eLEc CGF ι ⊤ 0 (fun _ => iprop(⌜False⌝)) sub0E
    (fun σ => σ.elim)).trans (wp_value_fupd' (s := .MaybeStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1

-- `_private.Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_base_stuck` idx 12: necessary (ectx toy language with empty state type: ∀ σ, Stuck holds vacuously for the value e = 0; WP 0 ?{{False}} is |={⊤}=> False; fupd soundness)
theorem w7c1_q42 : ¬ drop0% _private.Iris.ProgramLogic.EctxLifting.«0».Iris.ProgramLogic.wp_lift_pure_base_stuck 12 := fun h => soundX fun x => by
  letI L : Language Nat Empty Unit Unit := @EctxLanguage.instLanguage Nat Unit Empty Unit (List Unit) eLEc
  letI ι := @igF Nat Empty Unit Unit (@EctxLanguage.instLanguage Nat Unit Empty Unit (List Unit) eLEc) x
  exact (@h .hasNoLC Nat (List Unit) Empty Unit Unit eLEc CGF ι ⊤ 0 (fun _ => iprop(⌜False⌝)) sub0E
    (fun σ => σ.elim)).trans (wp_value_fupd' (s := .MaybeStuck) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1

end W7c1

namespace W7c1
open Iris Iris.BI Iris.ProgramLogic Iris.Std

-- `Iris.inv_open_maybe_ectxlang_inv` idx 10: necessary (wp E e Φ := ⌜e = 2⌝, e = 6 = fill [()] 2, P = True with an allocated invariant: the premise holds, ⌜6 = 2⌝ fails; fupd soundness)
theorem w7c1_36 : ¬ drop0% Iris.inv_open_maybe_ectxlang_inv 10 := fun h => soundIG (Expr := Nat) fun ι => by
  have H := @h Nat Unit Unit Unit EC _ CGF .hasNoLC ι (fun _ e _ => iprop(⌜e = 2⌝)) 6 ⊤ nroot iprop(True)
    (fun _ => iprop(True)) CoPset.subseteq_top ⟨(), _, _, _, _, BaseStep.ContextStep.ofBaseStep (Ectx := EC) [()] bs2⟩
  istart
  icases inv_alloc nroot ⊤ iprop(True) $$ [] with >#Hinv
  · itrivial
  imodintro
  iapply (H.trans (pure_mono (fun e => absurd e (by decide))))
  isplitr
  · iexact Hinv
  · iintro _
    imodintro
    ileft
    iexists ([()] : EC), (2:Nat)
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact at2
    isplitr
    · ipureintro; exact ⟨(), _, _, _, _, bs2⟩
    · ipureintro; rfl

end W7c1
