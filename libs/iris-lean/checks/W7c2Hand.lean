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

namespace W7c2
open Iris Iris.ProgramLogic

/-- Bool language: `true` is the only value; `false` steps to `false` with any observations and forks. -/
def bLang : Language Bool Unit Unit Unit where
  primStep := fun c _ r => c.1 = false ∧ r.1 = false
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by intro e σ obs e' σ' eₜ h; simp_all

/-- Context `K = const false` for `bLang`. -/
def bCtx : @Language.Context Bool Unit Unit Unit bLang (fun _ => false) := by
  refine @Language.Context.mk Bool Unit Unit Unit bLang (fun _ => false) ?_ ?_ ?_
  · intro e _; rfl
  · intro e σ obs e' σ' eₜ h; exact ⟨rfl, rfl⟩
  · intro e σ obs Ke σ' eₜ he h
    cases e
    · exact ⟨false, h.2, ⟨rfl, rfl⟩⟩
    · cases he

/-- Bool language without steps; `true` is the value. -/
def nLang : Language Bool Unit Unit Unit where
  primStep := fun _ _ _ => False
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by intro e σ obs e' σ' eₜ h; exact h.elim

def toValN (e : Nat) : Option Unit := if e = 0 then some () else none

/-- Nat language: `0` is the only value, `1` steps purely to `0`, everything else is stuck. -/
def cL : Language Nat Unit Unit Unit where
  primStep := fun c o r => c.1 = 1 ∧ o = [] ∧ r.1 = 0 ∧ r.2.2 = []
  toVal := toValN
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases he : e = 0 <;> simp_all [toValN]
  toVal_coe := fun _ => rfl
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    obtain ⟨h1, -⟩ := h
    simp only at h1
    subst h1
    rfl

def fillN (k : Bool) (e : Nat) : Nat := if k then (if e = 1 then 1 else 2 * e) else 2 * e + 1

theorem fillN_inj (k : Bool) : Function.Injective (fillN k) := by
  intro a b h; cases k
  · simp [fillN] at h; omega
  · by_cases ha : a = 1 <;> by_cases hb : b = 1 <;> simp [fillN, ha, hb] at h <;> omega

theorem fillN_val (e : Nat) (k : Bool) : (toValN (fillN k e)).isSome → (toValN e).isSome := by
  intro h
  by_cases he : e = 0
  · simp [toValN, he]
  · exfalso; cases k
    · simp [toValN, fillN] at h
    · by_cases h1 : e = 1 <;> simp [toValN, fillN, h1] at h <;> omega

theorem fillN_nvi (e₁ e₂ : Nat) (k₁ k₂ : Bool) (h1 : toValN e₁ = none) (h2 : toValN e₂ = none)
    (h : fillN k₁ e₁ = fillN k₂ e₂) : k₁ = k₂ := by
  simp [toValN] at h1 h2
  cases k₁ <;> cases k₂ <;> simp only [fillN] at h <;> simp at h ⊢
  · by_cases hb : e₂ = 1 <;> simp [hb] at h <;> omega
  · by_cases ha : e₁ = 1 <;> simp [ha] at h <;> omega

/-- Ectx-item language on Nat with two items (fill false e = 2e+1, fill true: 1 ↦ 1, e ↦ 2e), no base steps. -/
def iLang : EctxItemLanguage Nat Bool Unit Unit Unit where
  toVal := toValN
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases he : e = 0 <;> simp_all [toValN]
  toVal_coe := fun _ => rfl
  baseStep := fun _ _ _ => False
  fillItem := fillN
  fillItem_inj := fun {Ki} => fillN_inj Ki
  fillItem_val := fillN_val
  fillItem_no_val_inj := fun k₁ k₂ h1 h2 h => fillN_nvi _ _ k₁ k₂ h1 h2 h
  val_stuck := by intro e σ obs e' σ' eₜ h; exact h.elim
  base_ctx_step_val := by intro Ki e σ obs e' σ' eₜ h; exact h.elim

/-- Ectx-item language on Nat with no items; base step 1 ↦ 0. -/
def eLang : EctxItemLanguage Nat Empty Unit Unit Unit where
  toVal := toValN
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases he : e = 0 <;> simp_all [toValN]
  toVal_coe := fun _ => rfl
  baseStep := fun c _ r => c.1 = 1 ∧ r.1 = 0
  fillItem := fun k _ => k.elim
  fillItem_inj := fun {Ki} => Ki.elim
  fillItem_val := fun _ k => k.elim
  fillItem_no_val_inj := fun k => k.elim
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    obtain ⟨h1, -⟩ := h
    simp only at h1
    subst h1
    rfl
  base_ctx_step_val := fun {Ki} => Ki.elim

theorem step_nil {Expr State Obs Val : Type} [Language Expr State Obs Val] {σ : State} {o ρ}
    (hs : Language.Step (([] : List Expr), σ) o ρ) : False := by
  generalize hb : (([] : List Expr), σ) = b at hs
  cases hs with
  | atomic H t₁ t₂ =>
    have := congrArg Prod.fst hb
    simp at this

theorem n_step {ρ o ρ'} (hs : @Language.Step Bool Unit Unit Unit nLang ρ o ρ') : False := by
  cases hs with
  | atomic H => exact H

theorem rtg_nil {Expr State Obs Val : Type} [Language Expr State Obs Val] {σ : State} {C}
    (h : FromMathlib.Relation.ReflTransGen Language.ErasedStep (([] : List Expr), σ) C) :
    C = ([], σ) := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; obtain ⟨_, hs⟩ := hs; exact (step_nil hs).elim

theorem n_rtg {C C'} (h : FromMathlib.Relation.ReflTransGen (@Language.ErasedStep Bool Unit Unit Unit nLang) C C') :
    C = C' := by
  induction h with
  | refl => rfl
  | tail _ hs ih => obtain ⟨_, hs⟩ := hs; exact (n_step hs).elim

theorem tg_head {α} {R : α → α → Prop} {a b} (h : Relation.TransGen R a b) : ∃ c, R a c := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

theorem iter0 {α} {R : α → α → Prop} {x y} (h : Relation.Iterate R 0 x y) : x = y := by
  cases h; rfl

theorem iter1 {α} {R : α → α → Prop} {x y} (h : Relation.Iterate R 1 x y) : R x y := by
  cases h with
  | tail z h0 hr => cases h0; exact hr

theorem rtg_stuck {α} {R : α → α → Prop} {x y} (hx : ∀ z, ¬ R x z)
    (h : FromMathlib.Relation.ReflTransGen R x y) : x = y := by
  induction h with
  | refl => rfl
  | tail _ hr ih => subst ih; exact (hx _ hr).elim

section
attribute [local instance] cL
theorem cl_pure : @Language.PurePrimStep Nat Unit Unit Unit cL 1 0 :=
  ⟨fun _ => ⟨0, (), [], rfl, rfl, rfl, rfl⟩, fun h => ⟨h.2.1, rfl, h.2.2.1.symm, h.2.2.2⟩⟩

theorem cl_iter1 : Relation.Iterate (@Language.PurePrimStep Nat Unit Unit Unit cL) 1 1 0 :=
  .tail 1 (.rfl 1) cl_pure

theorem cl_nopure (e y : Nat) (he : e ≠ 1) : ¬ @Language.PurePrimStep Nat Unit Unit Unit cL e y :=
  fun hp => by obtain ⟨_, _, _, H⟩ := hp.safe (); exact he H.1

theorem cl_irr5 : PrimStep.Irreducible (Expr := Nat) (State := Unit) (Obs := List Unit) (5, ()) :=
  fun _ _ _ _ H => absurd H.1 (by decide)

theorem cl_not_ns5 : ¬ PrimStep.NotStuck (Expr := Nat) (State := Unit) (5, ()) := by
  rintro (h | ⟨_, _, _, _, H⟩)
  · exact absurd h (by decide)
  · exact absurd H.1 (by decide)


theorem cl_ps5 {σ κ e₂ σ₂ efs} (h : @PrimSteps Nat Unit Unit Unit cL 5 σ κ e₂ σ₂ efs) : False := by
  cases h with
  | once H => exact absurd H.1 (by simp)
  | next H _ => exact absurd H.1 (by simp)
end

section
attribute [local instance] bLang
theorem b_irr_true : PrimStep.Irreducible (Expr := Bool) (State := Unit) (Obs := List Unit) (true, ()) :=
  fun _ _ _ _ H => absurd H.1 (by decide)

/-- The empty pool is safe in `bLang`. -/
theorem nil_safe (f : Forking) : @cfgSafeForking Bool Unit Unit Unit bLang ([], ()) f := by
  intro C₂ hr
  obtain rfl := rtg_nil hr
  exact ⟨fun {e} he => by simp at he, fun _ e he => by simp at he⟩
end

theorem nsteps_zero {Expr State Obs Val : Type} [Language Expr State Obs Val] {n ρ κ ρ'}
    (h : Language.NSteps (Expr := Expr) (State := State) (Obs := Obs) n ρ κ ρ') (hn : n = 0) : ρ = ρ' := by
  cases h with
  | refl => rfl
  | cons => simp at hn

theorem nsteps_nil {Expr State Obs Val : Type} [Language Expr State Obs Val] {σ : State} {n κ ρ}
    (h : Language.NSteps n (([] : List Expr), σ) κ ρ) (hn : n ≠ 0) : False := by
  cases h with
  | refl => exact hn rfl
  | cons s _ => exact step_nil s

theorem n_nsteps {n ρ₁ κ ρ₂} (hs : @Language.NSteps Bool Unit Unit Unit nLang n ρ₁ κ ρ₂) (hn : n ≠ 0) : False := by
  cases hs with
  | refl => exact hn rfl
  | cons s _ => exact n_step s


theorem n_ps {e σ κ e₂ σ₂ efs} (h : @PrimSteps Bool Unit Unit Unit nLang e σ κ e₂ σ₂ efs) : False := by
  cases h with
  | once H => exact H
  | next H _ => exact H

section
attribute [local instance] nLang
/-- In `nLang`, `[true]` is safe for every forking mode. -/
theorem n_safe (f : Forking) : @cfgSafeForking Bool Unit Unit Unit nLang ([true], ()) f := by
  intro C₂ hr
  obtain rfl := (n_rtg hr).symm
  refine ⟨fun {e} he => ?_, fun _ e _ _ _ _ _ H => H.elim⟩
  simp at he; subst he; exact .inl rfl
end

end W7c2

namespace W7c2
open Iris Iris.BI Iris.ProgramLogic COFE Auth HeapView Std.LawfulSet

/-- Ectx-item language on Nat with no items and Bool state: 0 value; base steps 1 ↦ 0 (pure), 2 ↦ 0 (flips the state), 4 ↦ 5; everything else stuck. -/
def seL : EctxItemLanguage Nat Empty Bool Unit Unit where
  toVal := toValN
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases he : e = 0 <;> simp_all [toValN]
  toVal_coe := fun _ => rfl
  baseStep := fun c o r => o = [] ∧ r.2.2 = [] ∧
    ((c.1 = 1 ∧ r.1 = 0 ∧ r.2.1 = c.2) ∨ (c.1 = 2 ∧ r.1 = 0 ∧ r.2.1 = !c.2) ∨ (c.1 = 4 ∧ r.1 = 5 ∧ r.2.1 = c.2))
  fillItem := fun k _ => k.elim
  fillItem_inj := fun {Ki} => Ki.elim
  fillItem_val := fun _ k => k.elim
  fillItem_no_val_inj := fun k => k.elim
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    obtain ⟨-, -, h⟩ := h
    simp only at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  base_ctx_step_val := fun {Ki} => Ki.elim

/-- Ghost state with the invariant slots of the closed-proofs GF and an `ownP` slot for Bool states. -/
noncomputable def PGF : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF⟩
  | 1  => ⟨constOF CoPsetDisjL⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3  => ⟨AuthURF (constOF Credit)⟩
  | 4  => ⟨ownPRF Bool⟩
  | _  => ⟨constOF Unit⟩

instance pgfPre : OwnPGpreS Bool PGF where
  toWsatGpreS := { inv := { τ := 0, transp := by unfold PGF; rfl },
                   enabled := { τ := 1, transp := by unfold PGF; rfl },
                   disabled := { τ := 2, transp := by unfold PGF; rfl } }
  toLcGpreS := { lc_elem := { τ := 3, transp := by unfold PGF; rfl } }
  inG := { τ := 4, transp := by unfold PGF; rfl }

section
attribute [local instance] seL

theorem se_sub (e : Nat) : EctxLanguage.SubredexesAreValues (Ectx := List Empty) e := by
  intro K e' _ _
  cases K with
  | nil => rfl
  | cons k _ => exact k.elim

theorem se_prim {e σ obs r} : PrimStep.primStep (Expr := Nat) (State := Bool) (e, σ) obs r ↔
    BaseStep.baseStep (Expr := Nat) (e, σ) obs r := by
  obtain ⟨e', σ', eₜ⟩ := r
  exact EctxLanguage.baseStep_iff_primStep_of_subredexesAreValues (se_sub e)

/-- The adequacy-theorem instance of `IrisGS_gen` (state interpretation and fork post `True`). -/
noncomputable abbrev iS (x : InvGS_gen .hasNoLC PGF) : IrisGS_gen .hasNoLC Nat PGF :=
  .mk (toStateInterp := ⟨fun _ _ _ _ => iprop(True)⟩) (fun _ => 0) (fun _ => iprop(True)) (fun _ _ _ _ => fupd_intro)

theorem lift_adeq {s : Stuckness} {e : Nat} {σ : Bool} {φ : Unit → Prop}
    (H : ∀ x : InvGS_gen .hasNoLC PGF, letI := iS x; ⊢ (WP e @ s ; ⊤ {{ v, ⌜φ v⌝ }} : IProp PGF)) :
    adequate s e σ (fun v _ => φ v) :=
  wp_adequacy_gen (hlc := .hasNoLC) (GF := PGF) s e σ φ fun {x} κs => by
    refine .trans ?_ fupd_intro
    refine .trans ?_ (exists_intro (fun _ _ => iprop(True)))
    refine .trans ?_ (exists_intro (fun _ => iprop(True)))
    exact emp_sep.2.trans (sep_mono true_intro (H x))

theorem se_b5 {σ obs e' σ' eₜ} : ¬ BaseStep.baseStep (Expr := Nat) (State := Bool) (5, σ) obs (e', σ', eₜ) := by
  intro h; obtain ⟨-, -, h⟩ := h; simp at h

theorem se_bflip {σ obs e' eₜ} : ¬ BaseStep.baseStep (Expr := Nat) (State := Bool) (2, σ) obs (e', σ, eₜ) := by
  intro h; obtain ⟨-, -, h⟩ := h; simp at h

theorem se_val0 {σ obs e' σ' eₜ} : ¬ PrimStep.primStep (Expr := Nat) (State := Bool) (0, σ) obs (e', σ', eₜ) :=
  fun h => absurd (Language.val_stuck h) (by decide)

theorem se_stuck5 (σ : Bool) : PrimStep.Stuck (Expr := Nat) (State := Bool) (5, σ) :=
  ⟨rfl, fun _ _ _ _ h => se_b5 (se_prim.1 h)⟩

theorem se_flip {σ obs e' eₜ} : ¬ PrimStep.primStep (Expr := Nat) (State := Bool) (2, σ) obs (e', σ, eₜ) :=
  fun h => se_bflip (se_prim.1 h)

theorem se_red4 (σ : Bool) : PrimStep.Reducible (Expr := Nat) (State := Bool) (4, σ) :=
  ⟨[], 5, σ, [], se_prim.2 ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩⟩

theorem se_bred4 (σ : Bool) : BaseStep.Reducible (Expr := Nat) (State := Bool) (4, σ) :=
  ⟨[], 5, σ, [], ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩⟩

theorem se_bred2 (σ : Bool) : BaseStep.Reducible (Expr := Nat) (State := Bool) (2, σ) :=
  ⟨[], 0, !σ, [], ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩⟩

/-- From 4 the pool reaches the stuck [5]: not adequate for NotStuck. -/
theorem se_ad4 {φ} (A : adequate (Expr := Nat) .NotStuck 4 false φ) : False :=
  Language.not_not_suck.2 (se_stuck5 false)
    (A.adequate_not_stuck [5] false 5 rfl
      (.tail .refl ⟨[], Language.Step.of_primStep (t₁ := []) (t₂ := []) (eₜ := [])
        (se_prim.2 ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩)⟩) (by simp))

theorem se_ad5 {φ} (A : adequate (Expr := Nat) .NotStuck 5 false φ) : False :=
  Language.not_not_suck.2 (se_stuck5 false) (A.adequate_not_stuck [5] false 5 rfl .refl (by simp))

/-- From 2 the value 0 is reached (state flipped). -/
theorem se_ad2 {s} (A : adequate (Expr := Nat) (State := Bool) s 2 false (fun _ _ => False)) : False :=
  A.adequate_result [] true ()
    (.tail .refl ⟨[], Language.Step.of_primStep (t₁ := []) (t₂ := []) (eₜ := [])
      (se_prim.2 ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩)⟩)

theorem se_ad1 {s} (A : adequate (Expr := Nat) (State := Bool) s 1 false (fun _ _ => False)) : False :=
  A.adequate_result [] false ()
    (.tail .refl ⟨[], Language.Step.of_primStep (t₁ := []) (t₂ := []) (eₜ := [])
      (se_prim.2 ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩)⟩)

theorem se_ad0 {s} (A : adequate (Expr := Nat) (State := Bool) s 0 false (fun _ _ => False)) : False :=
  A.adequate_result [] false () .refl

/-- State interpretation `False`: every lifting premise over `stateInterp` holds. -/
noncomputable abbrev iF (x : InvGS_gen .hasNoLC PGF) : IrisGS_gen .hasNoLC Nat PGF :=
  .mk (toStateInterp := ⟨fun _ _ _ _ => iprop(False)⟩) (fun _ => 0) (fun _ => iprop(True)) (fun _ _ _ _ => fupd_intro)

theorem val_false {s : Stuckness}
    (H : ∀ x : InvGS_gen .hasNoLC PGF, letI := iF x; ⊢ (WP (0 : Nat) @ s ; ⊤ {{ v, ⌜False⌝ }} : IProp PGF)) : False :=
  pure_soundness (PROP := IProp PGF) (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun x =>
    letI := iF x
    wand_intro (sep_elim_left.trans ((H x).trans
      (wp_value_fupd' (Expr := Nat) (s := s) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝)) (v := ())).1)))

theorem own_adeq {s : Stuckness} {e : Nat} {σ : Bool} {φ : Unit → Prop}
    (H : ∀ ι : OwnPGS Bool PGF, ownP (GF := PGF) σ ⊢ (WP e @ s ; ⊤ {{ v, ⌜φ v⌝ }} : IProp PGF)) :
    adequate s e σ (fun v _ => φ v) :=
  ownP_adequacy (GF := PGF) s e σ φ (by intro ι; exact H ι)
end

end W7c2

open Iris Iris.ProgramLogic W7c2
-- `Iris.ProgramLogic.EctxItemLanguage.fillItem_val` idx 8: necessary (iLang: e = 1 is not a value)
theorem w7c2_0 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.fillItem_val 8 := fun h =>
  absurd (@h Nat Bool Unit Unit Unit iLang 1 true) (by decide)

-- `Iris.ProgramLogic.EctxItemLanguage.fillItem_no_val_inj` idx 10: necessary (iLang: fill false 0 = 1 = fill true 1, e1 = 0 a value)
theorem w7c2_1 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.fillItem_no_val_inj 10 := fun h =>
  absurd (@h Nat Bool Unit Unit Unit iLang 0 1 false true (by decide) (by decide)) (by decide)

-- `Iris.ProgramLogic.EctxItemLanguage.fillItem_no_val_inj` idx 12: necessary (iLang: items true, false on e1 = e2 = 1)
theorem w7c2_2 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.fillItem_no_val_inj 12 := fun h =>
  absurd (@h Nat Bool Unit Unit Unit iLang 1 1 true false (by decide) (by decide)) (by decide)

-- `Iris.ProgramLogic.EctxItemLanguage.val_stuck` idx 12: necessary (iLang: e = 0 is a value)
theorem w7c2_3 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.val_stuck 12 := fun h =>
  absurd (@h Nat Bool Unit Unit Unit iLang 0 () [] 0 () []) (by decide)

-- `Iris.ProgramLogic.EctxItemLanguage.base_ctx_step_val` idx 13: necessary (iLang: e = 1 is not a value)
theorem w7c2_4 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.base_ctx_step_val 13 := fun h =>
  absurd (@h Nat Bool Unit Unit Unit iLang true 1 () [] 0 () []) (by decide)

-- `Iris.ProgramLogic.EctxItemLanguage.fill_val` idx 8: necessary (iLang: K = [], e = 1)
theorem w7c2_5 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.fill_val 8 := fun h =>
  absurd (@h Nat Unit Unit Unit Bool iLang [] 1) (by decide)

-- `Iris.ProgramLogic.EctxItemLanguage.baseStep_fill_eq_val_absurd` idx 14: necessary (iLang: K = [], e = 0 = ofVal ())
theorem w7c2_6 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.baseStep_fill_eq_val_absurd 14 := fun h =>
  @h Nat Unit Unit Unit Bool iLang [] 0 0 () () [] [] () rfl

-- `Iris.ProgramLogic.EctxItemLanguage.baseStep_fill_eq_val_absurd` idx 15: necessary (eLang: base step 1 to 0)
theorem w7c2_7 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.baseStep_fill_eq_val_absurd 15 := fun h =>
  @h Nat Unit Unit Unit Empty eLang [] 1 0 () () [] [] () ⟨rfl, rfl⟩

-- `Iris.ProgramLogic.EctxItemLanguage.fill_not_val` idx 8: necessary (iLang: K = [], e = 0 a value)
theorem w7c2_8 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.fill_not_val 8 := fun h =>
  absurd (@h Nat Unit Unit Unit Bool iLang [] 0) (by decide)

-- `Iris.ProgramLogic.EctxItemLanguage.subredexes_are_values` idx 7: necessary (iLang: 4 = fill [true] 2, 2 not a value)
theorem w7c2_9 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.subredexes_are_values 7 := fun h => by
  have H := @h Nat Unit Unit Unit Bool iLang 4
  unfold EctxLanguage.SubredexesAreValues at H
  have H2 := @H [true] 2 (by decide) (by decide)
  nomatch H2

-- `Iris.ProgramLogic.ToVal.coe_of_toVal_eq_some` idx 5: necessary (Bool: ofVal () = true, e = false)
theorem w7c2_10 : ¬ drop0% Iris.ProgramLogic.ToVal.coe_of_toVal_eq_some 5 := fun h =>
  absurd (@h Bool Unit bLang.toToVal false ()) (by decide)

section
attribute [local instance] W7c2.bLang

-- `Iris.ProgramLogic.Language.val_stuck` idx 11: necessary (bLang: true is a value)
theorem w7c2_11 : ¬ drop0% Iris.ProgramLogic.Language.val_stuck 11 := fun h =>
  absurd (@h Bool Unit Unit Unit bLang true () [] true () []) (by decide)

-- `Iris.ProgramLogic.Language.toVal_none_of_reducible` idx 7: necessary (bLang: true is a value)
theorem w7c2_15 : ¬ drop0% Iris.ProgramLogic.Language.toVal_none_of_reducible 7 := fun h =>
  absurd (@h Bool Unit Unit Unit bLang true ()) (by decide)

-- `Iris.ProgramLogic.Language.val_irreducible` idx 6: necessary (bLang: false steps)
theorem w7c2_16 : ¬ drop0% Iris.ProgramLogic.Language.val_irreducible 6 := fun h =>
  @h Bool Unit Unit Unit bLang false () [] false () [] ⟨rfl, rfl⟩

-- `Iris.ProgramLogic.Language.Atomic.atomic` idx 7: necessary (bLang: false steps to the non-value false)
theorem w7c2_17 : ¬ drop0% Iris.ProgramLogic.Language.Atomic.atomic 7 := fun h => by
  have h2 : (@ToVal.toVal Bool Unit bLang.toToVal false).isSome = true :=
    @h Bool Unit Unit Unit bLang .StronglyAtomic false () [] false () [] ⟨rfl, rfl⟩
  exact absurd h2 (by decide)

-- `Iris.ProgramLogic.Language.Atomic.atomic` idx 13: necessary (bLang: value true is atomic, e' = false)
theorem w7c2_18 : ¬ drop0% Iris.ProgramLogic.Language.Atomic.atomic 13 := fun h => by
  have h2 : (@ToVal.toVal Bool Unit bLang.toToVal false).isSome = true :=
    @h Bool Unit Unit Unit bLang .StronglyAtomic true (Language.val_atomic (Λ := bLang) (v := ())) () [] false () []
  exact absurd h2 (by decide)

-- `Iris.ProgramLogic.Language.stronglyAtomic_atomic` idx 7: necessary (bLang: false is not atomic)
theorem w7c2_19 : ¬ drop0% Iris.ProgramLogic.Language.stronglyAtomic_atomic 7 := fun h => by
  have h2 : (@ToVal.toVal Bool Unit bLang.toToVal false).isSome = true :=
    @Language.Atomic.atomic Bool Unit Unit Unit bLang .StronglyAtomic false
      (@h Bool Unit Unit Unit bLang false .StronglyAtomic) () [] false () [] ⟨rfl, rfl⟩
  exact absurd h2 (by decide)

-- `Iris.ProgramLogic.Language.Context.toVal_eq_none_fill` idx 6: necessary (bLang, K = const true)
theorem w7c2_21 : ¬ drop0% Iris.ProgramLogic.Language.Context.toVal_eq_none_fill 6 := fun h =>
  absurd (@h Bool Unit Unit Unit bLang (fun _ => true) false rfl) (by decide)

-- `Iris.ProgramLogic.Language.Context.toVal_eq_none_fill` idx 8: necessary (bLang, K = id, e = true)
theorem w7c2_22 : ¬ drop0% Iris.ProgramLogic.Language.Context.toVal_eq_none_fill 8 := fun h =>
  absurd (@h Bool Unit Unit Unit bLang id (@Language.instContext_id Bool Unit Unit Unit bLang) true) (by decide)

-- `Iris.ProgramLogic.Language.Context.primStep_fill` idx 6: necessary (bLang, K = const true: values do not step)
theorem w7c2_23 : ¬ drop0% Iris.ProgramLogic.Language.Context.primStep_fill 6 := fun h =>
  absurd (@h Bool Unit Unit Unit bLang (fun _ => true) false () [] false () [] ⟨rfl, rfl⟩).1 (by decide)

-- `Iris.ProgramLogic.Language.Context.reducibleNoObs_fill_inv` idx 9: necessary (bLang, K = const false, e = true a value)
theorem w7c2_34 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducibleNoObs_fill_inv 9 := fun h => by
  obtain ⟨_, _, _, H⟩ := @h Bool Unit Unit Unit bLang (fun _ => false) bCtx true () ⟨false, (), [], rfl, rfl⟩
  exact absurd H.1 (by decide)

-- `Iris.ProgramLogic.Language.Context.irreducible_fill` idx 9: necessary (bLang, K = const false, e = true)
theorem w7c2_37 : ¬ drop0% Iris.ProgramLogic.Language.Context.irreducible_fill 9 := fun h =>
  @h Bool Unit Unit Unit bLang (fun _ => false) bCtx true () b_irr_true [] false () [] ⟨rfl, rfl⟩

-- `Iris.ProgramLogic.Language.Context.irreducible_fill` idx 10: necessary (bLang, K = id, e = false)
theorem w7c2_38 : ¬ drop0% Iris.ProgramLogic.Language.Context.irreducible_fill 10 := fun h =>
  @h Bool Unit Unit Unit bLang id (@Language.instContext_id Bool Unit Unit Unit bLang) false () rfl [] false () [] ⟨rfl, rfl⟩

-- `Iris.ProgramLogic.Language.Context.irreducible_fill_inv` idx 6: necessary (bLang, K = const true, e = false)
theorem w7c2_39 : ¬ drop0% Iris.ProgramLogic.Language.Context.irreducible_fill_inv 6 := fun h =>
  @h Bool Unit Unit Unit bLang (fun _ => true) false () b_irr_true [] false () [] ⟨rfl, rfl⟩

-- `Iris.ProgramLogic.Language.Context.irreducible_fill_inv` idx 9: necessary (bLang, K = id, e = false)
theorem w7c2_40 : ¬ drop0% Iris.ProgramLogic.Language.Context.irreducible_fill_inv 9 := fun h =>
  @h Bool Unit Unit Unit bLang id (@Language.instContext_id Bool Unit Unit Unit bLang) false () [] false () [] ⟨rfl, rfl⟩

-- `Iris.ProgramLogic.Language.perm_of_step` idx 11: necessary (bLang: [false] steps, the empty pool cannot)
theorem w7c2_44 : ¬ drop0% Iris.ProgramLogic.Language.perm_of_step 11 := fun h => by
  obtain ⟨_, _, hs⟩ := @h Bool Unit Unit Unit bLang [false] [] [false] [] () ()
    (Language.Step.of_primStep (Λ := bLang) (t₁ := []) (t₂ := []) (eₜ := []) ⟨rfl, rfl⟩)
  exact step_nil hs

-- `Iris.ProgramLogic.Language.perm_of_step` idx 12: necessary (empty pools do not step)
theorem w7c2_45 : ¬ drop0% Iris.ProgramLogic.Language.perm_of_step 12 := fun h => by
  obtain ⟨_, _, hs⟩ := @h Bool Unit Unit Unit bLang [] [] [] [] () () List.Perm.nil
  exact step_nil hs

-- `Iris.ProgramLogic.Language.step_update_of_getElem?` idx 13: necessary (bLang, t = [])
theorem w7c2_46 : ¬ drop0% Iris.ProgramLogic.Language.step_update_of_getElem? 13 := fun h =>
  step_nil (@h Bool Unit Unit Unit bLang false false 0 [] [] [] () () ⟨rfl, rfl⟩)

-- `Iris.ProgramLogic.Language.perm_of_erasedStep` idx 10: necessary (bLang: [false] steps, the empty pool cannot)
theorem w7c2_48 : ¬ drop0% Iris.ProgramLogic.Language.perm_of_erasedStep 10 := fun h => by
  obtain ⟨_, _, _, hs⟩ := @h Bool Unit Unit Unit bLang [false] [] [false] () ()
    ⟨[], Language.Step.of_primStep (Λ := bLang) (t₁ := []) (t₂ := []) (eₜ := []) ⟨rfl, rfl⟩⟩
  exact step_nil hs

-- `Iris.ProgramLogic.Language.perm_of_erasedStep` idx 11: necessary (empty pools do not step)
theorem w7c2_49 : ¬ drop0% Iris.ProgramLogic.Language.perm_of_erasedStep 11 := fun h => by
  obtain ⟨_, _, _, hs⟩ := @h Bool Unit Unit Unit bLang [] [] [] () () List.Perm.nil
  exact step_nil hs

-- `Iris.ProgramLogic.Language.PurePrimStep.deterministic` idx 7: necessary (bLang: false steps to false, e2 = true)
theorem w7c2_51 : ¬ drop0% Iris.ProgramLogic.Language.PurePrimStep.deterministic 7 := fun h =>
  absurd (@h Bool Unit Unit Unit bLang false true () () [] false [] ⟨rfl, rfl⟩).2.2.1 (by decide)

-- `Iris.ProgramLogic.cfg_step` idx 13: necessary (bLang, empty pool)
theorem w7c2_107 : ¬ drop0% Iris.ProgramLogic.cfg_step 13 := fun h =>
  step_nil (@h Bool Unit Unit Unit bLang [] () 0 false [] false () [] ⟨rfl, rfl⟩)

-- `Iris.ProgramLogic.cfg_stepsTc` idx 13: necessary (bLang, empty pool)
theorem w7c2_109 : ¬ drop0% Iris.ProgramLogic.cfg_stepsTc 13 := fun h => by
  obtain ⟨_, _, hs⟩ := tg_head (@h Bool Unit Unit Unit bLang [] () 0 false [] false () [] (.once ⟨rfl, rfl⟩))
  exact step_nil hs

-- `Iris.ProgramLogic.cfg_steps` idx 13: necessary (bLang, empty pool, step forking [true])
theorem w7c2_111 : ¬ drop0% Iris.ProgramLogic.cfg_steps 13 := fun h => by
  have H := rtg_nil (@h Bool Unit Unit Unit bLang [] () 0 false [] false () [true] (.once ⟨rfl, rfl⟩))
  have := congrArg Prod.fst H
  simp at this

-- `Iris.ProgramLogic.cfg_safeStep` idx 14: necessary (bLang: step of false forks [true], f = doesNotFork)
theorem w7c2_113 : ¬ drop0% Iris.ProgramLogic.cfg_safeStep 14 := fun h =>
  nomatch (@h Bool Unit Unit Unit bLang [false] () .doesNotFork 0 false [] false () [true] rfl ⟨rfl, rfl⟩).2 rfl

-- `Iris.ProgramLogic.cfg_safeStep` idx 15: necessary (bLang: empty pool is safe, step forks [true])
theorem w7c2_114 : ¬ drop0% Iris.ProgramLogic.cfg_safeStep 15 := fun h =>
  nomatch (@h Bool Unit Unit Unit bLang [] () .doesNotFork 0 false [] false () [true] (nil_safe _) ⟨rfl, rfl⟩).2 rfl

-- `Iris.ProgramLogic.cfg_safeSteps` idx 14: necessary (bLang: step of false forks [true], f = doesNotFork)
theorem w7c2_116 : ¬ drop0% Iris.ProgramLogic.cfg_safeSteps 14 := fun h =>
  nomatch (@h Bool Unit Unit Unit bLang [false] () .doesNotFork 0 false [] false () [true] rfl (.once ⟨rfl, rfl⟩)).2 rfl

-- `Iris.ProgramLogic.cfg_safeSteps` idx 15: necessary (bLang: empty pool is safe, step forks [true])
theorem w7c2_117 : ¬ drop0% Iris.ProgramLogic.cfg_safeSteps 15 := fun h =>
  nomatch (@h Bool Unit Unit Unit bLang [] () .doesNotFork 0 false [] false () [true] (nil_safe _) (.once ⟨rfl, rfl⟩)).2 rfl

-- `Iris.ProgramLogic.nSteps_right` idx 11: necessary (bLang: [false] steps, the empty pool cannot)
theorem w7c2_121 : ¬ drop0% Iris.ProgramLogic.nSteps_right 11 := fun h =>
  nsteps_nil (@h Bool Unit Unit Unit bLang 0 ([], ()) ([false], ()) ([false], ()) [] []
    (Language.Step.of_primStep (Λ := bLang) (t₁ := []) (t₂ := []) (eₜ := []) ⟨rfl, rfl⟩)) (by decide)

-- `Iris.ProgramLogic.primSteps_atomic` idx 11: necessary (bLang: false steps to the non-value false)
theorem w7c2_123 : ¬ drop0% Iris.ProgramLogic.primSteps_atomic 11 := fun h =>
  absurd (@h Bool Unit Unit Unit bLang false () [] false () [] (.once ⟨rfl, rfl⟩)).2 (by decide)

-- `Iris.ProgramLogic.primSteps_atomic` idx 12: necessary (bLang: the value true is atomic and does not step)
theorem w7c2_124 : ¬ drop0% Iris.ProgramLogic.primSteps_atomic 12 := fun h =>
  absurd (@h Bool Unit Unit Unit bLang true () [] false () []
    (Language.val_atomic (Λ := bLang) (v := ()))).1.1 (by decide)

end

section
attribute [local instance] W7c2.nLang

-- `Iris.ProgramLogic.Language.Step.of_primStep` idx 11: necessary (nLang has no steps)
theorem w7c2_12 : ¬ drop0% Iris.ProgramLogic.Language.Step.of_primStep 11 := fun h =>
  n_step (@h Bool Unit Unit Unit nLang true () [] true () [] [] [])

-- `Iris.ProgramLogic.Language.reducible_of_reducibleNoObs` idx 7: necessary (nLang has no steps)
theorem w7c2_13 : ¬ drop0% Iris.ProgramLogic.Language.reducible_of_reducibleNoObs 7 := fun h => by
  obtain ⟨_, _, _, _, H⟩ := @h Bool Unit Unit Unit nLang true ()
  exact H

-- `Iris.ProgramLogic.Language.notStuck_of_primStep` idx 11: necessary (nLang: false is stuck)
theorem w7c2_14 : ¬ drop0% Iris.ProgramLogic.Language.notStuck_of_primStep 11 := fun h => by
  rcases @h Bool Unit Unit Unit nLang false () [] false () [] with h1 | ⟨_, _, _, _, H⟩
  · exact absurd h1 (by decide)
  · exact H

-- `Iris.ProgramLogic.Language.prim_val_stuck` idx 11: necessary (conclusion False)
theorem w7c2_20 : ¬ drop0% Iris.ProgramLogic.Language.prim_val_stuck 11 := fun h =>
  @h Bool Unit Unit Unit nLang true () () () [] []

-- `Iris.ProgramLogic.Language.Context.primStep_fill` idx 13: necessary (nLang has no steps)
theorem w7c2_24 : ¬ drop0% Iris.ProgramLogic.Language.Context.primStep_fill 13 := fun h =>
  @h Bool Unit Unit Unit nLang id (@Language.instContext_id Bool Unit Unit Unit nLang) true () [] true () []

-- `Iris.ProgramLogic.Language.Context.reducible_fill` idx 9: necessary (nLang has no steps)
theorem w7c2_28 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducible_fill 9 := fun h => by
  obtain ⟨_, _, _, _, H⟩ := @h Bool Unit Unit Unit nLang id (@Language.instContext_id Bool Unit Unit Unit nLang) true ()
  exact H

-- `Iris.ProgramLogic.Language.Context.reducibleNoObs_fill` idx 9: necessary (nLang has no steps)
theorem w7c2_32 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducibleNoObs_fill 9 := fun h => by
  obtain ⟨_, _, _, H⟩ := @h Bool Unit Unit Unit nLang id (@Language.instContext_id Bool Unit Unit Unit nLang) true ()
  exact H

-- `Iris.ProgramLogic.Language.step_update_of_getElem?` idx 14: necessary (nLang has no steps)
theorem w7c2_47 : ¬ drop0% Iris.ProgramLogic.Language.step_update_of_getElem? 14 := fun h =>
  n_step (@h Bool Unit Unit Unit nLang true true 0 [] [] [true] () () rfl)

-- `Iris.ProgramLogic.Language.PurePrimStep.safe` idx 7: necessary (nLang has no steps)
theorem w7c2_50 : ¬ drop0% Iris.ProgramLogic.Language.PurePrimStep.safe 7 := fun h => by
  obtain ⟨_, _, _, H⟩ := @h Bool Unit Unit Unit nLang true true ()
  exact H

-- `Iris.ProgramLogic.Language.purePrimStep_fill` idx 9: necessary (nLang has no steps)
theorem w7c2_55 : ¬ drop0% Iris.ProgramLogic.Language.purePrimStep_fill 9 := fun h => by
  obtain ⟨_, _, _, H⟩ := (@h Bool Unit Unit Unit nLang id (@Language.instContext_id Bool Unit Unit Unit nLang) true true).safe ()
  exact H

-- `Iris.ProgramLogic.PrimSteps.fill` idx 13: necessary (nLang has no steps)
theorem w7c2_106 : ¬ drop0% Iris.ProgramLogic.PrimSteps.fill 13 := fun h =>
  n_ps (@h Bool Unit Unit Unit nLang id (@Language.instContext_id Bool Unit Unit Unit nLang) true () [] true () [])

-- `Iris.ProgramLogic.cfg_step` idx 14: necessary (nLang has no steps)
theorem w7c2_108 : ¬ drop0% Iris.ProgramLogic.cfg_step 14 := fun h =>
  n_step (@h Bool Unit Unit Unit nLang [true] () 0 true [] true () [] rfl)

-- `Iris.ProgramLogic.cfg_stepsTc` idx 14: necessary (nLang has no steps)
theorem w7c2_110 : ¬ drop0% Iris.ProgramLogic.cfg_stepsTc 14 := fun h => by
  obtain ⟨_, _, hs⟩ := tg_head (@h Bool Unit Unit Unit nLang [true] () 0 true [] true () [] rfl)
  exact n_step hs

-- `Iris.ProgramLogic.cfg_steps` idx 14: necessary (nLang has no steps, [true] to [false])
theorem w7c2_112 : ¬ drop0% Iris.ProgramLogic.cfg_steps 14 := fun h => by
  have H := n_rtg (@h Bool Unit Unit Unit nLang [true] () 0 true [] false () [] rfl)
  have := congrArg Prod.fst H
  simp at this

-- `Iris.ProgramLogic.cfg_safeStep` idx 16: necessary (nLang: [true] is safe, efs = [true], f = doesNotFork)
theorem w7c2_115 : ¬ drop0% Iris.ProgramLogic.cfg_safeStep 16 := fun h =>
  nomatch (@h Bool Unit Unit Unit nLang [true] () .doesNotFork 0 true [] true () [true] (n_safe _) rfl).2 rfl

-- `Iris.ProgramLogic.cfg_safeSteps` idx 16: necessary (nLang: [true] is safe, efs = [true], f = doesNotFork)
theorem w7c2_118 : ¬ drop0% Iris.ProgramLogic.cfg_safeSteps 16 := fun h =>
  nomatch (@h Bool Unit Unit Unit nLang [true] () .doesNotFork 0 true [] true () [true] (n_safe _) rfl).2 rfl

-- `Iris.ProgramLogic.nSteps_trans` idx 12: necessary (zero steps from [false] to [true])
theorem w7c2_119 : ¬ drop0% Iris.ProgramLogic.nSteps_trans 12 := fun h => by
  have H := nsteps_zero (@h Bool Unit Unit Unit nLang 0 0 ([false], ()) ([true], ()) ([true], ()) [] [] (.refl _)) rfl
  have := congrArg Prod.fst H
  simp at this

-- `Iris.ProgramLogic.nSteps_trans` idx 13: necessary (zero steps from [true] to [false])
theorem w7c2_120 : ¬ drop0% Iris.ProgramLogic.nSteps_trans 13 := fun h => by
  have H := nsteps_zero (@h Bool Unit Unit Unit nLang 0 0 ([true], ()) ([true], ()) ([false], ()) [] [] (.refl _)) rfl
  have := congrArg Prod.fst H
  simp at this

-- `Iris.ProgramLogic.nSteps_right` idx 12: necessary (nLang has no steps)
theorem w7c2_122 : ¬ drop0% Iris.ProgramLogic.nSteps_right 12 := fun h =>
  n_nsteps (@h Bool Unit Unit Unit nLang 0 ([true], ()) ([true], ()) ([true], ()) [] [] (.refl _)) (by decide)

end

section
attribute [local instance] W7c2.cL

-- `Iris.ProgramLogic.Language.Context.primStep_fill_inv` idx 6: necessary (cL, K = const 1, e = 5 stuck)
theorem w7c2_25 : ¬ drop0% Iris.ProgramLogic.Language.Context.primStep_fill_inv 6 := fun h => by
  obtain ⟨_, h1, _⟩ := @h Nat Unit Unit Unit cL (fun _ => 1) 5 () [] 0 () [] rfl ⟨rfl, rfl, rfl, rfl⟩
  exact absurd h1 (by decide)

-- `Iris.ProgramLogic.Language.Context.primStep_fill_inv` idx 14: necessary (cL, K = id, e = 5 stuck)
theorem w7c2_26 : ¬ drop0% Iris.ProgramLogic.Language.Context.primStep_fill_inv 14 := fun h => by
  obtain ⟨_, _, H⟩ := @h Nat Unit Unit Unit cL id (@Language.instContext_id Nat Unit Unit Unit cL) 5 () [] 0 () [] rfl
  exact absurd H.1 (by decide)

-- `Iris.ProgramLogic.Language.Context.reducible_fill` idx 6: necessary (cL, K = const 5, e = 1)
theorem w7c2_27 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducible_fill 6 := fun h => by
  obtain ⟨_, _, _, _, H⟩ := @h Nat Unit Unit Unit cL (fun _ => 5) 1 () ⟨[], 0, (), [], rfl, rfl, rfl, rfl⟩
  exact absurd H.1 (by decide)

-- `Iris.ProgramLogic.Language.Context.reducible_fill_inv` idx 6: necessary (cL, K = const 1, e = 5)
theorem w7c2_29 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducible_fill_inv 6 := fun h => by
  obtain ⟨_, _, _, _, H⟩ := @h Nat Unit Unit Unit cL (fun _ => 1) 5 () rfl ⟨[], 0, (), [], rfl, rfl, rfl, rfl⟩
  exact absurd H.1 (by decide)

-- `Iris.ProgramLogic.Language.Context.reducible_fill_inv` idx 10: necessary (cL, K = id, e = 5 stuck)
theorem w7c2_30 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducible_fill_inv 10 := fun h => by
  obtain ⟨_, _, _, _, H⟩ := @h Nat Unit Unit Unit cL id (@Language.instContext_id Nat Unit Unit Unit cL) 5 () rfl
  exact absurd H.1 (by decide)

-- `Iris.ProgramLogic.Language.Context.reducibleNoObs_fill` idx 6: necessary (cL, K = const 5, e = 1)
theorem w7c2_31 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducibleNoObs_fill 6 := fun h => by
  obtain ⟨_, _, _, H⟩ := @h Nat Unit Unit Unit cL (fun _ => 5) 1 () ⟨0, (), [], rfl, rfl, rfl, rfl⟩
  exact absurd H.1 (by decide)

-- `Iris.ProgramLogic.Language.Context.reducibleNoObs_fill_inv` idx 6: necessary (cL, K = const 1, e = 5)
theorem w7c2_33 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducibleNoObs_fill_inv 6 := fun h => by
  obtain ⟨_, _, _, H⟩ := @h Nat Unit Unit Unit cL (fun _ => 1) 5 () rfl ⟨0, (), [], rfl, rfl, rfl, rfl⟩
  exact absurd H.1 (by decide)

-- `Iris.ProgramLogic.Language.Context.reducibleNoObs_fill_inv` idx 10: necessary (cL, K = id, e = 5 stuck)
theorem w7c2_35 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducibleNoObs_fill_inv 10 := fun h => by
  obtain ⟨_, _, _, H⟩ := @h Nat Unit Unit Unit cL id (@Language.instContext_id Nat Unit Unit Unit cL) 5 () rfl
  exact absurd H.1 (by decide)

-- `Iris.ProgramLogic.Language.Context.irreducible_fill` idx 6: necessary (cL, K = const 1, e = 5)
theorem w7c2_36 : ¬ drop0% Iris.ProgramLogic.Language.Context.irreducible_fill 6 := fun h =>
  @h Nat Unit Unit Unit cL (fun _ => 1) 5 () rfl cl_irr5 [] 0 () [] ⟨rfl, rfl, rfl, rfl⟩

-- `Iris.ProgramLogic.Language.Context.notStuck_fill_inv` idx 8: necessary (cL, K = const 0, e = 5 stuck)
theorem w7c2_41 : ¬ drop0% Iris.ProgramLogic.Language.Context.notStuck_fill_inv 8 := fun h =>
  cl_not_ns5 (@h Nat Unit Unit Unit cL 5 () (fun _ => 0) (.inl rfl))

-- `Iris.ProgramLogic.Language.Context.notStuck_fill_inv` idx 9: necessary (cL, K = id, e = 5 stuck)
theorem w7c2_42 : ¬ drop0% Iris.ProgramLogic.Language.Context.notStuck_fill_inv 9 := fun h =>
  cl_not_ns5 (@h Nat Unit Unit Unit cL 5 () id (@Language.instContext_id Nat Unit Unit Unit cL))

-- `Iris.ProgramLogic.Language.Context.stuck_fill` idx 8: necessary (cL, K = const 0, e = 5 stuck)
theorem w7c2_43 : ¬ drop0% Iris.ProgramLogic.Language.Context.stuck_fill 8 := fun h =>
  absurd (@h Nat Unit Unit Unit cL 5 () (fun _ => 0) ⟨rfl, cl_irr5⟩).1 (by decide)

-- `Iris.ProgramLogic.Language.PurePrimStep.deterministic` idx 13: necessary (cL: pure step 1 to 0, e2' = 5)
theorem w7c2_52 : ¬ drop0% Iris.ProgramLogic.Language.PurePrimStep.deterministic 13 := fun h => by
  have H := @h Nat Unit Unit Unit cL 1 0 cl_pure
  have H2 := @H () () [] 5 []
  exact absurd H2.2.2.1 (by decide)

-- `Iris.ProgramLogic.Language.PureExec.pureExec` idx 9: necessary (cL: zero steps from 0 to 1)
theorem w7c2_53 : ¬ drop0% Iris.ProgramLogic.Language.PureExec.pureExec 9 := fun h =>
  absurd (iter0 (@h Nat Unit Unit Unit cL True 0 0 1 trivial)) (by decide)

-- `Iris.ProgramLogic.Language.purePrimStep_fill` idx 6: necessary (cL, K = const 5)
theorem w7c2_54 : ¬ drop0% Iris.ProgramLogic.Language.purePrimStep_fill 6 := fun h =>
  cl_nopure 5 5 (by decide) (@h Nat Unit Unit Unit cL (fun _ => 5) 1 0 cl_pure)

-- `Iris.ProgramLogic.Language.iterate_purePrimStep_fill` idx 6: necessary (cL, K = const 5)
theorem w7c2_56 : ¬ drop0% Iris.ProgramLogic.Language.iterate_purePrimStep_fill 6 := fun h =>
  cl_nopure 5 5 (by decide) (iter1 (@h Nat Unit Unit Unit cL (fun _ => 5) 1 1 0 cl_iter1))

-- `Iris.ProgramLogic.Language.iterate_purePrimStep_fill` idx 10: necessary (cL, K = id, zero steps from 0 to 1)
theorem w7c2_57 : ¬ drop0% Iris.ProgramLogic.Language.iterate_purePrimStep_fill 10 := fun h =>
  absurd (iter0 (@h Nat Unit Unit Unit cL id (@Language.instContext_id Nat Unit Unit Unit cL) 0 0 1)) (by decide)

-- `Iris.ProgramLogic.Language.ReflTransGen_pureStep_fill` idx 6: necessary (cL, K e = e + 5: 6 and 5 stuck)
theorem w7c2_58 : ¬ drop0% Iris.ProgramLogic.Language.ReflTransGen_pureStep_fill 6 := fun h =>
  absurd (rtg_stuck (fun z => cl_nopure 6 z (by decide))
    (@h Nat Unit Unit Unit cL (fun e => e + 5) 1 0 (.tail .refl cl_pure))) (by decide)

-- `Iris.ProgramLogic.Language.ReflTransGen_pureStep_fill` idx 9: necessary (cL, K = id, 0 does not reach 1)
theorem w7c2_59 : ¬ drop0% Iris.ProgramLogic.Language.ReflTransGen_pureStep_fill 9 := fun h =>
  absurd (rtg_stuck (fun z => cl_nopure 0 z (by decide))
    (@h Nat Unit Unit Unit cL id (@Language.instContext_id Nat Unit Unit Unit cL) 0 1)) (by decide)

-- `Iris.ProgramLogic.Language.pureExec_fill` idx 6: necessary (cL, PureExec True 1 1 0, K e = e + 5)
theorem w7c2_60 : ¬ drop0% Iris.ProgramLogic.Language.pureExec_fill 6 := fun h =>
  cl_nopure 6 5 (by decide)
    (iter1 ((@h Nat Unit Unit Unit cL (fun e => e + 5) True 1 1 0 ⟨fun _ => cl_iter1⟩).pureExec trivial))

-- `Iris.ProgramLogic.Language.pureExec_fill` idx 11: necessary (cL, K = id, PureExec True 0 0 1 fails)
theorem w7c2_61 : ¬ drop0% Iris.ProgramLogic.Language.pureExec_fill 11 := fun h =>
  absurd (iter0 ((@h Nat Unit Unit Unit cL id (@Language.instContext_id Nat Unit Unit Unit cL) True 0 0 1).pureExec trivial))
    (by decide)

-- `Iris.ProgramLogic.Language.ReflTransGen_purePrimStep_val` idx 8: necessary (cL: e = 1 is not a value)
theorem w7c2_62 : ¬ drop0% Iris.ProgramLogic.Language.ReflTransGen_purePrimStep_val 8 := fun h =>
  absurd (@h Nat Unit Unit Unit cL ⟨()⟩ () 1) (by decide)

-- `Iris.ProgramLogic.Language.IntoVal.into_val` idx 7: necessary (cL: ofVal () = 0, e = 1)
theorem w7c2_63 : ¬ drop0% Iris.ProgramLogic.Language.IntoVal.into_val 7 := fun h =>
  absurd (@h Nat Unit Unit Unit cL 1 ()) (by decide)

-- `Iris.ProgramLogic.Language.AsVal.as_val` idx 6: necessary (cL: e = 1 is not a value)
theorem w7c2_64 : ¬ drop0% Iris.ProgramLogic.Language.AsVal.as_val 6 := fun h => by
  obtain ⟨⟨⟩, hv⟩ := @h Nat Unit Unit Unit cL 1
  exact absurd hv (by decide)

-- `Iris.ProgramLogic.Language.as_val_isSome` idx 6: necessary (cL: e = 1 is not a value)
theorem w7c2_65 : ¬ drop0% Iris.ProgramLogic.Language.as_val_isSome 6 := fun h =>
  absurd (@h Nat Unit Unit Unit cL 1) (by decide)

-- `Iris.ProgramLogic.Language.erasedStep_pureSteps` idx 10: necessary (cL: t1 = t3 = [], t2 = [0])
theorem w7c2_66 : ¬ drop0% Iris.ProgramLogic.Language.erasedStep_pureSteps 10 := fun h => by
  rcases @h Nat Unit Unit Unit cL [] [0] [] () () List.Forall₂.nil with ⟨_, hps⟩ | ⟨i, e, _, _, _, h1, _⟩
  · cases hps
  · simp at h1

-- `Iris.ProgramLogic.Language.erasedStep_pureSteps` idx 11: necessary (cL: [1] steps to [0], t3 = [5])
theorem w7c2_67 : ¬ drop0% Iris.ProgramLogic.Language.erasedStep_pureSteps 11 := fun h => by
  rcases @h Nat Unit Unit Unit cL [1] [0] [5] () ()
      ⟨[], Language.Step.of_primStep (Λ := cL) (t₁ := []) (t₂ := []) (eₜ := []) ⟨rfl, rfl, rfl, rfl⟩⟩ with
    ⟨_, hps⟩ | ⟨i, e, _, _, _, h1, h2, _⟩
  · cases hps with
    | cons hr _ => exact absurd (rtg_stuck (fun z => cl_nopure 0 z (by decide)) hr) (by decide)
  · rcases i with _ | i <;> simp at h1 h2 <;> omega

-- `Iris.ProgramLogic.cfgSafe_of_cfgSafeForking` idx 7: necessary (cL: the pool [5] is stuck)
theorem w7c2_104 : ¬ drop0% Iris.ProgramLogic.cfgSafe_of_cfgSafeForking 7 := fun h => by
  have H := @h Nat Unit Unit Unit cL ([5], ()) .doesFork
  unfold cfgSafe at H
  exact cl_not_ns5 (@H ([5], ()) FromMathlib.Relation.ReflTransGen.refl 5 (by simp))

-- `Iris.ProgramLogic.PrimSteps.fill` idx 6: necessary (cL, K = const 5)
theorem w7c2_105 : ¬ drop0% Iris.ProgramLogic.PrimSteps.fill 6 := fun h =>
  cl_ps5 (@h Nat Unit Unit Unit cL (fun _ => 5) 1 () [] 0 () [] (.once ⟨rfl, rfl, rfl, rfl⟩))

end

open Iris Iris.BI Iris.ProgramLogic W7c2 Std.LawfulSet
section
attribute [local instance] W7c2.seL

-- `Iris.ProgramLogic.wp_lift_step_fupdN` idx 12: necessary (seL, e1 = 0 a value, s = MaybeStuck, Φ = False: premise vacuous, adequacy)
theorem w7c2_68 : ¬ drop0% Iris.ProgramLogic.wp_lift_step_fupdN 12 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 0 (fun _ => iprop(⌜False⌝)))
    iintro - %σ₁ %ns %obs %obs' %nt -
    iapply fupd_mask_intro_discard empty_subset
    isplit
    · ipureintro; trivial
    · iintro %e₂ %σ₂ %eₜ %hs
      exact (se_val0 hs).elim)

-- `Iris.ProgramLogic.wp_lift_step_fupd` idx 12: necessary (seL, e1 = 0 a value, s = MaybeStuck, Φ = False: premise vacuous, adequacy)
theorem w7c2_69 : ¬ drop0% Iris.ProgramLogic.wp_lift_step_fupd 12 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 0 (fun _ => iprop(⌜False⌝)))
    iintro - %σ₁ %ns %obs %obs' %nt -
    iapply fupd_mask_intro_discard empty_subset
    isplit
    · ipureintro; trivial
    · iintro %e₂ %σ₂ %eₜ %hs
      exact (se_val0 hs).elim)

-- `Iris.ProgramLogic.wp_lift_stuck` idx 11: necessary (seL, stateInterp = False makes the premise trivial; e = 0 a value, Φ = False)
theorem w7c2_70 : ¬ drop0% Iris.ProgramLogic.wp_lift_stuck 11 := fun h =>
  val_false (s := .MaybeStuck) fun x => by
    letI := iF x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iF x) ⊤ 0 (fun _ => iprop(⌜False⌝)))
    iintro - %σ %ns %obs %nt H
    iexfalso
    iexact H

-- `Iris.ProgramLogic.wp_lift_step` idx 12: necessary (seL, e1 = 0 a value, s = MaybeStuck, Φ = False: premise vacuous, adequacy)
theorem w7c2_71 : ¬ drop0% Iris.ProgramLogic.wp_lift_step 12 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 0 (fun _ => iprop(⌜False⌝)))
    iintro - %σ₁ %ns %obs %obs' %nt -
    iapply fupd_mask_intro_discard empty_subset
    isplit
    · ipureintro; trivial
    · iintro !> %e₂ %σ₂ %eₜ %hs
      exact (se_val0 hs).elim)

-- `Iris.ProgramLogic.wp_lift_pure_step_no_fork` idx 14: necessary (seL, e1 = 0 a value, Φ = False: premises vacuous, adequacy)
theorem w7c2_72 : ¬ drop0% Iris.ProgramLogic.wp_lift_pure_step_no_fork 14 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 0 (fun _ => iprop(⌜False⌝))
      ⟨false⟩ ⊤ (fun _ _ _ _ _ hs => (se_val0 hs).elim))
    iintro -
    iapply step_fupd_intro subset_refl
    iintro !> %obs %e₂ %eₜ %σ %hs
    exact (se_val0 hs).elim)

-- `Iris.ProgramLogic.wp_lift_pure_step_no_fork` idx 15: necessary (seL, e1 = 2 only steps by flipping the state: premise vacuous, 2 reaches the value 0)
theorem w7c2_73 : ¬ drop0% Iris.ProgramLogic.wp_lift_pure_step_no_fork 15 := fun h =>
  se_ad2 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 2 (fun _ => iprop(⌜False⌝))
      ⟨false⟩ ⊤ (fun _ => rfl))
    iintro -
    iapply step_fupd_intro subset_refl
    iintro !> %obs %e₂ %eₜ %σ %hs
    exact (se_flip hs).elim)

-- `Iris.ProgramLogic.wp_lift_pure_stuck` idx 12: necessary (seL, e = 0 a value, Φ = False: adequacy)
theorem w7c2_74 : ¬ drop0% Iris.ProgramLogic.wp_lift_pure_stuck 12 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x =>
    true_intro.trans (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) ⊤ 0 (fun _ => iprop(⌜False⌝)) ⟨false⟩))

-- `Iris.ProgramLogic.wp_lift_atomic_step_fupd` idx 12: necessary (seL, e1 = 0 a value, Φ = False: premise vacuous, adequacy)
theorem w7c2_75 : ¬ drop0% Iris.ProgramLogic.wp_lift_atomic_step_fupd 12 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 0 (fun _ => iprop(⌜False⌝)) ⊤)
    iintro - %σ₁ %ns %obs %obs' %nt -
    imodintro
    isplit
    · ipureintro; trivial
    · iintro %e₂ %σ₂ %eₜ %hs
      exact (se_val0 hs).elim)

-- `Iris.ProgramLogic.wp_lift_atomic_step` idx 12: necessary (seL, e1 = 0 a value, Φ = False: premise vacuous, adequacy)
theorem w7c2_76 : ¬ drop0% Iris.ProgramLogic.wp_lift_atomic_step 12 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 0 (fun _ => iprop(⌜False⌝)))
    iintro - %σ₁ %ns %obs %obs' %nt -
    imodintro
    isplit
    · ipureintro; trivial
    · iintro !> %e₂ %σ₂ %eₜ %hs
      exact (se_val0 hs).elim)

-- `Iris.ProgramLogic.wp_lift_pure_det_step_no_fork` idx 15: necessary (seL, e1 = 0 a value, e2 = 5 stuck so WP e2 holds under MaybeStuck, Φ = False)
theorem w7c2_77 : ¬ drop0% Iris.ProgramLogic.wp_lift_pure_det_step_no_fork 15 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 0 5 (fun _ => iprop(⌜False⌝))
      ⟨false⟩ ⊤ (fun hs => (se_val0 hs).elim))
    iintro -
    iapply step_fupd_intro subset_refl
    iintro !> -
    iapply (wp_lift_pure_stuck (fun σ => se_stuck5 σ))
    ipureintro; trivial)

-- `Iris.ProgramLogic.wp_lift_pure_det_step_no_fork` idx 16: necessary (seL, e1 = 1 steps purely to 0, e2 = 5 stuck so WP e2 holds under MaybeStuck, Φ = False)
theorem w7c2_78 : ¬ drop0% Iris.ProgramLogic.wp_lift_pure_det_step_no_fork 16 := fun h =>
  se_ad1 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 1 5 (fun _ => iprop(⌜False⌝))
      ⟨false⟩ ⊤ (fun _ => rfl))
    iintro -
    iapply step_fupd_intro subset_refl
    iintro !> -
    iapply (wp_lift_pure_stuck (fun σ => se_stuck5 σ))
    ipureintro; trivial)

-- `Iris.ProgramLogic.wp_pure_step_fupd` idx 17: necessary (seL, n = 0, e1 = 0 a value, e2 = 5 stuck, φ = True, Φ = False)
theorem w7c2_79 : ¬ drop0% Iris.ProgramLogic.wp_pure_step_fupd 17 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 0 5 (fun _ => iprop(⌜False⌝))
      True 0 ⟨false⟩ ⊤ trivial)
    simp only [step_fupdN]
    iintro - -
    iapply (wp_lift_pure_stuck (fun σ => se_stuck5 σ))
    ipureintro; trivial)

-- `Iris.ProgramLogic.wp_pure_step_later` idx 16: necessary (seL, n = 0, e1 = 0 a value, e2 = 5 stuck, φ = True, Φ = False)
theorem w7c2_80 : ¬ drop0% Iris.ProgramLogic.wp_pure_step_later 16 := fun h =>
  se_ad0 (lift_adeq (s := .MaybeStuck) (φ := fun _ => False) fun x => by
    letI := iS x
    refine .trans ?_ (@h .hasNoLC Nat Bool Unit Unit inferInstance PGF (iS x) .MaybeStuck ⊤ 0 5 (fun _ => iprop(⌜False⌝))
      True 0 ⟨false⟩ trivial)
    simp only [BI.BIBase.laterN, Nat.repeat]
    iintro - -
    iapply (wp_lift_pure_stuck (fun σ => se_stuck5 σ))
    ipureintro; trivial)
end

open Iris Iris.BI Iris.ProgramLogic W7c2 Std.LawfulSet
section
attribute [local instance] W7c2.seL

-- `Iris.ProgramLogic.ownP_adequacy` idx 11: necessary (seL with an ownP ghost slot, e = 0 a value, φ = False)
theorem w7c2_81 : ¬ drop0% Iris.ProgramLogic.ownP_adequacy 11 := fun h =>
  se_ad0 (@h Nat Bool Unit Unit PGF inferInstance pgfPre .MaybeStuck 0 false (fun _ => False))

-- `Iris.ProgramLogic.ownP_invariance` idx 13: necessary (seL with an ownP ghost slot, zero steps, φ = False)
theorem w7c2_82 : ¬ drop0% Iris.ProgramLogic.ownP_invariance 13 := fun h =>
  @h Nat Bool Unit Unit PGF inferInstance pgfPre .MaybeStuck 0 false [0] false (fun _ => False) .refl

-- `Iris.ProgramLogic.ownP_invariance` idx 14: necessary (seL, e = 0 a value, φ σ = (σ = false) holds at σ1 = false, σ2 = true)
theorem w7c2_83 : ¬ drop0% Iris.ProgramLogic.ownP_invariance 14 := fun h =>
  absurd (@h Nat Bool Unit Unit PGF inferInstance pgfPre .MaybeStuck 0 false [0] true (fun σ => σ = false) (by
    intro ι
    have hv : (iprop(True) : IProp PGF) ⊢ WP (0 : Nat) @ Stuckness.MaybeStuck ; ⊤ {{ _v, True }} := wp_value' (v := ()) (Φ := fun _ => iprop(True))
    iintro H
    imodintro
    isplitr [H]
    · iapply hv; ipureintro; trivial
    · iapply fupd_mask_intro_discard empty_subset
      iexists false
      isplit
      · iexact H
      · ipureintro; rfl)) (by decide)

-- `Iris.ProgramLogic.ownP_lift_pure_step` idx 12: necessary (seL, e1 = 5 stuck, s = NotStuck: premises vacuous, adequacy not_stuck)
theorem w7c2_84 : ¬ drop0% Iris.ProgramLogic.ownP_lift_pure_step 12 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF inferInstance ι .NotStuck ⊤ 5 (fun _ => iprop(⌜True⌝)) ⟨false⟩
      (fun hs => ((se_stuck5 _).2 _ _ _ _ hs).elim))
    iintro - !> %obs %e₂ %eₜ %σ %hs
    exact ((se_stuck5 σ).2 _ _ _ _ hs).elim)

-- `Iris.ProgramLogic.ownP_lift_pure_step` idx 13: necessary (seL, e1 = 2 only steps by flipping the state: premise vacuous, 2 reaches the value 0)
theorem w7c2_85 : ¬ drop0% Iris.ProgramLogic.ownP_lift_pure_step 13 := fun h =>
  se_ad2 (own_adeq (s := .MaybeStuck) (σ := false) (φ := fun _ => False) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF inferInstance ι .MaybeStuck ⊤ 2 (fun _ => iprop(⌜False⌝)) ⟨false⟩
      (fun _ => rfl))
    iintro - !> %obs %e₂ %eₜ %σ %hs
    exact (se_flip hs).elim)

-- `Iris.ProgramLogic.ownP_lift_atomic_step` idx 12: necessary (seL, e1 = 5 stuck, s = NotStuck, Φ = True: adequacy not_stuck)
theorem w7c2_86 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_step 12 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF inferInstance ι .NotStuck ⊤ 5 (fun _ => iprop(⌜True⌝)) false)
    iintro H
    isplitl [H]
    · iintro !>; iexact H
    · iintro !> %obs %e₂ %σ₂ %eₜ %hs
      exact ((se_stuck5 false).2 _ _ _ _ hs).elim)

-- `Iris.ProgramLogic.ownP_lift_atomic_det_step` idx 15: necessary (seL, e1 = 5 stuck, s = NotStuck, Φ = True, eₜ = []: adequacy not_stuck)
theorem w7c2_87 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_det_step 15 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF inferInstance ι .NotStuck ⊤ 5 (fun _ => iprop(⌜True⌝)) false false () []
      (fun hs => ((se_stuck5 false).2 _ _ _ _ hs).elim))
    iintro H
    isplitl [H]
    · iintro !>; iexact H
    · iintro !> -
      simp only [Algebra.BigOpL.bigOpL_nil]
      isplit
      · ipureintro; trivial
      · itrivial)

-- `Iris.ProgramLogic.ownP_lift_atomic_det_step` idx 16: necessary (seL, e1 = 4 steps to the stuck 5, s = NotStuck, Φ = True, eₜ = []: adequacy not_stuck)
theorem w7c2_88 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_det_step 16 := fun h =>
  se_ad4 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF inferInstance ι .NotStuck ⊤ 4 (fun _ => iprop(⌜True⌝)) false false () []
      (se_red4 false))
    iintro H
    isplitl [H]
    · iintro !>; iexact H
    · iintro !> -
      simp only [Algebra.BigOpL.bigOpL_nil]
      isplit
      · ipureintro; trivial
      · itrivial)

-- `Iris.ProgramLogic.ownP_lift_atomic_det_step_no_fork` idx 13: necessary (seL, e1 = 5 stuck, s = NotStuck, Φ = True: adequacy not_stuck)
theorem w7c2_89 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_det_step_no_fork 13 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    have H0 := @h Nat Bool Unit Unit PGF inferInstance ι .NotStuck ⊤ 5 false false ()
      (fun hs => ((se_stuck5 false).2 _ _ _ _ hs).elim)
    iintro H
    iapply H0 $$ %(fun _ => iprop(⌜True⌝)) [H]
    · iintro !>; iexact H
    · iintro !> -; ipureintro; trivial)

-- `Iris.ProgramLogic.ownP_lift_atomic_det_step_no_fork` idx 14: necessary (seL, e1 = 4 steps to the stuck 5, s = NotStuck, Φ = True: adequacy not_stuck)
theorem w7c2_90 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_det_step_no_fork 14 := fun h =>
  se_ad4 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    have H0 := @h Nat Bool Unit Unit PGF inferInstance ι .NotStuck ⊤ 4 false false () (se_red4 false)
    iintro H
    iapply H0 $$ %(fun _ => iprop(⌜True⌝)) [H]
    · iintro !>; iexact H
    · iintro !> -; ipureintro; trivial)

-- `Iris.ProgramLogic.ownP_lift_pure_det_step_no_fork` idx 13: necessary (seL, e1 = 5 stuck, e2 = 0 a value, s = NotStuck, Φ = True: adequacy not_stuck)
theorem w7c2_91 : ¬ drop0% Iris.ProgramLogic.ownP_lift_pure_det_step_no_fork 13 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    have hv : (iprop(⌜True⌝) : IProp PGF) ⊢ WP (0 : Nat) @ Stuckness.NotStuck ; ⊤ {{ _v, ⌜True⌝ }} :=
      wp_value' (v := ()) (Φ := fun _ => iprop(⌜True⌝))
    refine .trans ?_ (@h Nat Bool Unit Unit PGF inferInstance ι .NotStuck ⊤ 5 0 (fun _ => iprop(⌜True⌝)) ⟨false⟩
      (fun hs => ((se_stuck5 _).2 _ _ _ _ hs).elim))
    iintro - !>
    iapply hv
    ipureintro; trivial)

-- `Iris.ProgramLogic.ownP_lift_pure_det_step_no_fork` idx 14: necessary (seL, e1 = 4 steps to the stuck 5, e2 = 0 a value, s = NotStuck, Φ = True)
theorem w7c2_92 : ¬ drop0% Iris.ProgramLogic.ownP_lift_pure_det_step_no_fork 14 := fun h =>
  se_ad4 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    have hv : (iprop(⌜True⌝) : IProp PGF) ⊢ WP (0 : Nat) @ Stuckness.NotStuck ; ⊤ {{ _v, ⌜True⌝ }} :=
      wp_value' (v := ()) (Φ := fun _ => iprop(⌜True⌝))
    refine .trans ?_ (@h Nat Bool Unit Unit PGF inferInstance ι .NotStuck ⊤ 4 0 (fun _ => iprop(⌜True⌝)) ⟨false⟩
      se_red4)
    iintro - !>
    iapply hv
    ipureintro; trivial)

-- `_private.Iris.ProgramLogic.OwnP.0.Iris.ProgramLogic.reducibleOrNotVal_of_baseStep_reducible` idx 9: necessary (seL, s = MaybeStuck, e = 0 a value)
theorem w7c2_93 : ¬ drop0% _private.Iris.ProgramLogic.OwnP.«0».Iris.ProgramLogic.reducibleOrNotVal_of_baseStep_reducible 9 := fun h =>
  absurd (@h Nat Bool Unit Unit (List Empty) inferInstance .MaybeStuck 0 false) (by decide)

-- `Iris.ProgramLogic.ownP_lift_pure_base_step` idx 13: necessary (seL, e1 = 5 base-stuck, s = NotStuck, Φ = True: adequacy not_stuck)
theorem w7c2_95 : ¬ drop0% Iris.ProgramLogic.ownP_lift_pure_base_step 13 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF (List Empty) inferInstance ι .NotStuck ⊤ 5 (fun _ => iprop(⌜True⌝)) ⟨false⟩
      (fun hs => (se_b5 hs).elim))
    iintro - !> %obs %e₂ %eₜ %σ %hs
    exact (se_b5 hs).elim)

-- `Iris.ProgramLogic.ownP_lift_pure_base_step` idx 14: necessary (seL, e1 = 2 only steps by flipping the state: premise vacuous, 2 reaches the value 0)
theorem w7c2_96 : ¬ drop0% Iris.ProgramLogic.ownP_lift_pure_base_step 14 := fun h =>
  se_ad2 (own_adeq (s := .MaybeStuck) (σ := false) (φ := fun _ => False) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF (List Empty) inferInstance ι .MaybeStuck ⊤ 2 (fun _ => iprop(⌜False⌝)) ⟨false⟩
      se_bred2)
    iintro - !> %obs %e₂ %eₜ %σ %hs
    exact (se_bflip hs).elim)

-- `Iris.ProgramLogic.ownP_lift_atomic_base_step` idx 13: necessary (seL, e1 = 5 base-stuck, s = NotStuck, Φ = True: adequacy not_stuck)
theorem w7c2_97 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_base_step 13 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF (List Empty) inferInstance ι .NotStuck ⊤ 5 false (fun _ => iprop(⌜True⌝)))
    iintro H
    isplitl [H]
    · iintro !>; iexact H
    · iintro !> %obs %e₂ %σ₂ %eₜ %hs
      exact (se_b5 hs).elim)

-- `Iris.ProgramLogic.ownP_lift_atomic_det_base_step` idx 16: necessary (seL, e1 = 5 base-stuck, s = NotStuck, Φ = True, eₜ = []: adequacy not_stuck)
theorem w7c2_98 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_det_base_step 16 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF (List Empty) inferInstance ι .NotStuck ⊤ 5 false false (fun _ => iprop(⌜True⌝)) () []
      (fun hs => (se_b5 hs).elim))
    iintro H
    isplitl [H]
    · iintro !>; iexact H
    · iintro !> -
      simp only [Algebra.BigOpL.bigOpL_nil]
      isplit
      · ipureintro; trivial
      · itrivial)

-- `Iris.ProgramLogic.ownP_lift_atomic_det_base_step` idx 17: necessary (seL, e1 = 4 base-steps to the stuck 5, s = NotStuck, Φ = True, eₜ = [])
theorem w7c2_99 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_det_base_step 17 := fun h =>
  se_ad4 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF (List Empty) inferInstance ι .NotStuck ⊤ 4 false false (fun _ => iprop(⌜True⌝)) () []
      (se_bred4 false))
    iintro H
    isplitl [H]
    · iintro !>; iexact H
    · iintro !> -
      simp only [Algebra.BigOpL.bigOpL_nil]
      isplit
      · ipureintro; trivial
      · itrivial)

-- `Iris.ProgramLogic.ownP_lift_atomic_det_base_step_no_fork` idx 15: necessary (seL, e1 = 5 base-stuck, s = NotStuck, Φ = True: adequacy not_stuck)
theorem w7c2_100 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_det_base_step_no_fork 15 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    have H0 := @h Nat Bool Unit Unit PGF (List Empty) inferInstance ι .NotStuck ⊤ 5 false false () []
      (fun hs => (se_b5 hs).elim)
    iintro H
    iapply H0 $$ %(fun _ => iprop(⌜True⌝)) [H]
    · iintro !>; iexact H
    · iintro !> -; ipureintro; trivial)

-- `Iris.ProgramLogic.ownP_lift_atomic_det_base_step_no_fork` idx 16: necessary (seL, e1 = 4 base-steps to the stuck 5, s = NotStuck, Φ = True)
theorem w7c2_101 : ¬ drop0% Iris.ProgramLogic.ownP_lift_atomic_det_base_step_no_fork 16 := fun h =>
  se_ad4 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    have H0 := @h Nat Bool Unit Unit PGF (List Empty) inferInstance ι .NotStuck ⊤ 4 false false () [] (se_bred4 false)
    iintro H
    iapply H0 $$ %(fun _ => iprop(⌜True⌝)) [H]
    · iintro !>; iexact H
    · iintro !> -; ipureintro; trivial)

-- `Iris.ProgramLogic.ownP_lift_pure_det_base_step_no_fork` idx 14: necessary (seL, e1 = 5 base-stuck, e2 = 0 a value, s = NotStuck, Φ = True)
theorem w7c2_102 : ¬ drop0% Iris.ProgramLogic.ownP_lift_pure_det_base_step_no_fork 14 := fun h =>
  se_ad5 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    have hv : (iprop(⌜True⌝) : IProp PGF) ⊢ WP (0 : Nat) @ Stuckness.NotStuck ; ⊤ {{ _v, ⌜True⌝ }} :=
      wp_value' (v := ()) (Φ := fun _ => iprop(⌜True⌝))
    refine .trans ?_ (@h Nat Bool Unit Unit PGF (List Empty) inferInstance ι .NotStuck ⊤ 5 0 (fun _ => iprop(⌜True⌝)) ⟨false⟩
      (fun hs => (se_b5 hs).elim))
    iintro - !>
    iapply hv
    ipureintro; trivial)

-- `Iris.ProgramLogic.ownP_lift_pure_det_base_step_no_fork` idx 15: necessary (seL, e1 = 4 base-steps to the stuck 5, e2 = 0 a value, s = NotStuck, Φ = True)
theorem w7c2_103 : ¬ drop0% Iris.ProgramLogic.ownP_lift_pure_det_base_step_no_fork 15 := fun h =>
  se_ad4 (own_adeq (s := .NotStuck) (σ := false) (φ := fun _ => True) fun ι => by
    have hv : (iprop(⌜True⌝) : IProp PGF) ⊢ WP (0 : Nat) @ Stuckness.NotStuck ; ⊤ {{ _v, ⌜True⌝ }} :=
      wp_value' (v := ()) (Φ := fun _ => iprop(⌜True⌝))
    refine .trans ?_ (@h Nat Bool Unit Unit PGF (List Empty) inferInstance ι .NotStuck ⊤ 4 0 (fun _ => iprop(⌜True⌝)) ⟨false⟩
      se_bred4)
    iintro - !>
    iapply hv
    ipureintro; trivial)
end

namespace W7c2
open Iris Iris.BI Iris.ProgramLogic Std.LawfulSet

/-- Ectx-item language on Nat with one item `fill () e = e + 10`, Bool state: 0 value; base steps 1 ↦ 0 and 10 ↦ 0 (so 11 = fill () 1 is base-stuck but reduces in context to 10 and then to 0). -/
def kL : EctxItemLanguage Nat Unit Bool Unit Unit where
  toVal := toValN
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases he : e = 0 <;> simp_all [toValN]
  toVal_coe := fun _ => rfl
  baseStep := fun c o r => o = [] ∧ r.2.2 = [] ∧ r.2.1 = c.2 ∧ (c.1 = 1 ∨ c.1 = 10) ∧ r.1 = 0
  fillItem := fun _ e => e + 10
  fillItem_inj := fun {_} a b h => by simpa using h
  fillItem_val := fun e _ h => by simp [toValN] at h
  fillItem_no_val_inj := fun _ _ _ _ _ => rfl
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    obtain ⟨-, -, -, h, -⟩ := h
    simp only at h
    rcases h with rfl | rfl <;> rfl
  base_ctx_step_val := by
    intro Ki e σ obs e' σ' eₜ h
    obtain ⟨-, -, -, h, -⟩ := h
    simp only at h
    have : e = 0 := by omega
    subst this; rfl

section
attribute [local instance] kL

theorem k_stuck11 (σ : Bool) : BaseStep.Stuck (Expr := Nat) (State := Bool) (11, σ) :=
  ⟨rfl, fun _ _ _ _ h => by obtain ⟨-, -, -, h, -⟩ := h; simp at h⟩

theorem k_ad11 (A : adequate (Expr := Nat) (State := Bool) .MaybeStuck 11 false (fun _ _ => False)) : False := by
  have s1 : PrimStep.primStep (Expr := Nat) (State := Bool) (11, false) [] (10, false, []) :=
    BaseStep.ContextStep.ofBaseStep (Ectx := List Unit) [()] (e₁ := 1) (e₂ := 0) ⟨rfl, rfl, rfl, Or.inl rfl, rfl⟩
  have s2 : PrimStep.primStep (Expr := Nat) (State := Bool) (10, false) [] (0, false, []) :=
    EctxLanguage.primStep_of_baseStep (Ectx := List Unit) ⟨rfl, rfl, rfl, Or.inr rfl, rfl⟩
  exact A.adequate_result [] false ()
    (.tail (.tail .refl ⟨[], Language.Step.of_primStep (t₁ := []) (t₂ := []) (eₜ := []) s1⟩)
      ⟨[], Language.Step.of_primStep (t₁ := []) (t₂ := []) (eₜ := []) s2⟩)

theorem own_adeqK {s : Stuckness} {e : Nat} {σ : Bool} {φ : Unit → Prop}
    (H : ∀ ι : OwnPGS Bool PGF, ownP (GF := PGF) σ ⊢ (WP e @ s ; ⊤ {{ v, ⌜φ v⌝ }} : IProp PGF)) :
    adequate s e σ (fun v _ => φ v) :=
  ownP_adequacy (GF := PGF) s e σ φ (by intro ι; exact H ι)
end

end W7c2

open Iris Iris.BI Iris.ProgramLogic W7c2 Std.LawfulSet
section
attribute [local instance] W7c2.kL

-- `Iris.ProgramLogic.ownP_lift_base_stuck` idx 11: necessary (kL: 11 = fill () 1 is base-stuck but steps in context to 10 and then to the value 0; Φ = False)
theorem w7c2_94 : ¬ drop0% Iris.ProgramLogic.ownP_lift_base_stuck 11 := fun h =>
  k_ad11 (own_adeqK (s := .MaybeStuck) (σ := false) (φ := fun _ => False) fun ι => by
    refine .trans ?_ (@h Nat Bool Unit Unit PGF (List Unit) inferInstance ι ⊤ 11 (fun _ => iprop(⌜False⌝)))
    iintro H
    iapply fupd_mask_intro_discard empty_subset
    iexists false
    isplitr [H]
    · ipureintro; exact k_stuck11 false
    · iintro !>; iexact H)
end
