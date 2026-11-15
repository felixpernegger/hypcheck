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
namespace T1c6
open Iris Iris.BI COFE Auth

/-- Closed-proofs GF (invariant, mask, credit slots 0–3) with the functor F in every slot ≥ 4 (from W7c0). -/
noncomputable def GX (F : OFunctorPre) [RFunctorContractive F] [RFunctorAffine F] : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF⟩
  | 1  => ⟨constOF CoPsetDisjL⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3  => ⟨AuthURF (constOF Credit)⟩
  | _  => ⟨F⟩

section
variable (F : OFunctorPre) [RFunctorContractive F] [RFunctorAffine F]
instance gxWsat : WsatGpreS (GX F) where
  inv := { τ := 0, transp := by unfold GX; rfl }
  enabled := { τ := 1, transp := by unfold GX; rfl }
  disabled := { τ := 2, transp := by unfold GX; rfl }
instance gxLc : LcGpreS (GX F) where
  lc_elem := { τ := 3, transp := by unfold GX; rfl }
instance gxInv : InvGpreS (GX F) where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance
instance gxElem : ElemG (GX F) F := { τ := 4, transp := by unfold GX; rfl }
end

instance gvGX : GhostVarG (GX (GhostVarF Bool)) Bool := ⟨⟩
noncomputable abbrev GV := GX (GhostVarF Bool)

/-- Fancy-update soundness: ⊢ |={E1,E2}=> False under every invariant setup is impossible. -/
theorem fupd_false {GF : BundledGFunctors} [InvGpreS GF] (E1 E2 : CoPset)
    (H : ∀ [InvGS_gen .hasNoLC GF], ⊢ (iprop(|={E1,E2}=> ⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF)
    (fupd_soundness .hasNoLC 0 (E1 := E1) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))

/-- ⊢ |={∅}[∅]▷=> False is impossible in IProp (step_fupdN soundness, from W6c1). -/
theorem step_false {GF : BundledGFunctors} [InvGpreS GF] (H : ∀ [InvGS_gen .hasNoLC GF], ⊢ (iprop(|={∅}[∅]▷=> ⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF)
    (step_fupdN_soundness (hlc := .hasNoLC) 1 0 (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (H.trans (fupd_mask_intro_discard (fun _ h => (CoPset.mem_empty h).elim)))))

/-- A full ghost variable can be updated to any discarded value. -/
theorem gv_disc [InvGS_gen .hasNoLC GV] (E : CoPset) (γ : GName) (a : Bool) :
    (γ ↪VAR true : IProp GV) ⊢ |={E}=> γ ↪VAR{.discard} a := by
  iintro H
  imod ghost_var_update a γ true $$ H with H
  imod ghost_var_persist γ _ a $$ H with H
  imodintro
  iexact H

/-- Discarded ghost variables at both Booleans contradict. -/
theorem gv_both (γ : GName) : (iprop(∀ a : Bool, γ ↪VAR{.discard} a) : IProp GV) ⊢ ⌜False⌝ := by
  iintro #H
  ihave H1 := H $$ %true
  ihave H2 := H $$ %false
  ihave %He := ghost_var_agree γ true _ false _ $$ H1 H2
  exact absurd He (by decide)
end T1c6
open Iris Iris.BI T1c6

-- `Iris.ProofMode.fromForall_fupd` idx 12: necessary (IProp with a ghost variable: from γ ↪VAR true both discarded values are reachable, not both at once)
theorem t1c6_1 : ¬ drop0% Iris.ProofMode.fromForall_fupd 12 := fun h =>
  fupd_false (GF := GV) ∅ ∅ fun {_} => by
    iintro
    imod ghost_var_alloc (GF := GV) true with ⟨%γ, H⟩
    ihave K := (@h (IProp GV) _ _ _ _ ∅ ∅ iprop(∀ a : Bool, γ ↪VAR{.discard} a) Bool
      (fun a => iprop(γ ↪VAR{.discard} a)) ⟨fun _ h => h⟩ inferInstance).from_forall
    iapply (BIFUpdate.mono (gv_both γ))
    iapply K
    iintro %a
    iapply gv_disc ∅ γ a
    iexact H

-- `Iris.ProofMode.fromForall_stepFupd` idx 12: necessary (stated by hand at α : Type, drop0% would put α in Prop; same ghost variable argument under a step)
theorem t1c6_2 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP] [Iris.BI.BIAffine PROP]
    {α : Type} (E1 E2 : CoPset) (P : PROP) (Φ : α → PROP) [inst_4 : Iris.ProofMode.TCSideCondition (E2 ⊆ E1)]
    [h : Iris.ProofMode.FromForall P Φ],
    Iris.ProofMode.FromForall iprop(|={E1}[E2]▷=> P) fun a => iprop(|={E1}[E2]▷=> Φ a)) := fun h =>
  step_false (GF := GV) fun {_} => by
    iintro
    imod ghost_var_alloc (GF := GV) true with ⟨%γ, H⟩
    ihave K := (@h (IProp GV) _ _ _ _ Bool ∅ ∅ iprop(∀ a : Bool, γ ↪VAR{.discard} a)
      (fun a => iprop(γ ↪VAR{.discard} a)) ⟨fun _ h => h⟩ inferInstance).from_forall
    iapply (step_fupd_mono (gv_both γ))
    iapply K
    iintro %a
    iapply ((gv_disc ∅ γ a).trans (BIFUpdate.mono (fupd_intro.trans later_intro)))
    iexact H
