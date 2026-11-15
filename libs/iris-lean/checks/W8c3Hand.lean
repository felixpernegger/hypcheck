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

namespace W8c3
open Iris Iris.BI Iris.Std Iris.ProofMode Iris.OFE

abbrev sT : SiProp := iprop(True)
abbrev sF : SiProp := iprop(False)

/-- Identity basic update on SiProp (lawful). -/
@[reducible] def idBupd : BIUpdate SiProp where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h

/-- Constant-True basic update on SiProp (lawful, not BIBUpdateSbi). -/
@[reducible] def topBupd : BIUpdate SiProp where
  bupd _ := iprop(True)
  bupd_ne := ⟨fun _ _ _ _ _ _ => Iff.rfl⟩
  intro := fun _ _ => trivial
  mono _ := fun _ h => h
  trans := fun _ h => h
  frame_right := fun _ _ => trivial

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF

theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩

/-- fupd soundness with arbitrary masks (copied from W6c1). -/
theorem fupd_false (E1 E2 : CoPset) (H : ∀ [InvGS_gen .hasNoLC CGF], ⊢ (iprop(|={E1,E2}=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := E1) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))

/-- step-fupd soundness at empty masks (copied from W6c1). -/
theorem step_false (H : ∀ [InvGS_gen .hasNoLC CGF], ⊢ (iprop(|={∅}[∅]▷=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (step_fupdN_soundness (hlc := .hasNoLC) 1 0 (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (H.trans (fupd_mask_intro_discard LawfulSet.empty_subset))))

/-- No mask-opening update from the empty mask to top is provable (copied from W6c1). -/
theorem open_top_false (H0 : ∀ [InvGS_gen .hasNoLC CGF], ∃ Q : IProp CGF, ⊢ |={∅,⊤}=> Q) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ => by
      obtain ⟨Q, H⟩ := H0
      have H2 := H.trans (BIFUpdate.mono (Q := iprop(⌜(⊤ : CoPset) ## ⊤⌝ → ⌜False⌝)) (by
        iintro _ %hd
        exact absurd hd full_not_disj))
      have H3 := H2.trans (fupd_mask_frame_right_strong (E1 := ∅) (E2 := ⊤) (Ef := ⊤) (fun x ⟨h1, _⟩ => CoPset.mem_empty h1))
      have e1 : (∅ ∪ ⊤ : CoPset) = ⊤ := rfl
      have e2 : (⊤ ∪ ⊤ : CoPset) = ⊤ := rfl
      rw [e1, e2] at H3
      exact wand_intro (sep_elim_left.trans H3))

/-- Constant-True basic update on IProp (copied from W6c1). -/
@[reducible] noncomputable def topBupdI : BIUpdate (IProp CGF) where
  bupd _ := iprop(True)
  bupd_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  intro := true_intro
  mono _ := .rfl
  trans := .rfl
  frame_right := true_intro

/-- emp entails a top-mask update of True. -/
theorem fT [InvGS_gen .hasNoLC CGF] (E : CoPset) : (emp : IProp CGF) ⊢ iprop(|={E}=> True) :=
  true_intro.trans fupd_intro

/-- Two-element UORA with equality order (copied from W6c1): UPred NA is a non-affine BI. -/
inductive NA | e | a deriving DecidableEq

def NA.op : NA → NA → NA
  | .e, y => y
  | .a, _ => .a

instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨id⟩

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

instance : OrderRefl NA := ⟨fun x => show x = x from rfl⟩

instance instUORA : UORA NA where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

theorem na_true_not_emp : ¬ ((iprop(True) : UPred NA) ⊢ iprop(emp)) := fun h => by
  have H := h 0 ⟨.a, trivial⟩ trivial
  cases H

instance naPlainEmp : Plain (iprop(emp) : UPred NA) := ⟨fun _ _ _ => rfl⟩

theorem na_upd_emp : (iprop(True) : UPred NA) ⊢ iprop(|==> emp) :=
  fun _ _ _ _ _ _ _ => ⟨.e, trivial, rfl⟩

/-- In UPred NA: True entails (update to emp) * (emp -* emp). -/
theorem na_lhs : (iprop(True) : UPred NA) ⊢ iprop((|==> emp) ∗ (emp -∗ emp)) :=
  (na_upd_emp.trans sep_emp.2).trans (sep_mono .rfl (wand_intro emp_sep.1))

open Iris.Instances in
theorem cr_upd : (iprop(True) : UPred Credit) ⊢ iprop(|==> UPred.ownM (1 : Credit)) :=
  (UPred.ownM_unit' (M := Credit)).2.trans (UPred.bupd_ownM_update (fun _ _ _ => trivial))

open Iris.Instances in
theorem cr_bad (h : (iprop(True) : UPred Credit) ⊢ UPred.ownM (1 : Credit)) : False := by
  have := h 0 ⟨0, trivial⟩ trivial
  simp [UPred.ownM] at this
  obtain ⟨z, hz⟩ := this
  have hz' : (0 : Nat) = 1 + z := hz
  omega

open Iris.Instances in
/-- In UPred Credit: True entails (update to ownM 1) * (ownM 1 -* ownM 1). -/
theorem cr_lhs : (iprop(True) : UPred Credit) ⊢ iprop((|==> UPred.ownM (1 : Credit)) ∗ (UPred.ownM (1 : Credit) -∗ UPred.ownM (1 : Credit))) :=
  (cr_upd.trans sep_emp.2).trans (sep_mono .rfl (wand_intro emp_sep.1))

macro "fin " H:ident : tactic => `(tactic| first
  | exact $H 0 trivial
  | exact $H 0 ⟨trivial, trivial⟩
  | exact $H 0 (Or.inl trivial)
  | exact ($H 0 trivial).1
  | exact ($H 0 trivial).elim id id
  | exact $H 0 trivial 0 (Nat.le_refl 0) trivial
  | exact $H 0 ⟨trivial, fun _ _ h => h⟩
  | exact $H 0 (SiProp.exists_holds.2 ⟨trivial, trivial⟩)
  | exact SiProp.forall_holds.1 ($H 0 trivial) trivial
  | (have H0 := $H 0; simp at H0; done))

-- `Iris.ProofMode.fromAssumption_bupd` idx 7: necessary (SiProp, identity bupd: P=True, Q=False)
theorem w8c3_0 : ¬ drop0% Iris.ProofMode.fromAssumption_bupd 7 := fun h => by
  have H := (@h SiProp _ idBupd false .in sT sF).1; fin H
-- `Iris.ProofMode.fromPure_bupd` idx 7: necessary (SiProp, identity bupd: P=False, phi=True)
theorem w8c3_1 : ¬ drop0% Iris.ProofMode.fromPure_bupd 7 := fun h => by
  have H := (@h SiProp _ idBupd .in false sF True).1; fin H
-- `Iris.ProofMode.intoWand_bupd_args` idx 9: necessary (SiProp, identity bupd: R=P=True, Q=False)
theorem w8c3_2 : ¬ drop0% Iris.ProofMode.intoWand_bupd_args 9 := fun h => by
  have H := (@h SiProp _ idBupd false false .argument sT sT sF).1; fin H
-- `Iris.ProofMode.intoWand_bupd_persistent` idx 9: necessary (SiProp, identity bupd: R=P=True, Q=False)
theorem w8c3_3 : ¬ drop0% Iris.ProofMode.intoWand_bupd_persistent 9 := fun h => by
  have H := (@h SiProp _ idBupd false false .unknown sT sT sF).1; fin H
-- `Iris.ProofMode.fromSep_bupd` idx 6: necessary (SiProp, identity bupd: P=False, Q1=Q2=True)
theorem w8c3_4 : ¬ drop0% Iris.ProofMode.fromSep_bupd 6 := fun h => by
  have H := (@h SiProp _ idBupd sF sT sT).1; fin H
-- `Iris.ProofMode.fromOr_bupd` idx 6: necessary (SiProp, identity bupd: P=False, Q1=Q2=True)
theorem w8c3_5 : ¬ drop0% Iris.ProofMode.fromOr_bupd 6 := fun h => by
  have H := (@h SiProp _ idBupd sF sT sT).1; fin H
-- `Iris.ProofMode.intoAnd_bupd` idx 6: necessary (SiProp, identity bupd: P=True, Q1=Q2=False)
theorem w8c3_6 : ¬ drop0% Iris.ProofMode.intoAnd_bupd 6 := fun h => by
  have H := (@h SiProp _ idBupd sT sF sF).1; fin H
-- `Iris.ProofMode.fromExists_bupd` idx 6: necessary (SiProp, identity bupd: P=False, Phi=True)
theorem w8c3_7 : ¬ drop0% Iris.ProofMode.fromExists_bupd 6 := fun h => by
  have H := (@h SiProp _ idBupd True sF (fun _ => sT)).1; fin H
-- `Iris.ProofMode.intoForall_bupd` idx 6: necessary (SiProp, identity bupd: P=True, Phi=False)
theorem w8c3_8 : ¬ drop0% Iris.ProofMode.intoForall_bupd 6 := fun h => by
  have H := (@h SiProp _ idBupd True sT (fun _ => sF)).1; fin H
-- `Iris.ProofMode.isExcept0_bupd` idx 4: necessary (SiProp, identity bupd: P=False (except0 False holds at step 0))
theorem w8c3_9 : ¬ drop0% Iris.ProofMode.isExcept0_bupd 4 := fun h => by
  have H := (@h SiProp _ idBupd sF).1; fin H
-- `Iris.ProofMode.elimModal_bupd_plain_goal` idx 3: necessary (SiProp with constant-True bupd (lawful, not BIBUpdateSbi): P=Q=False)
theorem w8c3_10 : ¬ drop0% Iris.ProofMode.elimModal_bupd_plain_goal 3 := fun h => by
  have H := (@h SiProp _ topBupd _ false .in sF sF _).1 trivial; fin H
-- `Iris.ProofMode.elimModal_bupd_plain_goal` idx 4: necessary (non-affine UPred NA (library bupd, BIBUpdateSbi): P=Q=emp (plain, not absorbing); |==> emp holds at a)
theorem w8c3_11 : ¬ drop0% Iris.ProofMode.elimModal_bupd_plain_goal 4 := fun h => by
  have H := (@h (UPred NA) _ _ _ false .in iprop(emp) iprop(emp) naPlainEmp).1 trivial; exact na_true_not_emp (na_lhs.trans H)
-- `Iris.ProofMode.elimModal_bupd_plain_goal` idx 9: necessary (affine UPred Credit: P=Q=ownM 1 (not plain): 0 updates to 1)
theorem w8c3_12 : ¬ drop0% Iris.ProofMode.elimModal_bupd_plain_goal 9 := fun h => by
  have H := (@h (UPred Credit) _ _ _ _ false .in (UPred.ownM (1 : Credit)) (UPred.ownM (1 : Credit))).1 trivial; exact cr_bad (cr_lhs.trans H)
-- `Iris.ProofMode.elimModal_bupd_plain` idx 3: necessary (SiProp with constant-True bupd (lawful, not BIBUpdateSbi): P=Q=False)
theorem w8c3_13 : ¬ drop0% Iris.ProofMode.elimModal_bupd_plain 3 := fun h => by
  have H := (@h SiProp _ topBupd _ false .in sF sF _).1 trivial; fin H
-- `Iris.ProofMode.elimModal_bupd_plain` idx 4: necessary (non-affine UPred NA (library bupd, BIBUpdateSbi): P=Q=emp (plain, not absorbing); |==> emp holds at a)
theorem w8c3_14 : ¬ drop0% Iris.ProofMode.elimModal_bupd_plain 4 := fun h => by
  have H := (@h (UPred NA) _ _ _ false .in iprop(emp) iprop(emp) naPlainEmp).1 trivial; exact na_true_not_emp (na_lhs.trans H)
-- `Iris.ProofMode.elimModal_bupd_plain` idx 9: necessary (affine UPred Credit: P=Q=ownM 1 (not plain): 0 updates to 1)
theorem w8c3_15 : ¬ drop0% Iris.ProofMode.elimModal_bupd_plain 9 := fun h => by
  have H := (@h (UPred Credit) _ _ _ _ false .in (UPred.ownM (1 : Credit)) (UPred.ownM (1 : Credit))).1 trivial; exact cr_bad (cr_lhs.trans H)
-- `Iris.ProofMode.fromAssumption_fupd` idx 4: necessary (IProp with constant-True bupd (no BIUpdateFUpdate): P=True, Q=False; fupd soundness)
theorem w8c3_16 : ¬ drop0% Iris.ProofMode.fromAssumption_fupd 4 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => true_intro.trans (@h (IProp CGF) _ topBupdI _ ⊤ false .in iprop(True) iprop(⌜False⌝) ⟨true_intro⟩).1
-- `Iris.ProofMode.fromAssumption_fupd` idx 10: necessary (IProp: P=True, Q=False; fupd soundness)
theorem w8c3_17 : ¬ drop0% Iris.ProofMode.fromAssumption_fupd 10 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => true_intro.trans (@h (IProp CGF) _ _ _ _ ⊤ false .in iprop(True) iprop(⌜False⌝)).1
-- `Iris.ProofMode.fromPure_fupd` idx 8: necessary (IProp: P=False, phi=True; fupd soundness)
theorem w8c3_18 : ¬ drop0% Iris.ProofMode.fromPure_fupd 8 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (pure_intro trivial).trans (@h (IProp CGF) _ _ .in ⊤ false iprop(⌜False⌝) True).1
-- `Iris.ProofMode.intoWand_fupd` idx 10: necessary (IProp: R=P=True, Q=False; fupd soundness)
theorem w8c3_19 : ¬ drop0% Iris.ProofMode.intoWand_fupd 10 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (emp_sep.2.trans (sep_mono ((fT ⊤).trans (@h (IProp CGF) _ _ ⊤ false false .unknown iprop(True) iprop(True) iprop(⌜False⌝)).1) (fT ⊤))).trans wand_elim_left
-- `Iris.ProofMode.intoWand_fupd_persistent` idx 11: necessary (IProp: R=P=True, Q=False; fupd soundness)
theorem w8c3_20 : ¬ drop0% Iris.ProofMode.intoWand_fupd_persistent 11 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (emp_sep.2.trans (sep_mono ((fT ⊤).trans (@h (IProp CGF) _ _ ⊤ ⊤ false false .unknown iprop(True) iprop(True) iprop(⌜False⌝)).1) true_intro)).trans wand_elim_left
-- `Iris.ProofMode.intoWand_fupd_args` idx 11: necessary (IProp: R=P=True, Q=False; fupd soundness)
theorem w8c3_21 : ¬ drop0% Iris.ProofMode.intoWand_fupd_args 11 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (emp_sep.2.trans (sep_mono (true_intro.trans (@h (IProp CGF) _ _ ⊤ ⊤ false false .argument iprop(True) iprop(True) iprop(⌜False⌝)).1) (fT ⊤))).trans wand_elim_left
-- `Iris.ProofMode.fromSep_fupd` idx 7: necessary (IProp: P=False, Q1=Q2=True; fupd soundness)
theorem w8c3_22 : ¬ drop0% Iris.ProofMode.fromSep_fupd 7 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (emp_sep.2.trans (sep_mono (fT ⊤) (fT ⊤))).trans (@h (IProp CGF) _ _ ⊤ iprop(⌜False⌝) iprop(True) iprop(True)).1
-- `Iris.ProofMode.fromOr_fupd` idx 8: necessary (IProp: P=False, Q1=Q2=True; fupd soundness)
theorem w8c3_23 : ¬ drop0% Iris.ProofMode.fromOr_fupd 8 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => ((fT ⊤).trans or_intro_l).trans (@h (IProp CGF) _ _ ⊤ ⊤ iprop(⌜False⌝) iprop(True) iprop(True)).1
-- `Iris.ProofMode.intoAnd_fupd` idx 8: necessary (IProp: P=True, Q1=Q2=False; fupd soundness)
theorem w8c3_24 : ¬ drop0% Iris.ProofMode.intoAnd_fupd 8 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => ((fT ⊤).trans (@h (IProp CGF) _ _ ⊤ ⊤ iprop(True) iprop(⌜False⌝) iprop(⌜False⌝)).1).trans and_elim_l
-- `Iris.ProofMode.fromExists_fupd` idx 8: necessary (IProp: P=False, Phi=True; fupd soundness)
theorem w8c3_25 : ¬ drop0% Iris.ProofMode.fromExists_fupd 8 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => ((fT ⊤).trans (exists_intro (Ψ := fun _ : True => iprop(|={⊤}=> True)) trivial)).trans (@h (IProp CGF) _ _ True ⊤ ⊤ iprop(⌜False⌝) (fun _ => iprop(True))).1
-- `Iris.ProofMode.intoForall_fupd` idx 8: necessary (IProp: P=True, Phi=False; fupd soundness)
theorem w8c3_26 : ¬ drop0% Iris.ProofMode.intoForall_fupd 8 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => ((fT ⊤).trans (@h (IProp CGF) _ _ True ⊤ ⊤ iprop(True) (fun _ => iprop(⌜False⌝))).1).trans (forall_elim trivial)
-- `Iris.ProofMode.elimModal_bupd_fupd` idx 4: necessary (IProp with constant-True bupd (no BIUpdateFUpdate): P=Q=False; fupd soundness)
theorem w8c3_27 : ¬ drop0% Iris.ProofMode.elimModal_bupd_fupd 4 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (emp_sep.2.trans (sep_mono true_intro (wand_intro (sep_elim_right.trans (pure_elim' False.elim))))).trans ((@h (IProp CGF) _ topBupdI _ false .in ⊤ ⊤ iprop(⌜False⌝) iprop(⌜False⌝)).1 trivial)
-- `Iris.ProofMode.fromForall_fupd` idx 11: necessary (IProp: alpha=Empty, P=False; fupd soundness)
theorem w8c3_28 : ¬ drop0% Iris.ProofMode.fromForall_fupd 11 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (forall_intro fun a => a.elim).trans (@h (IProp CGF) _ _ _ _ ⊤ ⊤ iprop(⌜False⌝) Empty Empty.elim ⟨CoPset.subseteq_refl⟩ (fun a => a.elim)).1
-- `Iris.ProofMode.fromForall_stepFupd` idx 11: necessary (IProp: alpha=False, masks empty, P=False; step-fupd soundness)
theorem w8c3_29 : ¬ drop0% Iris.ProofMode.fromForall_stepFupd 11 := fun h => by
  exact step_false fun {_} => (forall_intro fun a => a.elim).trans (@h (IProp CGF) _ _ _ _ False ∅ ∅ iprop(⌜False⌝) (fun a => a.elim) ⟨CoPset.subseteq_refl⟩ (fun a => a.elim)).1
-- `Iris.ProofMode.fromForall_fupd` idx 10: necessary (IProp: E1=empty, E2=top, alpha=Empty, P=True: gives |={empty,top}=> True)
theorem w8c3_30 : ¬ drop0% Iris.ProofMode.fromForall_fupd 10 := fun h => by
  exact open_top_false fun {_} => ⟨_, (forall_intro fun a => a.elim).trans (@h (IProp CGF) _ _ _ _ ∅ ⊤ iprop(True) Empty Empty.elim ⟨true_intro⟩ (fun a => a.elim)).1⟩
-- `Iris.ProofMode.fromForall_stepFupd` idx 10: necessary (IProp: E1=empty, E2=top, alpha=False, P=True: gives |={empty,top}=> _)
theorem w8c3_31 : ¬ drop0% Iris.ProofMode.fromForall_stepFupd 10 := fun h => by
  exact open_top_false fun {_} => ⟨_, (forall_intro fun a => a.elim).trans (@h (IProp CGF) _ _ _ _ False ∅ ⊤ iprop(True) (fun a => a.elim) ⟨true_intro⟩ (fun a => a.elim)).1⟩
-- `Iris.ProofMode.Modality.mono` idx 7: necessary (SiProp, identity modality: P=True, Q=False)
theorem w8c3_32 : ¬ drop0% Iris.ProofMode.Modality.mono 7 := fun h => by
  have H := (@h SiProp SiProp _ _ modality_id sT sF); fin H

/-- A satisfiable predicate on Nat has a least witness (classical, no Mathlib). -/
theorem exMin (Q : Nat → Prop) (n : Nat) (hn : Q n) : ∃ m, Q m ∧ ∀ k, k < m → ¬ Q k := by
  classical
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : ∃ k, k < n ∧ Q k
    · obtain ⟨k, hk, pk⟩ := h; exact ih k hk pk
    · exact ⟨n, hn, fun k hk pk => h ⟨k, hk, pk⟩⟩

/-- In an affine Sbi, a family of plain propositions over a nonempty type has a least member:
the step-indexed contents siEmpValid of plain propositions are initial segments of Nat. -/
theorem minPlain {PROP : Type _} [Sbi PROP] [BIAffine PROP] {α : Sort _} (Φ : α → PROP)
    [hp : ∀ a, Plain (Φ a)] (a : α) : ∃ a0, ∀ b, Φ a0 ⊢ Φ b := by
  classical
  let s : α → SiProp := fun b => siEmpValid (Φ b)
  have key : ∃ a0, ∀ b, s a0 ⊢ s b := by
    by_cases hex : ∃ n, ∃ b, ¬ (s b).holds n
    · obtain ⟨n, hn⟩ := hex
      obtain ⟨n0, ⟨b0, hb0⟩, hmin⟩ := exMin (fun n => ∃ b, ¬ (s b).holds n) n hn
      refine ⟨b0, fun b m hm => ?_⟩
      have hlt : m < n0 := Nat.lt_of_not_le fun hle => hb0 ((s b0).closed hm hle)
      exact Classical.byContradiction fun hn => hmin m hlt ⟨b, hn⟩
    · exact ⟨a, fun b m _ => Classical.byContradiction fun hn => hex ⟨m, b, hn⟩⟩
  obtain ⟨a0, ha0⟩ := key
  exact ⟨a0, fun b => (hp a0).plain.trans ((siPure_mono (ha0 b)).trans
    (siPure_siEmpValid.trans persistently_elim))⟩

-- `Iris.ProofMode.fromForall_fupd` idx 3: removable (plain props are siPure of initial segments of Nat, so a nonempty family has a least member a0 and the fupd of the forall follows from the fupd of Φ a0 by monotonicity; empty alpha by mask_intro_discard)
theorem w8c3_r1 : drop% Iris.ProofMode.fromForall_fupd 3 := by
  intro PROP _ _ _ E1 E2 P α Φ inst h hpl
  constructor
  by_cases hα : Nonempty α
  · obtain ⟨a⟩ := hα
    obtain ⟨a0, ha0⟩ := minPlain Φ a
    exact (forall_elim a0).trans (BIFUpdate.mono ((forall_intro ha0).trans h.from_forall))
  · exact (forall_intro fun a => (hα ⟨a⟩).elim).trans
      (h.from_forall.trans (fupd_mask_intro_discard inst.sidecondition))

-- `Iris.ProofMode.fromForall_stepFupd` idx 3: removable (same least-member argument with step_fupd_mono; empty alpha by step_fupd_intro)
theorem w8c3_r2 : drop% Iris.ProofMode.fromForall_stepFupd 3 := by
  intro PROP _ _ _ α E1 E2 P Φ inst h hpl
  constructor
  by_cases hα : Nonempty α
  · obtain ⟨a⟩ := hα
    obtain ⟨a0, ha0⟩ := minPlain Φ a
    exact (forall_elim a0).trans (step_fupd_mono ((forall_intro ha0).trans h.from_forall))
  · exact (forall_intro fun a => (hα ⟨a⟩).elim).trans
      (h.from_forall.trans (later_intro.trans (step_fupd_intro inst.sidecondition)))
end W8c3
