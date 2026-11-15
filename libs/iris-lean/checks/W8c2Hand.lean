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

namespace W8c2
open Iris Iris.BI Iris.ProofMode

/-- SiProp true only at step 0. -/
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩
/-- SiProp true at steps 0 and 1. -/
def s1 : SiProp := ⟨fun n => n ≤ 1, fun h hle => by omega⟩

end W8c2

section
open Iris Iris.BI Iris.ProofMode W8c2

-- `Iris.ProofMode.fromAssumption_later` idx 6: necessary (SiProp step 1: p=false, P=True, Q=False)
theorem w8c2_1 : ¬ drop0% Iris.ProofMode.fromAssumption_later 6 := fun h =>
  (@h SiProp .in _ false iprop(True) iprop(False)).from_assumption 1 trivial

-- `Iris.ProofMode.fromAssumption_laterN` idx 7: necessary (SiProp: n=0, p=false, P=True, Q=False)
theorem w8c2_2 : ¬ drop0% Iris.ProofMode.fromAssumption_laterN 7 := fun h =>
  (@h SiProp .in _ 0 false iprop(True) iprop(False)).from_assumption 0 trivial

-- `Iris.ProofMode.fromAssumption_except0` idx 6: necessary (SiProp step 1: p=false, P=True, Q=False)
theorem w8c2_3 : ¬ drop0% Iris.ProofMode.fromAssumption_except0 6 := fun h =>
  ((@h SiProp .in _ false iprop(True) iprop(False)).from_assumption 1 trivial).elim id id

-- `Iris.ProofMode.fromAssumption_later_laterN` idx 6: necessary (SiProp step 1: n=0, p=false, P=True, Q=False)
theorem w8c2_4 : ¬ drop0% Iris.ProofMode.fromAssumption_later_laterN 6 := fun h =>
  (@h SiProp _ 0 false iprop(True) iprop(False)).from_assumption 1 trivial

-- `Iris.ProofMode.fromPure_later` idx 6: necessary (SiProp step 1: a=false, P=False, phi=True)
theorem w8c2_5 : ¬ drop0% Iris.ProofMode.fromPure_later 6 := fun h =>
  (@h SiProp .in _ false iprop(False) True).from_pure 1 trivial

-- `Iris.ProofMode.fromPure_except0` idx 6: necessary (SiProp step 1: a=false, P=False, phi=True)
theorem w8c2_6 : ¬ drop0% Iris.ProofMode.fromPure_except0 6 := fun h =>
  ((@h SiProp .in _ false iprop(False) True).from_pure 1 trivial).elim id id

-- `Iris.ProofMode.intoWand_later` idx 8: necessary (SiProp step 1: p=q=false, R=P=True, Q=False)
theorem w8c2_7 : ¬ drop0% Iris.ProofMode.intoWand_later 8 := fun h =>
  (@h SiProp (.matching .argument) _ false false iprop(True) iprop(True) iprop(False)).into_wand 1 trivial
    1 (Nat.le_refl 1) trivial

-- `Iris.ProofMode.intoWand_later_args` idx 8: necessary (SiProp step 1: p=q=false, R=P=True, Q=False)
theorem w8c2_8 : ¬ drop0% Iris.ProofMode.intoWand_later_args 8 := fun h =>
  (@h SiProp _ false false .argument iprop(True) iprop(True) iprop(False)).into_wand 1 trivial
    1 (Nat.le_refl 1) trivial

-- `Iris.ProofMode.intoWand_laterN` idx 9: necessary (SiProp: n=0, p=q=false, R=P=True, Q=False)
theorem w8c2_9 : ¬ drop0% Iris.ProofMode.intoWand_laterN 9 := fun h =>
  (@h SiProp (.matching .argument) _ 0 false false iprop(True) iprop(True) iprop(False)).into_wand 0 trivial
    0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_laterN_args` idx 9: necessary (SiProp: n=0, p=q=false, R=P=True, Q=False)
theorem w8c2_10 : ¬ drop0% Iris.ProofMode.intoWand_laterN_args 9 := fun h =>
  (@h SiProp _ 0 false false .argument iprop(True) iprop(True) iprop(False)).into_wand 0 trivial
    0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromAnd_later` idx 5: necessary (SiProp step 1: P=False, Q1=Q2=True)
theorem w8c2_11 : ¬ drop0% Iris.ProofMode.fromAnd_later 5 := fun h =>
  (@h SiProp _ iprop(False) iprop(True) iprop(True)).from_and 1 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAnd_laterN` idx 6: necessary (SiProp: n=0, P=False, Q1=Q2=True)
theorem w8c2_12 : ¬ drop0% Iris.ProofMode.fromAnd_laterN 6 := fun h =>
  (@h SiProp _ 0 iprop(False) iprop(True) iprop(True)).from_and 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAnd_except0` idx 5: necessary (SiProp step 1: P=False, Q1=Q2=True)
theorem w8c2_13 : ¬ drop0% Iris.ProofMode.fromAnd_except0 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_and 1 ⟨Or.inr trivial, Or.inr trivial⟩).elim id id

-- `Iris.ProofMode.fromSep_later` idx 5: necessary (SiProp step 1: P=False, Q1=Q2=True)
theorem w8c2_14 : ¬ drop0% Iris.ProofMode.fromSep_later 5 := fun h =>
  (@h SiProp _ iprop(False) iprop(True) iprop(True)).from_sep 1 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromSep_laterN` idx 6: necessary (SiProp: n=0, P=False, Q1=Q2=True)
theorem w8c2_15 : ¬ drop0% Iris.ProofMode.fromSep_laterN 6 := fun h =>
  (@h SiProp _ 0 iprop(False) iprop(True) iprop(True)).from_sep 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromSep_except0` idx 5: necessary (SiProp step 1: P=False, Q1=Q2=True)
theorem w8c2_16 : ¬ drop0% Iris.ProofMode.fromSep_except0 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_sep 1 ⟨Or.inr trivial, Or.inr trivial⟩).elim id id

-- `Iris.ProofMode.intoAnd_later` idx 6: necessary (SiProp step 1: p=false, P=Q2=True, Q1=False)
theorem w8c2_17 : ¬ drop0% Iris.ProofMode.intoAnd_later 6 := fun h =>
  ((@h SiProp _ false iprop(True) iprop(False) iprop(True)).into_and 1 trivial).1

-- `Iris.ProofMode.intoAnd_laterN` idx 7: necessary (SiProp: n=0, p=false, P=Q2=True, Q1=False)
theorem w8c2_18 : ¬ drop0% Iris.ProofMode.intoAnd_laterN 7 := fun h =>
  ((@h SiProp _ 0 false iprop(True) iprop(False) iprop(True)).into_and 0 trivial).1

-- `Iris.ProofMode.intoAnd_except0` idx 7: necessary (SiProp step 1: p=false, P=Q2=True, Q1=False)
theorem w8c2_19 : ¬ drop0% Iris.ProofMode.intoAnd_except0 7 := fun h =>
  ((@h SiProp _ _ false iprop(True) iprop(False) iprop(True)).into_and 1 (Or.inr trivial)).1.elim id id

-- `Iris.ProofMode.intoSep_later` idx 5: necessary (SiProp step 1: P=Q2=True, Q1=False)
theorem w8c2_20 : ¬ drop0% Iris.ProofMode.intoSep_later 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True)).into_sep 1 trivial).1

-- `Iris.ProofMode.intoSep_laterN` idx 6: necessary (SiProp: n=0, P=Q2=True, Q1=False)
theorem w8c2_21 : ¬ drop0% Iris.ProofMode.intoSep_laterN 6 := fun h =>
  ((@h SiProp _ 0 iprop(True) iprop(False) iprop(True)).into_sep 0 trivial).1

-- `Iris.ProofMode.intoSep_except0` idx 5: necessary (SiProp step 1: P=Q2=True, Q1=False)
theorem w8c2_22 : ¬ drop0% Iris.ProofMode.intoSep_except0 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True)).into_sep 1 (Or.inr trivial)).1.elim id id

-- `Iris.ProofMode.intoSep_affinely_later` idx 6: necessary (SiProp step 1: P=Q2=True, Q1=False)
theorem w8c2_23 : ¬ drop0% Iris.ProofMode.intoSep_affinely_later 6 := fun h =>
  ((@h SiProp _ _ iprop(True) iprop(False) iprop(True) _ _).into_sep 1 ⟨trivial, trivial⟩).1.2

-- `Iris.ProofMode.fromOr_later` idx 5: necessary (SiProp step 1: P=False, Q1=Q2=True)
theorem w8c2_24 : ¬ drop0% Iris.ProofMode.fromOr_later 5 := fun h =>
  (@h SiProp _ iprop(False) iprop(True) iprop(True)).from_or 1 (Or.inl trivial)

-- `Iris.ProofMode.fromOr_laterN` idx 6: necessary (SiProp: n=0, P=False, Q1=Q2=True)
theorem w8c2_25 : ¬ drop0% Iris.ProofMode.fromOr_laterN 6 := fun h =>
  (@h SiProp _ 0 iprop(False) iprop(True) iprop(True)).from_or 0 (Or.inl trivial)

-- `Iris.ProofMode.fromOr_except0` idx 5: necessary (SiProp step 1: P=False, Q1=Q2=True)
theorem w8c2_26 : ¬ drop0% Iris.ProofMode.fromOr_except0 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_or 1 (Or.inl (Or.inr trivial))).elim id id

-- `Iris.ProofMode.intoOr_later` idx 5: necessary (SiProp step 1: P=True, Q1=Q2=False)
theorem w8c2_27 : ¬ drop0% Iris.ProofMode.intoOr_later 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(False)).into_or 1 trivial).elim id id

-- `Iris.ProofMode.intoOr_laterN` idx 6: necessary (SiProp: n=0, P=True, Q1=Q2=False)
theorem w8c2_28 : ¬ drop0% Iris.ProofMode.intoOr_laterN 6 := fun h =>
  ((@h SiProp _ 0 iprop(True) iprop(False) iprop(False)).into_or 0 trivial).elim id id

-- `Iris.ProofMode.intoOr_except0` idx 5: necessary (SiProp step 1: P=True, Q1=Q2=False)
theorem w8c2_29 : ¬ drop0% Iris.ProofMode.intoOr_except0 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(False)).into_or 1 (Or.inr trivial)).elim
    (fun h1 => h1.elim id id) (fun h1 => h1.elim id id)
end

section
open Iris Iris.BI Iris.ProofMode W8c2

-- `Iris.ProofMode.fromExists_laterN` idx 6: necessary (SiProp: n=0, P=False, Phi=True)
theorem w8c2_30 : ¬ drop0% Iris.ProofMode.fromExists_laterN 6 := fun h =>
  (@h SiProp True _ 0 iprop(False) (fun _ => iprop(True))).from_exists 0
    (SiProp.exists_holds.2 ⟨trivial, trivial⟩)

-- `Iris.ProofMode.fromExists_except0` idx 5: necessary (SiProp step 1: P=False, Phi=True)
theorem w8c2_31 : ¬ drop0% Iris.ProofMode.fromExists_except0 5 := fun h =>
  ((@h SiProp True _ iprop(False) (fun _ => iprop(True))).from_exists 1
    (SiProp.exists_holds.2 ⟨trivial, Or.inr trivial⟩)).elim id id

-- `Iris.ProofMode.intoExists_laterN` idx 7: necessary (SiProp: n=0, P=True, Phi=False)
theorem w8c2_32 : ¬ drop0% Iris.ProofMode.intoExists_laterN 7 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp True _ ⟨trivial⟩ 0 iprop(True) (fun _ => iprop(False))).into_exists 0 trivial) with
  | ⟨_, hx⟩ => hx

-- `Iris.ProofMode.intoExists_except0` idx 6: necessary (SiProp step 1: P=True, Phi=False)
theorem w8c2_33 : ¬ drop0% Iris.ProofMode.intoExists_except0 6 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp True _ ⟨trivial⟩ iprop(True) (fun _ => iprop(False))).into_exists 1
    (Or.inr trivial)) with
  | ⟨_, hx⟩ => hx.elim id id

-- `Iris.ProofMode.intoForall_later` idx 5: necessary (SiProp step 1: P=True, Phi=False)
theorem w8c2_34 : ¬ drop0% Iris.ProofMode.intoForall_later 5 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp True _ iprop(True) (fun _ => iprop(False))).into_forall 1 trivial) trivial

-- `Iris.ProofMode.intoForall_laterN` idx 6: necessary (SiProp: n=0, P=True, Phi=False)
theorem w8c2_35 : ¬ drop0% Iris.ProofMode.intoForall_laterN 6 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp True _ 0 iprop(True) (fun _ => iprop(False))).into_forall 0 trivial) trivial

-- `Iris.ProofMode.intoForall_except0` idx 5: necessary (SiProp step 1: P=True, Phi=False)
theorem w8c2_36 : ¬ drop0% Iris.ProofMode.intoForall_except0 5 := fun h =>
  (SiProp.forall_holds.1 ((@h SiProp True _ iprop(True) (fun _ => iprop(False))).into_forall 1
    (Or.inr trivial)) trivial).elim id id

-- `Iris.ProofMode.fromForall_later` idx 5: necessary (SiProp step 1: P=False, Phi=True)
theorem w8c2_37 : ¬ drop0% Iris.ProofMode.fromForall_later 5 := fun h =>
  (@h SiProp True _ iprop(False) (fun _ => iprop(True))).from_forall 1 (SiProp.forall_holds.2 fun _ => trivial)

-- `Iris.ProofMode.fromForall_laterN` idx 6: necessary (SiProp: n=0, P=False, Phi=True)
theorem w8c2_38 : ¬ drop0% Iris.ProofMode.fromForall_laterN 6 := fun h =>
  (@h SiProp True _ 0 iprop(False) (fun _ => iprop(True))).from_forall 0 (SiProp.forall_holds.2 fun _ => trivial)

-- `Iris.ProofMode.fromForall_except0` idx 5: necessary (SiProp step 1: P=False, Phi=True)
theorem w8c2_39 : ¬ drop0% Iris.ProofMode.fromForall_except0 5 := fun h =>
  ((@h SiProp True _ iprop(False) (fun _ => iprop(True))).from_forall 1
    (SiProp.forall_holds.2 fun _ => Or.inr trivial)).elim id id

-- `Iris.ProofMode.intoExcept0_laterIf` idx 4: necessary (SiProp step 1: p=true, P=s0 true only at step 0)
theorem w8c2_40 : ¬ drop0% Iris.ProofMode.intoExcept0_laterIf 4 := fun h =>
  ((@h SiProp _ true s0).into_except0 1 (show (0:Nat) = 0 from rfl)).elim id
    (fun h1 => absurd (show (1:Nat) = 0 from h1) (by decide))

-- `Iris.ProofMode.intoExcept0_affinely` idx 4: necessary (SiProp step 1: P=True, Q=False)
theorem w8c2_41 : ¬ drop0% Iris.ProofMode.intoExcept0_affinely 4 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False)).into_except0 1 ⟨trivial, trivial⟩).elim id (·.2)

-- `Iris.ProofMode.intoExcept0_intuitionistically` idx 5: necessary (SiProp step 1: P=True, Q=False)
theorem w8c2_42 : ¬ drop0% Iris.ProofMode.intoExcept0_intuitionistically 5 := fun h =>
  ((@h SiProp _ _ iprop(True) iprop(False)).into_except0 1 ⟨trivial, trivial⟩).elim id (·.2)

-- `Iris.ProofMode.intoExcept0_absorbingly` idx 4: necessary (SiProp step 1: P=True, Q=False)
theorem w8c2_43 : ¬ drop0% Iris.ProofMode.intoExcept0_absorbingly 4 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False)).into_except0 1 ⟨trivial, trivial⟩).elim id (·.2)

-- `Iris.ProofMode.intoExcept0_persistently` idx 5: necessary (SiProp step 1: P=True, Q=False)
theorem w8c2_44 : ¬ drop0% Iris.ProofMode.intoExcept0_persistently 5 := fun h =>
  ((@h SiProp _ _ iprop(True) iprop(False)).into_except0 1 trivial).elim id id

-- `Iris.ProofMode.elimModal_timeless` idx 7: necessary (SiProp step 1: p=false, P=True, P'=False, Q=later False)
theorem w8c2_45 : ¬ drop0% Iris.ProofMode.elimModal_timeless 7 := fun h =>
  (@h SiProp _ _ false iprop(True) iprop(False) iprop(▷ False) _).elim_modal trivial 1
    ⟨trivial, fun _ _ hf => hf.elim⟩

-- `Iris.ProofMode.elimModal_timeless` idx 8: necessary (SiProp step 0: p=false, P=later False, P'=Q=False)
theorem w8c2_46 : ¬ drop0% Iris.ProofMode.elimModal_timeless 8 := fun h =>
  (@h SiProp _ _ false iprop(▷ False) iprop(False) iprop(False) ⟨fun _ hl => Or.inl hl⟩).elim_modal trivial 0
    ⟨trivial, fun _ _ hf => hf⟩

-- `Iris.ProofMode.elimModal_timeless_spatial` idx 6: necessary (SiProp step 1: p=false, P=True, P'=False, Q=later False)
theorem w8c2_47 : ¬ drop0% Iris.ProofMode.elimModal_timeless_spatial 6 := fun h =>
  (@h SiProp _ false iprop(True) iprop(False) iprop(▷ False) _).elim_modal trivial 1
    ⟨trivial, fun _ _ hf => hf.elim⟩

-- `Iris.ProofMode.addModal_later_except_0` idx 4: necessary (SiProp step 1: P=s0, Q=False)
theorem w8c2_48 : ¬ drop0% Iris.ProofMode.addModal_later_except_0 4 := fun h =>
  ((@h SiProp _ s0 iprop(False)).add_modal 1
    ⟨show (0:Nat) = 0 from rfl, fun n' _ (hs : n' = 0) => by subst hs; exact Or.inl trivial⟩).elim id id

-- `Iris.ProofMode.addModal_later` idx 4: necessary (SiProp step 1: P=s0, Q=False)
theorem w8c2_49 : ¬ drop0% Iris.ProofMode.addModal_later 4 := fun h =>
  (@h SiProp _ s0 iprop(False)).add_modal 1
    ⟨show (0:Nat) = 0 from rfl, fun n' _ (hs : n' = 0) => by subst hs; exact trivial⟩

-- `Iris.ProofMode.intoLaterN_later` idx 11: necessary (SiProp step 0: n=n'=m'=0, P=Q=lQ=False)
theorem w8c2_50 : ¬ drop0% Iris.ProofMode.intoLaterN_later 11 := fun h =>
  (@h SiProp false _ false false 0 0 0 iprop(False) iprop(False) iprop(False) ⟨fun _ h => h⟩
    ⟨⟨fun _ h => h, fun _ h => h⟩⟩).into_laterN 0 trivial

-- `Iris.ProofMode.intoLaterN_later` idx 12: necessary (SiProp step 1: n=1, n'=m'=0, P=True, Q=lQ=False)
theorem w8c2_51 : ¬ drop0% Iris.ProofMode.intoLaterN_later 12 := fun h =>
  (@h SiProp false _ false false 1 0 0 iprop(True) iprop(False) iprop(False) ⟨rfl⟩
    ⟨⟨fun _ h => h, fun _ h => h⟩⟩).into_laterN 1 trivial

-- `Iris.ProofMode.intoLaterN_later` idx 13: necessary (SiProp step 1: n=1, n'=m'=0, P=Q=True, lQ=False)
theorem w8c2_52 : ¬ drop0% Iris.ProofMode.intoLaterN_later 13 := fun h =>
  (@h SiProp false _ false false 1 0 0 iprop(True) iprop(True) iprop(False) ⟨rfl⟩
    ⟨fun _ h => h⟩).into_laterN 1 trivial

-- `Iris.ProofMode.intoLaterN_laterN` idx 12: necessary (SiProp step 0: m=1, n=n'=m'=0, P=Q=lQ=False)
theorem w8c2_53 : ¬ drop0% Iris.ProofMode.intoLaterN_laterN 12 := fun h =>
  (@h SiProp _ false false false 0 1 0 0 iprop(False) iprop(False) iprop(False) ⟨fun _ h => h⟩
    ⟨⟨fun _ h => h, fun _ h => h⟩⟩).into_laterN 0 trivial

-- `Iris.ProofMode.intoLaterN_laterN` idx 14: necessary (SiProp step 0: all counts 0, P=Q=True, lQ=False)
theorem w8c2_54 : ¬ drop0% Iris.ProofMode.intoLaterN_laterN 14 := fun h =>
  (@h SiProp _ false false false 0 0 0 0 iprop(True) iprop(True) iprop(False) ⟨rfl⟩
    ⟨fun _ h => h⟩).into_laterN 0 trivial

-- `Iris.ProofMode.intoLaterN_laterN_bool` idx 12: necessary (SiProp step 0: p=true, n=n'=m'=0, P=Q=lQ=False)
theorem w8c2_55 : ¬ drop0% Iris.ProofMode.intoLaterN_laterN_bool 12 := fun h =>
  (@h SiProp _ false false false 0 true 0 0 iprop(False) iprop(False) iprop(False) ⟨fun _ h => h⟩
    ⟨⟨fun _ h => h, fun _ h => h⟩⟩).into_laterN 0 trivial

-- `Iris.ProofMode.intoLaterN_laterN_bool` idx 13: necessary (SiProp step 1: p=true, n=1, n'=m'=0, P=True, Q=lQ=False)
theorem w8c2_56 : ¬ drop0% Iris.ProofMode.intoLaterN_laterN_bool 13 := fun h =>
  (@h SiProp _ false false false 1 true 0 0 iprop(True) iprop(False) iprop(False) ⟨rfl⟩
    ⟨⟨fun _ h => h, fun _ h => h⟩⟩).into_laterN 1 trivial

-- `Iris.ProofMode.intoLaterN_laterN_bool` idx 14: necessary (SiProp step 1: p=true, n=1, n'=m'=0, P=Q=True, lQ=False)
theorem w8c2_57 : ¬ drop0% Iris.ProofMode.intoLaterN_laterN_bool 14 := fun h =>
  (@h SiProp _ false false false 1 true 0 0 iprop(True) iprop(True) iprop(False) ⟨rfl⟩
    ⟨fun _ h => h⟩).into_laterN 1 trivial
end

section
open Iris Iris.BI Iris.ProofMode W8c2

-- `Iris.ProofMode.intoLaterN_and_left` idx 8: necessary (SiProp: n=0, P1=P2=Q2=True, Q1=False)
theorem w8c2_58 : ¬ drop0% Iris.ProofMode.intoLaterN_and_left 8 := fun h =>
  ((@h SiProp _ false 0 iprop(True) iprop(True) iprop(False) iprop(True) ⟨fun _ h => h⟩).into_laterN 0
    ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.intoLaterN_and_left` idx 9: necessary (SiProp: n=0, P1=P2=Q1=True, Q2=False)
theorem w8c2_59 : ¬ drop0% Iris.ProofMode.intoLaterN_and_left 9 := fun h =>
  ((@h SiProp _ false 0 iprop(True) iprop(True) iprop(True) iprop(False) ⟨fun _ h => h⟩).into_laterN 0
    ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoLaterN_and_right` idx 7: necessary (SiProp: n=0, P=P2=True, Q2=False)
theorem w8c2_60 : ¬ drop0% Iris.ProofMode.intoLaterN_and_right 7 := fun h =>
  ((@h SiProp _ false 0 iprop(True) iprop(True) iprop(False)).into_laterN 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoLaterN_forall` idx 7: necessary (SiProp: n=0, Phi=True, Psi=False)
theorem w8c2_61 : ¬ drop0% Iris.ProofMode.intoLaterN_forall 7 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp _ True 0 (fun _ => iprop(True)) (fun _ => iprop(False)) false).into_laterN 0
    (SiProp.forall_holds.2 fun _ => trivial)) trivial

-- `Iris.ProofMode.intoLaterN_exists` idx 7: necessary (SiProp: n=0, Phi=True, Psi=False)
theorem w8c2_62 : ¬ drop0% Iris.ProofMode.intoLaterN_exists 7 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp _ True 0 (fun _ => iprop(True)) (fun _ => iprop(False)) false).into_laterN 0
    (SiProp.exists_holds.2 ⟨trivial, trivial⟩)) with
  | ⟨_, hx⟩ => hx

-- `Iris.ProofMode.intoLaterN_or_left` idx 8: necessary (SiProp: n=0, P1=True, Q1=P2=Q2=False)
theorem w8c2_63 : ¬ drop0% Iris.ProofMode.intoLaterN_or_left 8 := fun h =>
  ((@h SiProp _ false 0 iprop(True) iprop(False) iprop(False) iprop(False) ⟨fun _ h => h⟩).into_laterN 0
    (Or.inl trivial)).elim id id

-- `Iris.ProofMode.intoLaterN_or_left` idx 9: necessary (SiProp: n=0, P2=True, P1=Q1=Q2=False)
theorem w8c2_64 : ¬ drop0% Iris.ProofMode.intoLaterN_or_left 9 := fun h =>
  ((@h SiProp _ false 0 iprop(False) iprop(True) iprop(False) iprop(False) ⟨fun _ h => h⟩).into_laterN 0
    (Or.inr trivial)).elim id id

-- `Iris.ProofMode.intoLaterN_or_right` idx 7: necessary (SiProp: n=0, P=Q2=False, P2=True)
theorem w8c2_65 : ¬ drop0% Iris.ProofMode.intoLaterN_or_right 7 := fun h =>
  ((@h SiProp _ false 0 iprop(False) iprop(True) iprop(False)).into_laterN 0 (Or.inr trivial)).elim id id

-- `Iris.ProofMode.intoLaterN_affinely` idx 6: necessary (SiProp: n=0, P=True, Q=False)
theorem w8c2_66 : ¬ drop0% Iris.ProofMode.intoLaterN_affinely 6 := fun h =>
  ((@h SiProp _ 0 iprop(True) iprop(False) false).into_laterN 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoLaterN_intuitionistically` idx 6: necessary (SiProp: n=0, P=True, Q=False)
theorem w8c2_67 : ¬ drop0% Iris.ProofMode.intoLaterN_intuitionistically 6 := fun h =>
  ((@h SiProp false _ 0 iprop(True) iprop(False)).into_laterN 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoLaterN_absorbingly` idx 6: necessary (SiProp: n=0, P=True, Q=False)
theorem w8c2_68 : ¬ drop0% Iris.ProofMode.intoLaterN_absorbingly 6 := fun h =>
  ((@h SiProp _ 0 iprop(True) iprop(False) false).into_laterN 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoLaterN_persistently` idx 6: necessary (SiProp: n=0, P=True, Q=False)
theorem w8c2_69 : ¬ drop0% Iris.ProofMode.intoLaterN_persistently 6 := fun h =>
  (@h SiProp _ 0 iprop(True) iprop(False) false).into_laterN 0 trivial

-- `Iris.ProofMode.intoLaterN_sep_left` idx 8: necessary (SiProp: n=0, P1=P2=Q2=True, Q1=False)
theorem w8c2_70 : ¬ drop0% Iris.ProofMode.intoLaterN_sep_left 8 := fun h =>
  ((@h SiProp _ 0 iprop(True) iprop(True) iprop(False) iprop(True) false ⟨fun _ h => h⟩).into_laterN 0
    ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.intoLaterN_sep_left` idx 9: necessary (SiProp: n=0, P1=P2=Q1=True, Q2=False)
theorem w8c2_71 : ¬ drop0% Iris.ProofMode.intoLaterN_sep_left 9 := fun h =>
  ((@h SiProp _ 0 iprop(True) iprop(True) iprop(True) iprop(False) false ⟨fun _ h => h⟩).into_laterN 0
    ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoLaterN_sep_right` idx 7: necessary (SiProp: n=0, P=P2=True, Q2=False)
theorem w8c2_72 : ¬ drop0% Iris.ProofMode.intoLaterN_sep_right 7 := fun h =>
  ((@h SiProp _ 0 iprop(True) iprop(True) iprop(False) false).into_laterN 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.combineSepAs_later` idx 5: necessary (SiProp step 1: Q1=Q2=True, P=False)
theorem w8c2_73 : ¬ drop0% Iris.ProofMode.combineSepAs_later 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_as 1 ⟨trivial, trivial⟩

-- `Iris.ProofMode.combineSepAs_laterN` idx 6: necessary (SiProp: n=0, Q1=Q2=True, P=False)
theorem w8c2_74 : ¬ drop0% Iris.ProofMode.combineSepAs_laterN 6 := fun h =>
  (@h SiProp 0 _ iprop(True) iprop(True) iprop(False)).combine_sep_as 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.combineSepAs_except0` idx 5: necessary (SiProp step 1: Q1=Q2=True, P=False)
theorem w8c2_75 : ¬ drop0% Iris.ProofMode.combineSepAs_except0 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_as 1 ⟨Or.inr trivial, Or.inr trivial⟩).elim id id

-- `Iris.ProofMode.combineSepGives_later` idx 5: necessary (SiProp step 1: Q1=Q2=True, P=False)
theorem w8c2_76 : ¬ drop0% Iris.ProofMode.combineSepGives_later 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_gives 1 ⟨trivial, trivial⟩

-- `Iris.ProofMode.combineSepGives_laterN` idx 6: necessary (SiProp: n=0, Q1=Q2=True, P=False)
theorem w8c2_77 : ¬ drop0% Iris.ProofMode.combineSepGives_laterN 6 := fun h =>
  (@h SiProp 0 _ iprop(True) iprop(True) iprop(False)).combine_sep_gives 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAssumption_plainly_l_true` idx 4: necessary (SiProp: P=True, Q=False)
theorem w8c2_78 : ¬ drop0% Iris.ProofMode.fromAssumption_plainly_l_true 4 := fun h =>
  (@h SiProp _ iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAssumption_plainly_l_false` idx 5: necessary (SiProp: P=True, Q=False)
theorem w8c2_79 : ¬ drop0% Iris.ProofMode.fromAssumption_plainly_l_false 5 := fun h =>
  (@h SiProp _ _ iprop(True) iprop(False)).from_assumption 0 trivial

-- `Iris.ProofMode.fromPure_plainly` idx 6: necessary (SiProp: a=false, P=False, phi=True)
theorem w8c2_80 : ¬ drop0% Iris.ProofMode.fromPure_plainly 6 := fun h =>
  (@h SiProp false .in _ iprop(False) True).from_pure 0 trivial

-- `Iris.ProofMode.intoPure_plainly` idx 4: necessary (SiProp: P=True, phi=False)
theorem w8c2_81 : ¬ drop0% Iris.ProofMode.intoPure_plainly 4 := fun h =>
  (@h SiProp _ iprop(True) False).into_pure 0 trivial

-- `Iris.ProofMode.intoWand_plainly_true` idx 7: necessary (SiProp: q=false, R=P=True, Q=False)
theorem w8c2_82 : ¬ drop0% Iris.ProofMode.intoWand_plainly_true 7 := fun h =>
  (@h SiProp _ false (.matching .argument) iprop(True) iprop(True) iprop(False)).into_wand 0 ⟨trivial, trivial⟩
    0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_plainly_false` idx 8: necessary (SiProp: q=false, R=P=True, Q=False)
theorem w8c2_83 : ¬ drop0% Iris.ProofMode.intoWand_plainly_false 8 := fun h =>
  (@h SiProp _ false (.matching .argument) iprop(True) iprop(True) iprop(False) _).into_wand 0 trivial
    0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromAnd_plainly` idx 5: necessary (SiProp: P=False, Q1=Q2=True)
theorem w8c2_84 : ¬ drop0% Iris.ProofMode.fromAnd_plainly 5 := fun h =>
  (@h SiProp _ iprop(False) iprop(True) iprop(True)).from_and 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromSep_plainly` idx 5: necessary (SiProp: P=False, Q1=Q2=True)
theorem w8c2_85 : ¬ drop0% Iris.ProofMode.fromSep_plainly 5 := fun h =>
  (@h SiProp _ iprop(False) iprop(True) iprop(True)).from_sep 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoAnd_plainly` idx 6: necessary (SiProp: p=false, P=Q2=True, Q1=False)
theorem w8c2_86 : ¬ drop0% Iris.ProofMode.intoAnd_plainly 6 := fun h =>
  ((@h SiProp _ false iprop(True) iprop(False) iprop(True)).into_and 0 trivial).1

-- `Iris.ProofMode.intoSep_plainly` idx 6: necessary (SiProp: P=Q2=True, Q1=False)
theorem w8c2_87 : ¬ drop0% Iris.ProofMode.intoSep_plainly 6 := fun h =>
  ((@h SiProp _ ⟨fun _ hx => ⟨⟨trivial, hx.2.1⟩, hx.2.2⟩⟩ iprop(True) iprop(False) iprop(True)).into_sep 0 trivial).1

-- `Iris.ProofMode.intoSep_plainly_affine` idx 5: necessary (SiProp: P=Q2=True, Q1=False)
theorem w8c2_88 : ¬ drop0% Iris.ProofMode.intoSep_plainly_affine 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True) _ _).into_sep 0 trivial).1

-- `Iris.ProofMode.fromOr_plainly` idx 5: necessary (SiProp: P=False, Q1=Q2=True)
theorem w8c2_89 : ¬ drop0% Iris.ProofMode.fromOr_plainly 5 := fun h =>
  (@h SiProp _ iprop(False) iprop(True) iprop(True)).from_or 0 (Or.inl trivial)

-- `Iris.ProofMode.intoOr_plainly` idx 6: necessary (SiProp: P=True, Q1=Q2=False)
theorem w8c2_90 : ¬ drop0% Iris.ProofMode.intoOr_plainly 6 := fun h =>
  ((@h SiProp _ _ iprop(True) iprop(False) iprop(False)).into_or 0 trivial).elim id id

-- `Iris.ProofMode.fromExists_plainly` idx 5: necessary (SiProp: P=False, Phi=True)
theorem w8c2_91 : ¬ drop0% Iris.ProofMode.fromExists_plainly 5 := fun h =>
  (@h SiProp True _ iprop(False) (fun _ => iprop(True))).from_exists 0 (SiProp.exists_holds.2 ⟨trivial, trivial⟩)

-- `Iris.ProofMode.intoExists_plainly` idx 6: necessary (SiProp: alpha=Unit, P=True, Phi=False)
theorem w8c2_92 : ¬ drop0% Iris.ProofMode.intoExists_plainly 6 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp _ _ iprop(True) Unit (fun _ => iprop(False))).into_exists 0 trivial) with
  | ⟨_, hx⟩ => hx

-- `Iris.ProofMode.intoForall_plainly` idx 5: necessary (SiProp: alpha=Unit, P=True, Phi=False)
theorem w8c2_93 : ¬ drop0% Iris.ProofMode.intoForall_plainly 5 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp _ iprop(True) Unit (fun _ => iprop(False))).into_forall 0 trivial) ()

-- `Iris.ProofMode.fromForall_plainly` idx 5: necessary (SiProp: P=False, Phi=True)
theorem w8c2_94 : ¬ drop0% Iris.ProofMode.fromForall_plainly 5 := fun h =>
  (@h SiProp _ iprop(False) True (fun _ => iprop(True))).from_forall 0 (SiProp.forall_holds.2 fun _ => trivial)

-- `Iris.ProofMode.intoExcept0_plainly` idx 4: necessary (SiProp step 1: P=True, Q=False)
theorem w8c2_95 : ¬ drop0% Iris.ProofMode.intoExcept0_plainly 4 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False)).into_except0 1 trivial).elim id id

-- `Iris.ProofMode.intoLaterN_plainly` idx 6: necessary (SiProp: n=0, P=True, Q=False)
theorem w8c2_96 : ¬ drop0% Iris.ProofMode.intoLaterN_plainly 6 := fun h =>
  (@h SiProp false _ 0 iprop(True) iprop(False)).into_laterN 0 trivial
end

namespace W8c2
open Iris Iris.BI

/-! GB (copied from W4c4): predicates on Bool with xor as a non-affine, non-positive BI. -/
def GB := Bool → Prop

instance : BIBase GB where
  Entails P Q      := ∀ x, P x → Q x
  emp            x := x = false
  pure φ         _ := φ
  and P Q        x := P x ∧ Q x
  or P Q         x := P x ∨ Q x
  imp P Q        x := P x → Q x
  sForall Ψ      x := ∀ p, Ψ p → p x
  sExists Ψ      x := ∃ p, Ψ p ∧ p x
  sep P Q        x := ∃ a b, x = xor a b ∧ P a ∧ Q b
  wand P Q       x := ∀ y, P y → Q (xor x y)
  persistently P _ := P false
  later P        x := P x

instance : COFE GB := COFE.ofDiscrete _

instance gbBI : BI GB where
  entails_refl _ h := h
  entails_trans h1 h2 x h := h2 x (h1 x h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h₁, h₂⟩ => funext fun σ => propext ⟨h₁ σ, h₂ σ⟩⟩
  and_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne           := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne         := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne        := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  pure_intro h _ _ := h
  pure_elim' h σ hφ := h hφ σ ⟨⟩
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 x h := ⟨h1 x h, h2 x h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 x h := h.elim (h1 x) (h2 x)
  imp_intro h x hP hQ := h x ⟨hP, hQ⟩
  imp_elim h x hPQ := h x hPQ.1 hPQ.2
  sForall_intro h x hP p hp := h p hp x hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h x := fun ⟨p, hp, hx⟩ => h p hp x hx
  sep_mono h1 h2 _ := fun ⟨a, b, e, ha, hb⟩ => ⟨a, b, e, h1 a ha, h2 b hb⟩
  emp_sep := ⟨fun _ ⟨a, b, e, ha, hb⟩ => by
      have ha' : a = false := ha
      subst ha'; subst e; simpa using hb,
    fun x h => ⟨false, x, by simp, rfl, h⟩⟩
  sep_symm _ := fun ⟨a, b, e, ha, hb⟩ => ⟨b, a, by subst e; cases a <;> cases b <;> rfl, hb, ha⟩
  sep_assoc_l _ := fun ⟨ab, c, e, ⟨a, b, e2, ha, hb⟩, hc⟩ =>
    ⟨a, xor b c, by subst e; subst e2; cases a <;> cases b <;> cases c <;> rfl, ha, b, c, rfl, hb, hc⟩
  wand_intro h x hP y hQ := h (xor x y) ⟨x, y, rfl, hP, hQ⟩
  wand_elim h _ := fun ⟨a, b, e, ha, hb⟩ => e ▸ h a ha b hb
  persistently_mono h _ hP := h false hP
  persistently_idem_2 _ h := h
  persistently_emp_2 _ _ := (rfl : false = false)
  persistently_and_2 _ h := h
  persistently_absorb_l _ := fun ⟨_, _, _, ha, _⟩ => ha
  persistently_and_l x h := ⟨false, x, by cases x <;> rfl, h.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr fun _ => h

def own1 : GB := fun x => x = true

theorem gb_true_not_emp : ¬ ((iprop(True) : GB) ⊢ iprop(emp)) := fun h =>
  Bool.noConfusion (h true trivial : true = false)

theorem gb_emp_not_absorbing : ¬ Absorbing (iprop(emp) : GB) := fun ⟨h⟩ =>
  Bool.noConfusion (h true ⟨true, false, rfl, trivial, rfl⟩ : true = false)

theorem gb_true_not_affine : ¬ Affine (iprop(True) : GB) := fun ⟨h⟩ => gb_true_not_emp h

theorem gb_own1_not_pers : ¬ Persistent own1 := fun ⟨h⟩ =>
  Bool.noConfusion (h true rfl : false = true)

theorem gb_not_biaffine : ¬ BIAffine GB := fun h => gb_true_not_affine (h.affine _)

-- helper: NA (copied from Probe3): two-element UORA, equality order; UPred NA is non-affine
/-- Two-element commutative monoid (e unit, a idempotent) with the equality order: a non-affine UORA. -/
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

-- helper: in UPred NA, True does not entail emp
theorem na_true_not_emp : ¬ ((iprop(True) : UPred NA) ⊢ iprop(emp)) := fun h => by
  have H := h 0 ⟨.a, trivial⟩ trivial
  cases H


-- helper: Bool with xor (unit o, i • i = o), equality order: UPred X2 is non-affine and not positive
inductive X2 | o | i deriving DecidableEq
def X2.op : X2 → X2 → X2
  | .o, y => y
  | .i, .o => .i
  | .i, .i => .o
instance : OFE X2 := OFE.ofDiscrete X2
instance : OFE.Discrete X2 := ⟨id⟩
instance x2ORA : ORA X2 := ORA.ofDiscreteORAData {
  pcore := fun _ => some .o
  op := X2.op
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
  pcore_mono := by intro x y cx h1 h2; exact ⟨.o, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.o, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; rfl
  increasing_closed := by intro x y _ h; cases h; assumption }
instance : OrderRefl X2 := ⟨fun x => show x = x from rfl⟩
instance x2UORA : UORA X2 where
  unit := .o
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl
abbrev oI : UPred X2 := UPred.ownM X2.i

-- helper: Bool with the discrete order (copied from Probe4): MonPred DIdx SiProp is an Sbi without SbiEmpValidExist
def DB := Bool
instance : LE DB := ⟨fun a b => a = b⟩
instance : Inhabited DB := ⟨(true : Bool)⟩
instance : Std.IsPreorder DB where
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2
abbrev DIdx : BiIndex := { car := DB, rel := inferInstance }
def phiD (a : Bool) : MonPred DIdx SiProp := ⟨fun i => iprop(⌜(i : Bool) = a⌝), fun hij _ h => hij ▸ h⟩
abbrev iT : DIdx.car := (true : Bool)
abbrev iF : DIdx.car := (false : Bool)

-- helper: ■ P at any index and step means P at every index
theorem dpl {X : MonPred DIdx SiProp} {i : DIdx.car} {n : Nat} (H : (iprop(■ X) : MonPred DIdx SiProp).monPred_at i |>.holds n)
    (j : DIdx.car) : (X.monPred_at j).holds n :=
  SiProp.forall_holds.1 ((MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) i X).mp n H) j
-- helper: a MonPred DIdx SiProp holding at index true but not false (same step) is not plain
theorem dnp {X : MonPred DIdx SiProp} (n : Nat) (h : X ⊢ ■ X) (ht : (X.monPred_at iT).holds n)
    (hf : ¬ (X.monPred_at iF).holds n) : False := hf (dpl (h iT n ht) iF)
theorem phT : ((phiD true).monPred_at iT).holds 0 := rfl
theorem phF : ¬ ((phiD true).monPred_at iF).holds 0 := fun e => Bool.noConfusion e
-- helper: phiD true is not plain; sandwich version
theorem phi_np (h : phiD true ⊢ ■ phiD true) : False := dnp 0 h phT phF
theorem dsand {X : MonPred DIdx SiProp} (h1 : phiD true ⊢ X) (h2 : X ⊢ phiD true) (h : X ⊢ ■ X) : False :=
  phi_np (h1.trans (h.trans (plainly_mono h2)))
-- helper: ■ (phiD true ∨ phiD false) holds, ■ phiD true ∨ ■ phiD false does not
theorem dor (H : (iprop(■ (phiD true ∨ phiD false)) : MonPred DIdx SiProp) ⊢ iprop(■ phiD true ∨ ■ phiD false)) : False := by
  have hl : ((iprop(■ (phiD true ∨ phiD false)) : MonPred DIdx SiProp).monPred_at iT).holds 0 :=
    (MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) iT _).mpr 0
      (SiProp.forall_holds.2 fun j => by
        show (j : Bool) = true ∨ (j : Bool) = false
        exact Bool.eq_false_or_eq_true j)
  rcases H iT 0 hl with h | h
  · exact Bool.noConfusion (dpl h iF : (false : Bool) = true)
  · exact Bool.noConfusion (dpl h iT : (true : Bool) = false)


theorem sExists_sub (Ψ : SiProp → Prop) :
    (BIBase.sExists Ψ : SiProp) ⊢ iprop(∃ x : {p : SiProp // Ψ p}, x.1) :=
  fun _ ⟨P, hP, h⟩ => SiProp.exists_holds.mpr ⟨⟨P, hP⟩, h⟩
@[instance_reducible] def spE (PROP : Type _) [Sbi PROP] : BiEmbed SiProp PROP where
  embed := siPure
  ne := Sbi.siPure_ne
  mono := siPure_mono
  emp_valid_inj := fun _ h => siPure_emp_valid.mp h
  emp_2 := true_intro.trans siPure_pure.2
  impl_2 := fun _ _ => siPure_imp_mpr
  forall_2 := fun Ψ R h =>
    (forall_intro fun q => imp_intro_swap (pure_elim_left fun hq => h q hq)).trans siPure_sForall_mpr
  exist_1 := fun Ψ R h =>
    (siPure_mono (sExists_sub Ψ)).trans (siPure_exist.mp.trans (exists_elim fun x => h x.1 x.2))
  sep := fun _ _ => siPure_and_sep
  wand_2 := fun _ _ => siPure_imp_wand.2
  persistently := fun _ => ⟨Persistent.persistent, persistently_elim⟩
theorem spT {PROP : Type _} [Sbi PROP] {P : SiProp} (hP : (iprop(True) : SiProp) ⊢ P) :
    (iprop(True) : PROP) ⊢ @Embed.embed SiProp PROP (spE PROP).toEmbed P :=
  siPure_pure.2.trans (siPure_mono hP)
theorem si_nf : ¬ ((iprop(True) : SiProp) ⊢ iprop(False)) := fun h => h 0 trivial

end W8c2

namespace W8c2
open Iris Iris.BI Iris.Std Iris.Algebra
abbrev TM := fun V => Std.ExtTreeMap Nat V compare
abbrev TS := Std.ExtTreeSet Nat compare
abbrev MSN := ListPerm Nat
abbrev sg {V : Type} (v : V) : TM V := PartialMap.insert ∅ 0 v
theorem sgE {PROP : Type _} [BI PROP] {V : Type} (Φ : Nat → V → PROP) (v : V) :
    bigSepM Φ (sg v) = Φ 0 v := BigOpM.bigOpM_singleton_eq (op := BIBase.sep) Φ 0 v
end W8c2

section
open Iris Iris.BI Iris.Std Iris.ProofMode W8c2

-- `Iris.ProofMode.intoLaterN_bigSepL` idx 8: necessary (SiProp: n=0, l=[()], Phi=True, Psi=False)
theorem w8c2_97 : ¬ drop0% Iris.ProofMode.intoLaterN_bigSepL 8 := fun h => by
  have H := (@h SiProp _ Unit false 0 (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]).into_laterN
  have a := (BigSepL.bigSepL_singleton (PROP := SiProp) (Φ := fun _ _ => iprop(True)) (x := ())).2 0 trivial
  exact (BigSepL.bigSepL_singleton (PROP := SiProp) (Φ := fun _ _ => iprop(False)) (x := ())).1 0 (H 0 a)

-- `Iris.ProofMode.intoLaterN_bigSepL2` idx 10: necessary (SiProp: n=0, l1=l2=[()], Phi=True, Psi=False)
theorem w8c2_98 : ¬ drop0% Iris.ProofMode.intoLaterN_bigSepL2 10 := fun h => by
  have H := (@h SiProp _ Unit Unit false 0 (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) [()] [()]).into_laterN
  have a := (BigSepL2.bigSepL2_singleton (PROP := SiProp) (Φ := fun _ _ _ => iprop(True)) (x := ()) (y := ())).2 0 trivial
  exact (BigSepL2.bigSepL2_singleton (PROP := SiProp) (Φ := fun _ _ _ => iprop(False)) (x := ()) (y := ())).1 0 (H 0 a)

-- `Iris.ProofMode.intoLaterN_bigSepM` idx 11: necessary (SiProp: n=0, one-key ExtTreeMap, Phi=True, Psi=False)
theorem w8c2_99 : ¬ drop0% Iris.ProofMode.intoLaterN_bigSepM 11 := fun h => by
  have H := (@h SiProp _ Nat Unit TM _ false 0 (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) (sg ())).into_laterN
  have H2 : (iprop(True) : SiProp) ⊢ iprop(False) := by
    have e1 := sgE (PROP := SiProp) (fun _ _ => iprop(True)) ()
    have e2 := sgE (PROP := SiProp) (fun _ _ => iprop(False)) ()
    exact e1 ▸ e2 ▸ H
  exact H2 0 trivial

-- `Iris.ProofMode.intoLaterN_bigSepS` idx 10: necessary (SiProp: n=0, X={0} in ExtTreeSet, Phi=True, Psi=False)
theorem w8c2_100 : ¬ drop0% Iris.ProofMode.intoLaterN_bigSepS 10 := fun h => by
  have H := (@h SiProp _ TS Nat _ false 0 (fun _ => iprop(True)) (fun _ => iprop(False)) {0}).into_laterN
  have a := (BigSepS.bigSepS_singleton (PROP := SiProp) (S := TS) (Φ := fun _ => iprop(True)) (x := 0)).2 0 trivial
  exact (BigSepS.bigSepS_singleton (PROP := SiProp) (S := TS) (Φ := fun _ => iprop(False)) (x := 0)).1 0 (H 0 a)

-- `Iris.ProofMode.intoLaterN_bigSepMS` idx 10: necessary (SiProp: n=0, X={0} in ListPerm Nat, Phi=True, Psi=False)
theorem w8c2_101 : ¬ drop0% Iris.ProofMode.intoLaterN_bigSepMS 10 := fun h => by
  have H := (@h SiProp _ MSN Nat _ false 0 (fun _ => iprop(True)) (fun _ => iprop(False)) {0}).into_laterN
  have a := (BigSepMS.bigSepMS_singleton (PROP := SiProp) (MS := MSN) (Φ := fun _ => iprop(True)) (x := 0)).2 0 trivial
  exact (BigSepMS.bigSepMS_singleton (PROP := SiProp) (MS := MSN) (Φ := fun _ => iprop(False)) (x := 0)).1 0 (H 0 a)

-- `Iris.ProofMode.intoLaterN_bigSepM2` idx 13: necessary (SiProp: n=0, one-key ExtTreeMaps, Phi=True, Psi=False)
theorem w8c2_102 : ¬ drop0% Iris.ProofMode.intoLaterN_bigSepM2 13 := fun h => by
  have a := (BigSepM2.bigSepM2_singleton (M := TM) (fun _ _ _ => (iprop(True) : SiProp)) 0 () ()).2 0 trivial
  have H := (@h SiProp _ Nat Unit Unit TM _ false 0 (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) (PartialMap.singleton 0 () : TM Unit) (PartialMap.singleton 0 () : TM Unit)).into_laterN
  exact (BigSepM2.bigSepM2_singleton (M := TM) (fun _ _ _ => (iprop(False) : SiProp)) 0 () ()).1 0 (H 0 a)

-- `Iris.ProofMode.quickAbsorbing_biAffine` idx 3: necessary (GB: emp is not absorbing)
theorem w8c2_103 : ¬ drop0% Iris.ProofMode.quickAbsorbing_biAffine 3 := fun h =>
  gb_emp_not_absorbing (@h GB _ iprop(emp)).1

-- `Iris.ProofMode.makeSep_true_left` idx 3: necessary (GB: P=emp, True ∗ emp holds at true)
theorem w8c2_104 : ¬ drop0% Iris.ProofMode.makeSep_true_left 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp)).make_sep.mp true ⟨true, false, rfl, trivial, rfl⟩ : true = false)

-- `Iris.ProofMode.makeSep_true_right` idx 3: necessary (GB: P=emp, emp ∗ True holds at true)
theorem w8c2_105 : ¬ drop0% Iris.ProofMode.makeSep_true_right 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp)).make_sep.mp true ⟨false, true, rfl, rfl, trivial⟩ : true = false)

-- `Iris.ProofMode.makeAnd_emp_left` idx 3: necessary (GB: P=True, True holds at true, emp does not)
theorem w8c2_106 : ¬ drop0% Iris.ProofMode.makeAnd_emp_left 3 := fun h =>
  Bool.noConfusion (((@h GB _ iprop(True)).make_and.mpr true trivial).1 : true = false)

-- `Iris.ProofMode.makeAnd_emp_right` idx 3: necessary (GB: P=True, True holds at true, emp does not)
theorem w8c2_107 : ¬ drop0% Iris.ProofMode.makeAnd_emp_right 3 := fun h =>
  Bool.noConfusion (((@h GB _ iprop(True)).make_and.mpr true trivial).2 : true = false)

-- `Iris.ProofMode.makeOr_emp_left` idx 3: necessary (GB: P=True, emp ∨ True holds at true, emp does not)
theorem w8c2_108 : ¬ drop0% Iris.ProofMode.makeOr_emp_left 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True)).make_or.mp true (Or.inr trivial) : true = false)

-- `Iris.ProofMode.makeAbsorbingly_absorbing` idx 3: necessary (GB: P=emp, absorbingly emp holds at true)
theorem w8c2_109 : ¬ drop0% Iris.ProofMode.makeAbsorbingly_absorbing 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp)).make_absorbingly.mp true ⟨true, false, rfl, trivial, rfl⟩ : true = false)

-- `Iris.ProofMode.makeIntuitionistically_True_affine` idx 2: necessary (GB: intuitionistically True fails at true)
theorem w8c2_110 : ¬ drop0% Iris.ProofMode.makeIntuitionistically_True_affine 2 := fun h =>
  Bool.noConfusion (((@h GB _).make_intuitionistically.mpr true trivial).1 : true = false)

-- `Iris.ProofMode.makeLaterN_emp` idx 2: necessary (UPred NA, n=1: later emp holds at step 0 on a, emp does not)
theorem w8c2_111 : ¬ drop0% Iris.ProofMode.makeLaterN_emp 2 := fun h => by
  have H := (@h (UPred NA) _ 1).make_laterN.mp
  have : (iprop(▷ emp) : UPred NA).holds 0 ⟨.a, trivial⟩ := by
    show (UPred.later _).holds 0 _
    trivial
  have H2 := H 0 ⟨.a, trivial⟩ this
  cases H2

-- `Iris.ProofMode.makeEmbed_emp` idx 5: necessary (siPure embedding SiProp into UPred NA: embed emp = True, not emp)
theorem w8c2_112 : ¬ drop0% Iris.ProofMode.makeEmbed_emp 5 := fun h =>
  na_true_not_emp ((spT (P := iprop(emp)) (fun _ _ => trivial)).trans
    (@h SiProp (UPred NA) _ _ (spE _)).make_embed.mp)

-- `Iris.ProofMode.fromAssumption_plainly_l_false` idx 2: necessary (UPred NA: P=True, Q=emp; plainly True holds where emp fails)
theorem w8c2_113 : ¬ drop0% Iris.ProofMode.fromAssumption_plainly_l_false 2 := fun h =>
  na_true_not_emp (plainly_pure.mpr.trans
    (@h (UPred NA) _ iprop(True) iprop(emp) ⟨intuitionistically_elim_emp⟩).from_assumption)

-- `Iris.ProofMode.intoWand_plainly_false` idx 7: necessary (UPred NA: R=P=Q=emp, q=false; plainly emp holds where emp fails)
theorem w8c2_114 : ¬ drop0% Iris.ProofMode.intoWand_plainly_false 7 := fun h =>
  na_true_not_emp (plainly_emp_intro.trans (sep_emp.2.trans (wand_elim
    (@h (UPred NA) _ false (.matching .argument) iprop(emp) iprop(emp) iprop(emp) ⟨wand_intro sep_emp.1⟩).into_wand)))

-- `Iris.ProofMode.intoSep_plainly` idx 2: necessary (non-positive UPred X2: P = oI ∗ oI, Q1=Q2=oI)
theorem w8c2_115 : ¬ drop0% Iris.ProofMode.intoSep_plainly 2 := fun h => by
  have H := (@h (UPred X2) _ iprop(oI ∗ oI) oI oI ⟨.rfl⟩).into_sep 0 ⟨.o, trivial⟩ ⟨.i, .i, rfl, rfl, rfl⟩
  obtain ⟨_, _, _, h1, _⟩ := H
  cases h1

-- `Iris.ProofMode.intoOr_plainly` idx 2: necessary (MonPred over discrete Bool index into SiProp: P = phiD true ∨ phiD false)
theorem w8c2_116 : ¬ drop0% Iris.ProofMode.intoOr_plainly 2 := fun h =>
  dor (@h (MonPred DIdx SiProp) _ iprop(phiD true ∨ phiD false) (phiD true) (phiD false) ⟨.rfl⟩).into_or
end

namespace W8c2
open Iris Iris.BI Iris.OFE

/-- SiProp true at steps 0 and 1 entails later of the step-0 proposition. -/
theorem s1_later_s0 : s1 ⊢ iprop(▷ s0) := fun k hk => match k with
  | 0 => trivial
  | 1 => (rfl : (0 : Nat) = 0)
  | _ + 2 => absurd (show _ ≤ 1 from hk) (by omega)

/-- Later credits on SiProp with every credit True. -/
@[reducible] def lcS : BILaterCredits SiProp where
  lc _ := iprop(True)
  lc_split := ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩
  lc_timeless _ := inferInstance
  lc_0_persistent := inferInstance
  lc_affine _ := inferInstance

/-- Constant-True fancy update on SiProp: lawful, but nothing can be eliminated from it. -/
@[reducible] def fupS : BIFUpdate SiProp where
  fupd _ _ _ := iprop(True)
  ne := ⟨fun _ _ _ _ {_} _ => Iff.rfl⟩
  subset _ := fun _ _ => trivial
  except0 := fun _ _ => trivial
  mono _ := fun _ _ => trivial
  trans := fun _ _ => trivial
  mask_frame_right_strong _ := fun _ _ => trivial
  frame_right := fun _ _ => trivial

/-- The interaction law holds for the constant-True update. -/
theorem fupSLc : @BIFUpdLaterCredits SiProp _ lcS fupS :=
  @BIFUpdLaterCredits.mk SiProp _ lcS fupS (fun _ _ _ _ _ _ _ _ => by unfold fupS; exact trivial)

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF

/-- Later credits on IProp with £ n := True (copied from W5c1). -/
@[reducible] noncomputable def lcT : BILaterCredits (IProp CGF) where
  lc _ := iprop(True)
  lc_split := ⟨emp_sep.2.trans (sep_mono_left true_intro), true_intro⟩
  lc_timeless _ := inferInstance
  lc_0_persistent := inferInstance
  lc_affine _ := inferInstance

/-- If ▷ Q ⊢ Q for Q := |={⊤}=> False in IProp, Löb and fupd soundness give False (copied from W5c1). -/
theorem fupd_loeb_false (H : ∀ [InvGS_gen .hasNoLC CGF],
    (iprop(▷ |={⊤}=> ⌜False⌝) : IProp CGF) ⊢ iprop(|={⊤}=> ⌜False⌝)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (true_intro.trans (loeb_weak H))))

/-- With real credits: £ 0 ⊢ |={⊤}=> False under every InvGS gives False. -/
theorem lc0_false (H : ∀ [InvGS CGF], (£ 0 : IProp CGF) ⊢ iprop(|={⊤}=> ⌜False⌝)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (emp_sep.1.trans H))

/-- With real credits: ▷ G ∗ £ 0 ⊢ G for G := |={⊤}=> False gives False (Löb on £ 0 -∗ G, £ 0 duplicable). -/
theorem lc0_loeb (H : ∀ [InvGS CGF],
    (iprop(▷ (|={⊤}=> ⌜False⌝) ∗ £ 0) : IProp CGF) ⊢ iprop(|={⊤}=> ⌜False⌝)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ => by
      have L : (iprop(True) : IProp CGF) ⊢ iprop(£ 0 -∗ |={⊤}=> ⌜False⌝) :=
        true_intro.trans (loeb_weak (wand_intro
          ((sep_mono_right (lc_split (n := 0) (m := 0)).1).trans
          (sep_assoc.2.trans
          ((sep_mono_left ((sep_mono_right later_intro).trans later_sep.2)).trans
          ((sep_mono_left (later_mono wand_elim_left)).trans H))))))
      exact wand_intro ((sep_mono_left (true_intro.trans L)).trans wand_elim_left))

end W8c2

section
open Iris Iris.BI Iris.OFE Iris.ProofMode W8c2

-- `tac_lc_add_laterN_split` idx 4: necessary (IProp, no-credit InvGS, £ n := True; n=m=1, newM=0, P = ▷G, Q = goal = G := |={⊤}=> False: ▷G ⊢ G, Löb + fupd soundness)
theorem w8c2_117 : ¬ drop0% tac_lc_add_laterN_split 4 := fun h =>
  fupd_loeb_false fun {_} => (sep_emp.2.trans (sep_mono_right true_intro)).trans
    (@h (IProp CGF) _ lcT _ True 1 1 0 false ⊤ iprop(▷ (|={⊤}=> ⌜False⌝) ∗ True) iprop(▷ (|={⊤}=> ⌜False⌝))
      iprop(▷ (|={⊤}=> ⌜False⌝) ∗ True) iprop(|={⊤}=> ⌜False⌝) iprop(|={⊤}=> ⌜False⌝)
      .rfl inferInstance trivial ⟨rfl⟩ .rfl sep_elim_left .rfl)

-- `tac_lc_add_laterN_split` idx 16: necessary (IProp with credits: e=True, P=False, n=m=newM=0, Q=R=False ∗ £0, goal = |={⊤}=> False)
theorem w8c2_118 : ¬ drop0% tac_lc_add_laterN_split 16 := fun h =>
  lc0_false fun {_} => true_intro.trans
    (@h (IProp CGF) _ _ _ _ True 0 0 0 false ⊤ iprop(True) iprop(⌜False⌝)
      iprop(⌜False⌝ ∗ £ 0) iprop(⌜False⌝ ∗ £ 0) iprop(|={⊤}=> ⌜False⌝)
      inferInstance trivial ⟨rfl⟩ .rfl .rfl (sep_elim_left.trans false_elim))

-- `tac_lc_add_laterN_split` idx 17: necessary (SiProp, £ n := True, constant-True fupd: n=m=1, newM=0, P=s1, Q=goal=s0; e = s1 ∗ True fails s0 at step 1)
theorem w8c2_119 : ¬ drop0% tac_lc_add_laterN_split 17 := fun h =>
  absurd ((@h SiProp _ lcS fupS fupSLc True 1 1 0 false ⊤ iprop(s1 ∗ True) s1 iprop(s1 ∗ True) s0 s0
      .rfl trivial ⟨rfl⟩ .rfl (sep_elim_left.trans s1_later_s0) .rfl) 1 ⟨Nat.le_refl 1, trivial⟩)
    (by decide : ¬ (1 : Nat) = 0)

-- `tac_lc_add_laterN_split` idx 18: necessary (SiProp, £ n := True, constant-True fupd, phi=False (ElimModal vacuous): n=m=1, newM=0, P=s1, Q=goal=s0)
theorem w8c2_120 : ¬ drop0% tac_lc_add_laterN_split 18 := fun h =>
  absurd ((@h SiProp _ lcS fupS fupSLc False 1 1 0 false ⊤ iprop(s1 ∗ True) s1 iprop(s1 ∗ True) s0 s0
      .rfl ⟨fun f => f.elim⟩ ⟨rfl⟩ .rfl (sep_elim_left.trans s1_later_s0) .rfl) 1 ⟨Nat.le_refl 1, trivial⟩)
    (by decide : ¬ (1 : Nat) = 0)

-- `tac_lc_add_laterN_split` idx 19: necessary (IProp with credits: m=newM=0, n=1, P=▷G, Q=goal=G := |={⊤}=> False; ▷G ∗ £0 ⊢ G, Löb on £0 -∗ G)
theorem w8c2_121 : ¬ drop0% tac_lc_add_laterN_split 19 := fun h =>
  lc0_loeb fun {_} =>
    @h (IProp CGF) _ _ _ _ True 1 0 0 false ⊤ iprop(▷ (|={⊤}=> ⌜False⌝) ∗ £ 0) iprop(▷ (|={⊤}=> ⌜False⌝))
      iprop(▷ (|={⊤}=> ⌜False⌝) ∗ £ 0) iprop(|={⊤}=> ⌜False⌝) iprop(|={⊤}=> ⌜False⌝)
      .rfl inferInstance trivial .rfl sep_elim_left .rfl

-- `tac_lc_add_laterN_split` idx 20: necessary (IProp with credits: n=m=newM=0, P=True, R=Q=False, goal = |={⊤}=> False)
theorem w8c2_122 : ¬ drop0% tac_lc_add_laterN_split 20 := fun h =>
  lc0_false fun {_} => (emp_sep.2.trans (sep_mono_left true_intro)).trans
    (@h (IProp CGF) _ _ _ _ True 0 0 0 false ⊤ iprop(True ∗ £ 0) iprop(True)
      iprop(⌜False⌝) iprop(⌜False⌝) iprop(|={⊤}=> ⌜False⌝)
      .rfl inferInstance trivial ⟨rfl⟩ false_elim false_elim)

-- `tac_lc_add_laterN_split` idx 21: necessary (IProp with credits: n=m=newM=0, P=True, R=True ∗ £0, Q=False, goal = |={⊤}=> False)
theorem w8c2_123 : ¬ drop0% tac_lc_add_laterN_split 21 := fun h =>
  lc0_false fun {_} => (emp_sep.2.trans (sep_mono_left true_intro)).trans
    (@h (IProp CGF) _ _ _ _ True 0 0 0 false ⊤ iprop(True ∗ £ 0) iprop(True)
      iprop(True ∗ £ 0) iprop(⌜False⌝) iprop(|={⊤}=> ⌜False⌝)
      .rfl inferInstance trivial ⟨rfl⟩ .rfl false_elim)

-- `tac_lc_add_laterN_split` idx 22: necessary (IProp with credits: n=m=newM=0, P=Q=True, R=True ∗ £0, goal = |={⊤}=> False)
theorem w8c2_124 : ¬ drop0% tac_lc_add_laterN_split 22 := fun h =>
  lc0_false fun {_} => (emp_sep.2.trans (sep_mono_left true_intro)).trans
    (@h (IProp CGF) _ _ _ _ True 0 0 0 false ⊤ iprop(True ∗ £ 0) iprop(True)
      iprop(True ∗ £ 0) iprop(True) iprop(|={⊤}=> ⌜False⌝)
      .rfl inferInstance trivial ⟨rfl⟩ .rfl true_intro)

-- `tac_lc_add_laterN_full` idx 4: necessary (IProp, no-credit InvGS, £ n := True; n=m=1, P = ▷G, Q = goal = G := |={⊤}=> False: Löb + fupd soundness)
theorem w8c2_125 : ¬ drop0% tac_lc_add_laterN_full 4 := fun h =>
  fupd_loeb_false fun {_} => (sep_emp.2.trans (sep_mono_right true_intro)).trans
    (@h (IProp CGF) _ lcT _ True 1 1 false ⊤ iprop(▷ (|={⊤}=> ⌜False⌝) ∗ True) iprop(▷ (|={⊤}=> ⌜False⌝))
      iprop(|={⊤}=> ⌜False⌝) iprop(|={⊤}=> ⌜False⌝)
      .rfl inferInstance trivial ⟨rfl⟩ .rfl .rfl)

-- `tac_lc_add_laterN_full` idx 14: necessary (IProp with credits: e=True, P=Q=False, n=m=0, goal = |={⊤}=> False)
theorem w8c2_126 : ¬ drop0% tac_lc_add_laterN_full 14 := fun h =>
  lc0_false fun {_} => true_intro.trans
    (@h (IProp CGF) _ _ _ _ True 0 0 false ⊤ iprop(True) iprop(⌜False⌝)
      iprop(⌜False⌝) iprop(|={⊤}=> ⌜False⌝)
      inferInstance trivial ⟨rfl⟩ false_elim false_elim)

-- `tac_lc_add_laterN_full` idx 15: necessary (SiProp, £ n := True, constant-True fupd: n=m=1, P=s1, Q=goal=s0; e = s1 ∗ True fails s0 at step 1)
theorem w8c2_127 : ¬ drop0% tac_lc_add_laterN_full 15 := fun h =>
  absurd ((@h SiProp _ lcS fupS fupSLc True 1 1 false ⊤ iprop(s1 ∗ True) s1 s0 s0
      .rfl trivial ⟨rfl⟩ s1_later_s0 .rfl) 1 ⟨Nat.le_refl 1, trivial⟩)
    (by decide : ¬ (1 : Nat) = 0)

-- `tac_lc_add_laterN_full` idx 16: necessary (SiProp, £ n := True, constant-True fupd, phi=False (ElimModal vacuous): n=m=1, P=s1, Q=goal=s0)
theorem w8c2_128 : ¬ drop0% tac_lc_add_laterN_full 16 := fun h =>
  absurd ((@h SiProp _ lcS fupS fupSLc False 1 1 false ⊤ iprop(s1 ∗ True) s1 s0 s0
      .rfl ⟨fun f => f.elim⟩ ⟨rfl⟩ s1_later_s0 .rfl) 1 ⟨Nat.le_refl 1, trivial⟩)
    (by decide : ¬ (1 : Nat) = 0)

-- `tac_lc_add_laterN_full` idx 17: necessary (IProp with credits: m=0, n=1, P=▷G, Q=goal=G := |={⊤}=> False; ▷G ∗ £0 ⊢ G, Löb on £0 -∗ G)
theorem w8c2_129 : ¬ drop0% tac_lc_add_laterN_full 17 := fun h =>
  lc0_loeb fun {_} =>
    @h (IProp CGF) _ _ _ _ True 1 0 false ⊤ iprop(▷ (|={⊤}=> ⌜False⌝) ∗ £ 0) iprop(▷ (|={⊤}=> ⌜False⌝))
      iprop(|={⊤}=> ⌜False⌝) iprop(|={⊤}=> ⌜False⌝)
      .rfl inferInstance trivial .rfl .rfl

-- `tac_lc_add_laterN_full` idx 18: necessary (IProp with credits: n=m=0, P=True, Q=False, goal = |={⊤}=> False)
theorem w8c2_130 : ¬ drop0% tac_lc_add_laterN_full 18 := fun h =>
  lc0_false fun {_} => (emp_sep.2.trans (sep_mono_left true_intro)).trans
    (@h (IProp CGF) _ _ _ _ True 0 0 false ⊤ iprop(True ∗ £ 0) iprop(True)
      iprop(⌜False⌝) iprop(|={⊤}=> ⌜False⌝)
      .rfl inferInstance trivial ⟨rfl⟩ false_elim)

-- `tac_lc_add_laterN_full` idx 19: necessary (IProp with credits: n=m=0, P=Q=True, goal = |={⊤}=> False)
theorem w8c2_131 : ¬ drop0% tac_lc_add_laterN_full 19 := fun h =>
  lc0_false fun {_} => (emp_sep.2.trans (sep_mono_left true_intro)).trans
    (@h (IProp CGF) _ _ _ _ True 0 0 false ⊤ iprop(True ∗ £ 0) iprop(True)
      iprop(True) iprop(|={⊤}=> ⌜False⌝)
      .rfl inferInstance trivial ⟨rfl⟩ true_intro)
end

namespace W8c2
open Iris Iris.BI Iris.OFE

/-! KW: an affine Kripke BI on four worlds a ≤ b ≤ c and d (isolated). Later at a looks at b; later is
trivially true at b, c, d (▷ False holds there). Persistently at a looks at a and d, elsewhere at the world
itself. ▷ commutes with <pers>, but <pers> (▷ False ∨ X) ⊬ ▷ False ∨ <pers> X for X := "not d" (at a):
a BI without BIPersistentlyExist where except0 does not commute with persistently. -/
inductive KW | a | b | c | d deriving DecidableEq

/-- The Kripke order. -/
def kle : KW → KW → Prop
  | .a, v => v ≠ .d
  | .b, v => v = .b ∨ v = .c
  | .c, v => v = .c
  | .d, v => v = .d

theorem kle_refl : ∀ w, kle w w
  | .a => fun h => nomatch h
  | .b => .inl rfl
  | .c => rfl
  | .d => rfl

theorem kle_ba {v : KW} (h : kle .b v) : kle .a v := by
  rcases h with rfl | rfl <;> exact fun h => nomatch h
theorem kle_cb {v : KW} (h : kle .c v) : kle .b v := .inr h

/-- Up-closed predicates on KW. -/
structure KQ where
  p : KW → Prop
  up_ab : p .a → p .b
  up_bc : p .b → p .c

theorem KQ.ext' {P Q : KQ} (h : ∀ w, P.p w ↔ Q.p w) : P = Q := by
  cases P; cases Q; congr; funext w; exact propext (h w)

theorem KQ.mono (P : KQ) : ∀ {v w : KW}, kle v w → P.p v → P.p w
  | .a, .a, _, h => h
  | .a, .b, _, h => P.up_ab h
  | .a, .c, _, h => P.up_bc (P.up_ab h)
  | .a, .d, e, _ => absurd rfl e
  | .b, .b, _, h => h
  | .b, .c, _, h => P.up_bc h
  | .b, .a, e, _ => by rcases e with e | e <;> cases e
  | .b, .d, e, _ => by rcases e with e | e <;> cases e
  | .c, .c, _, h => h
  | .c, .a, e, _ => by cases e
  | .c, .b, e, _ => by cases e
  | .c, .d, e, _ => by cases e
  | .d, .d, _, h => h
  | .d, .a, e, _ => by cases e
  | .d, .b, e, _ => by cases e
  | .d, .c, e, _ => by cases e

instance : COFE KQ := COFE.ofDiscrete _

/-- Kripke implication. -/
def KQ.imp (P Q : KQ) : KQ :=
  ⟨fun w => ∀ v, kle w v → P.p v → Q.p v, fun h v hv => h v (kle_ba hv), fun h v hv => h v (kle_cb hv)⟩

theorem KQ.imp_p {P Q : KQ} {w} (h : (KQ.imp P Q).p w) : P.p w → Q.p w := h w (kle_refl w)

theorem KQ.imp_intro' {R P Q : KQ} (h : ∀ w, R.p w ∧ P.p w → Q.p w) : ∀ w, R.p w → (KQ.imp P Q).p w :=
  fun _ hR v hv hP => h v ⟨R.mono hv hR, hP⟩

instance kwBase : BIBase KQ where
  Entails P Q := ∀ w, P.p w → Q.p w
  emp := ⟨fun _ => True, fun _ => trivial, fun _ => trivial⟩
  pure φ := ⟨fun _ => φ, id, id⟩
  and P Q := ⟨fun w => P.p w ∧ Q.p w, fun h => ⟨P.up_ab h.1, Q.up_ab h.2⟩, fun h => ⟨P.up_bc h.1, Q.up_bc h.2⟩⟩
  or P Q := ⟨fun w => P.p w ∨ Q.p w, fun h => h.imp P.up_ab Q.up_ab, fun h => h.imp P.up_bc Q.up_bc⟩
  imp := KQ.imp
  sForall Ψ := ⟨fun w => ∀ p, Ψ p → p.p w, fun h p hp => p.up_ab (h p hp), fun h p hp => p.up_bc (h p hp)⟩
  sExists Ψ := ⟨fun w => ∃ p, Ψ p ∧ p.p w, fun ⟨p, hp, h⟩ => ⟨p, hp, p.up_ab h⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, p.up_bc h⟩⟩
  sep P Q := ⟨fun w => P.p w ∧ Q.p w, fun h => ⟨P.up_ab h.1, Q.up_ab h.2⟩, fun h => ⟨P.up_bc h.1, Q.up_bc h.2⟩⟩
  wand := KQ.imp
  persistently P := ⟨fun w => P.p w ∧ (w = .a → P.p .d), fun h => ⟨P.up_ab h.1, (fun e => nomatch e)⟩,
    fun h => ⟨P.up_bc h.1, fun e => nomatch e⟩⟩
  later P := ⟨fun w => w = .a → P.p .b, (fun _ e => nomatch e), (fun _ e => nomatch e)⟩

instance kwBI : BI KQ where
  entails_refl _ h := h
  entails_trans h1 h2 w h := h2 w (h1 w h)
  equiv_iff {P Q} := ⟨fun e => e ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h1, h2⟩ => KQ.ext' fun w => ⟨h1 w, h2 w⟩⟩
  and_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  or_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  imp_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  sForall_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sExists_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sep_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  wand_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  later_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  persistently_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  pure_intro h _ _ := h
  pure_elim' h w hφ := h hφ w trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 w h := ⟨h1 w h, h2 w h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 w h := h.elim (h1 w) (h2 w)
  imp_intro h := KQ.imp_intro' h
  imp_elim h w hPQ := KQ.imp_p (h w hPQ.1) hPQ.2
  sForall_intro h w hP p hp := h p hp w hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h w := fun ⟨p, hp, hpw⟩ => h p hp w hpw
  sep_mono h1 h2 w h := ⟨h1 w h.1, h2 w h.2⟩
  emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩
  sep_symm _ h := ⟨h.2, h.1⟩
  sep_assoc_l _ h := ⟨h.1.1, h.1.2, h.2⟩
  wand_intro h := KQ.imp_intro' h
  wand_elim h w hPQ := KQ.imp_p (h w hPQ.1) hPQ.2
  persistently_mono h w hp := ⟨h w hp.1, fun e => h _ (hp.2 e)⟩
  persistently_idem_2 _ hp := ⟨hp, fun e => ⟨hp.2 e, (fun e2 => nomatch e2)⟩⟩
  persistently_emp_2 _ _ := ⟨trivial, fun _ => trivial⟩
  persistently_and_2 _ h := ⟨⟨h.1.1, h.2.1⟩, fun e => ⟨h.1.2 e, h.2.2 e⟩⟩
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1.1, h.2⟩
  later_mono h _ hl e := h _ (hl e)
  later_intro {P} w h e := by subst e; exact P.up_ab h
  later_sForall_2 _ h e p hp := KQ.imp_p (h _ ⟨p, rfl⟩) hp e
  later_sExists_false w hl := by
    cases w with
    | a =>
      obtain ⟨p, hp, hpb⟩ := hl rfl
      exact .inr ⟨_, ⟨p, rfl⟩, hp, fun _ => hpb⟩
    | b => exact .inl fun e => nomatch e
    | c => exact .inl fun e => nomatch e
    | d => exact .inl fun e => nomatch e
  later_sep := ⟨fun _ h => ⟨fun e => (h e).1, fun e => (h e).2⟩, fun _ h e => ⟨h.1 e, h.2 e⟩⟩
  later_persistently := ⟨fun _ h => ⟨fun e => (h e).1, (fun _ e2 => nomatch e2)⟩,
    fun _ h e => ⟨h.1 e, (fun e2 => nomatch e2)⟩⟩
  later_false_em {P} w h := by
    cases w with
    | a =>
      refine .inr fun v hv hf => ?_
      cases v with
      | a => exact absurd rfl hf
      | b => exact h rfl
      | c => exact P.up_bc (h rfl)
      | d => exact absurd rfl hv
    | b => exact .inl fun e => nomatch e
    | c => exact .inl fun e => nomatch e
    | d => exact .inl fun e => nomatch e

/-- X holds everywhere except at d. -/
def kX : KQ := ⟨fun w => w ≠ .d, (fun _ e => nomatch e), (fun _ e => nomatch e)⟩

/-- <pers> ◇ kX holds at a. -/
theorem kw_pe : (iprop(<pers> ◇ kX) : KQ).p .a :=
  ⟨.inr (fun e => nomatch e), (fun _ => .inl fun e => nomatch e)⟩

/-- ◇ <pers> kX fails at a. -/
theorem kw_ep (h : (iprop(◇ <pers> kX) : KQ).p .a) : False :=
  h.elim (fun hl => hl rfl) (fun hr => hr.2 rfl rfl)

end W8c2

section
open Iris Iris.BI Iris.ProofMode W8c2

-- `Iris.ProofMode.intoExcept0_persistently` idx 2: necessary (Kripke BI KW: P = ◇X, Q = X; <pers> ◇X holds at a, ◇ <pers> X does not)
theorem w8c2_132 : ¬ drop0% Iris.ProofMode.intoExcept0_persistently 2 := fun h =>
  kw_ep ((@h KQ _ iprop(◇ kX) kX ⟨.rfl⟩).into_except0 .a kw_pe)

-- `Iris.ProofMode.intoExcept0_intuitionistically` idx 2: necessary (Kripke BI KW: P = ◇X, Q = X at world a)
theorem w8c2_133 : ¬ drop0% Iris.ProofMode.intoExcept0_intuitionistically 2 := fun h =>
  kw_ep (((@h KQ _ iprop(◇ kX) kX ⟨.rfl⟩).into_except0 .a ⟨trivial, kw_pe⟩).imp id (·.2))

-- `Iris.ProofMode.intoAnd_except0` idx 2: necessary (Kripke BI KW: p = true, P = X, Q1 = Q2 = <pers> X at world a)
theorem w8c2_134 : ¬ drop0% Iris.ProofMode.intoAnd_except0 2 := fun h =>
  kw_ep (((@h KQ _ true kX iprop(<pers> kX) iprop(<pers> kX)
    ⟨fun _ hx => ⟨trivial, ⟨hx.2, hx.2⟩, fun e => ⟨⟨hx.2.2 e, fun e2 => nomatch e2⟩, ⟨hx.2.2 e, fun e2 => nomatch e2⟩⟩⟩⟩).into_and .a
    ⟨trivial, kw_pe⟩).2.1.1)

-- `Iris.ProofMode.elimModal_timeless` idx 2: necessary (Kripke BI KW: p = true, P = ◇X, P' = X, Q = ◇ <pers> X at world a)
theorem w8c2_135 : ¬ drop0% Iris.ProofMode.elimModal_timeless 2 := fun h =>
  kw_ep ((@h KQ _ true iprop(◇ kX) kX iprop(◇ <pers> kX) ⟨.rfl⟩ (isExcept0_except0 _)).elim_modal trivial .a
    ⟨⟨trivial, kw_pe⟩, (wand_intro (sep_elim_right.trans (affinely_elim.trans except0_intro)) :
      (emp : KQ) ⊢ iprop(□ kX -∗ ◇ <pers> kX)) .a trivial⟩)
end

namespace W8c2
open Iris Iris.BI

/-- Five-element UORA: e unit, a • b = x, every other non-unit product is the invalid z;
order: reflexive, e ≤ b, e ≤ x, a ≤ x, everything ≤ z. -/
inductive M5 | e | a | b | ab | bot deriving DecidableEq

def M5.op : M5 → M5 → M5
  | .e, y => y
  | y, .e => y
  | .a, .b => .ab
  | .b, .a => .ab
  | _, _ => .bot

def le5 : M5 → M5 → Bool
  | .e, .e => true | .e, .b => true | .e, .ab => true | .a, .a => true | .a, .ab => true
  | .b, .b => true | .ab, .ab => true | _, .bot => true | _, _ => false

instance : OFE M5 := OFE.ofDiscrete M5
instance : OFE.Discrete M5 := ⟨id⟩

instance m5ORA : ORA M5 := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := M5.op
  Valid := fun y => y ≠ .bot
  Order := fun y w => le5 y w = true
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y; cases x <;> cases y <;> decide
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := by intro x y; cases x <;> cases y <;> decide
  pcore_mono := by intro x y cx _ h2; cases h2; exact ⟨.e, rfl, rfl⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.e, rfl, rfl⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> rfl
  increasing_closed := by
    intro x y hx hxy w
    cases x <;> cases y <;> first
      | exact absurd hxy (by decide)
      | exact absurd (hx .e) (by decide)
      | (cases w <;> rfl) }

instance : OrderRefl M5 := ⟨fun y => by cases y <;> rfl⟩

instance m5UORA : UORA M5 where
  unit := .e
  unit_valid := fun h => nomatch h
  unit_left_id := rfl
  pcore_unit := rfl

end W8c2

namespace W8c2
open Iris Iris.BI

/-- emp = ownM unit is timeless in UPred M5 (discrete). -/
instance m5_emp_timeless : Timeless (emp : UPred M5) := UPred.ownM_timeless M5.e

/-- ownM b holds only above e, so it is affine. -/
instance ownb_affine : Affine (UPred.ownM M5.b) := ⟨fun n y hb => by
  obtain ⟨v, _⟩ := y
  change le5 .b v = true at hb
  change le5 .e v = true
  cases v <;> simp_all [le5]⟩

/-- In UPred M5 at step 1 and resource ab, <affine> ▷ (ownM a ∗ ownM b) holds. -/
theorem m5_lhs : (iprop(<affine> ▷ (UPred.ownM M5.a ∗ UPred.ownM M5.b)) : UPred M5).holds 1 ⟨.ab, fun h => nomatch h⟩ :=
  ⟨(rfl : le5 .e .ab = true), ⟨.a, .b, (rfl : le5 .ab .ab = true), (rfl : le5 .a .a = true), (rfl : le5 .b .b = true)⟩⟩

/-- … but <affine> ▷ ownM a ∗ <affine> ▷ ownM b does not: the only emp-resource above a is ab, and ab • b is invalid. -/
theorem m5_rhs (h : (iprop(<affine> ▷ UPred.ownM M5.a ∗ <affine> ▷ UPred.ownM M5.b) : UPred M5).holds 1 ⟨.ab, fun h => nomatch h⟩) :
    False := by
  obtain ⟨y1, y2, H, ⟨he1, ha⟩, ⟨he2, hb⟩⟩ := h
  change le5 (M5.op y1 y2) .ab = true at H
  change le5 .e y1 = true at he1
  change le5 .a y1 = true at ha
  change le5 .b y2 = true at hb
  cases y1 <;> cases y2 <;> first
    | exact absurd H (by decide)
    | exact absurd ha (by decide)
    | exact absurd hb (by decide)
    | exact absurd he1 (by decide)
    | exact absurd he2 (by decide)

/-- Swapped version. -/
theorem m5_lhs' : (iprop(<affine> ▷ (UPred.ownM M5.b ∗ UPred.ownM M5.a)) : UPred M5).holds 1 ⟨.ab, fun h => nomatch h⟩ :=
  ⟨(rfl : le5 .e .ab = true), ⟨.b, .a, (rfl : le5 .ab .ab = true), (rfl : le5 .b .b = true), (rfl : le5 .a .a = true)⟩⟩

theorem m5_rhs' (h : (iprop(<affine> ▷ UPred.ownM M5.b ∗ <affine> ▷ UPred.ownM M5.a) : UPred M5).holds 1 ⟨.ab, fun h => nomatch h⟩) :
    False := by
  obtain ⟨y1, y2, H, ⟨he1, hb⟩, ⟨he2, ha⟩⟩ := h
  change le5 (M5.op y1 y2) .ab = true at H
  change le5 .e y2 = true at he2
  change le5 .a y2 = true at ha
  change le5 .b y1 = true at hb
  cases y1 <;> cases y2 <;> first
    | exact absurd H (by decide)
    | exact absurd ha (by decide)
    | exact absurd hb (by decide)
    | exact absurd he1 (by decide)
    | exact absurd he2 (by decide)

end W8c2

section
open Iris Iris.BI Iris.ProofMode W8c2

-- `Iris.ProofMode.intoSep_affinely_later` idx 7: necessary (UPred over 5-element UORA M5 with e ≤ b, a • b = ab ≥ e: Q1 = ownM a (not affine), Q2 = ownM b (affine), P = Q1 ∗ Q2, at step 1 and resource ab)
theorem w8c2_136 : ¬ drop0% Iris.ProofMode.intoSep_affinely_later 7 := fun h =>
  m5_rhs ((@h (UPred M5) _ _ iprop(UPred.ownM M5.a ∗ UPred.ownM M5.b) (UPred.ownM M5.a) (UPred.ownM M5.b) ⟨.rfl⟩
    ownb_affine).into_sep 1 _ m5_lhs)

-- `Iris.ProofMode.intoSep_affinely_later` idx 8: necessary (UPred M5 as for idx 7 with Q1 = ownM b (affine), Q2 = ownM a (not affine))
theorem w8c2_137 : ¬ drop0% Iris.ProofMode.intoSep_affinely_later 8 := fun h =>
  m5_rhs' ((@h (UPred M5) _ _ iprop(UPred.ownM M5.b ∗ UPred.ownM M5.a) (UPred.ownM M5.b) (UPred.ownM M5.a) ⟨.rfl⟩
    ownb_affine).into_sep 1 _ m5_lhs')
end
