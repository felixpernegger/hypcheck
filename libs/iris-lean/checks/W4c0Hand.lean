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

namespace W4c0
open Iris Iris.BI

abbrev SP := Iris.SiProp
theorem tf_ne : (iprop(True) : SP) ≠ iprop(False) := fun e => cast (congrArg (fun P : SP => P.holds 0) e) trivial

end W4c0

section
open Iris Iris.BI W4c0

-- `Iris.BI.sForall_ne` idx 5: necessary (SiProp, n = 0: sForall of the empty set is True, sForall of the set of False is False)
theorem w4c0_1 : ¬ drop0% Iris.BI.sForall_ne 5 := fun h =>
  (((@h SP _ 0 (fun _ => False) (· = iprop(False))) (Nat.le_refl 0)).1 (fun _ hf => hf.elim)) _ rfl

-- `Iris.BI.sExists_ne` idx 5: necessary (SiProp, n = 0: sExists of the set of True vs the empty set)
theorem w4c0_2 : ¬ drop0% Iris.BI.sExists_ne 5 := fun h =>
  match ((@h SP _ 0 (· = iprop(True)) (fun _ => False)) (Nat.le_refl 0)).1 ⟨_, rfl, trivial⟩ with
  | ⟨_, hf, _⟩ => hf

-- `Iris.BI.pure_elim'` idx 4: necessary (SiProp: phi = True, P = False)
theorem w4c0_3 : ¬ drop0% Iris.BI.pure_elim' 4 := fun h =>
  (@h SP _ True iprop(False)) 0 trivial

-- `Iris.BI.and_intro` idx 5: necessary (SiProp: P = R = True, Q = False)
theorem w4c0_4 : ¬ drop0% Iris.BI.and_intro 5 := fun h =>
  ((@h SP _ iprop(True) iprop(False) iprop(True)) (fun _ h => h) 0 trivial).1

-- `Iris.BI.or_elim` idx 5: necessary (SiProp: P = True, Q = R = False)
theorem w4c0_5 : ¬ drop0% Iris.BI.or_elim 5 := fun h =>
  (@h SP _ iprop(True) iprop(False) iprop(False) (fun _ h => h)) 0 (Or.inl trivial)

-- `Iris.BI.or_elim` idx 6: necessary (SiProp: Q = True, P = R = False)
theorem w4c0_6 : ¬ drop0% Iris.BI.or_elim 6 := fun h =>
  (@h SP _ iprop(False) iprop(True) iprop(False) (fun _ h => h)) 0 (Or.inr trivial)

-- `Iris.BI.imp_intro` idx 5: necessary (SiProp: P = Q = True, R = False)
theorem w4c0_7 : ¬ drop0% Iris.BI.imp_intro 5 := fun h =>
  (@h SP _ iprop(True) iprop(True) iprop(False)) 0 trivial 0 (Nat.le_refl 0) trivial

-- `Iris.BI.imp_elim` idx 5: necessary (SiProp: P = Q = True, R = False)
theorem w4c0_8 : ¬ drop0% Iris.BI.imp_elim 5 := fun h =>
  (@h SP _ iprop(True) iprop(True) iprop(False)) 0 ⟨trivial, trivial⟩

-- `Iris.BI.sForall_intro` idx 4: necessary (SiProp: P = True, Psi = the set of False)
theorem w4c0_9 : ¬ drop0% Iris.BI.sForall_intro 4 := fun h =>
  (@h SP _ iprop(True) (· = iprop(False))) 0 trivial _ rfl

-- `Iris.BI.sForall_elim` idx 4: necessary (SiProp: Psi empty, p = False)
theorem w4c0_10 : ¬ drop0% Iris.BI.sForall_elim 4 := fun h =>
  (@h SP _ (fun _ => False) iprop(False)) 0 (fun _ hf => hf.elim)

-- `Iris.BI.sExists_intro` idx 4: necessary (SiProp: Psi empty, p = True)
theorem w4c0_11 : ¬ drop0% Iris.BI.sExists_intro 4 := fun h =>
  match (@h SP _ (fun _ => False) iprop(True)) 0 trivial with
  | ⟨_, hf, _⟩ => hf

-- `Iris.BI.sExists_elim` idx 4: necessary (SiProp: Phi = the set of True, Q = False)
theorem w4c0_12 : ¬ drop0% Iris.BI.sExists_elim 4 := fun h =>
  (@h SP _ (· = iprop(True)) iprop(False)) 0 ⟨_, rfl, trivial⟩

-- `Iris.BI.wand_intro` idx 5: necessary (SiProp: P = Q = True, R = False)
theorem w4c0_13 : ¬ drop0% Iris.BI.wand_intro 5 := fun h =>
  (@h SP _ iprop(True) iprop(True) iprop(False)) 0 trivial 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_elim` idx 5: necessary (SiProp: P = Q = True, R = False)
theorem w4c0_14 : ¬ drop0% Iris.BI.wand_elim 5 := fun h =>
  (@h SP _ iprop(True) iprop(True) iprop(False)) 0 ⟨trivial, trivial⟩

-- `Iris.BI.persistently_mono` idx 4: necessary (SiProp, persistently = id: P = True, Q = False)
theorem w4c0_15 : ¬ drop0% Iris.BI.persistently_mono 4 := fun h =>
  (@h SP _ iprop(True) iprop(False)) 0 trivial

-- `Iris.BI.later_mono` idx 4: necessary (SiProp at step 1: P = True, Q = False)
theorem w4c0_16 : ¬ drop0% Iris.BI.later_mono 4 := fun h =>
  (@h SP _ iprop(True) iprop(False)) 1 trivial

-- `Iris.BI.BIBase.Entails.of_eq` idx 4: necessary (SiProp: P = True, Q = False)
theorem w4c0_17 : ¬ drop0% Iris.BI.BIBase.Entails.of_eq 4 := fun h =>
  (@h SP _ iprop(True) iprop(False)) 0 trivial

-- `Iris.BI.BIBase.BiEntails.of_eq` idx 4: necessary (SiProp: P = True, Q = False)
theorem w4c0_18 : ¬ drop0% Iris.BI.BIBase.BiEntails.of_eq 4 := fun h =>
  (@h SP _ iprop(True) iprop(False)).1 0 trivial

-- `Eq.to_bi` idx 4: necessary (SiProp: P = True, Q = False)
theorem w4c0_19 : ¬ drop0% Eq.to_bi 4 := fun h =>
  (@h SP _ iprop(True) iprop(False)).1 0 trivial

-- `Iris.BI.BIBase.BiEntails.to_eq` idx 4: necessary (SiProp: True ≠ False)
theorem w4c0_20 : ¬ drop0% Iris.BI.BIBase.BiEntails.to_eq 4 := fun h =>
  tf_ne (@h SP _ iprop(True) iprop(False))

-- `Iris.BI.BIBase.BiEntails.symm` idx 4: necessary (SiProp: P = True, Q = False)
theorem w4c0_21 : ¬ drop0% Iris.BI.BIBase.BiEntails.symm 4 := fun h =>
  (@h SP _ iprop(True) iprop(False)).2 0 trivial

-- `Iris.BI.BIBase.BiEntails.trans` idx 5: necessary (SiProp: P = True, Q = R = False)
theorem w4c0_22 : ¬ drop0% Iris.BI.BIBase.BiEntails.trans 5 := fun h =>
  (@h SP _ iprop(True) iprop(False) iprop(False) ⟨fun _ h => h, fun _ h => h⟩).1 0 trivial

-- `Iris.BI.BIBase.BiEntails.trans` idx 6: necessary (SiProp: P = Q = True, R = False)
theorem w4c0_23 : ¬ drop0% Iris.BI.BIBase.BiEntails.trans 6 := fun h =>
  (@h SP _ iprop(True) iprop(True) iprop(False) ⟨fun _ h => h, fun _ h => h⟩).1 0 trivial

-- `Iris.BI.BIBase.BiEntails.ofMono` idx 5: removable (bi-entailment is equality in every BI, `BiEntails.to_eq`, so mod P = mod Q)
theorem w4c0_24 : drop% Iris.BI.BIBase.BiEntails.ofMono 5 := by
  intro PROP1 PROP2 _ _ mod P Q h
  rw [Iris.BI.BIBase.BiEntails.to_eq h]
  exact Iris.BI.BIBase.BiEntails.rfl

-- `Iris.BI.BIBase.BiEntails.ofMono` idx 8: necessary (SiProp, mod = id: P = True, Q = False)
theorem w4c0_25 : ¬ drop0% Iris.BI.BIBase.BiEntails.ofMono 8 := fun h =>
  (@h SP SP _ _ id (fun h => h) iprop(True) iprop(False)).1 0 trivial

-- `Iris.BI.BIBase.BiEntails.mpr` idx 4: necessary (SiProp: P = False, Q = True)
theorem w4c0_26 : ¬ drop0% Iris.BI.BIBase.BiEntails.mpr 4 := fun h =>
  (@h SP _ iprop(False) iprop(True)) 0 trivial
end

namespace W4c0
open Iris Iris.BI Iris.Instances.Data

-- helper: SiProp props that differ at step 0 are different
theorem holds_ne {P Q : SP} (e : P = Q) (hp : P.holds 0) (hq : ¬ Q.holds 0) : False := hq (e ▸ hp)

-- helper: step-indexed prop true only at step 0 (not timeless)
def s0 : SP := ⟨fun n => n = 0, fun h hle => by omega⟩

-- helper: non-affine BI HeapProp Unit, a non-empty heap
abbrev HP := Iris.Instances.Classical.HeapProp Unit
def s1 : State Unit := fun _ => result ()
theorem s1_ne : s1 ≠ ∅ := fun h => by have h0 := congrFun h 0; cases h0
-- helper: location 0 allocated (not persistent: fails at the empty heap)
def P1 : HP := fun σ => σ 0 ≠ unknown
theorem s1_split : s1 = s1 ∪ ∅ := (union_comm.trans empty_union.symm).symm
theorem s1_disj : s1 || (∅ : State Unit) := disjoint_comm.1 empty_disjoint

end W4c0

section
open Iris Iris.BI W4c0

-- `Iris.BI.BigAndL.bigAndL_mono` idx 6: necessary (SiProp, l = [()], Phi = True, Psi = False)
theorem w4c0_30 : ¬ drop0% Iris.BI.BigAndL.bigAndL_mono 6 := fun h =>
  ((@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]) 0 ⟨trivial, trivial⟩).1

-- `Iris.BI.BigAndL.bigAndL_eq` idx 6: necessary (SiProp, l = [()], Phi = True, Psi = False)
theorem w4c0_31 : ¬ drop0% Iris.BI.BigAndL.bigAndL_eq 6 := fun h =>
  holds_ne (@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]) ⟨trivial, trivial⟩ (fun hf => hf.1)

-- `Iris.BI.BigAndL.bigAndL_eq_of_forall_eq` idx 6: necessary (SiProp, l = [()], Phi = True, Psi = False)
theorem w4c0_32 : ¬ drop0% Iris.BI.BigAndL.bigAndL_eq_of_forall_eq 6 := fun h =>
  holds_ne (@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]) ⟨trivial, trivial⟩ (fun hf => hf.1)

-- `Iris.BI.BigAndL.bigAndL_affine_inst` idx 5: necessary (HeapProp Unit (non-affine), l = []: True is not affine)
theorem w4c0_33 : ¬ drop0% Iris.BI.BigAndL.bigAndL_affine_inst 5 := fun h =>
  s1_ne ((@h HP _ Unit (fun _ _ => iprop(True)) []).affine s1 trivial)

-- `Iris.BI.BigAndL.bigAndL_lookup` idx 7: necessary (SiProp, l = [], Phi = False)
theorem w4c0_34 : ¬ drop0% Iris.BI.BigAndL.bigAndL_lookup 7 := fun h =>
  (@h SP _ Unit (fun _ _ => iprop(False)) [] 0 ()) 0 trivial

-- `Iris.BI.BigAndL.bigAndL_mem` idx 6: necessary (SiProp, l = [], Phi = False)
theorem w4c0_35 : ¬ drop0% Iris.BI.BigAndL.bigAndL_mem 6 := fun h =>
  (@h SP _ Unit (fun _ => iprop(False)) [] ()) 0 trivial

-- `Iris.BI.BigAndL.bigAndL_perm` idx 6: necessary (SiProp, Phi b = (b = true), l1 = [true], l2 = [false])
theorem w4c0_36 : ¬ drop0% Iris.BI.BigAndL.bigAndL_perm 6 := fun h =>
  holds_ne (@h SP _ Bool (fun b => iprop(⌜b = true⌝)) [true] [false]) ⟨rfl, trivial⟩ (fun hf => Bool.false_ne_true hf.1)

-- `Iris.BI.BigAndL.bigAndL_submseteq` idx 7: necessary (SiProp, l1 = [()], l = l2 = [], Phi = False)
theorem w4c0_37 : ¬ drop0% Iris.BI.BigAndL.bigAndL_submseteq 7 := fun h =>
  ((@h SP _ Unit (fun _ => iprop(False)) [()] [] []) 0 trivial).1

-- `Iris.BI.BigAndL.bigAndL_dist` idx 7: necessary (SiProp, n = 0, l = [()], Phi = True, Psi = False)
theorem w4c0_38 : ¬ drop0% Iris.BI.BigAndL.bigAndL_dist 7 := fun h =>
  (((@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()] 0) (Nat.le_refl 0)).1
    ⟨trivial, trivial⟩).1

-- `Iris.BI.BigAndL.bigAndL_mono_of_forall` idx 6: necessary (SiProp, l = [()], Phi = True, Psi = False)
theorem w4c0_39 : ¬ drop0% Iris.BI.BigAndL.bigAndL_mono_of_forall 6 := fun h =>
  ((@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]) 0 ⟨trivial, trivial⟩).1

-- `Iris.BI.BigAndL.bigAndL_id_mono_of_forall` idx 4: necessary (SiProp, l1 = [], l2 = [False])
theorem w4c0_40 : ¬ drop0% Iris.BI.BigAndL.bigAndL_id_mono_of_forall 4 := fun h =>
  ((@h SP _ [] [iprop(False)] (fun _ _ _ h1 _ => by simp at h1)) 0 trivial).1

-- `Iris.BI.BigAndL.bigAndL_id_mono_of_forall` idx 5: necessary (SiProp, l1 = [True], l2 = [False])
theorem w4c0_41 : ¬ drop0% Iris.BI.BigAndL.bigAndL_id_mono_of_forall 5 := fun h =>
  ((@h SP _ [iprop(True)] [iprop(False)] rfl) 0 ⟨trivial, trivial⟩).1

-- `Iris.BI.BigAndL.bigAndL_absorbing` idx 5: necessary (HeapProp Unit, l = [()], Phi = emp: emp is not absorbing)
theorem w4c0_42 : ¬ drop0% Iris.BI.BigAndL.bigAndL_absorbing 5 := fun h =>
  s1_ne ((@h HP _ Unit (fun _ _ => iprop(emp)) [()]).absorbing s1
    ⟨s1, ∅, s1_split, s1_disj, trivial, rfl, trivial⟩).1

-- `Iris.BI.BigAndL.bigAndL_absorbing_inst` idx 5: necessary (HeapProp Unit, l = [()], Phi = emp: emp is not absorbing)
theorem w4c0_43 : ¬ drop0% Iris.BI.BigAndL.bigAndL_absorbing_inst 5 := fun h =>
  s1_ne ((@h HP _ Unit (fun _ _ => iprop(emp)) [()]).absorbing s1
    ⟨s1, ∅, s1_split, s1_disj, trivial, rfl, trivial⟩).1

-- `Iris.BI.BigAndL.bigAndL_persistent` idx 5: necessary (HeapProp Unit, l = [()], Phi = location 0 allocated: not persistent)
theorem w4c0_44 : ¬ drop0% Iris.BI.BigAndL.bigAndL_persistent 5 := fun h =>
  ((@h HP _ Unit (fun _ _ => P1) [()]).persistent s1 ⟨(fun h => nomatch h), trivial⟩).1 rfl

-- `Iris.BI.BigAndL.bigAndL_persistent_inst` idx 5: necessary (HeapProp Unit, l = [()], Phi = location 0 allocated: not persistent)
theorem w4c0_45 : ¬ drop0% Iris.BI.BigAndL.bigAndL_persistent_inst 5 := fun h =>
  ((@h HP _ Unit (fun _ _ => P1) [()]).persistent s1 ⟨(fun h => nomatch h), trivial⟩).1 rfl

-- `Iris.BI.BigAndL.bigAndL_timeless` idx 5: necessary (SiProp, l = [()], Phi = true only at step 0, at step 1)
theorem w4c0_46 : ¬ drop0% Iris.BI.BigAndL.bigAndL_timeless 5 := fun h =>
  match (@h SP _ Unit (fun _ _ => s0) [()]).timeless 1 ⟨rfl, trivial⟩ with
  | .inl hf => hf
  | .inr h1 => Nat.succ_ne_zero 0 h1.1

-- `Iris.BI.BigAndL.bigAndL_timeless_inst` idx 5: necessary (SiProp, l = [()], Phi = true only at step 0, at step 1)
theorem w4c0_47 : ¬ drop0% Iris.BI.BigAndL.bigAndL_timeless_inst 5 := fun h =>
  match (@h SP _ Unit (fun _ _ => s0) [()]).timeless 1 ⟨rfl, trivial⟩ with
  | .inl hf => hf
  | .inr h1 => Nat.succ_ne_zero 0 h1.1
end

section
open Iris Iris.BI W4c0

-- `Iris.BI.BigOrL.bigOrL_mono` idx 6: necessary (SiProp, l = [()], Phi = True, Psi = False)
theorem w4c0_50 : ¬ drop0% Iris.BI.BigOrL.bigOrL_mono 6 := fun h =>
  ((@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]) 0 (.inl trivial)).elim id id

-- `Iris.BI.BigOrL.bigOrL_eq` idx 6: necessary (SiProp, l = [()], Phi = True, Psi = False)
theorem w4c0_51 : ¬ drop0% Iris.BI.BigOrL.bigOrL_eq 6 := fun h =>
  holds_ne (@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]) (.inl trivial) (fun hf => hf.elim id id)

-- `Iris.BI.BigOrL.bigOrL_eq_of_forall_eq` idx 6: necessary (SiProp, l = [()], Phi = True, Psi = False)
theorem w4c0_52 : ¬ drop0% Iris.BI.BigOrL.bigOrL_eq_of_forall_eq 6 := fun h =>
  holds_ne (@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]) (.inl trivial) (fun hf => hf.elim id id)

-- `Iris.BI.BigOrL.bigOrL_dist` idx 7: necessary (SiProp, n = 0, l = [()], Phi = True, Psi = False)
theorem w4c0_53 : ¬ drop0% Iris.BI.BigOrL.bigOrL_dist 7 := fun h =>
  (((@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()] 0) (Nat.le_refl 0)).1
    (.inl trivial)).elim id id

-- `Iris.BI.BigOrL.bigOrL_intro` idx 7: necessary (SiProp, l = [], Phi = True)
theorem w4c0_54 : ¬ drop0% Iris.BI.BigOrL.bigOrL_intro 7 := fun h =>
  (@h SP _ Unit (fun _ _ => iprop(True)) [] 0 ()) 0 trivial

-- `Iris.BI.BigOrL.bigOrL_mem` idx 6: necessary (SiProp, l = [], Phi = True)
theorem w4c0_55 : ¬ drop0% Iris.BI.BigOrL.bigOrL_mem 6 := fun h =>
  (@h SP _ Unit (fun _ => iprop(True)) [] ()) 0 trivial

-- `Iris.BI.BigOrL.bigOrL_later` idx 5: necessary (SiProp, l = []: later False holds at step 0, False does not)
theorem w4c0_56 : ¬ drop0% Iris.BI.BigOrL.bigOrL_later 5 := fun h =>
  (@h SP _ Unit (fun _ _ => iprop(False)) []).1 0 trivial

-- `Iris.BI.BigOrL.bigOrL_laterN` idx 6: necessary (SiProp, l = [], n = 1: later False holds at step 0, False does not)
theorem w4c0_57 : ¬ drop0% Iris.BI.BigOrL.bigOrL_laterN 6 := fun h =>
  (@h SP _ Unit (fun _ _ => iprop(False)) [] 1).1 0 trivial

-- `Iris.BI.BigOrL.bigOrL_perm` idx 6: necessary (SiProp, Phi b = (b = true), l1 = [true], l2 = [false])
theorem w4c0_58 : ¬ drop0% Iris.BI.BigOrL.bigOrL_perm 6 := fun h =>
  holds_ne (@h SP _ Bool (fun b => iprop(⌜b = true⌝)) [true] [false]) (.inl rfl)
    (fun hf => hf.elim Bool.false_ne_true id)

-- `Iris.BI.BigOrL.bigOrL_submseteq` idx 7: necessary (SiProp, l1 = [()], l = l2 = [], Phi = True)
theorem w4c0_59 : ¬ drop0% Iris.BI.BigOrL.bigOrL_submseteq 7 := fun h =>
  (@h SP _ Unit (fun _ => iprop(True)) [()] [] []) 0 (.inl trivial)

-- `Iris.BI.BigOrL.bigOrL_mono_of_forall` idx 6: necessary (SiProp, l = [()], Phi = True, Psi = False)
theorem w4c0_60 : ¬ drop0% Iris.BI.BigOrL.bigOrL_mono_of_forall 6 := fun h =>
  ((@h SP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]) 0 (.inl trivial)).elim id id

-- `Iris.BI.BigOrL.bigOrL_id_mono_of_forall` idx 4: necessary (SiProp, l1 = [True], l2 = [])
theorem w4c0_61 : ¬ drop0% Iris.BI.BigOrL.bigOrL_id_mono_of_forall 4 := fun h =>
  (@h SP _ [iprop(True)] [] (fun _ h2 => by simp at h2)) 0 (.inl trivial)

-- `Iris.BI.BigOrL.bigOrL_id_mono_of_forall` idx 5: necessary (SiProp, l1 = [True], l2 = [False])
theorem w4c0_62 : ¬ drop0% Iris.BI.BigOrL.bigOrL_id_mono_of_forall 5 := fun h =>
  ((@h SP _ [iprop(True)] [iprop(False)] rfl) 0 (.inl trivial)).elim id id

-- `Iris.BI.BigOrL.bigOrL_persistent` idx 5: necessary (HeapProp Unit, l = [()], Phi = location 0 allocated: not persistent)
theorem w4c0_63 : ¬ drop0% Iris.BI.BigOrL.bigOrL_persistent 5 := fun h =>
  ((@h HP _ Unit (fun _ _ => P1) [()]).persistent s1 (.inl (fun h => nomatch h))).elim (fun h => h rfl) id

-- `Iris.BI.BigOrL.bigOrL_persistent_inst` idx 5: necessary (HeapProp Unit, l = [()], Phi = location 0 allocated: not persistent)
theorem w4c0_64 : ¬ drop0% Iris.BI.BigOrL.bigOrL_persistent_inst 5 := fun h =>
  ((@h HP _ Unit (fun _ _ => P1) [()]).persistent s1 (.inl (fun h => nomatch h))).elim (fun h => h rfl) id

-- `Iris.BI.BigOrL.bigOrL_timeless` idx 5: necessary (SiProp, l = [()], Phi = true only at step 0, at step 1)
theorem w4c0_65 : ¬ drop0% Iris.BI.BigOrL.bigOrL_timeless 5 := fun h =>
  match (@h SP _ Unit (fun _ _ => s0) [()]).timeless 1 (.inl rfl) with
  | .inl hf => hf
  | .inr h1 => h1.elim (Nat.succ_ne_zero 0) id

-- `Iris.BI.BigOrL.bigOrL_timeless_inst` idx 5: necessary (SiProp, l = [()], Phi = true only at step 0, at step 1)
theorem w4c0_66 : ¬ drop0% Iris.BI.BigOrL.bigOrL_timeless_inst 5 := fun h =>
  match (@h SP _ Unit (fun _ _ => s0) [()]).timeless 1 (.inl rfl) with
  | .inl hf => hf
  | .inr h1 => h1.elim (Nat.succ_ne_zero 0) id
end

namespace W4c0
open Iris Iris.BI Iris.Std LawfulPartialMap

-- helper: finite maps Nat → V
abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare
abbrev sg {V : Type} (i : Nat) (x : V) : TM V := PartialMap.insert ∅ i x

theorem insIns {V : Type} (a b : V) : PartialMap.insert (sg 0 a) 0 b = sg 0 b :=
  equiv_iff_eq.mp fun k => by
    by_cases hk : 0 = k
    · rw [get?_insert_eq hk, get?_insert_eq hk]
    · rw [get?_insert_ne hk, get?_insert_ne hk, get?_insert_ne hk]

theorem unionSg {M : Type → Type} [LawfulFiniteMap M Nat] {V : Type} (a b : V) :
    (PartialMap.insert (∅ : M V) 0 a ∪ PartialMap.insert ∅ 0 b) = PartialMap.insert ∅ 0 a :=
  equiv_iff_eq.mp fun k => by
    rw [get?_union]
    by_cases hk : 0 = k
    · rw [get?_insert_eq hk, get?_insert_eq hk]; rfl
    · rw [get?_insert_ne hk, get?_insert_ne hk, get?_empty]; rfl

-- helper: big conjunction over a singleton map, in any BI
theorem andM_sg {PROP : Type _} [BI PROP] {V : Type} {Φ : Nat → V → PROP} {i : Nat} {x : V} :
    ([∧map] k ↦ v ∈ sg i x, Φ k v) ⊣⊢ Φ i x :=
  (BigAndM.bigAndM_insert (get?_empty i)).trans
    ⟨and_elim_l, and_intro .rfl (true_intro.trans BigAndM.bigAndM_empty.2)⟩

theorem andM_sg_h {V : Type} {Φ : Nat → V → SP} {i : Nat} {x : V} {n : Nat} :
    ([∧map] k ↦ v ∈ sg i x, Φ k v).holds n ↔ (Φ i x).holds n := ⟨(andM_sg (PROP := SP)).1 n, (andM_sg (PROP := SP)).2 n⟩

theorem andM_emp_h {V : Type} {Φ : Nat → V → SP} {n : Nat} : ([∧map] k ↦ v ∈ (∅ : TM V), Φ k v).holds n :=
  (BigAndM.bigAndM_empty (PROP := SP)).2 n trivial

end W4c0

section
open Iris Iris.BI Iris.Std LawfulPartialMap W4c0

-- `Iris.BI.BigAndM.bigAndM_insert` idx 10: necessary (SiProp, m = {0 ↦ false}, insert 0 true, Phi k v = (v = true))
theorem w4c0_70 : ¬ drop0% Iris.BI.BigAndM.bigAndM_insert 10 := fun h => by
  have H := (@h SP _ Nat Bool TM _ (fun _ v => iprop(⌜v = true⌝)) (sg 0 false) 0 true).1 0
  rw [insIns] at H
  exact Bool.false_ne_true (andM_sg_h.1 (H (andM_sg_h.2 rfl)).2)

-- `Iris.BI.BigAndM.bigAndM_delete` idx 10: necessary (SiProp, m = ∅, Phi = False)
theorem w4c0_71 : ¬ drop0% Iris.BI.BigAndM.bigAndM_delete 10 := fun h =>
  ((@h SP _ Nat Unit TM _ (fun _ _ => iprop(False)) ∅ 0 ()).1 0 andM_emp_h).1

-- `Iris.BI.BigAndM.bigAndM_mono` idx 9: necessary (SiProp, m = {0 ↦ ()}, Phi = True, Psi = False)
theorem w4c0_72 : ¬ drop0% Iris.BI.BigAndM.bigAndM_mono 9 := fun h =>
  andM_sg_h.1 ((@h SP _ Nat Unit TM _ (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) (sg 0 ())) 0
    (andM_sg_h.2 trivial))

-- `Iris.BI.BigAndM.bigAndM_eq` idx 9: necessary (SiProp, m = {0 ↦ ()}, Phi = True, Psi = False)
theorem w4c0_73 : ¬ drop0% Iris.BI.BigAndM.bigAndM_eq 9 := fun h =>
  holds_ne (@h SP _ Nat Unit TM _ (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) (sg 0 ()))
    (andM_sg_h.2 trivial) (fun hf => andM_sg_h.1 hf)

-- `Iris.BI.BigAndM.bigAndM_eq_of_forall_eq` idx 9: necessary (SiProp, m = {0 ↦ ()}, Phi = True, Psi = False)
theorem w4c0_74 : ¬ drop0% Iris.BI.BigAndM.bigAndM_eq_of_forall_eq 9 := fun h =>
  holds_ne (@h SP _ Nat Unit TM _ (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) (sg 0 ()))
    (andM_sg_h.2 trivial) (fun hf => andM_sg_h.1 hf)

-- `Iris.BI.BigAndM.bigAndM_dist` idx 10: necessary (SiProp, n = 0, m = {0 ↦ ()}, Phi = True, Psi = False)
theorem w4c0_75 : ¬ drop0% Iris.BI.BigAndM.bigAndM_dist 10 := fun h =>
  andM_sg_h.1 (((@h SP _ Nat Unit TM _ (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) (sg 0 ()) 0)
    (Nat.le_refl 0)).1 (andM_sg_h.2 trivial))

-- `Iris.BI.BigAndM.bigAndM_mono_of_forall` idx 9: necessary (SiProp, m = {0 ↦ ()}, Phi = True, Psi = False)
theorem w4c0_76 : ¬ drop0% Iris.BI.BigAndM.bigAndM_mono_of_forall 9 := fun h =>
  andM_sg_h.1 ((@h SP _ Nat Unit TM _ (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) (sg 0 ())) 0
    (andM_sg_h.2 trivial))

-- `Iris.BI.BigAndM.bigAndM_affine_inst` idx 8: necessary (HeapProp Unit (non-affine), m = ∅: True is not affine)
theorem w4c0_77 : ¬ drop0% Iris.BI.BigAndM.bigAndM_affine_inst 8 := fun h =>
  s1_ne ((@h HP _ Nat Unit TM _ (fun _ _ => iprop(True)) ∅).affine s1 ((BigAndM.bigAndM_empty (PROP := HP)).2 s1 trivial))

-- `Iris.BI.BigAndM.bigAndM_persistent` idx 8: necessary (HeapProp Unit, m = {0 ↦ ()}, Phi = location 0 allocated: not persistent)
theorem w4c0_78 : ¬ drop0% Iris.BI.BigAndM.bigAndM_persistent 8 := fun h => by
  have H := @h HP _ Nat Unit TM _ (fun _ _ => P1) (sg 0 ())
  rw [andM_sg.to_eq] at H
  exact H.persistent s1 (fun h => nomatch h) rfl

-- `Iris.BI.BigAndM.bigAndM_persistent_inst` idx 8: necessary (HeapProp Unit, m = {0 ↦ ()}, Phi = location 0 allocated: not persistent)
theorem w4c0_79 : ¬ drop0% Iris.BI.BigAndM.bigAndM_persistent_inst 8 := fun h => by
  have H := @h HP _ Nat Unit TM _ (fun _ _ => P1) (sg 0 ())
  rw [andM_sg.to_eq] at H
  exact H.persistent s1 (fun h => nomatch h) rfl

-- `Iris.BI.BigAndM.bigAndM_absorbing` idx 8: necessary (HeapProp Unit, m = {0 ↦ ()}, Phi = emp: not absorbing)
theorem w4c0_80 : ¬ drop0% Iris.BI.BigAndM.bigAndM_absorbing 8 := fun h => by
  have H := @h HP _ Nat Unit TM _ (fun _ _ => iprop(emp)) (sg 0 ())
  rw [andM_sg.to_eq] at H
  exact s1_ne (H.absorbing s1 ⟨s1, ∅, s1_split, s1_disj, trivial, rfl⟩)

-- `Iris.BI.BigAndM.bigAndM_absorbing_inst` idx 8: necessary (HeapProp Unit, m = {0 ↦ ()}, Phi = emp: not absorbing)
theorem w4c0_81 : ¬ drop0% Iris.BI.BigAndM.bigAndM_absorbing_inst 8 := fun h => by
  have H := @h HP _ Nat Unit TM _ (fun _ _ => iprop(emp)) (sg 0 ())
  rw [andM_sg.to_eq] at H
  exact s1_ne (H.absorbing s1 ⟨s1, ∅, s1_split, s1_disj, trivial, rfl⟩)

-- `Iris.BI.BigAndM.bigAndM_timeless` idx 8: necessary (SiProp, m = {0 ↦ ()}, Phi = true only at step 0, at step 1)
theorem w4c0_82 : ¬ drop0% Iris.BI.BigAndM.bigAndM_timeless 8 := fun h => by
  have H := @h SP _ Nat Unit TM _ (fun _ _ => s0) (sg 0 ())
  rw [andM_sg.to_eq] at H
  match H.timeless 1 rfl with
  | .inl hf => exact hf
  | .inr h1 => exact Nat.succ_ne_zero 0 h1

-- `Iris.BI.BigAndM.bigAndM_timeless_inst` idx 8: necessary (SiProp, m = {0 ↦ ()}, Phi = true only at step 0, at step 1)
theorem w4c0_83 : ¬ drop0% Iris.BI.BigAndM.bigAndM_timeless_inst 8 := fun h => by
  have H := @h SP _ Nat Unit TM _ (fun _ _ => s0) (sg 0 ())
  rw [andM_sg.to_eq] at H
  match H.timeless 1 rfl with
  | .inl hf => exact hf
  | .inr h1 => exact Nat.succ_ne_zero 0 h1

-- `Iris.BI.BigAndM.bigAndM_lookup` idx 10: necessary (SiProp, m = ∅, Phi = False)
theorem w4c0_84 : ¬ drop0% Iris.BI.BigAndM.bigAndM_lookup 10 := fun h =>
  (@h SP _ Nat Unit TM _ (fun _ _ => iprop(False)) ∅ 0 ()) 0 andM_emp_h

-- `Iris.BI.BigAndM.bigAndM_lookup_dom` idx 10: necessary (SiProp, m = ∅, Phi = False)
theorem w4c0_85 : ¬ drop0% Iris.BI.BigAndM.bigAndM_lookup_dom 10 := fun h =>
  (@h SP _ Nat Unit TM _ (fun _ => iprop(False)) ∅ 0 ()) 0 ((BigAndM.bigAndM_empty (PROP := SP)).2 0 trivial)

-- `Iris.BI.BigAndM.bigAndM_intro` idx 9: necessary (SiProp, P = True, m = {0 ↦ ()}, Phi = False)
theorem w4c0_86 : ¬ drop0% Iris.BI.BigAndM.bigAndM_intro 9 := fun h =>
  andM_sg_h.1 ((@h SP _ Nat Unit TM _ iprop(True) (fun _ _ => iprop(False)) (sg 0 ())) 0 trivial)

-- `Iris.BI.BigAndM.bigAndM_subseteq` idx 9: necessary (SiProp, m1 = ∅, m2 = {0 ↦ ()}, Phi = False)
theorem w4c0_87 : ¬ drop0% Iris.BI.BigAndM.bigAndM_subseteq 9 := fun h =>
  andM_sg_h.1 ((@h SP _ Nat Unit TM _ (fun _ _ => iprop(False)) ∅ (sg 0 ())) 0 andM_emp_h)

-- `Iris.BI.BigAndM.bigAndM_union` idx 10: necessary (SiProp, m1 = {0 ↦ true}, m2 = {0 ↦ false}, Phi k v = (v = true))
theorem w4c0_88 : ¬ drop0% Iris.BI.BigAndM.bigAndM_union 10 := fun h => by
  have H := (@h SP _ Nat Bool TM _ _ (fun _ v => iprop(⌜v = true⌝)) (sg 0 true) (sg 0 false)).1 0
  rw [unionSg] at H
  exact Bool.false_ne_true (andM_sg_h.1 (H (andM_sg_h.2 rfl)).2)

-- `Iris.BI.BigAndM.bigAndM_insert_override` idx 12: necessary (SiProp, m = {0 ↦ false}, insert 0 true, Phi k v = (v = true))
theorem w4c0_89 : ¬ drop0% Iris.BI.BigAndM.bigAndM_insert_override 12 := fun h => by
  have H := @h SP _ Nat Bool TM _ (fun _ v => iprop(⌜v = true⌝)) (sg 0 false) 0 false true (get?_insert_eq rfl)
  rw [insIns] at H
  exact holds_ne H (andM_sg_h.2 rfl) (fun hf => Bool.false_ne_true (andM_sg_h.1 hf))

-- `Iris.BI.BigAndM.bigAndM_fn_insert` idx 14: necessary (SiProp, m = {0 ↦ ()}, i = 0, b = true, f = false, g k y c = (c = true))
theorem w4c0_90 : ¬ drop0% Iris.BI.BigAndM.bigAndM_fn_insert 14 := fun h => by
  have H := @h SP _ Nat Unit TM _ _ Bool (fun _ _ c => iprop(⌜c = true⌝)) (fun _ => false) (sg 0 ()) 0 () true
  rw [insIns] at H
  exact holds_ne H (andM_sg_h.2 (by simp)) (fun hf => Bool.false_ne_true (andM_sg_h.1 hf.2))

-- `Iris.BI.BigAndM.bigAndM_fn_insert_cond` idx 12: necessary (SiProp, m = {0 ↦ ()}, i = 0, P = True, f = False)
theorem w4c0_91 : ¬ drop0% Iris.BI.BigAndM.bigAndM_fn_insert_cond 12 := fun h => by
  have H := @h SP _ Nat Unit TM _ _ (fun _ => iprop(False)) (sg 0 ()) 0 () iprop(True)
  rw [insIns] at H
  exact holds_ne H (andM_sg_h.2 (by simp)) (fun hf => andM_sg_h.1 hf.2)
end

namespace W4c0
open Iris Iris.BI Iris.Std LawfulPartialMap LawfulFiniteMap

-- helper: a non-empty list whose keys are all 0 builds the singleton of its head value
theorem ofList_zero {V : Type} : ∀ (e : Nat × V) (L : List (Nat × V)), (∀ x ∈ e :: L, x.1 = 0) →
    (PartialMap.ofList (e :: L) : TM V) = sg 0 e.2
  | (k, v), [], hL => by
    have hk : k = 0 := hL _ (List.mem_cons_self ..)
    subst hk; rfl
  | (k, v), e' :: L', hL => by
    have hk : k = 0 := hL _ (List.mem_cons_self ..)
    subst hk
    rw [ofList_cons, ofList_zero e' L' (fun x hx => hL x (List.mem_cons_of_mem _ hx)), insIns]

-- helper: the two-key map {0 ↦ true, 1 ↦ false}
abbrev tw : TM Bool := PartialMap.insert (sg 0 true) 1 false

theorem tw_get0 : get? tw 0 = some true := by
  rw [get?_insert_ne (by decide), get?_insert_eq rfl]

/-- Renaming both keys of tw to 0 gives a singleton map. -/
theorem kmap_tw : ∃ v : Bool, (FiniteMap.kmap (fun _ : Nat => (0 : Nat)) tw : TM Bool) = sg 0 v := by
  unfold FiniteMap.kmap
  cases hL : FiniteMap.toList tw with
  | nil =>
    have := (toList_get?_none (k := 0) (m := tw)).1 (fun v hv => by have hv2 : (0, v) ∈ FiniteMap.toList tw := hv; rw [hL] at hv2; cases hv2)
    rw [tw_get0] at this; cases this
  | cons e L =>
    refine ⟨e.2, ?_⟩
    rw [List.map_cons]
    exact ofList_zero _ _ (fun x hx => by
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨_, _, rfl⟩ <;> rfl)

theorem tw_andM {Φ : Nat → Bool → SP} {n : Nat} (h : ([∧map] k ↦ x ∈ tw, Φ k x).holds n) :
    (Φ 1 false).holds n ∧ (Φ 0 true).holds n := by
  have e := (BigAndM.bigAndM_insert (PROP := SP) (Φ := Φ) (m := sg 0 true) (i := 1) (x := false)
    ((get?_insert_ne (by decide)).trans (get?_empty 1))).1 n h
  exact ⟨e.1, andM_sg_h.1 e.2⟩

end W4c0

section
open Iris Iris.BI Iris.Std W4c0

-- `Iris.BI.BigAndM.bigAndM_kmap` idx 13: necessary (SiProp, m = {0 ↦ true, 1 ↦ false}, f = constant 0: kmap is a singleton {0 ↦ v}, Phi k b = (b = v); the right side needs both v = true and v = false)
theorem w4c0_170 : ¬ drop0% Iris.BI.BigAndM.bigAndM_kmap 13 := fun h => by
  obtain ⟨v, hv⟩ := kmap_tw
  have H := @h SP _ Nat Bool TM _ Nat TM _ _ (fun _ => 0) (fun _ b => iprop(⌜b = v⌝)) tw
  rw [hv] at H
  have := tw_andM (H ▸ (andM_sg_h.2 rfl : ([∧map] k ↦ x ∈ sg 0 v, (fun _ b => iprop(⌜b = v⌝) : Nat → Bool → SP) k x).holds 0))
  exact Bool.false_ne_true ((show false = v from this.1).trans (show true = v from this.2).symm)
end

namespace W4c0
open Iris Iris.BI

/-- Two-world classical propositions; persistently P := ⌜emp ⊢ P⌝ ("P holds in every world").
A discrete BI in which persistently does not commute with disjunction (no BIPersistentlyExist). -/
structure KP where p : Bool → Prop

theorem KP.ext' {P Q : KP} (h : ∀ w, P.p w ↔ Q.p w) : P = Q := by
  cases P; cases Q; congr; funext w; exact propext (h w)

instance : COFE KP := COFE.ofDiscrete _

instance kpBase : BIBase KP where
  Entails P Q := ∀ w, P.p w → Q.p w
  emp := ⟨fun _ => True⟩
  pure φ := ⟨fun _ => φ⟩
  and P Q := ⟨fun w => P.p w ∧ Q.p w⟩
  or P Q := ⟨fun w => P.p w ∨ Q.p w⟩
  imp P Q := ⟨fun w => P.p w → Q.p w⟩
  sForall Ψ := ⟨fun w => ∀ p, Ψ p → p.p w⟩
  sExists Ψ := ⟨fun w => ∃ p, Ψ p ∧ p.p w⟩
  sep P Q := ⟨fun w => P.p w ∧ Q.p w⟩
  wand P Q := ⟨fun w => P.p w → Q.p w⟩
  persistently P := ⟨fun _ => ∀ w, True → P.p w⟩
  later P := P

instance kpBI : BI KP := BI.ofPersistentlyDiscrete
  (entails_refl := fun _ h => h)
  (entails_trans := fun h1 h2 w h => h2 w (h1 w h))
  (equiv_iff := fun {P Q} => ⟨fun e => e ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h1, h2⟩ => KP.ext' fun w => ⟨h1 w, h2 w⟩⟩)
  (pure_intro := fun h _ _ => h)
  (pure_elim' := fun h w hφ => h hφ w trivial)
  (and_elim_l := fun _ h => h.1)
  (and_elim_r := fun _ h => h.2)
  (and_intro := fun h1 h2 w h => ⟨h1 w h, h2 w h⟩)
  (or_intro_l := fun _ h => .inl h)
  (or_intro_r := fun _ h => .inr h)
  (or_elim := fun h1 h2 w h => h.elim (h1 w) (h2 w))
  (imp_intro := fun h w hP hQ => h w ⟨hP, hQ⟩)
  (imp_elim := fun h w hPQ => h w hPQ.1 hPQ.2)
  (sForall_intro := fun h w hP p hp => h p hp w hP)
  (sForall_elim := fun hp _ h => h _ hp)
  (sExists_intro := fun hp _ h => ⟨_, hp, h⟩)
  (sExists_elim := fun h w ⟨p, hp, hpw⟩ => h p hp w hpw)
  (sep_mono := fun h1 h2 w h => ⟨h1 w h.1, h2 w h.2⟩)
  (emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩)
  (sep_symm := fun _ h => ⟨h.2, h.1⟩)
  (sep_assoc_l := fun _ h => ⟨h.1.1, h.1.2, h.2⟩)
  (wand_intro := fun h w hP hQ => h w ⟨hP, hQ⟩)
  (wand_elim := fun h w hPQ => h w hPQ.1 hPQ.2)
  (later_mono := fun h => h)
  (later_intro := fun _ h => h)
  (later_sForall_2 := fun _ h p hp => h _ ⟨p, rfl⟩ hp)
  (later_sExists_false := fun _ ⟨p, hp, hpw⟩ => .inr ⟨_, ⟨p, rfl⟩, hp, hpw⟩)
  (later_sep := ⟨fun _ h => h, fun _ h => h⟩)
  (later_persistently := ⟨fun _ h => h, fun _ h => h⟩)
  (later_false_em := fun _ h => .inr (fun _ => h))
  (discrete := fun h => h)
  (persistently_eq := fun _ => rfl)

def kT : KP := ⟨fun w => w = true⟩
def kF : KP := ⟨fun w => w = false⟩

/-- persistently (kT ∨ kF) holds, persistently kT ∨ persistently kF does not. -/
theorem kp_pers_or : ¬ ((iprop(<pers> (kT ∨ kF)) : KP) ⊢ iprop(<pers> kT ∨ <pers> kF)) := fun h =>
  match h true (fun w _ => match w with | true => Or.inl rfl | false => Or.inr rfl) with
  | .inl h1 => Bool.false_ne_true (h1 false trivial)
  | .inr h2 => Bool.false_ne_true (h2 true trivial).symm

end W4c0

section
open Iris Iris.BI W4c0

-- `Iris.BI.bi_persistently_or_homomorphism` idx 2: necessary (two-world discrete BI KP with persistently P = ⌜emp ⊢ P⌝: persistently does not distribute over ∨)
theorem w4c0_110 : ¬ drop0% Iris.BI.bi_persistently_or_homomorphism 2 := fun h =>
  kp_pers_or (BI.BIBase.BiEntails.of_eq ((@h KP kpBI).map_op (x := kT) (y := kF))).1

-- `Iris.BI.BigOrL.bigOrL_persistently` idx 3: necessary (KP, l = [true, false], Phi k b = (world = b))
theorem w4c0_111 : ¬ drop0% Iris.BI.BigOrL.bigOrL_persistently 3 := fun h =>
  match (@h KP kpBI Bool (fun _ b => ⟨fun w => w = b⟩) [true, false]).1 true
    (fun w _ => match w with | true => Or.inl rfl | false => Or.inr (Or.inl rfl)) with
  | .inl h1 => Bool.false_ne_true (h1 false trivial)
  | .inr (.inl h2) => Bool.false_ne_true (h2 true trivial).symm
  | .inr (.inr hf) => hf

-- `Iris.BI.bi_persistently_sep_homomorphism` idx 2: necessary (HeapProp Unit (non-affine): persistently emp = True ≠ emp)
theorem w4c0_112 : ¬ drop0% Iris.BI.bi_persistently_sep_homomorphism 2 := fun h =>
  s1_ne (cast (congrFun (@h HP _).map_unit s1) (rfl : (∅ : Iris.Instances.Data.State Unit) = ∅))
end

namespace W4c0
open Iris Iris.OFE

/-- Discrete ORA on booleans: op is and, no core, order is equality (Probe1 BA). OrderRefl, not IncOrd, false not Increasing. -/
structure BA where b : Bool
instance : OFE BA := OFE.ofDiscrete BA
instance : OFE.Discrete BA := ⟨fun h => h⟩
def baData : DiscreteORAData BA where
  pcore _ := none
  op x y := ⟨x.b && y.b⟩
  Valid _ := True
  Order := Eq
  assoc x y z := congrArg BA.mk (Bool.and_assoc x.b y.b z.b).symm
  comm x y := congrArg BA.mk (Bool.and_comm x.b y.b)
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ h := h ▸ rfl
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ hx hxy := hxy ▸ hx
instance baORA : ORA BA := ORA.ofDiscreteORAData baData
instance baRefl : OrderRefl BA := ⟨fun _ => rfl⟩
theorem ba_not_inc : ¬ Increasing (⟨false⟩ : BA) := fun h => by
  have := h.increasing ⟨true⟩
  cases this

/-- Discrete ORA on Nat (W2c0 SN): x • y = x + y + 1, no core, order is strict <. IsInc, not OrderRefl, x ⋠ x. -/
structure SN where n : Nat
def snData : DiscreteORAData SN where
  pcore _ := none
  op x y := ⟨x.n + y.n + 1⟩
  Valid _ := True
  Order x y := x.n < y.n
  assoc x y z := by simp only [SN.mk.injEq]; omega
  comm x y := by simp only [SN.mk.injEq]; omega
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := Nat.lt_trans h1 h2
  op_mono_left _ _ _ h := by show _ < _; simp only; omega
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ _ z := by show _ < _; simp only; omega
instance : OFE SN := OFE.ofDiscrete SN
instance : OFE.Discrete SN := ⟨fun h => h⟩
instance snORA : ORA SN := ORA.ofDiscreteORAData snData
theorem sn_op (x y : SN) : x • y = ⟨x.n + y.n + 1⟩ := rfl
instance snIsInc : IsInc SN where
  inc_ord := fun ⟨z, hz⟩ => by subst hz; show _ < _; simp only [sn_op]; omega
  ord_inc {x y} h := ⟨⟨y.n - x.n - 1⟩, by
    have : x.n < y.n := h
    cases x; cases y; simp only [sn_op, SN.mk.injEq] at *; omega⟩
  ordN_incN {_ x y} h := ⟨⟨y.n - x.n - 1⟩, by
    have : x.n < y.n := h
    cases x; cases y; apply OFE.Dist.of_eq; simp only [sn_op, SN.mk.injEq] at *; omega⟩
theorem sn_not_incN {n} (x : SN) : ¬ x ≼{n} x := fun ⟨z, hz⟩ => by
  have := congrArg SN.n (OFE.discrete hz); simp only [sn_op] at this; omega
theorem sn_zero_not_op {n} (z1 z2 : SN) : ¬ (⟨0⟩ : SN) ≡{n}≡ z1 • z2 := fun hz => by
  have := congrArg SN.n (OFE.discrete hz); simp only [sn_op] at this; omega

end W4c0

section
open Iris Iris.OFE W4c0

-- `Iris.option_ord_totalI` idx 4: necessary (SiProp, A = BA (bool and, order =; OrderRefl): none ≼ₒ some false would make false Increasing)
theorem w4c0_120 : ¬ drop0% Iris.option_ord_totalI 4 := fun h =>
  ba_not_inc (Option.none_ordN_some_iff.1 ((@h SP BA _ _ baRefl none (some ⟨false⟩)).2 0 trivial))

-- `Iris.option_ord_totalI` idx 5: necessary (SiProp, A = SN (x•y = x+y+1, order <; IncOrd, not OrderRefl): some 0 ≼ₒ some 0 holds, 0 ≼ₒ 0 fails)
theorem w4c0_121 : ¬ drop0% Iris.option_ord_totalI 5 := fun h =>
  Nat.lt_irrefl 0 ((@h SP SN _ _ inferInstance (some ⟨0⟩) (some ⟨0⟩)).1 0
    (Option.some_ordN_some_iff.2 (.inl OFE.Dist.rfl)))

-- `Iris.option_included_totalI` idx 4: necessary (SiProp, A = SN (no core): some 0 ≼ some 0, but 0 ⋠ 0)
theorem w4c0_122 : ¬ drop0% Iris.option_included_totalI 4 := fun h =>
  match SiProp.exists_holds.1 ((@h SP SN _ _ (some ⟨0⟩) (some ⟨0⟩)).1 0
    (SiProp.exists_holds.2 ⟨none, OFE.Dist.rfl⟩)) with
  | ⟨c, hc⟩ => sn_not_incN _ ⟨c, hc⟩

-- `Iris.Some_included_totalI` idx 4: necessary (SiProp, A = SN (no core): some 0 ≼ some 0, but 0 ⋠ 0)
theorem w4c0_123 : ¬ drop0% Iris.Some_included_totalI 4 := fun h =>
  match SiProp.exists_holds.1 ((@h SP SN _ _ ⟨0⟩ ⟨0⟩).1 0
    (SiProp.exists_holds.2 ⟨none, OFE.Dist.rfl⟩)) with
  | ⟨c, hc⟩ => sn_not_incN _ ⟨c, hc⟩

-- `Iris.some_ordI` idx 4: necessary (SiProp, A = SN (order <, not OrderRefl): some 0 ≼ₒ some 0 holds, 0 ≼ₒ 0 fails)
theorem w4c0_124 : ¬ drop0% Iris.some_ordI 4 := fun h =>
  Nat.lt_irrefl 0 ((@h SP SN _ _ ⟨0⟩ ⟨0⟩).1 0 (Option.some_ordN_some_iff.2 (.inl OFE.Dist.rfl)))

-- `Iris.cmra_later_opI` idx 4: necessary (SiProp at step 0, A = SN (no core): 0 is no product z1 • z2)
theorem w4c0_125 : ¬ drop0% Iris.cmra_later_opI 4 := fun h =>
  match SiProp.exists_holds.1 ((@h SP _ SN _ ⟨0⟩ ⟨0⟩ ⟨0⟩) 0 trivial) with
  | ⟨z1, hz⟩ => match SiProp.exists_holds.1 hz with
    | ⟨z2, hx, _⟩ => sn_zero_not_op z1 z2 hx

-- `Iris.f_homom_includedI` idx 10: necessary (SiProp, A = B = SN, f = constant 0: 0 ≼ 1, but 0 ⋠ 0)
theorem w4c0_126 : ¬ drop0% Iris.f_homom_includedI 10 := fun h =>
  match SiProp.exists_holds.1 ((@h SP _ SN SN _ _ ⟨0⟩ ⟨1⟩ (fun _ => ⟨0⟩) ⟨fun _ _ _ _ => OFE.Dist.rfl⟩) 0
    (SiProp.exists_holds.2 ⟨⟨0⟩, OFE.Dist.rfl⟩)) with
  | ⟨c, hc⟩ => sn_not_incN _ ⟨c, hc⟩

-- `Iris.id_freeI_r` idx 6: necessary (SiProp, A = BA (bool and): false • false = false, valid)
theorem w4c0_127 : ¬ drop0% Iris.id_freeI_r 6 := fun h =>
  (@h SP _ BA _ ⟨false⟩ ⟨false⟩) 0 trivial 0 (Nat.le_refl 0) trivial 0 (Nat.le_refl 0) OFE.Dist.rfl

-- `Iris.id_freeI_l` idx 6: necessary (SiProp, A = BA (bool and): false • false = false, valid)
theorem w4c0_128 : ¬ drop0% Iris.id_freeI_l 6 := fun h =>
  (@h SP _ BA _ ⟨false⟩ ⟨false⟩) 0 trivial 0 (Nat.le_refl 0) trivial 0 (Nat.le_refl 0) OFE.Dist.rfl
end

namespace W4c0
open Iris Iris.OFE

/-- Two-element commutative monoid (e unit, a idempotent) with the equality order (W1c0 NA): not IncOrd. -/
inductive NA | e | a deriving DecidableEq
def NA.op : NA → NA → NA
  | .e, y => y
  | .a, _ => .a
instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨id⟩
@[instance_reducible] def naData : DiscreteORAData NA where
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
  increasing_closed := by intro x y _ h; cases h; assumption
instance naORA : ORA NA := ORA.ofDiscreteORAData naData
instance : ORA.Discrete NA := ORA.ofDiscreteORAData_discrete naData
instance : OrderRefl NA := ⟨fun x => show x = x from rfl⟩
instance naUORA : UORA NA where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

/-- Three elements e (unit), a (idempotent), z (absorbing, invalid); order x ≤ y iff y = z or x ≠ z
(W1c0 TX): a ≤ e although a is not included in e, not OrdInc. -/
inductive TX | e | a | z deriving DecidableEq
def TX.op : TX → TX → TX
  | .e, y => y
  | x, .e => x
  | .a, .a => .a
  | _, _ => .z
instance : OFE TX := OFE.ofDiscrete TX
instance : OFE.Discrete TX := ⟨id⟩
@[instance_reducible] def txData : DiscreteORAData TX where
  pcore := fun _ => some .e
  op := TX.op
  Valid := fun x => x ≠ .z
  Order := fun x y => y = .z ∨ x ≠ .z
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y; cases x <;> cases y <;> decide
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := by intro x y; cases x <;> cases y <;> decide
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨.e, rfl, by decide⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.e, rfl, by decide⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> decide
  increasing_closed := by intro x y _ _ w; cases y <;> cases w <;> decide
instance txORA : ORA TX := ORA.ofDiscreteORAData txData
instance : ORA.Discrete TX := ORA.ofDiscreteORAData_discrete txData
instance : OrderRefl TX := ⟨fun x => show x = .z ∨ x ≠ .z by cases x <;> decide⟩
instance txUORA : UORA TX where
  unit := .e
  unit_valid := show TX.e ≠ .z by decide
  unit_left_id := rfl
  pcore_unit := rfl

end W4c0

section
open Iris Iris.OFE W4c0

-- `Iris.both_dfrac_validI_ord` idx 4: necessary (SiProp, A = NA (equality order, not IncOrd): ●a • ◯e valid, e ≼ₒ a fails)
theorem w4c0_130 : ¬ drop0% Iris.both_dfrac_validI_ord 4 := fun h => by
  have := ((@h SP NA _ _ (.own 1) .a .e).1 0
    (Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨.a, rfl⟩, trivial⟩)).2.1
  cases this

-- `Iris.auth_both_validI_ord` idx 4: necessary (SiProp, A = NA (equality order, not IncOrd): ●a • ◯e valid, e ≼ₒ a fails)
theorem w4c0_131 : ¬ drop0% Iris.auth_both_validI_ord 4 := fun h => by
  have := ((@h SP NA _ _ .a .e).1 0 (Auth.both_validN_frame.mpr ⟨⟨.a, rfl⟩, trivial⟩)).1
  cases this

-- `Iris.both_dfrac_validI` idx 4: necessary (SiProp, A = TX (a ≤ e, a not included in e): ●e • ◯a valid, a ≼ e fails)
theorem w4c0_132 : ¬ drop0% Iris.both_dfrac_validI 4 := fun h => by
  obtain ⟨w, hw⟩ := SiProp.exists_holds.1 ((@h SP TX _ _ (.own 1) .e .a).1 0
    (Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨.e, Or.inr (by intro h; cases h)⟩, by intro h; cases h⟩)).2.1
  cases w <;> cases hw

-- `Iris.auth_both_validI` idx 4: necessary (SiProp, A = TX (a ≤ e, a not included in e): ●e • ◯a valid, a ≼ e fails)
theorem w4c0_133 : ¬ drop0% Iris.auth_both_validI 4 := fun h => by
  obtain ⟨w, hw⟩ := SiProp.exists_holds.1 ((@h SP TX _ _ .e .a).1 0
    (Auth.both_validN_frame.mpr ⟨⟨.e, Or.inr (by intro h; cases h)⟩, by intro h; cases h⟩)).1
  cases w <;> cases hw
end

namespace W4c0
open Iris Iris.OFE Iris.ORA

/-- Bool, xor, no core, all valid, order is equality (W2c3 BE): OrderRefl, not IncOrd. -/
structure BE where b : Bool
instance : OFE BE := OFE.ofDiscrete BE
instance : OFE.Discrete BE := ⟨fun h => h⟩
@[instance_reducible] def beData : DiscreteORAData BE where
  pcore _ := none
  op x y := ⟨xor x.b y.b⟩
  Valid _ := True
  Order x y := x = y
  assoc x y z := congrArg BE.mk (Bool.xor_assoc x.b y.b z.b).symm
  comm x y := congrArg BE.mk (Bool.xor_comm x.b y.b)
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ h := h ▸ rfl
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed x y hx h z := h ▸ hx z
instance beORA : ORA BE := ORA.ofDiscreteORAData beData
instance beRefl : OrderRefl BE := ⟨fun _ => rfl⟩

/-- Bool, or, no core, all valid, full order (W2c3 BT): OrderRefl and IncOrd, not OrdInc. -/
structure BT where b : Bool
instance : OFE BT := OFE.ofDiscrete BT
instance : OFE.Discrete BT := ⟨fun h => h⟩
@[instance_reducible] def btData : DiscreteORAData BT where
  pcore _ := none
  op x y := ⟨or x.b y.b⟩
  Valid _ := True
  Order _ _ := True
  assoc x y z := congrArg BT.mk (Bool.or_assoc x.b y.b z.b).symm
  comm x y := congrArg BT.mk (Bool.or_comm x.b y.b)
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ _ _ := trivial
  op_mono_left _ _ _ _ := trivial
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ _ _ := trivial
instance btORA : ORA BT := ORA.ofDiscreteORAData btData
instance btRefl : OrderRefl BT := ⟨fun _ => trivial⟩
instance btIncOrd : IncOrd BT := ⟨fun _ => trivial⟩

theorem q_sum : (Qp.quarter + Qp.threeQuarters : Qp) = 1 := Qp.quarter_add_threeQuarters
theorem qne : ¬ (1 : Qp) ≼{0} 1 := fun ⟨z, hz⟩ => by
  have := z.2; simp at hz; grind
theorem dq_inc (n : Nat) : DFrac.own Qp.quarter ≼{n} DFrac.own 1 :=
  ⟨DFrac.own Qp.threeQuarters, congrArg DFrac.own q_sum.symm⟩
theorem sg_get {V : Type} (x : V) : Iris.Std.get? (sg 0 x) 0 = some x := Iris.Std.LawfulPartialMap.get?_insert_eq rfl

theorem bt_v (n : Nat) : ✓{n} (HeapView.Auth (DFrac.own 1) (sg 0 (⟨false⟩ : BT)) • HeapView.Frag 0 (DFrac.own Qp.quarter) (⟨true⟩ : BT) : HeapView Nat BT TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨⟨false⟩, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, trivial⟩, none, .inr ⟨dq_inc n, trivial⟩⟩
theorem be_v (n : Nat) : ✓{n} (HeapView.Auth (DFrac.own 1) (sg 0 (⟨false⟩ : BE)) • HeapView.Frag 0 (DFrac.own Qp.quarter) (⟨true⟩ : BE) : HeapView Nat BE TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨⟨false⟩, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, trivial⟩,
    some (DFrac.own Qp.threeQuarters, ⟨true⟩), .inl ⟨congrArg DFrac.own q_sum, rfl⟩⟩
theorem qp_v (n : Nat) : ✓{n} (HeapView.Auth (DFrac.own 1) (sg 0 1) • HeapView.Frag 0 (DFrac.own 1) 1 : HeapView Nat Qp TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨1, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, Qp.valid_one⟩, none, .inl .rfl⟩

end W4c0

section
open Iris Iris.OFE W4c0

-- `Iris.auth_op_frag_validI_ord` idx 7: necessary (SiProp, V = BA (not IncOrd), heap all false, dq = discard, v = true: valid via frame (discard, false), order fails)
theorem w4c0_140 : ¬ drop0% Iris.auth_op_frag_validI_ord 7 := fun h => by
  have lhs := (HeapView.auth_op_frag_validN_iff_frame (H := fun V => Nat → Option V) (K := Nat) (V := BA) (n := 0)
    (dp := .discard) (m1 := fun _ => some ⟨false⟩) (k := 0) (dq := .discard) (v := ⟨true⟩)).mpr
    ⟨⟨false⟩, .discard, trivial, rfl, ⟨trivial, trivial⟩, some (.discard, ⟨false⟩), .inl (OFE.Dist.of_eq rfl)⟩
  obtain ⟨v', H1⟩ := SiProp.exists_holds.1
    ((@h Nat BA (fun V => Nat → Option V) _ _ SP _ .discard (fun _ => some ⟨false⟩) 0 .discard ⟨true⟩).1 0 lhs)
  obtain ⟨dq', -, hget, -, hord⟩ := SiProp.exists_holds.1 H1
  cases hget
  rcases hord with hd | ho
  · have := congrArg (fun p => p.2.b) (OFE.Discrete.discrete_0 hd)
    cases this
  · cases ho.2

-- `Iris.auth_op_frag_validI` idx 7: necessary (SiProp, V = BT (full order, not OrdInc): Auth {0 ↦ false} • Frag 0 (1/4) true valid, no inclusion witness)
theorem w4c0_141 : ¬ drop0% Iris.auth_op_frag_validI 7 := fun h => by
  obtain ⟨v, H1⟩ := SiProp.exists_holds.1
    ((@h Nat BT TM _ _ SP _ (DFrac.own 1) (sg 0 ⟨false⟩) 0 (DFrac.own Qp.quarter) ⟨true⟩).1 0 (bt_v 0))
  obtain ⟨dq, -, hm, -, hz⟩ := SiProp.exists_holds.1 H1
  obtain ⟨z, hz⟩ := SiProp.exists_holds.1 hz
  rw [sg_get] at hm; cases hm
  rcases z with _ | ⟨z⟩ <;> cases hz.2

-- `Iris.auth_op_frag_validI_total_ord` idx 7: necessary (SiProp, V = Qp (IncOrd, not OrderRefl): {0 ↦ 1}, Frag 0 (own 1) 1 valid; 1 not below 1)
theorem w4c0_142 : ¬ drop0% Iris.auth_op_frag_validI_total_ord 7 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := SiProp.exists_holds.1
    ((@h Nat Qp TM _ _ SP _ _ (DFrac.own 1) (sg 0 1) 0 (DFrac.own 1) 1) 0 (qp_v 0))
  rw [sg_get] at hm; cases hm; exact qne hz

-- `Iris.auth_op_frag_validI_total_ord` idx 8: necessary (SiProp, V = BE (xor, order =, OrderRefl, not IncOrd): valid via frame (3/4, true); true not below false)
theorem w4c0_143 : ¬ drop0% Iris.auth_op_frag_validI_total_ord 8 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := SiProp.exists_holds.1
    ((@h Nat BE TM _ _ SP _ _ (DFrac.own 1) (sg 0 ⟨false⟩) 0 (DFrac.own Qp.quarter) ⟨true⟩) 0 (be_v 0))
  rw [sg_get] at hm; cases hm; cases hz

-- `Iris.auth_op_frag_validI_total` idx 7: necessary (SiProp, V = Qp (OrdInc, not OrderRefl): 1 not included in 1)
theorem w4c0_144 : ¬ drop0% Iris.auth_op_frag_validI_total 7 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := SiProp.exists_holds.1
    ((@h Nat Qp TM _ _ SP _ _ (DFrac.own 1) (sg 0 1) 0 (DFrac.own 1) 1) 0 (qp_v 0))
  rw [sg_get] at hm; cases hm
  obtain ⟨z, hz⟩ := SiProp.exists_holds.1 hz
  exact qne ⟨z, hz⟩

-- `Iris.auth_op_frag_validI_total` idx 8: necessary (SiProp, V = BT (OrderRefl, not OrdInc): true not included in false)
theorem w4c0_145 : ¬ drop0% Iris.auth_op_frag_validI_total 8 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := SiProp.exists_holds.1
    ((@h Nat BT TM _ _ SP _ _ (DFrac.own 1) (sg 0 ⟨false⟩) 0 (DFrac.own Qp.quarter) ⟨true⟩) 0 (bt_v 0))
  rw [sg_get] at hm; cases hm
  obtain ⟨z, hz⟩ := SiProp.exists_holds.1 hz
  cases hz
end

namespace W4c0
open Iris Iris.OFE

/-- Leibniz (discrete) OFE on booleans. -/
structure LB where b : Bool
instance : OFE LB := OFE.ofDiscrete LB

/-- View relation over LB and Unit: R n a _ iff a = true (a lawful IsViewRel). -/
def lbR : ViewRel LB Unit := fun _ a _ => a.b = true
instance lbRel : IsViewRel lbR where
  mono h e _ _ := (show _ = _ from e) ▸ h
  op_left h := h
  rel_validN _ _ _ _ := trivial
  rel_unit _ := ⟨⟨true⟩, rfl⟩

/-- The empty relation over Unit has no unit witness: not a view relation. -/
def eR : ViewRel Unit Unit := fun _ _ _ => False
theorem eR_bad : ¬ IsViewRel eR := fun h => match h.rel_unit 0 with | ⟨_, hf⟩ => hf

end W4c0

section
open Iris Iris.OFE W4c0

-- `Iris.view_both_dfrac_validI_1` idx 7: necessary (dependent; A = B = Unit, R = empty relation (no unit), relI = anything)
theorem w4c0_150 : ¬ indep0% Iris.view_both_dfrac_validI_1 7 := fun H =>
  eR_bad (@H SP Unit Unit _ _ _ eR iprop(False) (DFrac.own 1) () () (fun _ hf => hf.elim))

-- `Iris.view_both_dfrac_validI_1` idx 12: necessary (SiProp, R n a _ = (a = true) over LB, Unit; a = true, relI = False)
theorem w4c0_151 : ¬ drop0% Iris.view_both_dfrac_validI_1 12 := fun h =>
  ((@h SP LB Unit _ _ _ lbR lbRel iprop(False) (DFrac.own 1) ⟨true⟩ ()) 0
    (View.auth_op_frag_validN_iff.2 ⟨DFrac.valid_own_one, rfl⟩)).2

-- `Iris.view_both_dfrac_validI_2` idx 7: necessary (dependent; A = B = Unit, R = empty relation (no unit), relI = False)
theorem w4c0_152 : ¬ indep0% Iris.view_both_dfrac_validI_2 7 := fun H =>
  eR_bad (@H SP Unit Unit _ _ _ eR iprop(False) (DFrac.own 1) () () (fun _ hf => hf))

-- `Iris.view_both_dfrac_validI_2` idx 12: necessary (SiProp, R n a _ = (a = true) over LB, Unit; a = false, relI = True)
theorem w4c0_153 : ¬ drop0% Iris.view_both_dfrac_validI_2 12 := fun h =>
  Bool.false_ne_true (View.auth_op_frag_validN_iff.1
    ((@h SP LB Unit _ _ _ lbR lbRel iprop(True) (DFrac.own 1) ⟨false⟩ ()) 0 ⟨DFrac.valid_own_one, trivial⟩)).2

-- `Iris.view_both_dfrac_validI` idx 7: necessary (dependent; A = B = Unit, R = empty relation (no unit), relI = False)
theorem w4c0_154 : ¬ indep0% Iris.view_both_dfrac_validI 7 := fun H =>
  eR_bad (@H SP Unit Unit _ _ _ eR iprop(False) (DFrac.own 1) () () (fun _ => Iff.rfl))

-- `Iris.view_both_dfrac_validI` idx 12: necessary (SiProp, R n a _ = (a = true) over LB, Unit; a = true, relI = False)
theorem w4c0_155 : ¬ drop0% Iris.view_both_dfrac_validI 12 := fun h =>
  ((@h SP LB Unit _ _ _ lbR lbRel iprop(False) (DFrac.own 1) ⟨true⟩ ()).1 0
    (View.auth_op_frag_validN_iff.2 ⟨DFrac.valid_own_one, rfl⟩)).2

-- `Iris.view_both_validI_1` idx 11: necessary (SiProp, R n a _ = (a = true) over LB, Unit; a = true, relI = False)
theorem w4c0_156 : ¬ drop0% Iris.view_both_validI_1 11 := fun h =>
  (@h SP LB Unit _ _ _ lbR lbRel iprop(False) ⟨true⟩ ()) 0 (View.auth_one_op_frag_validN_iff.2 rfl)

-- `Iris.view_both_validI_2` idx 7: necessary (dependent; A = B = Unit, R = empty relation (no unit), relI = False)
theorem w4c0_157 : ¬ indep0% Iris.view_both_validI_2 7 := fun H =>
  eR_bad (@H SP Unit Unit _ _ _ eR iprop(False) () () (fun _ hf => hf))

-- `Iris.view_both_validI_2` idx 11: necessary (SiProp, R n a _ = (a = true) over LB, Unit; a = false, relI = True)
theorem w4c0_158 : ¬ drop0% Iris.view_both_validI_2 11 := fun h =>
  Bool.false_ne_true (View.auth_one_op_frag_validN_iff.1
    ((@h SP LB Unit _ _ _ lbR lbRel iprop(True) ⟨false⟩ ()) 0 trivial))

-- `Iris.view_both_validI` idx 7: necessary (dependent; A = B = Unit, R = empty relation (no unit), relI = False)
theorem w4c0_159 : ¬ indep0% Iris.view_both_validI 7 := fun H =>
  eR_bad (@H SP Unit Unit _ _ _ eR iprop(False) () () (fun _ => Iff.rfl))

-- `Iris.view_both_validI` idx 11: necessary (SiProp, R n a _ = (a = true) over LB, Unit; a = true, relI = False)
theorem w4c0_160 : ¬ drop0% Iris.view_both_validI 11 := fun h =>
  (@h SP LB Unit _ _ _ lbR lbRel iprop(False) ⟨true⟩ ()).1 0 (View.auth_one_op_frag_validN_iff.2 rfl)

-- `Iris.view_auth_dfrac_validI` idx 7: necessary (dependent; A = B = Unit, R = empty relation (no unit), relI = False)
theorem w4c0_161 : ¬ indep0% Iris.view_auth_dfrac_validI 7 := fun H =>
  eR_bad (@H SP Unit Unit _ _ _ eR iprop(False) (DFrac.own 1) () (fun _ => Iff.rfl))

-- `Iris.view_auth_dfrac_validI` idx 11: necessary (SiProp, R n a _ = (a = true) over LB, Unit; a = true, relI = False)
theorem w4c0_162 : ¬ drop0% Iris.view_auth_dfrac_validI 11 := fun h =>
  ((@h SP LB Unit _ _ _ lbR lbRel iprop(False) (DFrac.own 1) ⟨true⟩).1 0
    (View.auth_validN_iff.2 ⟨DFrac.valid_own_one, rfl⟩)).2

-- `Iris.view_auth_validI` idx 7: necessary (dependent; A = B = Unit, R = empty relation (no unit), relI = False)
theorem w4c0_163 : ¬ indep0% Iris.view_auth_validI 7 := fun H =>
  eR_bad (@H SP Unit Unit _ _ _ eR iprop(False) () (fun _ => Iff.rfl))

-- `Iris.view_auth_validI` idx 10: necessary (SiProp, R n a _ = (a = true) over LB, Unit; a = true, relI = False)
theorem w4c0_164 : ¬ drop0% Iris.view_auth_validI 10 := fun h =>
  (@h SP LB Unit _ _ _ lbR lbRel iprop(False) ⟨true⟩).1 0 ((View.auth_one_validN_iff 0 _).2 rfl)

-- `Iris.view_frag_validI` idx 7: necessary (dependent; A = B = Unit, R = empty relation (no unit), relI = False)
theorem w4c0_165 : ¬ indep0% Iris.view_frag_validI 7 := fun H =>
  eR_bad (@H SP Unit Unit _ _ _ eR iprop(False) () (fun _ => ⟨False.elim, fun ⟨_, hf⟩ => hf⟩))

-- `Iris.view_frag_validI` idx 10: necessary (SiProp, R n a _ = (a = true) over LB, Unit; b = (), relI = False)
theorem w4c0_166 : ¬ drop0% Iris.view_frag_validI 10 := fun h =>
  (@h SP LB Unit _ _ _ lbR lbRel iprop(False) ()).1 0 (View.frag_validN_iff.2 ⟨⟨true⟩, rfl⟩)
end

namespace W4c0
open Iris Iris.BI

/-- Separation logic over the group (Bool, xor) with unit false: P ∗ Q = {x xor y}, emp = {false},
persistently P := ⌜emp ⊢ P⌝, later = id. Not positive: true ∗ true ∋ false. -/
structure ZP where p : Bool → Prop

theorem ZP.ext' {P Q : ZP} (h : ∀ w, P.p w ↔ Q.p w) : P = Q := by
  cases P; cases Q; congr; funext w; exact propext (h w)

instance : COFE ZP := COFE.ofDiscrete _

instance zpBase : BIBase ZP where
  Entails P Q := ∀ w, P.p w → Q.p w
  emp := ⟨fun w => w = false⟩
  pure φ := ⟨fun _ => φ⟩
  and P Q := ⟨fun w => P.p w ∧ Q.p w⟩
  or P Q := ⟨fun w => P.p w ∨ Q.p w⟩
  imp P Q := ⟨fun w => P.p w → Q.p w⟩
  sForall Ψ := ⟨fun w => ∀ p, Ψ p → p.p w⟩
  sExists Ψ := ⟨fun w => ∃ p, Ψ p ∧ p.p w⟩
  sep P Q := ⟨fun w => ∃ x y, w = xor x y ∧ P.p x ∧ Q.p y⟩
  wand P Q := ⟨fun w => ∀ y, P.p y → Q.p (xor w y)⟩
  persistently P := ⟨fun _ => ∀ w, w = false → P.p w⟩
  later P := P

instance zpBI : BI ZP := BI.ofPersistentlyDiscrete
  (entails_refl := fun _ h => h)
  (entails_trans := fun h1 h2 w h => h2 w (h1 w h))
  (equiv_iff := fun {P Q} => ⟨fun e => e ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h1, h2⟩ => ZP.ext' fun w => ⟨h1 w, h2 w⟩⟩)
  (pure_intro := fun h _ _ => h)
  (pure_elim' := fun h w hφ => h hφ w trivial)
  (and_elim_l := fun _ h => h.1)
  (and_elim_r := fun _ h => h.2)
  (and_intro := fun h1 h2 w h => ⟨h1 w h, h2 w h⟩)
  (or_intro_l := fun _ h => .inl h)
  (or_intro_r := fun _ h => .inr h)
  (or_elim := fun h1 h2 w h => h.elim (h1 w) (h2 w))
  (imp_intro := fun h w hP hQ => h w ⟨hP, hQ⟩)
  (imp_elim := fun h w hPQ => h w hPQ.1 hPQ.2)
  (sForall_intro := fun h w hP p hp => h p hp w hP)
  (sForall_elim := fun hp _ h => h _ hp)
  (sExists_intro := fun hp _ h => ⟨_, hp, h⟩)
  (sExists_elim := fun h w ⟨p, hp, hpw⟩ => h p hp w hpw)
  (sep_mono := fun h1 h2 _ ⟨x, y, e, hx, hy⟩ => ⟨x, y, e, h1 x hx, h2 y hy⟩)
  (emp_sep := ⟨fun w ⟨x, y, e, hx, hy⟩ => by
      have hx' : x = false := hx
      subst hx'; rw [Bool.false_xor] at e; exact e ▸ hy,
    fun w h => ⟨false, w, (Bool.false_xor w).symm, rfl, h⟩⟩)
  (sep_symm := fun _ ⟨x, y, e, hx, hy⟩ => ⟨y, x, e.trans (Bool.xor_comm x y), hy, hx⟩)
  (sep_assoc_l := fun _ ⟨u, z, e, ⟨x, y, eu, hx, hy⟩, hz⟩ =>
    ⟨x, xor y z, by rw [e, eu, Bool.xor_assoc], hx, ⟨y, z, rfl, hy, hz⟩⟩)
  (wand_intro := fun h w hP y hQ => h _ ⟨w, y, rfl, hP, hQ⟩)
  (wand_elim := fun h _ ⟨x, y, e, hx, hy⟩ => e ▸ h x hx y hy)
  (later_mono := fun h => h)
  (later_intro := fun _ h => h)
  (later_sForall_2 := fun _ h p hp => h _ ⟨p, rfl⟩ hp)
  (later_sExists_false := fun _ ⟨p, hp, hpw⟩ => .inr ⟨_, ⟨p, rfl⟩, hp, hpw⟩)
  (later_sep := ⟨fun _ h => h, fun _ h => h⟩)
  (later_persistently := ⟨fun _ h => h, fun _ h => h⟩)
  (later_false_em := fun _ h => .inr (fun _ => h))
  (discrete := fun h => h)
  (persistently_eq := fun _ => rfl)

/-- The singleton {true}. -/
def zT : ZP := ⟨fun w => w = true⟩

/-- persistently (zT ∗ zT) holds (false = true xor true), persistently zT does not. -/
theorem zp_pers_sep : ¬ ((iprop(<pers> (zT ∗ zT)) : ZP) ⊢ iprop(<pers> zT ∗ <pers> zT)) := fun h =>
  match h false (fun w hw => ⟨true, true, hw, rfl, rfl⟩) with
  | ⟨_, _, _, hx, _⟩ => Bool.false_ne_true (hx false rfl)

end W4c0

section
open Iris Iris.BI W4c0

-- `Iris.BI.bi_persistently_sep_weak_homomorphism` idx 2: necessary (discrete BI ZP over the group (Bool, xor): not positive; persistently ({true} ∗ {true}) holds, persistently {true} does not)
theorem w4c0_180 : ¬ drop0% Iris.BI.bi_persistently_sep_weak_homomorphism 2 := fun h =>
  zp_pers_sep (BI.BIBase.BiEntails.of_eq ((@h ZP zpBI).map_op (x := zT) (y := zT))).1
end

namespace W4c0
open Iris Iris.OFE

/-- Truncation OFE on naturals (W1c3 TI): op x y = x + y + 1, never valid, empty order, no core. 1 ≡{0} 2. -/
structure TI where v : Nat
instance : OFE TI where
  Dist n x y := min x.v (n+1) = min y.v (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b)
      simp only [TI.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show min x.v (m+1) = min y.v (m+1); omega
instance : Op TI where
  op x y := ⟨x.v + y.v + 1⟩
  op_ne := ⟨fun n y z h => by     have h' : min y.v (n+1) = min z.v (n+1) := h; show min _ (n+1) = min _ (n+1); simp only; omega⟩
  assoc {x y z} := congrArg TI.mk (show x.v + (y.v + z.v + 1) + 1 = (x.v + y.v + 1) + z.v + 1 by omega)
  comm {x y} := congrArg TI.mk (show x.v + y.v + 1 = y.v + x.v + 1 by omega)
instance : PCore TI where
  pcore _ := none
  pcore_ne _ h := (by cases h)
  pcore_idem h := (by cases h)
instance : Valid TI where
  ValidN _ _ := False
  Valid _ := False
  validN_ne _ h := h
  valid_iff_validN := ⟨False.elim, fun h => h 0⟩
  validN_succ h := h
instance : Ordered TI where
  OrderN _ _ _ := False
  Order _ _ := False
  ordN_ne _ _ h := h
  ordN_succ h := h
  ordN_trans h _ := h
  ord_trans h _ := h
  ordN_of_ord _ h := h
instance tiORA : ORA TI where
  validN_op_left h := h
  pcore_op_left h := (by cases h)
  extend h _ := h.elim
  op_monoN_left_ord _ h := h
  op_mono_left_ord _ h := h
  validN_of_ordN h _ := h.elim
  pcore_monoN_ord _ h := (by cases h)
  pcore_mono_ord _ h := (by cases h)
  pcore_order_op h := (by cases h)
  pcore_increasing h := (by cases h)
  increasing_closed hx _ := ⟨fun y => (hx.increasing y).elim⟩
  ordN_extend _ h := h.elim

/-- Halving on TI: f (1 • c) = f 1 • f c for all c, but not non-expansive (1 ≡{0} 2, f 1 = 0, f 2 = 1). -/
def halfTI (x : TI) : TI := ⟨x.v / 2⟩

end W4c0

section
open Iris Iris.OFE W4c0

-- `Iris.f_homom_includedI` idx 9: necessary (SiProp at step 0, A = B = TI (truncation Nat, x • y = x+y+1), f = halving, x = y = 1: 1 ≼{0} 1 (1 ≡{0} 2 = 1 • 0), but f 1 = 0 ⋠{0} 0)
theorem w4c0_190 : ¬ drop0% Iris.f_homom_includedI 9 := fun h =>
  match SiProp.exists_holds.1 ((@h SP _ TI TI _ _ ⟨1⟩ ⟨1⟩ halfTI
      (fun c n => show min (1 / 2 + c.v / 2 + 1) (n+1) = min ((1 + c.v + 1) / 2) (n+1) by omega)) 0
    (SiProp.exists_holds.2 ⟨⟨0⟩, (show min 1 (0+1) = min (1 + 0 + 1) (0+1) by decide)⟩)) with
  | ⟨c, hc⟩ => absurd (show min (1 / 2) (0+1) = min (1 / 2 + c.v + 1) (0+1) from hc) (by omega)
end

namespace W4c0
open Iris Iris.OFE Iris.Algebra

/-- Discrete OFE on Nat (Dist = Eq). -/
instance natOFE : OFE Nat := OFE.ofDiscrete Nat

theorem natNE2 (f : Nat → Nat → Nat) : OFE.NonExpansive₂ f :=
  ⟨fun n x₁ x₂ h y₁ y₂ h' => by
    change x₁ = x₂ at h; change y₁ = y₂ at h'; subst h h'; exact OFE.Dist.of_eq rfl⟩
theorem natNE (f : Nat → Nat) : OFE.NonExpansive f :=
  ⟨fun n x₁ x₂ h => by change x₁ = x₂ at h; subst h; exact OFE.Dist.of_eq rfl⟩

/-- Addition on Nat, as a named operation. -/
def ad (a b : Nat) : Nat := a + b

/-- (Nat, +, 0) as a commutative monoid. -/
instance addMon : MonoidOps ad 0 where
  op_ne := natNE2 _
  op_assoc := Nat.add_assoc _ _ _
  op_comm := Nat.add_comm _ _
  op_left_id := Nat.zero_add _

/-- (Nat, max, 0) as a commutative monoid. -/
instance maxMon : MonoidOps (M := Nat) max 0 where
  op_ne := natNE2 _
  op_assoc := Nat.max_assoc _ _ _
  op_comm := Nat.max_comm _ _
  op_left_id := Nat.zero_max _

/-- Left projection (not commutative). -/
def lp (a _ : Nat) : Nat := a

/-- The left projection is not a commutative monoid operation. -/
theorem badMon : ¬ MonoidOps lp 0 := fun h =>
  absurd (@MonoidOps.op_comm _ _ _ _ h 0 1) (by decide)

/-- Truncation OFE on naturals: dist n x y iff min x (n+1) = min y (n+1). Not discrete (1 and 2 agree at 0). -/
structure TN where v : Nat
instance tnOFE : OFE TN where
  Dist n x y := min x.v (n+1) = min y.v (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b)
      simp only [TN.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show min x.v (m+1) = min y.v (m+1); omega

/-- max on the truncation OFE, unit 0: a non-expansive commutative monoid. -/
def maxTN (a b : TN) : TN := ⟨max a.v b.v⟩
instance tnMax : MonoidOps maxTN ⟨0⟩ where
  op_ne := ⟨fun n x₁ x₂ h y₁ y₂ h' => by
    have a : min x₁.v (n+1) = min x₂.v (n+1) := h
    have b : min y₁.v (n+1) = min y₂.v (n+1) := h'
    show min (max x₁.v y₁.v) (n+1) = min (max x₂.v y₂.v) (n+1); omega⟩
  op_assoc := by intro a b c; simp [maxTN, Nat.max_assoc]
  op_comm := by intro a b; simp [maxTN, Nat.max_comm]
  op_left_id := by intro a; simp [maxTN]

/-- Predecessor on TN: preserves max and 0, not non-expansive (1 ≡{0} 2, but 0 and 1 differ at 0). -/
def predTN (a : TN) : TN := ⟨a.v - 1⟩
theorem predTN_max {x y : TN} : predTN (maxTN x y) = maxTN (predTN x) (predTN y) := by
  simp only [predTN, maxTN, TN.mk.injEq]; omega
theorem predTN_not_ne : ¬ NonExpansive predTN := fun h =>
  absurd (h.ne (n := 0) (x₁ := ⟨1⟩) (x₂ := ⟨2⟩) rfl) (by
    show ¬ (min (1 - 1) (0+1) = min (2 - 1) (0+1)); decide)

/-- 0 ↦ 0, otherwise 1: preserves 0, not additive. -/
def sgn (a : Nat) : Nat := if a = 0 then 0 else 1

end W4c0

section
open Iris Iris.OFE Iris.Algebra W4c0

-- `Iris.BI.MonoidHomomorphism.ofEq` idx 6: necessary (dependent; PROP = discrete Nat, op1 = left projection (not commutative), op2 = + , f = 0)
theorem w4c0_100 : ¬ indep0% Iris.BI.MonoidHomomorphism.ofEq 6 := fun H =>
  badMon (@H Nat natOFE lp ad 0 0 addMon (fun _ => 0) (natNE _) rfl rfl)

-- `Iris.BI.MonoidHomomorphism.ofEq` idx 7: necessary (dependent; PROP = discrete Nat, op1 = +, op2 = left projection (not commutative), f = 0)
theorem w4c0_101 : ¬ indep0% Iris.BI.MonoidHomomorphism.ofEq 7 := fun H =>
  badMon (@H Nat natOFE ad lp 0 0 addMon (fun _ => 0) (natNE _) rfl rfl)

-- `Iris.BI.MonoidHomomorphism.ofEq` idx 9: necessary (truncation OFE TN, op = max, f = predecessor: homomorphism, not non-expansive)
theorem w4c0_102 : ¬ drop0% Iris.BI.MonoidHomomorphism.ofEq 9 := fun h =>
  predTN_not_ne (@h TN _ maxTN maxTN ⟨0⟩ ⟨0⟩ tnMax tnMax predTN predTN_max rfl).map_ne

-- `Iris.BI.MonoidHomomorphism.ofEq` idx 10: necessary (discrete Nat, op = +, f = 0 ↦ 0 else 1: f (1 + 1) ≠ f 1 + f 1)
theorem w4c0_103 : ¬ drop0% Iris.BI.MonoidHomomorphism.ofEq 10 := fun h =>
  absurd ((@h Nat natOFE ad ad 0 0 addMon addMon sgn (natNE _) rfl).map_op (x := 1) (y := 1)) (by decide)

-- `Iris.BI.MonoidHomomorphism.ofEq` idx 11: necessary (discrete Nat, op1 = +, op2 = max, f = constant 1: f 0 ≠ 0)
theorem w4c0_104 : ¬ drop0% Iris.BI.MonoidHomomorphism.ofEq 11 := fun h =>
  absurd (@h Nat natOFE ad max 0 0 addMon maxMon (fun _ => 1) (natNE _) rfl).map_unit (by decide)

-- `Iris.BI.WeakMonoidHomomorphism.ofEq` idx 6: necessary (dependent; PROP = discrete Nat, op1 = left projection (not commutative), op2 = +, f = 0)
theorem w4c0_105 : ¬ indep0% Iris.BI.WeakMonoidHomomorphism.ofEq 6 := fun H =>
  badMon (@H Nat natOFE lp ad 0 0 addMon (fun _ => 0) (natNE _) rfl)

-- `Iris.BI.WeakMonoidHomomorphism.ofEq` idx 7: necessary (dependent; PROP = discrete Nat, op1 = +, op2 = left projection (not commutative), f = 0)
theorem w4c0_106 : ¬ indep0% Iris.BI.WeakMonoidHomomorphism.ofEq 7 := fun H =>
  badMon (@H Nat natOFE ad lp 0 0 addMon (fun _ => 0) (natNE _) rfl)

-- `Iris.BI.WeakMonoidHomomorphism.ofEq` idx 9: necessary (truncation OFE TN, op = max, f = predecessor: homomorphism, not non-expansive)
theorem w4c0_107 : ¬ drop0% Iris.BI.WeakMonoidHomomorphism.ofEq 9 := fun h =>
  predTN_not_ne (@h TN _ maxTN maxTN ⟨0⟩ ⟨0⟩ tnMax tnMax predTN predTN_max).map_ne

-- `Iris.BI.WeakMonoidHomomorphism.ofEq` idx 10: necessary (discrete Nat, op = +, f = 0 ↦ 0 else 1: f (1 + 1) ≠ f 1 + f 1)
theorem w4c0_108 : ¬ drop0% Iris.BI.WeakMonoidHomomorphism.ofEq 10 := fun h =>
  absurd ((@h Nat natOFE ad ad 0 0 addMon addMon sgn (natNE _)).map_op (x := 1) (y := 1)) (by decide)
end
