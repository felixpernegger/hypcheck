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

namespace Probe2

-- helper
open Iris Iris.BI Iris.Std Iris.Instances.Classical Iris.Instances.Data

-- helper
/-- step-indexed prop true only at step 0 (not timeless) -/
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩

-- helper
/-- heap owning cell 0 only -/
def h0 : State Unit := fun i => if i = 0 then result () else unknown

-- helper
theorem h0_ne : h0 ≠ ∅ := fun h => by
  have := congrFun h 0; simp [h0, EmptyCollection.emptyCollection] at this

-- helper
/-- heap prop: owns cell 0 -/
def own0 : HeapProp Unit := fun σ => σ 0 ≠ unknown

-- `Iris.BI.sep_mono_left` idx 5: necessary (SiProp: P=True, P'=False, Q=True; True*True |- False*True fails)
theorem p2_1 : ¬ drop0% Iris.BI.sep_mono_left 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(True) 0 ⟨trivial, trivial⟩).1

-- `Iris.BI.sep_mono_right` idx 5: necessary (SiProp: P=True, Q=True, Q'=False)
theorem p2_2 : ¬ drop0% Iris.BI.sep_mono_right 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False) 0 ⟨trivial, trivial⟩).2

-- `Iris.BI.BIBase.BiEntails.mp` idx 4: necessary (SiProp: P=True, Q=False)
theorem p2_3 : ¬ drop0% Iris.BI.BIBase.BiEntails.mp 4 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) 0 trivial)

-- `Iris.BI.or_congr_right` idx 5: necessary (SiProp: P=False, Q=True, Q'=False)
theorem p2_4 : ¬ drop0% Iris.BI.or_congr_right 5 := fun h => by
  have := (@h SiProp _ iprop(False) iprop(True) iprop(False)).mp 0 (Or.inr trivial)
  exact this.elim id id

-- `Iris.BI.sep_elim_emp_valid_right` idx 6: necessary (SiProp: P=True, R=True, Q=False)
theorem p2_5 : ¬ drop0% Iris.BI.sep_elim_emp_valid_right 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(True) (fun _ _ => trivial) 0 trivial)

-- `Iris.BI.imp_entails` idx 5: necessary (SiProp (affine): P=True, Q=False)
theorem p2_6 : ¬ drop0% Iris.BI.imp_entails 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) _ 0 trivial)

-- `Iris.BI.affinely_intro_of_affinely` idx 4: necessary (SiProp: P=True, Q=False)
theorem p2_7 : ¬ drop0% Iris.BI.affinely_intro_of_affinely 4 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) 0 ⟨trivial, trivial⟩).2

-- `Iris.BI.imp_mp` idx 6: necessary (SiProp: P=True, Q=False, R=False (P |- Q -> R holds))
theorem p2_8 : ¬ drop0% Iris.BI.imp_mp 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) (imp_intro (and_elim_r.trans false_elim)) 0 trivial)

-- `Iris.BI.affine_mono` idx 4: necessary (HeapProp Unit (non-affine): P=True, Q=emp; True not affine at heap {0})
theorem p2_9 : ¬ drop0% Iris.BI.affine_mono 4 := fun h =>
  h0_ne ((@h (HeapProp Unit) _ iprop(True) iprop(emp) emp_affine).affine h0 trivial)

-- `Iris.BI.sep_affine` idx 5: necessary (HeapProp Unit: P=emp, Q=True; emp*True not affine)
theorem p2_10 : ¬ drop0% Iris.BI.sep_affine 5 := fun h =>
  h0_ne ((@h (HeapProp Unit) _ iprop(emp) iprop(True) _).affine h0
    ⟨∅, h0, empty_union, empty_disjoint, rfl, trivial⟩)

-- `Iris.BI.affine_affinely` idx 3: necessary (HeapProp Unit: P=True; <affine> True = emp)
theorem p2_11 : ¬ drop0% Iris.BI.affine_affinely 3 := fun h =>
  h0_ne ((@h (HeapProp Unit) _ iprop(True)).mpr h0 trivial).1

-- `Iris.BI.persistent_and_affinely_sep_right_mp` idx 4: necessary (HeapProp Unit: P=True, Q=owns cell 0; P/\Q holds at {0}, P*<affine>Q does not)
theorem p2_12 : ¬ drop0% Iris.BI.persistent_and_affinely_sep_right_mp 4 := fun h => by
  obtain ⟨σ1, σ2, -, -, -, he, hq⟩ := @h (HeapProp Unit) _ iprop(True) own0 h0 ⟨trivial, by simp [own0, h0]⟩
  exact hq (by rw [he]; rfl)

-- `Iris.BI.persistently_imp_wand` idx 2: necessary (HeapProp Unit (not BIAffine): P=True, Q=emp; <pers>(True->emp) holds, <pers>(True-*emp) fails)
theorem p2_13 : ¬ drop0% Iris.BI.persistently_imp_wand 2 := fun h => by
  have := (@h (HeapProp Unit) _ iprop(True) iprop(emp)).mp ∅ (fun _ => rfl) h0 empty_disjoint trivial
  first | exact h0_ne (empty_union.trans this) | exact h0_ne ((union_comm.trans empty_union.symm).symm.trans this)

-- `Iris.BI.or_absorbing` idx 5: necessary (HeapProp Unit: P=False, Q=emp; False\/emp not absorbing)
theorem p2_14 : ¬ drop0% Iris.BI.or_absorbing 5 := fun h => by
  have := (@h (HeapProp Unit) _ iprop(False) iprop(emp) _).absorbing h0
    ⟨h0, ∅, by rw [union_comm]; exact empty_union, by rw [disjoint_comm]; exact empty_disjoint, trivial, Or.inr rfl⟩
  exact this.elim id h0_ne

-- `Iris.BI.forall_timeless` idx 4: necessary (SiProp, alpha=Unit, Psi = prop holding only at step 0 (not timeless))
theorem p2_15 : ¬ drop0% Iris.BI.forall_timeless 4 := fun h => by
  have := (@h SiProp _ Unit (fun _ => s0)).timeless 1 (fun P ⟨x, hx⟩ => hx ▸ rfl)
  rcases this with h1 | h1
  · exact h1
  · exact absurd (h1 _ ⟨(), rfl⟩) (by simp [s0])

-- `View.frag_incN_auth_op_frag_iff` idx 5: necessary (dependent; R = fun _ _ _ => False over Unit/Unit violates rel_unit)
theorem p2_16 : ¬ indep0% View.frag_incN_auth_op_frag_iff 5 := fun h => by
  obtain ⟨a, ha⟩ := (h (A := Unit) (B := Unit) (R := fun _ _ _ => False) (n := 0) (b1 := ()) (p := DFrac.discard) (a := ()) (b2 := ())).rel_unit 0
  exact ha

-- helper
theorem s0_not_timeless {Q : SiProp} (e : Q ⊣⊢ s0) (h : ▷ Q ⊢ ◇ Q) : False := by
  have := ((later_mono e.2).trans (h.trans (except0_mono e.1))) 1 rfl
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 (by simp [s0])

-- helper
theorem sp {P Q : SiProp} (h : P ⊢ Q) (n : Nat) : P.holds n → Q.holds n := h n

-- helper
abbrev TM := fun V => Std.ExtTreeMap Nat V compare

-- `Iris.BI.BigAndL.bigAndL_intro` idx 6: necessary (SiProp: P=True, l=[()], Phi=False)
theorem p2_17 : ¬ drop0% Iris.BI.BigAndL.bigAndL_intro 6 := fun h =>
  ((@h SiProp _ Unit iprop(True) (fun _ _ => iprop(False)) [()]).trans BigAndL.bigAndL_singleton.1) 0 trivial

-- `Iris.BI.BigSepL.bigSepL_eq_of_forall_eq` idx 6: necessary (SiProp: l=[()], Phi=True, Psi=False)
theorem p2_18 : ¬ drop0% Iris.BI.BigSepL.bigSepL_eq_of_forall_eq 6 := fun h => by
  have e := @h SiProp _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]
  have := (BigSepL.bigSepL_singleton (PROP := SiProp) (Φ := fun _ _ => iprop(False)) (x := ())).1
  rw [← e] at this
  exact this 0 ((BigSepL.bigSepL_singleton (PROP := SiProp) (Φ := fun _ _ => iprop(True)) (x := ())).2 0 trivial)

-- `Iris.BI.BigSepL.bigSepL_timeless_id` idx 4: necessary (SiProp: Ps=[s0], s0 holds only at step 0 (not timeless))
theorem p2_19 : ¬ drop0% Iris.BI.BigSepL.bigSepL_timeless_id 4 := fun h =>
  s0_not_timeless (BigSepL.bigSepL_singleton (Φ := fun _ P => P)) (@h SiProp _ _ [s0]).timeless

-- `Iris.BI.BigSepL2.bigSepL2_append` idx 9: necessary (SiProp: l1a=[()], l2a=[], l1b=[], l2b=[()], Phi=True)
theorem p2_20 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_append 9 := fun h => by
  have := (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] [] [] [()]).mp 0
    (sp BigSepL2.bigSepL2_singleton.2 0 trivial)
  exact absurd (sp BigSepL2.bigSepL2_nil_inv_right 0 this.1) (fun h : [()] = [] => nomatch h)

-- `Iris.BI.BigSepL2.bigSepL2_delete` idx 12: necessary (SiProp: l1=[()], l2=[true], i=0, x2=false, Phi k a b = (b = true))
theorem p2_21 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_delete 12 := fun h => by
  have := (@h SiProp _ Unit Bool _ (fun _ _ b => iprop(⌜b = true⌝)) [()] [true] 0 () false rfl).mp 0
    (sp BigSepL2.bigSepL2_singleton.2 0 rfl)
  exact absurd this.1 (fun h : false = true => nomatch h)

-- `Iris.BI.BigAndM.bigAndM_insert_override` idx 11: necessary (SiProp, ExtTreeMap Nat: m empty, i=0, Phi=False)
theorem p2_22 : ¬ drop0% Iris.BI.BigAndM.bigAndM_insert_override 11 := fun h => by
  have e := @h SiProp _ Nat Unit TM _ (fun _ _ => iprop(False)) ∅ 0 () () rfl
  have := (BigAndM.bigAndM_insert (PROP := SiProp) (M := TM) (Φ := fun _ _ => iprop(False)) (x := ()) (get?_empty 0)).1
  rw [e] at this
  exact (this 0 (sp BigAndM.bigAndM_empty.2 0 trivial)).1

-- `Iris.BI.BigSepM.bigSepM_subseteq` idx 11: necessary (SiProp, ExtTreeMap Nat: m1 empty, m2 = {0:=()}, Phi=False)
theorem p2_23 : ¬ drop0% Iris.BI.BigSepM.bigSepM_subseteq 11 := fun h => by
  have := ((BigSepM.bigSepM_empty (PROP := SiProp) (M := TM) (Φ := fun (_ : Nat) (_ : Unit) => iprop(False))).2.trans
    ((@h SiProp _ Nat Unit TM _ _ (fun _ _ => iprop(False)) ∅ (insert ∅ 0 ()) _).trans
    (BigSepM.bigSepM_insert (get?_empty 0)).1)) 0 trivial
  exact this.1

-- `Iris.BI.BigSepM2.bigSepM2_delete_right` idx 12: necessary (SiProp, ExtTreeMap Nat: m1 = m2 empty, Phi=True)
theorem p2_24 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_delete_right 12 := fun h => by
  have := ((BigSepM2.bigSepM2_empty (PROP := SiProp) (M := TM) (fun (_ : Nat) (_ _ : Unit) => iprop(True))).2.trans
    ((@h SiProp _ Nat Unit Unit TM _ (fun _ _ _ => iprop(True)) ∅ ∅ 0 ()).1.trans
    (show _ ⊢ iprop(False) from exists_elim fun _ => and_elim_l.trans (pure_elim' fun hx => by rw [get?_empty] at hx; cases hx)))) 0 trivial
  exact this

-- `Iris.BI.BigSepS.bigSepS_delete` idx 8: necessary (SiProp, ExtTreeSet Nat: X empty, Phi=False)
theorem p2_25 : ¬ drop0% Iris.BI.BigSepS.bigSepS_delete 8 := fun h => by
  have := (@h SiProp _ (Std.ExtTreeSet Nat compare) Nat _ (fun _ => iprop(False)) ∅ 0).mp 0
    (sp BigSepS.bigSepS_empty.2 0 trivial)
  exact this.1

-- helper
theorem hp {P Q : HeapProp Unit} (h : P ⊢ Q) (σ : State Unit) : P σ → Q σ := h σ

-- helper
theorem not_true_emp (h : iprop(True) ⊢ (emp : HeapProp Unit)) : False := h0_ne (h h0 trivial)

-- `View.auth_discard` idx 5: necessary (dependent; R = fun _ _ _ => False over Unit/Unit violates rel_unit)
theorem p2_26 : ¬ indep0% View.auth_discard 5 := fun h => by
  obtain ⟨a, ha⟩ := (h (A := Unit) (B := Unit) (R := fun _ _ _ => False) (dq := DFrac.discard) (a := ())).rel_unit 0
  exact ha

-- `Iris.view_both_validI_1` idx 7: necessary (dependent; PROP=SiProp, R = fun _ _ _ => False violates rel_unit)
theorem p2_27 : ¬ indep0% Iris.view_both_validI_1 7 := fun h => by
  obtain ⟨a, ha⟩ := (h (PROP := SiProp) (A := Unit) (B := Unit) (R := fun _ _ _ => False) (SiProp.pure True) () () (fun _ f => f.elim)).rel_unit 0
  exact ha

-- `Iris.BI.BigSepM.bigSepM_timeless_inst` idx 9: necessary (SiProp: m = {0:=()}, Phi = s0 (not timeless))
theorem p2_28 : ¬ drop0% Iris.BI.BigSepM.bigSepM_timeless_inst 9 := fun h =>
  s0_not_timeless BigSepM.bigSepM_singleton
    (@h SiProp _ Nat Unit TM _ _ (fun _ _ => s0) (PartialMap.singleton 0 ())).timeless

-- `Iris.BI.BigSepM.bigSepM_absorbing_inst` idx 6: necessary (HeapProp Unit (not BIAffine): m empty, Phi=True; emp not absorbing)
theorem p2_29 : ¬ drop0% Iris.BI.BigSepM.bigSepM_absorbing_inst 6 := fun h => by
  have := (absorbingly_mono BigSepM.bigSepM_empty.2).trans
    ((@h (HeapProp Unit) _ Nat Unit TM _ (fun _ _ => iprop(True)) ∅ (fun _ _ => inferInstance)).absorbing.trans
     BigSepM.bigSepM_empty.1)
  exact h0_ne (hp this h0 ⟨h0, ∅, (union_comm.trans empty_union.symm).symm, fun _ => Or.inr rfl, trivial, rfl⟩)

-- `Iris.BI.BigSepMS.bigSepMS_forall` idx 5: necessary (HeapProp Unit, ListPerm Nat: X empty, Phi=True; True |- emp fails)
theorem p2_31 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_forall 5 := fun h =>
  not_true_emp ((forall_intro fun _ => imp_intro and_elim_l).trans
    ((@h (HeapProp Unit) _ (ListPerm Nat) Nat _ (fun _ => iprop(True)) ∅ (fun _ => pure_persistent True)).2.trans
     BigSepMS.bigSepMS_empty.1))

-- `Iris.BI.BigSepMS.bigSepMS_persistent` idx 7: necessary (HeapProp Unit, ListPerm Nat: X={0}, Phi = owns cell 0 (not persistent))
theorem p2_32 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_persistent 7 := fun h => by
  have := (BigSepMS.bigSepMS_singleton (PROP := HeapProp Unit) (MS := ListPerm Nat) (Φ := fun _ => own0) (x := 0)).2.trans
    ((@h (HeapProp Unit) _ (ListPerm Nat) Nat _ (fun _ => own0) {0}).persistent.trans
     (persistently_mono BigSepMS.bigSepMS_singleton.1))
  exact hp this h0 (by simp [own0, h0]) rfl

-- `Iris.BI.BigSepM2.bigSepM2_sepM` idx 11: necessary (SiProp, ExtTreeMap Nat: m1={0:=()}, m2 empty, Phi1=Phi2=True)
theorem p2_33 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_sepM 11 := fun h => by
  have := (@h SiProp _ Nat Unit Unit TM _ (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
    (PartialMap.singleton 0 ()) ∅).2 0 ⟨sp BigSepM.bigSepM_singleton.2 0 trivial, sp BigSepM.bigSepM_empty.2 0 trivial⟩
  have hd := sp (BigSepM2.bigSepM2_dom _ _ _) 0 this
  have e := congrFun hd 0
  simp only [PartialMap.dom, get?_empty] at e
  rw [LawfulPartialMap.get?_singleton_eq rfl] at e
  simp at e

-- `Iris.BI.BigSepM2.bigSepM2_lookup_acc_impl` idx 15: necessary (SiProp: m1={0:=()}, m2={0:=true}, x2=false, Phi k a b = (b = true))
theorem p2_34 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_lookup_acc_impl 15 := fun h => by
  have := @h SiProp _ Nat Unit Bool TM _ _ (fun _ _ b => iprop(⌜b = true⌝)) (PartialMap.singleton 0 ())
    (PartialMap.singleton 0 true) 0 () false (LawfulPartialMap.get?_singleton_eq rfl) 0
    (sp (BigSepM2.bigSepM2_singleton _ _ _ _).2 0 rfl)
  exact absurd this.1 (fun h : false = true => nomatch h)

-- `Iris.BI.BigSepMS.bigSepMS_dup` idx 6: necessary (HeapProp Unit, ListPerm Nat: P=True (not affine), X empty)
theorem p2_35 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_dup 6 := fun h => by
  have := @h (HeapProp Unit) _ (ListPerm Nat) Nat _ iprop(True) ∅ ∅ rfl ∅ empty_disjoint
    ⟨rfl, fun σ' _ _ => ⟨∅, ∅ ∪ σ', empty_union, empty_disjoint, trivial, trivial⟩⟩ h0 (fun _ => Or.inl rfl) trivial
  have e := congrFun (hp BigSepMS.bigSepMS_empty.1 _ this) 0
  simp [h0, Union.union, EmptyCollection.emptyCollection] at e

-- helper
instance leU : LE Unit := ⟨fun _ _ => True⟩

-- helper
instance : Std.IsPreorder Unit := { le_refl := fun _ => trivial, le_trans := fun _ _ _ _ _ => trivial }

-- helper
def I0 : BiIndex := ⟨Unit, leU⟩

-- `Iris.BI.BiEmbed.emp_valid_inj` idx 6: necessary (embedding SiProp into MonPred over a one-point index, P=False)
theorem p2_36 : ¬ drop0% Iris.BI.BiEmbed.emp_valid_inj 6 := fun h =>
  @h SiProp (MonPred I0 SiProp) _ _ _ iprop(False) 0 trivial

-- helper
theorem own0_sep_own0 {σ : State Unit} : ¬ iprop(own0 ∗ own0) σ := fun ⟨σ1, σ2, _, hd, h1, h2⟩ =>
  (hd 0).elim h1 h2

-- `Iris.BI.BigSepS.bigSepS_union` idx 8: necessary (HeapProp Unit, ExtTreeSet Nat: X=Y={0}, Phi = owns cell 0 (own0*own0 = False))
theorem p2_37 : ¬ drop0% Iris.BI.BigSepS.bigSepS_union 8 := fun h => by
  have e := (@h (HeapProp Unit) _ (Std.ExtTreeSet Nat compare) Nat _ (fun _ => own0) {0} {0}).1
  rw [LawfulSet.union_idem] at e
  exact own0_sep_own0 (hp ((BigSepS.bigSepS_singleton.2.trans e).trans
    (sep_mono BigSepS.bigSepS_singleton.1 BigSepS.bigSepS_singleton.1)) h0 (by simp [own0, h0]))

-- `View.map_ne` idx 18: necessary (A=B=A'=Unit, B'=DFrac, f=id, g1 = const discard, g2 = const (own 1), v=<none, ()>)
theorem p2_38 : ¬ drop0% View.map_ne 18 := fun h => by
  have := (@h Unit Unit Unit DFrac _ _ _ (fun _ _ _ => True) (fun _ _ _ => True) 0 id id
    (fun _ => DFrac.discard) (fun _ => DFrac.own 1) inferInstance inferInstance ⟨none, ()⟩
    (fun _ => OFE.Dist.rfl)).2
  exact absurd this (by simp [OFE.Dist, View.map])

-- helper
universe u1 u2 u3 u4

-- `View.map_ne` idx 14: removable (the proof only needs pointwise f1 a =n= f2 a for Agree.map'; NonExpansive f1 is used only to form the coerced Agree.map in Agree.map_ne, whose proof does not use it)
theorem p2_39 : drop% View.map_ne 14 := by
  intro A B A' B' _ _ _ R R' n f1 f2 g1 g2 _ v h1 h2
  refine ⟨?_, h2 _⟩
  simp only [View.map]
  split
  · rfl
  · refine ⟨rfl, ?_⟩
    rename_i a _
    exact a.ind fun _ => by
      refine Agree.dist_mk.mpr ⟨?_, ?_⟩ <;> simp only [Agree.Raw.map'_car, List.mem_map] <;> rintro _ ⟨a, ha, rfl⟩
      · exact ⟨f2 a, ⟨a, ha, rfl⟩, h1 a⟩
      · exact ⟨f1 a, ⟨a, ha, rfl⟩, h1 a⟩

-- helper
def h1 : State Unit := fun i => if i = 1 then result () else unknown

-- helper
def P1 : HeapProp Unit := fun σ => σ = h0 ∨ σ = h1

-- `Iris.BI.BigSepM.bigSepM_insert_elim` idx 10: necessary (HeapProp Unit: m={0:=()}, i=0, Phi = heap is exactly {0} or exactly {1}; P*P |- P fails at {0,1})
theorem p2_40 : ¬ drop0% Iris.BI.BigSepM.bigSepM_insert_elim 10 := fun h => by
  have := @h (HeapProp Unit) _ Nat Unit TM _ (fun _ _ => P1) (PartialMap.singleton 0 ()) 0 () ∅ rfl
    h0 empty_disjoint (Or.inl rfl) h1
    (fun i => by by_cases hi : i = 0 <;> simp [h0, h1, hi, Union.union, EmptyCollection.emptyCollection])
    (hp BigSepM.bigSepM_singleton.2 h1 (Or.inr rfl))
  rw [BigSepM.bigSepM_insert_exist (LawfulPartialMap.get?_singleton_eq rfl) rfl] at this
  rcases hp BigSepM.bigSepM_singleton.1 _ this with e | e
  · have := congrFun e 1; simp [h0, h1, Union.union, EmptyCollection.emptyCollection] at this
  · have := congrFun e 0; simp [h0, h1, Union.union, EmptyCollection.emptyCollection] at this

-- `Iris.BI.BigSepM.bigSepM_sep_zipWith` idx 15: necessary (SiProp: A=Bool, B=C=Unit, g1 = const false, m1={0:=true}, m2={0:=()}, Phi1 k a = (a = true))
theorem p2_41 : ¬ drop0% Iris.BI.BigSepM.bigSepM_sep_zipWith 15 := fun h => by
  have hs : ∀ k, (get? (PartialMap.singleton 0 true : TM Bool) k).isSome = true ↔
      (get? (PartialMap.singleton 0 () : TM Unit) k).isSome = true := fun k => by
    by_cases hk : (0 : Nat) = k
    · rw [LawfulPartialMap.get?_singleton_eq hk, LawfulPartialMap.get?_singleton_eq hk]; rfl
    · rw [LawfulPartialMap.get?_singleton_ne hk, LawfulPartialMap.get?_singleton_ne hk]; exact Iff.rfl
  have e : PartialMap.zipWith (fun (_ : Bool) (_ : Unit) => ()) (PartialMap.singleton 0 true : TM Bool)
      (PartialMap.singleton 0 ()) = (PartialMap.singleton 0 () : TM Unit) := by
    apply LawfulPartialMap.equiv_iff_eq.mp
    intro k
    rw [LawfulPartialMap.get?_zipWith]
    by_cases hk : (0 : Nat) = k
    · simp only [LawfulPartialMap.get?_singleton_eq hk]; rfl
    · simp only [LawfulPartialMap.get?_singleton_ne hk]; rfl
  have := (@h SiProp _ Nat TM _ Bool Unit Unit (fun _ _ => ()) (fun _ => false) (fun _ => ())
    (fun _ a => iprop(⌜a = true⌝)) (fun _ _ => iprop(True)) (PartialMap.singleton 0 true)
    (PartialMap.singleton 0 ()) rfl hs).2 0
    ⟨sp BigSepM.bigSepM_singleton.2 0 rfl, sp BigSepM.bigSepM_singleton.2 0 trivial⟩
  rw [e] at this
  exact absurd (sp BigSepM.bigSepM_singleton.1 0 this).1 (fun h : false = true => nomatch h)

-- helper
open ORA in
abbrev CM : TM Unit := insert (PartialMap.singleton 0 ()) 1 ()

-- helper
theorem cm_forall_sep :
    (UPred.ownM (1 : Credit)) ⊢ ∀ k v, iprop(⌜get? CM k = some v⌝ → UPred.ownM (1 : Credit)) :=
  forall_intro fun _ => forall_intro fun _ => imp_intro and_elim_l

-- helper
theorem cm_sep_ownM : ([∗map] k ↦ v ∈ CM, (fun _ _ => UPred.ownM (1 : Credit)) k v) ⊢
    UPred.ownM (2 : Credit) :=
  ((BigSepM.bigSepM_insert (LawfulPartialMap.get?_singleton_ne (by decide))).1.trans
    (sep_mono_right BigSepM.bigSepM_singleton.1)).trans (UPred.ownM_op (1 : Credit) 1).2

-- helper
open ORA in
theorem cm_bad (h : (UPred.ownM (1 : Credit)) ⊢ UPred.ownM (2 : Credit)) : False := by
  have := h 0 ⟨1, (OFE.Dist.validN rfl).mp trivial⟩ (ordN_refl _)
  simp [UPred.ownM] at this
  obtain ⟨z, hz⟩ := this
  have hz' : (1 : Nat) = 2 + z := hz
  omega

-- `Iris.BI.BigSepM.bigSepM_forall_elim` idx 9: necessary (UPred Credit (affine, core = 0): m = {0,1}, Phi = ownM 1 (not persistent); ownM 1 |- ownM 2 fails)
theorem p2_30 : ¬ drop0% Iris.BI.BigSepM.bigSepM_forall_elim 9 := fun h =>
  cm_bad (cm_forall_sep.trans ((@h (UPred Credit) _ Nat Unit TM _ (fun _ _ => UPred.ownM (1 : Credit)) CM _).trans
    cm_sep_ownM))

-- `Iris.BI.BigSepM.bigSepM_forall` idx 9: necessary (UPred Credit (affine, core = 0): m = {0,1}, Phi = ownM 1 (not persistent))
theorem p2_42 : ¬ drop0% Iris.BI.BigSepM.bigSepM_forall 9 := fun h =>
  cm_bad (cm_forall_sep.trans ((@h (UPred Credit) _ Nat Unit TM _ (fun _ _ => UPred.ownM (1 : Credit)) CM _).2.trans
    cm_sep_ownM))

-- `Iris.BI.absorbingly_persistent` idx 3: necessary (UPred Credit (affine, core = 0): P = ownM 1; <absorb> P = P not persistent)
theorem p2_43 : ¬ drop0% Iris.BI.absorbingly_persistent 3 := fun h => by
  have e := ((absorbingly_intro (P := UPred.ownM (1 : Credit))).trans
    (@h (UPred Credit) _ (UPred.ownM (1 : Credit))).persistent).trans
    (persistently_mono (Absorbing.absorbing (P := UPred.ownM (1 : Credit))))
  have := e 0 ⟨1, (OFE.Dist.validN rfl).mp trivial⟩ (ORA.ordN_refl _)
  obtain ⟨z, hz⟩ := this
  have hz' : (0 : Nat) = 1 + z := hz
  omega


-- helper: two-element resource algebra (UPred over it is a non-affine BI)
/-- two-element resource algebra with equality order (not affine): o is the unit -/
inductive B2 | o | i deriving DecidableEq
def B2.or : B2 → B2 → B2
  | .o, y => y
  | .i, _ => .i
instance : COFE B2 := COFE.ofDiscrete _
instance : OFE.Discrete B2 := ⟨fun h => h⟩
instance : Op B2 where
  op := B2.or
  op_ne := ⟨fun _ _ _ h => by cases (h : _ = _); exact OFE.Dist.rfl⟩
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
instance : PCore B2 where
  pcore _ := some .o
  pcore_ne := by intro n x y cx _ h; cases h; exact ⟨.o, rfl, OFE.Dist.rfl⟩
  pcore_idem := by intro x cx h; cases h; rfl
instance : Valid B2 where
  ValidN _ _ := True
  Valid _ := True
  validN_ne := fun _ h => h
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ := fun h => h
instance : Ordered B2 where
  OrderN _ x y := x = y
  Order x y := x = y
  ordN_ne := by intro n x x' y y' hx hy h; exact (hx : x = x') ▸ (hy : y = y') ▸ h
  ordN_succ := id
  ordN_trans := Eq.trans
  ord_trans := Eq.trans
  ordN_of_ord := fun _ h => h
instance : ORA B2 where
  validN_op_left := fun _ => trivial
  pcore_op_left := by intro x cx h; cases h; rfl
  extend := fun {_ _ y₁ y₂} _ h => ⟨y₁, y₂, h, OFE.Dist.rfl, OFE.Dist.rfl⟩
  op_monoN_left_ord := by intro n x y z h; exact congrArg (· • z) h
  op_mono_left_ord := by intro x y z h; exact congrArg (· • z) h
  validN_of_ordN := fun _ _ => trivial
  pcore_monoN_ord := by intro n x y cx _ h; cases h; exact ⟨.o, rfl, rfl⟩
  pcore_mono_ord := by intro x y cx _ h; cases h; exact ⟨.o, rfl, rfl⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.o, rfl, rfl⟩
  pcore_increasing := by intro x cx h; cases h; exact ⟨fun y => rfl⟩
  increasing_closed := by
    intro n x y hx h
    rcases h with h | h <;> (have e : x = y := h; exact e ▸ hx)
  ordN_extend := by intro n x y _ h; exact ⟨y, rfl, (h : x = y) ▸ OFE.Dist.rfl⟩
instance : OrderRefl B2 := ⟨fun _ => rfl⟩
instance : UORA B2 where
  unit := .o
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

-- `Iris.BI.bi_laterN_sep_homomorphism` idx 2: necessary (UPred B2, a non-affine BI over a two-element RA with equality order: map_unit says later emp = emp, but at step 0 and resource i later emp holds and emp does not)
theorem p2_44 : ¬ drop0% Iris.BI.bi_laterN_sep_homomorphism 2 := fun h => by
  have e := (@h (UPred B2) _ 1).map_unit
  have : (iprop(▷^[1] emp) : UPred B2).holds 0 ⟨.i, trivial⟩ := by
    show (UPred.later _).holds 0 _
    trivial
  rw [e] at this
  exact absurd this (fun h' => nomatch (h' : B2.o = B2.i))


-- helper: delay embedding and identity embedding of SiProp into itself
/-- delay: a step-indexed prop read one step earlier -/
def dl (P : SiProp) : SiProp := ⟨fun n => P.holds (n - 1), fun h hle => P.closed h (by omega)⟩

/-- embedding of SiProp into itself by delay; it does not commute with later -/
@[instance_reducible] def delayE : BiEmbed SiProp SiProp where
  embed := dl
  ne := ⟨fun {n x y} h m hle => h (by omega)⟩
  mono := fun h n hp => h _ hp
  emp_valid_inj := fun P h n _ => h (n + 1) trivial
  emp_2 := fun _ _ => trivial
  impl_2 := fun P Q n h m hm hp => by
    cases n with
    | zero => have e : m = 0 := by omega
              subst e; exact h 0 (Nat.le_refl 0) hp
    | succ k => exact h (m + 1) (by omega) hp
  forall_2 := fun Ψ R h n hr P hP => h P hP n hr
  exist_1 := fun Ψ R h n ⟨P, hP, hp⟩ => h P hP n hp
  sep := fun P Q => ⟨fun _ h => h, fun _ h => h⟩
  wand_2 := fun P Q n h m hm hp => by
    cases n with
    | zero => have e : m = 0 := by omega
              subst e; exact h 0 (Nat.le_refl 0) hp
    | succ k => exact h (m + 1) (by omega) hp
  persistently := fun P => ⟨fun _ h => h, fun _ h => h⟩
/-- identity embedding of SiProp into itself (commutes with later) -/
@[instance_reducible] def idE : BiEmbed SiProp SiProp where
  embed := id
  ne := ⟨fun _ _ _ h => h⟩
  mono := fun h => h
  emp_valid_inj := fun _ h => h
  emp_2 := fun _ h => h
  impl_2 := fun _ _ _ h => h
  forall_2 := fun Ψ R h n hr P hP => h P hP n hr
  exist_1 := fun Ψ R h n ⟨P, hP, hp⟩ => h P hP n hp
  sep := fun _ _ => ⟨fun _ h => h, fun _ h => h⟩
  wand_2 := fun _ _ _ h => h
  persistently := fun _ => ⟨fun _ h => h, fun _ h => h⟩
theorem idL : @BiEmbedLater SiProp SiProp _ _ idE :=
  @BiEmbedLater.mk SiProp SiProp _ _ idE (fun _ => ⟨fun _ h => h, fun _ h => h⟩)

-- `Iris.BI.embed_embed_later` idx 9: necessary (PA = PB = PC = SiProp, identity embedding PA to PB commutes with later, delay embedding PB to PC does not; the composite maps later False to a prop true at step 1)
theorem p2_45 : ¬ drop0% Iris.BI.embed_embed_later 9 := fun h => by
  have h' := @h SiProp SiProp _ _ SiProp _ idE delayE idL
  exact (h'.1 iprop(False)).mp 1 trivial


-- helper: a commutative monoid on SiProp, conjunction with the step-0-only prop u2 adjoined as unit
/-- conjunction with the step-0-only prop adjoined as a fresh unit -/
def op2 (x y : SiProp) : SiProp :=
  ⟨fun n => (x.holds n ∧ y.holds n) ∨ (x.holds 0 ∧ ¬ x.holds 1 ∧ y.holds n) ∨ (y.holds 0 ∧ ¬ y.holds 1 ∧ x.holds n),
   fun h hle => by
     rcases h with ⟨a, b⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
     · exact Or.inl ⟨x.closed a hle, y.closed b hle⟩
     · exact Or.inr (Or.inl ⟨a, b, y.closed c hle⟩)
     · exact Or.inr (Or.inr ⟨a, b, x.closed c hle⟩)⟩
def u2 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩
theorem sp_ext {P Q : SiProp} (h : ∀ n, P.holds n ↔ Q.holds n) : P = Q := by
  obtain ⟨p, _⟩ := P; obtain ⟨q, _⟩ := Q
  have : p = q := funext fun n => propext (h n)
  subst this; rfl
theorem op2_assoc (a b c : SiProp) : op2 (op2 a b) c = op2 a (op2 b c) := by
  apply sp_ext; intro n
  have a10 : a.holds 1 → a.holds 0 := fun h => a.closed h (by omega)
  have b10 : b.holds 1 → b.holds 0 := fun h => b.closed h (by omega)
  have c10 : c.holds 1 → c.holds 0 := fun h => c.closed h (by omega)
  cases n with
  | zero => simp only [op2]; grind
  | succ k =>
    have ak : a.holds (k+1) → a.holds 1 := fun h => a.closed h (by omega)
    have bk : b.holds (k+1) → b.holds 1 := fun h => b.closed h (by omega)
    have ck : c.holds (k+1) → c.holds 1 := fun h => c.closed h (by omega)
    simp only [op2]; grind
theorem op2_comm (a b : SiProp) : op2 a b = op2 b a := by
  apply sp_ext; intro n; simp only [op2]; grind
theorem op2_left_id (a : SiProp) : op2 u2 a = a := by
  apply sp_ext; intro n
  have a10 : a.holds 1 → a.holds 0 := fun h => a.closed h (by omega)
  cases n with
  | zero => simp only [op2, u2]; grind
  | succ k =>
    have ak : a.holds (k+1) → a.holds 1 := fun h => a.closed h (by omega)
    simp only [op2, u2]; grind
theorem op2_ne : OFE.NonExpansive₂ op2 := ⟨fun n x₁ x₂ hx y₁ y₂ hy m hm => by
  have x0 := hx (Nat.zero_le n); have y0 := hy (Nat.zero_le n)
  have xm := hx hm; have ym := hy hm
  cases m with
  | zero => simp only [op2]; grind
  | succ k =>
    have x1 := hx (show 1 ≤ n by omega); have y1 := hy (show 1 ≤ n by omega)
    simp only [op2]; grind⟩
theorem op2Ops : Algebra.MonoidOps op2 u2 where
  op_ne := op2_ne
  op_assoc := op2_assoc _ _ _
  op_comm := op2_comm _ _
  op_left_id := op2_left_id _

-- `Iris.BI.mkEmbedHom` idx 12: necessary (delay embedding SiProp to SiProp, op1 = and with unit True, op2 = op2 with unit u2; hop holds since no delayed prop equals u2, but the delay of True is not u2)
theorem p2_46 : ¬ drop0% Iris.BI.mkEmbedHom 12 := fun h => by
  have h' := @h SiProp SiProp _ _ delayE BIBase.and op2 iprop(True) u2 andMonoidOps op2Ops (by
    intro x y; apply sp_ext; intro n
    have x10 : x.holds 1 → x.holds 0 := fun h => x.closed h (by omega)
    have y10 : y.holds 1 → y.holds 0 := fun h => y.closed h (by omega)
    have ex0 : (@Embed.embed SiProp SiProp delayE.toEmbed x).holds 0 ↔ x.holds 0 := Iff.rfl
    have ex1 : (@Embed.embed SiProp SiProp delayE.toEmbed x).holds 1 ↔ x.holds 0 := Iff.rfl
    have ey0 : (@Embed.embed SiProp SiProp delayE.toEmbed y).holds 0 ↔ y.holds 0 := Iff.rfl
    have ey1 : (@Embed.embed SiProp SiProp delayE.toEmbed y).holds 1 ↔ y.holds 0 := Iff.rfl
    have exn : ∀ k, (@Embed.embed SiProp SiProp delayE.toEmbed x).holds (k+1) ↔ x.holds k := fun _ => Iff.rfl
    have eyn : ∀ k, (@Embed.embed SiProp SiProp delayE.toEmbed y).holds (k+1) ↔ y.holds k := fun _ => Iff.rfl
    cases n with
    | zero => simp only [op2]; show Iff (x.holds 0 ∧ y.holds 0) _; grind
    | succ k => simp only [op2]; show Iff (x.holds k ∧ y.holds k) _; grind)
  have e := h'.map_unit
  have := congrArg (fun P : SiProp => P.holds 1) e
  simp only [u2] at this
  exact absurd (this ▸ trivial : (1 : Nat) = 0) (by omega)


-- helper: two-point index and an embedding of SiProp into MonPred that is the identity at lo and the delay at hi
/-- two-point index lo below hi -/
inductive Ix | lo | hi deriving DecidableEq, Inhabited
instance leIx : LE Ix := ⟨fun a b => a = .lo ∨ b = .hi⟩
instance : Std.IsPreorder Ix where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c h1 h2 := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]
def I2 : BiIndex := ⟨Ix, leIx⟩
/-- the prop itself at lo and its delay at hi -/
def eD (P : SiProp) : MonPred I2 SiProp where
  monPred_at i := match i with | .lo => P | .hi => dl P
  monPred_mono {i j} h := by
    cases i <;> cases j
    · exact fun _ h => h
    · exact fun n hp => P.closed hp (by omega)
    · exact absurd h (fun h' => by rcases h' with h' | h' <;> cases h')
    · exact fun _ h => h
/-- embedding of SiProp into MonPred over I2 via eD; it does not commute with plainly -/
@[instance_reducible] def eDE : BiEmbed SiProp (MonPred I2 SiProp) where
  embed := eD
  ne := ⟨fun n x y h i => by
    cases i
    · exact h
    · exact fun {m} hm => h (show m - 1 ≤ n by omega)⟩
  mono := fun h i => by
    cases i
    · exact h
    · exact fun n hp => h _ hp
  emp_valid_inj := fun P h => h .lo
  emp_2 := fun i => by cases i <;> exact fun _ _ => trivial
  impl_2 := fun P Q i => by
    cases i
    · exact fun n h => h _ ⟨.lo, rfl⟩ n (Nat.le_refl n) (Or.inl rfl)
    · exact fun n h => delayE.impl_2 P Q n (h _ ⟨.hi, rfl⟩ n (Nat.le_refl n) (Or.inr rfl))
  forall_2 := fun Ψ R h i => by
    cases i
    · exact fun n hr P hP => h P hP .lo n hr
    · exact fun n hr P hP => h P hP .hi n hr
  exist_1 := fun Ψ R h i => by
    cases i
    · exact fun n ⟨P, hP, hp⟩ => h P hP .lo n hp
    · exact fun n ⟨P, hP, hp⟩ => h P hP .hi n hp
  sep := fun P Q => ⟨fun i => by cases i <;> exact fun _ h => h, fun i => by cases i <;> exact fun _ h => h⟩
  wand_2 := fun P Q i => by
    cases i
    · exact fun n h => h _ ⟨.lo, rfl⟩ n (Nat.le_refl n) (Or.inl rfl)
    · exact fun n h => delayE.wand_2 P Q n (h _ ⟨.hi, rfl⟩ n (Nat.le_refl n) (Or.inr rfl))
  persistently := fun P => ⟨fun i => by cases i <;> exact fun _ h => h, fun i => by cases i <;> exact fun _ h => h⟩

-- `Iris.BI.embed_plainly_if` idx 5: necessary (P1 = SiProp, P2 = MonPred over a two-point index, embedding P to (P, delayed P); with p = true and P = s0 the left side holds at hi and step 1, the plainly of the embedding needs s0 at step 1)
theorem p2_47 : ¬ drop0% Iris.BI.embed_plainly_if 5 := fun h => by
  have := (@h SiProp (MonPred I2 SiProp) _ _ eDE true s0).mp .hi 1 rfl
  exact absurd (this _ ⟨.lo, rfl⟩) (fun h' => Nat.one_ne_zero (h' : (1 : Nat) = 0))

end Probe2
