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

namespace Probe4

abbrev UIdx : Iris.BI.BiIndex := { car := Nat, rel := inferInstance }

section
open Iris Iris.BI Iris.ProofMode


-- `Iris.ProofMode.AddModal.add_modal` idx 5: necessary (SiProp: P=True, P'=False, Q=False)
theorem p4_1 : ¬ drop0% Iris.ProofMode.AddModal.add_modal 5 := fun h =>
  (@h SiProp SiProp.instBI iprop(True) iprop(False) iprop(False)) 0 ⟨trivial, fun _ _ hf => hf⟩

-- `Iris.ProofMode.split_sr` idx 6: necessary (SiProp: P=Q=P2=True, P1=False)
theorem p4_2 : ¬ drop0% Iris.ProofMode.split_sr 6 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True)).mp 0 ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.remove_right` idx 6: necessary (SiProp: P=Q=R=True, Q'=False)
theorem p4_3 : ¬ drop0% Iris.ProofMode.remove_right 6 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True)).mp 0 ⟨trivial, trivial⟩).1.2

-- `Iris.ProofMode.intoWand_wand` idx 8: necessary (SiProp: P=True, Q=P'=False, p=q=false)
theorem p4_4 : ¬ drop0% Iris.ProofMode.intoWand_wand 8 := fun h =>
  (@h SiProp (.matching .argument) false false _ iprop(True) iprop(False) iprop(False)).into_wand 0
    (fun _ _ hf => hf) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromForall_intuitionistically` idx 7: necessary (SiProp: A=True, P=False, Phi=True)
theorem p4_5 : ¬ drop0% Iris.ProofMode.fromForall_intuitionistically 7 := fun h =>
  ((@h SiProp _ _ _ True iprop(False) (fun _ => iprop(True))).from_forall 0
    (SiProp.forall_holds.2 fun _ => ⟨trivial, trivial⟩)).2

-- `Iris.ProofMode.intoExist_and_pure` idx 7: necessary (SiProp: PQ=P=Q=True, Phi=False)
theorem p4_6 : ¬ drop0% Iris.ProofMode.intoExist_and_pure 7 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp _ iprop(True) iprop(True) iprop(True) False
    ⟨fun _ _ => ⟨trivial, trivial⟩⟩).into_exists 0 trivial) with
  | ⟨x, _⟩ => x

-- `Iris.ProofMode.intoSep_persistently` idx 6: necessary (SiProp: P=Q2=True, Q1=False)
theorem p4_7 : ¬ drop0% Iris.ProofMode.intoSep_persistently 6 := fun h =>
  ((@h SiProp _ _ iprop(True) iprop(False) iprop(True)).into_sep 0 trivial).1

-- `Iris.ProofMode.fromPure_pure_wand` idx 9: necessary (SiProp: a=false, P1=True, P2=False, phi1=phi2=True)
theorem p4_8 : ¬ drop0% Iris.ProofMode.fromPure_pure_wand 9 := fun h =>
  (@h SiProp false .in True True _ iprop(True) iprop(False) ⟨fun _ _ => trivial⟩
    (@Iris.Std.TCOr.l _ _ Iris.Std.TCEq.refl)).from_pure 0 (fun x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromPure_laterN` idx 7: necessary (SiProp: n=0, P=False, phi=True)
theorem p4_9 : ¬ drop0% Iris.ProofMode.fromPure_laterN 7 := fun h =>
  (@h SiProp .in _ false 0 iprop(False) True).from_pure 0 trivial

-- `Iris.ProofMode.fromExists_later` idx 5: necessary (SiProp at step 1: P=False, Phi=True)
theorem p4_10 : ¬ drop0% Iris.ProofMode.fromExists_later 5 := fun h =>
  (@h SiProp True _ iprop(False) (fun _ => iprop(True))).from_exists 1
    (SiProp.exists_holds.2 ⟨trivial, trivial⟩)

-- `Iris.ProofMode.intoExists_later` idx 6: necessary (SiProp at step 1: P=True, Phi=False)
theorem p4_11 : ¬ drop0% Iris.ProofMode.intoExists_later 6 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp True _ ⟨trivial⟩ iprop(True) (fun _ => iprop(False))).into_exists 1 trivial) with
  | ⟨_, hx⟩ => hx

-- `Iris.ProofMode.combineSepGives_except0` idx 5: necessary (SiProp at step 1: Q1=Q2=True, P=False)
theorem p4_12 : ¬ drop0% Iris.ProofMode.combineSepGives_except0 5 := fun h =>
  match (@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_gives 1 ⟨Or.inr trivial, Or.inr trivial⟩ with
  | Or.inl hl => hl
  | Or.inr hr => hr

-- `Iris.ProofMode.frame_finish_close_emp` idx 5: necessary (SiProp: origE=e=True, origGoal=False)
theorem p4_13 : ¬ drop0% Iris.ProofMode.frame_finish_close_emp 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False)) 0 trivial |>.2

-- `Iris.ProofMode.pure_intro_spatial` idx 6: necessary (SiProp: P=True, Q=False, phi=False)
theorem p4_14 : ¬ drop0% Iris.ProofMode.pure_intro_spatial 6 := fun h =>
  (@h SiProp iprop(True) _ iprop(False) False ⟨fun _ hf => hf⟩) 0 trivial
end

section
open Iris Iris.BI Iris.ProofMode


-- `Iris.ProofMode.intoIH_imp` idx 7: necessary (SiProp: phi=psi=False, Delta=P=True, Q=False)
theorem p4_15 : ¬ drop0% Iris.ProofMode.intoIH_imp 7 := fun h =>
  (@h SiProp _ False False iprop(True) iprop(True) iprop(False) ⟨fun hf => hf.elim⟩).into_ih id 0
    ⟨trivial, trivial⟩ 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.elimModal_timeless_spatial` idx 7: necessary (SiProp at step 0: P=later False, P'=Q=False)
theorem p4_16 : ¬ drop0% Iris.ProofMode.elimModal_timeless_spatial 7 := fun h =>
  (@h SiProp _ false iprop(▷ False) iprop(False) iprop(False) ⟨fun _ hl => Or.inl hl⟩).elim_modal trivial 0
    ⟨trivial, fun _ _ hf => hf⟩

-- `Iris.ProofMode.intoLaterN_laterN` idx 13: necessary (SiProp: all counts 0, P=True, Q=lQ=False)
theorem p4_17 : ¬ drop0% Iris.ProofMode.intoLaterN_laterN 13 := fun h =>
  (@h SiProp _ false false false 0 0 0 0 iprop(True) iprop(False) iprop(False) ⟨rfl⟩
    ⟨⟨fun _ h => h, fun _ h => h⟩⟩).into_laterN 0 trivial

-- `Iris.ProofMode.imp_intro_spatial` idx 10: necessary (SiProp: P=A1=B=True, Q=A2=False)
theorem p4_18 : ¬ drop0% Iris.ProofMode.imp_intro_spatial 10 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(True) iprop(False) iprop(True)
    ⟨fun n hi => hi n (Nat.le_refl n) trivial⟩ ⟨fun _ _ => trivial⟩ inferInstance) 0 trivial

-- `Iris.ProofMode.combineSepAs_embed` idx 8: necessary (embed SiProp into MonPred (Nat index): Q1=Q2=True, P=False)
theorem p4_19 : ¬ drop0% Iris.ProofMode.combineSepAs_embed 8 := fun h =>
  (@h SiProp (MonPred UIdx SiProp) _ _ _ iprop(True) iprop(True) iprop(False)).combine_sep_as (0 : Nat) 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromModal_later_embed` idx 13: necessary (embed into MonPred: n=0, Q=True, P=False)
theorem p4_20 : ¬ drop0% Iris.ProofMode.fromModal_later_embed 13 := fun h =>
  (@h SiProp (MonPred UIdx SiProp) _ _ _ _ Unit True .in () 0 iprop(False) iprop(True)).from_modal trivial
    (0 : Nat) 0 trivial

-- `Iris.ProofMode.intoWand_affine_embed_false` idx 9: necessary (embed into MonPred: R=P=True, Q=False, q=false)
theorem p4_21 : ¬ drop0% Iris.ProofMode.intoWand_affine_embed_false 9 := fun h => by
  have := (@h SiProp (MonPred UIdx SiProp) _ _ _ false iprop(True) iprop(False) iprop(True)).into_wand (0 : Nat) 0 trivial
  exact (SiProp.forall_holds.1 this) (0 : Nat) 0 (Nat.le_refl 0) (Nat.le_refl 0) 0 (Nat.le_refl 0) ⟨trivial, trivial⟩

-- `List.nodup_map_of_injective` idx 5: necessary (l=[(),()], f=id)
theorem p4_22 : ¬ drop0% List.nodup_map_of_injective 5 := fun h =>
  absurd (@h Unit Unit id [(), ()] (fun _ _ e => e)) (by decide)

-- `coinfinite_fset_coinfinite` idx 5: necessary (K=V=Unit: no injection Nat into Unit)
theorem p4_23 : ¬ drop0% coinfinite_fset_coinfinite 5 := fun h =>
  match @h Unit Unit () none (fun _ => none) with
  | ⟨_, _, hinj⟩ => absurd (hinj 0 1 rfl) (by decide)

-- `CoPset.elemOf_leftRaw_imp` idx 2: necessary (t = leaf false, p = xH)
theorem p4_24 : ¬ drop0% CoPset.elemOf_leftRaw_imp 2 := fun h =>
  absurd (h (.leaf false) .xH) (by decide)

-- `Iris.Std.LawfulSet.inter_subset_absorption` idx 5: necessary (CoPset: s1={xH}, s2=empty)
theorem p4_25 : ¬ drop0% Iris.Std.LawfulSet.inter_subset_absorption 5 := fun h => by
  have e := @h CoPset Pos _ {Pos.xH} ∅
  have h1 : Pos.xH ∈ ({Pos.xH} : CoPset) := Iris.Std.LawfulSet.mem_singleton.2 rfl
  rw [← e] at h1
  exact Iris.Std.LawfulSet.mem_empty (Iris.Std.LawfulSet.mem_inter.1 h1).2

-- `Iris.Std.disjUnion_difference_of_subseteq` idx 5: necessary (ListPerm Unit: X=empty, Y={()})
theorem p4_26 : ¬ drop0% Iris.Std.disjUnion_difference_of_subseteq 5 := fun h => by
  have e := congrArg (Iris.Std.MultiSet.multiplicity ()) (@h (Iris.Std.ListPerm Unit) Unit _ ∅ {()})
  rw [Iris.Std.multiplicity_disjUnion, Iris.Std.multiplicity_empty, Iris.Std.multiplicity_singleton_eq] at e
  omega

-- `Iris.Std.LawfulPartialMap.all_of_all_insert` idx 8: necessary (K->Option V map: m=const (some false), x=true, P k v := v=true)
theorem p4_27 : ¬ drop0% Iris.Std.LawfulPartialMap.all_of_all_insert 8 := fun h => by
  have := @h Unit Bool (fun V => Unit → Option V) _ (fun _ v => v = true) (fun _ => some false) () true
    (by intro k v hk; simp [Iris.Std.get?, Iris.Std.insert] at hk; exact hk)
  exact absurd (this () false rfl) (by decide)

-- `Iris.Std.LawfulPartialMap.all_map` idx 8: necessary (P=False, m=const (some ()))
theorem p4_28 : ¬ drop0% Iris.Std.LawfulPartialMap.all_map 8 := fun h => by
  have := @h Unit Unit (fun V => Unit → Option V) _ Unit (fun _ _ => False) id (fun _ => some ())
  exact this () () (by simp [Iris.Std.get?, Iris.Std.PartialMap.map, Iris.Std.bindAlter])
end

section
open Iris Iris.BI Iris.ProofMode Iris.Instances.Data

abbrev HP := Iris.Instances.Classical.HeapProp Unit
def s1 : State Unit := fun _ => result ()
theorem s1_ne : s1 ≠ ∅ := fun h => by have h0 := congrFun h 0; cases h0
theorem heap_not_affine : ¬ ((iprop(True) : HP) ⊢ emp) := fun h => s1_ne (h s1 trivial)

-- `Iris.ProofMode.quickAffine_biAffine` idx 3: necessary (HeapProp (non-affine): True is not affine)
theorem p4_29 : ¬ drop0% Iris.ProofMode.quickAffine_biAffine 3 := fun h =>
  s1_ne ((@h HP _ iprop(True)).quick_affine.affine s1 trivial)

-- `Iris.ProofMode.makeOr_emp_right` idx 3: necessary (HeapProp: True or emp is not emp)
theorem p4_30 : ¬ drop0% Iris.ProofMode.makeOr_emp_right 3 := fun h =>
  s1_ne ((@h HP _ iprop(True)).make_or.mp s1 (Or.inl trivial))

-- `Iris.ProofMode.intoAnd_and_affine_right` idx 5: necessary (HeapProp: P=Q=True, P'=<affine>True)
theorem p4_31 : ¬ drop0% Iris.ProofMode.intoAnd_and_affine_right 5 := fun h =>
  s1_ne ((@h HP _ iprop(True) iprop(<affine> True) iprop(True) ⟨fun _ h => h⟩).into_and s1 ⟨trivial, trivial⟩).1.1

-- `Iris.ProofMode.specialize_dup_context` idx 11: necessary (HeapProp: A=True non-affine, pa=false, P=emp, B=emp, B'=True)
theorem p4_32 : ¬ drop0% Iris.ProofMode.specialize_dup_context 11 := fun h =>
  heap_not_affine (emp_sep.2.trans ((@h HP _ iprop(emp) false iprop(True) iprop(emp ∗ True) false iprop(emp)
    iprop(True) ⟨fun _ _ => trivial⟩ sep_emp.2).trans ((sep_mono_right intuitionistically_elim_emp).trans emp_sep.1)))

theorem absorb_aux (a b : State Unit) (h : b 0 ≠ unknown) : (a ∪ b) 0 ≠ unknown := by
  simp only [Union.union]; split <;> simp_all

def P1 : HP := fun σ => σ 0 ≠ unknown

-- `Iris.ProofMode.frame_impl` idx 6: necessary (HeapProp: P1 = location 0 allocated (absorbing, not persistent), R=True, P2=Q2=False)
theorem p4_33 : ¬ drop0% Iris.ProofMode.frame_impl 6 := fun h =>
  (@h HP _ iprop(True) P1 iprop(False) iprop(False)
    ⟨⟨fun _ ⟨σ1, σ2, he, _, _, h2⟩ => he ▸ absorb_aux σ1 σ2 h2⟩⟩
    ⟨⟨fun _ ⟨_, _, _, _, _, hf⟩ => hf⟩⟩).frame s1
    ⟨s1, ∅, union_comm.trans empty_union.symm |>.symm, disjoint_comm.1 empty_disjoint, trivial,
      fun hp => hp rfl⟩ (fun h => by cases h)

-- `Iris.ProofMode.fromPure_monPred_at` idx 8: necessary (MonPred over SiProp: P=embed False, phi=True)
theorem p4_34 : ¬ drop0% Iris.ProofMode.fromPure_monPred_at 8 := fun h =>
  (@h UIdx SiProp _ false (MonPred.embed iprop(False)) .in True (0 : Nat)).from_pure 0 trivial

-- `Iris.ProofMode.makeMonPredAt_and` idx 9: necessary (MonPred: P=Q=embed True, Q-at=False)
theorem p4_35 : ¬ drop0% Iris.ProofMode.makeMonPredAt_and 9 := fun h =>
  ((@h UIdx SiProp _ (0 : Nat) (MonPred.embed iprop(True)) (MonPred.embed iprop(True)) iprop(True) iprop(False)
    ⟨⟨fun _ h => h, fun _ h => h⟩⟩).make_monPred_at.mp 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoWand_monPred_at_known_unknown_ge` idx 12: necessary (MonPred: R=P=embed True, Q=embed False)
theorem p4_36 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_known_unknown_ge 12 := fun h =>
  (@h UIdx SiProp _ false false (MonPred.embed iprop(True)) (MonPred.embed iprop(True)) (MonPred.embed iprop(False))
    iprop(False) (0 : Nat) (0 : Nat) ⟨Nat.le_refl 0⟩ ⟨⟨fun _ h => h, fun _ h => h⟩⟩).into_wand 0 trivial 0
    (Nat.le_refl 0) trivial

/-- Identity basic update modality on SiProp (a lawful BIUpdate). -/
instance idBupd : BIUpdate SiProp where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h

-- `Iris.ProofMode.intoWand_bupd` idx 9: necessary (SiProp with identity bupd (lawful BIUpdate): R=P=True, Q=False)
theorem p4_37 : ¬ drop0% Iris.ProofMode.intoWand_bupd 9 := fun h =>
  (@h SiProp _ idBupd false false (.matching .argument) iprop(True) iprop(True) iprop(False)).into_wand 0 trivial 0
    (Nat.le_refl 0) trivial

-- `Iris.ProofMode.elimModal_at_bupd_hyp` idx 15: necessary (identity bupd, MonPred: P=embed True, Q=False)
theorem p4_38 : ¬ drop0% Iris.ProofMode.elimModal_at_bupd_hyp 15 := fun h =>
  (@h UIdx SiProp _ idBupd True false .in false (MonPred.embed iprop(True)) iprop(True) iprop(True) iprop(False)
    iprop(True) (0 : Nat) ⟨⟨fun _ h => h, fun _ h => h⟩⟩).elim_modal trivial 0 ⟨trivial, fun _ _ h => h⟩

def mp1 : MonPred UIdx SiProp := ⟨fun k => iprop(⌜(1 : Nat) ≤ k⌝), fun hij _ h => Nat.le_trans h hij⟩

-- `_private.Iris.ProofMode.MonPred.0.Iris.ProofMode.intoWand_monPred_at_core` idx 12: necessary (MonPred over SiProp, Nat index: R=Q=(1<=k), P=True, i=1, j=0)
theorem p4_39 : ¬ drop0% _private.Iris.ProofMode.MonPred.«0».Iris.ProofMode.intoWand_monPred_at_core 12 := fun h =>
  (@h UIdx SiProp _ false false mp1 (MonPred.embed iprop(True)) mp1 iprop(True) iprop(False) (1 : Nat) (0 : Nat)
    (fun i _ hr => SiProp.forall_holds.2 fun k _ _ hik _ _ _ => Nat.le_trans hr hik)
    (fun _ h => h) (fun _ h => Nat.not_succ_le_zero 0 h)) 0 (Nat.le_refl 1) 0 (Nat.le_refl 0) trivial
end

section
open Iris Iris.ProgramLogic

def bLang : Language Bool Unit Unit Unit where
  primStep := fun c _ r => c.1 = false ∧ r.1 = false
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by intro e σ obs e' σ' eₜ h; simp_all

def bCtx : @Language.Context Bool Unit Unit Unit bLang (fun _ => false) := by
  refine @Language.Context.mk Bool Unit Unit Unit bLang (fun _ => false) ?_ ?_ ?_
  · intro e _; rfl
  · intro e σ obs e' σ' eₜ h; exact ⟨rfl, rfl⟩
  · intro e σ obs Ke σ' eₜ he h
    cases e
    · exact ⟨false, h.2, ⟨rfl, rfl⟩⟩
    · cases he

-- `Iris.ProgramLogic.Language.Context.reducible_fill_inv` idx 9: necessary (Bool language, only false steps; K=const false, e=true value)
theorem p4_40 : ¬ drop0% Iris.ProgramLogic.Language.Context.reducible_fill_inv 9 := fun h =>
  match @h Bool Unit Unit Unit bLang (fun _ => false) bCtx true () ⟨[], false, (), [], rfl, rfl⟩ with
  | ⟨_, _, _, _, hs⟩ => Bool.noConfusion hs.1

-- `Iris.ProgramLogic.Language.Context.stuck_fill` idx 9: necessary (Bool language, K=id, e=true (a value, not stuck))
theorem p4_41 : ¬ drop0% Iris.ProgramLogic.Language.Context.stuck_fill 9 := fun h => by
  have := (@h Bool Unit Unit Unit bLang true () id (@Language.instContext_id Bool Unit Unit Unit bLang)).1
  cases this

def nLang : Language Bool Unit Unit Unit where
  primStep := fun _ _ _ => False
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by intro e σ obs e' σ' eₜ h; exact h.elim

theorem nLang_nsteps {n ρ₁ κ ρ₂} (hs : Language.NSteps (Λ := nLang) n ρ₁ κ ρ₂) (hn : n ≠ 0) : False := by
  cases hs with
  | refl => exact hn rfl
  | cons s _ => cases s with | atomic H => exact H

-- `Iris.ProgramLogic.nSteps_one` idx 8: necessary (Bool language with no steps: NSteps 1 impossible)
theorem p4_42 : ¬ drop0% Iris.ProgramLogic.nSteps_one 8 := fun h =>
  nLang_nsteps (@h Bool Unit Unit Unit nLang ([], ()) ([], ()) []) (by decide)

def fillN (k : Bool) (e : Nat) : Nat := if k then (if e = 1 then 1 else 2 * e) else 2 * e + 1
def toValN (e : Nat) : Option Unit := if e = 0 then some () else none

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

-- `Iris.ProgramLogic.EctxItemLanguage.fillItem_no_val_inj` idx 11: necessary (Nat ectx-item language: fill false e=2e+1, fill true (1->1, e->2e); e1=1, e2=0 (value))
theorem p4_43 : ¬ drop0% Iris.ProgramLogic.EctxItemLanguage.fillItem_no_val_inj 11 := fun h =>
  Bool.noConfusion (@h Nat Bool Unit Unit Unit iLang 1 0 true false rfl (by decide))
end

section
open Iris Iris.Std

/-- Finite sets of Bool as characteristic functions; toList lists false before true. -/
def BS := Bool → Bool

instance : Iris.Std.Set BS Bool where
  mem X x := X x = true
  singleton y := fun x => x == y
  union X Y := fun x => or (X x) (Y x)
  inter X Y := fun x => and (X x) (Y x)
  sdiff X Y := fun x => and (X x) (not (Y x))
  emptyCollection := fun _ => false

def bsList (X : BS) : List Bool := (if X false then [false] else []) ++ (if X true then [true] else [])

instance bsLFS : LawfulFiniteSet BS Bool where
  ext {X Y} h := funext fun x => by
    have := h x; cases hx : X x <;> cases hy : Y x <;> simp_all [Membership.mem]
  mem_empty := by intro x h; cases h
  mem_singleton := by intro x y; show (x == y) = true ↔ x = y; simp
  mem_union := by intro X Y x; show (or (X x) (Y x)) = true ↔ X x = true ∨ Y x = true; simp
  mem_inter := by intro X Y x; show (and (X x) (Y x)) = true ↔ X x = true ∧ Y x = true; simp
  mem_diff := by intro X Y x; show (and (X x) (not (Y x))) = true ↔ X x = true ∧ ¬ Y x = true; simp
  toList := bsList
  mem_toList := by
    intro m k; show k ∈ bsList m ↔ m k = true
    cases hf : m false <;> cases ht : m true <;> cases k <;> simp [bsList, hf, ht]
  toList_nodup := by
    intro m; cases hf : m false <;> cases ht : m true <;> simp [bsList, hf, ht]

-- `Iris.Std.FiniteSet.fold_insert` idx 5: necessary (Bool sets as Bool->Bool, toList lists false first; f b x := x, a=false, s={true})
theorem p4_44 : ¬ drop0% Iris.Std.FiniteSet.fold_insert 5 := fun h => by
  have := @h BS Bool bsLFS Bool (fun _ x => x) false false (fun x => x == true) (by intro hm; cases hm)
  revert this; decide
end

section
open Iris Iris.BI Iris.ProofMode


-- `Iris.ProofMode.frame_eq_embed` idx 14: necessary (embed SiProp into MonPred, A=Unit, a=b=(), Q=True, P=False)
theorem p4_45 : ¬ drop0% Iris.ProofMode.frame_eq_embed 14 := fun h => by
  have c := (@h SiProp (MonPred UIdx SiProp) _ _ _ _ false Unit _ () () iprop(False) iprop(True)
    (Iris.BI.Embed.embed iprop(True)) ⟨⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩⟩).frame
  have d : (Iris.BI.Embed.embed iprop(True) : MonPred UIdx SiProp) ⊢ Iris.BI.Embed.embed iprop(False) :=
    emp_sep.2.trans ((sep_mono_left internalEq.refl).trans c)
  exact d (0 : Nat) 0 trivial
end

section
open Iris Iris.BI Iris.ProofMode

/-- Bool with the discrete order (no bottom element). -/
def DB := Bool
instance : LE DB := ⟨fun a b => a = b⟩
instance : Inhabited DB := ⟨(true : Bool)⟩
instance : Std.IsPreorder DB where
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2

abbrev DIdx : BiIndex := { car := DB, rel := inferInstance }

def phiD (a : Bool) : MonPred DIdx SiProp := ⟨fun i => iprop(⌜(i : Bool) = a⌝), fun hij _ h => hij ▸ h⟩

-- `Iris.ProofMode.intoExists_plainly` idx 2: necessary (MonPred SiProp over Bool with discrete order (no bottom): P=True, Phi a i := (i = a))
theorem p4_46 : ¬ drop0% Iris.ProofMode.intoExists_plainly 2 := fun h => by
  have c := (@h (MonPred DIdx SiProp) _ (MonPred.embed iprop(True)) Bool phiD
    ⟨fun i n _ => (MonPred.monPred_at_exist i phiD).mpr n (SiProp.exists_holds.2 ⟨(i : Bool), rfl⟩)⟩).into_exists
  have hp := (MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) (show DIdx.car from true)
    (MonPred.embed iprop(True))).mpr 0 (SiProp.forall_holds.2 fun _ => trivial)
  have d := (MonPred.monPred_at_exist (I := DIdx) (PROP := SiProp) (show DIdx.car from true)
    (fun a => iprop(■ phiD a))).mp 0 (c (show DIdx.car from true) 0 hp)
  obtain ⟨a, ha⟩ := SiProp.exists_holds.1 d
  have e := SiProp.forall_holds.1 ((MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp)
    (show DIdx.car from true) (phiD a)).mp 0 ha)
  have e1 : (true : Bool) = a := e (show DIdx.car from true)
  have e2 : (false : Bool) = a := e (show DIdx.car from false)
  exact Bool.noConfusion (e1.trans e2.symm)
end

end Probe4
