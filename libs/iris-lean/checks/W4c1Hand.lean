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
namespace W4c1
open Iris Iris.BI Iris.Std Iris.Instances.Classical Iris.Instances.Data

abbrev HP := HeapProp Unit
def s1 : State Unit := fun _ => result ()
theorem s1_ne : s1 ≠ ∅ := fun h => by have h0 := congrFun h 0; cases h0
theorem heap_not_affine : ¬ ((iprop(True) : HP) ⊢ emp) := fun h => s1_ne (h s1 trivial)
theorem true_not_affine : ¬ Affine (iprop(True) : HP) := fun ⟨h⟩ => heap_not_affine h
def h0 : State Unit := fun i => if i = 0 then result () else unknown
def own0 : HP := fun σ => σ 0 ≠ unknown
theorem own0_not_pers : ¬ Persistent own0 := fun ⟨h⟩ => h h0 (by show h0 0 ≠ unknown; simp [h0]) rfl
theorem msSing {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : ([∗mset] x ∈ ({0} : ListPerm Nat), Φ x) ⊣⊢ Φ 0 :=
  BigSepMS.bigSepMS_singleton (MS := ListPerm Nat)
theorem si_nf : ¬ ((iprop(True) : SiProp) ⊢ iprop(False)) := fun h => h 0 trivial
theorem si_ef : ¬ ((emp : SiProp) ⊢ iprop(False)) := fun h => h 0 trivial
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩
theorem s0_not_timeless : ¬ Timeless s0 := fun ⟨h⟩ => by
  have := h 1 rfl
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 (by simp [s0])
abbrev MSN := ListPerm Nat
theorem msSing1 {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : ([∗mset] x ∈ ({1} : ListPerm Nat), Φ x) ⊣⊢ Φ 1 :=
  BigSepMS.bigSepMS_singleton (MS := ListPerm Nat)
end W4c1
open Iris Iris.BI Iris.Std Iris.Instances.Classical Iris.Instances.Data W4c1

-- `Iris.BI.BigSepL.bigSepL_nil_intro` idx 4: necessary (HeapProp Unit: P=True not affine; True |- emp fails)
theorem w4c1_1 : ¬ drop0% Iris.BI.BigSepL.bigSepL_nil_intro 4 := fun h =>
  heap_not_affine ((@h HP _ Unit iprop(True) (fun _ _ => iprop(True))).trans BigSepL.bigSepL_nil.1)

-- `Iris.BI.BigSepL.bigSepL_mono` idx 6: necessary (SiProp: l=[()], Phi=True, Psi=False)
theorem w4c1_2 : ¬ drop0% Iris.BI.BigSepL.bigSepL_mono 6 := fun h =>
  si_nf (BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]).trans BigSepL.bigSepL_singleton.1))

-- `Iris.BI.BigSepL.bigSepL_eq` idx 6: necessary (SiProp: l=[()], Phi=True, Psi=False)
theorem w4c1_3 : ¬ drop0% Iris.BI.BigSepL.bigSepL_eq 6 := fun h =>
  si_nf (BigSepL.bigSepL_singleton.2.trans ((BiEntails.of_eq (@h SiProp _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()])).1.trans BigSepL.bigSepL_singleton.1))

-- `Iris.BI.BigSepL.bigSepL_dist` idx 7: necessary (HeapProp Unit (n-distance is equality): l=[()], Phi=True, Psi=False)
theorem w4c1_4 : ¬ drop0% Iris.BI.BigSepL.bigSepL_dist 7 := fun h => by
  have e : _ = _ := @h HP _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()] 0
  have := (BigSepL.bigSepL_singleton.2.trans ((BiEntails.of_eq e).1.trans BigSepL.bigSepL_singleton.1)) (∅ : State Unit) trivial
  exact this

-- `Iris.BI.BigSepL.bigSepL_persistent` idx 5: necessary (HeapProp Unit: l=[()], Phi=own0 (owns cell 0) not persistent)
theorem w4c1_5 : ¬ drop0% Iris.BI.BigSepL.bigSepL_persistent 5 := fun h =>
  own0_not_pers ⟨BigSepL.bigSepL_singleton.2.trans ((@h HP _ Unit (fun _ _ => own0) [()]).persistent.trans (persistently_mono BigSepL.bigSepL_singleton.1))⟩

-- `Iris.BI.BigSepL.bigSepL_timeless` idx 6: necessary (SiProp: l=[()], Phi=s0 (true only at step 0) not timeless)
theorem w4c1_6 : ¬ drop0% Iris.BI.BigSepL.bigSepL_timeless 6 := fun h =>
  s0_not_timeless ⟨(later_mono BigSepL.bigSepL_singleton.2).trans ((@h SiProp _ Unit _ (fun _ _ => s0) [()]).timeless.trans (except0_mono BigSepL.bigSepL_singleton.1))⟩

-- `Iris.BI.BigSepL.bigSepL_lookup` idx 7: necessary (SiProp: l=[true], i=0, x=false, Phi k y = (y = true))
theorem w4c1_7 : ¬ drop0% Iris.BI.BigSepL.bigSepL_lookup 7 := fun h =>
  Bool.false_ne_true ((BigSepL.bigSepL_singleton.2.trans (@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [true] 0 false (TCOr.l))) 0 rfl)

namespace W4c1
open Iris Iris.BI Iris.Std Iris.Instances.Classical Iris.Instances.Data
/-- Two-element resource algebra with equality order (non-affine UPred, later emp is not emp at step 0). -/
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
/-- In UPred B2, later emp does not entail emp (step 0, resource i). -/
theorem b2_later_emp (h : (iprop(▷ emp) : UPred B2) ⊢ emp) : False := by
  have : (iprop(▷ emp) : UPred B2).holds 0 ⟨.i, trivial⟩ := by
    show (UPred.later _).holds 0 _
    trivial
  exact absurd (h 0 ⟨.i, trivial⟩ this) (fun h' => nomatch (h' : B2.o = B2.i))
open ORA in
/-- UPred Credit (affine, core 0): ownM 1 does not entail ownM 2. -/
theorem cm_bad (h : (UPred.ownM (1 : Credit)) ⊢ UPred.ownM (2 : Credit)) : False := by
  have := h 0 ⟨1, (OFE.Dist.validN rfl).mp trivial⟩ (ordN_refl _)
  simp [UPred.ownM] at this
  obtain ⟨z, hz⟩ := this
  have hz' : (1 : Nat) = 2 + z := hz
  omega
/-- zip and set commute without length side conditions. -/
theorem zipSet {C D : Type _} : ∀ (l1 : List C) (l2 : List D) (i : Nat) (y1 : C) (y2 : D),
    (l1.zip l2).set i (y1, y2) = (l1.set i y1).zip (l2.set i y2)
  | [], _, _, _, _ => by simp
  | _::_, [], _, _, _ => by simp
  | _::_, _::_, 0, _, _ => by simp
  | _::xs, _::ys, i+1, y1, y2 => by simp [zipSet xs ys i y1 y2]
/-- bigSepL2_sep_sepL_left without BIAffine. -/
theorem sepLLeft {PROP : Type _} [BI PROP] {A B : Type _} : ∀ (Φ : Nat → A → PROP) (Ψ : Nat → A → B → PROP) (l1 : List A) (l2 : List B),
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 ∗ Ψ k x1 x2) ⊣⊢
      ([∗list] k ↦ x ∈ l1, Φ k x) ∗ [∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2
  | _, _, [], [] => ⟨emp_sep.2, emp_sep.1⟩
  | Φ, Ψ, _::xs, _::ys => (sep_congr_right (sepLLeft (fun n => Φ (n+1)) (fun n => Ψ (n+1)) xs ys)).trans sep_sep_sep_comm
  | _, _, [], _::_ => ⟨emp_sep.2, emp_sep.1⟩
  | _, _, _::_, [] => ⟨sep_false.2, sep_false.1⟩
end W4c1

-- `Iris.BI.BigSepL.bigSepL_mono_of_forall` idx 6: necessary (SiProp: l=[()], Phi=True, Psi=False)
theorem w4c1_9 : ¬ drop0% Iris.BI.BigSepL.bigSepL_mono_of_forall 6 := fun h =>
  si_nf (BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ Unit (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) [()]).trans BigSepL.bigSepL_singleton.1))

-- `Iris.BI.BigSepL.bigSepL_flip_mono` idx 6: necessary (SiProp: l=[()], Psi=True, Phi=False)
theorem w4c1_10 : ¬ drop0% Iris.BI.BigSepL.bigSepL_flip_mono 6 := fun h =>
  si_nf (BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ Unit (fun _ _ => iprop(False)) (fun _ _ => iprop(True)) [()]).trans BigSepL.bigSepL_singleton.1))

-- `Iris.BI.BigSepL.bigSepL_id_mono` idx 4: necessary (SiProp: Ps=[], Qs=[False]; emp |- False fails)
theorem w4c1_11 : ¬ drop0% Iris.BI.BigSepL.bigSepL_id_mono 4 := fun h =>
  si_ef ((@h SiProp _ [] [iprop(False)] (fun i P Q h1 _ => by simp at h1)).trans BigSepL.bigSepL_singleton.1)

-- `Iris.BI.BigSepL.bigSepL_id_mono` idx 5: necessary (SiProp: Ps=[True], Qs=[False])
theorem w4c1_12 : ¬ drop0% Iris.BI.BigSepL.bigSepL_id_mono 5 := fun h =>
  si_nf (BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ [iprop(True)] [iprop(False)] rfl).trans BigSepL.bigSepL_singleton.1))

-- `Iris.BI.BigSepL.bigSepL_persistent_id` idx 3: necessary (HeapProp Unit: Ps=[own0], own0 not persistent)
theorem w4c1_13 : ¬ drop0% Iris.BI.BigSepL.bigSepL_persistent_id 3 := fun h =>
  own0_not_pers ⟨BigSepL.bigSepL_singleton.2.trans ((@h HP _ [own0]).persistent.trans (persistently_mono BigSepL.bigSepL_singleton.1))⟩

-- `Iris.BI.BigSepL.bigSepL_persistent_inst` idx 5: necessary (HeapProp Unit: l=[()], Phi=own0 not persistent)
theorem w4c1_14 : ¬ drop0% Iris.BI.BigSepL.bigSepL_persistent_inst 5 := fun h =>
  own0_not_pers ⟨BigSepL.bigSepL_singleton.2.trans ((@h HP _ Unit (fun _ _ => own0) [()]).persistent.trans (persistently_mono BigSepL.bigSepL_singleton.1))⟩

-- `Iris.BI.BigSepL.bigSepL_affine_id` idx 3: necessary (HeapProp Unit: Ps=[True], True not affine)
theorem w4c1_15 : ¬ drop0% Iris.BI.BigSepL.bigSepL_affine_id 3 := fun h =>
  true_not_affine ⟨BigSepL.bigSepL_singleton.2.trans (@h HP _ [iprop(True)]).affine⟩

-- `Iris.BI.BigSepL.bigSepL_affine` idx 5: necessary (HeapProp Unit: l=[()], Phi=True not affine)
theorem w4c1_16 : ¬ drop0% Iris.BI.BigSepL.bigSepL_affine 5 := fun h =>
  true_not_affine ⟨BigSepL.bigSepL_singleton.2.trans (@h HP _ Unit (fun _ _ => iprop(True)) [()]).affine⟩

-- `Iris.BI.BigSepL.bigSepL_affine_inst` idx 5: necessary (HeapProp Unit: l=[()], Phi=True not affine)
theorem w4c1_17 : ¬ drop0% Iris.BI.BigSepL.bigSepL_affine_inst 5 := fun h =>
  true_not_affine ⟨BigSepL.bigSepL_singleton.2.trans (@h HP _ Unit (fun _ _ => iprop(True)) [()]).affine⟩

-- `Iris.BI.BigSepL.bigSepL_timeless_inst` idx 6: necessary (SiProp: l=[()], Phi=s0 (true only at step 0) not timeless)
theorem w4c1_18 : ¬ drop0% Iris.BI.BigSepL.bigSepL_timeless_inst 6 := fun h =>
  s0_not_timeless ⟨(later_mono BigSepL.bigSepL_singleton.2).trans ((@h SiProp _ Unit _ (fun _ _ => s0) [()]).timeless.trans (except0_mono BigSepL.bigSepL_singleton.1))⟩

-- `Iris.BI.BigSepL.bigSepL_pure` idx 3: necessary (HeapProp Unit (not affine): l=[], True |- emp fails)
theorem w4c1_19 : ¬ drop0% Iris.BI.BigSepL.bigSepL_pure 3 := fun h =>
  heap_not_affine ((pure_intro (fun _ _ h => by simp at h)).trans (@h HP _ Unit (fun _ _ => True) []).2)

-- `Iris.BI.BigSepL.bigSepL_lookup_acc` idx 7: necessary (SiProp: l=[true], i=0, x=false, Phi k y = (y = true))
theorem w4c1_20 : ¬ drop0% Iris.BI.BigSepL.bigSepL_lookup_acc 7 := fun h =>
  Bool.false_ne_true ((BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [true] 0 false).1.trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL.bigSepL_insert_acc` idx 7: necessary (SiProp: l=[true], i=0, x=false, Phi k y = (y = true))
theorem w4c1_21 : ¬ drop0% Iris.BI.BigSepL.bigSepL_insert_acc 7 := fun h =>
  Bool.false_ne_true ((BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [true] 0 false).trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL.bigSepL_mem_acc` idx 6: necessary (SiProp: l=[true], x=false, Phi y = (y = true))
theorem w4c1_22 : ¬ drop0% Iris.BI.BigSepL.bigSepL_mem_acc 6 := fun h =>
  Bool.false_ne_true ((BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ Bool (fun y => iprop(⌜y = true⌝)) [true] false).trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL.bigSepL_mem` idx 6: necessary (SiProp: l=[true], x=false, Phi y = (y = true))
theorem w4c1_23 : ¬ drop0% Iris.BI.BigSepL.bigSepL_mem 6 := fun h =>
  Bool.false_ne_true ((BigSepL.bigSepL_singleton.2.trans (@h SiProp _ Bool (fun y => iprop(⌜y = true⌝)) [true] false TCOr.l)) 0 rfl)

-- `Iris.BI.BigSepL.bigSepL_delete_cond` idx 7: necessary (SiProp: l=[true], i=0, x=false, Phi k y = (y = true))
theorem w4c1_24 : ¬ drop0% Iris.BI.BigSepL.bigSepL_delete_cond 7 := fun h =>
  Bool.false_ne_true ((BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [true] 0 false).1.trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL.bigSepL_delete` idx 3: necessary (HeapProp Unit: l=[()], i=0, Phi=emp; emp vs emp * (False -> emp), the latter is True)
theorem w4c1_25 : ¬ drop0% Iris.BI.BigSepL.bigSepL_delete 3 := fun h =>
  heap_not_affine ((emp_sep.2.trans (sep_mono_right ((BI.imp_intro (and_elim_r.trans (pure_elim' fun h => absurd rfl h))).trans (BigSepL.bigSepL_singleton (PROP := HP) (Φ := fun k _ => iprop(⌜k ≠ 0⌝ → emp)) (x := ())).2))).trans
    ((@h HP _ Unit (fun _ _ => emp) [()] 0 () rfl).2.trans BigSepL.bigSepL_singleton.1))

-- `Iris.BI.BigSepL.bigSepL_delete` idx 8: necessary (SiProp: l=[true], i=0, x=false, Phi k y = (y = true))
theorem w4c1_26 : ¬ drop0% Iris.BI.BigSepL.bigSepL_delete 8 := fun h =>
  Bool.false_ne_true ((BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ Bool _ (fun _ y => iprop(⌜y = true⌝)) [true] 0 false).1.trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL.bigSepL_intro` idx 6: necessary (HeapProp Unit: P=True (not intuitionistic), l=[])
theorem w4c1_27 : ¬ drop0% Iris.BI.BigSepL.bigSepL_intro 6 := fun h =>
  heap_not_affine (@h HP _ Unit iprop(True) (fun _ _ => iprop(True)) [] (fun k x h => by simp at h))

-- `Iris.BI.BigSepL.bigSepL_intro` idx 7: necessary (SiProp: P=emp, l=[()], Phi=False)
theorem w4c1_28 : ¬ drop0% Iris.BI.BigSepL.bigSepL_intro 7 := fun h =>
  si_ef ((@h SiProp _ Unit emp (fun _ _ => iprop(False)) [()] _).trans BigSepL.bigSepL_singleton.1)

-- `Iris.BI.BigSepL.bigSepL_forall_elim` idx 5: necessary (HeapProp Unit: l=[], Phi=True; True |- emp fails)
theorem w4c1_29 : ¬ drop0% Iris.BI.BigSepL.bigSepL_forall_elim 5 := fun h =>
  heap_not_affine ((forall_intro fun _ => forall_intro fun _ => BI.imp_intro (and_elim_r.trans (pure_elim' fun h => by simp at h))).trans
    (@h HP _ Unit (fun _ _ => iprop(True)) [] _))

-- `Iris.BI.BigSepL.bigSepL_forall_eqv` idx 5: necessary (HeapProp Unit: l=[], Phi=True; True |- emp fails)
theorem w4c1_30 : ¬ drop0% Iris.BI.BigSepL.bigSepL_forall_eqv 5 := fun h =>
  heap_not_affine ((forall_intro fun _ => forall_intro fun _ => BI.imp_intro (and_elim_r.trans (pure_elim' fun h => by simp at h))).trans
    (@h HP _ Unit (fun _ _ => iprop(True)) [] _).2)

-- `Iris.BI.BigSepL.bigSepL_lookup_acc_impl` idx 7: necessary (SiProp: l=[true], i=0, x=false, Phi k y = (y = true))
theorem w4c1_31 : ¬ drop0% Iris.BI.BigSepL.bigSepL_lookup_acc_impl 7 := fun h =>
  Bool.false_ne_true ((BigSepL.bigSepL_singleton.2.trans ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [true] 0 false).trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL.bigSepL_persistently` idx 5: necessary (HeapProp Unit: l=[]; <pers> emp = True, not |- emp)
theorem w4c1_32 : ¬ drop0% Iris.BI.BigSepL.bigSepL_persistently 5 := fun h =>
  heap_not_affine ((show (iprop(True) : HP) ⊢ <pers> emp from fun _ _ => rfl).trans (@h HP _ Unit (fun _ _ => emp) []).1)

-- `Iris.BI.BigSepL.bigSepL_perm` idx 6: necessary (SiProp: l1=[()], l2=[], Phi=False)
theorem w4c1_33 : ¬ drop0% Iris.BI.BigSepL.bigSepL_perm 6 := fun h =>
  si_ef ((@h SiProp _ Unit (fun _ => iprop(False)) [()] []).2.trans BigSepL.bigSepL_singleton.1)

-- `Iris.BI.BigSepL.bigSepL_submseteq` idx 4: necessary (HeapProp Unit: Phi=True not affine, l1=[], l=l2=[()])
theorem w4c1_34 : ¬ drop0% Iris.BI.BigSepL.bigSepL_submseteq 4 := fun h =>
  heap_not_affine (BigSepL.bigSepL_singleton.2.trans (@h HP _ Unit (fun _ => iprop(True)) [] [()] [()] (List.Perm.refl _)))

-- `Iris.BI.BigSepL.bigSepL_submseteq` idx 8: necessary (SiProp: Phi=False, l1=[()], l=l2=[])
theorem w4c1_35 : ¬ drop0% Iris.BI.BigSepL.bigSepL_submseteq 8 := fun h =>
  si_ef ((@h SiProp _ Unit (fun _ => iprop(False)) _ [()] [] []).trans BigSepL.bigSepL_singleton.1)

-- `Iris.BI.BigSepL.bigSepL_sep_zip` idx 8: necessary (SiProp: l1=[()], l2=[], Phi=False; zip is empty)
theorem w4c1_36 : ¬ drop0% Iris.BI.BigSepL.bigSepL_sep_zip 8 := fun h =>
  si_ef ((@h SiProp _ Unit Unit (fun _ _ => iprop(False)) (fun _ _ => iprop(True)) [()] []).1.trans (sep_elim_left.trans BigSepL.bigSepL_singleton.1))

-- `Iris.BI.BigSepL.bigSepL_sep_zip_with` idx 12: necessary (SiProp: A=Bool, l1=[true], l2=[()], g1 constantly false, Phi i x = (x = true))
theorem w4c1_37 : ¬ drop0% Iris.BI.BigSepL.bigSepL_sep_zip_with 12 := fun h =>
  Bool.false_ne_true ((((emp_sep (P := (emp : SiProp))).2.trans (sep_mono ((pure_intro rfl).trans (BigSepL.bigSepL_singleton (Φ := fun _ x => iprop(⌜x = true⌝)) (x := true)).2) ((pure_intro trivial).trans (BigSepL.bigSepL_singleton (Φ := fun _ _ => iprop(True)) (x := ())).2))).trans
    ((@h SiProp _ Bool Unit Unit (fun _ _ => ()) (fun _ => false) (fun _ => ()) (fun _ x => iprop(⌜x = true⌝)) (fun _ _ => iprop(True)) [true] [()]
      (fun _ _ => rfl) rfl).2.trans (BigSepL.bigSepL_singleton.1.trans sep_elim_left))) 0 trivial)

-- `Iris.BI.BigSepL.bigSepL_sep_zip_with` idx 13: necessary (SiProp: B=Bool, l1=[()], l2=[true], g2 constantly false, Psi i y = (y = true))
theorem w4c1_38 : ¬ drop0% Iris.BI.BigSepL.bigSepL_sep_zip_with 13 := fun h =>
  Bool.false_ne_true ((((emp_sep (P := (emp : SiProp))).2.trans (sep_mono ((pure_intro trivial).trans (BigSepL.bigSepL_singleton (Φ := fun _ _ => iprop(True)) (x := ())).2) ((pure_intro rfl).trans (BigSepL.bigSepL_singleton (Φ := fun _ x => iprop(⌜x = true⌝)) (x := true)).2))).trans
    ((@h SiProp _ Unit Bool Unit (fun _ _ => ()) (fun _ => ()) (fun _ => false) (fun _ _ => iprop(True)) (fun _ y => iprop(⌜y = true⌝)) [()] [true]
      (fun _ _ => rfl) rfl).2.trans (BigSepL.bigSepL_singleton.1.trans sep_elim_right))) 0 trivial)

-- `Iris.BI.BigSepL.bigSepL_sep_zip_with` idx 14: necessary (SiProp: f=Prod.mk, l1=[()], l2=[], Phi=False)
theorem w4c1_39 : ¬ drop0% Iris.BI.BigSepL.bigSepL_sep_zip_with 14 := fun h =>
  si_ef ((@h SiProp _ Unit Unit (Unit × Unit) Prod.mk Prod.fst Prod.snd (fun _ _ => iprop(False)) (fun _ _ => iprop(True)) [()] []
    (fun _ _ => rfl) (fun _ _ => rfl)).1.trans (sep_elim_left.trans BigSepL.bigSepL_singleton.1))

-- `Iris.BI.BigSepL2.bigSepL2_nil_affine` idx 5: necessary (HeapProp Unit: P=True not affine)
theorem w4c1_40 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_nil_affine 5 := fun h =>
  heap_not_affine (@h HP _ Unit Unit iprop(True) (fun _ _ _ => iprop(True)))

-- `_private.Iris.BI.BigOp.BigSepList.0.Iris.BI.BigSepL2.bigSepL2_alt_bwd` idx 7: necessary (SiProp: l1=[()], l2=[]; zip is empty, bigSepL2 of different lengths is False)
theorem w4c1_41 : ¬ drop0% _private.Iris.BI.BigOp.BigSepList.«0».Iris.BI.BigSepL2.bigSepL2_alt_bwd 7 := fun h =>
  si_ef (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] [])

-- `Iris.BI.BigSepL2.bigSepL2_mono` idx 8: necessary (SiProp: l1=l2=[()], Phi=True, Psi=False)
theorem w4c1_42 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_mono 8 := fun h =>
  si_nf (BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) [()] [()]).trans BigSepL2.bigSepL2_singleton.1))

-- `Iris.BI.BigSepL2.bigSepL2_eqv` idx 8: necessary (SiProp: l1=l2=[()], Phi=True, Psi=False)
theorem w4c1_43 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_eqv 8 := fun h =>
  si_nf (BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) [()] [()]).1.trans BigSepL2.bigSepL2_singleton.1))

-- `Iris.BI.BigSepL2.bigSepL2_eqv_of_forall_eqv` idx 8: necessary (SiProp: l1=l2=[()], Phi=True, Psi=False)
theorem w4c1_44 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_eqv_of_forall_eqv 8 := fun h =>
  si_nf (BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) [()] [()]).1.trans BigSepL2.bigSepL2_singleton.1))

-- `Iris.BI.BigSepL2.bigSepL2_dist` idx 9: necessary (HeapProp Unit (discrete, n-distance is equality): l1=l2=[()], Phi=True, Psi=False)
theorem w4c1_45 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_dist 9 := fun h => by
  have e : _ = _ := @h HP _ Unit Unit (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) [()] [()] 0
  exact (BigSepL2.bigSepL2_singleton.2.trans ((BiEntails.of_eq e).1.trans BigSepL2.bigSepL2_singleton.1)) (∅ : State Unit) trivial

-- `Iris.BI.BigSepL2.bigSepL2_mono_of_forall` idx 8: necessary (SiProp: l1=l2=[()], Phi=True, Psi=False)
theorem w4c1_46 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_mono_of_forall 8 := fun h =>
  si_nf (BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) [()] [()]).trans BigSepL2.bigSepL2_singleton.1))

-- `Iris.BI.BigSepL2.bigSepL2_closed` idx 8: necessary (SiProp: P Q = (Q |- False), l1=l2=[]; conclusion emp |- False)
theorem w4c1_47 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_closed 8 := fun h =>
  si_ef (@h SiProp _ Unit Unit (fun Q => Q ⊢ iprop(False)) (fun _ _ _ => iprop(True)) [] [] .rfl
    (fun h1 _ => sep_elim_left.trans h1) (fun h1 _ => by simp at h1))

-- `Iris.BI.BigSepL2.bigSepL2_closed` idx 9: necessary (SiProp: P Q = (emp |- Q), l1=[()], l2=[]; bigSepL2 is False)
theorem w4c1_48 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_closed 9 := fun h =>
  si_ef (@h SiProp _ Unit Unit (fun Q => emp ⊢ Q) (fun _ _ _ => iprop(True)) [()] [] .rfl
    (fun h1 h2 => emp_sep.2.trans (sep_mono h1 h2)) (fun _ h2 => by simp at h2))

-- `Iris.BI.BigSepL2.bigSepL2_closed` idx 11: necessary (SiProp: P Q = (emp |- Q) or (Q |- False), l1=l2=[()], Phi=s0 (true only at step 0))
theorem w4c1_49 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_closed 11 := fun h => by
  have := @h SiProp _ Unit Unit (fun Q => (emp ⊢ Q) ∨ (Q ⊢ iprop(False))) (fun _ _ _ => s0) [()] [()] (.inl .rfl) (.inr .rfl)
    (fun h1 h2 => by
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact .inl (emp_sep.2.trans (sep_mono h1 h2))
        · exact .inr (sep_elim_right.trans h2)
      · exact .inr (sep_elim_left.trans h1))
  rcases this with h1 | h1
  · exact absurd (((h1.trans sep_emp.1) : (emp : SiProp) ⊢ s0) 1 trivial) (by simp [s0])
  · exact (sep_emp.2.trans h1) 0 rfl

-- `Iris.BI.BigSepL2.bigSepL2_persistent` idx 7: necessary (HeapProp Unit: l1=l2=[()], Phi=own0 not persistent)
theorem w4c1_50 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_persistent 7 := fun h =>
  own0_not_pers ⟨BigSepL2.bigSepL2_singleton.2.trans ((@h HP _ Unit Unit (fun _ _ _ => own0) [()] [()]).persistent.trans (persistently_mono BigSepL2.bigSepL2_singleton.1))⟩

-- `Iris.BI.BigSepL2.bigSepL2_persistent_inst` idx 7: necessary (HeapProp Unit: l1=l2=[()], Phi=own0 not persistent)
theorem w4c1_51 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_persistent_inst 7 := fun h =>
  own0_not_pers ⟨BigSepL2.bigSepL2_singleton.2.trans ((@h HP _ Unit Unit (fun _ _ _ => own0) [()] [()]).persistent.trans (persistently_mono BigSepL2.bigSepL2_singleton.1))⟩

-- `Iris.BI.BigSepL2.bigSepL2_affine` idx 7: necessary (HeapProp Unit: l1=l2=[()], Phi=True not affine)
theorem w4c1_52 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_affine 7 := fun h =>
  true_not_affine ⟨BigSepL2.bigSepL2_singleton.2.trans (@h HP _ Unit Unit (fun _ _ _ => iprop(True)) [()] [()]).affine⟩

-- `Iris.BI.BigSepL2.bigSepL2_affine_inst` idx 7: necessary (HeapProp Unit: l1=l2=[()], Phi=True not affine)
theorem w4c1_53 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_affine_inst 7 := fun h =>
  true_not_affine ⟨BigSepL2.bigSepL2_singleton.2.trans (@h HP _ Unit Unit (fun _ _ _ => iprop(True)) [()] [()]).affine⟩

-- `Iris.BI.BigSepL2.bigSepL2_timeless` idx 8: necessary (SiProp: l1=l2=[()], Phi=s0 not timeless)
theorem w4c1_54 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_timeless 8 := fun h =>
  s0_not_timeless ⟨(later_mono BigSepL2.bigSepL2_singleton.2).trans ((@h SiProp _ Unit Unit _ (fun _ _ _ => s0) [()] [()]).timeless.trans (except0_mono BigSepL2.bigSepL2_singleton.1))⟩

-- `Iris.BI.BigSepL2.bigSepL2_timeless'` idx 8: necessary (SiProp: l1=l2=[()], Phi=s0 not timeless)
theorem w4c1_55 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_timeless' 8 := fun h =>
  s0_not_timeless ⟨(later_mono BigSepL2.bigSepL2_singleton.2).trans ((@h SiProp _ Unit Unit _ (fun _ _ _ => s0) [()] [()]).timeless.trans (except0_mono BigSepL2.bigSepL2_singleton.1))⟩

-- `Iris.BI.BigSepL2.bigSepL2_pure` idx 4: necessary (HeapProp Unit: l1=l2=[]; True |- emp fails)
theorem w4c1_56 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_pure 4 := fun h =>
  heap_not_affine ((pure_intro ⟨rfl, fun _ _ _ h => by simp at h⟩).trans (@h HP _ Unit Unit (fun _ _ _ => True) [] []).2)

-- `_private.Iris.BI.BigOp.BigSepList.0.Iris.BI.BigSepL2.bigSepL2_app_inv_core` idx 9: necessary (SiProp: l1a=[()], l2a=[], l1b=[], l2b=[()], Phi=True)
theorem w4c1_57 : ¬ drop0% _private.Iris.BI.BigOp.BigSepList.«0».Iris.BI.BigSepL2.bigSepL2_app_inv_core 9 := fun h =>
  si_ef (((pure_intro trivial).trans (BigSepL2.bigSepL2_singleton (Φ := fun _ _ _ => iprop(True)) (x := ()) (y := ())).2).trans
    ((@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] [] [] [()]).trans sep_elim_left))

-- `Iris.BI.BigSepL2.bigSepL2_app_same_length` idx 9: necessary (SiProp: l1a=[()], l2a=[], l1b=[], l2b=[()], Phi=True)
theorem w4c1_58 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_app_same_length 9 := fun h =>
  si_ef (((pure_intro trivial).trans (BigSepL2.bigSepL2_singleton (Φ := fun _ _ _ => iprop(True)) (x := ()) (y := ())).2).trans
    ((@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] [] [] [()]).1.trans sep_elim_left))

-- `Iris.BI.BigSepL2.bigSepL2_insert_acc` idx 10: necessary (SiProp: l1=[true], x1=false, l2=[()], i=0, Phi k y1 y2 = (y1 = true))
theorem w4c1_59 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_insert_acc 10 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Bool Unit (fun _ y _ => iprop(⌜y = true⌝)) [true] [()] 0 false () rfl).trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_insert_acc` idx 11: necessary (SiProp: l2=[true], x2=false, l1=[()], i=0, Phi k y1 y2 = (y2 = true))
theorem w4c1_60 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_insert_acc 11 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Bool (fun _ _ y => iprop(⌜y = true⌝)) [()] [true] 0 () false rfl).trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_lookup_acc` idx 10: necessary (SiProp: l1=[true], x1=false, l2=[()], i=0, Phi k y1 y2 = (y1 = true))
theorem w4c1_61 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_lookup_acc 10 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Bool Unit (fun _ y _ => iprop(⌜y = true⌝)) [true] [()] 0 false () rfl).trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_lookup_acc` idx 11: necessary (SiProp: l2=[true], x2=false, l1=[()], i=0, Phi k y1 y2 = (y2 = true))
theorem w4c1_62 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_lookup_acc 11 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Bool (fun _ _ y => iprop(⌜y = true⌝)) [()] [true] 0 () false rfl).trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_lookup` idx 10: necessary (SiProp: l1=[true], x1=false, l2=[()], i=0, Phi k y1 y2 = (y1 = true))
theorem w4c1_63 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_lookup 10 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans (@h SiProp _ Bool Unit (fun _ y _ => iprop(⌜y = true⌝)) [true] [()] 0 false () rfl TCOr.l)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_lookup` idx 11: necessary (SiProp: l2=[true], x2=false, l1=[()], i=0, Phi k y1 y2 = (y2 = true))
theorem w4c1_64 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_lookup 11 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans (@h SiProp _ Unit Bool (fun _ _ y => iprop(⌜y = true⌝)) [()] [true] 0 () false rfl TCOr.l)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_lookup_left` idx 9: necessary (SiProp: l1=[true], x1=false, l2=[()], i=0, Phi k y1 y2 = (y1 = true))
theorem w4c1_65 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_lookup_left 9 := fun h =>
  si_ef (((pure_intro rfl).trans (BigSepL2.bigSepL2_singleton (Φ := fun _ y _ => iprop(⌜y = true⌝)) (x := true) (y := ())).2).trans
    ((@h SiProp _ Bool Unit (fun _ y _ => iprop(⌜y = true⌝)) [true] [()] 0 false TCOr.l).trans
      (exists_elim fun _ => and_elim_r.trans (pure_elim' fun e => nomatch e))))

-- `Iris.BI.BigSepL2.bigSepL2_lookup_right` idx 9: necessary (SiProp: l2=[true], x2=false, l1=[()], i=0, Phi k y1 y2 = (y2 = true))
theorem w4c1_66 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_lookup_right 9 := fun h =>
  si_ef (((pure_intro rfl).trans (BigSepL2.bigSepL2_singleton (Φ := fun _ _ y => iprop(⌜y = true⌝)) (x := ()) (y := true)).2).trans
    ((@h SiProp _ Unit Bool (fun _ _ y => iprop(⌜y = true⌝)) [()] [true] 0 false TCOr.l).trans
      (exists_elim fun _ => and_elim_r.trans (pure_elim' fun e => nomatch e))))

-- `Iris.BI.BigSepL2.bigSepL2_delete_cond` idx 10: necessary (SiProp: l1=[true], x1=false, l2=[()], i=0, Phi k y1 y2 = (y1 = true))
theorem w4c1_67 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_delete_cond 10 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Bool Unit (fun _ y _ => iprop(⌜y = true⌝)) [true] [()] 0 false () rfl).1.trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_delete_cond` idx 11: necessary (SiProp: l2=[true], x2=false, l1=[()], i=0, Phi k y1 y2 = (y2 = true))
theorem w4c1_68 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_delete_cond 11 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Bool (fun _ _ y => iprop(⌜y = true⌝)) [()] [true] 0 () false rfl).1.trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_delete` idx 11: necessary (SiProp: l1=[true], x1=false, l2=[()], i=0, Phi k y1 y2 = (y1 = true))
theorem w4c1_69 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_delete 11 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Bool Unit _ (fun _ y _ => iprop(⌜y = true⌝)) [true] [()] 0 false () rfl).1.trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_lookup_acc_impl` idx 10: necessary (SiProp: l1=[true], x1=false, l2=[()], i=0, Phi k y1 y2 = (y1 = true))
theorem w4c1_70 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_lookup_acc_impl 10 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Bool Unit (fun _ y _ => iprop(⌜y = true⌝)) [true] [()] 0 false () rfl).trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_lookup_acc_impl` idx 11: necessary (SiProp: l2=[true], x2=false, l1=[()], i=0, Phi k y1 y2 = (y2 = true))
theorem w4c1_71 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_lookup_acc_impl 11 := fun h =>
  Bool.false_ne_true ((BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Bool (fun _ _ y => iprop(⌜y = true⌝)) [()] [true] 0 () false rfl).trans sep_elim_left)) 0 rfl)

-- `Iris.BI.BigSepL2.bigSepL2_forall` idx 4: necessary (HeapProp Unit: l1=l2=[], Phi=True; True |- emp fails)
theorem w4c1_72 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_forall 4 := fun h =>
  heap_not_affine ((and_intro (pure_intro rfl) (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      BI.imp_intro (and_elim_r.trans (pure_elim' fun h => by simp at h)))).trans
    (@h HP _ Unit Unit (fun _ _ _ => iprop(True)) [] [] (fun _ _ _ => inferInstance)).2)

-- `Iris.BI.BigSepL2.bigSepL2_persistently` idx 4: necessary (HeapProp Unit: l1=l2=[]; <pers> emp = True, not |- emp)
theorem w4c1_73 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_persistently 4 := fun h =>
  heap_not_affine ((show (iprop(True) : HP) ⊢ <pers> emp from fun _ _ => rfl).trans (@h HP _ Unit Unit (fun _ _ _ => emp) [] []).1)

-- `Iris.BI.BigSepL2.bigSepL2_delete` idx 4: necessary (HeapProp Unit: l1=l2=[()], i=0, Phi=emp; emp vs emp * (False -> emp), the latter is True)
theorem w4c1_74 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_delete 4 := fun h =>
  heap_not_affine ((emp_sep.2.trans (sep_mono_right ((BI.imp_intro (and_elim_r.trans (pure_elim' fun h => absurd rfl h))).trans (BigSepL2.bigSepL2_singleton (PROP := HP) (Φ := fun k _ _ => iprop(⌜k ≠ 0⌝ → emp)) (x := ()) (y := ())).2))).trans
    ((@h HP _ Unit Unit (fun _ _ _ => emp) [()] [()] 0 () () rfl rfl).2.trans BigSepL2.bigSepL2_singleton.1))

-- `Iris.BI.BigSepMS.bigSepMS_mono` idx 8: necessary (SiProp: X={0}, Phi=True, Psi=False)
theorem w4c1_8 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_mono 8 := fun h =>
  si_nf ((msSing _).2.trans ((@h SiProp _ MSN Nat _ (fun _ => iprop(True)) (fun _ => iprop(False)) {0}).trans (msSing _).1))

-- `Iris.BI.BigSepMS.bigSepMS_ne` idx 9: necessary (HeapProp Unit (n-distance is equality): X={0}, Phi=True, Psi=False)
theorem w4c1_75 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_ne 9 := fun h => by
  have e : _ = _ := @h HP _ MSN Nat _ (fun _ => iprop(True)) (fun _ => iprop(False)) {0} 0
  exact ((msSing _).2.trans ((BiEntails.of_eq e).1.trans (msSing _).1)) (∅ : State Unit) trivial

-- `Iris.BI.BigSepMS.bigSepMS_eq` idx 8: necessary (SiProp: X={0}, Phi=True, Psi=False)
theorem w4c1_76 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_eq 8 := fun h =>
  si_nf ((msSing _).2.trans ((BiEntails.of_eq (@h SiProp _ MSN Nat _ (fun _ => iprop(True)) (fun _ => iprop(False)) {0})).1.trans (msSing _).1))

-- `Iris.BI.BigSepMS.bigSepMS_eqv` idx 8: necessary (SiProp: X={0}, Phi=True, Psi=False)
theorem w4c1_77 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_eqv 8 := fun h =>
  si_nf ((msSing _).2.trans ((@h SiProp _ MSN Nat _ (fun _ => iprop(True)) (fun _ => iprop(False)) {0}).1.trans (msSing _).1))

-- `Iris.BI.BigSepMS.bigSepMS_mono_of_forall` idx 8: necessary (SiProp: X={0}, Phi=True, Psi=False)
theorem w4c1_78 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_mono_of_forall 8 := fun h =>
  si_nf ((msSing _).2.trans ((@h SiProp _ MSN Nat _ (fun _ => iprop(True)) (fun _ => iprop(False)) {0}).trans (msSing _).1))

-- `Iris.BI.BigSepMS.bigSepMS_flip_mono` idx 8: necessary (SiProp: X={0}, Psi=True, Phi=False)
theorem w4c1_79 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_flip_mono 8 := fun h =>
  si_nf ((msSing _).2.trans ((@h SiProp _ MSN Nat _ (fun _ => iprop(False)) (fun _ => iprop(True)) {0}).trans (msSing _).1))

-- `Iris.BI.BigSepMS.bigSepMS_empty_intro` idx 6: necessary (HeapProp Unit: P=True not affine)
theorem w4c1_80 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_empty_intro 6 := fun h =>
  heap_not_affine ((@h HP _ MSN Nat _ iprop(True) (fun _ => iprop(True))).trans BigSepMS.bigSepMS_empty.1)

-- `Iris.BI.BigSepMS.bigSepMS_delete` idx 8: necessary (SiProp: X=empty, x=0, Phi=False)
theorem w4c1_81 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_delete 8 := fun h =>
  si_ef (BigSepMS.bigSepMS_empty.2.trans ((@h SiProp _ MSN Nat _ (fun _ => iprop(False)) ∅ 0).1.trans sep_elim_left))

-- `Iris.BI.BigSepMS.bigSepMS_persistent_inst` idx 7: necessary (HeapProp Unit: X={0}, Phi=own0 not persistent)
theorem w4c1_82 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_persistent_inst 7 := fun h =>
  own0_not_pers ⟨(msSing _).2.trans ((@h HP _ MSN Nat _ (fun _ => own0) {0}).persistent.trans (persistently_mono (msSing _).1))⟩

-- `Iris.BI.BigSepMS.bigSepMS_affine` idx 7: necessary (HeapProp Unit: X={0}, Phi=True not affine)
theorem w4c1_83 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_affine 7 := fun h =>
  true_not_affine ⟨(msSing _).2.trans (@h HP _ MSN Nat _ (fun _ => iprop(True)) {0}).affine⟩

-- `Iris.BI.BigSepMS.bigSepMS_affine_inst` idx 7: necessary (HeapProp Unit: X={0}, Phi=True not affine)
theorem w4c1_84 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_affine_inst 7 := fun h =>
  true_not_affine ⟨(msSing _).2.trans (@h HP _ MSN Nat _ (fun _ => iprop(True)) {0}).affine⟩

-- `Iris.BI.BigSepMS.bigSepMS_timeless` idx 8: necessary (SiProp: X={0}, Phi=s0 not timeless)
theorem w4c1_85 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_timeless 8 := fun h =>
  s0_not_timeless ⟨(later_mono (msSing _).2).trans ((@h SiProp _ MSN Nat _ _ (fun _ => s0) {0}).timeless.trans (except0_mono (msSing _).1))⟩

-- `Iris.BI.BigSepMS.bigSepMS_timeless_inst` idx 8: necessary (SiProp: X={0}, Phi=s0 not timeless)
theorem w4c1_86 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_timeless_inst 8 := fun h =>
  s0_not_timeless ⟨(later_mono (msSing _).2).trans ((@h SiProp _ MSN Nat _ _ (fun _ => s0) {0}).timeless.trans (except0_mono (msSing _).1))⟩

-- `Iris.BI.BigSepMS.bigSepMS_elem_of` idx 8: necessary (SiProp: X=empty, x=0, Phi=False)
theorem w4c1_87 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_elem_of 8 := fun h =>
  si_ef (BigSepMS.bigSepMS_empty.2.trans (@h SiProp _ MSN Nat _ (fun _ => iprop(False)) ∅ 0 _))

-- `Iris.BI.BigSepMS.bigSepMS_elem_of` idx 9: necessary (HeapProp Unit: X={0} disjoint-union {1}, x=0, Phi 0 = emp, Phi 1 = True (not affine))
theorem w4c1_88 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_elem_of 9 := fun h =>
  heap_not_affine ((emp_sep.2.trans (sep_mono_right ((pure_intro trivial).trans (msSing1 (fun x => if x = 0 then emp else iprop(True))).2))).trans
    ((BigSepMS.bigSepMS_insert (MS := MSN)).2.trans
      (@h HP _ MSN Nat _ (fun x => if x = 0 then emp else iprop(True)) ({0} ⊎ {1}) 0 (mem_disjUnion_iff.2 (.inl (mem_singleton_iff.2 rfl))))))

-- `Iris.BI.BigSepMS.bigSepMS_elem_of_acc` idx 8: necessary (SiProp: X=empty, x=0, Phi=False)
theorem w4c1_89 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_elem_of_acc 8 := fun h =>
  si_ef (BigSepMS.bigSepMS_empty.2.trans ((@h SiProp _ MSN Nat _ (fun _ => iprop(False)) ∅ 0).trans sep_elim_left))

-- `Iris.BI.BigSepMS.bigSepMS_pure` idx 5: necessary (HeapProp Unit: X=empty; True |- emp fails)
theorem w4c1_90 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_pure 5 := fun h =>
  heap_not_affine ((pure_intro (fun _ h => absurd h not_mem_empty)).trans ((@h HP _ MSN Nat _ (fun _ => True) ∅).2.trans BigSepMS.bigSepMS_empty.1))

-- `Iris.BI.BigSepMS.bigSepMS_intro` idx 8: necessary (HeapProp Unit: P=True (not intuitionistic), X=empty)
theorem w4c1_91 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_intro 8 := fun h =>
  heap_not_affine ((@h HP _ MSN Nat _ iprop(True) (fun _ => iprop(True)) ∅ (fun hx => absurd hx not_mem_empty)).trans BigSepMS.bigSepMS_empty.1)

-- `Iris.BI.BigSepMS.bigSepMS_intro` idx 9: necessary (SiProp: P=emp, X={0}, Phi=False)
theorem w4c1_92 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_intro 9 := fun h =>
  si_ef ((@h SiProp _ MSN Nat _ emp (fun _ => iprop(False)) {0} _).trans (msSing _).1)

-- `Iris.BI.BigSepMS.bigSepMS_elem_of_acc_impl` idx 8: necessary (SiProp: X=empty, x=0, Phi=False)
theorem w4c1_93 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_elem_of_acc_impl 8 := fun h =>
  si_ef (BigSepMS.bigSepMS_empty.2.trans ((@h SiProp _ MSN Nat _ (fun _ => iprop(False)) ∅ 0).trans sep_elim_left))

-- `Iris.BI.BigSepMS.bigSepMS_persistently` idx 5: necessary (HeapProp Unit: X=empty; <pers> emp = True, not |- emp)
theorem w4c1_94 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_persistently 5 := fun h =>
  heap_not_affine ((show (iprop(True) : HP) ⊢ <pers> emp from fun _ _ => rfl).trans ((persistently_mono BigSepMS.bigSepMS_empty.2).trans
    ((@h HP _ MSN Nat _ (fun _ => emp) ∅).1.trans BigSepMS.bigSepMS_empty.1)))

-- `Iris.BI.BigSepMS.bigSepMS_subseteq` idx 8: necessary (HeapProp Unit: X={0}, Y=empty, Phi=True not affine)
theorem w4c1_95 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_subseteq 8 := fun h =>
  heap_not_affine ((msSing _).2.trans ((@h HP _ MSN Nat _ (fun _ => iprop(True)) {0} ∅
    (subset_iff.mpr fun _ => by rw [LawfulMultiSet.multiplicity_empty]; exact Nat.zero_le _)).trans BigSepMS.bigSepMS_empty.1))

-- `Iris.BI.BigSepMS.bigSepMS_subseteq` idx 9: necessary (SiProp: X=empty, Y={0}, Phi=False)
theorem w4c1_96 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_subseteq 9 := fun h =>
  si_ef (BigSepMS.bigSepMS_empty.2.trans ((@h SiProp _ MSN Nat _ (fun _ => iprop(False)) ∅ {0} _).trans (msSing _).1))

-- `Iris.BI.BigSepL.bigSepL_later` idx 3: necessary (UPred B2 (non-affine): l=[]; later emp |- emp fails at step 0)
theorem w4c1_97 : ¬ drop0% Iris.BI.BigSepL.bigSepL_later 3 := fun h =>
  b2_later_emp (@h (UPred B2) _ Unit (fun _ _ => emp) []).1

-- `Iris.BI.BigSepL.bigSepL_laterN` idx 3: necessary (UPred B2 (non-affine): l=[], n=1; later emp |- emp fails at step 0)
theorem w4c1_98 : ¬ drop0% Iris.BI.BigSepL.bigSepL_laterN 3 := fun h =>
  b2_later_emp (@h (UPred B2) _ Unit (fun _ _ => emp) [] 1).1

-- `Iris.BI.BigSepMS.bigSepMS_later` idx 5: necessary (UPred B2 (non-affine): X=empty; later emp |- emp fails at step 0)
theorem w4c1_99 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_later 5 := fun h =>
  b2_later_emp ((later_mono BigSepMS.bigSepMS_empty.2).trans ((@h (UPred B2) _ MSN Nat _ (fun _ => emp) ∅).1.trans BigSepMS.bigSepMS_empty.1))

-- `Iris.BI.BigSepMS.bigSepMS_laterN` idx 5: necessary (UPred B2 (non-affine): X=empty, n=1; later emp |- emp fails at step 0)
theorem w4c1_100 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_laterN 5 := fun h =>
  b2_later_emp ((later_mono BigSepMS.bigSepMS_empty.2).trans ((@h (UPred B2) _ MSN Nat _ (fun _ => emp) 1 ∅).1.trans BigSepMS.bigSepMS_empty.1))

-- `Iris.BI.BigSepL.bigSepL_forall_elim` idx 6: necessary (UPred Credit (affine, core 0): l=[(),()], Phi=ownM 1 (not persistent); ownM 1 |- ownM 2 fails)
theorem w4c1_101 : ¬ drop0% Iris.BI.BigSepL.bigSepL_forall_elim 6 := fun h =>
  cm_bad ((forall_intro fun _ => forall_intro fun _ => BI.imp_intro and_elim_l).trans
    ((@h (UPred Credit) _ Unit (fun _ _ => UPred.ownM (1 : Credit)) [(), ()] _).trans ((sep_mono_right sep_emp.1).trans (UPred.ownM_op (1 : Credit) 1).2)))

-- `Iris.BI.BigSepL.bigSepL_forall_eqv` idx 6: necessary (UPred Credit (affine, core 0): l=[(),()], Phi=ownM 1 (not persistent))
theorem w4c1_102 : ¬ drop0% Iris.BI.BigSepL.bigSepL_forall_eqv 6 := fun h =>
  cm_bad ((forall_intro fun _ => forall_intro fun _ => BI.imp_intro and_elim_l).trans
    ((@h (UPred Credit) _ Unit (fun _ _ => UPred.ownM (1 : Credit)) [(), ()] _).2.trans ((sep_mono_right sep_emp.1).trans (UPred.ownM_op (1 : Credit) 1).2)))

-- `Iris.BI.BigSepL2.bigSepL2_forall` idx 8: necessary (UPred Credit (affine, core 0): l1=l2=[(),()], Phi=ownM 1 (not persistent))
theorem w4c1_103 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_forall 8 := fun h =>
  cm_bad ((and_intro (pure_intro rfl) (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => BI.imp_intro (BI.imp_intro (and_elim_l.trans and_elim_l)))).trans
    ((@h (UPred Credit) _ Unit Unit _ (fun _ _ _ => UPred.ownM (1 : Credit)) [(), ()] [(), ()]).2.trans ((sep_mono_right sep_emp.1).trans (UPred.ownM_op (1 : Credit) 1).2)))

-- `Iris.BI.BigSepMS.bigSepMS_forall` idx 8: necessary (UPred Credit (affine, core 0): X={0} disjoint-union {1}, Phi=ownM 1 (not persistent))
theorem w4c1_104 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_forall 8 := fun h =>
  cm_bad ((forall_intro fun _ => BI.imp_intro and_elim_l).trans
    ((@h (UPred Credit) _ MSN Nat _ _ (fun _ => UPred.ownM (1 : Credit)) ({0} ⊎ {1})).2.trans
      ((BigSepMS.bigSepMS_insert (MS := MSN)).1.trans ((sep_mono_right (msSing1 _).1).trans (UPred.ownM_op (1 : Credit) 1).2))))

-- `Iris.BI.BigSepL.bigSepL_forall_intro` idx 5: necessary (HeapProp Unit: l=[(),()], Phi 0 = emp, Phi 1 = True (both persistent); True |- emp fails)
theorem w4c1_105 : ¬ drop0% Iris.BI.BigSepL.bigSepL_forall_intro 5 := fun h =>
  heap_not_affine (((emp_sep.2.trans (sep_mono_right sep_emp.2)) : (iprop(True) : HP) ⊢ bigSepL (fun k (_ : Unit) => if k = 0 then emp else iprop(True)) [(), ()]).trans
    ((@h HP _ Unit (fun k _ => if k = 0 then emp else iprop(True)) [(), ()] (fun k _ => by split <;> infer_instance)).trans
      ((forall_elim 0).trans ((forall_elim ()).trans ((and_intro .rfl (pure_intro rfl)).trans imp_elim_left)))))

-- `Iris.BI.BigSepL.bigSepL_forall_intro` idx 6: removable (in an affine BI every element of the big separating conjunction can be extracted by bigSepL_lookup; persistence is only needed for the converse)
theorem w4c1_106 : drop% Iris.BI.BigSepL.bigSepL_forall_intro 6 := by
  intro PROP _ A Φ l _
  exact forall_intro fun k => forall_intro fun x => BI.imp_intro (pure_elim_right fun hk => BigSepL.bigSepL_lookup hk)

-- `_private.Iris.BI.BigOp.BigSepList.0.Iris.BI.BigSepL2.zip_set` idx 5: removable (zip and set commute for every index: out of range both sides are unchanged; induction on the lists)
theorem w4c1_107 : drop% _private.Iris.BI.BigOp.BigSepList.«0».Iris.BI.BigSepL2.zip_set 5 := by
  intro C D l1 l2 i _ y1 y2
  exact zipSet l1 l2 i y1 y2

-- `_private.Iris.BI.BigOp.BigSepList.0.Iris.BI.BigSepL2.zip_set` idx 6: removable (zip and set commute for every index: out of range both sides are unchanged; induction on the lists)
theorem w4c1_108 : drop% _private.Iris.BI.BigOp.BigSepList.«0».Iris.BI.BigSepL2.zip_set 6 := by
  intro C D l1 l2 i _ y1 y2
  exact zipSet l1 l2 i y1 y2

-- `Iris.BI.BigSepL2.bigSepL2_sep_sepL_left` idx 4: removable (holds in every BI: induction on the lists; equal heads by sep_sep_sep_comm, different lengths give False on both sides)
theorem w4c1_109 : drop% Iris.BI.BigSepL2.bigSepL2_sep_sepL_left 4 := by
  intro PROP _ A B Φ Ψ l1 l2
  exact sepLLeft Φ Ψ l1 l2

-- `Iris.BI.BigSepL2.bigSepL2_sep_sepL_right` idx 4: removable (the library derivation from bigSepL2_sep_sepL_left goes through with the BIAffine-free version)
theorem w4c1_110 : drop% Iris.BI.BigSepL2.bigSepL2_sep_sepL_right 4 := by
  intro PROP _ A B Φ Ψ l1 l2
  exact (BigSepL2.bigSepL2_eqv_of_forall_eqv sep_comm).trans <| BigSepL2.bigSepL2_flip.trans <|
    (BigSepL2.bigSepL2_eqv_of_forall_eqv sep_comm).trans <| (sepLLeft _ _ _ _).trans <|
    sep_congr_right BigSepL2.bigSepL2_flip

-- `Iris.BI.BigSepL2.bigSepL2_proper_2` idx 12: necessary (SiProp: l1=[()], l1'=[], l2=l2'=[]; False vs emp)
theorem w4c1_111 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_proper_2 12 := fun h =>
  si_ef (@h SiProp _ Unit Unit _ _ (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(True)) [()] [] [] [] rfl
    (fun _ h2 => by simp at h2) (fun h1 _ => by simp at h1) (fun _ h2 _ _ _ _ => by simp at h2)).2

-- `Iris.BI.BigSepL2.bigSepL2_proper_2` idx 13: necessary (SiProp: l2=[()], l2'=[], l1=l1'=[]; False vs emp)
theorem w4c1_112 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_proper_2 13 := fun h =>
  si_ef (@h SiProp _ Unit Unit _ _ (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(True)) [] [] [()] [] rfl
    (fun h1 _ => by simp at h1) (fun _ h2 => by simp at h2) (fun h1 _ _ _ _ _ => by simp at h1)).2

-- `Iris.BI.BigSepL2.bigSepL2_proper_2` idx 14: necessary (SiProp, A=Bool (discrete): l1=[false], l1'=[true], l2=l2'=[()], Phi=True, Psi=False; hf vacuous)
theorem w4c1_113 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_proper_2 14 := fun h =>
  si_nf (BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Bool Unit (OFE.ofDiscrete Bool) _ (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False))
    [false] [true] [()] [()] rfl rfl (fun _ _ => rfl) (fun {k} _ _ h1 h2 e _ _ _ => by cases k <;> simp_all)).1.trans BigSepL2.bigSepL2_singleton.1))

-- `Iris.BI.BigSepL2.bigSepL2_proper_2` idx 15: necessary (SiProp, B=Bool (discrete): l2=[false], l2'=[true], l1=l1'=[()], Phi=True, Psi=False; hf vacuous)
theorem w4c1_114 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_proper_2 15 := fun h =>
  si_nf (BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Bool _ (OFE.ofDiscrete Bool) (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False))
    [()] [()] [false] [true] rfl rfl (fun _ _ => rfl) (fun {k} _ _ _ _ _ h1 h2 e => by cases k <;> simp_all)).1.trans BigSepL2.bigSepL2_singleton.1))

-- `Iris.BI.BigSepL2.bigSepL2_proper_2` idx 16: necessary (SiProp: all lists [()], Phi=True, Psi=False)
theorem w4c1_115 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_proper_2 16 := fun h =>
  si_nf (BigSepL2.bigSepL2_singleton.2.trans ((@h SiProp _ Unit Unit _ _ (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False))
    [()] [()] [()] [()] rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)).1.trans BigSepL2.bigSepL2_singleton.1))

-- `Iris.BI.BigSepL2.bigSepL2_dist_2` idx 13: necessary (HeapProp Unit (n-distance is equality): l1=[()], l1'=[], l2=l2'=[]; False vs emp)
theorem w4c1_116 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_dist_2 13 := fun h => by
  have e : _ = _ := @h HP _ Unit Unit _ _ (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(True)) [()] [] [] [] 0 rfl
    (fun _ h2 => by simp at h2) (fun h1 _ => by simp at h1) (fun _ h2 _ _ _ _ => by simp at h2)
  exact (BiEntails.of_eq e).2 (∅ : State Unit) rfl

-- `Iris.BI.BigSepL2.bigSepL2_dist_2` idx 14: necessary (HeapProp Unit: l2=[()], l2'=[], l1=l1'=[]; False vs emp)
theorem w4c1_117 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_dist_2 14 := fun h => by
  have e : _ = _ := @h HP _ Unit Unit _ _ (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(True)) [] [] [()] [] 0 rfl
    (fun h1 _ => by simp at h1) (fun _ h2 => by simp at h2) (fun h1 _ _ _ _ _ => by simp at h1)
  exact (BiEntails.of_eq e).2 (∅ : State Unit) rfl

-- `Iris.BI.BigSepL2.bigSepL2_dist_2` idx 15: necessary (HeapProp Unit, A=Bool (discrete): l1=[false], l1'=[true], l2=l2'=[()], Phi=True, Psi=False; hf vacuous)
theorem w4c1_118 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_dist_2 15 := fun h => by
  have e : _ = _ := @h HP _ Bool Unit (OFE.ofDiscrete Bool) _ (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False))
    [false] [true] [()] [()] 0 rfl rfl (fun _ _ => OFE.Dist.rfl) (fun {k} _ _ h1 h2 e _ _ _ => by cases k <;> simp_all [OFE.Dist])
  exact (BigSepL2.bigSepL2_singleton.2.trans ((BiEntails.of_eq e).1.trans BigSepL2.bigSepL2_singleton.1)) (∅ : State Unit) trivial

-- `Iris.BI.BigSepL2.bigSepL2_dist_2` idx 16: necessary (HeapProp Unit, B=Bool (discrete): l2=[false], l2'=[true], l1=l1'=[()], Phi=True, Psi=False; hf vacuous)
theorem w4c1_119 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_dist_2 16 := fun h => by
  have e : _ = _ := @h HP _ Unit Bool _ (OFE.ofDiscrete Bool) (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False))
    [()] [()] [false] [true] 0 rfl rfl (fun _ _ => OFE.Dist.rfl) (fun {k} _ _ _ _ _ h1 h2 e => by cases k <;> simp_all [OFE.Dist])
  exact (BigSepL2.bigSepL2_singleton.2.trans ((BiEntails.of_eq e).1.trans BigSepL2.bigSepL2_singleton.1)) (∅ : State Unit) trivial

-- `Iris.BI.BigSepL2.bigSepL2_dist_2` idx 17: necessary (HeapProp Unit: all lists [()], Phi=True, Psi=False)
theorem w4c1_120 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_dist_2 17 := fun h => by
  have e : _ = _ := @h HP _ Unit Unit _ _ (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False))
    [()] [()] [()] [()] 0 rfl rfl (fun _ _ => OFE.Dist.rfl) (fun _ _ => OFE.Dist.rfl)
  exact (BigSepL2.bigSepL2_singleton.2.trans ((BiEntails.of_eq e).1.trans BigSepL2.bigSepL2_singleton.1)) (∅ : State Unit) trivial

namespace W4c1
open Iris Iris.BI Iris.Std Iris.Instances.Classical Iris.Instances.Data
def h1 : State Unit := fun i => if i = 1 then result () else unknown
/-- Heap props exactly cell 0 (k = 0) or exactly cell 1 (k > 0). -/
def phiC : Nat → Unit → Unit → HP := fun k _ _ => if k = 0 then (fun σ => σ = h0) else (fun σ => σ = h1)
end W4c1

-- `Iris.BI.BigSepL2.bigSepL2_closed` idx 10: necessary (HeapProp Unit: P Q = Q only holds on heaps missing cell 0 or cell 1; emp, False, exactly-{0}, exactly-{1} satisfy it, their separating conjunction does not)
theorem w4c1_121 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_closed 10 := fun h => by
  have hc := @h HP _ Unit Unit (fun Q => ∀ σ, Q σ → σ 0 = unknown ∨ σ 1 = unknown) phiC [(),()] [(),()]
    (fun σ (e : σ = ∅) => .inl (by subst e; rfl)) (fun _ f => f.elim)
    (fun {k} _ _ h1' _ σ hσ => by
      rcases k with _ | _ | k
      · have e : σ = h0 := hσ
        subst e; exact .inr (by simp [h0])
      · have e : σ = h1 := hσ
        subst e; exact .inl (by simp [h1])
      · simp at h1')
  have := hc (h0 ∪ (h1 ∪ ∅)) ⟨h0, h1 ∪ ∅, rfl,
    fun i => by by_cases hi : i = 0 <;> simp [h0, h1, hi, Union.union, EmptyCollection.emptyCollection],
    (rfl : h0 = h0), h1, ∅, rfl, fun i => .inr rfl, (rfl : h1 = h1), (rfl : (∅ : State Unit) = ∅)⟩
  rcases this with e | e <;> simp [Union.union, h0, h1, EmptyCollection.emptyCollection] at e

namespace W4c1
open Iris Iris.BI Iris.Std
/-- Step-indexed predicates over the Bool-or monoid with exact splitting, downward closed in the step
and resource-blind at step 0. As a BI, emp holds at every resource at step 0 but only at false later,
so emp is not timeless (a non-affine BI with non-timeless emp). -/
structure TP where
  holds : Nat → Bool → Prop
  mono {n n' : Nat} {m : Bool} : holds n m → n' ≤ n → holds n' m
  irr {m m' : Bool} : holds 0 m → holds 0 m'

theorem TP.ext' : {P Q : TP} → (∀ n m, P.holds n m ↔ Q.holds n m) → P = Q
  | ⟨p, _, _⟩, ⟨q, _, _⟩, h => by
    have : p = q := funext fun n => funext fun m => propext (h n m)
    subst this; rfl

def TP.emp : TP where
  holds n m := n = 0 ∨ m = false
  mono h hle := by rcases h with h | h; exact .inl (by omega); exact .inr h
  irr _ := .inl rfl
def TP.pure (φ : Prop) : TP where
  holds _ _ := φ
  mono h _ := h
  irr h := h
def TP.and (P Q : TP) : TP where
  holds n m := P.holds n m ∧ Q.holds n m
  mono h hle := ⟨P.mono h.1 hle, Q.mono h.2 hle⟩
  irr h := ⟨P.irr h.1, Q.irr h.2⟩
def TP.or (P Q : TP) : TP where
  holds n m := P.holds n m ∨ Q.holds n m
  mono h hle := h.elim (fun h => .inl (P.mono h hle)) (fun h => .inr (Q.mono h hle))
  irr h := h.elim (fun h => .inl (P.irr h)) (fun h => .inr (Q.irr h))
def TP.imp (P Q : TP) : TP where
  holds n m := ∀ n', n' ≤ n → P.holds n' m → Q.holds n' m
  mono h hle n'' h'' hp := h n'' (Nat.le_trans h'' hle) hp
  irr h n' hn' hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) (P.irr hp))
def TP.sForall (Ψ : TP → Prop) : TP where
  holds n m := ∀ p, Ψ p → p.holds n m
  mono h hle p hp := p.mono (h p hp) hle
  irr h p hp := p.irr (h p hp)
def TP.sExists (Ψ : TP → Prop) : TP where
  holds n m := ∃ p, Ψ p ∧ p.holds n m
  mono h hle := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.mono h hle⟩
  irr h := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.irr h⟩
def TP.sep (P Q : TP) : TP where
  holds n m := ∃ a b, m = Bool.or a b ∧ P.holds n a ∧ Q.holds n b
  mono h hle := let ⟨a, b, e, hp, hq⟩ := h; ⟨a, b, e, P.mono hp hle, Q.mono hq hle⟩
  irr {_ m'} h := let ⟨_, _, _, hp, hq⟩ := h; ⟨m', false, by cases m' <;> rfl, P.irr hp, Q.irr hq⟩
def TP.wand (P Q : TP) : TP where
  holds n m := ∀ n', n' ≤ n → ∀ b, P.holds n' b → Q.holds n' (Bool.or m b)
  mono h hle n'' h'' b hp := h n'' (Nat.le_trans h'' hle) b hp
  irr h n' hn' b hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) b hp)
def TP.pers (P : TP) : TP where
  holds n _ := P.holds n false
  mono h hle := P.mono h hle
  irr h := h
def TP.later (P : TP) : TP where
  holds n m := match n with | 0 => True | k+1 => P.holds k m
  mono {n n' m} h hle := by
    cases n' with
    | zero => trivial
    | succ k' => cases n with
      | zero => omega
      | succ k => exact P.mono h (by omega)
  irr _ := trivial

instance : BIBase TP where
  Entails P Q := ∀ n m, P.holds n m → Q.holds n m
  emp := TP.emp
  pure := TP.pure
  and := TP.and
  or := TP.or
  imp := TP.imp
  sForall := TP.sForall
  sExists := TP.sExists
  sep := TP.sep
  wand := TP.wand
  persistently := TP.pers
  later := TP.later

instance : COFE TP := COFE.ofDiscrete _

instance tpBI : BI TP where
  entails_refl _ _ h := h
  entails_trans h1 h2 n m h := h2 n m (h1 n m h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ _ h => h, fun _ _ h => h⟩,
    fun ⟨h1, h2⟩ => TP.ext' fun n m => ⟨h1 n m, h2 n m⟩⟩
  and_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  pure_intro h _ _ _ := h
  pure_elim' h n m hφ := h hφ n m trivial
  and_elim_l _ _ h := h.1
  and_elim_r _ _ h := h.2
  and_intro h1 h2 n m h := ⟨h1 n m h, h2 n m h⟩
  or_intro_l _ _ h := .inl h
  or_intro_r _ _ h := .inr h
  or_elim h1 h2 n m h := h.elim (h1 n m) (h2 n m)
  imp_intro {P _ _} h n m hp n' hle hq := h n' m ⟨P.mono hp hle, hq⟩
  imp_elim h n m hpq := h n m hpq.1 n (Nat.le_refl n) hpq.2
  sForall_intro h n m hp p hΨ := h p hΨ n m hp
  sForall_elim hΨ n m h := h _ hΨ
  sExists_intro hΨ n m h := ⟨_, hΨ, h⟩
  sExists_elim h n m := fun ⟨p, hp, hh⟩ => h p hp n m hh
  sep_mono h1 h2 n m := fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, h1 n a hp, h2 n b hq⟩
  emp_sep {P} := ⟨fun n m ⟨a, b, e, he, hp⟩ => by
      rcases he with he | he
      · subst he; exact P.irr hp
      · subst he; cases b <;> (subst e; exact hp),
    fun n m hp => ⟨false, m, by cases m <;> rfl, .inr rfl, hp⟩⟩
  sep_symm n m := fun ⟨a, b, e, hp, hq⟩ => ⟨b, a, by rw [e, Bool.or_comm], hq, hp⟩
  sep_assoc_l n m := fun ⟨_, c, e, ⟨a, b, e', hp, hq⟩, hr⟩ =>
    ⟨a, or b c, by rw [e, e', Bool.or_assoc], hp, b, c, rfl, hq, hr⟩
  wand_intro {P _ _} h n m hp n' hle b hq := h n' (Bool.or m b) ⟨m, b, rfl, P.mono hp hle, hq⟩
  wand_elim h n m := fun ⟨a, b, e, hp, hq⟩ => e ▸ h n a hp n (Nat.le_refl n) b hq
  persistently_mono h n _ hp := h n false hp
  persistently_idem_2 _ _ h := h
  persistently_emp_2 _ _ _ := .inr rfl
  persistently_and_2 _ _ h := h
  persistently_absorb_l n m := fun ⟨_, _, _, hp, _⟩ => hp
  persistently_and_l n m := fun ⟨hp, hq⟩ => ⟨false, m, by cases m <;> rfl, hp, hq⟩
  later_mono h n m hp := by
    cases n with
    | zero => trivial
    | succ k => exact h k m hp
  later_intro {P} n m hp := by
    cases n with
    | zero => trivial
    | succ k => exact P.mono hp (Nat.le_succ k)
  later_sForall_2 n m h := by
    cases n with
    | zero => trivial
    | succ k => exact fun p hp => h _ ⟨p, rfl⟩ (k+1) (Nat.le_refl _) hp
  later_sExists_false n m h := by
    cases n with
    | zero => exact .inl trivial
    | succ k =>
      obtain ⟨p, hp, hh⟩ := h
      exact .inr ⟨_, ⟨p, rfl⟩, hp, hh⟩
  later_sep := ⟨fun n m h => by
      cases n with
      | zero => exact ⟨m, false, by cases m <;> rfl, trivial, trivial⟩
      | succ k => exact h,
    fun n m h => by
      cases n with
      | zero => trivial
      | succ k => exact h⟩
  later_persistently := ⟨fun n m h => by cases n <;> exact h, fun n m h => by cases n <;> exact h⟩
  later_false_em {P} n m h := by
    cases n with
    | zero => exact .inl trivial
    | succ k =>
      refine .inr fun n' hle hf => ?_
      cases n' with
      | zero => exact P.mono h (Nat.zero_le _)
      | succ j => exact hf.elim

theorem tp_emp_not_timeless : ¬ Timeless (emp : TP) := fun ⟨h⟩ => by
  have := h 1 true (.inl rfl)
  rcases this with h1 | h1
  · exact h1
  · rcases h1 with h1 | h1 <;> simp at h1
end W4c1

-- `Iris.BI.BigSepL.bigSepL_timeless_id` idx 2: necessary (custom BI TP (step-indexed Bool-resource predicates, emp not timeless): Ps=[])
theorem w4c1_122 : ¬ drop0% Iris.BI.BigSepL.bigSepL_timeless_id 2 := fun h =>
  tp_emp_not_timeless ⟨(@h TP _ [] TCForall.nil).timeless⟩

-- `Iris.BI.BigSepL.bigSepL_timeless` idx 3: necessary (custom BI TP (emp not timeless): l=[])
theorem w4c1_123 : ¬ drop0% Iris.BI.BigSepL.bigSepL_timeless 3 := fun h =>
  tp_emp_not_timeless ⟨(@h TP _ Unit (fun _ _ => iprop(False)) [] (fun h => by simp at h)).timeless⟩

-- `Iris.BI.BigSepL.bigSepL_nil_timeless_inst` idx 3: necessary (custom BI TP (emp not timeless))
theorem w4c1_124 : ¬ drop0% Iris.BI.BigSepL.bigSepL_nil_timeless_inst 3 := fun h =>
  tp_emp_not_timeless ⟨(@h TP _ Unit (fun _ _ => iprop(False))).timeless⟩

-- `Iris.BI.BigSepL.bigSepL_timeless_inst` idx 3: necessary (custom BI TP (emp not timeless): l=[], Phi=False)
theorem w4c1_125 : ¬ drop0% Iris.BI.BigSepL.bigSepL_timeless_inst 3 := fun h =>
  tp_emp_not_timeless ⟨(@h TP _ Unit (fun _ _ => iprop(False)) [] _).timeless⟩

-- `Iris.BI.BigSepL2.bigSepL2_nil_timeless` idx 4: necessary (custom BI TP (emp not timeless))
theorem w4c1_126 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_nil_timeless 4 := fun h =>
  tp_emp_not_timeless ⟨(@h TP _ Unit Unit (fun _ _ _ => iprop(False))).timeless⟩

-- `Iris.BI.BigSepL2.bigSepL2_timeless` idx 4: necessary (custom BI TP (emp not timeless): l1=l2=[])
theorem w4c1_127 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_timeless 4 := fun h =>
  tp_emp_not_timeless ⟨(@h TP _ Unit Unit (fun _ _ _ => iprop(False)) [] [] (fun _ _ _ h => by simp at h)).timeless⟩

-- `Iris.BI.BigSepL2.bigSepL2_timeless'` idx 4: necessary (custom BI TP (emp not timeless): l1=l2=[], Phi=False)
theorem w4c1_128 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_timeless' 4 := fun h =>
  tp_emp_not_timeless ⟨(@h TP _ Unit Unit (fun _ _ _ => iprop(False)) [] [] _).timeless⟩

-- `Iris.BI.BigSepL2.bigSepL2_later_1` idx 4: necessary (custom BI TP (emp not timeless): l1=l2=[]; later emp |- except0 emp fails)
theorem w4c1_129 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_later_1 4 := fun h =>
  tp_emp_not_timeless ⟨@h TP _ Unit Unit (fun _ _ _ => iprop(False)) [] []⟩

-- `Iris.BI.BigSepL2.bigSepL2_later` idx 4: necessary (custom BI TP (emp not timeless): l1=l2=[]; later emp |- except0 emp fails)
theorem w4c1_130 : ¬ drop0% Iris.BI.BigSepL2.bigSepL2_later 4 := fun h =>
  tp_emp_not_timeless ⟨(@h TP _ Unit Unit (fun _ _ _ => iprop(False)) [] []).1⟩

-- `Iris.BI.BigSepMS.bigSepMS_empty_timeless_inst` idx 5: necessary (custom BI TP (emp not timeless))
theorem w4c1_131 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_empty_timeless_inst 5 := fun h =>
  tp_emp_not_timeless ⟨(later_mono BigSepMS.bigSepMS_empty.2).trans ((@h TP _ MSN Nat _ (fun _ => iprop(False))).timeless.trans (except0_mono BigSepMS.bigSepMS_empty.1))⟩

-- `Iris.BI.BigSepMS.bigSepMS_timeless` idx 5: necessary (custom BI TP (emp not timeless): X=empty)
theorem w4c1_132 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_timeless 5 := fun h =>
  tp_emp_not_timeless ⟨(later_mono BigSepMS.bigSepMS_empty.2).trans ((@h TP _ MSN Nat _ (fun _ => iprop(False)) ∅ (fun hx => absurd hx not_mem_empty)).timeless.trans (except0_mono BigSepMS.bigSepMS_empty.1))⟩

-- `Iris.BI.BigSepMS.bigSepMS_timeless_inst` idx 5: necessary (custom BI TP (emp not timeless): X=empty, Phi=False)
theorem w4c1_133 : ¬ drop0% Iris.BI.BigSepMS.bigSepMS_timeless_inst 5 := fun h =>
  tp_emp_not_timeless ⟨(later_mono BigSepMS.bigSepMS_empty.2).trans ((@h TP _ MSN Nat _ (fun _ => iprop(False)) ∅ _).timeless.trans (except0_mono BigSepMS.bigSepMS_empty.1))⟩
