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
namespace W9c2
open Iris Iris.Std

abbrev FM : Type → Type := fun V => Nat → Option V
@[simp] theorem fm_get {V : Type} (m : Nat → Option V) (k : Nat) : get? (M := FM) m k = m k := rfl
@[simp] theorem fm_ins {V : Type} (m : Nat → Option V) (k k' : Nat) (v : V) :
    (Std.insert (M := FM) m k v) k' = if k = k' then some v else m k' := rfl
@[simp] theorem fm_del {V : Type} (m : Nat → Option V) (k k' : Nat) :
    (delete (M := FM) m k) k' = if k = k' then none else m k' := rfl

abbrev z0 : Nat → Option Nat := fun _ => none
abbrev c0 : Nat → Option Nat := fun _ => some 0
abbrev o1 : Nat → Option Nat := fun k => if k = 1 then some 0 else none
abbrev o0 : Nat → Option Nat := fun k => if k = 0 then some 0 else none

end W9c2
open Iris Iris.Std W9c2

-- `Iris.Std.PartialMap.equiv.trans` idx 7: necessary (a = const 0, b = c = empty)
theorem w9c2_26 : ¬ drop0% Iris.Std.PartialMap.equiv.trans 7 := fun h =>
  absurd (@h Nat Nat FM _ c0 z0 z0 (fun _ => rfl) 0) (by decide)
-- `Iris.Std.PartialMap.equiv.trans` idx 8: necessary
theorem w9c2_27 : ¬ drop0% Iris.Std.PartialMap.equiv.trans 8 := fun h =>
  absurd (@h Nat Nat FM _ z0 z0 c0 (fun _ => rfl) 0) (by decide)
-- `Iris.Std.PartialMap.equiv.symm` idx 6: necessary
theorem w9c2_28 : ¬ drop0% Iris.Std.PartialMap.equiv.symm 6 := fun h =>
  absurd (@h Nat Nat FM _ z0 c0 0) (by decide)
-- `Iris.Std.PartialMap.subset_trans` idx 7: necessary
theorem w9c2_29 : ¬ drop0% Iris.Std.PartialMap.subset_trans 7 := fun h =>
  absurd (@h Nat Nat FM _ c0 z0 z0 (fun _ _ h => h) 0 0 rfl) (by decide)
-- `Iris.Std.PartialMap.subset_trans` idx 8: necessary
theorem w9c2_30 : ¬ drop0% Iris.Std.PartialMap.subset_trans 8 := fun h =>
  absurd (@h Nat Nat FM _ c0 c0 z0 (fun _ _ h => h) 0 0 rfl) (by decide)
-- `Iris.Std.PartialMap.disjoint_comm` idx 6: necessary
theorem w9c2_31 : ¬ drop0% Iris.Std.PartialMap.disjoint_comm 6 := fun h =>
  @h Nat Nat FM _ c0 c0 0 ⟨rfl, rfl⟩
-- `Iris.Std.PartialMap.all_mono` idx 7: necessary
theorem w9c2_32 : ¬ drop0% Iris.Std.PartialMap.all_mono 7 := fun h =>
  @h Nat Nat FM _ (fun _ _ => False) (fun _ _ => False) c0 (fun _ _ x => x) 0 0 rfl
-- `Iris.Std.PartialMap.all_mono` idx 8: necessary
theorem w9c2_33 : ¬ drop0% Iris.Std.PartialMap.all_mono 8 := fun h =>
  @h Nat Nat FM _ (fun _ _ => True) (fun _ _ => False) c0 (fun _ _ _ => trivial) 0 0 rfl
-- `Iris.Std.LawfulPartialMap.get?_insert_eq` idx 8: necessary
theorem w9c2_34 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_insert_eq 8 := fun h =>
  absurd (@h FM Nat _ Nat z0 0 1 0) (by decide)
-- `Iris.Std.LawfulPartialMap.get?_insert_ne` idx 8: necessary
theorem w9c2_35 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_insert_ne 8 := fun h =>
  absurd (@h FM Nat _ Nat z0 0 0 0) (by decide)
-- `Iris.Std.LawfulPartialMap.get?_delete_eq` idx 7: necessary
theorem w9c2_36 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_delete_eq 7 := fun h =>
  absurd (@h FM Nat _ Nat c0 0 1) (by decide)
-- `Iris.Std.LawfulPartialMap.get?_delete_ne` idx 7: necessary
theorem w9c2_37 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_delete_ne 7 := fun h =>
  absurd (@h FM Nat _ Nat c0 0 0) (by decide)
-- `Iris.Std.LawfulPartialMap.get?_singleton_eq` idx 7: necessary
theorem w9c2_38 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_singleton_eq 7 := fun h =>
  absurd (@h Nat Nat FM _ 0 1 0) (by decide)
-- `Iris.Std.LawfulPartialMap.get?_singleton_ne` idx 7: necessary
theorem w9c2_39 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_singleton_ne 7 := fun h =>
  absurd (@h Nat Nat FM _ 0 0 0) (by decide)
-- `Iris.Std.LawfulPartialMap.get?_insert_rev` idx 8: necessary
theorem w9c2_40 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_insert_rev 8 := fun h =>
  absurd (@h Nat Nat FM _ z0 0 0 1) (by decide)
-- `Iris.Std.LawfulPartialMap.insert_insert_comm` idx 9: necessary
theorem w9c2_41 : ¬ drop0% Iris.Std.LawfulPartialMap.insert_insert_comm 9 := fun h =>
  absurd (congrFun (@h Nat Nat FM _ z0 0 0 0 1) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.delete_insert_of_ne` idx 8: necessary
theorem w9c2_42 : ¬ drop0% Iris.Std.LawfulPartialMap.delete_insert_of_ne 8 := fun h =>
  absurd (congrFun (@h Nat Nat FM _ z0 0 0 0) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.delete_of_get?` idx 6: necessary
theorem w9c2_43 : ¬ drop0% Iris.Std.LawfulPartialMap.delete_of_get? 6 := fun h =>
  absurd (congrFun (@h Nat Nat FM _ c0 0) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.insert_get?` idx 7: necessary
theorem w9c2_44 : ¬ drop0% Iris.Std.LawfulPartialMap.insert_get? 7 := fun h =>
  absurd (congrFun (@h Nat Nat FM _ z0 0 0) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.subset_insert` idx 7: necessary
theorem w9c2_45 : ¬ drop0% Iris.Std.LawfulPartialMap.subset_insert 7 := fun h =>
  absurd (@h Nat Nat FM _ c0 0 1 0 0 rfl) (by decide)
-- `Iris.Std.LawfulPartialMap.delete_subset_delete` idx 7: necessary
theorem w9c2_46 : ¬ drop0% Iris.Std.LawfulPartialMap.delete_subset_delete 7 := fun h =>
  absurd (@h Nat Nat FM _ c0 z0 0 1 0 rfl) (by decide)
-- `Iris.Std.LawfulPartialMap.insert_subset_insert` idx 8: necessary
theorem w9c2_47 : ¬ drop0% Iris.Std.LawfulPartialMap.insert_subset_insert 8 := fun h =>
  absurd (@h Nat Nat FM _ c0 z0 0 0 1 0 rfl) (by decide)
-- `Iris.Std.LawfulPartialMap.delete_singleton_ne` idx 7: necessary
theorem w9c2_48 : ¬ drop0% Iris.Std.LawfulPartialMap.delete_singleton_ne 7 := fun h =>
  absurd (congrFun (@h Nat Nat FM _ 0 0 0) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.all_insert_of_all` idx 8: necessary
theorem w9c2_49 : ¬ drop0% Iris.Std.LawfulPartialMap.all_insert_of_all 8 := fun h =>
  @h Nat Nat FM _ (fun _ _ => False) z0 0 0
-- `Iris.Std.LawfulPartialMap.all_of_all_insert` idx 9: necessary
theorem w9c2_50 : ¬ drop0% Iris.Std.LawfulPartialMap.all_of_all_insert 9 := fun h =>
  @h Nat Nat FM _ (fun _ _ => False) o1 0 0 rfl 1 0 rfl
-- `Iris.Std.LawfulPartialMap.all_insert` idx 8: necessary
theorem w9c2_51 : ¬ drop0% Iris.Std.LawfulPartialMap.all_insert 8 := fun h =>
  @h Nat Nat FM _ (fun _ _ => False) z0 0 0 (fun _ _ h => by simp at h) 0 0 rfl
-- `Iris.Std.LawfulPartialMap.all_insert` idx 9: necessary
theorem w9c2_52 : ¬ drop0% Iris.Std.LawfulPartialMap.all_insert 9 := fun h =>
  absurd (@h Nat Nat FM _ (fun k _ => k = 0) c0 0 0 rfl 1 0 rfl) (by decide)
-- `Iris.Std.LawfulPartialMap.all_insert_iff` idx 8: necessary (m = {0 ↦ 0}, insert 0 ↦ 1, P v := v = 1)
theorem w9c2_53 : ¬ drop0% Iris.Std.LawfulPartialMap.all_insert_iff 8 := fun h =>
  absurd (((@h Nat Nat FM _ (fun _ v => v = 1) o0 0 1).mp (fun k v hk => by
    simp only [fm_get, fm_ins] at hk; split at hk <;> simp_all)).2 0 0 rfl) (by decide)
-- `Iris.Std.LawfulPartialMap.all_delete` idx 7: necessary
theorem w9c2_54 : ¬ drop0% Iris.Std.LawfulPartialMap.all_delete 7 := fun h =>
  @h Nat Nat FM _ (fun _ _ => False) c0 0 1 0 rfl
-- `Iris.Std.LawfulPartialMap.disjoint_insert_left` idx 8: necessary
theorem w9c2_55 : ¬ drop0% Iris.Std.LawfulPartialMap.disjoint_insert_left 8 := fun h =>
  @h Nat Nat FM _ z0 c0 0 0 (fun _ h => by simp at h) 0 ⟨rfl, rfl⟩
-- `Iris.Std.LawfulPartialMap.disjoint_insert_left` idx 9: necessary
theorem w9c2_56 : ¬ drop0% Iris.Std.LawfulPartialMap.disjoint_insert_left 9 := fun h =>
  @h Nat Nat FM _ o1 o1 0 0 rfl 1 ⟨rfl, rfl⟩
-- `Iris.Std.LawfulPartialMap.disjoint_insert_right` idx 8: necessary
theorem w9c2_58 : ¬ drop0% Iris.Std.LawfulPartialMap.disjoint_insert_right 8 := fun h =>
  @h Nat Nat FM _ c0 z0 0 0 (fun _ h => by simp at h) 0 ⟨rfl, rfl⟩
-- `Iris.Std.LawfulPartialMap.disjoint_insert_right` idx 9: necessary
theorem w9c2_59 : ¬ drop0% Iris.Std.LawfulPartialMap.disjoint_insert_right 9 := fun h =>
  @h Nat Nat FM _ o1 o1 0 0 rfl 1 ⟨rfl, rfl⟩
-- `Iris.Std.LawfulPartialMap.disjoint_delete_left` idx 7: necessary
theorem w9c2_60 : ¬ drop0% Iris.Std.LawfulPartialMap.disjoint_delete_left 7 := fun h =>
  @h Nat Nat FM _ c0 c0 0 1 ⟨rfl, rfl⟩
-- `Iris.Std.LawfulPartialMap.disjoint_delete_right` idx 7: necessary
theorem w9c2_61 : ¬ drop0% Iris.Std.LawfulPartialMap.disjoint_delete_right 7 := fun h =>
  @h Nat Nat FM _ c0 c0 0 1 ⟨rfl, rfl⟩
-- `Iris.Std.LawfulPartialMap.disjoint_singleton_left` idx 7: necessary
theorem w9c2_62 : ¬ drop0% Iris.Std.LawfulPartialMap.disjoint_singleton_left 7 := fun h =>
  @h Nat Nat FM _ c0 0 0 0 ⟨rfl, rfl⟩
-- `Iris.Std.LawfulPartialMap.disjoint_singleton_right` idx 7: necessary
theorem w9c2_63 : ¬ drop0% Iris.Std.LawfulPartialMap.disjoint_singleton_right 7 := fun h =>
  @h Nat Nat FM _ c0 0 0 0 ⟨rfl, rfl⟩
-- `Iris.Std.LawfulPartialMap.union_equiv` idx 8: necessary
theorem w9c2_64 : ¬ drop0% Iris.Std.LawfulPartialMap.union_equiv 8 := fun h =>
  absurd (congrFun (@h Nat Nat FM _ c0 z0 z0 z0 rfl) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.union_equiv` idx 9: necessary
theorem w9c2_65 : ¬ drop0% Iris.Std.LawfulPartialMap.union_equiv 9 := fun h =>
  absurd (congrFun (@h Nat Nat FM _ z0 z0 c0 z0 rfl) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.map_equiv` idx 8: necessary
theorem w9c2_66 : ¬ drop0% Iris.Std.LawfulPartialMap.map_equiv 8 := fun h =>
  absurd (congrFun (@h Nat Nat FM _ Nat id c0 z0) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.dom_eq_of_option_rel` idx 8: necessary
theorem w9c2_67 : ¬ drop0% Iris.Std.LawfulPartialMap.dom_eq_of_option_rel 8 := fun h => by
  have := congrFun (@h Nat Nat FM _ Nat (fun _ _ => True) c0 z0) 0
  simp [PartialMap.dom] at this
-- `Iris.Std.LawfulPartialMap.disjoint_map` idx 9: necessary
theorem w9c2_68 : ¬ drop0% Iris.Std.LawfulPartialMap.disjoint_map 9 := fun h =>
  @h Nat Nat FM _ Nat id id c0 c0 0 ⟨rfl, rfl⟩
-- `Iris.Std.LawfulPartialMap.get?_zipWith_prod_eq_some` idx 10: necessary
theorem w9c2_69 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_zipWith_prod_eq_some 10 := fun h =>
  absurd (@h Nat Nat FM _ Nat z0 z0 0 0 0).1 (by decide)
-- `Iris.Std.LawfulPartialMap.isSome_zipWith_prod_congr` idx 13: necessary
theorem w9c2_70 : ¬ drop0% Iris.Std.LawfulPartialMap.isSome_zipWith_prod_congr 13 := fun h =>
  absurd (@h Nat Nat FM _ Nat Nat Nat Eq Eq c0 z0 c0 c0 (fun _ => .some rfl) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.isSome_zipWith_prod_congr` idx 14: necessary
theorem w9c2_71 : ¬ drop0% Iris.Std.LawfulPartialMap.isSome_zipWith_prod_congr 14 := fun h =>
  absurd (@h Nat Nat FM _ Nat Nat Nat Eq Eq c0 c0 c0 z0 (fun _ => .some rfl) 0) (by decide)
-- `Iris.Std.LawfulPartialMap.noDupKeys_cons` idx 4: necessary
theorem w9c2_72 : ¬ drop0% Iris.Std.LawfulPartialMap.noDupKeys_cons 4 := fun h =>
  absurd (@h Nat Nat (0, 0) [(0, 0), (0, 0)]) (by unfold NoDupKeys; decide)
-- `Iris.Std.LawfulPartialMap.noDupKeys_inj` idx 7: necessary
theorem w9c2_73 : ¬ drop0% Iris.Std.LawfulPartialMap.noDupKeys_inj 7 := fun h =>
  absurd (@h Nat Nat 0 0 1 [(0, 1)] (by unfold NoDupKeys; decide) (by simp)) (by decide)
-- `Iris.Std.LawfulPartialMap.noDupKeys_inj` idx 8: necessary
theorem w9c2_74 : ¬ drop0% Iris.Std.LawfulPartialMap.noDupKeys_inj 8 := fun h =>
  absurd (@h Nat Nat 0 1 0 [(0, 1)] (by unfold NoDupKeys; decide) (by simp)) (by decide)
-- `Iris.Std.LawfulPartialMap.get?_ofList_some` idx 8: necessary
theorem w9c2_75 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_ofList_some 8 := fun h =>
  absurd (@h Nat Nat FM _ 0 0 _ [] (by unfold NoDupKeys; decide)) (by decide)
-- `Iris.Std.LawfulPartialMap.get?_ofList_some` idx 9: necessary (first entry wins)
theorem w9c2_76 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_ofList_some 9 := fun h =>
  absurd (@h Nat Nat FM _ 0 1 _ [(0, 0), (0, 1)] (by simp)) (by decide)
-- `Iris.Std.LawfulPartialMap.get?_ofList_none` idx 6: necessary
theorem w9c2_77 : ¬ drop0% Iris.Std.LawfulPartialMap.get?_ofList_none 6 := fun h =>
  absurd (@h Nat Nat FM _ 0 [(0, 0)] (by unfold NoDupKeys; decide)) (by decide)

namespace W9c2
open Iris Iris.Std
abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare
abbrev TS := Std.ExtTreeSet Nat compare
theorem m00 : (0 : Nat) ∈ ({0} : TS) := Iris.Std.LawfulSet.mem_singleton.mpr rfl

/-- Heap on Nat → Option with finite support as the not-full condition. -/
noncomputable def hpF : Heap FM Nat where
  toPartialMap := instPartialMapFun
  notFull m := ∃ N, ∀ j, N ≤ j → m j = none
  fresh h := Classical.choose h
  get?_fresh {_ _ H} := Classical.choose_spec H _ (Nat.le_refl _)

noncomputable def uhF : UnboundedHeap FM Nat where
  toHeap := hpF
  notFull_empty := ⟨0, fun _ _ => rfl⟩
  notFull_insert_fresh {V v m H} := ⟨Classical.choose H + 1, fun j hj => by
    show (if Classical.choose H = j then some v else m j) = none
    rw [if_neg (by omega)]; exact Classical.choose_spec H j (by omega)⟩

/-- Relation on Nat: equality, or both at most 1. -/
def r01 (x y : Nat) : Prop := x = y ∨ (x ≤ 1 ∧ y ≤ 1)
instance : DecidableRel r01 := fun x y => inferInstanceAs (Decidable (x = y ∨ (x ≤ 1 ∧ y ≤ 1)))
theorem r01_eqv : Equivalence r01 :=
  ⟨fun _ => .inl rfl, fun {x y} h => by unfold r01 at *; omega, fun {x y z} h1 h2 => by unfold r01 at *; omega⟩
def rf (z : Nat) : Nat := if z = 1 then 5 else z
def rg (z : Nat) : Nat := if z = 0 then 1 else if z = 1 then 5 else z

end W9c2
open Iris Iris.Std W9c2

-- `Iris.Std.Heap.get?_fresh` idx 5: necessary (heap whose not-full condition is finite support; constant map)
theorem w9c2_24 : ¬ indep0% Iris.Std.Heap.get?_fresh 5 := fun h => by
  obtain ⟨N, hN⟩ := @h FM Nat hpF Nat c0
  exact absurd (hN N (Nat.le_refl _)) (by simp)
-- `Iris.Std.UnboundedHeap.notFull_insert_fresh` idx 6: necessary
theorem w9c2_25 : ¬ indep0% Iris.Std.UnboundedHeap.notFull_insert_fresh 6 := fun h => by
  obtain ⟨N, hN⟩ := @h FM Nat uhF Nat 0 c0
  exact absurd (hN N (Nat.le_refl _)) (by simp)
-- `cofinite_alter_cofinite` idx 4: necessary (at Type: P = Nat, S = True, S' = False)
theorem w9c2_13 : ¬ (∀ {P : Type} {S S' : P → Prop} (p' : P), infinite S → infinite S') := fun h => by
  obtain ⟨f, hf, -⟩ := @h Nat (fun _ => True) (fun _ => False) 0 ⟨id, fun _ => trivial, fun _ _ h => h⟩
  exact hf 0
-- `List.exists_of_forall₂_append` idx 6: necessary
theorem w9c2_14 : ¬ drop0% List.exists_of_forall₂_append 6 := fun h => by
  obtain ⟨l₂, l₂', he, hf, -, -⟩ := @h Nat Nat Eq [0] [] []
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp he.symm
  cases hf
-- `List.Forall₂.symm` idx 5: necessary
theorem w9c2_15 : ¬ drop0% List.Forall₂.symm 5 := fun h => by
  have := @h Nat Eq (fun h => h.symm) [0] []
  cases this
-- `List.Forall₂.equivalence` idx 2: necessary
theorem w9c2_16 : ¬ drop0% List.Forall₂.equivalence 2 := fun h => by
  have := (@h Nat (fun _ _ => False)).refl [0]
  cases this; assumption
-- `Nat.repeat_rel` idx 5: necessary (R = equal or both ≤ 1)
theorem w9c2_22 : ¬ drop0% Nat.repeat_rel 5 := fun h =>
  absurd (@h Nat r01 r01_eqv rf rg (fun z => by unfold r01 rf rg; split <;> split <;> omega) 2 0) (by decide)
-- `Option.Forall₂.equivalence` idx 2: necessary
theorem w9c2_23 : ¬ drop0% Option.Forall₂.equivalence 2 := fun h => by
  have := (@h Nat (fun _ _ => False)).refl (some 0)
  simp [Option.Forall₂] at this
-- `nclose_subseteq'` idx 5: necessary (E = ∅)
theorem w9c2_17 : ¬ drop0% nclose_subseteq' 5 := fun h =>
  CoPset.mem_empty (@h Namespace ∅ _ nroot nroot _ (coPpick_nclose _))
-- `ndot_ne_disjoint` idx 5: necessary (x = y)
theorem w9c2_18 : ¬ drop0% ndot_ne_disjoint 5 := fun h =>
  @h Namespace _ nroot nroot nroot _ ⟨coPpick_nclose _, coPpick_nclose _⟩
-- `ndot_preserve_disjoint_l` idx 5: necessary (E = full)
theorem w9c2_19 : ¬ drop0% ndot_preserve_disjoint_l 5 := fun h =>
  @h Namespace _ nroot CoPset.full nroot _ ⟨coPpick_nclose _, CoPset.mem_full⟩
-- `ndot_preserve_disjoint_r` idx 5: necessary (E = full)
theorem w9c2_20 : ¬ drop0% ndot_preserve_disjoint_r 5 := fun h =>
  @h Namespace _ nroot CoPset.full nroot _ ⟨CoPset.mem_full, coPpick_nclose _⟩
-- `CoPset.difference_difference` idx 4: necessary (X1 = Y = full, X2 = X3 = ∅)
theorem w9c2_21 : ¬ drop0% CoPset.difference_difference 4 := fun h =>
  h CoPset.full ∅ ∅ CoPset.full .xH
    ⟨CoPset.in_diff.mpr ⟨CoPset.mem_full, CoPset.not_in_union.mpr ⟨CoPset.mem_empty, CoPset.mem_empty⟩⟩,
     CoPset.mem_full⟩
-- `Pos.flatten_suffix` idx 2: necessary (l = [1], k = [])
theorem w9c2_92 : ¬ drop0% Pos.flatten_suffix 2 := fun h => by
  obtain ⟨q, hq⟩ := h [.xH] []
  cases hq
-- `Pos.dup_suffix_eq` idx 4: necessary
theorem w9c2_93 : ¬ drop0% Pos.dup_suffix_eq 4 := fun h =>
  absurd (@h .xH (.xO .xH) .xH .xH) (by decide)
-- `Pos.flatten_suffix_eq` idx 4: necessary (xs = [], ys = [1])
theorem w9c2_94 : ¬ drop0% Pos.flatten_suffix_eq 4 := fun h =>
  absurd (@h (.xH ++ Pos.flatten [.xH]) .xH [] [.xH] rfl) (by decide)
-- `Pos.flatten_suffix_eq` idx 5: necessary
theorem w9c2_95 : ¬ drop0% Pos.flatten_suffix_eq 5 := fun h =>
  absurd (@h .xH .xH [.xH] [.xO .xH] rfl) (by decide)
-- `Relation.Iterate.head_induction_on` idx 4: necessary (motive n := n ≠ 0)
theorem w9c2_96 : ¬ drop0% Relation.Iterate.head_induction_on 4 := fun h =>
  @h Unit (fun _ _ => True) () (fun n _ _ => n ≠ 0) (fun _ _ _ _ => Nat.succ_ne_zero _) 0 () (.rfl ()) rfl
-- `Relation.Iterate.head_induction_on` idx 5: necessary (motive n := n = 0)
theorem w9c2_97 : ¬ drop0% Relation.Iterate.head_induction_on 5 := fun h =>
  absurd (@h Unit (fun _ _ => True) () (fun n _ _ => n = 0) rfl 1 () (Relation.Iterate.head trivial (.rfl ())))
    (by decide)
-- `Relation.Iterate.head_induction_on` idx 8: necessary (empty relation, distinct endpoints)
theorem w9c2_98 : ¬ indep0% Relation.Iterate.head_induction_on 8 := fun h => by
  have := @h Bool (fun _ _ => False) false (fun _ _ _ => True) trivial (fun _ _ _ _ => trivial) 0 true
  cases this
-- `Iris.Std.LawfulFiniteMap.noDupKeys_map_key` idx 6: necessary
theorem w9c2_79 : ¬ drop0% Iris.Std.LawfulFiniteMap.noDupKeys_map_key 6 := fun h =>
  absurd (@h Nat Nat Nat id (fun _ _ h => h) [(0, 0), (0, 0)]) (by unfold NoDupKeys; decide)
-- `Iris.Std.LawfulFiniteMap.noDupKeys_mapIdx` idx 4: necessary
theorem w9c2_80 : ¬ drop0% Iris.Std.LawfulFiniteMap.noDupKeys_mapIdx 4 := fun h =>
  absurd (@h Nat Nat (fun _ => 0) [0, 0]) (by unfold NoDupKeys; decide)
-- `Iris.Std.LawfulFiniteMap.get?_ofSet_of_mem` idx 10: necessary (s = ∅)
theorem w9c2_81 : ¬ drop0% Iris.Std.LawfulFiniteMap.get?_ofSet_of_mem 10 := fun h => by
  have := @h Nat Nat TM _ TS _ _ 0 ∅ 0
  rw [LawfulFiniteMap.ofSet_empty, get?_empty] at this; cases this
-- `Iris.Std.LawfulFiniteMap.get?_ofSet_of_not_mem` idx 9: necessary (s = {0})
theorem w9c2_82 : ¬ drop0% Iris.Std.LawfulFiniteMap.get?_ofSet_of_not_mem 9 := fun h => by
  have := @h Nat Nat TM _ TS _ 0 {0} 0
  rw [LawfulFiniteMap.get?_ofSet_of_mem m00] at this; cases this
-- `Iris.Std.LawfulFiniteMap.induction_on` idx 6: necessary (P = False)
theorem w9c2_83 : ¬ drop0% Iris.Std.LawfulFiniteMap.induction_on 6 := fun h =>
  @h Nat Nat TM _ _ (fun _ => False) (fun _ _ _ _ h => h) ∅
-- `Iris.Std.LawfulFiniteMap.induction_on` idx 7: necessary (P m := m = ∅)
theorem w9c2_84 : ¬ drop0% Iris.Std.LawfulFiniteMap.induction_on 7 := fun h =>
  LawfulPartialMap.insert_ne_empty (@h Nat Nat TM _ _ (fun m => m = ∅) rfl (PartialMap.insert (∅ : TM Nat) 0 0))
-- `Iris.Std.LawfulFiniteMap.mem_of_mem_ofList` idx 8: necessary
theorem w9c2_85 : ¬ drop0% Iris.Std.LawfulFiniteMap.mem_of_mem_ofList 8 := fun h => by
  have := @h Nat Nat TM _ _ [] 0 0
  simp at this
-- `Iris.Std.LawfulFiniteMap.toList_delete` idx 7: necessary (m = ∅)
theorem w9c2_86 : ¬ drop0% Iris.Std.LawfulFiniteMap.toList_delete 7 := fun h => by
  have := (@h Nat Nat TM _ ∅ 0 0).length_eq
  rw [LawfulFiniteMap.toList_empty] at this; simp at this
-- `Iris.Std.LawfulFiniteMap.mem_ofList` idx 8: necessary (duplicate key, first entry wins)
theorem w9c2_87 : ¬ drop0% Iris.Std.LawfulFiniteMap.mem_ofList 8 := fun h => by
  have := (@h Nat Nat TM _ _ [(0, 0), (0, 1)] 0 1).mp (by simp)
  rw [LawfulPartialMap.ofList_cons, get?_insert_eq rfl] at this; cases this
-- `Iris.Std.LawfulFiniteMap.ofList_injective` idx 7: necessary
theorem w9c2_88 : ¬ drop0% Iris.Std.LawfulFiniteMap.ofList_injective 7 := fun h => by
  have := (@h Nat Nat TM _ _ [(0, 0), (0, 0)] [(0, 0)] (by decide)
    (by simp only [LawfulPartialMap.ofList_cons, LawfulPartialMap.insert_insert_same])).length_eq
  simp at this
-- `Iris.Std.LawfulFiniteMap.ofList_injective` idx 8: necessary
theorem w9c2_89 : ¬ drop0% Iris.Std.LawfulFiniteMap.ofList_injective 8 := fun h => by
  have := (@h Nat Nat TM _ _ [(0, 0)] [(0, 0), (0, 0)] (by decide)
    (by simp only [LawfulPartialMap.ofList_cons, LawfulPartialMap.insert_insert_same])).length_eq
  simp at this
-- `Iris.Std.LawfulFiniteMap.ofList_injective` idx 9: necessary
theorem w9c2_90 : ¬ drop0% Iris.Std.LawfulFiniteMap.ofList_injective 9 := fun h => by
  have := (@h Nat Nat TM _ _ [] [(0, 0)] (by decide) (by decide)).length_eq
  simp at this

namespace W9c2
open Iris Iris.Std
/-- Mapping values of an association list partially keeps distinct keys distinct. -/
theorem ndk_filterMap {K V W : Type _} (g : V → Option W) : ∀ (l : List (K × V)), NoDupKeys l →
    NoDupKeys (l.filterMap (fun kv => (g kv.2).map (kv.1, ·)))
  | [], _ => by simp [NoDupKeys]
  | (k, v) :: t, h => by
    unfold NoDupKeys at *
    simp only [List.map_cons, List.nodup_cons] at h
    have ih := ndk_filterMap g t h.2
    unfold NoDupKeys at ih
    cases hg : g v with
    | none => simpa [List.filterMap_cons, hg] using ih
    | some w =>
      simp only [List.filterMap_cons, hg, Option.map_some, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => h.1 ?_, ih⟩
      simp only [List.mem_map, List.mem_filterMap, Option.map_eq_some_iff] at hm ⊢
      obtain ⟨⟨k', w'⟩, ⟨⟨k'', v''⟩, hmem, w'', -, he⟩, rfl⟩ := hm
      cases he
      exact ⟨_, hmem, rfl⟩
end W9c2
open Iris Iris.Std W9c2

-- `Iris.Std.LawfulPartialMap.disjoint_insert_left_iff` idx 8: removable (at key i the left side already forces get? m₂ i = none)
theorem w9c2_57 : drop% Iris.Std.LawfulPartialMap.disjoint_insert_left_iff 8 := by
  intro K V M _ m₁ m₂ i x
  refine ⟨fun hd => ⟨?_, fun k ⟨hs1, hs2⟩ => ?_⟩,
    fun ⟨h1, h2⟩ => LawfulPartialMap.disjoint_insert_left h1 h2⟩
  · rcases h : get? m₂ i with _ | _
    · rfl
    · exact absurd (hd i ⟨by simp [get?_insert_eq rfl], by simp [h]⟩) id
  · by_cases hik : i = k
    · subst hik; exact hd i ⟨by simp [get?_insert_eq rfl], hs2⟩
    · exact hd k ⟨by simp [get?_insert_ne hik, hs1], hs2⟩
-- `Iris.Std.LawfulPartialMap.get?_ofList_none` idx 7: removable (induction on L; NoDupKeys unused)
theorem w9c2_78 : drop% Iris.Std.LawfulPartialMap.get?_ofList_none 7 := by
  intro K V M _ k L Hin
  induction L with
  | nil => simp [PartialMap.ofList, get?_empty]
  | cons h t IH =>
    obtain ⟨k', v'⟩ := h
    rw [LawfulPartialMap.ofList_cons]
    by_cases hk : k' = k
    · exact (Hin ⟨v', hk ▸ List.mem_cons_self⟩).elim
    · rw [get?_insert_ne hk]; exact IH (fun ⟨v, hv⟩ => Hin ⟨v, List.mem_cons_of_mem _ hv⟩)
-- `Iris.Std.LawfulFiniteMap.toList_filterMap` idx 6: removable (the right side has distinct keys since toList m has)
theorem w9c2_91 : drop% Iris.Std.LawfulFiniteMap.toList_filterMap 6 := by
  intro K V M _ f m
  refine (List.perm_ext_iff_of_nodup LawfulFiniteMap.nodup_toList ?_).mpr fun ⟨k, v⟩ => ⟨?_, ?_⟩
  · exact LawfulFiniteMap.NoDupKeys_noDup (ndk_filterMap f _ LawfulFiniteMap.toList_noDupKeys)
  · intro H
    refine List.mem_filterMap.mpr ?_
    have H' := LawfulFiniteMap.toList_get.mp H
    simp [LawfulPartialMap.get?_filterMap] at H'
    obtain ⟨v', Ha₁, Ha₂⟩ := Option.bind_eq_some_iff.mp H'
    simp only [Option.map_eq_some_iff]
    exact ⟨(k, v'), LawfulFiniteMap.toList_get.mpr Ha₁, v, Ha₂, rfl⟩
  · intro H
    obtain ⟨a, Ha₁, Ha₂⟩ := List.mem_filterMap.mp H
    refine LawfulFiniteMap.toList_get.mpr ?_
    rw [LawfulPartialMap.get?_filterMap]
    refine Option.bind_eq_some_iff.mpr ?_
    simp at Ha₂
    obtain ⟨H', rfl⟩ := Ha₂
    exact ⟨a.snd, LawfulFiniteMap.toList_get.mp Ha₁, H'⟩

namespace W9c2
/-- Keys with the constant comparison `.eq` (transitive, not `LawfulEq`). -/
structure CE where v : Nat
deriving DecidableEq, Repr
instance : Ord CE := ⟨fun _ _ => .eq⟩
instance ceTrans : Std.TransCmp (compare : CE → CE → Ordering) where
  eq_swap := rfl
  isLE_trans _ _ := rfl
abbrev ct1 : Std.TreeMap CE Nat compare := (∅ : Std.TreeMap CE Nat compare).insert ⟨0⟩ 0
abbrev ct2 : Std.TreeMap CE Nat compare := (∅ : Std.TreeMap CE Nat compare).insert ⟨1⟩ 0

/-- Nat keys ordered naturally except that 5 and 6 lie below 0 (lawful equality, not transitive). -/
structure RC where v : Nat
deriving DecidableEq, Repr
def rcCmp (a b : RC) : Ordering :=
  if a.v = b.v then .eq else
  if (decide (a.v < b.v)) != (decide ((min a.v b.v = 0) ∧ (max a.v b.v = 5 ∨ max a.v b.v = 6))) then .lt else .gt
instance : Ord RC := ⟨rcCmp⟩
instance rcLawful : Std.LawfulEqCmp (compare : RC → RC → Ordering) where
  compare_self {a} := by simp [compare, rcCmp]
  eq_of_compare {a b} h := by
    cases a; cases b
    simp only [compare, rcCmp] at h
    split at h
    · simp_all
    · split at h <;> cases h
abbrev r1 : Std.TreeMap RC Nat compare :=
  ((((∅ : Std.TreeMap RC Nat compare).insert ⟨0⟩ 1).insert ⟨3⟩ 1).insert ⟨7⟩ 1 |>.insert ⟨4⟩ 1).insert ⟨5⟩ 1
abbrev r2 : Std.TreeMap RC Nat compare := (∅ : Std.TreeMap RC Nat compare).insert ⟨6⟩ 2
def tf (k : RC) (a b : Nat) : Nat := 100*k.v + 10*a + b
/-- A badly ordered tree: root key 1 with left child 2. -/
abbrev badT : Std.DTreeMap.Internal.Impl Nat (fun _ => Nat) := .inner 2 1 0 (.inner 1 2 0 .leaf .leaf) .leaf
end W9c2
open W9c2

-- `Std.TreeMap.getElem?_mergeWith'` idx 4: necessary (all keys compare equal; f uses the key)
theorem w9c2_11 : ¬ drop0% Std.TreeMap.getElem?_mergeWith' 4 := fun h =>
  absurd (@h CE Nat _ _ ct1 ct2 (fun k _ _ => k.v) ⟨5⟩) (by decide)
-- `Std.ExtTreeMap.getElem?_mergeWith'` idx 4: necessary (all keys compare equal; f uses the key)
theorem w9c2_12 : ¬ drop0% Std.ExtTreeMap.getElem?_mergeWith' 4 := fun h =>
  absurd (@h CE Nat _ _ (fun k _ _ => k.v) ⟨5⟩ ((∅ : Std.ExtTreeMap CE Nat compare).insert ⟨0⟩ 0)
    ((∅ : Std.ExtTreeMap CE Nat compare).insert ⟨1⟩ 0)) (by decide)
-- `Std.TreeMap.getElem?_mergeWith'` idx 3: necessary (non-transitive order: key 0 is lost by the merge rotation)
theorem w9c2_10 : ¬ drop0% Std.TreeMap.getElem?_mergeWith' 3 := fun h =>
  absurd (@h RC Nat _ _ r1 r2 tf ⟨0⟩) (by decide)
-- `_private.Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_foldl_alter` idx 3: necessary (same non-transitive order)
theorem w9c2_6 : ¬ drop0% _private.Iris.Std.HeapInstances.«0».Std.TreeMap.getElem?_foldl_alter 3 := fun h =>
  absurd (@h RC Nat _ _ ⟨0⟩ tf [(⟨6⟩, 2)] r1 (List.pairwise_singleton _ _)) (by decide)
-- `_private.Iris.Std.HeapInstances.0.Std.TreeMap.get?_foldl_alter_impl_sigma` idx 3: necessary (same non-transitive order)
theorem w9c2_2 : ¬ drop0% _private.Iris.Std.HeapInstances.«0».Std.TreeMap.get?_foldl_alter_impl_sigma 3 := fun h =>
  absurd (@h RC Nat _ _ r1.inner.inner ⟨0⟩ tf [⟨⟨6⟩, 2⟩] r1.inner.wf (List.pairwise_singleton _ _)) (by decide)
-- `_private.Iris.Std.HeapInstances.0.Std.TreeMap.get?_foldl_alter_impl_sigma` idx 9: necessary (badly ordered tree, rebalancing exposes key 2)
theorem w9c2_4 : ¬ drop0% _private.Iris.Std.HeapInstances.«0».Std.TreeMap.get?_foldl_alter_impl_sigma 9 := fun h =>
  absurd (@h Nat Nat _ _ _ badT 2 (fun _ _ b => b) [⟨0, 5⟩] (List.pairwise_singleton _ _)) (by decide)
-- `_private.Iris.Std.HeapInstances.0.Std.TreeMap.get?_foldl_alter_impl_sigma` idx 10: necessary (duplicate key in l)
theorem w9c2_5 : ¬ drop0% _private.Iris.Std.HeapInstances.«0».Std.TreeMap.get?_foldl_alter_impl_sigma 10 := fun h =>
  absurd (@h Nat Nat _ _ _ (∅ : Std.DTreeMap Nat (fun _ => Nat) compare).inner 0 (fun _ _ b => b) [⟨0, 1⟩, ⟨0, 2⟩]
    (∅ : Std.DTreeMap Nat (fun _ => Nat) compare).wf) (by decide)

open Std.DTreeMap.Internal in
-- `_private.Iris.Std.HeapInstances.0.Std.TreeMap.get?_foldl_alter_impl_sigma` idx 4: removable (transitivity suffices where the proof used LawfulEqOrd)
theorem w9c2_3 : drop% _private.Iris.Std.HeapInstances.«0».Std.TreeMap.get?_foldl_alter_impl_sigma 4 := by
  intro K V _ _ init k f l hinit hl
  induction l generalizing init with
  | nil => rfl
  | cons hd tl IH =>
    rcases hd with ⟨a, b⟩
    rw [List.foldl_cons, IH (Impl.WF.constAlter! hinit) hl.tail, Impl.Const.get?_alter! hinit]
    by_cases h : compare a k = .eq
    · have hn : tl.find? (fun x => (compare x.1 k).isEq) = none := by
        refine List.find?_eq_none.mpr fun x hx He => List.rel_of_pairwise_cons hl hx ?_
        rw [Std.TransCmp.eq_trans h (Std.OrientedCmp.eq_symm (Ordering.isEq_iff_eq_eq.mp He))]; rfl
      rw [hn, if_pos h, List.find?_cons_of_pos (by simp [h]), Impl.Const.get?_congr hinit h]
      cases Impl.Const.get? init k <;> rfl
    · rw [if_neg h, List.find?_cons_of_neg (by simp [h])]
-- `_private.Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_foldl_alter` idx 4: removable (transitivity suffices where the proof used LawfulEqOrd)
theorem w9c2_7 : drop% _private.Iris.Std.HeapInstances.«0».Std.TreeMap.getElem?_foldl_alter 4 := by
  intro K V _ _ k f l init hl
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldl_cons, ih hl.tail, Std.TreeMap.getElem?_alter]
    by_cases heq : compare hd.1 k = .eq
    · have htl : tl.find? (fun kv => (compare kv.1 k).isEq) = none := by
        refine List.find?_eq_none.mpr fun kv hkv h => List.rel_of_pairwise_cons hl hkv ?_
        exact Std.TransCmp.eq_trans heq (Std.OrientedCmp.eq_symm (Ordering.isEq_iff_eq_eq.mp h))
      rw [htl, if_pos heq, List.find?_cons_of_pos (by simp [heq]), Std.TreeMap.getElem?_congr heq]
      cases init[k]? <;> rfl
    · rw [if_neg heq, List.find?_cons_of_neg (by simp [heq])]
open Std.DTreeMap.Internal in
-- `_private.Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_mergeWith_eq_foldl` idx 4: removable (both sides are the same tree: mergeWith folds alter over the entries of t₂; no order laws needed)
theorem w9c2_9 : drop% _private.Iris.Std.HeapInstances.«0».Std.TreeMap.getElem?_mergeWith_eq_foldl 4 := by
  intro K V _ _ t₁ t₂ f k
  show Impl.Const.get? (Impl.Const.mergeWith f t₁.inner.inner t₂.inner.inner t₁.inner.wf.balanced).impl k = Impl.Const.get? _ k
  rw [Impl.Const.mergeWith, Impl.foldl_eq_foldl]
  show _ = Impl.Const.get? (List.foldl _ t₁ (Impl.Const.toList t₂.inner.inner)).inner.inner k
  rw [Impl.Const.toList_eq_toListModel_map]
  generalize t₂.inner.inner.toListModel = L
  induction L generalizing t₁ with
  | nil => rfl
  | cons p tl ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons]
    refine Eq.trans ?_ (ih (t₁ := t₁.alter p.1 (Option.insertOrMerge (f p.1) p.2)))
    congr 3
    show Impl.BalancedTree.mk _ _ = Impl.BalancedTree.mk _ _
    congr 1
    show _ = (Impl.Const.alter p.1 _ t₁.inner.inner _).impl
    congr 2; funext o; cases o <;> rfl
open Std.DTreeMap.Internal in
-- `_private.Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_mergeWith_eq_foldl` idx 3: removable (both sides are the same tree: mergeWith folds alter over the entries of t₂; no order laws needed)
theorem w9c2_8 : drop% _private.Iris.Std.HeapInstances.«0».Std.TreeMap.getElem?_mergeWith_eq_foldl 3 := by
  intro K V _ _ t₁ t₂ f k
  show Impl.Const.get? (Impl.Const.mergeWith f t₁.inner.inner t₂.inner.inner t₁.inner.wf.balanced).impl k = Impl.Const.get? _ k
  rw [Impl.Const.mergeWith, Impl.foldl_eq_foldl]
  show _ = Impl.Const.get? (List.foldl _ t₁ (Impl.Const.toList t₂.inner.inner)).inner.inner k
  rw [Impl.Const.toList_eq_toListModel_map]
  generalize t₂.inner.inner.toListModel = L
  induction L generalizing t₁ with
  | nil => rfl
  | cons p tl ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons]
    refine Eq.trans ?_ (ih (t₁ := t₁.alter p.1 (Option.insertOrMerge (f p.1) p.2)))
    congr 3
    show Impl.BalancedTree.mk _ _ = Impl.BalancedTree.mk _ _
    congr 1
    show _ = (Impl.Const.alter p.1 _ t₁.inner.inner _).impl
    congr 2; funext o; cases o <;> rfl
open Std.DTreeMap.Internal in
-- `Iris.Std.insert_eq_singleton_union_extTreeSet` idx 3: removable (set insert is insertIfNew and the union of a one-element set into a nonempty set is insertIfNew; true for any TransCmp)
theorem w9c2_1 : drop% Iris.Std.insert_eq_singleton_union_extTreeSet 3 := by
  intro α cmp _ ps p
  rcases ps with ⟨⟨⟨q⟩⟩⟩
  induction q using Quotient.ind with | _ d => ?_
  show (⟨⟨⟨Quotient.mk _ (d.insertIfNew p ())⟩⟩⟩ : Std.ExtTreeSet α cmp) =
    ⟨⟨⟨Quotient.mk _ (((∅ : Std.DTreeMap α (fun _ => Unit) cmp).insertIfNew p ()) ∪ d)⟩⟩⟩
  congr 4
  rcases d with ⟨t, wf⟩
  show Std.DTreeMap.mk _ _ = Std.DTreeMap.mk _ _
  congr 1
  letI : Ord α := ⟨cmp⟩
  show _ = Impl.union (Impl.inner 1 p () .leaf .leaf) t _ _
  unfold Impl.union
  split
  · rfl
  · rename_i hs
    cases t with
    | leaf => rfl
    | inner sz k v l r =>
      exfalso; apply hs
      have hb := wf.balanced
      cases hb with
      | inner _ _ _ hsz => simp only [Impl.size] at hsz ⊢; omega
