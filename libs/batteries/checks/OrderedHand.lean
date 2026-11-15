import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init
import Batteries.Data.OrderedAssocList
import Batteries.Data.BinomialHeap.Lemmas
import Batteries.Data.PairingHeap

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
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

open Batteries
noncomputable instance HypCheckDec.ltHeadKey {α β} (cmp : α → α → Ordering) (a : α)
    (t : Batteries.AssocList α β) : Decidable (Batteries.AssocList.LTHeadKey cmp a t) :=
  match t with
  | .nil => isTrue trivial
  | .cons x _ _ => (inferInstance : Decidable (cmp a x = .lt))
noncomputable instance HypCheckDec.keysOrdered {α β} (cmp : α → α → Ordering) (t : Batteries.AssocList α β) :
    Decidable (Batteries.AssocList.KeysOrdered cmp t) :=
  Batteries.AssocList.rec (motive := fun t => Decidable (Batteries.AssocList.KeysOrdered cmp t))
    (isTrue trivial)
    (fun a _ t ih => @instDecidableAnd (Batteries.AssocList.LTHeadKey cmp a t) _ inferInstance ih) t
noncomputable instance HypCheckDec.olLTHeadKey {α β} (cmp : α → α → Ordering) (a : α)
    (l : Batteries.OrderedAssocList cmp β) : Decidable (l.LTHeadKey a) :=
  HypCheckDec.ltHeadKey cmp a l.toAssocList
noncomputable instance HypCheckDec.pairingNoSibling {α} (s : Batteries.PairingHeapImp.Heap α) :
    Decidable s.NoSibling :=
  match s with
  | .nil => isTrue .nil
  | .node a c .nil => isTrue (.node a c)
  | .node _ _ (.node _ _ _) => isFalse (fun h => by cases h)

-- Ordered cluster (wave W1): OrderedAssocList, BinomialHeap, PairingHeap hypotheses.

open Batteries Batteries.AssocList

-- cyclic comparison on Fin 3: oriented and lawful-eq, not transitive
def cyc3 : Fin 3 → Fin 3 → Ordering := fun a b => if a = b then .eq else if b = a + 1 then .lt else .gt
instance : Std.LawfulEqCmp cyc3 where
  compare_self {a} := by revert a; decide
  eq_of_compare {a b} := by revert a b; decide
instance : Std.OrientedCmp cyc3 where
  eq_swap {a b} := by revert a b; decide
theorem cyc3_not_trans : ¬ Std.TransCmp cyc3 := fun h =>
  absurd (h.isLE_trans (a := 0) (b := 1) (c := 2) rfl rfl) (by decide)

-- compare halves on Fin 4: transitive, not lawful-eq
def half4 : Fin 4 → Fin 4 → Ordering := fun a b => compare (a.val / 2) (b.val / 2)
instance : Std.TransCmp half4 where
  eq_swap {a b} := by revert a b; decide
  isLE_trans {a b c} := by revert a b c; decide

-- lawful-eq, not oriented
def cmpG : Fin 2 → Fin 2 → Ordering := fun a b => if a = b then .eq else .gt
instance : Std.LawfulEqCmp cmpG where
  compare_self {a} := by revert a; decide
  eq_of_compare {a b} := by revert a b; decide

-- oriented, neither lawful-eq (0 ~ 2) nor transitive
def cmpX : Fin 4 → Fin 4 → Ordering := fun a b =>
  if a = b then .eq else if a = 0 then (if b = 2 then .eq else .gt)
  else if b = 0 then (if a = 2 then .eq else .lt) else compare a.val b.val
instance : Std.OrientedCmp cmpX where
  eq_swap {a b} := by revert a b; decide

-- always `.gt` on Fin 1: not reflexive
def cmpGt : Fin 1 → Fin 1 → Ordering := fun _ _ => .gt

-- the lawful order on Fin 3
def natc : Fin 3 → Fin 3 → Ordering := fun a b => compare a.val b.val
instance : Std.TransCmp natc where
  eq_swap {a b} := by revert a b; decide
  isLE_trans {a b c} := by revert a b c; decide
instance : Std.LawfulEqCmp natc where
  compare_self {a} := by revert a; decide
  eq_of_compare {a b} := by revert a b; decide

-- Nat ≤ as a Bool relation (total)
def leN : Nat → Nat → Bool := fun a b => decide (a ≤ b)
instance : TotalBLE leN := ⟨fun {a b} => by simp only [leN, decide_eq_true_eq]; omega⟩

instance hcLEHead {α β γ} (cmp : α → α → Ordering) (s : Batteries.AssocList α β) (t : Batteries.AssocList α γ) :
    Decidable (LEHeadKey cmp s t) := by
  unfold LEHeadKey; split <;> infer_instance


abbrev L3 : Batteries.AssocList (Fin 3) Nat := cons 0 0 (cons 1 0 (cons 2 0 nil))

-- `Batteries.AssocList.keysOrdered_iff_pairwise`
theorem c1 : ¬ drop0% Batteries.AssocList.keysOrdered_iff_pairwise 3 := fun H =>
  absurd ((@H (Fin 3) Nat cyc3 L3).mp (by decide)) (by decide)

-- `Batteries.AssocList.KeysOrdered.lt_of_mem`
theorem c2 : ¬ drop0% Batteries.AssocList.KeysOrdered.lt_of_mem 3 := fun H =>
  absurd (@H (Fin 3) Nat cyc3 0 0 (cons 1 0 (cons 2 0 nil)) (by decide) (2, 0) (by decide)) (by decide)

-- `Batteries.AssocList.leHeadKey_cons`
theorem c3 : ¬ drop0% Batteries.AssocList.leHeadKey_cons 8 := fun H =>
  absurd (@H (Fin 3) cyc3 0 Nat 0 (cons 1 0 nil) Nat (cons 2 0 nil) (by decide) (by decide)) (by decide)

-- `Batteries.AssocList.leHeadKey_cons`
theorem c4 : ¬ drop0% Batteries.AssocList.leHeadKey_cons 9 := fun H =>
  absurd (@H (Fin 3) natc 2 Nat 0 (cons 1 0 nil) Nat (cons 1 0 nil) inferInstance (by decide)) (by decide)

-- `Batteries.AssocList.KeysOrdered.orderedInsert_aux`
theorem c5 : ¬ drop0% Batteries.AssocList.KeysOrdered.orderedInsert_aux 5 := fun H =>
  absurd (@H (Fin 4) cmpX 0 Nat 0 inferInstance 1 0 (cons 2 0 (cons 3 0 nil)) (by decide) (by decide))
    (by decide)

-- `Batteries.AssocList.KeysOrdered.orderedInsert_aux`
theorem c6 : ¬ drop0% Batteries.AssocList.KeysOrdered.orderedInsert_aux 6 := fun H =>
  absurd (@H (Fin 2) cmpG 1 Nat 0 inferInstance 0 0 nil (by decide) (by decide)) (by decide)

-- `Batteries.AssocList.KeysOrdered.orderedInsert`
theorem c7 : ¬ drop0% Batteries.AssocList.KeysOrdered.orderedInsert 6 := fun H =>
  absurd (@H (Fin 4) cmpX Nat (cons 2 0 (cons 3 0 nil)) 0 0 inferInstance (by decide)) (by decide)

-- `Batteries.AssocList.KeysOrdered.orderedInsert`
theorem c8 : ¬ drop0% Batteries.AssocList.KeysOrdered.orderedInsert 7 := fun H =>
  absurd (@H (Fin 2) cmpG Nat (cons 0 0 nil) 1 0 inferInstance (by decide)) (by decide)

-- `Batteries.AssocList.leHeadKey_filterMapVal`
theorem c9 : ¬ drop0% Batteries.AssocList.leHeadKey_filterMapVal 6 := fun H =>
  absurd (@H (Fin 1) cmpGt Nat (cons 0 0 nil) Nat (fun _ b => some b) (by decide)) (by decide)

-- `Batteries.AssocList.leHeadKey_filterMapVal`
theorem c10 : ¬ drop0% Batteries.AssocList.leHeadKey_filterMapVal 7 := fun H =>
  absurd (@H (Fin 3) natc Nat (cons 1 0 (cons 0 0 nil)) Nat (fun a b => if a = 1 then none else some b)
    inferInstance) (by decide)

-- `Batteries.AssocList.KeysOrdered.filterMapVal`
theorem c11 : ¬ drop0% Batteries.AssocList.KeysOrdered.filterMapVal 6 := fun H =>
  absurd (@H (Fin 3) cyc3 Nat L3 Nat (fun a b => if a = 1 then none else some b) (by decide)) (by decide)

-- `Batteries.AssocList.ltHeadKey_orderedMerge`
theorem c12 : ¬ drop0% Batteries.AssocList.ltHeadKey_orderedMerge 9 := fun H =>
  absurd (@H (Fin 3) cyc3 0 Nat (cons 1 0 (cons 2 0 nil)) Nat nil Nat
    (fun a x _ => if a = 1 then none else x) (by decide) (by decide) (by decide) (by decide))
    (by decide +kernel)

-- `Batteries.AssocList.ltHeadKey_orderedMerge`
theorem c13 : ¬ drop0% Batteries.AssocList.ltHeadKey_orderedMerge 12 := fun H =>
  absurd (@H (Fin 3) natc 0 Nat (cons 1 0 (cons 0 0 nil)) Nat nil Nat
    (fun a x _ => if a = 1 then none else x) inferInstance (by decide) (by decide) (by decide))
    (by decide +kernel)

-- `Batteries.AssocList.ltHeadKey_orderedMerge`
theorem c14 : ¬ drop0% Batteries.AssocList.ltHeadKey_orderedMerge 13 := fun H =>
  absurd (@H (Fin 3) natc 0 Nat nil Nat (cons 1 0 (cons 0 0 nil)) Nat
    (fun a _ y => if a = 1 then none else y) inferInstance (by decide) (by decide) (by decide))
    (by decide +kernel)

-- `Batteries.AssocList.KeysOrdered.orderedMerge`
theorem c15 : ¬ drop0% Batteries.AssocList.KeysOrdered.orderedMerge 9 := fun H =>
  absurd (@H (Fin 3) cyc3 Nat L3 Nat nil Nat (fun a x _ => if a = 1 then none else x) inferInstance
    (by decide) (by decide)) (by decide +kernel)

-- `Batteries.AssocList.orderedFind?_filterMapVal`
theorem c16 : ¬ drop0% Batteries.AssocList.orderedFind?_filterMapVal 7 := fun H =>
  absurd (@H (Fin 3) Nat Nat (fun a b => if a = 0 then none else some b) 2 cyc3 inferInstance L3
    (by decide)) (by decide)

-- `Batteries.AssocList.orderedFind?_filterMapVal`
theorem c17 : ¬ drop0% Batteries.AssocList.orderedFind?_filterMapVal 9 := fun H =>
  absurd (@H (Fin 3) Nat Nat (fun a b => if a = 1 then none else some b) 0 natc inferInstance
    inferInstance (cons 1 0 (cons 0 0 nil))) (by decide)

-- `Batteries.AssocList.ext_orderedFind?`
theorem c18 : ¬ drop0% Batteries.AssocList.ext_orderedFind? 3 := fun H =>
  absurd (congrArg toList (@H (Fin 4) Nat half4 inferInstance (cons 0 0 nil) (cons 1 0 nil)
    (by decide) (by decide) (by decide))) (by decide)

-- `Batteries.AssocList.ext_orderedFind?`
theorem c19 : ¬ drop0% Batteries.AssocList.ext_orderedFind? 4 := fun H =>
  absurd (congrArg toList (@H (Fin 3) Nat cyc3 inferInstance L3 (cons 0 0 (cons 1 0 nil))
    (by decide) (by decide) (by decide))) (by decide)

-- `Batteries.AssocList.ext_orderedFind?`
theorem c20 : ¬ drop0% Batteries.AssocList.ext_orderedFind? 7 := fun H =>
  absurd (congrArg toList (@H (Fin 3) Nat natc inferInstance inferInstance (cons 0 0 (cons 0 0 nil))
    (cons 0 0 nil) (by decide) (by decide))) (by decide)

-- `Batteries.AssocList.ext_orderedFind?`
theorem c21 : ¬ drop0% Batteries.AssocList.ext_orderedFind? 8 := fun H =>
  absurd (congrArg toList (@H (Fin 3) Nat natc inferInstance inferInstance (cons 0 0 nil)
    (cons 0 0 (cons 0 0 nil)) (by decide) (by decide))) (by decide)


-- `Batteries.OrderedAssocList.ext_iff`
theorem c22 : ¬ drop0% Batteries.OrderedAssocList.ext_iff 3 := fun H =>
  absurd (congrArg (·.toAssocList.toList) ((@H (Fin 4) half4 Nat inferInstance
    ⟨cons 0 0 nil, keysOrdered_cons_nil⟩ ⟨cons 1 0 nil, keysOrdered_cons_nil⟩).mpr (by decide)))
    (by decide)

-- `Batteries.OrderedAssocList.ext`
theorem c23 : ¬ drop0% Batteries.OrderedAssocList.ext 3 := fun H =>
  absurd (congrArg (·.toAssocList.toList) (@H (Fin 4) half4 Nat inferInstance
    ⟨cons 0 0 nil, keysOrdered_cons_nil⟩ ⟨cons 1 0 nil, keysOrdered_cons_nil⟩ (by decide)))
    (by decide)

-- `Batteries.OrderedAssocList.ext_iff`
theorem c24 : ¬ drop0% Batteries.OrderedAssocList.ext_iff 4 := fun H =>
  absurd (congrArg (·.toAssocList.toList) ((@H (Fin 3) cyc3 Nat inferInstance
    ⟨L3, by decide⟩ ⟨cons 0 0 (cons 1 0 nil), by decide⟩).mpr (by decide)))
    (by decide)

-- `Batteries.OrderedAssocList.ext`
theorem c25 : ¬ drop0% Batteries.OrderedAssocList.ext 4 := fun H =>
  absurd (congrArg (·.toAssocList.toList) (@H (Fin 3) cyc3 Nat inferInstance
    ⟨L3, by decide⟩ ⟨cons 0 0 (cons 1 0 nil), by decide⟩ (by decide)))
    (by decide)

-- `Batteries.OrderedAssocList.toAssocList_merge_mk_cons_mk_cons`
theorem c26 : ¬ indep0% _private.Batteries.Data.OrderedAssocList.«0».Batteries.OrderedAssocList.toAssocList_merge_mk_cons_mk_cons 3 :=
  fun H => cyc3_not_trans (@H (Fin 3) cyc3 inferInstance Nat Nat Nat (fun _ _ _ => none)
    0 0 nil keysOrdered_cons_nil 0 0 nil keysOrdered_cons_nil)

-- `Batteries.OrderedAssocList.merge_mk_cons_mk_cons`
theorem c27 : ¬ indep0% _private.Batteries.Data.OrderedAssocList.«0».Batteries.OrderedAssocList.merge_mk_cons_mk_cons 3 :=
  fun H => cyc3_not_trans (@H (Fin 3) cyc3 inferInstance Nat Nat Nat
    0 0 nil keysOrdered_cons_nil 0 0 nil keysOrdered_cons_nil (fun _ _ _ => none))

-- `Batteries.OrderedAssocList.merge_assoc`
theorem c28 : ¬ indep0% Batteries.OrderedAssocList.merge_assoc 3 :=
  fun H => cyc3_not_trans (@H (Fin 3) cyc3 inferInstance Nat Nat Nat Nat Nat Nat
    (fun _ _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)
    .nil .nil .nil)

-- `Batteries.OrderedAssocList.merge_comm`
theorem c29 : ¬ drop0% Batteries.OrderedAssocList.merge_comm 10 := fun H =>
  absurd (congrArg (·.toAssocList.toList) (@H (Fin 3) natc inferInstance inferInstance Nat Nat Nat
    (fun _ x _ => x) (fun _ _ _ => none) (fun _ => rfl)
    ⟨cons 0 0 nil, keysOrdered_cons_nil⟩ .nil)) (by decide +kernel)

-- `Batteries.OrderedAssocList.merge_assoc`
theorem c30 : ¬ drop0% Batteries.OrderedAssocList.merge_assoc 14 := fun H =>
  absurd (congrArg (·.toAssocList.toList) (@H (Fin 3) natc inferInstance inferInstance
    Unit Unit Bool Unit Unit Unit
    (fun _ x y => some (x.isSome || y.isSome))
    (fun _ u z => match u with | some true => some () | some false => z | none => none)
    (fun _ y z => if y.isSome || z.isSome then some () else none)
    (fun _ x v => if x.isSome || v.isSome then some () else none)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (by intro a x y z; cases x <;> cases y <;> cases z <;> rfl)
    .nil .nil ⟨cons 0 () nil, keysOrdered_cons_nil⟩)) (by decide +kernel)

-- `Batteries.OrderedAssocList.merge_assoc`
theorem c31 : ¬ drop0% Batteries.OrderedAssocList.merge_assoc 16 := fun H =>
  absurd (congrArg (·.toAssocList.toList) (@H (Fin 3) natc inferInstance inferInstance
    Unit Unit Unit Unit Unit Bool
    (fun _ x y => if x.isSome || y.isSome then some () else none)
    (fun _ u z => if u.isSome || z.isSome then some () else none)
    (fun _ y z => some (y.isSome || z.isSome))
    (fun _ x v => match v with | some true => some () | some false => x | none => none)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (by intro a x y z; cases x <;> cases y <;> cases z <;> rfl)
    ⟨cons 0 () nil, keysOrdered_cons_nil⟩ .nil .nil)) (by decide +kernel)

-- `Batteries.OrderedAssocList.merge_assoc`
theorem c32 : ¬ drop0% Batteries.OrderedAssocList.merge_assoc 18 := fun H =>
  absurd (congrArg (·.toAssocList.toList) (@H (Fin 3) natc inferInstance inferInstance
    Unit Unit Unit Unit Unit Unit
    (fun _ _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none) (fun _ x _ => x)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    ⟨cons 0 () nil, keysOrdered_cons_nil⟩ .nil .nil)) (by decide +kernel)

open Batteries

namespace HCP
open Batteries.PairingHeapImp
/-- Bool check of pairing-heap node well-formedness for `leN`. -/
def nwfB (a : Nat) : Heap Nat → Bool
  | .nil => true
  | .node b c s => leN a b && nwfB b c && nwfB a s
theorem nwfB_of {a : Nat} {s : Heap Nat} (h : Heap.NodeWF leN a s) : nwfB a s = true := by
  induction s generalizing a with
  | nil => rfl
  | node b c s ihc ihs =>
    obtain ⟨h1, h2, h3⟩ := h
    simp only [nwfB, Bool.and_eq_true]
    exact ⟨⟨h1, ihc h2⟩, ihs h3⟩
def wfB : Heap Nat → Bool
  | .nil => true
  | .node a c .nil => nwfB a c
  | _ => false
theorem wfB_of {s : Heap Nat} (h : Heap.WF leN s) : wfB s = true := by
  cases h with
  | nil => rfl
  | node h => exact nwfB_of h
/-- A pairing heap that violates the heap order for `leN`. -/
abbrev B : Heap Nat := .node 1 (.node 0 .nil .nil) .nil
end HCP
open HCP

-- `Batteries.PairingHeapImp.Heap.WF.merge_node`
theorem c33 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.merge_node 8 := fun H =>
  absurd (wfB_of (@H Nat leN 1 (.node 0 .nil .nil) 2 .nil .nil .nil trivial)) (by decide)

-- `Batteries.PairingHeapImp.Heap.WF.merge_node`
theorem c34 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.merge_node 9 := fun H =>
  absurd (wfB_of (@H Nat leN 2 .nil 1 (.node 0 .nil .nil) .nil .nil trivial)) (by decide)

-- `Batteries.PairingHeapImp.Heap.WF.merge`
theorem c35 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.merge 4 := fun H =>
  absurd (wfB_of (@H Nat leN B .nil .nil)) (by decide)

-- `Batteries.PairingHeapImp.Heap.WF.merge`
theorem c36 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.merge 5 := fun H =>
  absurd (wfB_of (@H Nat leN .nil B .nil)) (by decide)

-- `Batteries.PairingHeapImp.Heap.WF.combine`
theorem c37 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.combine 4 := fun H =>
  absurd (wfB_of (@H Nat leN B 0)) (by decide)

-- `Batteries.PairingHeapImp.Heap.WF.deleteMin`
theorem c38 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.deleteMin 5 := fun H =>
  absurd (wfB_of (@H Nat leN 5 B (.node 5 B .nil) rfl)) (by decide)

-- `Batteries.PairingHeapImp.Heap.WF.deleteMin`
theorem c39 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.deleteMin 6 := fun H =>
  absurd (wfB_of (@H Nat leN 0 B (.node 0 .nil .nil) (.node trivial))) (by decide)

-- `Batteries.PairingHeapImp.Heap.WF.tail?`
theorem c40 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.tail? 4 := fun H =>
  absurd (wfB_of (@H Nat (.node 5 B .nil) leN B rfl)) (by decide)

-- `Batteries.PairingHeapImp.Heap.WF.tail?`
theorem c41 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.tail? 5 := fun H =>
  absurd (wfB_of (@H Nat .nil leN B .nil)) (by decide)

-- `Batteries.PairingHeapImp.Heap.WF.tail`
theorem c42 : ¬ drop0% Batteries.PairingHeapImp.Heap.WF.tail 3 := fun H =>
  absurd (wfB_of (@H Nat (.node 5 B .nil) leN)) (by decide)

open Batteries

namespace HCB
open Batteries.BinomialHeap.Imp
/-- The always-true Bool relation. -/
abbrev leT : Nat → Nat → Bool := fun _ _ => true
/-- A binomial heap whose rank-1 tree has no children. -/
abbrev BB : Heap Nat := .cons 1 0 .nil .nil
/-- Two singleton trees with ranks 0 and 1. -/
abbrev S2 : Heap Nat := .cons 0 0 .nil (.cons 1 0 .nil .nil)
theorem bb_bad {n : Nat} : ¬ Heap.WF leT n BB := fun h => Nat.succ_ne_zero 0 h.2.1
theorem s2_del : Heap.deleteMin leT S2 = some (0, BB) := by
  simp only [Heap.deleteMin, Heap.findMin, HeapNode.toHeap]
  show some (0, Heap.merge leT .nil _) = _
  rw [Heap.merge]; simp
end HCB
open HCB

-- `Batteries.BinomialHeap.Imp.Heap.WF.of_rankGT`
theorem c43 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.of_rankGT 5 := fun H =>
  absurd (@H Nat leT 0 (.cons 0 0 .nil .nil) 0 ⟨Nat.le_refl _, rfl, trivial⟩).1 (by decide)

-- `Batteries.BinomialHeap.Imp.Heap.WF.of_rankGT`
theorem c44 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.of_rankGT 6 := fun H =>
  bb_bad (@H Nat leT 0 BB 0 (by decide))

-- `Batteries.BinomialHeap.Imp.Heap.WF.of_le`
theorem c45 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.of_le 5 := fun H =>
  absurd (@H 1 0 Nat leT (.cons 0 0 .nil .nil) ⟨Nat.le_refl _, rfl, trivial⟩).1 (by decide)

-- `Batteries.BinomialHeap.Imp.Heap.WF.of_le`
theorem c46 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.of_le 6 := fun H =>
  bb_bad (@H 0 0 Nat leT BB (Nat.le_refl 0))

-- `Batteries.BinomialHeap.Imp.Heap.WF.merge'`
theorem c47 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.merge' 5 := fun H => by
  have := (@H Nat leT BB .nil 0 trivial).1
  rw [Batteries.BinomialHeap.Imp.Heap.merge] at this
  all_goals first | exact bb_bad this | exact fun h => nomatch h

-- `Batteries.BinomialHeap.Imp.Heap.WF.merge'`
theorem c48 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.merge' 6 := fun H => by
  have := (@H Nat leT .nil BB 0 trivial).1
  rw [Batteries.BinomialHeap.Imp.Heap.merge] at this
  all_goals first | exact bb_bad this | exact fun h => nomatch h

-- `Batteries.BinomialHeap.Imp.Heap.WF.merge`
theorem c49 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.merge 5 := fun H => by
  have := @H Nat leT BB .nil 0 trivial
  rw [Batteries.BinomialHeap.Imp.Heap.merge] at this
  all_goals first | exact bb_bad this | exact fun h => nomatch h

-- `Batteries.BinomialHeap.Imp.Heap.WF.merge`
theorem c50 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.merge 6 := fun H => by
  have := @H Nat leT .nil BB 0 trivial
  rw [Batteries.BinomialHeap.Imp.Heap.merge] at this
  all_goals first | exact bb_bad this | exact fun h => nomatch h

-- `Batteries.BinomialHeap.Imp.HeapNode.WF.toHeap`
theorem c51 : ¬ drop0% Batteries.BinomialHeap.Imp.HeapNode.WF.toHeap 5 := fun H =>
  absurd (show (2 - 1 : Nat) = 0 from (@H Nat leT 0 0 (.node 0 .nil (.node 0 .nil .nil))).2.2.2.1) (by decide)

-- `HeapNode.WF.toHeap.go`
theorem c52 : ¬ drop0% _private.Batteries.Data.BinomialHeap.Basic.«0».Batteries.BinomialHeap.Imp.HeapNode.WF.toHeap.go 6 :=
  fun H => absurd (show (2 - 1 : Nat) = 0 from
    (@H Nat leT 0 .nil 0 (.node 0 .nil (.node 0 .nil .nil)) trivial).2.2.2.1) (by decide)

-- `HeapNode.WF.toHeap.go`
theorem c53 : ¬ drop0% _private.Batteries.Data.BinomialHeap.Basic.«0».Batteries.BinomialHeap.Imp.HeapNode.WF.toHeap.go 7 :=
  fun H => bb_bad (@H Nat leT 0 BB 0 .nil rfl)

-- `Batteries.BinomialHeap.Imp.FindMin.WF.before`
theorem c54 : ¬ drop0% Batteries.BinomialHeap.Imp.FindMin.WF.before 5 := fun H =>
  bb_bad (@H Nat leT ⟨id, 0, .nil, .nil⟩ ⟨0, fun h => h, rfl, trivial⟩ BB)

-- `Batteries.BinomialHeap.Imp.Heap.WF.deleteMin`
theorem c55 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.deleteMin 6 := fun H =>
  bb_bad (@H Nat leT 0 0 BB S2 s2_del)

-- `Batteries.BinomialHeap.Imp.Heap.WF.deleteMin`
theorem c56 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.deleteMin 7 := fun H =>
  bb_bad (@H Nat leT 0 0 BB .nil trivial)

-- `Batteries.BinomialHeap.Imp.Heap.WF.tail?`
theorem c57 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.tail? 5 := fun H =>
  bb_bad (@H Nat S2 leT 0 BB (by simp [Batteries.BinomialHeap.Imp.Heap.tail?, s2_del]))

-- `Batteries.BinomialHeap.Imp.Heap.WF.tail?`
theorem c58 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.tail? 6 := fun H =>
  bb_bad (@H Nat .nil leT 0 BB trivial)

-- `Batteries.BinomialHeap.Imp.Heap.WF.tail`
theorem c59 : ¬ drop0% Batteries.BinomialHeap.Imp.Heap.WF.tail 4 := fun H => by
  have := @H Nat S2 leT 0
  simp only [Batteries.BinomialHeap.Imp.Heap.tail, Batteries.BinomialHeap.Imp.Heap.tail?, s2_del,
    Option.map_some, Option.getD_some] at this
  exact bb_bad this

-- `Heap.realSize_findMin`
theorem c60 : ¬ drop0% _private.Batteries.Data.BinomialHeap.Basic.«0».Batteries.BinomialHeap.Imp.Heap.realSize_findMin 9 :=
  fun H => by
    obtain ⟨m, -, hm⟩ := @H Nat id 0 leT ⟨id, 0, .nil, .nil⟩ .nil 0 (fun _ => (Nat.zero_add _).symm) rfl
    all_goals simp [Batteries.BinomialHeap.Imp.Heap.findMin] at hm

-- `Heap.realSize_findMin`
theorem c61 : ¬ drop0% _private.Batteries.Data.BinomialHeap.Basic.«0».Batteries.BinomialHeap.Imp.Heap.realSize_findMin 8 :=
  fun H => by
    obtain ⟨m, h1, h2⟩ := @H Nat (fun s => .cons 0 0 .nil s) 1 (fun _ _ => false) ⟨id, 0, .nil, .nil⟩
      (.cons 0 0 .nil .nil) 1 (fun s => by simp) (Exists.intro 0 ⟨fun s => by simp, rfl⟩)
    have h3 := h1 .nil
    all_goals simp [Batteries.BinomialHeap.Imp.Heap.findMin] at h2 h3
    all_goals omega

-- `Heap.realSize_findMin`
theorem c62 : ¬ drop0% _private.Batteries.Data.BinomialHeap.Basic.«0».Batteries.BinomialHeap.Imp.Heap.realSize_findMin 7 :=
  fun H => by
    obtain ⟨m, h1, h2⟩ := @H Nat (fun _ => .nil) 1 (fun _ _ => false) ⟨id, 0, .nil, .nil⟩
      (.cons 0 0 .nil .nil) 0 rfl (Exists.intro 0 ⟨fun s => by simp, rfl⟩)
    have h3 := h1 BB
    all_goals simp [Batteries.BinomialHeap.Imp.Heap.findMin] at h2 h3
    all_goals omega

open Batteries Batteries.AssocList Std

namespace HCO
/-- Composition of `filterMapVal`s, for any list and no comparison at all. -/
theorem fmv_fmv {α β γ δ : Type _} {f : α → γ → Option δ} {g : α → β → Option γ} (l : Batteries.AssocList α β) :
    filterMapVal f (filterMapVal g l) = filterMapVal (fun a b => (g a b).bind (fun c => f a c)) l := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    rw [filterMapVal_cons g, filterMapVal_cons (fun a b => (g a b).bind (fun c => f a c))]
    cases g k v with
    | none => simpa using ih
    | some c => cases hf : f k c <;> simp [filterMapVal_cons, hf, ih]

/-- `orderedFind?` after `orderedInsert` of the same key, for any reflexive comparison and any list. -/
theorem ofi_self {α β : Type _} {cmp : α → α → Ordering} [ReflCmp cmp] (l : Batteries.AssocList α β) (a : α) (b : β) :
    (orderedInsert cmp l a b).orderedFind? cmp a = some b := by
  induction l with
  | nil => simp [orderedInsert, orderedFind?, ReflCmp.compare_self]
  | cons k v t ih =>
    rw [orderedInsert_cons]
    split <;> rename_i w <;> simp [orderedFind?, ReflCmp.compare_self, w, ih]

/-- `orderedFind?` after `orderedInsert`, for any transitive comparison and any list. -/
theorem ofi {α β : Type _} {cmp : α → α → Ordering} [TransCmp cmp] (l : Batteries.AssocList α β) (a : α) (b : β)
    (x : α) : (orderedInsert cmp l a b).orderedFind? cmp x =
      if cmp x a = .eq then some b else l.orderedFind? cmp x := by
  induction l with
  | nil => cases h : cmp x a <;> simp [orderedInsert, orderedFind?, h]
  | cons k v t ih =>
    rw [orderedInsert_cons]
    split <;> rename_i w
    · cases h : cmp x a
      · have := TransCmp.lt_trans h w
        simp [orderedFind?, h, this]
      · simp [orderedFind?, h]
      · simp [orderedFind?, h]
    · cases h : cmp x a
      · have := TransCmp.lt_of_lt_of_eq h w
        simp [orderedFind?, h, this]
      · simp [orderedFind?, h]
      · have := TransCmp.gt_of_gt_of_eq h w
        simp [orderedFind?, h, this]
    · have w' := OrientedCmp.lt_of_gt w
      cases h : cmp x k
      · have := TransCmp.lt_trans h w'
        simp [orderedFind?, h, this]
      · have := TransCmp.lt_of_eq_of_lt h w'
        simp [orderedFind?, h, this]
      · simp [orderedFind?, h, ih]

/-- `KeysOrdered.orderedMerge` without `LawfulEqCmp`. -/
theorem kom {α β γ δ : Type _} {cmp : α → α → Ordering} {f : α → Option β → Option γ → Option δ}
    [TransCmp cmp] {l₁ : Batteries.AssocList α β} {l₂ : Batteries.AssocList α γ}
    (h₁ : KeysOrdered cmp l₁) (h₂ : KeysOrdered cmp l₂) :
    KeysOrdered cmp (AssocList.orderedMerge cmp f l₁ l₂) := by
  match l₁, l₂ with
  | .nil, .nil => rw [AssocList.orderedMerge]; trivial
  | .nil, .cons a₂ g t₂ =>
    rw [AssocList.orderedMerge]
    exact h₂.filterMapVal
  | .cons a₁ b t₁, .nil =>
    rw [AssocList.orderedMerge]
    exact h₁.filterMapVal
  | .cons a₁ b t₁, .cons a₂ g t₂ =>
    rw [AssocList.orderedMerge]
    match h : cmp a₁ a₂ with
    | .lt => match (f a₁ (some b) none) with
      | some d =>
        apply KeysOrdered.cons
        · apply ltHeadKey_orderedMerge h₁.ltHeadKey (ltHeadKey_cons.mpr h)
            h₁.tail h₂
        · exact kom h₁.tail h₂
      | none => exact kom h₁.tail h₂
    | .eq => match (f a₁ (some b) (some g)) with
      | some d =>
        dsimp
        apply KeysOrdered.cons
        · exact ltHeadKey_orderedMerge h₁.ltHeadKey
            (ltHeadKey_of_le (by simp [h]) h₂.ltHeadKey) h₁.tail h₂.tail
        · exact kom h₁.tail h₂.tail
      | none => exact kom h₁.tail h₂.tail
    | .gt => match (f a₂ none (some g)) with
      | some d =>
        apply KeysOrdered.cons
        · apply ltHeadKey_orderedMerge (ltHeadKey_cons.mpr (OrientedCmp.lt_of_gt h))
            h₂.ltHeadKey h₁ h₂.tail
        · exact kom h₁ h₂.tail
      | none => exact kom h₁ h₂.tail

/-- `orderedMerge` never looks at `f a none none`. -/
theorem om_congr {α β γ δ : Type _} {cmp : α → α → Ordering} {f f' : α → Option β → Option γ → Option δ}
    (hf : ∀ a x y, (x.isSome || y.isSome) = true → f a x y = f' a x y) :
    ∀ (l₁ : Batteries.AssocList α β) (l₂ : Batteries.AssocList α γ),
      orderedMerge cmp f l₁ l₂ = orderedMerge cmp f' l₁ l₂
  | .nil, .nil => by rw [orderedMerge, orderedMerge]
  | .nil, .cons a₂ g t₂ => by
    rw [orderedMerge, orderedMerge]; congr 1; funext a g; exact hf _ _ _ rfl
  | .cons a₁ b t₁, .nil => by
    rw [orderedMerge, orderedMerge]; congr 1; funext a b; exact hf _ _ _ rfl
  | .cons a₁ b t₁, .cons a₂ g t₂ => by
    rw [orderedMerge, orderedMerge, hf a₁ (some b) none rfl, hf a₁ (some b) (some g) rfl,
      hf a₂ none (some g) rfl, om_congr hf t₁ (.cons a₂ g t₂), om_congr hf t₁ t₂,
      om_congr hf (.cons a₁ b t₁) t₂]
termination_by l₁ l₂ => l₁.length + l₂.length
end HCO
open HCO

-- `Batteries.AssocList.filterMapVal_filterMapVal`
theorem r1 : drop% Batteries.AssocList.filterMapVal_filterMapVal 5 := by intros; exact fmv_fmv _
-- `Batteries.AssocList.filterMapVal_filterMapVal`
theorem r2 : drop% Batteries.AssocList.filterMapVal_filterMapVal 6 := by intros; exact fmv_fmv _
-- `Batteries.AssocList.filterMapVal_filterMapVal`
theorem r3 : drop% Batteries.AssocList.filterMapVal_filterMapVal 10 := by intros; exact fmv_fmv _
-- `Batteries.OrderedAssocList.filterMapVal_filterMapVal`
theorem r4 : drop% Batteries.OrderedAssocList.filterMapVal_filterMapVal 6 := by
  intros; exact OrderedAssocList.ext_toAssocList (fmv_fmv _)
-- `Batteries.AssocList.orderedFind?_orderedInsert_self`
theorem r5 : drop% Batteries.AssocList.orderedFind?_orderedInsert_self 3 := by intros; exact ofi_self _ _ _
-- `Batteries.AssocList.orderedFind?_orderedInsert_self`
theorem r6 : drop% Batteries.AssocList.orderedFind?_orderedInsert_self 4 := by intros; exact ofi_self _ _ _
-- `Batteries.AssocList.orderedFind?_orderedInsert_self`
theorem r7 : drop% Batteries.AssocList.orderedFind?_orderedInsert_self 6 := by intros; exact ofi_self _ _ _
-- `Batteries.AssocList.orderedFind?_orderedInsert`
theorem r8 : drop% Batteries.AssocList.orderedFind?_orderedInsert 4 := by intros; exact ofi _ _ _ _
-- `Batteries.AssocList.orderedFind?_orderedInsert`
theorem r9 : drop% Batteries.AssocList.orderedFind?_orderedInsert 7 := by intros; exact ofi _ _ _ _
-- `Batteries.AssocList.KeysOrdered.orderedMerge`
theorem r10 : drop% Batteries.AssocList.KeysOrdered.orderedMerge 8 := by intros; exact kom ‹_› ‹_›

-- `Batteries.AssocList.toList_orderedInsert`
theorem r11 : drop% Batteries.AssocList.toList_orderedInsert 3 := by
  intro α β cmp _ l h a b
  induction l with
  | nil => simp
  | cons x y t ih =>
    have tail_lt : ∀ p ∈ t.toList, cmp x p.1 = .lt := fun _ hp => h.lt_of_mem hp
    simp only [orderedInsert_cons, toList, List.filter_cons]
    match w : cmp a x with
    | .lt =>
      have all_lt : ∀ p ∈ t.toList, cmp a p.1 = .lt :=
        fun p hp => TransCmp.lt_trans w (tail_lt p hp)
      have e1 : t.toList.filter (fun p => cmp a p.1 == .gt) = [] :=
        List.filter_eq_nil_iff.mpr fun p hp => by simp [all_lt p hp]
      have e2 : t.toList.filter (fun p => cmp a p.1 == .lt) = t.toList :=
        List.filter_eq_self.mpr fun p hp => by simp [all_lt p hp]
      simp [e1, e2]
    | .eq =>
      have all_lt : ∀ p ∈ t.toList, cmp a p.1 = .lt :=
        fun p hp => TransCmp.lt_of_eq_of_lt w (tail_lt p hp)
      have e1 : t.toList.filter (fun p => cmp a p.1 == .gt) = [] :=
        List.filter_eq_nil_iff.mpr fun p hp => by simp [all_lt p hp]
      have e2 : t.toList.filter (fun p => cmp a p.1 == .lt) = t.toList :=
        List.filter_eq_self.mpr fun p hp => by simp [all_lt p hp]
      simp [e1, e2]
    | .gt => simp [ih h.tail]

-- `Batteries.OrderedAssocList.toAssocList_tail_mk_nil`
theorem r12 : indep% Batteries.OrderedAssocList.toAssocList_tail_mk_nil 3 := by intros; exact trivial
-- `Batteries.OrderedAssocList.getElem?_mk_nil`
theorem r13 : indep% Batteries.OrderedAssocList.getElem?_mk_nil 3 := by intros; exact trivial
-- `Batteries.OrderedAssocList.insert_mk_nil`
theorem r14 : indep% Batteries.OrderedAssocList.insert_mk_nil 5 := by intros; exact trivial
-- `Batteries.OrderedAssocList.merge_mk_nil_mk_cons`
theorem r15 : indep% Batteries.OrderedAssocList.merge_mk_nil_mk_cons 7 := by intros; exact trivial
-- `Batteries.OrderedAssocList.merge_mk_cons_mk_nil`
theorem r16 : indep% Batteries.OrderedAssocList.merge_mk_cons_mk_nil 11 := by intros; exact trivial

-- `Batteries.OrderedAssocList.merge_comm`
theorem r17 : drop% Batteries.OrderedAssocList.merge_comm 9 := by
  intro α cmp _ _ β γ δ f g w l₁ l₂
  let g' : α → Option γ → Option β → Option δ := fun a y x => if (y.isSome || x.isSome) then g a y x else none
  have e1 : OrderedAssocList.merge f l₁ l₂ = OrderedAssocList.merge (fun a x y => g' a y x) l₁ l₂ :=
    OrderedAssocList.ext_toAssocList (om_congr (fun a x y h => by
      simp only [g', Bool.or_comm y.isSome x.isSome, h, ite_true, w]) _ _)
  have e2 : OrderedAssocList.merge g l₂ l₁ = OrderedAssocList.merge g' l₂ l₁ :=
    OrderedAssocList.ext_toAssocList (om_congr (fun a y x h => by simp only [g', h, ite_true]) _ _)
  rw [e1, e2]
  exact OrderedAssocList.merge_comm _ g' (fun a => by simp [g']) (fun _ _ _ => rfl) l₁ l₂

-- `Batteries.OrderedAssocList.merge_assoc`
theorem r18 : drop% Batteries.OrderedAssocList.merge_assoc 15 := by
  intro α cmp _ _ β₁ β₂ γ₁ β₃ ε γ₂ f₁ f₂ g₁ g₂ hf₁ hg₁ hg₂ w l₁ l₂ l₃
  refine OrderedAssocList.merge_assoc f₁ f₂ g₁ g₂ hf₁ (fun a => ?_) hg₁ hg₂ w l₁ l₂ l₃
  have := w a none none none
  rw [hf₁, hg₁, hg₂] at this
  exact this

-- `Batteries.OrderedAssocList.merge_assoc`
theorem r19 : drop% Batteries.OrderedAssocList.merge_assoc 17 := by
  intro α cmp _ _ β₁ β₂ γ₁ β₃ ε γ₂ f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ w l₁ l₂ l₃
  refine OrderedAssocList.merge_assoc f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ (fun a => ?_) w l₁ l₂ l₃
  have := w a none none none
  rw [hf₁, hf₂, hg₁] at this
  exact this.symm
