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
namespace W1c2
open Iris Iris.OFE Iris.Algebra Iris.Std

/-- Discrete OFE on naturals (a fresh structure, so instance search finds only these monoids). -/
structure AN where v : Nat
instance anOFE : OFE AN := OFE.ofDiscrete AN
instance : Inhabited AN := ⟨⟨0⟩⟩
theorem an_dist {n} {x y : AN} : x ≡{n}≡ y ↔ x = y := Iff.rfl
/-- Addition on AN: a lawful, non-idempotent commutative monoid with unit 0. -/
def addAN (a b : AN) : AN := ⟨a.v + b.v⟩
instance anAdd : MonoidOps addAN ⟨0⟩ where
  op_ne := ⟨fun _ _ _ h _ _ h' => by cases h; cases h'; rfl⟩
  op_assoc := by intro a b c; simp [addAN, Nat.add_assoc]
  op_comm := by intro a b; simp [addAN, Nat.add_comm]
  op_left_id := by intro a; simp [addAN]
/-- Max on AN: a lawful idempotent commutative monoid with unit 0. -/
def maxAN (a b : AN) : AN := ⟨max a.v b.v⟩
instance anMax : MonoidOps maxAN ⟨0⟩ where
  op_ne := ⟨fun _ _ _ h _ _ h' => by cases h; cases h'; rfl⟩
  op_assoc := by intro a b c; simp [maxAN, Nat.max_assoc]
  op_comm := by intro a b; simp [maxAN, Nat.max_comm]
  op_left_id := by intro a; simp [maxAN]
/-- Constant-zero operation on AN: unit 0 is no left identity. -/
def zAN (_ _ : AN) : AN := ⟨0⟩
theorem z_bad : ¬ MonoidOps zAN ⟨0⟩ := fun h => absurd (congrArg AN.v (h.op_left_id (a := ⟨1⟩))) (by decide)
/-- Constant-one map: a weak monoid homomorphism from addition to max (for Eq), not preserving the unit. -/
def c1AN (_ : AN) : AN := ⟨1⟩
instance wh1 : WeakMonoidHomomorphism addAN maxAN ⟨0⟩ ⟨0⟩ Eq c1AN where
  rel_refl := rfl
  rel_trans := Eq.trans
  op_proper := by intro a a' b b' h1 h2; subst h1; subst h2; rfl
  map_ne := ⟨fun _ _ _ _ => rfl⟩
  map_op := rfl
abbrev TS := Std.ExtTreeSet Nat compare
abbrev TM := fun V => Std.ExtTreeMap Nat V compare
abbrev MSN := ListPerm Nat
theorem ts_ne : ({0} : TS) ≠ ∅ := fun e =>
  LawfulSet.mem_empty (e ▸ (LawfulSet.mem_singleton.2 rfl : (0 : Nat) ∈ ({0} : TS)))
theorem ms_ne : ({0} : MSN) ≠ ∅ := fun e =>
  Iris.Std.not_mem_empty (e ▸ (Iris.Std.mem_singleton_iff.2 rfl : (0 : Nat) ∈ ({0} : MSN)))
def tm1 : TM Nat := Iris.Std.PartialMap.insert (∅ : TM Nat) 0 0
theorem tm_ne : tm1 ≠ ∅ := fun e => by
  have := LawfulPartialMap.eq_empty_iff.1 e 0
  simp [tm1, LawfulPartialMap.get?_insert] at this
theorem ts01 : ¬ (0 : Nat) ∈ ({1} : TS) := by rw [LawfulSet.mem_singleton]; decide
end W1c2
open Iris Iris.OFE Iris.Algebra Iris.Std W1c2
-- `Iris.Algebra.BigOpM.bigOpM_sep_zip_eq` idx 4: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_1 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_sep_zip_eq 4 := fun H =>
  z_bad (@H (AN) _ (zAN) (default) (TM) (Nat) _ (Nat) (Nat) (default) (default) (∅) (∅) (fun _ => Iff.rfl))
-- `Iris.Algebra.BigOpM.bigOpM_comm_list` idx 4: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_2 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_comm_list 4 := fun H =>
  z_bad (@H (AN) _ (zAN) (default) (TM) (Nat) (Nat) _ (Nat) (default) (∅) ([]))
-- `Iris.Algebra.BigOpM.bigOpM_comm_map` idx 4: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_3 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_comm_map 4 := fun H =>
  z_bad (@H (AN) _ (zAN) (default) (TM) (Nat) (Nat) _ (Nat) (Nat) (TM) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpM.bigOpM_comm_set` idx 4: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_4 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_comm_set 4 := fun H =>
  z_bad (@H (AN) _ (zAN) (default) (TM) (Nat) (Nat) _ (Nat) (TS) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpM.bigOpM_comm_mset` idx 4: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_5 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_comm_mset 4 := fun H =>
  z_bad (@H (AN) _ (zAN) (default) (TM) (Nat) (Nat) _ (Nat) (MSN) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpM.bigOpM_hom` idx 11: necessary (M = AN, op₁ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_6 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_hom 11 := fun H =>
  z_bad (@H (TM) (Nat) _ (AN) _ (AN) _ (zAN) (addAN) (⟨0⟩) (⟨0⟩) anAdd (fun _ _ => True) (default) (Nat) (default) (∅))
-- `Iris.Algebra.BigOpM.bigOpM_hom` idx 12: necessary (M = AN, op₂ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_7 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_hom 12 := fun H =>
  z_bad (@H (TM) (Nat) _ (AN) _ (AN) _ (addAN) (zAN) (⟨0⟩) (⟨0⟩) anAdd (fun _ _ => True) (default) (Nat) (default) (∅))
-- `Iris.Algebra.BigOpM.bigOpM_weak_hom` idx 11: necessary (M = AN, op₁ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_8 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_weak_hom 11 := fun H =>
  z_bad (@H (TM) (Nat) _ (AN) _ (AN) _ (zAN) (addAN) (⟨0⟩) (⟨0⟩) anAdd (fun _ _ => True) (default) (Nat) _ (default) (tm1) tm_ne)
-- `Iris.Algebra.BigOpM.bigOpM_weak_hom` idx 12: necessary (M = AN, op₂ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_9 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_weak_hom 12 := fun H =>
  z_bad (@H (TM) (Nat) _ (AN) _ (AN) _ (addAN) (zAN) (⟨0⟩) (⟨0⟩) anAdd (fun _ _ => True) (default) (Nat) _ (default) (tm1) tm_ne)
-- `Iris.Algebra.BigOpS.bigOpS_empty` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_10 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_empty 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default))
-- `Iris.Algebra.BigOpS.bigOpS_bigOpL` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_11 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_bigOpL 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) (∅))
-- `Iris.Algebra.BigOpS.bigOpS_insert` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_12 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_insert 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) (∅) (0) LawfulSet.mem_empty)
-- `Iris.Algebra.BigOpS.bigOpS_const_unit` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_13 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_const_unit 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (∅))
-- `Iris.Algebra.BigOpS.bigOpS_singleton` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_14 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_singleton 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) (0))
-- `Iris.Algebra.BigOpS.bigOpS_union` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_15 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_union 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) (∅) (∅) LawfulSet.disjoint_empty_left)
-- `Iris.Algebra.BigOpS.bigOpS_eq_of_forall_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_16 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_eq_of_forall_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) (default) (∅) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpS.bigOpS_dist` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_17 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_dist 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) (default) (∅) (0) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpS.bigOpS_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_18 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) (default) (∅) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpS.bigOpS_op_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_19 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_op_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) (default) (∅))
-- `Iris.Algebra.BigOpS.bigOpS_closed` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_20 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_closed 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (fun _ => True) (default) (∅) (by intros; first | trivial | rfl) (by intros; first | trivial | rfl) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpS.bigOpS_gen_proper` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_21 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_gen_proper 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (fun _ _ => True) (default) (default) (∅) (by intros; first | trivial | rfl) (by intros; first | trivial | rfl) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpS.bigOpS_fn_insert_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_22 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_fn_insert_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ _ (Nat) (default) (default) (∅) (0) (default) LawfulSet.mem_empty)
-- `Iris.Algebra.BigOpS.bigOpS_fn_insert_eq'` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_23 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_fn_insert_eq' 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ _ (default) (∅) (0) (default) LawfulSet.mem_empty)
-- `Iris.Algebra.BigOpS.bigOpS_delete` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_24 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_delete 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) ({0}) (0) (LawfulSet.mem_singleton.2 rfl))
-- `Iris.Algebra.BigOpS.bigOpS_filter_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_25 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_filter_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) (default) (∅))
-- `Iris.Algebra.BigOpS.bigOpS_ofList_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_26 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_ofList_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (default) ([]) List.nodup_nil)
-- `Iris.Algebra.BigOpS.bigOpS_map_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_27 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_map_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (Nat) (TS) _ (id) (fun _ _ e => e) default ∅)
-- `Iris.Algebra.BigOpS.bigOpS_comm_list` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_28 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_comm_list 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (Nat) (default) (∅) ([]))
-- `Iris.Algebra.BigOpS.bigOpS_comm_map` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_29 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_comm_map 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (Nat) (Nat) (TM) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpS.bigOpS_comm_set` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_30 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_comm_set 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (Nat) (TS) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpS.bigOpS_comm_mset` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_31 : ¬ indep0% Iris.Algebra.BigOpS.bigOpS_comm_mset 6 := fun H =>
  z_bad (@H (AN) (Nat) (TS) _ (zAN) (default) _ (Nat) (MSN) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpS.hom` idx 8: necessary (M = AN, op₁ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_32 : ¬ indep0% Iris.Algebra.BigOpS.hom 8 := fun H =>
  z_bad (@H (AN) (AN) _ _ (zAN) (addAN) (⟨0⟩) (⟨0⟩) anAdd (Nat) (TS) _ (fun _ _ => True) (default) (default) (∅))
-- `Iris.Algebra.BigOpS.hom` idx 9: necessary (M = AN, op₂ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_33 : ¬ indep0% Iris.Algebra.BigOpS.hom 9 := fun H =>
  z_bad (@H (AN) (AN) _ _ (addAN) (zAN) (⟨0⟩) (⟨0⟩) anAdd (Nat) (TS) _ (fun _ _ => True) (default) (default) (∅))
-- `Iris.Algebra.BigOpS.hom_weak` idx 8: necessary (M = AN, op₁ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_34 : ¬ indep0% Iris.Algebra.BigOpS.hom_weak 8 := fun H =>
  z_bad (@H (AN) (AN) _ _ (zAN) (addAN) (⟨0⟩) (⟨0⟩) anAdd (Nat) (TS) _ (fun _ _ => True) (default) (default) ({0}) ts_ne)
-- `Iris.Algebra.BigOpS.hom_weak` idx 9: necessary (M = AN, op₂ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_35 : ¬ indep0% Iris.Algebra.BigOpS.hom_weak 9 := fun H =>
  z_bad (@H (AN) (AN) _ _ (addAN) (zAN) (⟨0⟩) (⟨0⟩) anAdd (Nat) (TS) _ (fun _ _ => True) (default) (default) ({0}) ts_ne)
-- `Iris.Algebra.BigOpMS.bigOpMS_empty` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_36 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_empty 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default))
-- `Iris.Algebra.BigOpMS.bigOpMS_bigOpL` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_37 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_bigOpL 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default) (∅))
-- `Iris.Algebra.BigOpMS.bigOpMS_singleton` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_38 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_singleton 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default) (0))
-- `Iris.Algebra.BigOpMS.bigOpMS_disjUnion` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_39 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_disjUnion 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpMS.bigOpMS_insert` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_40 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_insert 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default) (∅) (0))
-- `Iris.Algebra.BigOpMS.bigOpMS_delete` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_41 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_delete 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default) ({0}) (0) (Iris.Std.mem_singleton_iff.2 rfl))
-- `Iris.Algebra.BigOpMS.bigOpMS_eq_of_forall_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_42 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_eq_of_forall_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default) (default) (∅) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpMS.bigOpMS_dist` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_43 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_dist 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default) (default) (∅) (0) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpMS.bigOpMS_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_44 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default) (default) (∅) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpMS.bigOpMS_op_eq` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_45 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_op_eq 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (default) (default) (∅))
-- `Iris.Algebra.BigOpMS.bigOpMS_const_unit` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_46 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_const_unit 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (∅))
-- `Iris.Algebra.BigOpMS.bigOpMS_closed` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_47 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_closed 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (fun _ => True) (default) (∅) (by intros; first | trivial | rfl) (by intros; first | trivial | rfl) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpMS.bigOpMS_gen_proper` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_48 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_gen_proper 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (fun _ _ => True) (default) (default) (∅) (by intros; first | trivial | rfl) (by intros; first | trivial | rfl) (by intros; first | trivial | rfl))
-- `Iris.Algebra.BigOpMS.hom` idx 8: necessary (M = AN, op₁ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_49 : ¬ indep0% Iris.Algebra.BigOpMS.hom 8 := fun H =>
  z_bad (@H (AN) (AN) _ _ (zAN) (addAN) (⟨0⟩) (⟨0⟩) anAdd (Nat) (MSN) _ (fun _ _ => True) (default) (default) (∅))
-- `Iris.Algebra.BigOpMS.hom` idx 9: necessary (M = AN, op₂ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_50 : ¬ indep0% Iris.Algebra.BigOpMS.hom 9 := fun H =>
  z_bad (@H (AN) (AN) _ _ (addAN) (zAN) (⟨0⟩) (⟨0⟩) anAdd (Nat) (MSN) _ (fun _ _ => True) (default) (default) (∅))
-- `Iris.Algebra.BigOpMS.hom_weak` idx 8: necessary (M = AN, op₁ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_51 : ¬ indep0% Iris.Algebra.BigOpMS.hom_weak 8 := fun H =>
  z_bad (@H (AN) (AN) _ _ (zAN) (addAN) (⟨0⟩) (⟨0⟩) anAdd (Nat) (MSN) _ (fun _ _ => True) (default) (default) ({0}) ms_ne)
-- `Iris.Algebra.BigOpMS.hom_weak` idx 9: necessary (M = AN, op₂ = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_52 : ¬ indep0% Iris.Algebra.BigOpMS.hom_weak 9 := fun H =>
  z_bad (@H (AN) (AN) _ _ (addAN) (zAN) (⟨0⟩) (⟨0⟩) anAdd (Nat) (MSN) _ (fun _ _ => True) (default) (default) ({0}) ms_ne)
-- `Iris.Algebra.BigOpMS.bigOpMS_comm_list` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_53 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_comm_list 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (Nat) (default) (∅) ([]))
-- `Iris.Algebra.BigOpMS.bigOpMS_comm_map` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_54 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_comm_map 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (Nat) (Nat) (TM) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpMS.bigOpMS_comm_set` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_55 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_comm_set 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (Nat) (TS) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpMS.bigOpMS_comm_mset` idx 6: necessary (M = AN, op = constant 0 with unit 0: no left identity; other data trivial)
theorem w1c2_56 : ¬ indep0% Iris.Algebra.BigOpMS.bigOpMS_comm_mset 6 := fun H =>
  z_bad (@H (AN) (Nat) (MSN) _ (zAN) (default) _ (Nat) (MSN) _ (default) (∅) (∅))
-- `Iris.Algebra.BigOpM.bigOpM_hom` idx 16: necessary (no homomorphism: R = False, M1 = M2 = AN with addition, m empty)
theorem w1c2_57 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_hom 16 := fun H =>
  @H TM Nat _ AN _ AN _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd (fun _ _ => False) id Nat default ∅
-- `Iris.Algebra.BigOpM.bigOpM_weak_hom` idx 17: necessary (no homomorphism: R = False, m = singleton map)
theorem w1c2_58 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_weak_hom 17 := fun H =>
  @H TM Nat _ AN _ AN _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd (fun _ _ => False) id Nat _ default tm1 tm_ne
-- `Iris.Algebra.BigOpM.bigOpM_weak_hom` idx 20: necessary (constant-1 weak hom from addition to max, R = Eq, m empty: 1 = 0)
theorem w1c2_59 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_weak_hom 20 := fun H => by
  have := @H TM Nat _ AN _ AN _ addAN maxAN ⟨0⟩ ⟨0⟩ anAdd anMax Eq c1AN Nat _ wh1 default ∅
  rw [BigOpM.bigOpM_empty, BigOpM.bigOpM_empty] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpS.bigOpS_insert` idx 11: necessary (addition on AN, Phi = 1, s = {0}, x = 0: 1 = 1 + 1)
theorem w1c2_60 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_insert 11 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) {0} 0
  rw [LawfulSet.union_idem, BigOpS.bigOpS_singleton] at this
  exact absurd (congrArg AN.v this) (by simp [addAN])
-- `Iris.Algebra.BigOpS.bigOpS_eq_of_forall_eq` idx 11: necessary (addition, s = {0}, Phi = 1, Psi = 0)
theorem w1c2_61 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_eq_of_forall_eq 11 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) (fun _ => ⟨0⟩) {0}
  rw [BigOpS.bigOpS_singleton, BigOpS.bigOpS_singleton] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpS.bigOpS_dist` idx 12: necessary (discrete AN with addition, s = {0}, Phi = 1, Psi = 0, n = 0)
theorem w1c2_62 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_dist 12 := fun H => by
  have := an_dist.1 (@H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) (fun _ => ⟨0⟩) {0} 0)
  rw [BigOpS.bigOpS_singleton, BigOpS.bigOpS_singleton] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpS.bigOpS_eq` idx 11: necessary (addition, s = {0}, Phi = 1, Psi = 0)
theorem w1c2_63 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_eq 11 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) (fun _ => ⟨0⟩) {0}
  rw [BigOpS.bigOpS_singleton, BigOpS.bigOpS_singleton] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpS.bigOpS_closed` idx 11: necessary (addition, P x = (x != 0), s empty: P unit fails)
theorem w1c2_64 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_closed 11 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun x => x.v ≠ 0) default ∅
    (fun h1 _ => by show _ + _ ≠ 0; omega) (fun h => absurd h LawfulSet.mem_empty)
  rw [BigOpS.bigOpS_empty] at this
  exact this rfl
-- `Iris.Algebra.BigOpS.bigOpS_closed` idx 12: necessary (addition, P x = (x <= 1), Phi = 1, s = {0,1}: sum 2)
theorem w1c2_65 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_closed 12 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun x => x.v ≤ 1) (fun _ => ⟨1⟩) ({0} ∪ {1})
    (by show 0 ≤ 1; omega) (fun _ => by show 1 ≤ 1; omega)
  rw [BigOpS.bigOpS_insert ts01, BigOpS.bigOpS_singleton] at this
  exact absurd this (by simp [addAN])
-- `Iris.Algebra.BigOpS.bigOpS_closed` idx 13: necessary (addition, P x = (x = 0), Phi = 1, s = {0})
theorem w1c2_66 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_closed 13 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun x => x.v = 0) (fun _ => ⟨1⟩) {0}
    rfl (fun h1 h2 => by show _ + _ = 0; omega)
  rw [BigOpS.bigOpS_singleton] at this
  exact absurd this (by decide)
-- `Iris.Algebra.BigOpS.bigOpS_gen_proper` idx 12: necessary (addition, R a b = (a < b), s empty: R unit unit fails)
theorem w1c2_67 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_gen_proper 12 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun a b => a.v < b.v) default default ∅
    (fun h1 h2 => by show _ + _ < _ + _; omega) (fun h => absurd h LawfulSet.mem_empty)
  exact Nat.lt_irrefl _ this
-- `Iris.Algebra.BigOpS.bigOpS_gen_proper` idx 13: necessary (addition, R a b = (a = b or a = 1 and b = 0), Phi = 1, Psi = 0, s = {0,1}: R 2 0 fails)
theorem w1c2_68 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_gen_proper 13 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun a b => a = b ∨ (a.v = 1 ∧ b.v = 0)) (fun _ => ⟨1⟩) (fun _ => ⟨0⟩)
    ({0} ∪ {1}) (Or.inl rfl) (fun _ => Or.inr ⟨rfl, rfl⟩)
  rw [BigOpS.bigOpS_insert ts01, BigOpS.bigOpS_singleton, BigOpS.bigOpS_insert ts01, BigOpS.bigOpS_singleton] at this
  rcases this with h | h
  · exact absurd (congrArg AN.v h) (by simp [addAN])
  · exact absurd h.1 (by simp [addAN])
-- `Iris.Algebra.BigOpS.bigOpS_gen_proper` idx 14: necessary (addition, R = Eq, Phi = 1, Psi = 0, s = {0})
theorem w1c2_69 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_gen_proper 14 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ Eq (fun _ => ⟨1⟩) (fun _ => ⟨0⟩) {0} rfl (fun h1 h2 => by rw [h1, h2])
  rw [BigOpS.bigOpS_singleton, BigOpS.bigOpS_singleton] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpS.bigOpS_fn_insert_eq` idx 15: necessary (addition, s = {0}, x = 0, Phi y b = b, f = 1, b = 1: 1 = 1 + 1)
theorem w1c2_70 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_fn_insert_eq 15 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ _ AN (fun _ b => b) (fun _ => ⟨1⟩) {0} 0 ⟨1⟩
  rw [LawfulSet.union_idem, BigOpS.bigOpS_singleton, BigOpS.bigOpS_singleton] at this
  exact absurd (congrArg AN.v this) (by simp [addAN])
-- `Iris.Algebra.BigOpS.bigOpS_fn_insert_eq'` idx 13: necessary (addition, s = {0}, x = 0, Phi = 1, P = 1: 1 = 1 + 1)
theorem w1c2_71 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_fn_insert_eq' 13 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ _ (fun _ => ⟨1⟩) {0} 0 ⟨1⟩
  rw [LawfulSet.union_idem, BigOpS.bigOpS_singleton, BigOpS.bigOpS_singleton] at this
  exact absurd (congrArg AN.v this) (by simp [addAN])
-- `Iris.Algebra.BigOpS.bigOpS_delete` idx 11: necessary (addition, s empty, x = 0, Phi = 1: 0 = 1 + _)
theorem w1c2_72 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_delete 11 := fun H => by
  have := congrArg AN.v (@H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) ∅ 0)
  rw [BigOpS.bigOpS_empty] at this
  simp [addAN] at this; omega
-- `Iris.Algebra.BigOpS.bigOpS_ofList_eq` idx 10: necessary (addition, l = [0, 0] not Nodup, Phi = 1: set sum 1, list sum 2)
theorem w1c2_73 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_ofList_eq 10 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) [0, 0]
  have e : (LawfulSet.ofList [0, 0] : TS) = {0} := LawfulSet.ext fun y => by
    rw [← LawfulSet.mem_ofList, LawfulSet.mem_singleton]; simp
  rw [e, BigOpS.bigOpS_singleton] at this
  exact absurd (congrArg AN.v this) (by simp [bigOpL, addAN])
-- `Iris.Algebra.BigOpS.bigOpS_map_eq` idx 12: necessary (addition, f = const 0 not injective, s = {0,1}, Phi = 1: 1 = 2)
theorem w1c2_74 : ¬ drop0% Iris.Algebra.BigOpS.bigOpS_map_eq 12 := fun H => by
  have := @H AN Nat TS _ addAN ⟨0⟩ anAdd _ Nat TS _ (fun _ => 0) (fun _ => ⟨1⟩) ({0} ∪ {1})
  have e : (FiniteSet.map (S' := TS) (fun _ : Nat => (0 : Nat)) ({0} ∪ {1} : TS)) = {0} := LawfulSet.ext fun y => by
    rw [FiniteSet.mem_map, LawfulSet.mem_singleton]
    constructor
    · rintro ⟨_, h, _⟩; exact h.symm
    · intro h; exact ⟨0, h.symm, by rw [LawfulSet.mem_union, LawfulSet.mem_singleton]; simp⟩
  rw [e, BigOpS.bigOpS_singleton, BigOpS.bigOpS_insert ts01, BigOpS.bigOpS_singleton] at this
  exact absurd (congrArg AN.v this) (by simp [addAN])
-- `Iris.Algebra.BigOpS.hom` idx 15: necessary (no homomorphism: R = False, addition on AN, s empty)
theorem w1c2_75 : ¬ drop0% Iris.Algebra.BigOpS.hom 15 := fun H =>
  @H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd Nat TS _ (fun _ _ => False) id default ∅
-- `Iris.Algebra.BigOpS.hom_weak` idx 15: necessary (no homomorphism: R = False, s = {0})
theorem w1c2_76 : ¬ drop0% Iris.Algebra.BigOpS.hom_weak 15 := fun H =>
  @H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd Nat TS _ (fun _ _ => False) id default {0} ts_ne
-- `Iris.Algebra.BigOpS.hom_weak` idx 18: necessary (constant-1 weak hom from addition to max, R = Eq, s empty: 1 = 0)
theorem w1c2_77 : ¬ drop0% Iris.Algebra.BigOpS.hom_weak 18 := fun H => by
  have := @H AN AN _ _ addAN maxAN ⟨0⟩ ⟨0⟩ anAdd anMax Nat TS _ Eq c1AN wh1 default ∅
  rw [BigOpS.bigOpS_empty, BigOpS.bigOpS_empty] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpMS.bigOpMS_delete` idx 11: necessary (addition, X empty, x = 0, Phi = 1: 0 = 1 + _)
theorem w1c2_78 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_delete 11 := fun H => by
  have := congrArg AN.v (@H AN Nat MSN _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) ∅ 0)
  rw [BigOpMS.bigOpMS_empty] at this
  simp [addAN] at this; omega
-- `Iris.Algebra.BigOpMS.bigOpMS_eq_of_forall_eq` idx 11: necessary (addition, X = {0}, Phi = 1, Psi = 0)
theorem w1c2_79 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_eq_of_forall_eq 11 := fun H => by
  have := @H AN Nat MSN _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) (fun _ => ⟨0⟩) {0}
  rw [BigOpMS.bigOpMS_singleton, BigOpMS.bigOpMS_singleton] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpMS.bigOpMS_dist` idx 12: necessary (discrete AN with addition, X = {0}, Phi = 1, Psi = 0, n = 0)
theorem w1c2_80 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_dist 12 := fun H => by
  have := an_dist.1 (@H AN Nat MSN _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) (fun _ => ⟨0⟩) {0} 0)
  rw [BigOpMS.bigOpMS_singleton, BigOpMS.bigOpMS_singleton] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpMS.bigOpMS_eq` idx 11: necessary (addition, X = {0}, Phi = 1, Psi = 0)
theorem w1c2_81 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_eq 11 := fun H => by
  have := @H AN Nat MSN _ addAN ⟨0⟩ anAdd _ (fun _ => ⟨1⟩) (fun _ => ⟨0⟩) {0}
  rw [BigOpMS.bigOpMS_singleton, BigOpMS.bigOpMS_singleton] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpMS.bigOpMS_closed` idx 11: necessary (addition, P x = (x != 0), X empty: P unit fails)
theorem w1c2_82 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_closed 11 := fun H => by
  have := @H AN Nat MSN _ addAN ⟨0⟩ anAdd _ (fun x => x.v ≠ 0) default ∅
    (fun h1 _ => by show _ + _ ≠ 0; omega) (fun h => absurd h Iris.Std.not_mem_empty)
  rw [BigOpMS.bigOpMS_empty] at this
  exact this rfl
-- `Iris.Algebra.BigOpMS.bigOpMS_closed` idx 12: necessary (addition, P x = (x <= 1), Phi = 1, X = {0,0}: sum 2)
theorem w1c2_83 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_closed 12 := fun H => by
  have := @H AN Nat MSN _ addAN ⟨0⟩ anAdd _ (fun x => x.v ≤ 1) (fun _ => ⟨1⟩) ({0} ⊎ {0})
    (by show 0 ≤ 1; omega) (fun _ => by show 1 ≤ 1; omega)
  rw [BigOpMS.bigOpMS_insert, BigOpMS.bigOpMS_singleton] at this
  exact absurd this (by simp [addAN])
-- `Iris.Algebra.BigOpMS.bigOpMS_closed` idx 13: necessary (addition, P x = (x = 0), Phi = 1, X = {0})
theorem w1c2_84 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_closed 13 := fun H => by
  have := @H AN Nat MSN _ addAN ⟨0⟩ anAdd _ (fun x => x.v = 0) (fun _ => ⟨1⟩) {0}
    rfl (fun h1 h2 => by show _ + _ = 0; omega)
  rw [BigOpMS.bigOpMS_singleton] at this
  exact absurd this (by decide)
-- `Iris.Algebra.BigOpMS.bigOpMS_gen_proper` idx 12: necessary (addition, R a b = (a < b), X empty: R unit unit fails)
theorem w1c2_85 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_gen_proper 12 := fun H => by
  have := @H AN Nat MSN _ addAN ⟨0⟩ anAdd _ (fun a b => a.v < b.v) default default ∅
    (fun h1 h2 => by show _ + _ < _ + _; omega) (fun h => absurd h Iris.Std.not_mem_empty)
  exact Nat.lt_irrefl _ this
-- `Iris.Algebra.BigOpMS.bigOpMS_gen_proper` idx 13: necessary (addition, R a b = (a = b or a = 1 and b = 0), Phi = 1, Psi = 0, X = {0,0}: R 2 0 fails)
theorem w1c2_86 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_gen_proper 13 := fun H => by
  have := @H AN Nat MSN _ addAN ⟨0⟩ anAdd _ (fun a b => a = b ∨ (a.v = 1 ∧ b.v = 0)) (fun _ => ⟨1⟩) (fun _ => ⟨0⟩)
    ({0} ⊎ {0}) (Or.inl rfl) (fun _ => Or.inr ⟨rfl, rfl⟩)
  rw [BigOpMS.bigOpMS_insert, BigOpMS.bigOpMS_singleton, BigOpMS.bigOpMS_insert, BigOpMS.bigOpMS_singleton] at this
  rcases this with h | h
  · exact absurd (congrArg AN.v h) (by simp [addAN])
  · exact absurd h.1 (by simp [addAN])
-- `Iris.Algebra.BigOpMS.bigOpMS_gen_proper` idx 14: necessary (addition, R = Eq, Phi = 1, Psi = 0, X = {0})
theorem w1c2_87 : ¬ drop0% Iris.Algebra.BigOpMS.bigOpMS_gen_proper 14 := fun H => by
  have := @H AN Nat MSN _ addAN ⟨0⟩ anAdd _ Eq (fun _ => ⟨1⟩) (fun _ => ⟨0⟩) {0} rfl (fun h1 h2 => by rw [h1, h2])
  rw [BigOpMS.bigOpMS_singleton, BigOpMS.bigOpMS_singleton] at this
  exact absurd (congrArg AN.v this) (by decide)
-- `Iris.Algebra.BigOpMS.hom` idx 15: necessary (no homomorphism: R = False, addition on AN, X empty)
theorem w1c2_88 : ¬ drop0% Iris.Algebra.BigOpMS.hom 15 := fun H =>
  @H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd Nat MSN _ (fun _ _ => False) id default ∅
-- `Iris.Algebra.BigOpMS.hom_weak` idx 15: necessary (no homomorphism: R = False, X = {0})
theorem w1c2_89 : ¬ drop0% Iris.Algebra.BigOpMS.hom_weak 15 := fun H =>
  @H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd Nat MSN _ (fun _ _ => False) id default {0} ms_ne
-- `Iris.Algebra.BigOpMS.hom_weak` idx 18: necessary (constant-1 weak hom from addition to max, R = Eq, X empty: 1 = 0)
theorem w1c2_90 : ¬ drop0% Iris.Algebra.BigOpMS.hom_weak 18 := fun H => by
  have := @H AN AN _ _ addAN maxAN ⟨0⟩ ⟨0⟩ anAdd anMax Nat MSN _ Eq c1AN wh1 default ∅
  rw [BigOpMS.bigOpMS_empty, BigOpMS.bigOpMS_empty] at this
  exact absurd (congrArg AN.v this) (by decide)
