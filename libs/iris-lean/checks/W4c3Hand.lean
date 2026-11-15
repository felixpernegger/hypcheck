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

namespace W4c3
open Iris Iris.BI Iris.OFE

-- helper: SiProp true only at step 0 (not timeless)
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩

/-- non-affine 2-element UORA (e unit, a absorbing), equality order (copied from Probe3) -/
inductive NA | e | a deriving DecidableEq

def NA.op : NA → NA → NA
  | .e, y => y
  | .a, _ => .a

instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨id⟩

instance naORA : ORA NA := ORA.ofDiscreteORAData {
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

instance naUORA : UORA NA where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

-- helper: in the non-affine UPred NA, True does not entail emp
theorem na_true_not_emp : ¬ ((iprop(True) : UPred NA) ⊢ iprop(emp)) := fun h => by
  have H := h 0 ⟨.a, trivial⟩ trivial
  cases H

/-- Bool with constant op, no core, n-validity n = 0 and nothing valid (copied from W1c5). -/
structure VZ where b : Bool
instance : OFE VZ := OFE.ofDiscrete VZ
instance : OFE.Discrete VZ := ⟨fun h => h⟩
instance vzOp : Op VZ where
  op _ _ := ⟨false⟩
  op_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  assoc := rfl
  comm := rfl
instance vzPCore : PCore VZ where
  pcore _ := none
  pcore_ne _ h := nomatch h
  pcore_idem h := nomatch h
instance vzValid : Iris.Valid VZ where
  ValidN n _ := n = 0
  Valid _ := False
  validN_ne _ h := h
  valid_iff_validN := ⟨False.elim, fun h => by have := h 1; omega⟩
  validN_succ h := by omega
instance vzOrdered : Ordered VZ where
  OrderN _ _ _ := True
  Order _ _ := True
  ordN_ne _ _ _ := trivial
  ordN_succ _ := trivial
  ordN_trans _ _ := trivial
  ord_trans _ _ := trivial
  ordN_of_ord _ _ := trivial
instance vzORA : ORA VZ where
  validN_op_left h := h
  pcore_op_left h := nomatch h
  extend {_ _ y₁ y₂} _ e := ⟨y₁, y₂, e, OFE.Dist.rfl, OFE.Dist.rfl⟩
  op_monoN_left_ord _ _ := trivial
  op_mono_left_ord _ _ := trivial
  validN_of_ordN _ h := h
  pcore_monoN_ord _ h := nomatch h
  pcore_mono_ord _ h := nomatch h
  pcore_order_op h := nomatch h
  pcore_increasing h := nomatch h
  increasing_closed _ _ := ⟨fun _ => trivial⟩
  ordN_extend _ _ := ⟨_, trivial, OFE.Dist.rfl⟩

/-- Bool with constant op, no core, nothing valid, n-order n = 0, order false (copied from W1c5). -/
structure VF where b : Bool
instance : OFE VF := OFE.ofDiscrete VF
instance : OFE.Discrete VF := ⟨fun h => h⟩
instance vfOp : Op VF where
  op _ _ := ⟨false⟩
  op_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  assoc := rfl
  comm := rfl
instance vfPCore : PCore VF where
  pcore _ := none
  pcore_ne _ h := nomatch h
  pcore_idem h := nomatch h
instance vfValid : Iris.Valid VF where
  ValidN _ _ := False
  Valid _ := False
  validN_ne _ h := h
  valid_iff_validN := ⟨False.elim, fun h => h 0⟩
  validN_succ h := h
instance vfOrdered : Ordered VF where
  OrderN n _ _ := n = 0
  Order _ _ := False
  ordN_ne _ _ h := h
  ordN_succ h := by omega
  ordN_trans h _ := h
  ord_trans h _ := h
  ordN_of_ord _ h := h.elim
instance vfORA : ORA VF where
  validN_op_left h := h
  pcore_op_left h := nomatch h
  extend v _ := v.elim
  op_monoN_left_ord _ h := h
  op_mono_left_ord _ h := h
  validN_of_ordN _ h := h.elim
  pcore_monoN_ord _ h := nomatch h
  pcore_mono_ord _ h := nomatch h
  pcore_order_op h := nomatch h
  pcore_increasing h := nomatch h
  increasing_closed h _ := (h.increasing ⟨false⟩).elim
  ordN_extend v _ := v.elim

/-- Bool, xor, no core, all valid, empty order (copied from W1c3). -/
structure BX where b : Bool
instance : OFE BX := OFE.ofDiscrete BX
instance : OFE.Discrete BX := ⟨fun h => h⟩
def bxData : DiscreteORAData BX where
  pcore _ := none
  op x y := ⟨xor x.b y.b⟩
  Valid _ := True
  Order _ _ := False
  assoc x y z := congrArg BX.mk (Bool.xor_assoc x.b y.b z.b).symm
  comm x y := congrArg BX.mk (Bool.xor_comm x.b y.b)
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h _ := h
  op_mono_left _ _ _ h := h
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ h := h.elim
instance bxORA : ORA BX := ORA.ofDiscreteORAData bxData

/-- Bool, or, no core, all valid, full order (copied from W1c3). -/
structure BT where b : Bool
instance : OFE BT := OFE.ofDiscrete BT
instance : OFE.Discrete BT := ⟨fun h => h⟩
def btData : DiscreteORAData BT where
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

theorem bxOrdInc : OrdInc BX := ⟨fun h => False.elim h, fun h => False.elim h⟩
theorem btIncOrd : IncOrd BT := ⟨fun _ => trivial⟩

/-- Discrete Nat, x • y = x + y + 2, no core, all valid, empty order: x is never included in y ≤ x + 1. -/
structure TD where v : Nat
instance : OFE TD := OFE.ofDiscrete TD
instance : OFE.Discrete TD := ⟨fun h => h⟩
def tdData : DiscreteORAData TD where
  pcore _ := none
  op x y := ⟨x.v + y.v + 2⟩
  Valid _ := True
  Order _ _ := False
  assoc _ _ _ := by simp only [TD.mk.injEq]; omega
  comm _ _ := by simp only [TD.mk.injEq]; omega
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h _ := h
  op_mono_left _ _ _ h := h
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ h := h.elim
instance tdORA : ORA TD := ORA.ofDiscreteORAData tdData
theorem td_incN {n} {x y : TD} (h : x ≼{n} y) : x.v + 2 ≤ y.v := by
  obtain ⟨z, hz⟩ := h
  have := congrArg TD.v hz; change y.v = x.v + z.v + 2 at this; omega

/-- Truncation OFE on naturals (copied from W1c4): dist n x y iff min x (n+1) = min y (n+1). -/
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

/-- CMRA on TN (copied from W1c4): x • y = x + y + 2, no core, only 0 valid. -/
@[instance_reducible] def tcData : CMRAData TN where
  op x y := ⟨x.v + y.v + 2⟩
  op_ne := ⟨fun {n a b} h => by
    have h' : min a.v (n+1) = min b.v (n+1) := h
    show min (_ + a.v + 2) (n+1) = min (_ + b.v + 2) (n+1); omega⟩
  assoc {x y z} := by show TN.mk _ = TN.mk _; simp only [TN.mk.injEq]; omega
  comm {x y} := by show TN.mk _ = TN.mk _; simp only [TN.mk.injEq]; omega
  pcore _ := none
  pcore_ne _ e := nomatch e
  pcore_idem e := nomatch e
  ValidN _ x := x.v = 0
  Valid x := x.v = 0
  validN_ne {n x y} h v := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show y.v = 0; have : x.v = 0 := v; omega
  valid_iff_validN := ⟨fun h _ => h, fun h => h 0⟩
  validN_succ := id
  validN_op_left {n x y} v := by have : x.v + y.v + 2 = 0 := v; omega
  pcore_op_left e := nomatch e
  extend {n x y₁ y₂} v h := False.elim (by
    have h' : min x.v (n+1) = min (y₁.v + y₂.v + 2) (n+1) := h
    have : x.v = 0 := v; omega)
  pcore_op_mono e := nomatch e
instance tcCMRA : CMRA TN := ORA.ofCMRAData tcData
theorem tc_inc0 : (⟨0⟩ : TN) ≼{0} ⟨1⟩ := ⟨⟨0⟩, rfl⟩
theorem tc_not_inc (x : TN) : ¬ x ≼ ⟨1⟩ := fun ⟨z, hz⟩ => by
  have := congrArg TN.v hz; change 1 = x.v + z.v + 2 at this; omega
theorem tc_not_inc1 (x : TN) : ¬ x ≼{1} ⟨1⟩ := fun ⟨z, hz⟩ => by
  have h' : min 1 2 = min (x.v + z.v + 2) 2 := hz; omega

-- helper: the SiProp internal inclusion holds at n iff n-inclusion
theorem incH {A : Type} [ORA A] {a b : A} {n : Nat}
    (h : (internalCmraIncluded (PROP := SiProp) a b).holds n) : a ≼{n} b := by
  obtain ⟨c, hc⟩ := SiProp.exists_holds.mp h; exact ⟨c, hc⟩
theorem incH' {A : Type} [ORA A] {a b : A} {n : Nat}
    (h : a ≼{n} b) : (internalCmraIncluded (PROP := SiProp) a b).holds n := by
  obtain ⟨c, hc⟩ := h; exact SiProp.exists_holds.mpr ⟨c, hc⟩

end W4c3

namespace W4c3
open Iris Iris.BI Iris.OFE

-- `Iris.BI.Timeless.timeless` idx 3: necessary (SiProp, P = s0 true only at step 0)
theorem w4c3_1 : ¬ drop0% Iris.BI.Timeless.timeless 3 := fun h => by
  have H := (@h SiProp SiProp.instBI s0) 1 rfl
  rcases H with H | H
  · exact H
  · exact Nat.succ_ne_zero 0 H

-- `Iris.internalCmraValid_intro` idx 6: necessary (SiProp, VZ valid only at step 0, n = 1)
theorem w4c3_2 : ¬ drop0% Iris.internalCmraValid_intro 6 := fun h =>
  Nat.succ_ne_zero 0 ((@h SiProp VZ _ _ iprop(True) ⟨true⟩) 1 trivial)

-- `Iris.intuitionistically_internalCmraValid` idx 4: necessary (non-affine UPred NA, a = ())
theorem w4c3_3 : ¬ drop0% Iris.intuitionistically_internalCmraValid 4 := fun h =>
  na_true_not_emp <| ((internalCmraValid_intro (PROP := UPred NA) (P := iprop(True)) (a := ()) trivial).trans
    (@h (UPred NA) Unit _ _ ()).mpr).trans intuitionistically_elim_emp

-- `Iris.internalCmraValid_discrete` idx 4: necessary (SiProp, VZ valid only at step 0)
theorem w4c3_4 : ¬ drop0% Iris.internalCmraValid_discrete 4 := fun h =>
  (@h SiProp VZ _ _ ⟨true⟩).mp 0 rfl

-- `Iris.internalCmraValid_timeless` idx 4: necessary (SiProp, VZ valid only at step 0)
theorem w4c3_5 : ¬ drop0% Iris.internalCmraValid_timeless 4 := fun h => by
  have H := (@h SiProp VZ _ _ ⟨true⟩).timeless 1 rfl
  rcases H with H | H
  · exact H
  · exact Nat.succ_ne_zero 0 H

-- `Iris.internalCmraIncluded_intro` idx 7: necessary (SiProp, TD: 0 not included in 0)
theorem w4c3_6 : ¬ drop0% Iris.internalCmraIncluded_intro 7 := fun h => by
  have := td_incN (incH ((@h SiProp TD _ _ iprop(True) ⟨0⟩ ⟨0⟩) 0 trivial)); simp at this

-- `Iris.internalCmraIncluded_iff` idx 10: necessary (SiProp, () included in () vs TD 0 not in 0)
theorem w4c3_7 : ¬ drop0% Iris.internalCmraIncluded_iff 10 := fun h => by
  have := td_incN (incH ((@h SiProp Unit _ _ TD _ () () ⟨0⟩ ⟨0⟩).mp 0 (incH' ⟨(), OFE.Dist.rfl⟩))); simp at this

-- `Iris.internalCmraIncluded_pure` idx 7: necessary (SiProp, () included in (), phi = False)
theorem w4c3_8 : ¬ drop0% Iris.internalCmraIncluded_pure 7 := fun h =>
  (@h SiProp Unit _ _ () () False).mp 0 (incH' ⟨(), OFE.Dist.rfl⟩)

-- `Iris.intuitionistically_internalCmraIncluded` idx 4: necessary (non-affine UPred NA, a = b = ())
theorem w4c3_9 : ¬ drop0% Iris.intuitionistically_internalCmraIncluded 4 := fun h =>
  na_true_not_emp <| ((internalCmraIncluded_intro (PROP := UPred NA) (P := iprop(True)) (a := ()) (b := ())
    ⟨(), rfl⟩).trans (@h (UPred NA) Unit _ _ () ()).mpr).trans intuitionistically_elim_emp

-- `Iris.internalCmraIncluded_discrete` idx 6: necessary (SiProp, TN with x•y = x+y+2: 0 included in 1 at step 0 only)
theorem w4c3_10 : ¬ drop0% Iris.internalCmraIncluded_discrete 6 := fun h =>
  tc_not_inc _ ((@h SiProp TN _ _ ⟨0⟩ ⟨1⟩).mp 0 (incH' tc_inc0))

-- `Iris.internalCmraIncluded_refl` idx 5: necessary (SiProp, TD: 0 not included in 0)
theorem w4c3_11 : ¬ drop0% Iris.internalCmraIncluded_refl 5 := fun h => by
  have := td_incN (incH ((@h SiProp TD _ _ ⟨0⟩) 0 trivial)); simp at this

-- `Iris.internalCmraIncluded_map` idx 7: necessary (SiProp, g : TN → TD, n ↦ n, a homomorphism that is not non-expansive)
theorem w4c3_12 : ¬ drop0% Iris.internalCmraIncluded_map 7 := fun h => by
  have := td_incN (incH ((@h SiProp TN _ _ TD _ (fun x => ⟨x.v⟩) (fun _ _ => rfl) ⟨0⟩ ⟨1⟩) 0 (incH' tc_inc0)))
  simp at this

-- `Iris.internalCmraIncluded_map` idx 8: necessary (SiProp, g : Unit → TD constant 0, not a homomorphism)
theorem w4c3_13 : ¬ drop0% Iris.internalCmraIncluded_map 8 := fun h => by
  have := td_incN (incH ((@h SiProp Unit _ _ TD _ (fun _ => ⟨0⟩) ⟨fun _ _ _ _ => rfl⟩ () ()) 0
    (incH' ⟨(), OFE.Dist.rfl⟩)))
  simp at this

-- `Iris.internalCmraIncluded_timeless` idx 6: necessary (SiProp, TN: 0 included in 1 at step 0, not at step 1)
theorem w4c3_14 : ¬ drop0% Iris.internalCmraIncluded_timeless 6 := fun h => by
  have H := (@h SiProp TN _ _ ⟨0⟩ ⟨1⟩).timeless 1 (incH' tc_inc0)
  rcases H with H | H
  · exact H
  · exact tc_not_inc1 _ (incH H)

-- `SiProp.cmraOrder_timeless` idx 2: necessary (VF ordered only at step 0)
theorem w4c3_15 : ¬ drop0% SiProp.cmraOrder_timeless 2 := fun h => by
  have H := (@h VF _ ⟨true⟩ ⟨true⟩).timeless 1 rfl
  rcases H with H | H
  · exact H
  · exact Nat.succ_ne_zero 0 H

-- `Iris.internalCmraOrder_intro` idx 7: necessary (SiProp, VF ordered only at step 0, n = 1)
theorem w4c3_16 : ¬ drop0% Iris.internalCmraOrder_intro 7 := fun h =>
  Nat.succ_ne_zero 0 ((@h SiProp VF _ _ iprop(True) ⟨true⟩ ⟨true⟩) 1 trivial)

-- `Iris.internalCmraOrder_iff` idx 10: necessary (SiProp, VF ordered at step 0, BX never ordered)
theorem w4c3_17 : ¬ drop0% Iris.internalCmraOrder_iff 10 := fun h =>
  (@h SiProp VF _ _ BX _ ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨true⟩).mp 0 rfl

-- `Iris.internalCmraOrder_pure` idx 7: necessary (SiProp, VF ordered at step 0, phi = False)
theorem w4c3_18 : ¬ drop0% Iris.internalCmraOrder_pure 7 := fun h =>
  (@h SiProp VF _ _ ⟨true⟩ ⟨true⟩ False).mp 0 rfl

-- `Iris.intuitionistically_internalCmraOrder` idx 4: necessary (non-affine UPred NA, BT with full order)
theorem w4c3_19 : ¬ drop0% Iris.intuitionistically_internalCmraOrder 4 := fun h =>
  na_true_not_emp <| ((internalCmraOrder_intro (PROP := UPred NA) (P := iprop(True)) (a := (⟨true⟩ : BT))
    (b := ⟨true⟩) trivial).trans (@h (UPred NA) BT _ _ ⟨true⟩ ⟨true⟩).mpr).trans intuitionistically_elim_emp

-- `Iris.internalCmraOrder_discrete` idx 6: necessary (SiProp, VF ordered only at step 0)
theorem w4c3_20 : ¬ drop0% Iris.internalCmraOrder_discrete 6 := fun h =>
  (@h SiProp VF _ _ ⟨true⟩ ⟨true⟩).mp 0 rfl

-- `Iris.internalCmraOrder_refl` idx 5: necessary (SiProp, VF ordered only at step 0, n = 1)
theorem w4c3_21 : ¬ drop0% Iris.internalCmraOrder_refl 5 := fun h =>
  Nat.succ_ne_zero 0 ((@h SiProp VF _ _ ⟨true⟩) 1 trivial)

-- `Iris.internalCmraOrder_of_inc` idx 4: necessary (SiProp, VF: false included in false, not ordered at step 1)
theorem w4c3_22 : ¬ drop0% Iris.internalCmraOrder_of_inc 4 := fun h =>
  Nat.succ_ne_zero 0 ((@h SiProp VF _ _ ⟨false⟩ ⟨false⟩) 1 (incH' ⟨⟨false⟩, rfl⟩))

-- `Iris.internalCmraIncluded_of_ord` idx 4: necessary (SiProp, BT: true below false in the full order, not included)
theorem w4c3_23 : ¬ drop0% Iris.internalCmraIncluded_of_ord 4 := fun h => by
  obtain ⟨c, hc⟩ := incH ((@h SiProp BT _ _ ⟨true⟩ ⟨false⟩) 0 trivial)
  have h2 : (⟨false⟩ : BT) = ⟨or true c.b⟩ := hc; have h3 := congrArg BT.b h2; simp at h3

-- `Iris.internalCmraIncluded_iff_internalCmraOrder` idx 4: necessary (SiProp, BX: OrdInc, false included in false, empty order)
theorem w4c3_24 : ¬ drop0% Iris.internalCmraIncluded_iff_internalCmraOrder 4 := fun h =>
  (@h SiProp BX _ _ bxOrdInc ⟨false⟩ ⟨false⟩).mp 0 (incH' ⟨⟨false⟩, rfl⟩)

-- `Iris.internalCmraIncluded_iff_internalCmraOrder` idx 5: necessary (SiProp, BT: IncOrd, true below false, not included)
theorem w4c3_25 : ¬ drop0% Iris.internalCmraIncluded_iff_internalCmraOrder 5 := fun h => by
  obtain ⟨c, hc⟩ := incH ((@h SiProp BT _ _ btIncOrd ⟨true⟩ ⟨false⟩).mpr 0 trivial)
  have h2 : (⟨false⟩ : BT) = ⟨or true c.b⟩ := hc; have h3 := congrArg BT.b h2; simp at h3

-- `Iris.internalCmraOrder_timeless` idx 6: necessary (SiProp, VF ordered only at step 0)
theorem w4c3_26 : ¬ drop0% Iris.internalCmraOrder_timeless 6 := fun h => by
  have H := (@h SiProp VF _ _ ⟨true⟩ ⟨true⟩).timeless 1 rfl
  rcases H with H | H
  · exact H
  · exact Nat.succ_ne_zero 0 H

end W4c3

namespace W4c3
open Iris Iris.BI Iris.OFE

-- `Iris.BI.and_elim_left_trans` idx 5: necessary (P=Q=True, R=False)
theorem w4c3_27 : ¬ drop0% Iris.BI.and_elim_left_trans 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H 0 ⟨trivial, trivial⟩

-- `Iris.BI.and_elim_right_trans` idx 5: necessary (P=Q=True, R=False)
theorem w4c3_28 : ¬ drop0% Iris.BI.and_elim_right_trans 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H 0 ⟨trivial, trivial⟩

-- `Iris.BI.or_intro_left_trans` idx 5: necessary (P=True, Q=R=False)
theorem w4c3_29 : ¬ drop0% Iris.BI.or_intro_left_trans 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False)
  (H 0 trivial).elim id id

-- `Iris.BI.or_intro_right_trans` idx 5: necessary (P=True, Q=R=False)
theorem w4c3_30 : ¬ drop0% Iris.BI.or_intro_right_trans 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False)
  (H 0 trivial).elim id id

-- `Iris.BI.imp_intro_swap` idx 5: necessary (P=Q=True, R=False)
theorem w4c3_31 : ¬ drop0% Iris.BI.imp_intro_swap 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H 0 trivial 0 (Nat.le_refl 0) trivial

-- `Iris.BI.imp_mp` idx 5: necessary (P=Q=True, R=False)
theorem w4c3_32 : ¬ drop0% Iris.BI.imp_mp 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False) .rfl
  H 0 trivial

-- `Iris.BI.imp_elim_swap` idx 5: necessary (P=Q=True, R=False)
theorem w4c3_33 : ¬ drop0% Iris.BI.imp_elim_swap 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H 0 ⟨trivial, trivial⟩

-- `Iris.BI.entails_eq_true` idx 4: necessary (P=True, Q=False)
theorem w4c3_34 : ¬ drop0% Iris.BI.entails_eq_true 4 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  H.mpr 0 trivial 0 (Nat.le_refl 0) trivial

-- `Iris.BI.entails_equiv_left` idx 5: necessary (P=True, Q=R=False)
theorem w4c3_35 : ¬ drop0% Iris.BI.entails_equiv_left 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False) .rfl
  H 0 trivial

-- `Iris.BI.entails_equiv_left` idx 6: necessary (P=Q=True, R=False)
theorem w4c3_36 : ¬ drop0% Iris.BI.entails_equiv_left 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False) .rfl
  H 0 trivial

-- `Iris.BI.entails_equiv_right` idx 5: necessary (P=True, Q=R=False)
theorem w4c3_37 : ¬ drop0% Iris.BI.entails_equiv_right 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False) .rfl
  H 0 trivial

-- `Iris.BI.entails_equiv_right` idx 6: necessary (P=Q=True, R=False)
theorem w4c3_38 : ¬ drop0% Iris.BI.entails_equiv_right 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False) .rfl
  H 0 trivial

-- `Iris.BI.and_mono` idx 6: necessary (P=P'=Q'=True, Q=False)
theorem w4c3_39 : ¬ drop0% Iris.BI.and_mono 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True) .rfl
  (H 0 ⟨trivial, trivial⟩).1

-- `Iris.BI.and_mono` idx 7: necessary (P=P'=Q=True, Q'=False)
theorem w4c3_40 : ¬ drop0% Iris.BI.and_mono 7 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) .rfl
  (H 0 ⟨trivial, trivial⟩).2

-- `Iris.BI.and_mono_left` idx 5: necessary (P=Q=True, P'=False)
theorem w4c3_41 : ¬ drop0% Iris.BI.and_mono_left 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(True)
  (H 0 ⟨trivial, trivial⟩).1

-- `Iris.BI.and_mono_right` idx 5: necessary (P=Q=True, Q'=False)
theorem w4c3_42 : ¬ drop0% Iris.BI.and_mono_right 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  (H 0 ⟨trivial, trivial⟩).2

-- `Iris.BI.and_congr` idx 6: necessary (P=P'=Q'=True, Q=False)
theorem w4c3_43 : ¬ drop0% Iris.BI.and_congr 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True) .rfl
  (H.mp 0 ⟨trivial, trivial⟩).1

-- `Iris.BI.and_congr` idx 7: necessary (P=P'=Q=True, Q'=False)
theorem w4c3_44 : ¬ drop0% Iris.BI.and_congr 7 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) .rfl
  (H.mp 0 ⟨trivial, trivial⟩).2

-- `Iris.BI.and_congr_left` idx 5: necessary (P=Q=True, P'=False)
theorem w4c3_45 : ¬ drop0% Iris.BI.and_congr_left 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(True)
  (H.mp 0 ⟨trivial, trivial⟩).1

-- `Iris.BI.and_congr_right` idx 5: necessary (P=Q=True, Q'=False)
theorem w4c3_46 : ¬ drop0% Iris.BI.and_congr_right 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  (H.mp 0 ⟨trivial, trivial⟩).2

-- `Iris.BI.or_mono` idx 6: necessary (P=True, P'=Q=Q'=False)
theorem w4c3_47 : ¬ drop0% Iris.BI.or_mono 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False) iprop(False) .rfl
  (H 0 (.inl trivial)).elim id id

-- `Iris.BI.or_mono` idx 7: necessary (P'=True, P=Q=Q'=False)
theorem w4c3_48 : ¬ drop0% Iris.BI.or_mono 7 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(False) iprop(False) .rfl
  (H 0 (.inr trivial)).elim id id

-- `Iris.BI.or_mono_left` idx 5: necessary (P=True, P'=Q=False)
theorem w4c3_49 : ¬ drop0% Iris.BI.or_mono_left 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False)
  (H 0 (.inl trivial)).elim id id

-- `Iris.BI.or_mono_right` idx 5: necessary (Q=True, P=Q'=False)
theorem w4c3_50 : ¬ drop0% Iris.BI.or_mono_right 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(False)
  (H 0 (.inr trivial)).elim id id

-- `Iris.BI.or_congr` idx 6: necessary (P=True, P'=Q=Q'=False)
theorem w4c3_51 : ¬ drop0% Iris.BI.or_congr 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False) iprop(False) .rfl
  (H.mp 0 (.inl trivial)).elim id id

-- `Iris.BI.or_congr_left` idx 5: necessary (P=True, P'=Q=False)
theorem w4c3_52 : ¬ drop0% Iris.BI.or_congr_left 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False)
  (H.mp 0 (.inl trivial)).elim id id

-- `Iris.BI.imp_mono` idx 6: necessary (P=P'=Q'=False, Q=True)
theorem w4c3_53 : ¬ drop0% Iris.BI.imp_mono 6 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(False) iprop(True) iprop(False) .rfl
  H 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.imp_mono` idx 7: necessary (P=P'=Q=True, Q'=False)
theorem w4c3_54 : ¬ drop0% Iris.BI.imp_mono 7 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) .rfl
  H 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.imp_mono_left` idx 5: necessary (P=Q=False, P'=True)
theorem w4c3_55 : ¬ drop0% Iris.BI.imp_mono_left 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(False)
  H 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.imp_mono_right` idx 5: necessary (P=Q=True, Q'=False)
theorem w4c3_56 : ¬ drop0% Iris.BI.imp_mono_right 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.imp_congr` idx 6: necessary (P=P'=Q'=False, Q=True)
theorem w4c3_57 : ¬ drop0% Iris.BI.imp_congr 6 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(False) iprop(True) iprop(False) .rfl
  H.mp 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.imp_congr` idx 7: necessary (P=P'=Q=True, Q'=False)
theorem w4c3_58 : ¬ drop0% Iris.BI.imp_congr 7 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) .rfl
  H.mp 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.imp_congr_left` idx 5: necessary (P=Q=False, P'=True)
theorem w4c3_59 : ¬ drop0% Iris.BI.imp_congr_left 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(False)
  H.mp 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.imp_congr_right` idx 5: necessary (P=Q=True, Q'=False)
theorem w4c3_60 : ¬ drop0% Iris.BI.imp_congr_right 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H.mp 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.forall_ne` idx 6: necessary (alpha=True, n=0, Phi=True, Psi=False)
theorem w4c3_61 : ¬ drop0% Iris.BI.forall_ne 6 := fun h =>
  have H := @h SiProp True 0 _ (fun _ => iprop(True)) (fun _ => iprop(False))
  SiProp.forall_holds.mp ((H (Nat.le_refl 0)).mp (SiProp.forall_holds.mpr fun _ => trivial)) trivial

-- `Iris.BI.forall_intro` idx 5: necessary (alpha=True, P=True, Psi=False)
theorem w4c3_62 : ¬ drop0% Iris.BI.forall_intro 5 := fun h =>
  have H := @h SiProp True _ iprop(True) (fun _ => iprop(False))
  SiProp.forall_holds.mp (H 0 trivial) trivial

-- `Iris.BI.forall_elim_trans` idx 5: necessary (alpha=True, P=True, Psi=False)
theorem w4c3_63 : ¬ drop0% Iris.BI.forall_elim_trans 5 := fun h =>
  have H := @h SiProp True _ (fun _ => iprop(False)) iprop(True) trivial
  H 0 trivial

-- `Iris.BI.forall_mono` idx 5: necessary (alpha=True, Phi=True, Psi=False)
theorem w4c3_64 : ¬ drop0% Iris.BI.forall_mono 5 := fun h =>
  have H := @h SiProp True _ (fun _ => iprop(True)) (fun _ => iprop(False))
  SiProp.forall_holds.mp (H 0 (SiProp.forall_holds.mpr fun _ => trivial)) trivial

-- `Iris.BI.forall_congr` idx 5: necessary (alpha=True, Phi=True, Psi=False)
theorem w4c3_65 : ¬ drop0% Iris.BI.forall_congr 5 := fun h =>
  have H := @h SiProp True _ (fun _ => iprop(True)) (fun _ => iprop(False))
  SiProp.forall_holds.mp (H.mp 0 (SiProp.forall_holds.mpr fun _ => trivial)) trivial

-- `Iris.BI.exists_ne` idx 6: necessary (alpha=True, n=0, Phi=True, Psi=False)
theorem w4c3_66 : ¬ drop0% Iris.BI.exists_ne 6 := fun h =>
  have H := @h SiProp True 0 _ (fun _ => iprop(True)) (fun _ => iprop(False))
  (SiProp.exists_holds.mp ((H (Nat.le_refl 0)).mp (SiProp.exists_holds.mpr ⟨trivial, trivial⟩))).elim fun _ h => h

-- `Iris.BI.exists_intro_trans` idx 6: necessary (alpha=True, P=True, Psi=False)
theorem w4c3_67 : ¬ drop0% Iris.BI.exists_intro_trans 6 := fun h =>
  have H := @h SiProp True _ iprop(True) (fun _ => iprop(False)) trivial
  (SiProp.exists_holds.mp (H 0 trivial)).elim fun _ h => h

-- `Iris.BI.exists_elim` idx 5: necessary (alpha=True, Phi=True, Q=False)
theorem w4c3_68 : ¬ drop0% Iris.BI.exists_elim 5 := fun h =>
  have H := @h SiProp True _ (fun _ => iprop(True)) iprop(False)
  H 0 (SiProp.exists_holds.mpr ⟨trivial, trivial⟩)

-- `Iris.BI.exists_mono` idx 5: necessary (alpha=True, Phi=True, Psi=False)
theorem w4c3_69 : ¬ drop0% Iris.BI.exists_mono 5 := fun h =>
  have H := @h SiProp True _ (fun _ => iprop(True)) (fun _ => iprop(False))
  (SiProp.exists_holds.mp (H 0 (SiProp.exists_holds.mpr ⟨trivial, trivial⟩))).elim fun _ h => h

-- `Iris.BI.exists_congr` idx 5: necessary (alpha=True, Phi=True, Psi=False)
theorem w4c3_70 : ¬ drop0% Iris.BI.exists_congr 5 := fun h =>
  have H := @h SiProp True _ (fun _ => iprop(True)) (fun _ => iprop(False))
  (SiProp.exists_holds.mp (H.mp 0 (SiProp.exists_holds.mpr ⟨trivial, trivial⟩))).elim fun _ h => h

-- `Iris.BI.wand_mono` idx 6: necessary (SiProp (wand = imp): P=P'=Q'=False, Q=True)
theorem w4c3_71 : ¬ drop0% Iris.BI.wand_mono 6 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(False) iprop(True) iprop(False) .rfl
  H 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_mono` idx 7: necessary (SiProp (wand = imp): P=P'=Q=True, Q'=False)
theorem w4c3_72 : ¬ drop0% Iris.BI.wand_mono 7 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) .rfl
  H 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_mono_left` idx 5: necessary (SiProp: P=Q=False, P'=True)
theorem w4c3_73 : ¬ drop0% Iris.BI.wand_mono_left 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(False)
  H 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_mono_right` idx 5: necessary (SiProp: P=Q=True, Q'=False)
theorem w4c3_74 : ¬ drop0% Iris.BI.wand_mono_right 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_congr` idx 6: necessary (SiProp: P=P'=Q'=False, Q=True)
theorem w4c3_75 : ¬ drop0% Iris.BI.wand_congr 6 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(False) iprop(True) iprop(False) .rfl
  H.mp 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_congr` idx 7: necessary (SiProp: P=P'=Q=True, Q'=False)
theorem w4c3_76 : ¬ drop0% Iris.BI.wand_congr 7 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) .rfl
  H.mp 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_congr_left` idx 5: necessary (SiProp: P=Q=False, P'=True)
theorem w4c3_77 : ¬ drop0% Iris.BI.wand_congr_left 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(False)
  H.mp 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_congr_right` idx 5: necessary (SiProp: P=Q=True, Q'=False)
theorem w4c3_78 : ¬ drop0% Iris.BI.wand_congr_right 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H.mp 0 (fun _ _ x => x) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_intro_left` idx 5: necessary (SiProp: P=Q=True, R=False)
theorem w4c3_79 : ¬ drop0% Iris.BI.wand_intro_left 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H 0 trivial 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wand_elim_swap` idx 5: necessary (SiProp: P=Q=True, R=False)
theorem w4c3_80 : ¬ drop0% Iris.BI.wand_elim_swap 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H 0 ⟨trivial, trivial⟩

-- `Iris.BI.sep_intro_emp_valid_left` idx 5: necessary (SiProp: P=False, Q=R=True)
theorem w4c3_81 : ¬ drop0% Iris.BI.sep_intro_emp_valid_left 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(True) .rfl
  (H 0 trivial).1

-- `Iris.BI.sep_intro_emp_valid_left` idx 6: necessary (SiProp: P=R=True, Q=False)
theorem w4c3_82 : ¬ drop0% Iris.BI.sep_intro_emp_valid_left 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(True) true_intro
  (H 0 trivial).2

-- `Iris.BI.sep_intro_emp_valid_right` idx 5: necessary (SiProp: P=False, Q=R=True)
theorem w4c3_83 : ¬ drop0% Iris.BI.sep_intro_emp_valid_right 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(True) true_intro
  (H 0 trivial).1

-- `Iris.BI.sep_intro_emp_valid_right` idx 6: necessary (SiProp: P=R=True, Q=False)
theorem w4c3_84 : ¬ drop0% Iris.BI.sep_intro_emp_valid_right 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(True) .rfl
  (H 0 trivial).2

-- `Iris.BI.sep_elim_emp_valid_left` idx 5: necessary (SiProp: P=Q=False, R=True)
theorem w4c3_85 : ¬ drop0% Iris.BI.sep_elim_emp_valid_left 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(False) iprop(True) (fun _ h => h.1)
  H 0 trivial

-- `Iris.BI.sep_elim_emp_valid_left` idx 6: necessary (SiProp: P=R=True, Q=False)
theorem w4c3_86 : ¬ drop0% Iris.BI.sep_elim_emp_valid_left 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(True) true_intro
  H 0 trivial

-- `Iris.BI.sep_elim_emp_valid_right` idx 5: necessary (SiProp: P=Q=False, R=True)
theorem w4c3_87 : ¬ drop0% Iris.BI.sep_elim_emp_valid_right 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(False) iprop(True) (fun _ h => h.2)
  H 0 trivial

-- `Iris.BI.wand_apply` idx 6: necessary (SiProp: P=Q=S=True, R=False)
theorem w4c3_88 : ¬ drop0% Iris.BI.wand_apply 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True) (fun _ _ => ⟨trivial, trivial⟩)
  H 0 trivial

-- `Iris.BI.wand_apply` idx 7: necessary (SiProp: P=R=False, Q=S=True)
theorem w4c3_89 : ¬ drop0% Iris.BI.wand_apply 7 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(False) iprop(True) (fun _ h => h.elim)
  H 0 trivial

-- `Iris.BI.wand_elim_left_trans` idx 5: necessary (SiProp: P=Q=True, R=False)
theorem w4c3_90 : ¬ drop0% Iris.BI.wand_elim_left_trans 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(True) iprop(False)
  H 0 ⟨trivial, trivial⟩

-- `Iris.BI.wandIff_congr` idx 6: necessary (SiProp: P=True, P'=Q=Q'=False)
theorem w4c3_91 : ¬ drop0% Iris.BI.wandIff_congr 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False) iprop(False) .rfl
  (H.mpr 0 ⟨(fun _ _ x => x), (fun _ _ x => x)⟩).1 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wandIff_congr` idx 7: necessary (SiProp: P'=True, P=Q=Q'=False)
theorem w4c3_92 : ¬ drop0% Iris.BI.wandIff_congr 7 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(True) iprop(False) iprop(False) .rfl
  (H.mpr 0 ⟨(fun _ _ x => x), (fun _ _ x => x)⟩).2 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wandIff_congr_left` idx 5: necessary (SiProp: P=True, P'=Q=False)
theorem w4c3_93 : ¬ drop0% Iris.BI.wandIff_congr_left 5 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False) iprop(False)
  (H.mpr 0 ⟨(fun _ _ x => x), (fun _ _ x => x)⟩).1 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wandIff_congr_right` idx 5: necessary (SiProp: P=Q=False, Q'=True)
theorem w4c3_94 : ¬ drop0% Iris.BI.wandIff_congr_right 5 := fun h =>
  have H := @h SiProp _ iprop(False) iprop(False) iprop(True)
  (H.mp 0 ⟨(fun _ _ x => x), (fun _ _ x => x)⟩).2 0 (Nat.le_refl 0) trivial

-- `Iris.BI.entails_imp` idx 4: necessary (SiProp: P=True, Q=False)
theorem w4c3_95 : ¬ drop0% Iris.BI.entails_imp 4 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  H 0 trivial 0 (Nat.le_refl 0) trivial

-- `Iris.BI.equiv_iff_thm` idx 4: necessary (SiProp: P=True, Q=False)
theorem w4c3_96 : ¬ drop0% Iris.BI.equiv_iff_thm 4 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  (H 0 trivial).1 0 (Nat.le_refl 0) trivial

-- `Iris.BI.iff_equiv` idx 6: necessary (SiProp (affine): P=True, Q=False)
theorem w4c3_97 : ¬ drop0% Iris.BI.iff_equiv 6 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  H.mp 0 trivial

-- `Iris.BI.wand_entails` idx 4: necessary (SiProp: P=True, Q=False)
theorem w4c3_98 : ¬ drop0% Iris.BI.wand_entails 4 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  H 0 trivial

-- `Iris.BI.wand_entails_emp` idx 4: necessary (SiProp: P=True, Q=False)
theorem w4c3_99 : ¬ drop0% Iris.BI.wand_entails_emp 4 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  H 0 trivial

-- `Iris.BI.entails_wand` idx 4: necessary (SiProp: P=True, Q=False)
theorem w4c3_100 : ¬ drop0% Iris.BI.entails_wand 4 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  H 0 trivial 0 (Nat.le_refl 0) trivial

-- `Iris.BI.entails_wand_emp` idx 4: necessary (SiProp: P=True, Q=False)
theorem w4c3_101 : ¬ drop0% Iris.BI.entails_wand_emp 4 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  H 0 trivial 0 (Nat.le_refl 0) trivial

-- `Iris.BI.equiv_wandIff` idx 4: necessary (SiProp: P=True, Q=False)
theorem w4c3_102 : ¬ drop0% Iris.BI.equiv_wandIff 4 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  (H 0 trivial).1 0 (Nat.le_refl 0) trivial

-- `Iris.BI.wandIff_equiv` idx 4: necessary (SiProp: P=True, Q=False)
theorem w4c3_103 : ¬ drop0% Iris.BI.wandIff_equiv 4 := fun h =>
  have H := @h SiProp _ iprop(True) iprop(False)
  H.mp 0 trivial

-- `Iris.BI.pure_elim` idx 5: necessary (SiProp: phi=False, Q=True, R=False)
theorem w4c3_104 : ¬ drop0% Iris.BI.pure_elim 5 := fun h =>
  have H := @h SiProp _ False iprop(True) iprop(False) (fun h => h.elim)
  H 0 trivial

-- `Iris.BI.pure_elim` idx 6: necessary (SiProp: phi=True, Q=True, R=False)
theorem w4c3_105 : ¬ drop0% Iris.BI.pure_elim 6 := fun h =>
  have H := @h SiProp _ True iprop(True) iprop(False) (fun _ _ => trivial)
  H 0 trivial

-- `Iris.BI.pure_mono` idx 4: necessary (SiProp: phi1=True, phi2=False)
theorem w4c3_106 : ¬ drop0% Iris.BI.pure_mono 4 := fun h =>
  have H := @h SiProp _ True False
  H 0 trivial

-- `Iris.BI.pure_congr` idx 4: necessary (SiProp: phi1=True, phi2=False)
theorem w4c3_107 : ¬ drop0% Iris.BI.pure_congr 4 := fun h =>
  have H := @h SiProp _ True False
  H.mp 0 trivial

-- `Iris.BI.pure_elim_left` idx 5: necessary (SiProp: phi=True, Q=True, R=False)
theorem w4c3_108 : ¬ drop0% Iris.BI.pure_elim_left 5 := fun h =>
  have H := @h SiProp _ True iprop(True) iprop(False)
  H 0 ⟨trivial, trivial⟩

end W4c3

namespace W4c3
open Iris Iris.BI Iris.OFE

-- `Iris.BI.imp_entails` idx 4: necessary (non-affine UPred NA: P = True, Q = emp; emp ⊢ True → emp holds, True ⊢ emp fails)
theorem w4c3_109 : ¬ drop0% Iris.BI.imp_entails 4 := fun h =>
  na_true_not_emp (@h (UPred NA) _ iprop(True) iprop(emp) (imp_intro and_elim_l))

-- `Iris.BI.iff_equiv` idx 4: necessary (non-affine UPred NA: P = True, Q = emp (affine), ⊢ True ↔ emp holds)
theorem w4c3_110 : ¬ drop0% Iris.BI.iff_equiv 4 := fun h =>
  na_true_not_emp (@h (UPred NA) _ iprop(True) iprop(emp) _
    (and_intro (imp_intro and_elim_l) (imp_intro true_intro))).mp

-- `Iris.BI.iff_equiv` idx 5: necessary (non-affine UPred NA: P = emp (affine), Q = True, ⊢ emp ↔ True holds)
theorem w4c3_111 : ¬ drop0% Iris.BI.iff_equiv 5 := fun h =>
  na_true_not_emp (@h (UPred NA) _ iprop(emp) iprop(True) _
    (and_intro (imp_intro true_intro) (imp_intro and_elim_l))).mpr

end W4c3
