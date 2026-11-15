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

namespace W2c3
open Iris Iris.OFE Iris.ORA
/-- One-point ORA, never valid, step-indexed order only at step 0, no core (from W1c3 UZ). -/
structure UZ where
instance : OFE UZ := OFE.ofDiscrete UZ
instance : Op UZ where
  op _ _ := ⟨⟩
  op_ne := ⟨fun _ _ _ _ => rfl⟩
  assoc := rfl
  comm := rfl
instance : PCore UZ where
  pcore _ := none
  pcore_ne _ h := (by cases h)
  pcore_idem h := (by cases h)
instance : Valid UZ where
  ValidN _ _ := False
  Valid _ := False
  validN_ne _ h := h
  valid_iff_validN := ⟨False.elim, fun h => h 0⟩
  validN_succ h := h
instance : Ordered UZ where
  OrderN n _ _ := n = 0
  Order _ _ := False
  ordN_ne _ _ h := h
  ordN_succ h := absurd h (Nat.succ_ne_zero _)
  ordN_trans h _ := h
  ord_trans h _ := h
  ordN_of_ord _ h := h.elim
instance uzORA : ORA UZ where
  validN_op_left h := h
  pcore_op_left h := (by cases h)
  extend h _ := h.elim
  op_monoN_left_ord _ h := h
  op_mono_left_ord _ h := h
  validN_of_ordN _ h := h
  pcore_monoN_ord _ h := (by cases h)
  pcore_mono_ord _ h := (by cases h)
  pcore_order_op h := (by cases h)
  pcore_increasing h := (by cases h)
  increasing_closed hx _ := hx
  ordN_extend hv _ := hv.elim

/-- Bool, xor, no core, all valid, empty order (from W1c3 BX): not IncOrd. -/
structure BX where b : Bool
instance : OFE BX := OFE.ofDiscrete BX
instance : OFE.Discrete BX := ⟨fun h => h⟩
@[instance_reducible] def bxData : DiscreteORAData BX where
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

/-- Bool, xor, no core, all valid, order is equality: OrderRefl, not IncOrd. -/
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

/-- Bool, or, no core, all valid, full order (from W1c3 BT): OrderRefl and IncOrd, not OrdInc. -/
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

structure UV where

instance : OFE UV := OFE.ofDiscrete UV

instance : Op UV where
  op _ _ := ⟨⟩
  op_ne := ⟨fun _ _ _ _ => rfl⟩
  assoc := rfl
  comm := rfl

instance : PCore UV where
  pcore _ := none
  pcore_ne _ h := (by cases h)
  pcore_idem h := (by cases h)

instance : Valid UV where
  ValidN n _ := n = 0
  Valid _ := False
  validN_ne _ h := h
  valid_iff_validN := ⟨False.elim, fun h => absurd (h 1) (by decide)⟩
  validN_succ h := absurd h (Nat.succ_ne_zero _)

instance : Ordered UV where
  OrderN _ _ _ := False
  Order _ _ := False
  ordN_ne _ _ h := h
  ordN_succ h := h
  ordN_trans h _ := h
  ord_trans h _ := h
  ordN_of_ord _ h := h

instance uvORA : ORA UV where
  validN_op_left h := h
  pcore_op_left h := (by cases h)
  extend _ _ := ⟨⟨⟩, ⟨⟩, rfl, rfl, rfl⟩
  op_monoN_left_ord _ h := h
  op_mono_left_ord _ h := h
  validN_of_ordN h _ := h.elim
  pcore_monoN_ord _ h := (by cases h)
  pcore_mono_ord _ h := (by cases h)
  pcore_order_op h := (by cases h)
  pcore_increasing h := (by cases h)
  increasing_closed hx _ := hx
  ordN_extend _ h := h.elim

instance : ORA.Discrete BX := ORA.ofDiscreteORAData_discrete bxData

instance : ORA.Discrete BT := ORA.ofDiscreteORAData_discrete btData

instance : ORA.Discrete BE := ORA.ofDiscreteORAData_discrete beData

instance unitCoreId : CoreId () := ⟨rfl⟩

theorem qne : ¬ (1 : Qp) ≼{0} 1 := fun ⟨z, hz⟩ => by
  have := z.2; simp at hz; grind

theorem qne' : ¬ (1 : Qp) ≼ 1 := fun ⟨z, hz⟩ => by
  have := z.2; simp at hz; grind

theorem q2 : ¬ ✓{0} ((1 + 1 : Qp)) := by
  intro h; have : ((1:Qp)+1).val ≤ 1 := h; grind

theorem q2ne : (1 : Qp) ≠ 1 + 1 := fun h => by
  have := congrArg Subtype.val h; grind

theorem qv (n : Nat) : ✓{n} ((●F{DFrac.own 1} (1 : Qp)) • ◯F{1} (1 : Qp)) :=
  Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨none, .inl ⟨rfl, rfl⟩⟩, ⟨Qp.valid_one, Qp.valid_one⟩⟩

theorem qv' : ✓ ((●F{DFrac.own 1} (1 : Qp)) • ◯F{1} (1 : Qp)) :=
  valid_iff_validN.mpr qv

theorem bxv : ✓ ((●F{DFrac.own 1} (⟨false⟩ : BX)) • ◯F{Qp.quarter} (⟨true⟩ : BX)) :=
  Auth.both_dfrac_valid_frame.mpr ⟨DFrac.valid_own_one, fun _ => ⟨some (Qp.threeQuarters, ⟨true⟩), .inl ⟨q_sum, rfl⟩⟩, valid_iff_validN.mpr fun _ => ⟨Qp.valid_one, trivial⟩⟩

theorem bev (n : Nat) : ✓{n} ((●F{DFrac.own 1} (⟨false⟩ : BE)) • ◯F{Qp.quarter} (⟨true⟩ : BE)) :=
  Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨some (Qp.threeQuarters, ⟨true⟩), .inl ⟨q_sum, rfl⟩⟩, ⟨Qp.valid_one, trivial⟩⟩

theorem btv (n : Nat) : ✓{n} ((●F{DFrac.own 1} (⟨false⟩ : BT)) • ◯F{Qp.quarter} (⟨true⟩ : BT)) :=
  Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨none, .inr ⟨⟨Qp.threeQuarters, q_sum.symm⟩, trivial⟩⟩, ⟨Qp.valid_one, trivial⟩⟩

/-- Truncation OFE on naturals (from Probe1 TN): 1 and 2 agree at step 0. -/
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

theorem tn12 : (⟨1⟩ : TN) ≡{0}≡ ⟨2⟩ := rfl

theorem tn12ne : (⟨1⟩ : TN) ≠ ⟨2⟩ := by simp

theorem ml_not_inc : ¬ (◯ML [()] : MonoList Unit) ≼ ◯ML [] := fun ⟨w, hw⟩ => by
  have hv : ✓ ((●ML ([] : List Unit)) • ◯ML []) := (MonoList.both_valid _ _).mpr (List.prefix_refl _)
  have : ✓ ((●ML ([] : List Unit)) • ◯ML [()]) :=
    valid_of_inc ⟨w, by rw [hw, assoc]⟩ hv
  have := (MonoList.both_valid _ _).mp this
  simp at this

abbrev FN := fun V => Nat → Option V

theorem dq_inc (n : Nat) : DFrac.own Qp.quarter ≼{n} DFrac.own 1 := ⟨DFrac.own Qp.threeQuarters, congrArg DFrac.own q_sum.symm⟩

theorem bt_heapR (n : Nat) : HeapR Nat BT FN n (fun _ => some ⟨false⟩) (fun _ => some (DFrac.own Qp.quarter, ⟨true⟩)) := by
  intro k fv hk
  cases hk
  exact ⟨⟨false⟩, DFrac.own 1, rfl, ⟨DFrac.valid_own_one, trivial⟩, none, .inr ⟨dq_inc n, trivial⟩⟩

/-- Bool, op constantly true, no core, all valid, step-indexed order total, order is implication:
OrderRefl and IncOrd, not OrdInc, not ORA.Discrete (false below true at every step, true not below false). -/
structure BK where b : Bool

instance : OFE BK := OFE.ofDiscrete BK

instance : Op BK where
  op _ _ := ⟨true⟩
  op_ne := ⟨fun _ _ _ _ => rfl⟩
  assoc := rfl
  comm := rfl

instance : PCore BK where
  pcore _ := none
  pcore_ne _ h := (by cases h)
  pcore_idem h := (by cases h)

instance : Valid BK where
  ValidN _ _ := True
  Valid _ := True
  validN_ne _ h := h
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ h := h

instance : Ordered BK where
  OrderN _ _ _ := True
  Order x y := (or (!x.b) y.b) = true
  ordN_ne _ _ h := h
  ordN_succ h := h
  ordN_trans h _ := h
  ord_trans {x y z} h1 h2 := by
    rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> simp_all
  ordN_of_ord _ _ := trivial

instance bkORA : ORA BK where
  validN_op_left _ := trivial
  pcore_op_left h := (by cases h)
  extend {_ x y₁ y₂} _ e := ⟨y₁, y₂, e, .rfl, .rfl⟩
  op_monoN_left_ord _ _ := trivial
  op_mono_left_ord _ _ := rfl
  validN_of_ordN _ _ := trivial
  pcore_monoN_ord _ h := (by cases h)
  pcore_mono_ord _ h := (by cases h)
  pcore_order_op h := (by cases h)
  pcore_increasing h := (by cases h)
  increasing_closed _ _ := ⟨fun y => by rcases y with ⟨_|_⟩ <;> rfl⟩
  ordN_extend _ _ := ⟨_, trivial, .rfl⟩

instance bkRefl : OrderRefl BK := ⟨fun x => by rcases x with ⟨_|_⟩ <;> rfl⟩

instance bkIncOrd : IncOrd BK := ⟨fun {x y} ⟨z, hz⟩ => by subst hz; rcases x with ⟨_|_⟩ <;> rfl⟩

abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare

abbrev sg {V : Type} (x : V) : TM V := Iris.Std.PartialMap.insert ∅ 0 x

theorem sg_get {V : Type} (x : V) : Iris.Std.get? (sg x) 0 = some x := Iris.Std.LawfulPartialMap.get?_insert_eq rfl

theorem emp_get {V : Type} (k : Nat) : Iris.Std.get? (∅ : TM V) k = none := Iris.Std.LawfulPartialMap.get?_empty k

theorem dq2 : ¬ ✓ (DFrac.own (1 + 1)) := fun h => by
  have : ((1:Qp)+1).val ≤ 1 := h; grind

/-- Validity of auth with fragment implies validity of the fragment's pair. -/
theorem hv_frag {V : Type} [ORA V] {dp : DFrac} {m : TM V} {k : Nat} {dq : DFrac} {v : V} {n : Nat}
    (h : ✓{n} (HeapView.Auth dp m • HeapView.Frag k dq v : HeapView Nat V TM)) : ✓{n} (dq, v) := by
  obtain ⟨v', dq', -, -, hv, c, hc⟩ := HeapView.auth_op_frag_validN_iff_frame.mp h
  have h1 : ✓{n} (some (dq, v) • c) := validN_of_ordN hc (show ✓{n} (some (dq', v')) from hv)
  exact ORA.validN_op_left (α := Option (DFrac × V)) h1

theorem bk_v (n : Nat) : ✓{n} (HeapView.Auth (DFrac.own 1) (sg (⟨false⟩ : BK)) • HeapView.Frag 0 (DFrac.own Qp.quarter) (⟨true⟩ : BK) : HeapView Nat BK TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨⟨false⟩, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, trivial⟩, none, .inr ⟨dq_inc n, trivial⟩⟩

theorem bt_v (n : Nat) : ✓{n} (HeapView.Auth (DFrac.own 1) (sg (⟨false⟩ : BT)) • HeapView.Frag 0 (DFrac.own Qp.quarter) (⟨true⟩ : BT) : HeapView Nat BT TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨⟨false⟩, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, trivial⟩, none, .inr ⟨dq_inc n, trivial⟩⟩

theorem bx_v (n : Nat) : ✓{n} (HeapView.Auth (DFrac.own 1) (sg (⟨false⟩ : BX)) • HeapView.Frag 0 (DFrac.own Qp.quarter) (⟨true⟩ : BX) : HeapView Nat BX TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨⟨false⟩, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, trivial⟩,
    some (DFrac.own Qp.threeQuarters, ⟨true⟩), .inl ⟨congrArg DFrac.own q_sum, rfl⟩⟩

theorem be_v (n : Nat) : ✓{n} (HeapView.Auth (DFrac.own 1) (sg (⟨false⟩ : BE)) • HeapView.Frag 0 (DFrac.own Qp.quarter) (⟨true⟩ : BE) : HeapView Nat BE TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨⟨false⟩, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, trivial⟩,
    some (DFrac.own Qp.threeQuarters, ⟨true⟩), .inl ⟨congrArg DFrac.own q_sum, rfl⟩⟩

theorem qp_v (n : Nat) : ✓{n} (HeapView.Auth (DFrac.own 1) (sg 1) • HeapView.Frag 0 (DFrac.own 1) 1 : HeapView Nat Qp TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨1, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, Qp.valid_one⟩, none, .inl .rfl⟩

theorem un_v (n : Nat) : ✓{n} (HeapView.Auth (DFrac.own 1) (sg ()) • HeapView.Frag 0 (DFrac.own 1) () : HeapView Nat Unit TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨(), DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, trivial⟩, none, .inl .rfl⟩

theorem bk_fv : ✓ ((●F{DFrac.own 1} (⟨false⟩ : BK)) • ◯F{Qp.quarter} (⟨true⟩ : BK)) :=
  Auth.both_dfrac_valid_frame.mpr ⟨DFrac.valid_own_one, fun _ => ⟨none, .inr ⟨⟨Qp.threeQuarters, q_sum.symm⟩, trivial⟩⟩,
    valid_iff_validN.mpr fun _ => ⟨Qp.valid_one, trivial⟩⟩

theorem ins_get {V : Type} (x y : V) : Iris.Std.get? (Iris.Std.PartialMap.insert (sg x) 0 y) 0 = some y :=
  Iris.Std.LawfulPartialMap.get?_insert_eq rfl

abbrev TS := Std.ExtTreeSet Nat compare

instance : Iris.Std.DecidableDisj TS := Iris.Std.LawfulSet.disjoint_dec

theorem m00 : (0 : Nat) ∈ ({0} : TS) := Iris.Std.LawfulSet.mem_singleton.mpr rfl

theorem nd00 : ¬ (({0} : TS) ## {0}) := fun hd => hd 0 ⟨m00, m00⟩

theorem e00 : (DisjointLeibnizSet.valid ({0} : TS) • DisjointLeibnizSet.valid {0}) = .error := by
  rcases h : (DisjointLeibnizSet.valid ({0} : TS) • DisjointLeibnizSet.valid {0}) with s | _
  · exact absurd (DisjointLeibnizSet.valid_op_iff_disj.mp (h ▸ DisjointLeibnizSet.valid_set)) nd00
  · rfl

theorem e0x : (DisjointLeibnizSet.valid (∅ : TS) • DisjointLeibnizSet.valid {0}) = .valid {0} :=
  (DisjointLeibnizSet.disj_op_union Iris.Std.LawfulSet.disjoint_empty_left).trans
    (congrArg _ Iris.Std.LawfulSet.union_empty_left)

theorem bemp {V : Type} [ORA V] (dq : DFrac) :
    Iris.Algebra.bigOpM (M := HeapView Nat V TM) Iris.Op.op (fun k v => HeapView.Frag k dq v) (∅ : TM V) = UORA.unit :=
  Iris.Algebra.BigOpM.bigOpM_empty (M := HeapView Nat V TM) (M' := TM) (K := Nat) (op := Op.op) (V := V) _

theorem bsg {V : Type} [ORA V] (dq : DFrac) (x : V) :
    Iris.Algebra.bigOpM (M := HeapView Nat V TM) Iris.Op.op (fun k v => HeapView.Frag k dq v) (sg x) = HeapView.Frag 0 dq x := by
  rw [Iris.Algebra.BigOpM.bigOpM_insert_eq _ _ (emp_get 0), bemp, unit_right_id]

abbrev BF (V : Type) [ORA V] (dq : DFrac) (m : TM V) : HeapView Nat V TM :=
  Iris.Algebra.bigOpM (M := HeapView Nat V TM) Iris.Op.op (fun k v => HeapView.Frag k dq v) m

abbrev AU (V : Type) [ORA V] (m : TM V) : HeapView Nat V TM := HeapView.Auth (DFrac.own 1) m

theorem bemp' {V : Type} [ORA V] (dq : DFrac) : BF V dq ∅ = UORA.unit := bemp dq

theorem bsg' {V : Type} [ORA V] (dq : DFrac) (x : V) : BF V dq (sg x) = HeapView.Frag 0 dq x := bsg dq x

def qtwo : Qp := 1 + 1

theorem disj_sg_emp {V : Type} (x : V) : Iris.Std.PartialMap.disjoint (sg x) (∅ : TM V) :=
  (Iris.Std.PartialMap.disjoint_iff _ _).mpr fun k => .inr (emp_get k)

/-- Three elements a, b, bad: op constantly bad, valid iff not bad, order b ≤ a and bad ≤ bad, no core.
Not OrdInc (b ≤ a but a is no product); local updates from (a, b) hold vacuously. -/
inductive T3 where | a | b | bad
deriving DecidableEq

instance : OFE T3 := OFE.ofDiscrete T3

instance : OFE.Discrete T3 := ⟨fun h => h⟩

@[instance_reducible] def t3Data : DiscreteORAData T3 where
  pcore _ := none
  op _ _ := .bad
  Valid x := x ≠ .bad
  Order x y := (x = .b ∧ y = .a) ∨ (x = .bad ∧ y = .bad)
  assoc _ _ _ := rfl
  comm _ _ := rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ h := absurd rfl h
  ord_trans x y z h1 h2 := by
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h3, rfl⟩ | ⟨h3, rfl⟩ <;> cases h3 <;> simp
  op_mono_left _ _ _ _ := .inr ⟨rfl, rfl⟩
  valid_of_ord x y h hv := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact T3.noConfusion
    · exact hv
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed x _ hx _ _ := by
    rcases hx .a with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

instance t3ORA : ORA T3 := ORA.ofDiscreteORAData t3Data

theorem t3_lu (a' b' : T3) : ((T3.a, T3.b) : T3 × T3) ~l~> (a', b') := fun n mz _ e => by
  rcases mz with _ | z
  · cases (e : T3.a = T3.b)
  · cases (e : T3.a = T3.bad)

theorem t3_fv : ✓{0} ((●F{DFrac.own 1} T3.a) • ◯F{Qp.quarter} T3.b) :=
  Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨none, .inr ⟨⟨Qp.threeQuarters, q_sum.symm⟩, .inl ⟨rfl, rfl⟩⟩⟩,
    ⟨Qp.valid_one, T3.noConfusion⟩⟩

theorem t3_hv : ✓{0} (HeapView.Auth (DFrac.own 1) (sg T3.a) • HeapView.Frag 0 (DFrac.own Qp.quarter) T3.b : HeapView Nat T3 TM) :=
  HeapView.auth_op_frag_validN_iff_frame.mpr ⟨.a, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, T3.noConfusion⟩,
    none, .inr ⟨dq_inc 0, .inl ⟨rfl, rfl⟩⟩⟩

theorem fr_get {V : Type} (dq : DFrac) (x : V) :
    Iris.Std.get? (Iris.Std.PartialMap.singleton 0 (dq, x) : TM (DFrac × V)) 0 = some (dq, x) :=
  Iris.Std.LawfulPartialMap.get?_insert_eq rfl

end W2c3

open Iris Iris.OFE Iris.ORA W2c3

-- `HeapR.of_inc` (hypothesis 8): necessary, V=Unit, Nat->Option heaps: m empty, f = (own 1, ()) everywhere; no entry of m at key 0
theorem w2c3_0 : ¬ drop0% HeapR.of_inc 8 := fun h => by
  obtain ⟨v, dq, hm, -⟩ := @h Nat Unit FN _ _ 0 (fun _ => none) (fun _ => some (DFrac.own 1, ())) 0 _ rfl
  cases hm

-- `HeapR.iff_inc` (hypothesis 5): necessary, V=BT (or, full order, not OrdInc): fragment (1/4,true) below (own 1,false) is HeapR but not HeapRInc (true or z is never false)
theorem w2c3_1 : ¬ drop0% HeapR.iff_inc 5 := fun h => by
  obtain ⟨v, dq, hm, -, z, hz⟩ := (@h Nat BT FN _ _ 0 _ _).mp (bt_heapR 0) 0 _ rfl
  cases hm
  rcases z with _ | ⟨z⟩ <;> cases hz.2

-- `HeapR.singleton_get_iff_ord` (hypothesis 5): necessary, V=BX (xor, empty order, not IncOrd): (1/4,true) with frame (3/4,true) equals (1,false), but (1/4,true) is not ordered below (dq',false)
theorem w2c3_2 : ¬ drop0% HeapR.singleton_get_iff_ord 5 := fun h => by
  obtain ⟨v, dq, hm, -, hz⟩ := (@h Nat BX FN _ _ 0 (fun _ => some ⟨false⟩) 0 (DFrac.own Qp.quarter) ⟨true⟩).mp
    ((HeapR.singleton_get_iff_frame ..).mpr ⟨⟨false⟩, DFrac.own 1, rfl, ⟨DFrac.valid_own_one, trivial⟩,
      some (DFrac.own Qp.threeQuarters, ⟨true⟩), .inl ⟨congrArg DFrac.own q_sum, rfl⟩⟩)
  cases hm
  rcases hz with hz | hz
  · cases hz.2
  · exact hz.2

-- `HeapR.singleton_get_iff` (hypothesis 5): necessary, V=BT: singleton (1/4,true) under m 0 = false is HeapR but (1/4,true) is not included in any (dq',false)
theorem w2c3_3 : ¬ drop0% HeapR.singleton_get_iff 5 := fun h => by
  obtain ⟨v, dq, hm, -, z, hz⟩ := (@h Nat BT FN _ _ 0 (fun _ => some ⟨false⟩) 0 (DFrac.own Qp.quarter) ⟨true⟩).mp
    ((HeapR.singleton_get_iff_frame ..).mpr ⟨⟨false⟩, DFrac.own 1, rfl, ⟨DFrac.valid_own_one, trivial⟩, none, .inr ⟨dq_inc 0, trivial⟩⟩)
  cases hm
  rcases z with _ | ⟨z⟩ <;> cases hz.2

-- `HeapR.instIsViewRelDiscreteProdDFracOfDiscrete` (hypothesis 5): necessary, V=UV (valid only at step 0): heap relation holds at step 0, not at step 1 (value not valid at 1)
theorem w2c3_4 : ¬ drop0% HeapR.instIsViewRelDiscreteProdDFracOfDiscrete 5 := fun h => by
  have h0 : HeapR Nat UV FN 0 (fun _ => some ⟨⟩) (fun _ => some (DFrac.own 1, ⟨⟩)) := by
    intro k fv hk; cases hk
    exact ⟨⟨⟩, DFrac.own 1, rfl, ⟨DFrac.valid_own_one, rfl⟩, none, .inl .rfl⟩
  obtain ⟨v, dq, hm, hv, -⟩ := (@h Nat UV FN _ _).discrete 1 _ _ h0 0 _ rfl
  cases hm
  exact Nat.succ_ne_zero 0 hv.2

-- `HeapView.instIsOpViewProdDFracHeapRAuth` (hypothesis 10): necessary, V=Unit, dq=dq1=dq2=own 1: Auth 1 m = Auth 1 m * Auth 1 m would make the invalid product valid
theorem w2c3_5 : ¬ drop0% HeapView.instIsOpViewProdDFracHeapRAuth 10 := fun h => by
  have := (@h Nat Unit TM _ _ (DFrac.own 1) ∅ .merge (DFrac.own 1) (DFrac.own 1)).is_op
  exact HeapView.auth_one_op_auth_one_valid_iff.mp (this ▸ HeapView.auth_one_valid)

-- `HeapView.auth_ord_of_map_eq` (hypothesis 8): necessary, V=Unit, m1 empty, m2 = {0:()}: Auth m1 below Auth m2 would make Auth m1 * Frag 0 (own 1) () valid
theorem w2c3_6 : ¬ drop0% HeapView.auth_ord_of_map_eq 8 := fun h => by
  have h1 := op_mono_left_ord (HeapView.Frag 0 (DFrac.own 1) ()) (@h Nat Unit TM _ _ ∅ (sg ()) (DFrac.own 1))
  have h2 := validN_of_ordN (ordN_of_ord 0 h1) (un_v 0)
  obtain ⟨v, dq, -, hm, -⟩ := HeapView.auth_op_frag_validN_iff_frame.mp h2
  rw [emp_get] at hm; cases hm

-- `HeapView.dist_of_validN_auth_op` (hypothesis 10): necessary, m1 empty, m2 = all () (Nat->Option): not 0-equal
theorem w2c3_7 : ¬ drop0% HeapView.dist_of_validN_auth_op 10 := fun h => by
  have := @h Nat Unit FN _ _ (DFrac.own 1) (DFrac.own 1) 0 (fun _ => none) (fun _ => some ()) 0
  cases this

-- `HeapView.equiv_of_valid_auth_op` (hypothesis 9): necessary, m1 empty, m2 = all (): not equal
theorem w2c3_8 : ¬ drop0% HeapView.equiv_of_valid_auth_op 9 := fun h => by
  have := congrFun (@h Nat Unit FN _ _ (DFrac.own 1) (DFrac.own 1) (fun _ => none) (fun _ => some ())) 0
  cases this

-- `HeapView.instIsOpViewSemiOutParamCoreToInOutProdDFracHeapRFrag` (hypothesis 14): necessary, V=Qp, dp = discard*discard, v = v1 = v2 = 1: Frag 0 _ 1 valid but Frag 0 _ (1+1) not
theorem w2c3_9 : ¬ drop0% HeapView.instIsOpViewSemiOutParamCoreToInOutProdDFracHeapRFrag 14 := fun h => by
  have e := (@h Nat Qp TM _ _ (DFrac.discard • DFrac.discard) 0 1 1 .merge DFrac.discard DFrac.discard 1 (isOpMerge_op _ _)).is_op
  rw [← HeapView.frag_op_eqv] at e
  have hv : ✓ (HeapView.Frag 0 (DFrac.discard • DFrac.discard) (1 : Qp) : HeapView Nat Qp TM) :=
    HeapView.frag_valid_iff.mpr ⟨DFrac.valid_discard, Qp.valid_one⟩
  rw [e] at hv
  exact q2 ((HeapView.frag_valid_iff.mp hv).2.validN)

-- `HeapView.auth_op_frag_validN_iff` (hypothesis 11): necessary, V=BT (not OrdInc): Auth(own 1){0:false} * Frag 0 (1/4) true valid via order, but no inclusion witness
theorem w2c3_10 : ¬ drop0% HeapView.auth_op_frag_validN_iff 11 := fun h => by
  obtain ⟨v, dq, -, hm, -, z, hz⟩ := (@h Nat BT TM _ _ _ _ 0 _ _ _).mp (bt_v 0)
  rw [sg_get] at hm; cases hm
  rcases z with _ | ⟨z⟩ <;> cases hz.2

-- `HeapView.auth_op_frag_validN_total_iff_ord` (hypothesis 11): necessary, V=Qp (IncOrd, not OrderRefl): m{0:1}, Frag 0 (own 1) 1 valid; 1 is not below 1 in Qp
theorem w2c3_11 : ¬ drop0% HeapView.auth_op_frag_validN_total_iff_ord 11 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := @h Nat Qp TM _ _ _ _ 0 _ _ _ _ (qp_v 0)
  rw [sg_get] at hm; cases hm; exact qne hz

-- `HeapView.auth_op_frag_validN_total_iff_ord` (hypothesis 12): necessary, V=BE (xor, order = equality, OrderRefl, not IncOrd): valid via frame (3/4,true); true not below false
theorem w2c3_12 : ¬ drop0% HeapView.auth_op_frag_validN_total_iff_ord 12 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := @h Nat BE TM _ _ _ _ 0 _ _ _ _ (be_v 0)
  rw [sg_get] at hm; cases hm; cases hz

-- `HeapView.auth_op_frag_validN_total_iff_ord` (hypothesis 13): necessary, V=Unit, empty heap: no value at key 0
theorem w2c3_13 : ¬ drop0% HeapView.auth_op_frag_validN_total_iff_ord 13 := fun h => by
  obtain ⟨v, -, -, hm, -⟩ := @h Nat Unit TM _ _ (DFrac.own 1) (DFrac.own 1) 0 ∅ 0 () _ _
  rw [emp_get] at hm; cases hm

-- `HeapView.auth_op_frag_validN_total_iff` (hypothesis 11): necessary, V=Qp (OrdInc, not OrderRefl): 1 not included in 1
theorem w2c3_14 : ¬ drop0% HeapView.auth_op_frag_validN_total_iff 11 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := @h Nat Qp TM _ _ _ _ 0 _ _ _ _ (qp_v 0)
  rw [sg_get] at hm; cases hm; exact qne hz

-- `HeapView.auth_op_frag_validN_total_iff` (hypothesis 12): necessary, V=BT (OrderRefl, not OrdInc): true not included in false
theorem w2c3_15 : ¬ drop0% HeapView.auth_op_frag_validN_total_iff 12 := fun h => by
  obtain ⟨v, -, -, hm, -, z, hz⟩ := @h Nat BT TM _ _ _ _ 0 _ _ _ _ (bt_v 0)
  rw [sg_get] at hm; cases hm; cases hz

-- `HeapView.auth_op_frag_validN_total_iff` (hypothesis 13): necessary, V=Unit, empty heap: no value at key 0
theorem w2c3_16 : ¬ drop0% HeapView.auth_op_frag_validN_total_iff 13 := fun h => by
  obtain ⟨v, -, -, hm, -⟩ := @h Nat Unit TM _ _ (DFrac.own 1) (DFrac.own 1) 0 ∅ 0 () _ _
  rw [emp_get] at hm; cases hm

-- `HeapView.auth_op_frag_discrete_valid_iff_frame` (hypothesis 10): necessary, V=BK (op constantly true, step-indexed order total, order = implication; not ORA.Discrete): valid at every step, but true is not below false in the full order
theorem w2c3_17 : ¬ drop0% HeapView.auth_op_frag_discrete_valid_iff_frame 10 := fun h => by
  obtain ⟨v, dq, -, hm, -, z, hz⟩ := (@h Nat BK TM _ _ _ _ _ 0 _).mp (valid_iff_validN.mpr bk_v)
  rw [sg_get] at hm; cases hm
  rcases z with _ | ⟨z⟩
  · rcases hz with hz | hz
    · cases congrArg Prod.snd hz
    · cases hz.2
  · rcases hz with hz | hz
    · cases congrArg Prod.snd hz
    · cases hz.2

-- `HeapView.auth_op_frag_discrete_valid_iff_ord` (hypothesis 10): necessary, V=BK (IncOrd, not ORA.Discrete): valid, but (1/4,true) not below (dq',false) in the full order
theorem w2c3_18 : ¬ drop0% HeapView.auth_op_frag_discrete_valid_iff_ord 10 := fun h => by
  obtain ⟨v, dq, -, hm, -, hz⟩ := (@h Nat BK TM _ _ _ _ _ 0 _ _).mp (valid_iff_validN.mpr bk_v)
  rw [sg_get] at hm; cases hm
  rcases hz with hz | hz
  · cases congrArg Prod.snd hz
  · cases hz.2

-- `HeapView.auth_op_frag_discrete_valid_iff_ord` (hypothesis 11): necessary, V=BX (discrete, not IncOrd): valid via frame (3/4,true), but not ordered
theorem w2c3_19 : ¬ drop0% HeapView.auth_op_frag_discrete_valid_iff_ord 11 := fun h => by
  obtain ⟨v, dq, -, hm, -, hz⟩ := (@h Nat BX TM _ _ _ _ _ 0 _ _).mp (valid_iff_validN.mpr bx_v)
  rw [sg_get] at hm; cases hm
  rcases hz with hz | hz
  · cases congrArg Prod.snd hz
  · exact hz.2

-- `HeapView.auth_op_frag_discrete_valid_iff` (hypothesis 11): necessary, V=BT (discrete, not OrdInc): valid, but (1/4,true) not included in (dq',false)
theorem w2c3_21 : ¬ drop0% HeapView.auth_op_frag_discrete_valid_iff 11 := fun h => by
  obtain ⟨v, dq, -, hm, -, z, hz⟩ := (@h Nat BT TM _ _ _ _ _ 0 _ _).mp (valid_iff_validN.mpr bt_v)
  rw [sg_get] at hm; cases hm
  rcases z with _ | ⟨⟨a, b⟩⟩
  · exact Bool.false_ne_true (congrArg (fun p => p.2.b) (Option.some.inj hz))
  · have : (some (dq, (⟨false⟩ : BT)) : Option (DFrac × BT)) = some (DFrac.own Qp.quarter • a, ⟨true⟩) := hz
    exact Bool.false_ne_true (congrArg (fun p => p.2.b) (Option.some.inj this))

-- `HeapView.auth_op_frag_valid_total_discrete_iff_ord` (hypothesis 10): necessary, V=Qp (discrete, IncOrd, not OrderRefl): 1 not below 1
theorem w2c3_22 : ¬ drop0% HeapView.auth_op_frag_valid_total_discrete_iff_ord 10 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := @h Nat Qp TM _ _ _ _ _ 0 _ _ _ (valid_iff_validN.mpr qp_v)
  rw [sg_get] at hm; cases hm; exact qne' hz

-- `HeapView.auth_op_frag_valid_total_discrete_iff_ord` (hypothesis 11): necessary, V=BK (OrderRefl, IncOrd, not discrete): valid, true not below false
theorem w2c3_23 : ¬ drop0% HeapView.auth_op_frag_valid_total_discrete_iff_ord 11 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := @h Nat BK TM _ _ _ _ _ 0 _ _ _ (valid_iff_validN.mpr bk_v)
  rw [sg_get] at hm; cases hm; cases hz

-- `HeapView.auth_op_frag_valid_total_discrete_iff_ord` (hypothesis 12): necessary, V=BE (OrderRefl, discrete, not IncOrd): true not below false
theorem w2c3_24 : ¬ drop0% HeapView.auth_op_frag_valid_total_discrete_iff_ord 12 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := @h Nat BE TM _ _ _ _ _ 0 _ _ _ (valid_iff_validN.mpr be_v)
  rw [sg_get] at hm; cases hm; cases hz

-- `HeapView.auth_op_frag_valid_total_discrete_iff_ord` (hypothesis 13): necessary, V=Unit, empty heap
theorem w2c3_25 : ¬ drop0% HeapView.auth_op_frag_valid_total_discrete_iff_ord 13 := fun h => by
  obtain ⟨v, -, -, hm, -⟩ := @h Nat Unit TM _ _ (DFrac.own 1) (DFrac.own 1) ∅ 0 () _ _ _
  rw [emp_get] at hm; cases hm

-- `HeapView.auth_op_frag_valid_total_discrete_iff` (hypothesis 10): necessary, V=Qp (discrete, OrdInc, not OrderRefl): 1 not included in 1
theorem w2c3_26 : ¬ drop0% HeapView.auth_op_frag_valid_total_discrete_iff 10 := fun h => by
  obtain ⟨v, -, -, hm, -, hz⟩ := @h Nat Qp TM _ _ _ _ _ 0 _ _ _ (valid_iff_validN.mpr qp_v)
  rw [sg_get] at hm; cases hm; exact qne' hz

-- `HeapView.auth_op_frag_valid_total_discrete_iff` (hypothesis 12): necessary, V=BT (OrderRefl, discrete, not OrdInc): true not included in false
theorem w2c3_28 : ¬ drop0% HeapView.auth_op_frag_valid_total_discrete_iff 12 := fun h => by
  obtain ⟨v, -, -, hm, -, z, hz⟩ := @h Nat BT TM _ _ _ _ _ 0 _ _ _ (valid_iff_validN.mpr bt_v)
  rw [sg_get] at hm; cases hm; cases hz

-- `HeapView.auth_op_frag_valid_total_discrete_iff` (hypothesis 13): necessary, V=Unit, empty heap
theorem w2c3_29 : ¬ drop0% HeapView.auth_op_frag_valid_total_discrete_iff 13 := fun h => by
  obtain ⟨v, -, -, hm, -⟩ := @h Nat Unit TM _ _ (DFrac.own 1) (DFrac.own 1) ∅ 0 () _ _ _
  rw [emp_get] at hm; cases hm

-- `HeapView.instCoreIdFragOfDFrac` (hypothesis 8): necessary, V=Unit, dq = own 1: CoreId would give Frag*Frag = Frag, i.e. own 2 valid
theorem w2c3_30 : ¬ drop0% HeapView.instCoreIdFragOfDFrac 8 := fun h => by
  have e := @op_self _ _ (HeapView.Frag 0 (DFrac.own 1) () : HeapView Nat Unit TM) (@h Nat Unit TM _ _ (DFrac.own 1) 0 () unitCoreId)
  rw [← HeapView.frag_op_eqv] at e
  have hv : ✓ (HeapView.Frag 0 (DFrac.own 1) () : HeapView Nat Unit TM) :=
    HeapView.frag_valid_iff.mpr ⟨DFrac.valid_own_one, trivial⟩
  rw [← e] at hv
  exact dq2 (HeapView.frag_valid_iff.mp hv).1

-- `HeapView.instCoreIdFragOfDFrac` (hypothesis 9): necessary, V=Qp, dq = discard, v1 = 1: CoreId would give Frag 0 discard (1+1) valid
theorem w2c3_31 : ¬ drop0% HeapView.instCoreIdFragOfDFrac 9 := fun h => by
  have e := @op_self _ _ (HeapView.Frag 0 DFrac.discard (1 : Qp) : HeapView Nat Qp TM) (@h Nat Qp TM _ _ DFrac.discard 0 1 inferInstance)
  rw [← HeapView.frag_op_eqv] at e
  have hv : ✓ (HeapView.Frag 0 DFrac.discard (1 : Qp) : HeapView Nat Qp TM) :=
    HeapView.frag_valid_iff.mpr ⟨DFrac.valid_discard, Qp.valid_one⟩
  rw [← e] at hv
  exact q2 ((HeapView.frag_valid_iff.mp hv).2.validN)

-- `HeapView.update_one_alloc` (hypothesis 9): necessary, V=Unit, m1 = {0:()}, frame Frag 0 (own 1) (): allocating over the existing key gives own 2
theorem w2c3_32 : ¬ drop0% HeapView.update_one_alloc 9 := fun h => by
  have := @h Nat Unit TM _ _ (DFrac.own 1) (sg ()) 0 () DFrac.valid_own_one trivial 0
    (some (HeapView.Frag 0 (DFrac.own 1) ())) (un_v 0)
  have h2 : ✓{0} ((HeapView.Auth (DFrac.own 1) (Iris.Std.PartialMap.insert (sg ()) 0 ()) • HeapView.Frag 0 (DFrac.own 1) ()) •
      HeapView.Frag 0 (DFrac.own 1) () : HeapView Nat Unit TM) := this
  rw [← assoc, ← HeapView.frag_op_eqv] at h2
  exact dq2 (hv_frag h2).1

-- `HeapView.update_one_alloc` (hypothesis 10): necessary, dq = own 2 (invalid): the new fragment is invalid
theorem w2c3_33 : ¬ drop0% HeapView.update_one_alloc 10 := fun h => by
  have := @h Nat Unit TM _ _ (DFrac.own (1 + 1)) ∅ 0 () (emp_get 0) trivial 0 none
    (HeapView.auth_validN_iff.mpr DFrac.valid_own_one)
  exact dq2 (hv_frag this).1

-- `HeapView.update_one_alloc` (hypothesis 11): necessary, V=UZ (never valid): the new fragment is invalid
theorem w2c3_34 : ¬ drop0% HeapView.update_one_alloc 11 := fun h => by
  have := @h Nat UZ TM _ _ (DFrac.own 1) ∅ 0 ⟨⟩ (emp_get 0) DFrac.valid_own_one 0 none
    (HeapView.auth_validN_iff.mpr DFrac.valid_own_one)
  exact (hv_frag this).2

-- `HeapView.update_auth_op_frag_frame` (hypothesis 12): necessary, dq' = own 2: target fragment invalid, source Auth{0:()} * Frag 0 (own 1) () valid
theorem w2c3_35 : ¬ drop0% HeapView.update_auth_op_frag_frame 12 := fun h =>
  dq2 (hv_frag (@h Nat Unit TM _ _ (DFrac.own 1) (sg ()) 0 () () (DFrac.own (1 + 1)) () 0 none (un_v 0))).1

-- `HeapView.update_auth_op_frag_ord` (hypothesis 12): necessary, dq' = own 2: target fragment invalid, source Auth{0:()} * Frag 0 (own 1) () valid
theorem w2c3_36 : ¬ drop0% HeapView.update_auth_op_frag_ord 12 := fun h =>
  dq2 (hv_frag (@h Nat Unit TM _ _ (DFrac.own 1) (sg ()) 0 () () (DFrac.own (1 + 1)) () 0 none (un_v 0))).1

-- `HeapView.update_auth_op_frag` (hypothesis 12): necessary, V=T3 (op constantly bad, b below a, not OrdInc): Hup holds vacuously for m1{0:a}, v = b; source valid via order, target value bad invalid
theorem w2c3_37 : ¬ drop0% HeapView.update_auth_op_frag 12 := fun h => by
  have := @h Nat T3 TM _ _ (DFrac.own Qp.quarter) (sg .a) 0 .b (DFrac.own Qp.quarter) .b .bad
    (fun n mv f hm _ e => by
      rw [sg_get] at hm; cases hm
      rcases f with _ | ⟨d, z⟩
      · cases (e : T3.a = T3.b)
      · cases (e : T3.a = T3.bad)) 0 none t3_hv
  obtain ⟨v, dq, -, hm, hv, -⟩ := HeapView.auth_op_frag_validN_iff_frame.mp this
  rw [ins_get] at hm; cases hm
  exact hv.2 rfl

-- `HeapView.update_auth_op_frag` (hypothesis 13): necessary, V=Unit, dq' = own 2: target fragment invalid
theorem w2c3_38 : ¬ drop0% HeapView.update_auth_op_frag 13 := fun h =>
  dq2 (hv_frag (@h Nat Unit TM _ _ (DFrac.own 1) (sg ()) 0 () (DFrac.own (1 + 1)) () () _ 0 none (un_v 0))).1

-- `HeapView.update_of_local_update` (hypothesis 12): necessary, V=T3: local update (a,b) ~l~> (bad,b) holds vacuously; source valid via order, target value bad invalid
theorem w2c3_39 : ¬ drop0% HeapView.update_of_local_update 12 := fun h => by
  have := @h Nat T3 TM _ _ (DFrac.own Qp.quarter) (sg .a) 0 .a .b .bad .b (sg_get _) (t3_lu _ _) 0 none t3_hv
  obtain ⟨v, dq, -, hm, hv, -⟩ := HeapView.auth_op_frag_validN_iff_frame.mp this
  rw [ins_get] at hm; cases hm
  exact hv.2 rfl

-- `HeapView.update_of_local_update` (hypothesis 13): necessary, V=Qp, m1{0:1}, mv = mv' = 1+1 (identity local update), v = v' = 1/4: source valid, target map value 1+1 invalid
theorem w2c3_40 : ¬ drop0% HeapView.update_of_local_update 13 := fun h => by
  have := @h Nat Qp TM _ _ (DFrac.own Qp.quarter) (sg 1) 0 (1 + 1) Qp.quarter (1 + 1) Qp.quarter _ (LocalUpdate.id _) 0 none
    (HeapView.auth_op_frag_validN_iff_frame.mpr ⟨1, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, Qp.valid_one⟩,
      none, .inr ⟨dq_inc 0, ⟨Qp.threeQuarters, q_sum.symm⟩⟩⟩)
  obtain ⟨v, dq, -, hm, hv, -⟩ := HeapView.auth_op_frag_validN_iff_frame.mp this
  rw [ins_get] at hm; cases hm
  exact q2 hv.2

-- `HeapView.update_of_local_update` (hypothesis 14): necessary, V=Qp, m1{0:1}, mv = v = 1, mv' = 1+1: target map value invalid
theorem w2c3_41 : ¬ drop0% HeapView.update_of_local_update 14 := fun h => by
  have := @h Nat Qp TM _ _ (DFrac.own 1) (sg 1) 0 1 1 (1 + 1) 1 _ (sg_get _) 0 none (qp_v 0)
  obtain ⟨v, dq, -, hm, hv, -⟩ := HeapView.auth_op_frag_validN_iff_frame.mp this
  rw [ins_get] at hm; cases hm
  exact q2 hv.2

-- `HeapView.update_replace` (hypothesis 9): necessary, V=Qp, v2 = 1+1: target fragment invalid
theorem w2c3_42 : ¬ drop0% HeapView.update_replace 9 := fun h =>
  q2 (hv_frag (@h Nat Qp TM _ _ (sg 1) 0 1 (1 + 1) 0 none (qp_v 0))).2

-- `HeapView.update_of_dfrac_update` (hypothesis 9): necessary, P = False: no allocation possible from a valid fragment
theorem w2c3_43 : ¬ drop0% HeapView.update_of_dfrac_update 9 := fun h => by
  obtain ⟨y, ⟨dq', -, hf⟩, -⟩ := @h Nat Unit TM _ _ (DFrac.own 1) 0 () (fun _ => False) 0 none
    (valid_iff_validN.mp (HeapView.frag_valid_iff.mpr ⟨DFrac.valid_own_one, trivial⟩) 0)
  exact hf

-- `HeapView.heapR_map_eq` (hypothesis 18): necessary, T = constOF Unit, m empty, mv = {0:(own 1,())}: mapped fragment has key 0, mapped model does not
theorem w2c3_44 : ¬ drop0% HeapView.heapR_map_eq 18 := fun h => by
  have := @h Nat TM _ Unit Unit Unit Unit (constOF Unit) _ _ _ _ _ OFE.Hom.id OFE.Hom.id 0 ∅ (sg (DFrac.own 1, ()))
  obtain ⟨v, dq, hm, -⟩ := this 0 (DFrac.own 1, ()) (by
    simp [_root_.PartialMap.mapC, _root_.PartialMap.get?_map, sg_get]; rfl)
  simp [_root_.PartialMap.mapO, _root_.PartialMap.get?_map, emp_get] at hm

-- `HeapView.instRFunctorAffine` (hypothesis 5): necessary, T = constOF T3 (not IncOrd): Frag 0 (1/4) a is included in Frag 0 (1/2) bad but not ordered below it
theorem w2c3_45 : ¬ drop0% HeapView.instRFunctorAffine 5 := fun h => by
  have hi := (@h Nat TM _ (constOF T3) _).affine (α := Unit) (β := Unit)
  have hle := hi.inc_ord (x := (HeapView.Frag 0 (DFrac.own Qp.quarter) T3.a : HeapView Nat T3 TM))
    ⟨HeapView.Frag 0 (DFrac.own Qp.quarter) T3.a, rfl⟩
  have h0 := hle.2 0
  rw [← HeapView.frag_op_eqv] at h0
  have h1 : (some (DFrac.own Qp.quarter, T3.a) : Option (DFrac × T3)) ≼ₒ some (DFrac.own Qp.quarter • DFrac.own Qp.quarter, T3.bad) := by
    have e1 := fr_get (DFrac.own Qp.quarter) T3.a
    have e2 := fr_get (DFrac.own Qp.quarter • DFrac.own Qp.quarter) (T3.a • T3.a)
    simp only [HeapView.Frag] at h0
    rw [e1, e2] at h0
    exact h0
  rcases h1 with h1 | h1
  · cases congrArg Prod.snd h1
  · rcases h1.2 with ⟨h3, -⟩ | ⟨h3, -⟩ <;> cases h3

-- `update_big_replace` (hypothesis 9): necessary, V=Unit, m = {0:()}, m0 empty, m1 = {0:()}, frame Frag 0 (own 1) (): target has own 2
theorem w2c3_46 : ¬ drop0% update_big_replace 9 := fun h => by
  have := @h Nat Unit TM _ _ _ (sg ()) ∅ (sg ()) (fun _ _ _ => trivial) 0 (some (HeapView.Frag 0 (DFrac.own 1) ()))
    (by show ✓{0} (Iris.Op.op (Iris.Op.op (AU Unit (sg ())) (BF Unit (DFrac.own 1) ∅)) (HeapView.Frag 0 (DFrac.own 1) ()))
        rw [bemp', unit_right_id]; exact un_v 0)
  have h2 : ✓{0} (Iris.Op.op (Iris.Op.op (AU Unit (sg () ∪ sg ())) (BF Unit (DFrac.own 1) (sg ()))) (HeapView.Frag 0 (DFrac.own 1) ())) := this
  rw [bsg', ← assoc, ← HeapView.frag_op_eqv] at h2
  exact dq2 (hv_frag h2).1

-- `update_big_replace` (hypothesis 10): necessary, V=Qp, m = m0 = {0:1}, m1 = {0:1+1} (same domain): target fragment invalid
theorem w2c3_47 : ¬ drop0% update_big_replace 10 := fun h => by
  have hd : Iris.Std.PartialMap.dom (sg (1 : Qp)) = Iris.Std.PartialMap.dom (sg qtwo) := funext fun k => by
    simp [Iris.Std.PartialMap.dom, Iris.Std.LawfulPartialMap.get?_insert]; split <;> rfl
  have := @h Nat Qp TM _ _ _ (sg 1) (sg 1) (sg qtwo) hd 0 none
    (by show ✓{0} (Iris.Op.op (AU Qp (sg 1)) (BF Qp (DFrac.own 1) (sg 1)))
        rw [bsg']; exact qp_v 0)
  rw [bsg] at this
  exact q2 (hv_frag this).2

-- `update_big_alloc` (hypothesis 9): necessary, V=Unit, m1 = m2 = {0:()}, frame Frag 0 (own 1) (): target has own 2
theorem w2c3_48 : ¬ drop0% update_big_alloc 9 := fun h => by
  have := @h Nat Unit TM _ _ _ (sg ()) (sg ()) (DFrac.own 1) DFrac.valid_own_one (fun _ _ _ => trivial) 0
    (some (HeapView.Frag 0 (DFrac.own 1) ())) (un_v 0)
  have h2 : ✓{0} (Iris.Op.op (Iris.Op.op (AU Unit (sg () ∪ sg ())) (BF Unit (DFrac.own 1) (sg ()))) (HeapView.Frag 0 (DFrac.own 1) ())) := this
  rw [bsg', ← assoc, ← HeapView.frag_op_eqv] at h2
  exact dq2 (hv_frag h2).1

-- `update_big_alloc` (hypothesis 10): necessary, V=Unit, m1 empty, m2 = {0:()}, dq = own 2: target fragment invalid
theorem w2c3_49 : ¬ drop0% update_big_alloc 10 := fun h => by
  have := @h Nat Unit TM _ _ _ ∅ (sg ()) (DFrac.own (1 + 1)) (disj_sg_emp ()) (fun _ _ _ => trivial) 0 none
    (HeapView.auth_validN_iff.mpr DFrac.valid_own_one)
  have h2 : ✓{0} (Iris.Op.op (AU Unit (sg () ∪ ∅)) (BF Unit (DFrac.own (1 + 1)) (sg ()))) := this
  rw [bsg'] at h2
  exact dq2 (hv_frag h2).1

-- `update_big_alloc` (hypothesis 11): necessary, V=Qp, m1 empty, m2 = {0:1+1}: target fragment invalid
theorem w2c3_50 : ¬ drop0% update_big_alloc 11 := fun h => by
  have := @h Nat Qp TM _ _ _ ∅ (sg (1 + 1)) (DFrac.own 1) (disj_sg_emp _) DFrac.valid_own_one 0 none
    (HeapView.auth_validN_iff.mpr DFrac.valid_own_one)
  have h2 : ✓{0} (Iris.Op.op (AU Qp (sg (1 + 1) ∪ ∅)) (BF Qp (DFrac.own 1) (sg (1 + 1)))) := this
  rw [bsg'] at h2
  exact q2 (hv_frag h2).2

-- `Iris.isOp_pair` (hypothesis 9): necessary, alpha=Qp, a = b1 = b2 = 1 (h2 from isOpMerge_op): 1 is not 1+1
theorem w2c3_51 : ¬ drop0% Iris.isOp_pair 9 := fun h =>
  q2ne (congrArg Prod.fst (@h Qp _ .merge 1 1 1 _ 1 1 (isOpMerge_op 1 1)).is_op)

-- `Iris.isOp_pair` (hypothesis 10): necessary, alpha=Qp, a' = b1' = b2' = 1: 1 is not 1+1
theorem w2c3_52 : ¬ drop0% Iris.isOp_pair 10 := fun h =>
  q2ne (congrArg Prod.snd (@h Qp _ .merge _ 1 1 1 1 1 (isOpMerge_op 1 1)).is_op)

-- `Iris.isOp_pair_core_id_l` (hypothesis 9): necessary, alpha=beta=Qp, a = 1 (not core-id): 1 is not 1+1
theorem w2c3_53 : ¬ drop0% Iris.isOp_pair_core_id_l 9 := fun h =>
  q2ne (congrArg Prod.fst (@h Qp Qp _ _ .merge 1 _ 1 1 (isOpMerge_op 1 1)).is_op)

-- `Iris.isOp_pair_core_id_l` (hypothesis 10): necessary, alpha=Unit (core id), beta=Qp, a' = b1' = b2' = 1
theorem w2c3_54 : ¬ drop0% Iris.isOp_pair_core_id_l 10 := fun h =>
  q2ne (congrArg Prod.snd (@h Unit Qp _ _ .merge () 1 1 1 unitCoreId).is_op)

-- `Iris.isOp_pair_core_id_r` (hypothesis 9): necessary, alpha=beta=Qp, a' = 1 (not core-id): 1 is not 1+1
theorem w2c3_55 : ¬ drop0% Iris.isOp_pair_core_id_r 9 := fun h =>
  q2ne (congrArg Prod.snd (@h Qp Qp _ _ .merge _ 1 1 1 (isOpMerge_op 1 1)).is_op)

-- `Iris.isOp_some` (hypothesis 6): necessary, alpha=Qp, a = b1 = b2 = 1
theorem w2c3_56 : ¬ drop0% Iris.isOp_some 6 := fun h =>
  q2ne (Option.some.inj (@h Qp _ 1 1 1 .merge).is_op)

-- `LeibnizMultiSet.localUpdate` (hypothesis 7): necessary, ListPerm Nat: X = Y = Y' = empty, X' = {0}: frame none gives {0} = empty
theorem w2c3_57 : ¬ drop0% LeibnizMultiSet.localUpdate 7 := fun h => by
  have := (@h Nat (Iris.Std.ListPerm Nat) _ ∅ ∅ {0} ∅ 0 none trivial rfl).2
  have h1 : LeibnizMultiSet.ofSet ({0} : Iris.Std.ListPerm Nat) = .ofSet ∅ := this
  have h2 := congrArg (fun | LeibnizMultiSet.ofSet X => Iris.Std.MultiSet.multiplicity 0 X) h1
  simp [Iris.Std.LawfulMultiSet.multiplicity_singleton_eq, Iris.Std.LawfulMultiSet.multiplicity_empty] at h2

-- `LeibnizMultiSet.localUpdate_dealloc` (hypothesis 6): necessary, ListPerm Nat: X = {0}, Y = empty, X' = {0}, frame {0}: multiplicity of 0 is 0 vs 1
theorem w2c3_58 : ¬ drop0% LeibnizMultiSet.localUpdate_dealloc 6 := fun h => by
  open Iris.Std.LawfulMultiSet in
  have hyp : LeibnizMultiSet.ofSet ({0} : Iris.Std.ListPerm Nat) = LeibnizMultiSet.ofSet (∅ : Iris.Std.ListPerm Nat) • LeibnizMultiSet.ofSet ({0} : Iris.Std.ListPerm Nat) :=
    congrArg LeibnizMultiSet.ofSet (Iris.Std.LawfulMultiSet.ext fun a => by
      simp [multiplicity_disjUnion, multiplicity_empty])
  have := (@h Nat (Iris.Std.ListPerm Nat) _ {0} ∅ {0} 0 (some (.ofSet {0})) trivial hyp).2
  have h1 : LeibnizMultiSet.ofSet (({0} : Iris.Std.ListPerm Nat) \ {0}) = .ofSet ((∅ \ {0}) ⊎ {0}) := this
  have h2 := congrArg (fun | LeibnizMultiSet.ofSet X => Iris.Std.MultiSet.multiplicity 0 X) h1
  open Iris.Std.LawfulMultiSet in
  simp [multiplicity_disjUnion, multiplicity_difference, multiplicity_singleton_eq, multiplicity_empty] at h2

-- `DisjointLeibnizSet.exist_set_of_mem` (hypothesis 5): necessary, x = error
theorem w2c3_59 : ¬ drop0% DisjointLeibnizSet.exist_set_of_mem 5 := fun h => by
  obtain ⟨x', hx⟩ := @h TS Nat 0 _ .error
  cases hx

-- `DisjointLeibnizSet.mem_iff_of_valid_union` (hypothesis 6): necessary, ExtTreeSet Nat: x = y = valid {0}: x*y = error contains nothing
theorem w2c3_60 : ¬ drop0% DisjointLeibnizSet.mem_iff_of_valid_union 6 := fun h => by
  have := (@h Nat TS _ _ (.valid {0}) (.valid {0}) 0).mpr (.inl m00)
  rw [e00] at this; exact this

-- `DisjointLeibnizSet.mem_iff_of_validN_union` (hypothesis 7): necessary, ExtTreeSet Nat: x = y = valid {0}: x*y = error contains nothing
theorem w2c3_61 : ¬ drop0% DisjointLeibnizSet.mem_iff_of_validN_union 7 := fun h => by
  have := (@h Nat TS _ _ 0 (.valid {0}) (.valid {0}) 0).mpr (.inl m00)
  rw [e00] at this; exact this

-- `DisjointLeibnizSet.disj_op_union` (hypothesis 6): necessary, X = Y = {0}: valid X * valid Y = error
theorem w2c3_62 : ¬ drop0% DisjointLeibnizSet.disj_op_union 6 := fun h => by
  have := @h Nat TS _ _ {0} {0}
  rw [e00] at this; cases this

-- `DisjointLeibnizSet.valid_inv_l` (hypothesis 6): necessary, Y = error
theorem w2c3_63 : ¬ drop0% DisjointLeibnizSet.valid_inv_l 6 := fun h => by
  obtain ⟨Y', hY, -⟩ := @h Nat TS _ _ {0} .error
  cases hY

-- `DisjointLeibnizSet.not_mem_of_mem_and_valid_op_left` (hypothesis 6): necessary, x = y = valid {0}, p = 0
theorem w2c3_64 : ¬ drop0% DisjointLeibnizSet.not_mem_of_mem_and_valid_op_left 6 := fun h =>
  @h Nat TS _ _ (.valid {0}) (.valid {0}) 0 m00 m00

-- `DisjointLeibnizSet.not_mem_of_mem_and_valid_op_left` (hypothesis 8): necessary, x = valid empty, y = valid {0}, p = 0
theorem w2c3_65 : ¬ drop0% DisjointLeibnizSet.not_mem_of_mem_and_valid_op_left 8 := fun h =>
  @h Nat TS _ _ (.valid ∅) (.valid {0}) (by rw [e0x]; exact DisjointLeibnizSet.valid_set) 0 m00

-- `DisjointLeibnizSet.not_mem_of_mem_and_valid_op_right` (hypothesis 6): necessary, x = y = valid {0}, p = 0
theorem w2c3_66 : ¬ drop0% DisjointLeibnizSet.not_mem_of_mem_and_valid_op_right 6 := fun h =>
  @h Nat TS _ _ (.valid {0}) (.valid {0}) 0 m00 m00

-- `DisjointLeibnizSet.not_mem_of_mem_and_valid_op_right` (hypothesis 8): necessary, x = valid {0}, y = valid empty, p = 0
theorem w2c3_67 : ¬ drop0% DisjointLeibnizSet.not_mem_of_mem_and_valid_op_right 8 := fun h =>
  @h Nat TS _ _ (.valid {0}) (.valid ∅) (by rw [comm, e0x]; exact DisjointLeibnizSet.valid_set) 0 m00

-- `DisjointLeibnizSet.localUpdate_union_r_of_disj` (hypothesis 7): necessary, X = Z = {0}, Y = empty, frame valid {0}: target valid {0} vs error
theorem w2c3_68 : ¬ drop0% DisjointLeibnizSet.localUpdate_union_r_of_disj 7 := fun h => by
  have := (@h Nat TS _ _ {0} ∅ {0} 0 (some (.valid {0})) DisjointLeibnizSet.validN_set e0x.symm).2
  have h2 : DisjointLeibnizSet.valid (({0} : TS) ∪ {0}) = DisjointLeibnizSet.valid (({0} : TS) ∪ ∅) • DisjointLeibnizSet.valid {0} := this
  rw [Iris.Std.LawfulSet.union_empty_right, e00] at h2
  cases h2

-- `DisjointLeibnizSet.localUpdate_alloc_empty_of_disj` (hypothesis 6): necessary, X = Z = {0}, frame valid {0}: target valid {0} vs error
theorem w2c3_69 : ¬ drop0% DisjointLeibnizSet.localUpdate_alloc_empty_of_disj 6 := fun h => by
  have := (@h Nat TS _ _ {0} {0} 0 (some (.valid {0})) DisjointLeibnizSet.validN_set e0x.symm).2
  have h2 : DisjointLeibnizSet.valid (({0} : TS) ∪ {0}) = DisjointLeibnizSet.valid ({0} : TS) • DisjointLeibnizSet.valid {0} := this
  rw [e00] at h2
  cases h2

-- `DisjointLeibnizSet.alloc_updateP_strong` (hypothesis 7): necessary, P = Q = False, X empty
theorem w2c3_70 : ¬ drop0% DisjointLeibnizSet.alloc_updateP_strong 7 := fun h => by
  obtain ⟨y, hy, -⟩ := @h Nat TS _ _ (fun _ => False) (fun _ => False) ∅ (fun _ hp => hp) 0 none DisjointLeibnizSet.validN_set
  exact hy

-- `DisjointLeibnizSet.alloc_updateP_strong` (hypothesis 8): necessary, P = True, Q = False, X empty (fresh elements exist in finite sets)
theorem w2c3_71 : ¬ drop0% DisjointLeibnizSet.alloc_updateP_strong 8 := fun h => by
  obtain ⟨y, hy, -⟩ := @h Nat TS _ _ (fun _ => True) (fun _ => False) ∅
    (fun Y _ => let ⟨j, hj⟩ := Iris.Std.FiniteSet.fresh Y; ⟨j, hj, trivial⟩) 0 none DisjointLeibnizSet.validN_set
  exact hy

-- `DisjointLeibnizSet.alloc_updateP_strong'` (hypothesis 6): necessary, P = False
theorem w2c3_72 : ¬ drop0% DisjointLeibnizSet.alloc_updateP_strong' 6 := fun h => by
  obtain ⟨y, ⟨i, -, -, hp⟩, -⟩ := @h Nat TS _ _ (fun _ => False) ∅ 0 none DisjointLeibnizSet.validN_set
  exact hp

-- `DisjointLeibnizSet.alloc_empty_updateP_strong` (hypothesis 6): necessary, P = Q = False
theorem w2c3_73 : ¬ drop0% DisjointLeibnizSet.alloc_empty_updateP_strong 6 := fun h => by
  obtain ⟨y, hy, -⟩ := @h Nat TS _ _ (fun _ => False) (fun _ => False) (fun hp => hp) 0 none DisjointLeibnizSet.validN_set
  exact hy

-- `DisjointLeibnizSet.alloc_empty_updateP_strong` (hypothesis 7): necessary, P = True, Q = False (fresh elements exist)
theorem w2c3_74 : ¬ drop0% DisjointLeibnizSet.alloc_empty_updateP_strong 7 := fun h => by
  obtain ⟨y, hy, -⟩ := @h Nat TS _ _ (fun _ => True) (fun _ => False)
    (fun Y => let ⟨j, hj⟩ := Iris.Std.FiniteSet.fresh Y; ⟨j, hj, trivial⟩) 0 none DisjointLeibnizSet.validN_set
  exact hy

-- `DisjointLeibnizSet.alloc_empty_updateP_strong'` (hypothesis 5): necessary, P = False
theorem w2c3_75 : ¬ drop0% DisjointLeibnizSet.alloc_empty_updateP_strong' 5 := fun h => by
  obtain ⟨y, ⟨i, -, hp⟩, -⟩ := @h Nat TS _ _ (fun _ => False) 0 none DisjointLeibnizSet.validN_set
  exact hp

-- `DisjointLeibnizSet.alloc_empty_updateP` (hypothesis 6): necessary, Q = False
theorem w2c3_76 : ¬ drop0% DisjointLeibnizSet.alloc_empty_updateP 6 := fun h => by
  obtain ⟨y, hy, -⟩ := @h Nat TS _ _ _ (fun _ => False) 0 none DisjointLeibnizSet.validN_set
  exact hy

-- `LeibnizSet.localUpdate` (hypothesis 6): necessary, X = Y = {0}, X' = empty, frame valid {0}: target empty = {0}
theorem w2c3_77 : ¬ drop0% LeibnizSet.localUpdate 6 := fun h => by
  have hyp : (LeibnizSet.valid ({0} : TS)) = LeibnizSet.valid ({0} : TS) • LeibnizSet.valid ({0} : TS) := by
    rw [LeibnizSet.op_union, Iris.Std.LawfulSet.union_idem]
  have := (@h Nat TS _ {0} {0} ∅ 0 (some (.valid {0})) trivial hyp).2
  have h2 : LeibnizSet.valid (∅ : TS) = LeibnizSet.valid (∅ : TS) • LeibnizSet.valid ({0} : TS) := this
  rw [LeibnizSet.op_union, Iris.Std.LawfulSet.union_empty_left] at h2
  injection h2 with h3
  exact Iris.Std.LawfulSet.mem_empty (by rw [h3]; exact m00)

-- `Iris.DFracAgree.mk_discrete` (hypothesis 4): necessary, A = TN (truncation OFE): mk d 1 and mk d 2 agree at step 0 but differ
theorem w2c3_78 : ¬ drop0% Iris.DFracAgree.mk_discrete 4 := fun h =>
  tn12ne (DFracAgree.mk_inj ((@h TN _ (DFrac.own 1) ⟨1⟩).discrete (DFracAgree.mk_ne.ne tn12))).2

-- `Iris.DFracAgree.update₂` (hypothesis 7): necessary, A = TN, d1 = d2 = discard, a1 = a2 = 0, a' = 5, frame mk discard 0: 5 and 0 disagree at step 0
theorem w2c3_79 : ¬ drop0% Iris.DFracAgree.update₂ 7 := fun h => by
  have e : ∀ a : TN, DFracAgree.mk .discard a • DFracAgree.mk .discard a = DFracAgree.mk .discard a :=
    fun a => (DFracAgree.mk_op (d₁ := .discard) (d₂ := .discard)).symm
  have := @h TN _ .discard .discard ⟨0⟩ ⟨0⟩ ⟨5⟩ 0 (some (DFracAgree.mk .discard ⟨0⟩))
  have h2 : ✓{0} ((DFracAgree.mk .discard (⟨0⟩ : TN) • DFracAgree.mk .discard (⟨0⟩ : TN)) • DFracAgree.mk .discard (⟨0⟩ : TN)) →
      ✓{0} ((DFracAgree.mk .discard (⟨5⟩ : TN) • DFracAgree.mk .discard (⟨5⟩ : TN)) • DFracAgree.mk .discard (⟨0⟩ : TN)) := this
  rw [e ⟨0⟩, e ⟨5⟩] at h2
  have := (DFracAgree.op_validN.mp (h2 (DFracAgree.op_validN.mpr ⟨DFrac.valid_discard, rfl⟩))).2
  exact (by decide : ¬ (min 5 (0+1) = min 0 (0+1))) this

-- `Iris.DFracAgree.Frac.update₂` (hypothesis 7): necessary, A = TN, q1 = q2 = 1/4, a = 0, a' = 5, frame mk 1/4 0
theorem w2c3_80 : ¬ drop0% Iris.DFracAgree.Frac.update₂ 7 := fun h => by
  have := @h TN _ Qp.quarter Qp.quarter ⟨0⟩ ⟨0⟩ ⟨5⟩ 0 (some (DFracAgree.Frac.mk Qp.quarter ⟨0⟩))
  have h2 : ✓{0} ((DFracAgree.Frac.mk Qp.quarter (⟨0⟩ : TN) • DFracAgree.Frac.mk Qp.quarter (⟨0⟩ : TN)) • DFracAgree.Frac.mk Qp.quarter (⟨0⟩ : TN)) →
      ✓{0} ((DFracAgree.Frac.mk Qp.quarter (⟨5⟩ : TN) • DFracAgree.Frac.mk Qp.quarter (⟨5⟩ : TN)) • DFracAgree.Frac.mk Qp.quarter (⟨0⟩ : TN)) := this
  have e : ∀ a : TN, DFracAgree.Frac.mk Qp.quarter a • DFracAgree.Frac.mk Qp.quarter a =
      DFracAgree.Frac.mk (Qp.quarter + Qp.quarter) a := fun a => DFracAgree.Frac.mk_op.symm
  rw [e ⟨0⟩, e ⟨5⟩] at h2
  have := (DFracAgree.Frac.op_validN.mp (h2 (DFracAgree.Frac.op_validN.mpr ⟨by show ((Qp.quarter + Qp.quarter) + Qp.quarter).val ≤ 1; simp; grind, rfl⟩))).2
  exact (by decide : ¬ (min 5 (0+1) = min 0 (0+1))) this

-- `Iris.ExclAuth.auth_discrete` (hypothesis 3): necessary, A = TN: auth 1 and auth 2 agree at step 0 but differ
theorem w2c3_81 : ¬ drop0% Iris.ExclAuth.auth_discrete 3 := fun h => by
  have := (Auth.auth_inj ((@h TN _ ⟨1⟩).discrete (ExclAuth.auth_ne.ne tn12))).2
  exact tn12ne (Excl.excl.inj (Option.some.inj this))

-- `Iris.ExclAuth.frag_discrete` (hypothesis 3): necessary, A = TN: frag 1 and frag 2 agree at step 0 but differ
theorem w2c3_82 : ¬ drop0% Iris.ExclAuth.frag_discrete 3 := fun h => by
  have := (Auth.frag_inj ((@h TN _ ⟨1⟩).discrete (ExclAuth.frag_ne.ne tn12)))
  exact tn12ne (Excl.excl.inj (Option.some.inj this))

-- `FracAuth.auth_discrete` (hypothesis 4): necessary, A = Excl TN: auth (excl 1) and auth (excl 2) agree at step 0 but differ
theorem w2c3_83 : ¬ drop0% FracAuth.auth_discrete 4 := fun h => by
  have := (Auth.auth_inj ((@h (Excl TN) _ (DFrac.own 1) (.excl ⟨1⟩)).discrete
    (FracAuth.auth_ne.ne (x₂ := .excl ⟨2⟩) tn12))).2
  exact tn12ne (Excl.excl.inj (Prod.mk.inj (Option.some.inj this)).2)

-- `FracAuth.frag_discrete` (hypothesis 4): necessary, A = Excl TN: frag (excl 1) and frag (excl 2) agree at step 0 but differ
theorem w2c3_84 : ¬ drop0% FracAuth.frag_discrete 4 := fun h => by
  have := (Auth.frag_inj ((@h (Excl TN) _ 1 (.excl ⟨1⟩)).discrete
    (FracAuth.frag_ne.ne (x₂ := .excl ⟨2⟩) tn12)))
  exact tn12ne (Excl.excl.inj (Prod.mk.inj (Option.some.inj this)).2)

-- `FracAuth.dfrac_validN` (hypothesis 6): necessary, A = UZ (never valid)
theorem w2c3_85 : ¬ drop0% FracAuth.dfrac_validN 6 := fun h => by
  have := Auth.both_dfrac_validN_frame.mp (@h UZ _ (DFrac.own 1) 0 ⟨⟩ DFrac.valid_own_one)
  exact this.2.2.2

-- `FracAuth.validN` (hypothesis 4): necessary, A = UZ (never valid)
theorem w2c3_86 : ¬ drop0% FracAuth.validN 4 := fun h =>
  (Auth.both_dfrac_validN_frame.mp (@h UZ _ 0 ⟨⟩)).2.2.2

-- `FracAuth.dfrac_valid` (hypothesis 5): necessary, A = UZ (never valid)
theorem w2c3_87 : ¬ drop0% FracAuth.dfrac_valid 5 := fun h =>
  (valid_iff_validN.mp (Auth.both_dfrac_valid_frame.mp (@h UZ _ (DFrac.own 1) ⟨⟩ DFrac.valid_own_one)).2.2 0).2

-- `FracAuth.valid` (hypothesis 3): necessary, A = UZ (never valid)
theorem w2c3_88 : ¬ drop0% FracAuth.valid 3 := fun h => by
  have := Auth.both_dfrac_valid_frame.mp (@h UZ _ ⟨⟩)
  exact (valid_iff_validN.mp this.2.2 0).2

-- `FracAuth.ordN` (hypothesis 2): necessary, A = BX (not IncOrd): auth false, frag 1/4 true with frame (3/4,true); true not below false
theorem w2c3_89 : ¬ drop0% FracAuth.ordN 2 := fun h => by
  have := @h BX _ 0 (DFrac.own 1) Qp.quarter ⟨false⟩ ⟨true⟩
    (Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨some (Qp.threeQuarters, ⟨true⟩), .inl ⟨q_sum, rfl⟩⟩, ⟨Qp.valid_one, trivial⟩⟩)
  rcases this with h | h
  · cases h
  · exact h

-- `FracAuth.includedN` (hypothesis 2): necessary, A = BT (not OrdInc): auth false, frag 1/4 true below via order; true not included in false
theorem w2c3_90 : ¬ drop0% FracAuth.includedN 2 := fun h => by
  have := @h BT _ 0 (DFrac.own 1) Qp.quarter ⟨false⟩ ⟨true⟩
    (Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨none, .inr ⟨⟨Qp.threeQuarters, q_sum.symm⟩, trivial⟩⟩, ⟨Qp.valid_one, trivial⟩⟩)
  obtain ⟨z, hz⟩ := this
  rcases z with _ | ⟨z⟩
  · cases hz
  · cases hz

-- `FracAuth.ord_frame` (hypothesis 3): necessary, A = BK (not ORA.Discrete): valid via the total step-indexed order, no frame in the full order
theorem w2c3_91 : ¬ drop0% FracAuth.ord_frame 3 := fun h => by
  obtain ⟨c, hc⟩ := @h BK _ Qp.quarter (DFrac.own 1) ⟨false⟩ ⟨true⟩ bk_fv
  rcases c with _ | w <;> rcases hc with hc | hc
  · cases hc
  · exact Bool.noConfusion (hc : false = true)
  · exact Bool.noConfusion (congrArg BK.b hc : true = false)
  · exact Bool.noConfusion (hc : false = true)

-- `FracAuth.ord` (hypothesis 3): necessary, A = BK (IncOrd, not discrete): true not below false in the full order
theorem w2c3_92 : ¬ drop0% FracAuth.ord 3 := fun h => by
  rcases @h BK _ Qp.quarter _ (DFrac.own 1) ⟨false⟩ ⟨true⟩ bk_fv with hc | hc
  · cases hc
  · exact Bool.noConfusion (hc : false = true)

-- `FracAuth.ord` (hypothesis 4): necessary, A = BX (discrete, not IncOrd)
theorem w2c3_93 : ¬ drop0% FracAuth.ord 4 := fun h => by
  rcases @h BX _ Qp.quarter _ (DFrac.own 1) ⟨false⟩ ⟨true⟩ bxv with h | h
  · cases h
  · exact h

-- `FracAuth.included` (hypothesis 4): necessary, A = BT (discrete, not OrdInc)
theorem w2c3_95 : ¬ drop0% FracAuth.included 4 := fun h => by
  obtain ⟨z, hz⟩ := @h BT _ Qp.quarter _ (DFrac.own 1) ⟨false⟩ ⟨true⟩ (valid_iff_validN.mpr btv)
  rcases z with _ | ⟨z⟩ <;> cases hz

-- `FracAuth.ordN_total` (hypothesis 4): necessary, A = Qp (IncOrd, not OrderRefl): 1 not below 1
theorem w2c3_96 : ¬ drop0% FracAuth.ordN_total 4 := fun h =>
  qne (@h Qp _ 0 1 _ (DFrac.own 1) 1 1 (qv 0))

-- `FracAuth.ordN_total` (hypothesis 5): necessary, A = BE (OrderRefl, not IncOrd)
theorem w2c3_97 : ¬ drop0% FracAuth.ordN_total 5 := fun h => by
  have := @h BE _ 0 Qp.quarter _ (DFrac.own 1) ⟨false⟩ ⟨true⟩ (bev 0)
  cases this

-- `FracAuth.ordN_total` (hypothesis 9): necessary, A = Option Qp: some 1 not below none
theorem w2c3_98 : ¬ drop0% FracAuth.ordN_total 9 := fun h =>
  @h (Option Qp) _ 0 1 _ _ (DFrac.own 1) none (some 1)

-- `FracAuth.includedN_total` (hypothesis 4): necessary, A = Qp (OrdInc, not OrderRefl)
theorem w2c3_99 : ¬ drop0% FracAuth.includedN_total 4 := fun h =>
  qne (@h Qp _ 0 1 _ (DFrac.own 1) 1 1 (qv 0))

-- `FracAuth.includedN_total` (hypothesis 5): necessary, A = BT (OrderRefl, not OrdInc)
theorem w2c3_100 : ¬ drop0% FracAuth.includedN_total 5 := fun h => by
  obtain ⟨z, hz⟩ := @h BT _ 0 Qp.quarter _ (DFrac.own 1) ⟨false⟩ ⟨true⟩ (btv 0)
  cases hz

-- `FracAuth.includedN_total` (hypothesis 9): necessary, A = Option Qp: some 1 not included in none
theorem w2c3_101 : ¬ drop0% FracAuth.includedN_total 9 := fun h => by
  obtain ⟨z, hz⟩ := @h (Option Qp) _ 0 1 _ _ (DFrac.own 1) none (some 1)
  rcases z with _ | _ <;> cases hz

-- `FracAuth.ord_total` (hypothesis 3): necessary, A = BK (OrderRefl, IncOrd, not discrete)
theorem w2c3_102 : ¬ drop0% FracAuth.ord_total 3 := fun h =>
  Bool.noConfusion (@h BK _ Qp.quarter _ _ (DFrac.own 1) ⟨false⟩ ⟨true⟩ bk_fv : false = true)

-- `FracAuth.ord_total` (hypothesis 4): necessary, A = Qp (discrete, IncOrd, not OrderRefl)
theorem w2c3_103 : ¬ drop0% FracAuth.ord_total 4 := fun h =>
  qne' (@h Qp _ 1 _ _ (DFrac.own 1) 1 1 qv')

-- `FracAuth.ord_total` (hypothesis 5): necessary, A = BE (discrete, OrderRefl, not IncOrd)
theorem w2c3_104 : ¬ drop0% FracAuth.ord_total 5 := fun h => by
  have := @h BE _ Qp.quarter _ _ (DFrac.own 1) ⟨false⟩ ⟨true⟩ (valid_iff_validN.mpr bev)
  cases this

-- `FracAuth.ord_total` (hypothesis 9): necessary, A = Option Qp: some 1 not below none
theorem w2c3_105 : ¬ drop0% FracAuth.ord_total 9 := fun h =>
  @h (Option Qp) _ 1 _ _ _ (DFrac.own 1) none (some 1)

-- `FracAuth.included_total` (hypothesis 4): necessary, A = Qp (discrete, OrdInc, not OrderRefl)
theorem w2c3_107 : ¬ drop0% FracAuth.included_total 4 := fun h =>
  qne' (@h Qp _ 1 _ _ (DFrac.own 1) 1 1 qv')

-- `FracAuth.included_total` (hypothesis 5): necessary, A = BT (discrete, OrderRefl, not OrdInc)
theorem w2c3_108 : ¬ drop0% FracAuth.included_total 5 := fun h => by
  obtain ⟨z, hz⟩ := @h BT _ Qp.quarter _ _ (DFrac.own 1) ⟨false⟩ ⟨true⟩ (valid_iff_validN.mpr btv)
  cases hz

-- `FracAuth.included_total` (hypothesis 9): necessary, A = Option Qp: some 1 not included in none
theorem w2c3_109 : ¬ drop0% FracAuth.included_total 9 := fun h => by
  obtain ⟨z, hz⟩ := @h (Option Qp) _ 1 _ _ _ (DFrac.own 1) none (some 1)
  rcases z with _ | _ <;> cases hz

-- `FracAuth.auth_op_validN` (hypothesis 5): necessary, A = Unit: conclusion False
theorem w2c3_110 : ¬ drop0% FracAuth.auth_op_validN 5 := fun h => @h Unit _ 0 () ()

-- `FracAuth.auth_op_valid` (hypothesis 4): necessary, A = Unit: conclusion False
theorem w2c3_111 : ¬ drop0% FracAuth.auth_op_valid 4 := fun h => @h Unit _ () ()

-- `FracAuth.isOp_frac_auth` (hypothesis 9): necessary, A = Unit, q = q1 = q2 = 1: 1 is not 1+1
theorem w2c3_112 : ¬ drop0% FracAuth.isOp_frac_auth 9 := fun h => by
  have := (@h Unit _ .merge 1 1 1 () () _ (isOpMerge_op () ())).is_op
  have := Auth.frag_inj this
  have h3 : some ((1:Qp), ()) = some ((1:Qp) + 1, ()) := this
  exact q2ne (Prod.mk.inj (Option.some.inj h3)).1

-- `FracAuth.isOp_frac_auth` (hypothesis 10): necessary, A = Qp, q = 1+1 via isOpMerge_op, a = a1 = a2 = 1: 1 is not 1+1
theorem w2c3_113 : ¬ drop0% FracAuth.isOp_frac_auth 10 := fun h => by
  have := (@h Qp _ .merge (1 + 1) 1 1 1 1 1 (isOpMerge_op (1 : Qp) 1)).is_op
  have := Auth.frag_inj this
  have h3 : some ((1:Qp) + 1, (1:Qp)) = some ((1:Qp) + 1, (1:Qp) + 1) := this
  exact q2ne (Prod.mk.inj (Option.some.inj h3)).2

-- `FracAuth.isOp_frac_auth_core_id` (hypothesis 7): necessary, A = Qp, a = 1 (not core-id): 1 is not 1+1
theorem w2c3_114 : ¬ drop0% FracAuth.isOp_frac_auth_core_id 7 := fun h => by
  have := (@h Qp _ .merge (1 + 1) 1 1 1 (isOpMerge_op (1 : Qp) 1)).is_op
  have := Auth.frag_inj this
  have h3 : some ((1:Qp) + 1, (1:Qp)) = some ((1:Qp) + 1, (1:Qp) + 1) := this
  exact q2ne (Prod.mk.inj (Option.some.inj h3)).2

-- `FracAuth.isOp_frac_auth_core_id` (hypothesis 8): necessary, A = Unit, q = q1 = q2 = 1
theorem w2c3_115 : ¬ drop0% FracAuth.isOp_frac_auth_core_id 8 := fun h => by
  have := (@h Unit _ .merge 1 1 1 () unitCoreId).is_op
  have := Auth.frag_inj this
  have h3 : some ((1:Qp), ()) = some ((1:Qp) + 1, ()) := this
  exact q2ne (Prod.mk.inj (Option.some.inj h3)).1

-- `FracAuth.update` (hypothesis 2): necessary, A = T3 (not OrdInc): local update (a,b) ~l~> (bad,b) holds vacuously, source valid via order, target invalid
theorem w2c3_116 : ¬ drop0% FracAuth.update 2 := fun h => by
  have := Auth.both_dfrac_validN_frame.mp (@h T3 _ Qp.quarter .a .b .bad .b (t3_lu _ _) 0 none t3_fv)
  exact this.2.2.2 rfl

-- `FracAuth.update` (hypothesis 8): necessary, A = Qp, a = b = b' = 1, a' = 1+1: target invalid
theorem w2c3_117 : ¬ drop0% FracAuth.update 8 := fun h => by
  have := Auth.both_dfrac_validN_frame.mp (@h Qp _ _ 1 1 1 (1 + 1) 1 0 none (qv 0))
  exact q2 this.2.2.2

-- `FracAuth.update_full` (hypothesis 5): necessary, A = Qp, a = b = 1, a' = 1+1: target invalid
theorem w2c3_118 : ¬ drop0% FracAuth.update_full 5 := fun h => by
  have := Auth.both_dfrac_validN_frame.mp (@h Qp _ 1 1 (1 + 1) 0 none (qv 0))
  exact q2 this.2.2.2

-- `Iris.instDiscrete` (hypothesis 2): necessary, alpha = TN: lb [1] and lb [2] agree at step 0 but differ
theorem w2c3_119 : ¬ drop0% Iris.instDiscrete 2 := fun h => by
  have e := (@h TN _).discrete_0 (x := ◯ML [⟨1⟩]) (y := ◯ML [⟨2⟩]) (MonoList.lb_ne.ne (.cons tn12 .nil))
  have := MonoList.lb_inj e
  simp at this

-- `Iris.MonoList.lb_op_left` (hypothesis 4): necessary, alpha = Unit, l1 = [()], l2 = []: would make lb [()] = lb []
theorem w2c3_120 : ¬ drop0% Iris.MonoList.lb_op_left 4 := fun h =>
  absurd (MonoList.lb_inj ((MonoList.lb_op_right (List.nil_prefix)).symm.trans (@h Unit _ [()] []))) (by simp)

-- `Iris.MonoList.lb_op_right` (hypothesis 4): necessary, alpha = Unit, l1 = [()], l2 = []
theorem w2c3_121 : ¬ drop0% Iris.MonoList.lb_op_right 4 := fun h =>
  absurd (MonoList.lb_inj ((MonoList.lb_op_left (List.nil_prefix)).symm.trans (@h Unit _ [()] []))) (by simp)

-- `Iris.MonoList.instIsOpAuthOfDFrac` (hypothesis 7): necessary, alpha = Unit, dq = dq1 = dq2 = own 1: auth * auth invalid
theorem w2c3_122 : ¬ drop0% Iris.MonoList.instIsOpAuthOfDFrac 7 := fun h => by
  have := (@h Unit _ .merge (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) []).is_op
  exact (MonoList.auth_op_valid [] []).mp (this ▸ MonoList.auth_valid [])

-- `Iris.MonoList.lb_mono_ord` (hypothesis 4): necessary, alpha = Unit, l1 = [()], l2 = []: auth [] * lb [()] would be valid
theorem w2c3_123 : ¬ drop0% Iris.MonoList.lb_mono_ord 4 := fun h => ml_not_inc (OrdInc.ord_inc (@h Unit _ [()] []))

-- `Iris.MonoList.lb_mono` (hypothesis 4): necessary, alpha = Unit, l1 = [()], l2 = []
theorem w2c3_124 : ¬ drop0% Iris.MonoList.lb_mono 4 := fun h => ml_not_inc (@h Unit _ [()] [])

-- `Iris.MonoList.update` (hypothesis 4): necessary, alpha = Unit, l1 = [()], l2 = [], frame lb [()]
theorem w2c3_125 : ¬ drop0% Iris.MonoList.update 4 := fun h => by
  have hv : ✓ ((●ML [()]) • ◯ML [()]) := (MonoList.both_valid _ _).mpr (List.prefix_refl _)
  have : ✓ ((●ML ([] : List Unit)) • ◯ML [()]) :=
    valid_iff_validN.mpr fun n => @h Unit _ [()] [] n (some _) (valid_iff_validN.mp hv n)
  have := (MonoList.both_valid _ _).mp this
  simp at this

