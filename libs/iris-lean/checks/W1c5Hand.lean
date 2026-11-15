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
namespace W1c5
open Iris Iris.OFE Iris.ORA

/-- Discrete ORA on Bool: op = and, no core, all valid, order = equality (copied from Probe1). -/
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
theorem ba_not_inc : ¬ Increasing (⟨false⟩ : BA) := fun h => by
  have := h.increasing ⟨true⟩
  cases this
theorem ba_op (x y : BA) : x • y = ⟨x.b && y.b⟩ := rfl
theorem ba_true_canc : Cancelable (⟨true⟩ : BA) := ⟨fun {n y z} _ e => by
  have e' : (⟨true && y.b⟩ : BA) = ⟨true && z.b⟩ := e
  cases y; cases z; simp_all⟩
theorem ba_false_not_canc : ¬ Cancelable (⟨false⟩ : BA) := fun h => by
  have := h.cancelableN (n := 0) (y := ⟨true⟩) (z := ⟨false⟩) trivial rfl
  cases this
theorem ba_not_idfree (x : BA) : ¬ IdFree x := fun h =>
  h.id_free0_r x trivial (by cases x with | mk b => cases b <;> rfl)

/-- BA with validity `b = true`: `false` is invalid, so it is vacuously cancelable and id-free. -/
structure BV where b : Bool
instance : OFE BV := OFE.ofDiscrete BV
instance : OFE.Discrete BV := ⟨fun h => h⟩
def bvData : DiscreteORAData BV where
  pcore _ := none
  op x y := ⟨x.b && y.b⟩
  Valid x := x.b = true
  Order := Eq
  assoc x y z := congrArg BV.mk (Bool.and_assoc x.b y.b z.b).symm
  comm x y := congrArg BV.mk (Bool.and_comm x.b y.b)
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left x y h := by cases x with | mk a => cases a <;> simp_all
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ h := h ▸ rfl
  valid_of_ord _ _ h v := h ▸ v
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ hx hxy := hxy ▸ hx
instance bvORA : ORA BV := ORA.ofDiscreteORAData bvData
theorem bv_validN {n} (x : BV) : ✓{n} x ↔ x.b = true := Iff.rfl
theorem bv_op (x y : BV) : x • y = ⟨x.b && y.b⟩ := rfl
instance bv_false_canc : Cancelable (⟨false⟩ : BV) := ⟨fun {n y z} v _ => by
  rw [bv_validN, bv_op] at v; cases v⟩
instance bv_true_canc : Cancelable (⟨true⟩ : BV) := ⟨fun {n y z} _ e => by
  have e' : (⟨true && y.b⟩ : BV) = ⟨true && z.b⟩ := e
  cases y; cases z; simp_all⟩
instance bv_false_idfree : IdFree (⟨false⟩ : BV) := ⟨fun _ v => absurd ((bv_validN _).mp v) (by decide)⟩
theorem bv_true_not_idfree : ¬ IdFree (⟨true⟩ : BV) := fun h => h.id_free0_r ⟨true⟩ rfl rfl
theorem bv_false_not_valid : ¬ ✓ (⟨false⟩ : BV) := fun h => by
  have := (valid_iff_validN.mp h) 0
  cases this

/-- Bool, op = and, total core `true` (the unit), order = equality: a UORA whose order is not the inclusion. -/
structure BT where b : Bool
instance : OFE BT := OFE.ofDiscrete BT
instance : OFE.Discrete BT := ⟨fun h => h⟩
def btData : DiscreteORAData BT where
  pcore _ := some ⟨true⟩
  op x y := ⟨x.b && y.b⟩
  Valid _ := True
  Order := Eq
  assoc x y z := congrArg BT.mk (Bool.and_assoc x.b y.b z.b).symm
  comm x y := congrArg BT.mk (Bool.and_comm x.b y.b)
  pcore_op_left x _ h := by cases h; cases x; rfl
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ h := h ▸ rfl
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ h e := by subst h; exact ⟨_, e, rfl⟩
  pcore_order_op _ _ h _ := ⟨_, rfl, by cases h; rfl⟩
  pcore_increasing _ _ h y := by cases h; cases y; rfl
  increasing_closed _ _ hx hxy := hxy ▸ hx
instance btORA : ORA BT := ORA.ofDiscreteORAData btData
instance btUORA : UORA BT where
  toORA := btORA
  unit := ⟨true⟩
  unit_valid := trivial
  unit_left_id {x} := by cases x; rfl
  pcore_unit := rfl
  ord_refl _ := rfl
instance btTotal : IsTotal BT := ⟨fun _ => ⟨_, rfl⟩⟩
theorem bt_not_inc : ¬ Increasing (⟨false⟩ : BT) := fun h => by
  have := h.increasing ⟨true⟩
  cases this

/-- Bool, op = and, core `true`, order everywhere true: a UORA that is not `OrdInc`. -/
structure UT where b : Bool
instance : OFE UT := OFE.ofDiscrete UT
instance : OFE.Discrete UT := ⟨fun h => h⟩
def utData : DiscreteORAData UT where
  pcore _ := some ⟨true⟩
  op x y := ⟨x.b && y.b⟩
  Valid _ := True
  Order _ _ := True
  assoc x y z := congrArg UT.mk (Bool.and_assoc x.b y.b z.b).symm
  comm x y := congrArg UT.mk (Bool.and_comm x.b y.b)
  pcore_op_left x _ h := by cases h; cases x; rfl
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ _ _ := trivial
  op_mono_left _ _ _ _ := trivial
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ e := ⟨_, rfl, trivial⟩
  pcore_order_op _ _ _ _ := ⟨_, rfl, trivial⟩
  pcore_increasing _ _ _ _ := trivial
  increasing_closed _ _ _ _ _ := trivial
instance utORA : ORA UT := ORA.ofDiscreteORAData utData
instance utUORA : UORA UT where
  toORA := utORA
  unit := ⟨true⟩
  unit_valid := trivial
  unit_left_id {x} := by cases x; rfl
  pcore_unit := rfl
  ord_refl _ := trivial

/-- Nat with max, core 2 ↦ 0 and identity elsewhere, order everywhere true: total, not `OrdInc`,
core not monotone for the inclusion (1 ≼ 2 but core 1 = 1 is not included in core 2 = 0). -/
structure MX where v : Nat
instance : OFE MX := OFE.ofDiscrete MX
instance : OFE.Discrete MX := ⟨fun h => h⟩
def mxc (x : MX) : MX := ⟨if x.v = 2 then 0 else x.v⟩
def mxData : DiscreteORAData MX where
  pcore x := some (mxc x)
  op x y := ⟨max x.v y.v⟩
  Valid _ := True
  Order _ _ := True
  assoc x y z := by simp only [MX.mk.injEq]; omega
  comm x y := by simp only [MX.mk.injEq]; omega
  pcore_op_left x _ h := by cases h; cases x; simp only [mxc, MX.mk.injEq]; split <;> omega
  pcore_idem x _ h := by cases h; cases x; simp only [mxc, Option.some.injEq, MX.mk.injEq]; split <;> simp_all
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ _ _ := trivial
  op_mono_left _ _ _ _ := trivial
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ e := ⟨_, rfl, trivial⟩
  pcore_order_op _ _ _ _ := ⟨_, rfl, trivial⟩
  pcore_increasing _ _ _ _ := trivial
  increasing_closed _ _ _ _ _ := trivial
instance mxORA : ORA MX := ORA.ofDiscreteORAData mxData
instance mxTotal : IsTotal MX := ⟨fun _ => ⟨_, rfl⟩⟩
theorem mx_not_inc10 : ¬ (⟨1⟩ : MX) ≼ ⟨0⟩ := fun ⟨z, hz⟩ => by
  have : (0:Nat) = max 1 z.v := congrArg MX.v hz
  omega

/-- Nat with max, core = identity, order ≤ (= the inclusion): total and `OrdInc`. -/
structure MI where v : Nat
instance : OFE MI := OFE.ofDiscrete MI
instance : OFE.Discrete MI := ⟨fun h => h⟩
def miData : DiscreteORAData MI where
  pcore x := some x
  op x y := ⟨max x.v y.v⟩
  Valid _ := True
  Order x y := x.v ≤ y.v
  assoc x y z := by simp only [MI.mk.injEq]; omega
  comm x y := by simp only [MI.mk.injEq]; omega
  pcore_op_left x _ h := by cases h; cases x; exact congrArg MI.mk (Nat.max_self _)
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := Nat.le_trans h1 h2
  op_mono_left _ _ _ h := by simp only; omega
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ y _ h e := by cases e; exact ⟨y, rfl, h⟩
  pcore_order_op _ _ h _ := by cases h; exact ⟨_, rfl, by simp only; omega⟩
  pcore_increasing _ _ _ _ := by simp only; omega
  increasing_closed _ _ _ _ _ := by simp only; omega
instance miORA : ORA MI := ORA.ofDiscreteORAData miData
instance miTotal : IsTotal MI := ⟨fun _ => ⟨_, rfl⟩⟩
instance miOrdInc : OrdInc MI where
  ord_inc {x y} h := ⟨y, show y = ⟨max x.v y.v⟩ from congrArg MI.mk (by have : x.v ≤ y.v := h; omega)⟩
  ordN_incN {n x y} h := ⟨y, show y = ⟨max x.v y.v⟩ from congrArg MI.mk (by have : x.v ≤ y.v := h; omega)⟩

/-- Pairs of Bools (own part, discarded part) with componentwise or, core = discarded part
(only when present), order = componentwise ≤ (= the inclusion): `IsInc`, not total. -/
structure DF where
  o : Bool
  d : Bool
instance : OFE DF := OFE.ofDiscrete DF
instance : OFE.Discrete DF := ⟨fun h => h⟩
def dfData : DiscreteORAData DF where
  pcore x := if x.d then some ⟨false, true⟩ else none
  op x y := ⟨or x.o y.o, or x.d y.d⟩
  Valid _ := True
  Order x y := (x.o = true → y.o = true) ∧ (x.d = true → y.d = true)
  assoc x y z := by cases x; cases y; cases z; simp [Bool.or_assoc]
  comm x y := by cases x; cases y; simp [Bool.or_comm]
  pcore_op_left x _ h := by rcases x with ⟨a, _|_⟩ <;> simp at h; cases h; simp
  pcore_idem x _ h := by rcases x with ⟨a, _|_⟩ <;> simp at h; cases h; simp
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := ⟨fun h => h2.1 (h1.1 h), fun h => h2.2 (h1.2 h)⟩
  op_mono_left x y z h := by
    rcases x with ⟨_|_, _|_⟩ <;> rcases y with ⟨_|_, _|_⟩ <;> rcases z with ⟨_|_, _|_⟩ <;> simp_all
  valid_of_ord _ _ _ _ := trivial
  pcore_mono x y _ h e := by
    rcases x with ⟨_, _|_⟩ <;> rcases y with ⟨_, _|_⟩ <;> simp_all
  pcore_order_op x _ h y := by
    rcases x with ⟨_, _|_⟩ <;> rcases y with ⟨_, _|_⟩ <;> simp_all
  pcore_increasing x _ h y := by
    rcases x with ⟨_, _|_⟩ <;> rcases y with ⟨_|_, _|_⟩ <;> simp_all
  increasing_closed _ y _ _ z := by
    rcases y with ⟨_|_, _|_⟩ <;> rcases z with ⟨_|_, _|_⟩ <;> simp_all
instance dfORA : ORA DF := ORA.ofDiscreteORAData dfData
theorem df_op (x y : DF) : x • y = ⟨or x.o y.o, or x.d y.d⟩ := rfl
theorem df_ord_inc {x y : DF} (h : x ≼ₒ y) : x ≼ y := ⟨y, by
  have h' : (x.o = true → y.o = true) ∧ (x.d = true → y.d = true) := h
  rcases x with ⟨_|_, _|_⟩ <;> rcases y with ⟨_|_, _|_⟩ <;> simp_all <;> rfl⟩
instance dfIsInc : IsInc DF where
  inc_ord {x y} := fun ⟨z, hz⟩ => by
    subst hz
    show (x.o = true → _) ∧ (x.d = true → _)
    rcases x with ⟨_|_, _|_⟩ <;> rcases z with ⟨_|_, _|_⟩ <;> simp [df_op]
  ord_inc := df_ord_inc
  ordN_incN h := let ⟨z, hz⟩ := df_ord_inc h; ⟨z, OFE.Dist.of_eq hz⟩
theorem df_not_total : ¬ IsTotal DF := fun h => by
  have ⟨_, e⟩ := h.total ⟨true, false⟩
  cases e

/-- Nat with a • b = a + b + 1, no core, order <: every element increasing and id-free, order not reflexive. -/
structure NS where v : Nat
instance : OFE NS := OFE.ofDiscrete NS
instance : OFE.Discrete NS := ⟨fun h => h⟩
def nsData : DiscreteORAData NS where
  pcore _ := none
  op x y := ⟨x.v + y.v + 1⟩
  Valid _ := True
  Order x y := x.v < y.v
  assoc x y z := by simp only [NS.mk.injEq]; omega
  comm x y := by simp only [NS.mk.injEq]; omega
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := Nat.lt_trans h1 h2
  op_mono_left _ _ _ h := by simp only; omega
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ _ _ := by simp only; omega
instance nsORA : ORA NS := ORA.ofDiscreteORAData nsData
instance nsInc (x : NS) : Increasing x := ⟨fun y => by
  show _ < _ + _ + 1; omega⟩

/-- Option Nat with some a • some b = some (a + b + 1) and none absorbing, no core, order =
equality: every `some a` is id-free, `none` is neither id-free nor cancelable. -/
structure NI where v : Option Nat
instance : OFE NI := OFE.ofDiscrete NI
instance : OFE.Discrete NI := ⟨fun h => h⟩
def niop : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b + 1)
  | _, _ => none
def niData : DiscreteORAData NI where
  pcore _ := none
  op x y := ⟨niop x.v y.v⟩
  Valid _ := True
  Order := Eq
  assoc x y z := by
    rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> simp [niop]; omega
  comm x y := by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> simp [niop]; omega
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
instance niORA : ORA NI := ORA.ofDiscreteORAData niData
instance ni_idfree (a : Nat) : IdFree (⟨some a⟩ : NI) := ⟨fun y _ h => by
  have h' : (⟨niop (some a) y.v⟩ : NI) = ⟨some a⟩ := h
  rcases y with ⟨_|b⟩ <;> simp [niop] at h'; omega⟩
theorem ni_none_not_idfree : ¬ IdFree (⟨none⟩ : NI) := fun h => h.id_free0_r ⟨none⟩ trivial rfl

/-- Bool with constant op, no core, n-validity `n = 0` and no valid element, order everywhere true:
an ORA on a discrete OFE whose validity is not discrete. -/
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

/-- Bool with constant op, no core, nothing valid, n-order `n = 0`, order false: an ORA on a
discrete OFE whose order is not discrete. -/
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

/-- The constant-`true` ORA morphism on BT (differs from the identity at false). -/
def btConst : BT -C> BT where
  f _ := ⟨true⟩
  ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  validN _ := trivial
  pcore _ := rfl
  op _ _ := rfl
  monoN_ord _ := rfl
  mono_ord _ := rfl
  increasing _ := ⟨fun y => by cases y; rfl⟩

def sTrue : SiProp := ⟨fun _ => True, fun h _ => h⟩
def sFalse : SiProp := ⟨fun _ => False, fun h _ => h⟩
instance dfOrderRefl : OrderRefl DF := ⟨fun _ => ⟨id, id⟩⟩
instance baOrderRefl : OrderRefl BA := ⟨fun _ => rfl⟩
/-- The contractive functor `Excl (▶ (A -n> B))`: its action uses both arguments. -/
abbrev XF : COFE.OFunctorPre := Excl.ExclOF (LaterOF (HomOF IdOF IdOF))

/-- Nat with n-distance `min x n = min y n` (everything agrees at step 0): a non-discrete OFE
whose bottom element 0 is not discrete. -/
structure TD where v : Nat
instance tdOFE : OFE TD where
  Dist n x y := min x.v n = min y.v n
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b+1)
      simp only [TD.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v n = min y.v n := h
    show min x.v m = min y.v m; omega
theorem td_dist {n} {x y : TD} : x ≡{n}≡ y ↔ min x.v n = min y.v n := Iff.rfl
/-- Max on TD with core 0, order ≤ (n-order on truncations): a UORA whose unit 0 is not discrete. -/
instance tdOp : Op TD where
  op x y := ⟨max x.v y.v⟩
  op_ne := ⟨fun n y z h => by
    show min (max _ y.v) n = min (max _ z.v) n
    have h' : min y.v n = min z.v n := h
    omega⟩
  assoc := by simp only [TD.mk.injEq]; omega
  comm := by simp only [TD.mk.injEq]; omega
instance tdPCore : PCore TD where
  pcore _ := some ⟨0⟩
  pcore_ne _ h := by cases h; exact ⟨_, rfl, OFE.Dist.rfl⟩
  pcore_idem h := by cases h; rfl
instance tdValid : Iris.Valid TD where
  ValidN _ _ := True
  Valid _ := True
  validN_ne _ h := h
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ h := h
instance tdOrdered : Ordered TD where
  OrderN n x y := min x.v n ≤ min y.v n
  Order x y := x.v ≤ y.v
  ordN_ne {n x x' y y'} (hx : min x.v n = min x'.v n) (hy : min y.v n = min y'.v n) h := by
    show min x'.v n ≤ min y'.v n; omega
  ordN_succ {n x y} (h : min x.v (n+1) ≤ min y.v (n+1)) := show min x.v n ≤ min y.v n by omega
  ordN_trans {n x y z} (h1 : min x.v n ≤ min y.v n) (h2 : min y.v n ≤ min z.v n) :=
    show min x.v n ≤ min z.v n by omega
  ord_trans {x y z} (h1 : x.v ≤ y.v) (h2 : y.v ≤ z.v) := show x.v ≤ z.v by omega
  ordN_of_ord {x y} n (h : x.v ≤ y.v) := show min x.v n ≤ min y.v n by omega
def tdz (n : Nat) (x y : TD) : TD := if y.v < n then y else x
instance tdORA : ORA TD where
  validN_op_left _ := trivial
  pcore_op_left {x cx} h := by cases h; show (⟨max 0 x.v⟩ : TD) = x; cases x; simp
  extend {n x y₁ y₂} _ e := ⟨tdz n x y₁, tdz n x y₂, by
      have e' : min x.v n = min (max y₁.v y₂.v) n := e
      cases x with | mk a => cases y₁ with | mk b => cases y₂ with | mk c =>
      show TD.mk a = TD.mk (max (tdz n ⟨a⟩ ⟨b⟩).v (tdz n ⟨a⟩ ⟨c⟩).v)
      simp only at e'
      simp only [tdz, TD.mk.injEq]
      split <;> split <;> simp only <;> omega,
    by
      have e' : min x.v n = min (max y₁.v y₂.v) n := e
      show min (tdz n x y₁).v n = min y₁.v n
      simp only [tdz]; split <;> omega,
    by
      have e' : min x.v n = min (max y₁.v y₂.v) n := e
      show min (tdz n x y₂).v n = min y₂.v n
      simp only [tdz]; split <;> omega⟩
  op_monoN_left_ord {n x y} z (h : min x.v n ≤ min y.v n) :=
    show min (max x.v z.v) n ≤ min (max y.v z.v) n by omega
  op_mono_left_ord {x y} z (h : x.v ≤ y.v) := show max x.v z.v ≤ max y.v z.v by omega
  validN_of_ordN _ _ := trivial
  pcore_monoN_ord _ h := by cases h; exact ⟨_, rfl, show min 0 _ ≤ min 0 _ from Nat.le_refl _⟩
  pcore_mono_ord _ h := by cases h; exact ⟨_, rfl, show 0 ≤ 0 from Nat.le_refl _⟩
  pcore_order_op h _ := by cases h; exact ⟨_, rfl, show 0 ≤ 0 from Nat.le_refl _⟩
  pcore_increasing h := by cases h; exact ⟨fun y => show y.v ≤ max 0 y.v by omega⟩
  increasing_closed {_ _ y} _ _ := ⟨fun z => show z.v ≤ max y.v z.v by omega⟩
  ordN_extend {n x y} _ (h : min x.v n ≤ min y.v n) :=
    ⟨⟨min x.v n⟩, show min (min x.v n) (n+1) ≤ min y.v (n+1) by omega,
      show min (min x.v n) n = min x.v n by omega⟩
instance tdUORA : UORA TD where
  unit := ⟨0⟩
  unit_valid := trivial
  unit_left_id {x} := by show (⟨max 0 x.v⟩ : TD) = x; cases x; simp
  pcore_unit := rfl
  ord_refl x := show x.v ≤ x.v from Nat.le_refl _

end W1c5

open Iris Iris.OFE Iris.ORA W1c5

-- `Iris.ORA.core_ordN_core` (hypothesis 2): necessary, DF (not total): x = own, y = own+discard, core x = own is not below core y = discard
theorem w5_1 : ¬ drop0% Iris.ORA.core_ordN_core 2 := fun h => by
  have := @h DF _ 0 ⟨true, false⟩ ⟨true, true⟩ ⟨fun _ => rfl, fun _ => rfl⟩
  exact absurd (this.1 rfl) (by decide)
-- `Iris.ORA.core_ordN_core` (hypothesis 6): necessary, MI (max, core id, order ≤): core 1 = 1 is not below core 0 = 0
theorem w5_2 : ¬ drop0% Iris.ORA.core_ordN_core 6 := fun h => by
  have : (1 : Nat) ≤ 0 := @h MI _ _ 0 ⟨1⟩ ⟨0⟩
  omega
-- `Iris.ORA.core_mono_ord` (hypothesis 2): necessary, DF (not total) as for core_ordN_core
theorem w5_3 : ¬ drop0% Iris.ORA.core_mono_ord 2 := fun h => by
  have := @h DF _ ⟨true, false⟩ ⟨true, true⟩ ⟨fun _ => rfl, fun _ => rfl⟩
  exact absurd (this.1 rfl) (by decide)
-- `Iris.ORA.core_mono_ord` (hypothesis 5): necessary, MI: core 1 is not below core 0
theorem w5_4 : ¬ drop0% Iris.ORA.core_mono_ord 5 := fun h => by
  have : (1 : Nat) ≤ 0 := @h MI _ _ ⟨1⟩ ⟨0⟩
  omega
-- `Iris.ORA.core_incN_core` (hypothesis 2): necessary, DF (IsInc, not total): own ≼ own+discard, core own = own not included in discard
theorem w5_5 : ¬ drop0% Iris.ORA.core_incN_core 2 := fun h => by
  obtain ⟨z, hz⟩ := @h DF _ _ 0 ⟨true, false⟩ ⟨true, true⟩ ⟨⟨false, true⟩, rfl⟩
  have : (⟨false, true⟩ : DF) = ⟨or true z.o, or false z.d⟩ := hz
  simp at this
-- `Iris.ORA.core_incN_core` (hypothesis 3): necessary, MX (max, core 2 ↦ 0, order true; not OrdInc): 1 ≼ 2 but core 1 = 1 not included in core 2 = 0
theorem w5_6 : ¬ drop0% Iris.ORA.core_incN_core 3 := fun h => by
  obtain ⟨z, hz⟩ := @h MX _ _ 0 ⟨1⟩ ⟨2⟩ ⟨⟨2⟩, rfl⟩
  have : (0 : Nat) = max 1 z.v := congrArg MX.v hz
  omega
-- `Iris.ORA.core_incN_core` (hypothesis 7): necessary, MI: core 1 = 1 not included in core 0 = 0
theorem w5_7 : ¬ drop0% Iris.ORA.core_incN_core 7 := fun h => by
  obtain ⟨z, hz⟩ := @h MI _ _ _ 0 ⟨1⟩ ⟨0⟩
  have : (0 : Nat) = max 1 z.v := congrArg MI.v hz
  omega
-- `Iris.ORA.core_op_mono` (hypothesis 3): necessary, MX: core 1 = 1 not included in core (1 • 2) = 0
theorem w5_8 : ¬ drop0% Iris.ORA.core_op_mono 3 := fun h => by
  obtain ⟨z, hz⟩ := @h MX _ _ ⟨1⟩ ⟨2⟩
  have : (0 : Nat) = max 1 z.v := congrArg MX.v hz
  omega
-- `Iris.ORA.core_mono` (hypothesis 2): necessary, DF (IsInc, not total): own ≼ own+discard, cores not included
theorem w5_9 : ¬ drop0% Iris.ORA.core_mono 2 := fun h => by
  obtain ⟨z, hz⟩ := @h DF _ _ ⟨true, false⟩ ⟨true, true⟩ ⟨⟨false, true⟩, rfl⟩
  have : (⟨false, true⟩ : DF) = ⟨or true z.o, or false z.d⟩ := hz
  simp at this
-- `Iris.ORA.core_mono` (hypothesis 3): necessary, MX: 1 ≼ 2, core 1 = 1 not included in core 2 = 0
theorem w5_10 : ¬ drop0% Iris.ORA.core_mono 3 := fun h => by
  obtain ⟨z, hz⟩ := @h MX _ _ ⟨1⟩ ⟨2⟩ ⟨⟨2⟩, rfl⟩
  have : (0 : Nat) = max 1 z.v := congrArg MX.v hz
  omega
-- `Iris.ORA.core_mono` (hypothesis 6): necessary, MI: core 1 not included in core 0
theorem w5_11 : ¬ drop0% Iris.ORA.core_mono 6 := fun h => by
  obtain ⟨z, hz⟩ := @h MI _ _ _ ⟨1⟩ ⟨0⟩
  have : (0 : Nat) = max 1 z.v := congrArg MI.v hz
  omega
-- `Iris.ORA.increasing_core` (hypothesis 2): necessary, BA (no core): core false = false is not increasing
theorem w5_12 : ¬ drop0% Iris.ORA.increasing_core 2 := fun h => ba_not_inc (@h BA _ ⟨false⟩)
-- `Iris.ORA.ordN_op_right` (hypothesis 5): necessary, BA: true is not below false • true = false
theorem w5_13 : ¬ drop0% Iris.ORA.ordN_op_right 5 := fun h => by
  have : (⟨true⟩ : BA) = ⟨false⟩ := @h BA _ 0 ⟨false⟩ ⟨true⟩
  cases this
-- `Iris.ORA.pcore_ord_self` (hypothesis 4): necessary, BT (core true, order =): core of false is true, not below false
theorem w5_14 : ¬ drop0% Iris.ORA.pcore_ord_self 4 := fun h => by
  have : (⟨true⟩ : BT) = ⟨false⟩ := @h BT _ ⟨false⟩ ⟨true⟩ rfl
  cases this
-- `Iris.ORA.core_ord_self` (hypothesis 2): necessary, NS (a • b = a + b + 1, order <, no core): core 0 = 0 is not < 0
theorem w5_15 : ¬ drop0% Iris.ORA.core_ord_self 2 := fun h => by
  have : (0 : Nat) < 0 := @h NS _ ⟨0⟩ (nsInc _)
  omega
-- `Iris.ORA.core_ord_self` (hypothesis 4): necessary, BT: core false = true is not below false
theorem w5_16 : ¬ drop0% Iris.ORA.core_ord_self 4 := fun h => by
  have : (⟨true⟩ : BT) = ⟨false⟩ := @h BT _ _ ⟨false⟩
  cases this
-- `Iris.ORA.valid_iff_validN'` (hypothesis 2): necessary, VZ (n-valid iff n = 0, never valid): valid at 0, not valid
theorem w5_17 : ¬ drop0% Iris.ORA.valid_iff_validN' 2 := fun h => (@h VZ _ 0 ⟨false⟩).mpr rfl
-- `Iris.ORA.valid_0_iff_validN` (hypothesis 2): necessary, VZ: valid at 0, not at 1
theorem w5_18 : ¬ drop0% Iris.ORA.valid_0_iff_validN 2 := fun h => by
  have : (1 : Nat) = 0 := (@h VZ _ 1 ⟨false⟩).mp rfl
  omega
-- `Iris.ORA.ord_iff_ordN` (hypothesis 2): necessary, VF (n-order iff n = 0, order false)
theorem w5_19 : ¬ drop0% Iris.ORA.ord_iff_ordN 2 := fun h => (@h VF _ 0 ⟨false⟩ ⟨false⟩).mpr rfl
-- `Iris.ORA.ord_0_iff_ordN` (hypothesis 2): necessary, VF: ordered at 0, not at 1
theorem w5_20 : ¬ drop0% Iris.ORA.ord_0_iff_ordN 2 := fun h => by
  have : (1 : Nat) = 0 := (@h VF _ 1 ⟨false⟩ ⟨false⟩).mp rfl
  omega
-- `Iris.ORA.cancelable` (hypothesis 5): necessary, BA: false • true = false • false, true ≠ false
theorem w5_21 : ¬ drop0% Iris.ORA.cancelable 5 := fun h => by
  have := @h BA _ ⟨false⟩ ⟨true⟩ ⟨false⟩ trivial rfl
  cases this
-- `Iris.ORA.cancelable` (hypothesis 6): necessary, BV (valid iff true): false is vacuously cancelable, false • true = false • false
theorem w5_22 : ¬ drop0% Iris.ORA.cancelable 6 := fun h => by
  have := @h BV _ ⟨false⟩ ⟨true⟩ ⟨false⟩ bv_false_canc rfl
  cases this
-- `Iris.ORA.cancelable` (hypothesis 7): necessary, BV: x = y = true, z = false
theorem w5_23 : ¬ drop0% Iris.ORA.cancelable 7 := fun h => by
  have := @h BV _ ⟨true⟩ ⟨true⟩ ⟨false⟩ bv_true_canc rfl
  cases this
-- `Iris.ORA.discrete_cancelable` (hypothesis 3): necessary, VZ (constant op, nothing valid, valid at step 0): H holds vacuously, false is not cancelable at step 0
theorem w5_24 : ¬ drop0% Iris.ORA.discrete_cancelable 3 := fun h => by
  have := (@h VZ _ ⟨false⟩ (fun v _ => (v : False).elim)).cancelableN (n := 0) (y := ⟨true⟩) (z := ⟨false⟩) rfl OFE.Dist.rfl
  cases this
-- `Iris.ORA.discrete_cancelable` (hypothesis 4): necessary, BA: false is not cancelable
theorem w5_25 : ¬ drop0% Iris.ORA.discrete_cancelable 4 := fun h =>
  ba_false_not_canc (@h BA _ ⟨false⟩ (ORA.ofDiscreteORAData_discrete baData))
-- `Iris.ORA.cancelable_op` (hypothesis 4): necessary, BA: x = false, y = true (cancelable), false • true = false not cancelable
theorem w5_26 : ¬ drop0% Iris.ORA.cancelable_op 4 := fun h =>
  ba_false_not_canc (@h BA _ ⟨false⟩ ⟨true⟩ ba_true_canc)
-- `Iris.ORA.cancelable_op` (hypothesis 5): necessary, BA: x = true (cancelable), y = false
theorem w5_27 : ¬ drop0% Iris.ORA.cancelable_op 5 := fun h =>
  ba_false_not_canc (@h BA _ ⟨true⟩ ⟨false⟩ ba_true_canc)
-- `Iris.ORA.exclusive_cancelable` (hypothesis 3): necessary, BA: false is not cancelable
theorem w5_28 : ¬ drop0% Iris.ORA.exclusive_cancelable 3 := fun h => ba_false_not_canc (@h BA _ ⟨false⟩)
-- `Iris.ORA.op_opM_cancel_dist` (hypothesis 7): necessary, BA: x = false, y = true, z = false, mw = none
theorem w5_29 : ¬ drop0% Iris.ORA.op_opM_cancel_dist 7 := fun h => by
  have := @h BA _ 0 none ⟨false⟩ ⟨true⟩ ⟨false⟩ trivial rfl
  cases this
-- `Iris.ORA.op_opM_cancel_dist` (hypothesis 8): necessary, BV: x = false (vacuously cancelable), y = true, z = false, mw = none
theorem w5_30 : ¬ drop0% Iris.ORA.op_opM_cancel_dist 8 := fun h => by
  have := @h BV _ 0 none ⟨false⟩ ⟨true⟩ ⟨false⟩ bv_false_canc rfl
  cases this
-- `Iris.ORA.op_opM_cancel_dist` (hypothesis 9): necessary, BV: x = y = true, z = false, mw = none
theorem w5_31 : ¬ drop0% Iris.ORA.op_opM_cancel_dist 9 := fun h => by
  have := @h BV _ 0 none ⟨true⟩ ⟨true⟩ ⟨false⟩ bv_true_canc rfl
  cases this
-- `Iris.ORA.IdFree.of_dist` (hypothesis 5): necessary, BV: false is id-free (invalid), true is not
theorem w5_32 : ¬ drop0% Iris.ORA.IdFree.of_dist 5 := fun h =>
  bv_true_not_idfree (@h BV _ ⟨false⟩ ⟨true⟩ 0 bv_false_idfree)
-- `Iris.ORA.IdFree.of_dist` (hypothesis 6): necessary, BA: true is not id-free
theorem w5_33 : ¬ drop0% Iris.ORA.IdFree.of_dist 6 := fun h =>
  ba_not_idfree _ (@h BA _ ⟨true⟩ ⟨true⟩ 0 OFE.Dist.rfl)
-- `Iris.OFE.Dist.idFree` (hypothesis 5): necessary, BV: false id-free, true not
theorem w5_34 : ¬ drop0% Iris.OFE.Dist.idFree 5 := fun h =>
  bv_true_not_idfree ((@h BV _ 0 ⟨false⟩ ⟨true⟩).mp bv_false_idfree)
-- `Iris.ORA.id_freeN_r` (hypothesis 7): necessary, BV: false is id-free (invalid) but false • true = false
theorem w5_35 : ¬ drop0% Iris.ORA.id_freeN_r 7 := fun h => @h BV _ 0 0 ⟨false⟩ bv_false_idfree ⟨true⟩ rfl
-- `Iris.ORA.id_freeN_l` (hypothesis 7): necessary, BV: true • false = false
theorem w5_36 : ¬ drop0% Iris.ORA.id_freeN_l 7 := fun h => @h BV _ 0 0 ⟨false⟩ bv_false_idfree ⟨true⟩ rfl
-- `Iris.ORA.id_free_r` (hypothesis 5): necessary, BV: false • true = false
theorem w5_37 : ¬ drop0% Iris.ORA.id_free_r 5 := fun h => @h BV _ ⟨false⟩ bv_false_idfree ⟨true⟩ rfl
-- `Iris.ORA.id_free_l` (hypothesis 5): necessary, BV: true • false = false
theorem w5_38 : ¬ drop0% Iris.ORA.id_free_l 5 := fun h => @h BV _ ⟨false⟩ bv_false_idfree ⟨true⟩ rfl
-- `Iris.ORA.discrete_id_free` (hypothesis 3): necessary, VZ: H vacuous (nothing valid), false valid at 0 and false • false = false
theorem w5_39 : ¬ drop0% Iris.ORA.discrete_id_free 3 := fun h =>
  (@h VZ _ ⟨false⟩ (fun _ v => (v : False).elim)).id_free0_r ⟨false⟩ rfl OFE.Dist.rfl
-- `Iris.ORA.discrete_id_free` (hypothesis 4): necessary, BA: true • true = true
theorem w5_40 : ¬ drop0% Iris.ORA.discrete_id_free 4 := fun h =>
  ba_not_idfree _ (@h BA _ ⟨true⟩ (ORA.ofDiscreteORAData_discrete baData))
-- `Iris.ORA.idFree_op_r` (hypothesis 4): necessary, BA: x = y = true (cancelable), true • true = true not id-free
theorem w5_41 : ¬ drop0% Iris.ORA.idFree_op_r 4 := fun h =>
  ba_not_idfree _ (@h BA _ ⟨true⟩ ⟨true⟩ ba_true_canc)
-- `Iris.ORA.idFree_op_r` (hypothesis 5): necessary, NI (absorbing none): y = some 0 id-free, none • some 0 = none not id-free
theorem w5_42 : ¬ drop0% Iris.ORA.idFree_op_r 5 := fun h =>
  ni_none_not_idfree (@h NI _ ⟨none⟩ ⟨some 0⟩ (ni_idfree 0))
-- `Iris.ORA.idFree_op_l` (hypothesis 4): necessary, BA: x = y = true
theorem w5_43 : ¬ drop0% Iris.ORA.idFree_op_l 4 := fun h =>
  ba_not_idfree _ (@h BA _ ⟨true⟩ ⟨true⟩ ba_true_canc)
-- `Iris.ORA.idFree_op_l` (hypothesis 5): necessary, NI: x = some 0 id-free, y = none
theorem w5_44 : ¬ drop0% Iris.ORA.idFree_op_l 5 := fun h =>
  ni_none_not_idfree (@h NI _ ⟨some 0⟩ ⟨none⟩ (ni_idfree 0))
-- `Iris.ORA.exclusive_idFree` (hypothesis 3): necessary, BA: true is not id-free
theorem w5_45 : ¬ drop0% Iris.ORA.exclusive_idFree 3 := fun h => ba_not_idfree _ (@h BA _ ⟨true⟩)
-- `Iris.ORA.ordN_op_right_of_unit_ordN` (hypothesis 5): necessary, BT (UORA, order =): x = false, y = true
theorem w5_46 : ¬ drop0% Iris.ORA.ordN_op_right_of_unit_ordN 5 := fun h => by
  have : (⟨true⟩ : BT) = ⟨false⟩ := @h BT _ 0 ⟨false⟩ ⟨true⟩
  cases this
-- `Iris.ORA.exists_op_ordN_iff_ordN` (hypothesis 2): necessary, BT: true • false ≼ false but true not below false
theorem w5_47 : ¬ drop0% Iris.ORA.exists_op_ordN_iff_ordN 2 := fun h => by
  have : (⟨true⟩ : BT) = ⟨false⟩ := (@h BT _ 0 ⟨true⟩ ⟨false⟩).mp ⟨⟨false⟩, rfl⟩
  cases this
-- `Iris.ORA.exists_op_ord_iff_ord` (hypothesis 2): necessary, BT as above
theorem w5_48 : ¬ drop0% Iris.ORA.exists_op_ord_iff_ord 2 := fun h => by
  have : (⟨true⟩ : BT) = ⟨false⟩ := (@h BT _ ⟨true⟩ ⟨false⟩).mp ⟨⟨false⟩, rfl⟩
  cases this
-- `Iris.ORA.exists_op_ordN_iff_incN` (hypothesis 2): necessary, UT (UORA, order true): false • c ≼ true, false not included in true
theorem w5_49 : ¬ drop0% Iris.ORA.exists_op_ordN_iff_incN 2 := fun h => by
  obtain ⟨z, hz⟩ := (@h UT _ 0 ⟨false⟩ ⟨true⟩).mp ⟨⟨true⟩, trivial⟩
  have : (⟨true⟩ : UT) = ⟨false && z.b⟩ := hz
  simp at this
-- `Iris.ORA.exists_op_ord_iff_inc` (hypothesis 2): necessary, UT as above
theorem w5_50 : ¬ drop0% Iris.ORA.exists_op_ord_iff_inc 2 := fun h => by
  obtain ⟨z, hz⟩ := (@h UT _ ⟨false⟩ ⟨true⟩).mp ⟨⟨true⟩, trivial⟩
  have : (⟨true⟩ : UT) = ⟨false && z.b⟩ := hz
  simp at this
-- `Iris.ORA.ordN_unit` (hypothesis 4): necessary, BT: unit true is not below false
theorem w5_51 : ¬ drop0% Iris.ORA.ordN_unit 4 := fun h => by
  have : (⟨true⟩ : BT) = ⟨false⟩ := @h BT _ 0 ⟨false⟩
  cases this
-- `Iris.ORA.ord_unit` (hypothesis 3): necessary, BT: unit true is not below false
theorem w5_52 : ¬ drop0% Iris.ORA.ord_unit 3 := fun h => by
  have : (⟨true⟩ : BT) = ⟨false⟩ := @h BT _ ⟨false⟩
  cases this
-- `Iris.ORA.core_idem_L` (hypothesis 3): removable, core x = (pcore x).getD x; if pcore x = some cx then pcore cx = some cx (pcore_idem), else core x = x
theorem w5_53 : drop% Iris.ORA.core_idem_L 3 := by
  intro α _ x
  unfold PCore.core
  cases e : PCore.pcore x with
  | none => simp [e]
  | some cx => simp [PCore.pcore_idem e]
-- `Iris.ORA.coreId_iff_core_eq_self` (hypothesis 3): necessary, BA (no core): core true = true but true is not CoreId
theorem w5_54 : ¬ drop0% Iris.ORA.coreId_iff_core_eq_self 3 := fun h => by
  have := ((@h BA _ ⟨true⟩).mpr rfl).core_id
  cases this
-- `Iris.ORA.core_eq_self` (hypothesis 3): removable, CoreId x gives pcore x = some x, so core x = x without IsTotal
theorem w5_55 : drop% Iris.ORA.core_eq_self 3 := by
  intro α _ x c
  unfold PCore.core
  rw [c.core_id]
  rfl

-- `Iris.ORA.Hom.ext` (hypothesis 6): necessary, BT: the identity and the constant-true morphism differ at false
theorem w5_56 : ¬ drop0% Iris.ORA.Hom.ext 6 := fun h => by
  have := congrArg (fun F : BT -C> BT => F.f ⟨false⟩) (@h BT BT _ _ ORA.Hom.id btConst)
  cases this
-- `Iris.ORA.Hom.monoN_ord` (hypothesis 8): necessary, identity on BA: true is not below false
theorem w5_57 : ¬ drop0% Iris.ORA.Hom.monoN_ord 8 := fun h => by
  have : (⟨true⟩ : BA) = ⟨false⟩ := @h BA BA _ _ ORA.Hom.id 0 ⟨true⟩ ⟨false⟩
  cases this
-- `Iris.ORA.Hom.increasing` (hypothesis 6): necessary, identity on BA: false is not increasing
theorem w5_58 : ¬ drop0% Iris.ORA.Hom.increasing 6 := fun h => ba_not_inc (@h BA BA _ _ ORA.Hom.id ⟨false⟩)
-- `Iris.ORA.Hom.mono` (hypothesis 7): necessary, identity on BA: false is not included in true
theorem w5_59 : ¬ drop0% Iris.ORA.Hom.mono 7 := fun h => by
  obtain ⟨z, hz⟩ := @h BA _ BA _ ORA.Hom.id ⟨false⟩ ⟨true⟩
  have : (⟨true⟩ : BA) = ⟨false && z.b⟩ := hz
  simp at this
-- `Iris.ORA.Hom.monoN` (hypothesis 8): necessary, identity on BA: false is not included in true
theorem w5_60 : ¬ drop0% Iris.ORA.Hom.monoN 8 := fun h => by
  obtain ⟨z, hz⟩ := @h BA _ BA _ ORA.Hom.id 0 ⟨false⟩ ⟨true⟩
  have : (⟨true⟩ : BA) = ⟨false && z.b⟩ := hz
  simp at this
-- `Iris.ORA.Hom.valid` (hypothesis 6): necessary, identity on BV: false is not valid
theorem w5_61 : ¬ drop0% Iris.ORA.Hom.valid 6 := fun h => bv_false_not_valid (@h BV _ BV _ ORA.Hom.id ⟨false⟩)
-- `Iris.RFunctorAffine.affine` (hypothesis 2): necessary, constOF BA: true is included in false but not ordered
theorem w5_62 : ¬ drop0% Iris.RFunctorAffine.affine 2 := fun h => by
  have := (@h (constOF BA) _ Unit Unit _ _).inc_ord (x := (⟨true⟩ : BA)) (y := ⟨false⟩) ⟨⟨false⟩, rfl⟩
  have : (⟨true⟩ : BA) = ⟨false⟩ := this
  cases this
-- `Iris.instRFunctorAffineComposeOF` (hypothesis 5): necessary, F1 = constOF BA (not affine), F2 = constOF Unit
theorem w5_63 : ¬ drop0% Iris.instRFunctorAffineComposeOF 5 := fun h => by
  have := (@h (constOF BA) (constOF Unit) _ (fun _ _ _ _ => inferInstance) _).affine (α := Unit) (β := Unit)
  have := this.inc_ord (x := (⟨true⟩ : BA)) (y := ⟨false⟩) ⟨⟨false⟩, rfl⟩
  have : (⟨true⟩ : BA) = ⟨false⟩ := this
  cases this
-- `Iris.COFE.OFunctor.constOF_RFunctorAffine` (hypothesis 2): necessary, B = BA (not IncOrd)
theorem w5_64 : ¬ drop0% Iris.COFE.OFunctor.constOF_RFunctorAffine 2 := fun h => by
  have := (@h BA _).affine (α := Unit) (β := Unit)
  have := this.inc_ord (x := (⟨true⟩ : BA)) (y := ⟨false⟩) ⟨⟨false⟩, rfl⟩
  have : (⟨true⟩ : BA) = ⟨false⟩ := this
  cases this
-- `Iris.instRFunctorAffineDiscreteFunOF` (hypothesis 3): necessary, F c = constOF BT (BT is a UORA, not IncOrd), C = Unit
theorem w5_65 : ¬ drop0% Iris.instRFunctorAffineDiscreteFunOF 3 := fun h => by
  have := (@h Unit (fun _ => constOF BT) (fun _ => inferInstance)).affine (α := Unit) (β := Unit)
  have := this.inc_ord (x := fun _ => (⟨true⟩ : BT)) (y := fun _ => ⟨false⟩) ⟨fun _ => ⟨false⟩, rfl⟩
  have : (⟨true⟩ : BT) = ⟨false⟩ := this ()
  cases this
-- `Iris.DiscreteFun.ordNR_apply` (hypothesis 6): necessary, β = BA, f = true, g = false
theorem w5_66 : ¬ drop0% Iris.DiscreteFun.ordNR_apply 6 := fun h => by
  rcases @h Unit (fun _ => BA) _ 0 (fun _ => ⟨true⟩) (fun _ => ⟨false⟩) () with e | e <;> cases e
-- `Iris.DiscreteFun.increasing_apply` (hypothesis 4): necessary, β = BA, f = false
theorem w5_67 : ¬ drop0% Iris.DiscreteFun.increasing_apply 4 := fun h =>
  ba_not_inc (@h Unit (fun _ => BA) _ (fun _ => ⟨false⟩) ())
-- `Iris.DiscreteFun.op_apply` (hypothesis 3): necessary (dependent), β = DF is not total
theorem w5_68 : ¬ indep0% Iris.DiscreteFun.op_apply 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => ⟨false, false⟩) (fun _ => ⟨false, false⟩) () ())
-- `Iris.DiscreteFun.core_apply` (hypothesis 3): necessary (dependent), β = DF is not total
theorem w5_69 : ¬ indep0% Iris.DiscreteFun.core_apply 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => ⟨false, false⟩) () ())
-- `Iris.DiscreteFun.ord_apply` (hypothesis 3): necessary (dependent), β = DF is not total
theorem w5_70 : ¬ indep0% Iris.DiscreteFun.ord_apply 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => ⟨false, false⟩) (fun _ => ⟨false, false⟩) () ())
-- `Iris.DiscreteFun.ord_iff` (hypothesis 3): necessary (dependent), β = DF is not total
theorem w5_71 : ¬ indep0% Iris.DiscreteFun.ord_iff 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => ⟨false, false⟩) (fun _ => ⟨false, false⟩) ())
-- `Iris.DiscreteFun.ordN_iff` (hypothesis 3): necessary (dependent), β = DF is not total
theorem w5_72 : ¬ indep0% Iris.DiscreteFun.ordN_iff 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ 0 (fun _ => ⟨false, false⟩) (fun _ => ⟨false, false⟩) ())
-- `Iris.DiscreteFun.inc_apply` (hypothesis 3): necessary (dependent), β = DF is not total
theorem w5_73 : ¬ indep0% Iris.DiscreteFun.inc_apply 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => ⟨false, false⟩) (fun _ => ⟨false, false⟩) () ())
-- `Iris.DiscreteFun.inc_iff` (hypothesis 3): necessary (dependent), β = DF is not total
theorem w5_74 : ¬ indep0% Iris.DiscreteFun.inc_iff 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => ⟨false, false⟩) (fun _ => ⟨false, false⟩) ())
-- `Iris.DiscreteFun.incN_apply` (hypothesis 3): necessary (dependent), β = DF is not total
theorem w5_75 : ¬ indep0% Iris.DiscreteFun.incN_apply 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ 0 (fun _ => ⟨false, false⟩) (fun _ => ⟨false, false⟩) () ())
-- `Iris.DiscreteFun.incN_iff` (hypothesis 3): necessary (dependent), β = DF is not total
theorem w5_76 : ¬ indep0% Iris.DiscreteFun.incN_iff 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ 0 (fun _ => ⟨false, false⟩) (fun _ => ⟨false, false⟩) ())
-- `Iris.DiscreteFun.instOrderRefl` (hypothesis 3): necessary (dependent), β = DF (reflexive order) is not total
theorem w5_77 : ¬ indep0% Iris.DiscreteFun.instOrderRefl 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => inferInstance) ())
-- `Iris.DiscreteFun.instIncOrd` (hypothesis 3): necessary (dependent), β = DF (IsInc) is not total
theorem w5_78 : ¬ indep0% Iris.DiscreteFun.instIncOrd 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => inferInstance) ())
-- `Iris.DiscreteFun.instOrdInc` (hypothesis 3): necessary (dependent), β = DF (IsInc) is not total
theorem w5_79 : ¬ indep0% Iris.DiscreteFun.instOrdInc 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => inferInstance) ())
-- `Iris.DiscreteFun.instIsInc` (hypothesis 3): necessary (dependent), β = DF (IsInc) is not total
theorem w5_80 : ¬ indep0% Iris.DiscreteFun.instIsInc 3 := fun h =>
  df_not_total (@h Unit (fun _ => DF) _ (fun _ => inferInstance) ())
-- `Iris.DiscreteFun.instIncOrd` (hypothesis 4): necessary, β = BT (total, not IncOrd): true is included in false pointwise but not ordered
theorem w5_81 : ¬ drop0% Iris.DiscreteFun.instIncOrd 4 := fun h => by
  have := (@h Unit (fun _ => BT) _ _).inc_ord (x := fun _ => ⟨true⟩) (y := fun _ => ⟨false⟩) ⟨fun _ => ⟨false⟩, rfl⟩
  have : (⟨true⟩ : BT) = ⟨false⟩ := this ()
  cases this
-- `Iris.DiscreteFun.instOrdInc` (hypothesis 4): necessary, β = UT (total, order true): false ≼ₒ true pointwise, not included
theorem w5_82 : ¬ drop0% Iris.DiscreteFun.instOrdInc 4 := fun h => by
  obtain ⟨z, hz⟩ := (@h Unit (fun _ => UT) _ _).ord_inc (x := fun _ => ⟨false⟩) (y := fun _ => ⟨true⟩) (fun _ => trivial)
  have : (⟨true⟩ : UT) = ⟨false && (z ()).b⟩ := congrFun hz ()
  simp at this
-- `Iris.DiscreteFun.instIsInc` (hypothesis 4): necessary, β = BT (not IncOrd)
theorem w5_83 : ¬ drop0% Iris.DiscreteFun.instIsInc 4 := fun h => by
  have := (@h Unit (fun _ => BT) _ _).inc_ord (x := fun _ => ⟨true⟩) (y := fun _ => ⟨false⟩) ⟨fun _ => ⟨false⟩, rfl⟩
  have : (⟨true⟩ : BT) = ⟨false⟩ := this ()
  cases this
-- `Iris.DiscreteFun.ord_apply` (hypothesis 6): necessary, β = BT, f = true, g = false
theorem w5_84 : ¬ drop0% Iris.DiscreteFun.ord_apply 6 := fun h => by
  have : (⟨true⟩ : BT) = ⟨false⟩ := @h Unit (fun _ => BT) _ _ (fun _ => ⟨true⟩) (fun _ => ⟨false⟩) ()
  cases this
-- `Iris.DiscreteFun.inc_apply` (hypothesis 6): necessary, β = BT, f = false, g = true: false not included in true
theorem w5_85 : ¬ drop0% Iris.DiscreteFun.inc_apply 6 := fun h => by
  obtain ⟨z, hz⟩ := @h Unit (fun _ => BT) _ _ (fun _ => ⟨false⟩) (fun _ => ⟨true⟩) ()
  have : (⟨true⟩ : BT) = ⟨false && z.b⟩ := hz
  simp at this
-- `Iris.DiscreteFun.incN_apply` (hypothesis 7): necessary, β = BT, f = false, g = true
theorem w5_86 : ¬ drop0% Iris.DiscreteFun.incN_apply 7 := fun h => by
  obtain ⟨z, hz⟩ := @h Unit (fun _ => BT) _ _ 0 (fun _ => ⟨false⟩) (fun _ => ⟨true⟩) ()
  have : (⟨true⟩ : BT) = ⟨false && z.b⟩ := hz
  simp at this
-- `Iris.Option.ord_of_some_ord_some` (hypothesis 2): necessary, NS (order <, not reflexive): some 0 ≼ some 0 by equality, 0 < 0 fails
theorem w5_87 : ¬ drop0% Iris.Option.ord_of_some_ord_some 2 := fun h => by
  have : (0 : Nat) < 0 := @h NS _ ⟨0⟩ ⟨0⟩ (.inl rfl)
  omega
-- `Iris.Option.ord_of_some_ord_some` (hypothesis 5): necessary, BA (order =): true is not below false
theorem w5_88 : ¬ drop0% Iris.Option.ord_of_some_ord_some 5 := fun h => by
  have : (⟨true⟩ : BA) = ⟨false⟩ := @h BA _ _ ⟨false⟩ ⟨true⟩
  cases this
-- `Iris.Option.ordN_of_some_ordN_some` (hypothesis 2): necessary, NS: some 0 ≼{0} some 0 by equality, 0 < 0 fails
theorem w5_89 : ¬ drop0% Iris.Option.ordN_of_some_ordN_some 2 := fun h => by
  have : (0 : Nat) < 0 := @h NS _ 0 ⟨0⟩ ⟨0⟩ (.inl OFE.Dist.rfl)
  omega
-- `Iris.Option.ordN_of_some_ordN_some` (hypothesis 6): necessary, BA: true is not below false
theorem w5_90 : ¬ drop0% Iris.Option.ordN_of_some_ordN_some 6 := fun h => by
  have : (⟨true⟩ : BA) = ⟨false⟩ := @h BA _ _ 0 ⟨false⟩ ⟨true⟩
  cases this
-- `Iris.RFunctorContractive.map_distLater` (hypothesis 15): necessary, F = Excl (▶ (A -n> B)), n = 1, f1 = const True, f2 = const False : Unit -n> SiProp, g = id
theorem w5_91 : ¬ drop0% Iris.RFunctorContractive.map_distLater 15 := fun h => by
  have := @h SiProp Unit SiProp SiProp XF _ _ _ _ _ 1 ⟨Function.const _ sTrue, const_ne⟩ ⟨Function.const _ sFalse, const_ne⟩
    OFE.Hom.id OFE.Hom.id DistLater.rfl (Excl.excl ⟨OFE.Hom.id⟩)
  have h2 : sTrue ≡{0}≡ sFalse := (this 0 (by omega)) ()
  exact (h2 (m := 0) (Nat.le_refl 0)).mp trivial
-- `Iris.RFunctorContractive.map_distLater` (hypothesis 16): necessary, F = Excl (▶ (A -n> B)), n = 1, f = id, g1 = const True, g2 = const False : Unit -n> SiProp
theorem w5_92 : ¬ drop0% Iris.RFunctorContractive.map_distLater 16 := fun h => by
  have := @h Unit Unit Unit SiProp XF _ _ _ _ _ 1 OFE.Hom.id OFE.Hom.id
    ⟨Function.const _ sTrue, const_ne⟩ ⟨Function.const _ sFalse, const_ne⟩ DistLater.rfl (Excl.excl ⟨OFE.Hom.id⟩)
  have h2 : sTrue ≡{0}≡ sFalse := (this 0 (by omega)) ()
  exact (h2 (m := 0) (Nat.le_refl 0)).mp trivial
-- `Iris.URFunctorContractive.map_distLater` (hypothesis 15): necessary, F = Option (Excl (▶ (A -n> B))), as for the RFunctor version
theorem w5_93 : ¬ drop0% Iris.URFunctorContractive.map_distLater 15 := fun h => by
  have := @h SiProp Unit SiProp SiProp (OptionOF XF) _ _ _ _ _ 1 ⟨Function.const _ sTrue, const_ne⟩ ⟨Function.const _ sFalse, const_ne⟩
    OFE.Hom.id OFE.Hom.id DistLater.rfl (some (Excl.excl ⟨OFE.Hom.id⟩))
  have h2 : sTrue ≡{0}≡ sFalse := (this 0 (by omega)) ()
  exact (h2 (m := 0) (Nat.le_refl 0)).mp trivial
-- `Iris.URFunctorContractive.map_distLater` (hypothesis 16): necessary, F = Option (Excl (▶ (A -n> B))), as for the RFunctor version
theorem w5_94 : ¬ drop0% Iris.URFunctorContractive.map_distLater 16 := fun h => by
  have := @h Unit Unit Unit SiProp (OptionOF XF) _ _ _ _ _ 1 OFE.Hom.id OFE.Hom.id
    ⟨Function.const _ sTrue, const_ne⟩ ⟨Function.const _ sFalse, const_ne⟩ DistLater.rfl (some (Excl.excl ⟨OFE.Hom.id⟩))
  have h2 : sTrue ≡{0}≡ sFalse := (this 0 (by omega)) ()
  exact (h2 (m := 0) (Nat.le_refl 0)).mp trivial

-- `Iris.DiscreteFun.instDiscreteEForallUnit` (hypothesis 3): necessary, β = TD (max UORA on Nat with n-distance min · n): the unit 0 agrees with 1 at step 0
theorem w5_95 : ¬ drop0% Iris.DiscreteFun.instDiscreteEForallUnit 3 := fun h => by
  have := (@h Unit (fun _ => TD) _).discrete (y := fun _ => ⟨1⟩) (fun _ => rfl)
  have : (⟨0⟩ : TD) = ⟨1⟩ := congrFun this ()
  cases this
