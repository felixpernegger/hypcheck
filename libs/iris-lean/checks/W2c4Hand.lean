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

namespace W2c4
open Iris Iris.OFE Iris.ORA

/-- Bool, op = and, total core true, order = equality: discrete total UORA (copied from W1c5 BT). -/
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

/-- Bool, constant op false, only true valid, no core, order = equality: true is exclusive,
false is invalid. -/
structure EX where b : Bool
instance : OFE EX := OFE.ofDiscrete EX
instance : OFE.Discrete EX := ⟨fun h => h⟩
def exData : DiscreteORAData EX where
  pcore _ := none
  op _ _ := ⟨false⟩
  Valid x := x.b = true
  Order := Eq
  assoc _ _ _ := rfl
  comm _ _ := rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ h := nomatch h
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ _ := rfl
  valid_of_ord _ _ h v := h ▸ v
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ hx _ := by cases hx ⟨true⟩
instance exORA : ORA EX := ORA.ofDiscreteORAData exData
instance exExcl : Exclusive (⟨true⟩ : EX) := ⟨fun _ h => nomatch h⟩
instance exIdFree : IdFree (⟨true⟩ : EX) := ⟨fun _ _ h => nomatch h⟩

/-- Nat, op = +, core 0, all valid, order ≤: discrete total ORA, not idempotent. -/
structure NA where v : Nat
instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨fun h => h⟩
def naData : DiscreteORAData NA where
  pcore _ := some ⟨0⟩
  op x y := ⟨x.v + y.v⟩
  Valid _ := True
  Order x y := x.v ≤ y.v
  assoc x y z := congrArg NA.mk (Nat.add_assoc x.v y.v z.v).symm
  comm x y := congrArg NA.mk (Nat.add_comm x.v y.v)
  pcore_op_left x _ h := by cases h; cases x; simp
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := Nat.le_trans h1 h2
  op_mono_left _ _ _ h := Nat.add_le_add_right h _
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ e := by cases e; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_order_op _ _ h _ := by cases h; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_increasing _ _ h y := by cases h; show y.v ≤ 0 + y.v; omega
  increasing_closed _ y _ _ z := show z.v ≤ y.v + z.v by omega
instance naORA : ORA NA := ORA.ofDiscreteORAData naData

/-- Bool, op = or, core false, valid iff false, order implication: discrete UORA with an invalid
element. -/
structure BU where b : Bool
instance : OFE BU := OFE.ofDiscrete BU
instance : OFE.Discrete BU := ⟨fun h => h⟩
def buData : DiscreteORAData BU where
  pcore _ := some ⟨false⟩
  op x y := ⟨x.b || y.b⟩
  Valid x := x.b = false
  Order x y := x.b = true → y.b = true
  assoc x y z := congrArg BU.mk (Bool.or_assoc x.b y.b z.b).symm
  comm x y := congrArg BU.mk (Bool.or_comm x.b y.b)
  pcore_op_left x _ h := by cases h; cases x; rfl
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left x y h := by cases x with | mk a => cases y with | mk b => cases a <;> cases b <;> simp_all
  ord_trans _ _ _ h1 h2 h := h2 (h1 h)
  op_mono_left x y z h := by
    cases x with | mk a => cases y with | mk b => cases z with | mk c =>
    cases a <;> cases b <;> cases c <;> simp_all
  valid_of_ord x y h v := by cases x with | mk a => cases y with | mk b => cases a <;> cases b <;> simp_all
  pcore_mono _ _ _ _ e := by cases e; exact ⟨_, rfl, id⟩
  pcore_order_op _ _ h _ := by cases h; exact ⟨_, rfl, id⟩
  pcore_increasing _ _ h y := by cases h; cases y with | mk a => cases a <;> simp
  increasing_closed x y _ _ z := by
    cases y with | mk a => cases z with | mk c => cases a <;> cases c <;> simp
instance buORA : ORA BU := ORA.ofDiscreteORAData buData
instance buUORA : UORA BU where
  toORA := buORA
  unit := ⟨false⟩
  unit_valid := (valid_iff_validN (α := BU)).mpr fun _ => rfl
  unit_left_id {x} := by cases x; rfl
  pcore_unit := rfl
  ord_refl _ := id

/-- Nat, op = max, core 0, order = equality, n-validity `v = 0 ∨ n + v ≤ 2` (1 is valid up to
step 1, 2 only at step 0), validity `v = 0`: a total UORA on a discrete OFE whose validity is not
discrete. -/
structure VL where v : Nat
instance : OFE VL := OFE.ofDiscrete VL
instance : OFE.Discrete VL := ⟨fun h => h⟩
instance vlOp : Op VL where
  op x y := ⟨max x.v y.v⟩
  op_ne := ⟨fun _ _ _ (h : _ = _) => by subst h; exact OFE.Dist.rfl⟩
  assoc {x y z} := congrArg VL.mk (Nat.max_assoc x.v y.v z.v).symm
  comm {x y} := congrArg VL.mk (Nat.max_comm x.v y.v)
instance vlPCore : PCore VL where
  pcore _ := some ⟨0⟩
  pcore_ne _ h := by cases h; exact ⟨_, rfl, OFE.Dist.rfl⟩
  pcore_idem h := by cases h; rfl
instance vlValid : Iris.Valid VL where
  ValidN n x := x.v = 0 ∨ n + x.v ≤ 2
  Valid x := x.v = 0
  validN_ne h v := by subst h; exact v
  valid_iff_validN := ⟨fun h _ => Or.inl h, fun h => by have := h 3; omega⟩
  validN_succ h := by omega
instance vlOrdered : Ordered VL where
  OrderN _ x y := x = y
  Order x y := x = y
  ordN_ne h1 h2 h := by subst h1; subst h2; exact h
  ordN_succ h := h
  ordN_trans h1 h2 := h1.trans h2
  ord_trans h1 h2 := h1.trans h2
  ordN_of_ord _ h := h
instance vlORA : ORA VL where
  validN_op_left {n x y} (h : max x.v y.v = 0 ∨ n + max x.v y.v ≤ 2) :=
    show x.v = 0 ∨ n + x.v ≤ 2 by omega
  pcore_op_left {x _} h := by cases h; show (⟨max 0 x.v⟩ : VL) = x; cases x; simp
  extend {_ _ y₁ y₂} _ e := ⟨y₁, y₂, e, OFE.Dist.rfl, OFE.Dist.rfl⟩
  op_monoN_left_ord _ h := by subst h; rfl
  op_mono_left_ord _ h := by subst h; rfl
  validN_of_ordN h v := by subst h; exact v
  pcore_monoN_ord h e := by subst h; exact ⟨_, e, rfl⟩
  pcore_mono_ord h e := by subst h; exact ⟨_, e, rfl⟩
  pcore_order_op h _ := by cases h; exact ⟨_, rfl, rfl⟩
  pcore_increasing h := by cases h; exact ⟨fun y => show y = ⟨max 0 y.v⟩ by cases y; simp⟩
  increasing_closed hx h := by rcases h with h | h <;> (cases h; exact hx)
  ordN_extend _ h := ⟨_, rfl, h.symm⟩
instance vlUORA : UORA VL where
  unit := ⟨0⟩
  unit_valid := rfl
  unit_left_id {x} := by show (⟨max 0 x.v⟩ : VL) = x; cases x; simp
  pcore_unit := rfl
  ord_refl _ := rfl
instance vlTotal : IsTotal VL := ⟨fun _ => ⟨_, rfl⟩⟩

/-- Bool, op = or, core = identity, all valid, order implication: every element is a core. -/
structure BO where b : Bool
instance : OFE BO := OFE.ofDiscrete BO
instance : OFE.Discrete BO := ⟨fun h => h⟩
def boData : DiscreteORAData BO where
  pcore x := some x
  op x y := ⟨x.b || y.b⟩
  Valid _ := True
  Order x y := x.b = true → y.b = true
  assoc x y z := congrArg BO.mk (Bool.or_assoc x.b y.b z.b).symm
  comm x y := congrArg BO.mk (Bool.or_comm x.b y.b)
  pcore_op_left x _ h := by cases h; cases x with | mk a => cases a <;> rfl
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 h := h2 (h1 h)
  op_mono_left x y z h := by
    cases x with | mk a => cases y with | mk b => cases z with | mk c =>
    cases a <;> cases b <;> cases c <;> simp_all
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ h e := by cases e; exact ⟨_, rfl, h⟩
  pcore_order_op x _ h y := by
    cases h; refine ⟨_, rfl, fun hx => ?_⟩
    show (x.b || y.b) = true; simp [hx]
  pcore_increasing x _ h y := by cases h; intro hy; show (x.b || y.b) = true; simp [hy]
  increasing_closed x y _ _ z := by intro hz; show (y.b || z.b) = true; simp [hz]
instance boORA : ORA BO := ORA.ofDiscreteORAData boData
instance boCore (x : BO) : CoreId x := ⟨rfl⟩
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


abbrev bT : BT := ⟨true⟩
abbrev bF : BT := ⟨false⟩
theorem bt_bad : ¬ ((bT, bT) ~l~> (bT, bF)) := fun h => nomatch (h 0 none trivial rfl).2
theorem ex_bad : ¬ (((⟨true⟩ : EX), (⟨true⟩ : EX)) ~l~> (⟨false⟩, ⟨false⟩)) :=
  fun h => nomatch (h 0 none rfl rfl).1
theorem vl_bad : ¬ (((⟨1⟩ : VL), (⟨1⟩ : VL)) ~l~> (⟨2⟩, ⟨2⟩)) := fun h => by
  have := (h 1 none (Or.inr (by decide)) rfl).1
  change 2 = 0 ∨ 1 + 2 ≤ 2 at this; omega
theorem vl_not_valid : ¬ ✓ (⟨1⟩ : VL) := fun h => nomatch (h : 1 = 0)

/-- Discrete OFE on Bool as a fresh structure (Dist = Eq). -/
structure DB where b : Bool
instance : OFE DB := OFE.ofDiscrete DB
instance dbCOFE : COFE DB := COFE.ofDiscrete DB
abbrev dT : DB := ⟨true⟩
abbrev dF : DB := ⟨false⟩
theorem db_ne : ¬ ([dT] : List DB) ≡{0}≡ [dF] := fun h => nomatch (Iris.cons_dist_inj h).1
theorem db_nil_ne {n} : ¬ ([] : List DB) ≡{n}≡ [dT] := fun h => nomatch h

/-- Discrete OFE on Nat (Dist = Eq), (Nat, +, 0) as a monoid (copied from W1c1). -/
instance natOFE : OFE Nat := OFE.ofDiscrete Nat
theorem natNE2 (f : Nat → Nat → Nat) : OFE.NonExpansive₂ f :=
  ⟨fun n x₁ x₂ h y₁ y₂ h' => by
    change x₁ = x₂ at h; change y₁ = y₂ at h'; subst h h'; exact OFE.Dist.of_eq rfl⟩
def ad (a b : Nat) : Nat := a + b
instance addMon : Iris.Algebra.MonoidOps ad 0 where
  op_ne := natNE2 _
  op_assoc := Nat.add_assoc _ _ _
  op_comm := Nat.add_comm _ _
  op_left_id := Nat.zero_add _

/-- Bool, op = and, no core, all valid, order = equality (copied from Probe1 BA): not IncOrd. -/
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

/-- Bool, op = or, no core, all valid, order everywhere true: OrderRefl, not OrdInc. -/
structure BR where b : Bool
instance : OFE BR := OFE.ofDiscrete BR
instance : OFE.Discrete BR := ⟨fun h => h⟩
def brData : DiscreteORAData BR where
  pcore _ := none
  op x y := ⟨x.b || y.b⟩
  Valid _ := True
  Order _ _ := True
  assoc x y z := congrArg BR.mk (Bool.or_assoc x.b y.b z.b).symm
  comm x y := congrArg BR.mk (Bool.or_comm x.b y.b)
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
instance brORA : ORA BR := ORA.ofDiscreteORAData brData
instance brRefl : OrderRefl BR := ⟨fun _ => trivial⟩

/-- Bool, constant op false, no core, all valid, order `y = false` (irreflexive at true):
discrete, IncOrd and OrdInc, not OrderRefl. -/
structure OF where b : Bool
instance : OFE OF := OFE.ofDiscrete OF
instance : OFE.Discrete OF := ⟨fun h => h⟩
def ofData : DiscreteORAData OF where
  pcore _ := none
  op _ _ := ⟨false⟩
  Valid _ := True
  Order _ y := y.b = false
  assoc _ _ _ := rfl
  comm _ _ := rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ _ h := h
  op_mono_left _ _ _ _ := rfl
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ _ _ := rfl
instance ofORA : ORA OF := ORA.ofDiscreteORAData ofData
theorem of_eqF {y : OF} (h : y.b = false) : y = ⟨false⟩ := by cases y; cases h; rfl
instance ofIncOrd : IncOrd OF := ⟨fun ⟨_, e⟩ => by
  show _ = false; rw [show _ = _ from e]; rfl⟩
instance ofOrdInc : OrdInc OF where
  ord_inc {x y} h := ⟨x, show y = ⟨false⟩ from of_eqF h⟩
  ordN_incN {n x y} h := ⟨x, show y = ⟨false⟩ from of_eqF h⟩

/-- Bool, constant op false, no core, all valid, n-order everywhere true, order `x = y ∨ y = false`:
an ORA on a discrete OFE whose order is not discrete; OrderRefl and IncOrd. -/
structure OR where b : Bool
instance : OFE OR := OFE.ofDiscrete OR
instance : OFE.Discrete OR := ⟨fun h => h⟩
instance orOp : Op OR where
  op _ _ := ⟨false⟩
  op_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  assoc := rfl
  comm := rfl
instance orPCore : PCore OR where
  pcore _ := none
  pcore_ne _ h := nomatch h
  pcore_idem h := nomatch h
instance orValid : Iris.Valid OR where
  ValidN _ _ := True
  Valid _ := True
  validN_ne _ h := h
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ h := h
instance orOrdered : Ordered OR where
  OrderN _ _ _ := True
  Order x y := x = y ∨ y.b = false
  ordN_ne _ _ _ := trivial
  ordN_succ _ := trivial
  ordN_trans _ _ := trivial
  ord_trans h1 h2 := by
    rcases h2 with h2 | h2
    · subst h2; exact h1
    · exact .inr h2
  ordN_of_ord _ _ := trivial
instance orORA : ORA OR where
  validN_op_left _ := trivial
  pcore_op_left h := nomatch h
  extend {_ _ y₁ y₂} _ e := ⟨y₁, y₂, e, OFE.Dist.rfl, OFE.Dist.rfl⟩
  op_monoN_left_ord _ _ := trivial
  op_mono_left_ord _ _ := .inl rfl
  validN_of_ordN _ _ := trivial
  pcore_monoN_ord _ h := nomatch h
  pcore_mono_ord _ h := nomatch h
  pcore_order_op h := nomatch h
  pcore_increasing h := nomatch h
  increasing_closed _ _ := ⟨fun _ => .inr rfl⟩
  ordN_extend _ _ := ⟨_, trivial, OFE.Dist.rfl⟩
instance orRefl : OrderRefl OR := ⟨fun _ => .inl rfl⟩
instance orIncOrd : IncOrd OR := ⟨fun ⟨_, e⟩ => .inr (by rw [show _ = _ from e]; rfl)⟩

instance boRefl : OrderRefl BO := ⟨fun _ => id⟩
instance boIncOrd : IncOrd BO := ⟨fun {x y} ⟨c, e⟩ hx => by
  rw [show y = _ from e]; show (x.b || c.b) = true; simp [hx]⟩
theorem bo_le {x y : BO} (h : x.b = true → y.b = true) : y = x • y := by
  cases x with | mk a => cases y with | mk b =>
  show _ = BO.mk (a || b); cases a <;> cases b <;> simp_all
instance boOrdInc : OrdInc BO where
  ord_inc {x y} h := ⟨y, bo_le h⟩
  ordN_incN {n x y} h := ⟨y, bo_le h⟩
abbrev aT : BA := ⟨true⟩
abbrev aF : BA := ⟨false⟩
abbrev rT : BR := ⟨true⟩
abbrev rF : BR := ⟨false⟩
abbrev oT : OR := ⟨true⟩
abbrev oF : OR := ⟨false⟩
abbrev fT : OF := ⟨true⟩
abbrev t1 : TD := ⟨1⟩
abbrev t2 : TD := ⟨2⟩
abbrev boT : BO := ⟨true⟩
abbrev boF : BO := ⟨false⟩
instance baDisc : ORA.Discrete BA := ORA.ofDiscreteORAData_discrete baData
instance brDisc : ORA.Discrete BR := ORA.ofDiscreteORAData_discrete brData
instance ofDisc : ORA.Discrete OF := ORA.ofDiscreteORAData_discrete ofData
instance boDisc : ORA.Discrete BO := ORA.ofDiscreteORAData_discrete boData
end W2c4

open Iris Iris.OFE Iris.ORA W2c4


-- `Iris.LocalUpdate.trans` idx 5: necessary (BT, y = z = (T,F), x = (T,T))
theorem w2c4_1 : ¬ drop0% Iris.LocalUpdate.trans 5 := fun h =>
  bt_bad (@h BT _ (bT, bT) (bT, bF) (bT, bF) (LocalUpdate.id _))
-- `Iris.LocalUpdate.trans` idx 6: necessary
theorem w2c4_2 : ¬ drop0% Iris.LocalUpdate.trans 6 := fun h =>
  bt_bad (@h BT _ (bT, bT) (bT, bT) (bT, bF) (LocalUpdate.id _))
-- `Iris.LocalUpdate.exclusive` idx 3: necessary (BT, y = T, x = F, x' = T, frame F)
theorem w2c4_3 : ¬ drop0% Iris.LocalUpdate.exclusive 3 := fun h =>
  nomatch (@h BT _ bT bF bT trivial 0 (some bF) trivial rfl).2
-- `Iris.LocalUpdate.exclusive` idx 6: necessary (EX, x' = F invalid)
theorem w2c4_4 : ¬ drop0% Iris.LocalUpdate.exclusive 6 := fun h =>
  nomatch (@h EX _ ⟨true⟩ _ ⟨true⟩ ⟨false⟩ 0 none rfl rfl).1
-- `Iris.LocalUpdate.op` idx 5: necessary (EX, z • x invalid)
theorem w2c4_5 : ¬ drop0% Iris.LocalUpdate.op 5 := fun h =>
  ex_bad (@h EX _ ⟨true⟩ ⟨true⟩ ⟨true⟩)
-- `Iris.LocalUpdate.op_discrete` idx 2: necessary (VL, 1 not valid, 2 = 2 • 1 invalid at step 1)
theorem w2c4_6 : ¬ drop0% Iris.LocalUpdate.op_discrete 2 := fun h =>
  vl_bad (@h VL _ ⟨1⟩ ⟨1⟩ ⟨2⟩ (fun v => absurd v vl_not_valid))
-- `Iris.LocalUpdate.op_discrete` idx 6: necessary (EX)
theorem w2c4_7 : ¬ drop0% Iris.LocalUpdate.op_discrete 6 := fun h =>
  ex_bad (@h EX _ _ ⟨true⟩ ⟨true⟩ ⟨true⟩)
-- `Iris.LocalUpdate.op_frame` idx 7: necessary (BT)
theorem w2c4_8 : ¬ drop0% Iris.LocalUpdate.op_frame 7 := fun h =>
  bt_bad (@h BT _ bT bT bT bF bT)
-- `Iris.LocalUpdate.cancel` idx 5: necessary (BT, x = F)
theorem w2c4_9 : ¬ drop0% Iris.LocalUpdate.cancel 5 := fun h =>
  nomatch (@h BT _ bF bT bF 0 none trivial rfl).2
-- `Iris.LocalUpdate.replace` idx 4: necessary (BT, x = F, y = T, frame F)
theorem w2c4_10 : ¬ drop0% Iris.LocalUpdate.replace 4 := fun h =>
  nomatch (@h BT _ bF bT trivial 0 (some bF) trivial rfl).2
-- `Iris.LocalUpdate.replace` idx 5: necessary (EX, true id-free, y = F invalid)
theorem w2c4_11 : ¬ drop0% Iris.LocalUpdate.replace 5 := fun h =>
  ex_bad (@h EX _ ⟨true⟩ ⟨false⟩ _)
-- `Iris.LocalUpdate.core_id` idx 5: necessary (NA, x = y = z = 1, no CoreId)
theorem w2c4_12 : ¬ drop0% Iris.LocalUpdate.core_id 5 := fun h =>
  nomatch (@h NA _ ⟨1⟩ ⟨1⟩ ⟨1⟩ ⟨⟨0⟩, rfl⟩ 0 none trivial rfl).2
-- `Iris.LocalUpdate.core_id` idx 6: necessary (BO, y = T core, x = z = F)
theorem w2c4_13 : ¬ drop0% Iris.LocalUpdate.core_id 6 := fun h =>
  nomatch (@h BO _ ⟨false⟩ ⟨true⟩ ⟨false⟩ _ 0 none trivial rfl).2
-- `Iris.LocalUpdate.discrete` idx 2: necessary (VL: left side fails, right side vacuous)
theorem w2c4_14 : ¬ drop0% Iris.LocalUpdate.discrete 2 := fun h =>
  vl_bad ((@h VL _ ⟨1⟩ ⟨1⟩ ⟨2⟩ ⟨2⟩).mpr fun _ v => absurd v vl_not_valid)
-- `Iris.LocalUpdate.valid0` idx 6: necessary (BT)
theorem w2c4_15 : ¬ drop0% Iris.LocalUpdate.valid0 6 := fun h => bt_bad (@h BT _ bT bT bT bF)
-- `Iris.LocalUpdate.valid` idx 2: necessary (VL, premise vacuous)
theorem w2c4_16 : ¬ drop0% Iris.LocalUpdate.valid 2 := fun h =>
  vl_bad (@h VL _ ⟨1⟩ ⟨1⟩ ⟨2⟩ ⟨2⟩ fun v => absurd v vl_not_valid)
-- `Iris.LocalUpdate.valid` idx 7: necessary (BT)
theorem w2c4_17 : ¬ drop0% Iris.LocalUpdate.valid 7 := fun h => bt_bad (@h BT _ _ bT bT bT bF)
-- `Iris.LocalUpdate.total_valid0` idx 2: necessary (EX: T not included in T, F invalid)
theorem w2c4_18 : ¬ drop0% Iris.LocalUpdate.total_valid0 2 := fun h =>
  ex_bad (@h EX _ ⟨true⟩ ⟨true⟩ ⟨false⟩ ⟨false⟩ fun _ _ ⟨_, e⟩ => nomatch e)
-- `Iris.LocalUpdate.total_valid0` idx 7: necessary (BT)
theorem w2c4_19 : ¬ drop0% Iris.LocalUpdate.total_valid0 7 := fun h => bt_bad (@h BT _ _ bT bT bT bF)
-- `Iris.LocalUpdate.total_valid` idx 2: necessary (EX)
theorem w2c4_20 : ¬ drop0% Iris.LocalUpdate.total_valid 2 := fun h =>
  ex_bad (@h EX _ _ ⟨true⟩ ⟨true⟩ ⟨false⟩ ⟨false⟩ fun _ _ ⟨_, e⟩ => nomatch e)
-- `Iris.LocalUpdate.total_valid` idx 3: necessary (VL, total, premise vacuous)
theorem w2c4_21 : ¬ drop0% Iris.LocalUpdate.total_valid 3 := fun h =>
  vl_bad (@h VL _ _ ⟨1⟩ ⟨1⟩ ⟨2⟩ ⟨2⟩ fun v => absurd v vl_not_valid)
-- `Iris.LocalUpdate.total_valid` idx 8: necessary (BT)
theorem w2c4_22 : ¬ drop0% Iris.LocalUpdate.total_valid 8 := fun h => bt_bad (@h BT _ _ _ bT bT bT bF)
-- `Iris.local_update_unital_discrete` idx 2: necessary (VL)
theorem w2c4_23 : ¬ drop0% Iris.local_update_unital_discrete 2 := fun h =>
  vl_bad ((@h VL _ ⟨1⟩ ⟨1⟩ ⟨2⟩ ⟨2⟩).mpr fun _ v => absurd v vl_not_valid)
-- `Iris.cancel_local_update_unit` idx 4: necessary (BT, x = F, y = T, frame F)
theorem w2c4_24 : ¬ drop0% Iris.cancel_local_update_unit 4 := fun h =>
  nomatch (@h BT _ bF bT 0 (some bF) trivial rfl).2
-- `Iris.discrete_unital_triv_local_update` idx 6: necessary (TD, x = 1, y = 2, x' = 0, y' = 1 at step 1)
theorem w2c4_25 : ¬ drop0% Iris.discrete_unital_triv_local_update 6 := fun h => by
  have := (@h TD _ ⟨1⟩ ⟨2⟩ ⟨0⟩ ⟨1⟩ (fun _ => trivial) (fun {z} e => by
    have : (1 : Nat) = max 2 z.v := congrArg TD.v e
    omega) 1 none trivial (show min 1 1 = min 2 1 by rfl)).2
  change min 0 1 = min 1 1 at this; omega
-- `Iris.discrete_unital_triv_local_update` idx 7: necessary (BU, x = y = F, x' = y' = T invalid)
theorem w2c4_26 : ¬ drop0% Iris.discrete_unital_triv_local_update 7 := fun h =>
  nomatch (@h BU _ ⟨false⟩ ⟨false⟩ ⟨true⟩ ⟨true⟩ _ (fun _ => by cases ‹BU› with | mk c => cases c <;> rfl) 0 none rfl rfl).1
-- `Iris.discrete_unital_triv_local_update` idx 8: necessary (BT)
theorem w2c4_27 : ¬ drop0% Iris.discrete_unital_triv_local_update 8 := fun h =>
  bt_bad (@h BT _ bT bT bT bF _ fun _ => trivial)
-- `Iris.LocalUpdate.discrete_fun` idx 7: necessary (Unit → BT)
theorem w2c4_28 : ¬ drop0% Iris.LocalUpdate.discrete_fun 7 := fun h =>
  nomatch (@h Unit (fun _ => BT) _ (fun _ => bT) (fun _ => bT) (fun _ => bT) (fun _ => bF)
    0 none (fun _ => trivial) (fun _ => rfl)).2 ()
-- `Iris.LocalUpdate.prod` idx 8: necessary (BT × BT, first component fails)
theorem w2c4_29 : ¬ drop0% Iris.LocalUpdate.prod 8 := fun h =>
  nomatch (@h BT BT _ _ (bT, bT) (bT, bT) (bT, bT) (bF, bT) (LocalUpdate.id _) 0 none
    ⟨trivial, trivial⟩ ⟨rfl, rfl⟩).2.1
-- `Iris.LocalUpdate.prod` idx 9: necessary
theorem w2c4_30 : ¬ drop0% Iris.LocalUpdate.prod 9 := fun h =>
  nomatch (@h BT BT _ _ (bT, bT) (bT, bT) (bT, bT) (bT, bF) (LocalUpdate.id _) 0 none
    ⟨trivial, trivial⟩ ⟨rfl, rfl⟩).2.2
-- `Iris.LocalUpdate.prod'` idx 12: necessary
theorem w2c4_31 : ¬ drop0% Iris.LocalUpdate.prod' 12 := fun h =>
  nomatch (@h BT BT _ _ bT bT bT bF bT bT bT bT (LocalUpdate.id _) 0 none
    ⟨trivial, trivial⟩ ⟨rfl, rfl⟩).2.1
-- `Iris.LocalUpdate.prod'` idx 13: necessary
theorem w2c4_32 : ¬ drop0% Iris.LocalUpdate.prod' 13 := fun h =>
  nomatch (@h BT BT _ _ bT bT bT bT bT bT bT bF (LocalUpdate.id _) 0 none
    ⟨trivial, trivial⟩ ⟨rfl, rfl⟩).2.2
-- `Iris.LocalUpdate.prod_1` idx 10: necessary
theorem w2c4_33 : ¬ drop0% Iris.LocalUpdate.prod_1 10 := fun h =>
  nomatch (@h BT BT _ _ bT bT bT bF bT bT 0 none ⟨trivial, trivial⟩ ⟨rfl, rfl⟩).2.1
-- `Iris.LocalUpdate.prod_2` idx 10: necessary
theorem w2c4_34 : ¬ drop0% Iris.LocalUpdate.prod_2 10 := fun h =>
  nomatch (@h BT BT _ _ bT bT bT bT bT bF 0 none ⟨trivial, trivial⟩ ⟨rfl, rfl⟩).2.2
-- `Iris.LocalUpdate.option` idx 6: necessary (BT)
theorem w2c4_35 : ¬ drop0% Iris.LocalUpdate.option 6 := fun h =>
  nomatch (@h BT _ bT bT bT bF 0 none trivial rfl).2
-- `Iris.LocalUpdate.option_none` idx 5: necessary (BT, frame T, y' = F)
theorem w2c4_36 : ¬ drop0% Iris.LocalUpdate.option_none 5 := fun h =>
  nomatch (@h BT _ bT bT bF 0 (some (some bT)) trivial rfl).2
-- `Iris.LocalUpdate.alloc_option` idx 4: necessary (EX, x = F invalid)
theorem w2c4_37 : ¬ drop0% Iris.LocalUpdate.alloc_option 4 := fun h =>
  nomatch (@h EX _ ⟨false⟩ none 0 none trivial OFE.Dist.rfl).1
-- `Iris.LocalUpdate.delete_option` idx 4: necessary (BT, x = some T, y = T, frame T)
theorem w2c4_38 : ¬ drop0% Iris.LocalUpdate.delete_option 4 := fun h =>
  nomatch (@h BT _ (some bT) bT 0 (some (some bT)) trivial rfl).2
-- `Iris.LocalUpdate.delete_option_cancelable` idx 3: necessary (BT, mx = some T, frame T)
theorem w2c4_39 : ¬ drop0% Iris.LocalUpdate.delete_option_cancelable 3 := fun h =>
  nomatch (@h BT _ (some bT) 0 (some (some bT)) trivial rfl).2
-- `Iris.modify_ne` idx 5: necessary (DB, f = id, g = const false, l = k = [true])
theorem w2c4_40 : ¬ drop0% Iris.modify_ne 5 := fun h =>
  db_ne (@h DB _ 0 id (fun _ => dF) 0 [dT] [dT] OFE.Dist.rfl)
-- `Iris.filter_ne` idx 4: necessary (TD at step 0: 1 and 2 agree, p distinguishes them)
theorem w2c4_41 : ¬ drop0% Iris.filter_ne 4 := fun h => by
  have := @h TD _ 0 (fun x => x.v == 1) [⟨1⟩] [⟨2⟩] (.cons (show min 1 0 = min 2 0 by rfl) .nil)
  nomatch this
-- `Iris.app_dist_eq_mp` idx 6: necessary (k1 = [true], l = k2 = [])
theorem w2c4_42 : ¬ drop0% Iris.app_dist_eq_mp 6 := fun h => by
  obtain ⟨k1', k2', e, h1, _⟩ := @h DB _ 0 [dT] [] []
  have : k1' = [] := (List.append_eq_nil_iff.mp e.symm).1
  subst this; nomatch h1
-- `Iris.list_ofe_discrete` idx 2: necessary (List TD: [1] and [2] agree at step 0 only)
theorem w2c4_43 : ¬ drop0% Iris.list_ofe_discrete 2 := fun h => by
  have e := (@h TD _).discrete_0 (x := [⟨1⟩]) (y := [⟨2⟩]) (.cons (show min 1 0 = min 2 0 by rfl) .nil)
  exact absurd (TD.mk.inj (List.cons.inj e).1) (by decide)
-- `Iris.cons_discrete` idx 4: necessary (TD, x = 1, l = [])
theorem w2c4_44 : ¬ drop0% Iris.cons_discrete 4 := fun h => by
  have e := (@h TD _ ⟨1⟩ [] _).discrete (y := [⟨2⟩]) (.cons (show min 1 0 = min 2 0 by rfl) .nil)
  exact absurd (TD.mk.inj (List.cons.inj e).1) (by decide)
-- `Iris.dist_Permutation` idx 6: necessary (l1 = [true], l2 = l3 = [])
theorem w2c4_45 : ¬ drop0% Iris.dist_Permutation 6 := fun h => by
  obtain ⟨l, hp, hd⟩ := @h DB _ 0 [dT] [] [] (List.Perm.refl _)
  have := Iris.nil_dist_eq.mp hd
  subst this; exact absurd hp.length_eq (by decide)
-- `Iris.dist_Permutation` idx 7: necessary (l1 = l2 = [], l3 = [true])
theorem w2c4_46 : ¬ drop0% Iris.dist_Permutation 7 := fun h => by
  obtain ⟨l, hp, hd⟩ := @h DB _ 0 [] [] [dT] OFE.Dist.rfl
  have := List.Perm.nil_eq hp
  subst this; nomatch hd
-- `Iris.listComplGo_conv_compl` idx 5: necessary (c0 = [], constant chain [true])
theorem w2c4_47 : ¬ drop0% Iris.listComplGo_conv_compl 5 := fun h =>
  nomatch (@h DB _ 0 (Chain.const [dT]) [])
-- `Iris.list_fmap_ne` idx 7: necessary (f = id, g = const false)
theorem w2c4_48 : ¬ drop0% Iris.list_fmap_ne 7 := fun h =>
  db_ne (@h DB DB _ _ 0 id (fun _ => dF) [dT] [dT] OFE.Dist.rfl)
-- `Iris.list_fmap_dist_inj` idx 9: necessary (f = id, l = [], k = [true])
theorem w2c4_49 : ¬ drop0% Iris.list_fmap_dist_inj 9 := fun h =>
  db_nil_ne (@h DB DB _ _ 0 id (fun e => e) [] [dT])
-- `Iris.list_omap_ne` idx 7: necessary (f = some, g = const none)
theorem w2c4_50 : ¬ drop0% Iris.list_omap_ne 7 := fun h =>
  nomatch (@h DB DB _ _ 0 some (fun _ => none) [dT] [dT] OFE.Dist.rfl)
-- `Iris.list_omap_ne` idx 10: necessary (f = g = some, l = [], k = [true])
theorem w2c4_51 : ¬ drop0% Iris.list_omap_ne 10 := fun h =>
  nomatch (@h DB DB _ _ 0 some some (fun e => e) [] [dT])
-- `Iris.mapIdx_ne` idx 7: necessary (f = projection, g = const false)
theorem w2c4_52 : ¬ drop0% Iris.mapIdx_ne 7 := fun h =>
  db_ne (@h DB DB _ _ 0 (fun _ a => a) (fun _ _ => dF) [dT] [dT] OFE.Dist.rfl)
-- `Iris.list_flatMap_ne` idx 7: necessary (f = singleton, g = const [])
theorem w2c4_53 : ¬ drop0% Iris.list_flatMap_ne 7 := fun h =>
  nomatch (@h DB DB _ _ 0 (fun a => [a]) (fun _ => []) [dT] [dT] OFE.Dist.rfl)
-- `Iris.list_flatMap_ne` idx 10: necessary (f = g = singleton, l = [], k = [true])
theorem w2c4_54 : ¬ drop0% Iris.list_flatMap_ne 10 := fun h =>
  nomatch (@h DB DB _ _ 0 (fun a => [a]) (fun a => [a]) (fun _ _ e => .cons e .nil) [] [dT])
-- `Iris.zipWith_ne` idx 9: necessary (f = first projection, g = const false)
theorem w2c4_55 : ¬ drop0% Iris.zipWith_ne 9 := fun h =>
  db_ne (@h DB DB DB _ _ _ 0 (fun a _ => a) (fun _ _ => dF) [dT] [dT] [dT] [dT] OFE.Dist.rfl OFE.Dist.rfl)
-- `Iris.zipWith_ne` idx 14: necessary (l1 = [], l2 = [true])
theorem w2c4_56 : ¬ drop0% Iris.zipWith_ne 14 := fun h =>
  nomatch (@h DB DB DB _ _ _ 0 (fun a _ => a) (fun a _ => a) (fun e _ => e) [] [dT] [dT] [dT] OFE.Dist.rfl)
-- `Iris.zipWith_ne` idx 15: necessary (k1 = [], k2 = [true])
theorem w2c4_57 : ¬ drop0% Iris.zipWith_ne 15 := fun h =>
  nomatch (@h DB DB DB _ _ _ 0 (fun a _ => a) (fun a _ => a) (fun e _ => e) [dT] [dT] [] [dT] OFE.Dist.rfl)
-- `Iris.bigOpL_dist_2` idx 10: necessary ((Nat, +, 0), l1 = [], l2 = [true], f = g = 1)
theorem w2c4_58 : ¬ drop0% Iris.bigOpL_dist_2 10 := fun h => by
  have := @h Nat DB _ _ ad 0 addMon 0 [] [dT] (fun _ _ => 1) (fun _ _ => 1) (fun e _ _ => nomatch e)
  have h2 : (0 : Nat) = 1 + 0 := this
  exact absurd h2 (by decide)
-- `Iris.bigOpL_dist_2` idx 13: necessary (l1 = l2 = [true], f = 0, g = 1)
theorem w2c4_59 : ¬ drop0% Iris.bigOpL_dist_2 13 := fun h => by
  have := @h Nat DB _ _ ad 0 addMon 0 [dT] [dT] OFE.Dist.rfl (fun _ _ => 0) (fun _ _ => 1)
  have h2 : (0 + 0 : Nat) = 1 + 0 := this
  exact absurd h2 (by decide)
-- `Iris.MaxPrefixList.instDiscrete` idx 2: necessary (TD: [1] and [2] agree only at step 0)
theorem w2c4_70 : ¬ drop0% Iris.MaxPrefixList.instDiscrete 2 := fun h => by
  have e0 : MaxPrefixList.toMaxPrefixList [(⟨1⟩ : TD)] ≡{0}≡ MaxPrefixList.toMaxPrefixList [⟨2⟩] :=
    MaxPrefixList.toMaxPrefixList_ne.ne (.cons (show min 1 0 = min 2 0 by rfl) .nil)
  have e := (@h TD _).discrete_0 e0
  have := (Iris.cons_dist_inj (MaxPrefixList.toMaxPrefixList_dist_inj (e.dist (n := 2)))).1
  change min 1 2 = min 2 2 at this; omega
-- `Iris.MaxPrefixList.toMaxPrefixList_op_left` idx 4: necessary (l1 = [true], l2 = [])
theorem w2c4_71 : ¬ drop0% Iris.MaxPrefixList.toMaxPrefixList_op_left 4 := fun h => by
  have e := @h DB _ [dT] []
  rw [MaxPrefixList.toMaxPrefixList_nil, ORA.unit_right_id, ← MaxPrefixList.toMaxPrefixList_nil] at e
  nomatch MaxPrefixList.toMaxPrefixList_inj e
-- `Iris.MaxPrefixList.toMaxPrefixList_op_right` idx 4: necessary (l1 = [true], l2 = [])
theorem w2c4_72 : ¬ drop0% Iris.MaxPrefixList.toMaxPrefixList_op_right 4 := fun h => by
  have e := @h DB _ [dT] []
  rw [MaxPrefixList.toMaxPrefixList_nil, UORA.unit_left_id, ← MaxPrefixList.toMaxPrefixList_nil] at e
  nomatch MaxPrefixList.toMaxPrefixList_inj e
-- `Iris.MaxPrefixList.toMaxPrefixList_op_validN_aux` idx 5: necessary (l1 = [true], l2 = [])
theorem w2c4_73 : ¬ drop0% Iris.MaxPrefixList.toMaxPrefixList_op_validN_aux 5 := fun h =>
  nomatch @h DB _ 0 [dT] [] (MaxPrefixList.toMaxPrefixList_op_validN.mpr (.inr ⟨[dT], OFE.Dist.rfl⟩))
-- `Iris.MaxPrefixList.local_update` idx 4: necessary (l1 = [true], l2 = [], frame [true])
theorem w2c4_74 : ¬ drop0% Iris.MaxPrefixList.local_update 4 := fun h => by
  have := (@h DB _ [dT] [] 0 (some (MaxPrefixList.toMaxPrefixList [dT]))
    (MaxPrefixList.toMaxPrefixList_validN _) (OFE.Dist.of_eq (op_self _).symm)).2
  have e : MaxPrefixList.toMaxPrefixList ([] : List DB) ≡{0}≡ MaxPrefixList.toMaxPrefixList [dT] := by
    refine this.trans (OFE.Dist.of_eq ?_)
    show MaxPrefixList.toMaxPrefixList ([] : List DB) • MaxPrefixList.toMaxPrefixList [dT] = _
    rw [MaxPrefixList.toMaxPrefixList_nil, UORA.unit_left_id]
  nomatch MaxPrefixList.toMaxPrefixList_dist_inj e
-- `Iris.MonoNat.lb_mono_ord` idx 2: necessary (n1 = 1, n2 = 0: ●0 • ◯1 would be valid)
theorem w2c4_60 : ¬ drop0% Iris.MonoNat.lb_mono_ord 2 := fun h => by
  have := valid_of_ord (op_mono_right_ord (●MN (0 : MaxNat)) (h 1 0))
    ((MonoNat.both_valid 0 0).mpr (Nat.le_refl 0))
  have h2 : 1 ≤ 0 := (MonoNat.both_valid 0 1).mp this
  omega
-- `Iris.MonoNat.lb_mono` idx 2: necessary (n1 = 1, n2 = 0)
theorem w2c4_61 : ¬ drop0% Iris.MonoNat.lb_mono 2 := fun h => by
  have := valid_of_inc (op_mono_right (●MN (0 : MaxNat)) (h 1 0))
    ((MonoNat.both_valid 0 0).mpr (Nat.le_refl 0))
  have h2 : 1 ≤ 0 := (MonoNat.both_valid 0 1).mp this
  omega
-- `Iris.MonoNat.update` idx 2: necessary (n = 1, n' = 0, frame ◯1)
theorem w2c4_62 : ¬ drop0% Iris.MonoNat.update 2 := fun h => by
  have := @h 1 0 0 (some (◯MN (1 : MaxNat))) ((MonoNat.both_valid 1 1).mpr (Nat.le_refl 1)).validN
  have h2 : 1 ≤ 0 := (MonoNat.both_valid 0 1).mp (discrete_valid this)
  omega
-- `Iris.MonoNat.instIsOpAuthMaxNatAuthOfDFrac` idx 5: necessary (dq = dq1 = dq2 = 1)
theorem w2c4_63 : ¬ drop0% Iris.MonoNat.instIsOpAuthMaxNatAuthOfDFrac 5 := fun h =>
  (MonoNat.auth_op_valid 0 0).mp
    ((@h .merge (.own 1) (.own 1) (.own 1) 0).is_op ▸ MonoNat.auth_valid 0)
-- `Iris.MonoZ.lb_mono` idx 2: necessary (n1 = 1, n2 = 0)
theorem w2c4_64 : ¬ drop0% Iris.MonoZ.lb_mono 2 := fun h => by
  have := valid_of_inc (op_mono_right (●MZ (⟨0⟩ : MaxInt)) (h ⟨1⟩ ⟨0⟩))
    ((MonoZ.both_valid ⟨0⟩ ⟨0⟩).mpr (Int.le_refl 0))
  have h2 : (1 : Int) ≤ 0 := (MonoZ.both_valid ⟨0⟩ ⟨1⟩).mp this
  omega
-- `Iris.MonoZ.update` idx 2: necessary (n = 1, n' = 0, frame ◯1)
theorem w2c4_65 : ¬ drop0% Iris.MonoZ.update 2 := fun h => by
  have := @h ⟨1⟩ ⟨0⟩ 0 (some (◯MZ (⟨1⟩ : MaxInt)))
    ((MonoZ.both_valid ⟨1⟩ ⟨1⟩).mpr (Int.le_refl 1)).validN
  have h2 : (1 : Int) ≤ 0 := (MonoZ.both_valid ⟨0⟩ ⟨1⟩).mp (discrete_valid this)
  omega
-- `Iris.MonoZ.instIsOpAuthOptionMaxIntAuthOfDFrac` idx 5: necessary (dq = dq1 = dq2 = 1)
theorem w2c4_66 : ¬ drop0% Iris.MonoZ.instIsOpAuthOptionMaxIntAuthOfDFrac 5 := fun h =>
  (MonoZ.auth_op_valid ⟨0⟩ ⟨0⟩).mp
    ((@h .merge (.own 1) (.own 1) (.own 1) ⟨0⟩).is_op ▸ MonoZ.auth_valid ⟨0⟩)
-- `Iris.MonoZ.instIsOpAuthOptionMaxIntLb` idx 4: necessary (◯0 = ◯1 • ◯1 = ◯1)
theorem w2c4_67 : ¬ drop0% Iris.MonoZ.instIsOpAuthOptionMaxIntLb 4 := fun h => by
  have e : (◯MZ (⟨0⟩ : MaxInt)) = ◯MZ ⟨1⟩ := (@h .merge ⟨0⟩ ⟨1⟩ ⟨1⟩).is_op.trans rfl
  have v := (MonoZ.both_valid ⟨0⟩ ⟨0⟩).mpr (Int.le_refl 0)
  rw [e] at v
  have h2 : (1 : Int) ≤ 0 := (MonoZ.both_valid ⟨0⟩ ⟨1⟩).mp v
  omega
-- `Iris.Algebra.TimeReceipt.instIsOpViewNatFragViewRelFragExcl` idx 4: necessary (0 = 1 + 1)
theorem w2c4_68 : ¬ drop0% Iris.Algebra.TimeReceipt.instIsOpViewNatFragViewRelFragExcl 4 := fun h => by
  have e := (@h .merge 0 1 1).is_op
  have v := (Iris.Algebra.TimeReceipt.auth_op_fragExcl_valid_iff 0 0).mpr (Nat.le_refl 0)
  rw [show Iris.Algebra.TimeReceipt.fragExcl 0 = _ from e] at v
  rw [← Iris.Algebra.TimeReceipt.fragExcl_op] at v
  have := (Iris.Algebra.TimeReceipt.auth_op_fragExcl_valid_iff 0 (1 + 1)).mp v
  omega
-- `Iris.Algebra.TimeReceipt.instIsOpViewNatFragViewRelFragPersOfMaxNatOfNat` idx 4: necessary (0 = max 1 1)
theorem w2c4_69 : ¬ drop0% Iris.Algebra.TimeReceipt.instIsOpViewNatFragViewRelFragPersOfMaxNatOfNat 4 := fun h => by
  have e := (@h .merge 0 1 1).is_op
  have v := (Iris.Algebra.TimeReceipt.auth_op_fragPers_valid_iff 0 0).mpr (Nat.le_refl 0)
  rw [show Iris.Algebra.TimeReceipt.fragPers 0 = _ from e] at v
  rw [← Iris.Algebra.TimeReceipt.fragPers_op] at v
  have := (Iris.Algebra.TimeReceipt.auth_op_fragPers_valid_iff 0 (max 1 1)).mp v
  omega
namespace W2c4
open Iris Iris.OFE Iris.ORA UFracAuth
/-- Validity with an explicit frame `c`: the authoritative part is `b • c` with fraction `q + r`. -/
theorem uf_valid_frame {A : Type} [ORA A] {n : Nat} (q r : Qp) (b c : A) (hv : ✓{n} (b • c)) :
    ✓{n} ((●U{q + r} (b • c)) • ◯U{q} b) :=
  Auth.both_validN_frame.mpr ⟨⟨some (⟨r⟩, c), .inl OFE.Dist.rfl⟩, ⟨trivial, hv⟩⟩
/-- Validity without frame from the order: fraction `q + s` above `q`, element `b ≼ₒ{n} a`. -/
theorem uf_valid_ord {A : Type} [ORA A] {n : Nat} (q s : Qp) (a b : A) (hab : b ≼ₒ{n} a) (ha : ✓{n} a) :
    ✓{n} ((●U{q + s} a) • ◯U{q} b) :=
  Auth.both_validN_frame.mpr ⟨⟨none, .inr ⟨⟨⟨s⟩, rfl⟩, hab⟩⟩, ⟨trivial, ha⟩⟩
/-- Fragments determine their fraction and element. -/
theorem uf_frag_inj {A : Type} [ORA A] {q1 q2 : Qp} {a1 a2 : A}
    (e : (◯U{q1} a1 : UFracAuth (A := A)) = ◯U{q2} a2) : q1 = q2 ∧ a1 = a2 := by
  have h2 : (some (UFrac.mk q1, a1) : Option (UFrac × A)) = some (UFrac.mk q2, a2) := congrArg View.frag e
  simp only [Option.some.injEq, Prod.mk.injEq, UFrac.mk.injEq] at h2
  exact h2
theorem qp_ne : (1 : Qp) ≠ 1 + 1 := by grind
end W2c4
open Iris Iris.OFE Iris.ORA W2c4

-- `Iris.UFracAuth.auth_discrete` idx 4: necessary (A = TD, a = 1 agrees with 2 at step 0)
theorem w2c4_88 : ¬ drop0% Iris.UFracAuth.auth_discrete 4 := fun h => by
  have d0 : (●U{(1 : Qp)} t1 : UFracAuth (A := TD)) ≡{0}≡ ●U{1} t2 :=
    UFracAuth.auth_ne.ne (show min 1 0 = min 2 0 by rfl)
  have e := (@h TD _ 1 t1).discrete d0
  have v : ✓{2} ((●U{(1 : Qp)} t1) • ◯U{(1 : Qp)} t1) := UFracAuth.validN trivial
  have v2 := (OFE.Dist.validN (e.dist (n := 2)).op_l).mp v
  have := UFracAuth.agreeN v2
  change min 2 2 = min 1 2 at this; omega
-- `Iris.UFracAuth.frag_discrete` idx 4: necessary (A = TD)
theorem w2c4_89 : ¬ drop0% Iris.UFracAuth.frag_discrete 4 := fun h => by
  have d0 : (◯U{(1 : Qp)} t1 : UFracAuth (A := TD)) ≡{0}≡ ◯U{1} t2 :=
    UFracAuth.frag_ne.ne (show min 1 0 = min 2 0 by rfl)
  have e := (@h TD _ 1 t1).discrete d0
  have v : ✓{2} ((●U{(1 : Qp)} t1) • ◯U{(1 : Qp)} t1) := UFracAuth.validN trivial
  have v2 := (OFE.Dist.validN (e.dist (n := 2)).op_r).mp v
  have := UFracAuth.agreeN v2
  change min 1 2 = min 2 2 at this; omega
-- `Iris.UFracAuth.validN` idx 5: necessary (A = EX, a = false invalid)
theorem w2c4_90 : ¬ drop0% Iris.UFracAuth.validN 5 := fun h =>
  nomatch UFracAuth.auth_validN.mp (validN_op_left (@h EX _ 0 ⟨false⟩ 1))
-- `Iris.UFracAuth.valid` idx 4: necessary (A = EX, a = false invalid)
theorem w2c4_91 : ¬ drop0% Iris.UFracAuth.valid 4 := fun h =>
  nomatch (valid_iff_validN.mp (UFracAuth.auth_valid.mp (valid_op_left (@h EX _ 1 ⟨false⟩)))) 0
-- `Iris.UFracAuth.ordN` idx 2: necessary (A = BA not IncOrd, b = true, frame false)
theorem w2c4_92 : ¬ drop0% Iris.UFracAuth.ordN 2 := fun h => by
  have := @h BA _ 0 (1 + 1) 1 (aT • aF) aT (uf_valid_frame 1 1 aT aF trivial)
  rcases this with e | e <;> nomatch e
-- `Iris.UFracAuth.includedN` idx 2: necessary (A = BR not OrdInc, b = true, a = false)
theorem w2c4_93 : ¬ drop0% Iris.UFracAuth.includedN 2 := fun h => by
  obtain ⟨c, e⟩ := @h BR _ 0 (1 + 1) 1 rF rT (uf_valid_ord 1 1 rF rT trivial trivial)
  rcases c with _ | ⟨c⟩ <;> nomatch e
-- `Iris.UFracAuth.ord_frame` idx 2: necessary (A = OR, n-order true, order not)
theorem w2c4_94 : ¬ drop0% Iris.UFracAuth.ord_frame 2 := fun h => by
  obtain ⟨c, e⟩ := @h OR _ 1 (1 + 1) oT oF
    (valid_iff_validN.mpr fun _ => uf_valid_ord 1 1 oT oF trivial trivial)
  rcases c with _ | ⟨c⟩ <;> rcases e with e | e <;> rcases e with e | e <;> nomatch e
-- `Iris.UFracAuth.ord` idx 2: necessary (A = OR: IncOrd, n-order true, order not)
theorem w2c4_95 : ¬ drop0% Iris.UFracAuth.ord 2 := fun h => by
  have := @h OR _ _ 1 (1 + 1) oT oF
    (valid_iff_validN.mpr fun _ => uf_valid_ord 1 1 oT oF trivial trivial)
  rcases this with e | e <;> rcases e with e | e <;> nomatch e
-- `Iris.UFracAuth.ord` idx 3: necessary (A = BA, discrete, not IncOrd)
theorem w2c4_96 : ¬ drop0% Iris.UFracAuth.ord 3 := fun h => by
  have := @h BA _ _ 1 (1 + 1) (aT • aF) aT
    (valid_iff_validN.mpr fun _ => uf_valid_frame 1 1 aT aF trivial)
  rcases this with e | e <;> nomatch e
-- `Iris.UFracAuth.included` idx 3: necessary (A = BR, discrete, not OrdInc)
theorem w2c4_97 : ¬ drop0% Iris.UFracAuth.included 3 := fun h => by
  obtain ⟨c, e⟩ := @h BR _ _ 1 (1 + 1) rF rT
    (valid_iff_validN.mpr fun _ => uf_valid_ord 1 1 rF rT trivial trivial)
  rcases c with _ | ⟨c⟩ <;> nomatch e
-- `Iris.UFracAuth.ordN_total` idx 2: necessary (A = OF: IncOrd, true not below itself)
theorem w2c4_98 : ¬ drop0% Iris.UFracAuth.ordN_total 2 := fun h =>
  nomatch @h OF _ _ 0 1 1 fT fT (UFracAuth.validN trivial)
-- `Iris.UFracAuth.ordN_total` idx 3: necessary (A = BA: OrderRefl, not IncOrd)
theorem w2c4_99 : ¬ drop0% Iris.UFracAuth.ordN_total 3 := fun h =>
  nomatch @h BA _ _ 0 1 (1 + 1) (aT • aF) aT (uf_valid_frame 1 1 aT aF trivial)
-- `Iris.UFracAuth.ordN_total` idx 9: necessary (A = BO, true not below false)
theorem w2c4_100 : ¬ drop0% Iris.UFracAuth.ordN_total 9 := fun h =>
  nomatch (@h BO _ _ _ 0 1 1 boF boT) rfl
-- `Iris.UFracAuth.includedN_total` idx 2: necessary (A = OF: OrdInc, true not included in itself)
theorem w2c4_101 : ¬ drop0% Iris.UFracAuth.includedN_total 2 := fun h => by
  obtain ⟨c, e⟩ := @h OF _ _ 0 1 1 fT fT (UFracAuth.validN trivial)
  nomatch e
-- `Iris.UFracAuth.includedN_total` idx 3: necessary (A = BR: OrderRefl, not OrdInc)
theorem w2c4_102 : ¬ drop0% Iris.UFracAuth.includedN_total 3 := fun h => by
  obtain ⟨c, e⟩ := @h BR _ _ 0 1 (1 + 1) rF rT (uf_valid_ord 1 1 rF rT trivial trivial)
  nomatch e
-- `Iris.UFracAuth.includedN_total` idx 9: necessary (A = BO, true not included in false)
theorem w2c4_103 : ¬ drop0% Iris.UFracAuth.includedN_total 9 := fun h => by
  obtain ⟨c, e⟩ := @h BO _ _ _ 0 1 1 boF boT
  nomatch e
-- `Iris.UFracAuth.ord_total` idx 2: necessary (A = OR: OrderRefl, IncOrd, order not discrete)
theorem w2c4_104 : ¬ drop0% Iris.UFracAuth.ord_total 2 := fun h => by
  have := @h OR _ _ _ 1 (1 + 1) oT oF
    (valid_iff_validN.mpr fun _ => uf_valid_ord 1 1 oT oF trivial trivial)
  rcases this with e | e <;> nomatch e
-- `Iris.UFracAuth.ord_total` idx 3: necessary (A = OF: discrete, IncOrd, not OrderRefl)
theorem w2c4_105 : ¬ drop0% Iris.UFracAuth.ord_total 3 := fun h =>
  nomatch @h OF _ _ _ 1 1 fT fT (UFracAuth.valid trivial)
-- `Iris.UFracAuth.ord_total` idx 4: necessary (A = BA: discrete, OrderRefl, not IncOrd)
theorem w2c4_106 : ¬ drop0% Iris.UFracAuth.ord_total 4 := fun h =>
  nomatch @h BA _ _ _ 1 (1 + 1) (aT • aF) aT
    (valid_iff_validN.mpr fun _ => uf_valid_frame 1 1 aT aF trivial)
-- `Iris.UFracAuth.ord_total` idx 9: necessary (A = BO)
theorem w2c4_107 : ¬ drop0% Iris.UFracAuth.ord_total 9 := fun h =>
  nomatch (@h BO _ _ _ _ 1 1 boF boT) rfl
-- `Iris.UFracAuth.included_total` idx 3: necessary (A = OF: discrete, OrdInc, not OrderRefl)
theorem w2c4_108 : ¬ drop0% Iris.UFracAuth.included_total 3 := fun h => by
  obtain ⟨c, e⟩ := @h OF _ _ _ 1 1 fT fT (UFracAuth.valid trivial)
  nomatch e
-- `Iris.UFracAuth.included_total` idx 4: necessary (A = BR: discrete, OrderRefl, not OrdInc)
theorem w2c4_109 : ¬ drop0% Iris.UFracAuth.included_total 4 := fun h => by
  obtain ⟨c, e⟩ := @h BR _ _ _ 1 (1 + 1) rF rT
    (valid_iff_validN.mpr fun _ => uf_valid_ord 1 1 rF rT trivial trivial)
  nomatch e
-- `Iris.UFracAuth.included_total` idx 9: necessary (A = BO)
theorem w2c4_110 : ¬ drop0% Iris.UFracAuth.included_total 9 := fun h => by
  obtain ⟨c, e⟩ := @h BO _ _ _ _ 1 1 boF boT
  nomatch e
-- `Iris.UFracAuth.isOp_ufrac_auth` idx 9: necessary (fractions 1 = 1 + 1 forced)
theorem w2c4_111 : ¬ drop0% Iris.UFracAuth.isOp_ufrac_auth 9 := fun h =>
  qp_ne (uf_frag_inj (@h BT _ .merge 1 1 1 bT bT (bT • bT) (isOpMerge_op bT bT)).is_op).1
-- `Iris.UFracAuth.isOp_ufrac_auth` idx 10: necessary (A = BT, a = true, a1 = a2 = false)
theorem w2c4_112 : ¬ drop0% Iris.UFracAuth.isOp_ufrac_auth 10 := fun h =>
  nomatch (uf_frag_inj (@h BT _ .merge ((1 : Qp) • 1) 1 1 bF bF bT (isOpMerge_op 1 1)).is_op).2
-- `Iris.UFracAuth.isOp_ufrac_auth_core_id` idx 7: necessary (A = NA, a = 1 not a core: 1 ≠ 1 + 1)
theorem w2c4_113 : ¬ drop0% Iris.UFracAuth.isOp_ufrac_auth_core_id 7 := fun h =>
  nomatch (uf_frag_inj (@h NA _ .merge ((1 : Qp) • 1) 1 1 ⟨1⟩ (isOpMerge_op 1 1)).is_op).2
-- `Iris.UFracAuth.isOp_ufrac_auth_core_id` idx 8: necessary (A = BO, all cores; fractions 1 = 1 + 1)
theorem w2c4_114 : ¬ drop0% Iris.UFracAuth.isOp_ufrac_auth_core_id 8 := fun h =>
  qp_ne (uf_frag_inj (@h BO _ .merge 1 1 1 boT _).is_op).1
-- `Iris.UFracAuth.update` idx 9: necessary (A = BO, OrdInc; ●F • ◯F to ●F • ◯T breaks agreement)
theorem w2c4_115 : ¬ drop0% Iris.UFracAuth.update 9 := fun h =>
  nomatch UFracAuth.agreeN (@h BO _ _ 1 1 boF boF boF boT 0 none (UFracAuth.validN trivial))
-- `Iris.UFracAuth.update_surplus` idx 6: necessary (A = EX, a = b = true, a • b invalid)
theorem w2c4_116 : ¬ drop0% Iris.UFracAuth.update_surplus 6 := fun h =>
  nomatch UFracAuth.auth_validN.mp (validN_op_left
    (@h EX _ 1 1 ⟨true⟩ ⟨true⟩ 0 none (UFracAuth.auth_validN.mpr rfl)))
-- `Iris.UFracAuth.update_surplus_cancel` idx 7: necessary (A = BO, a = false, b = true not cancelable, frame ◯U{1} true)
theorem w2c4_117 : ¬ drop0% Iris.UFracAuth.update_surplus_cancel 7 := fun h => by
  have v : ✓{0} (((●U{(1 : Qp) + 1} (boF • boT)) • ◯U{(1 : Qp)} boT) • ◯U{(1 : Qp)} boT) := by
    rw [← assoc']
    exact (UFracAuth.validN (p := (1 : Qp) + 1) (a := boT) trivial)
  exact nomatch UFracAuth.agreeN (@h BO _ _ 1 1 boF boT 0 (some (◯U{(1 : Qp)} boT)) v)

namespace W2c4
open Iris Iris.OFE Iris.ORA
/-- Elements 0 (unit-like), 1, and ≥ 2 (invalid); every product is 2; order: equality plus 0 below 1;
valid iff below 2. Not OrdInc: 0 ≼ₒ 1 but 1 is no product. -/
structure TR where v : Nat
instance : OFE TR := OFE.ofDiscrete TR
instance : OFE.Discrete TR := ⟨fun h => h⟩
def trData : DiscreteORAData TR where
  pcore _ := none
  op _ _ := ⟨2⟩
  Valid x := x.v < 2
  Order x y := x = y ∨ (x.v = 0 ∧ y.v = 1)
  assoc _ _ _ := rfl
  comm _ _ := rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ h := absurd h (by decide)
  ord_trans x y z h1 h2 := by
    rcases h2 with h2 | ⟨h2, h3⟩
    · subst h2; exact h1
    · rcases h1 with h1 | ⟨h1, h4⟩
      · subst h1; exact .inr ⟨h2, h3⟩
      · omega
  op_mono_left _ _ _ _ := .inl rfl
  valid_of_ord x y h v := by
    rcases h with h | ⟨h, _⟩
    · subst h; exact v
    · show x.v < 2; omega
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ hx _ := by
    rcases hx ⟨0⟩ with h | ⟨_, h⟩
    · nomatch h
    · nomatch h
instance trORA : ORA TR := ORA.ofDiscreteORAData trData
abbrev tr0 : TR := ⟨0⟩
abbrev tr1 : TR := ⟨1⟩
abbrev tr2 : TR := ⟨2⟩
theorem tr_lu : ((⟨1⟩ : TR), (⟨0⟩ : TR)) ~l~> (⟨2⟩, ⟨2⟩) := fun n mz _ e => by
  rcases mz with _ | z
  · nomatch e
  · nomatch e
end W2c4
open Iris Iris.OFE Iris.ORA W2c4
-- `Iris.UFracAuth.update` idx 2: necessary (A = TR not OrdInc: 0 ≼ₒ 1 but 1 is not of form 0 •? z, so the local update to the invalid 2 is vacuous)
theorem w2c4_118 : ¬ drop0% Iris.UFracAuth.update 2 := fun h => by
  have o : tr0 ≼ₒ{0} tr1 := Or.inr ⟨rfl, rfl⟩
  have va : ✓{0} tr1 := show 1 < 2 by decide
  have := @h TR _ (1 + 1) 1 tr1 tr0 tr2 tr2 tr_lu 0 none (uf_valid_ord 1 1 tr1 tr0 o va)
  have v : 2 < 2 := UFracAuth.auth_validN.mp (validN_op_left this)
  omega

namespace W2c4
open Iris Iris.OFE Iris.ORA
/-- Nat, op = +, no core, all valid, order: equality, or both at least 3. Every element is
cancelable; 4 ≼ₒ 3 although 3 ≼ₒ 2 fails and 2 is no sum 3 + w: not OrdInc. -/
structure NG where v : Nat
instance : OFE NG := OFE.ofDiscrete NG
instance : OFE.Discrete NG := ⟨fun h => h⟩
def ngData : DiscreteORAData NG where
  pcore _ := none
  op x y := ⟨x.v + y.v⟩
  Valid _ := True
  Order x y := x = y ∨ (3 ≤ x.v ∧ 3 ≤ y.v)
  assoc x y z := congrArg NG.mk (Nat.add_assoc x.v y.v z.v).symm
  comm x y := congrArg NG.mk (Nat.add_comm x.v y.v)
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans x y z h1 h2 := by
    rcases h2 with h2 | ⟨h2, h3⟩
    · subst h2; exact h1
    · rcases h1 with h1 | ⟨h1, _⟩
      · subst h1; exact .inr ⟨h2, h3⟩
      · exact .inr ⟨h1, h3⟩
  op_mono_left x y z h := by
    rcases h with h | ⟨h1, h2⟩
    · subst h; exact .inl rfl
    · exact .inr ⟨show 3 ≤ x.v + z.v by omega, show 3 ≤ y.v + z.v by omega⟩
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed x y hx h z := by
    have h0 := hx ⟨0⟩
    have hx0 : x.v = 0 := by
      rcases h0 with h0 | ⟨h0, _⟩
      · have := congrArg NG.v h0; simp at this; omega
      · simp at h0
    have hy0 : y.v = 0 := by
      rcases h with h | ⟨h, _⟩
      · subst h; exact hx0
      · omega
    exact .inl (by cases z; cases y; simp_all)
instance ngORA : ORA NG := ORA.ofDiscreteORAData ngData
abbrev ng1 : NG := ⟨1⟩
abbrev ng2 : NG := ⟨2⟩
abbrev ng3 : NG := ⟨3⟩
instance ngCanc (x : NG) : Cancelable x := ⟨fun {n y z} _ e => by
  have : x.v + y.v = x.v + z.v := congrArg NG.v (show (⟨x.v + y.v⟩ : NG) = ⟨x.v + z.v⟩ from e)
  cases y; cases z; show NG.mk _ = NG.mk _; simp only at this; congr 1; omega⟩
/-- ●U{2} 2 • ◯U{1} 3 is invalid in UFracAuth NG. -/
theorem ng_target_bad : ¬ ✓{0} ((●U{(1 : Qp) + 1} ng2) • ◯U{(1 : Qp)} ng3) := fun h => by
  obtain ⟨⟨c, hc⟩, _⟩ := Auth.both_validN_frame.mp h
  rcases c with _ | ⟨s, w⟩
  · rcases hc with hc | hc
    · have := congrArg NG.v hc.2; simp at this
    · rcases hc.2 with h2 | ⟨_, h2⟩
      · have := congrArg NG.v h2; simp at this
      · simp at h2
  · rcases hc with hc | hc
    · have : 3 + w.v = 2 := congrArg NG.v hc.2
      omega
    · rcases hc.2 with h2 | ⟨_, h2⟩
      · have : 3 + w.v = 2 := congrArg NG.v h2
        omega
      · simp at h2
end W2c4
open Iris Iris.OFE Iris.ORA W2c4
-- `Iris.UFracAuth.update_surplus_cancel` idx 2: necessary (A = NG not OrdInc, a = 2, b = 1 cancelable, p = 2, q = 1, frame ◯U{1} 3: 4 ≼ₒ 3 but 3 is not below 2)
theorem w2c4_119 : ¬ drop0% Iris.UFracAuth.update_surplus_cancel 2 := fun h => by
  have v : ✓{0} (((●U{((1 : Qp) + 1) + 1} (ng2 • ng1)) • ◯U{(1 : Qp)} ng1) • ◯U{(1 : Qp)} ng3) := by
    rw [← assoc']
    exact uf_valid_ord (n := 0) ((1 : Qp) + 1) 1 (ng2 • ng1) (ng1 • ng3)
      (Or.inr ⟨show 3 ≤ 4 by decide, show 3 ≤ 3 by decide⟩) trivial
  exact ng_target_bad (@h NG _ (1 + 1) 1 ng2 ng1 _ 0 (some (◯U{(1 : Qp)} ng3)) v)

namespace W2c4
open Iris Iris.Std
attribute [local instance] lexOrd
/-- Finite sets of pairs of naturals. -/
abbrev PS := Std.ExtTreeSet (Nat × Nat) compare
theorem ps_mem {p q : Nat × Nat} : p ∈ ({q} : PS) ↔ p = q := Std.LawfulSet.mem_singleton
theorem ps_mem_u {p : Nat × Nat} {L1 L2 : PS} : p ∈ L1 ∪ L2 ↔ p ∈ L1 ∨ p ∈ L2 := Std.LawfulSet.mem_union
/-- A singleton relation is bijective. -/
theorem bij_sg (a b : Nat) : SetBijective ({(a, b)} : PS) := fun hab => by
  rw [ps_mem] at hab
  cases hab
  exact ⟨fun b' hb' => by rw [ps_mem] at hb'; cases hb'; rfl,
         fun a' ha' => by rw [ps_mem] at ha'; cases ha'; rfl⟩
/-- A relation containing (a, b) and (a, c) with b ≠ c is not bijective. -/
theorem bij_bad1 {L : PS} {a b c : Nat} (h1 : (a, b) ∈ L) (h2 : (a, c) ∈ L) (hne : b ≠ c) :
    ¬ SetBijective L := fun h => hne ((h h2).1 b h1)
/-- A relation containing (a, c) and (b, c) with a ≠ b is not bijective. -/
theorem bij_bad2 {L : PS} {a b c : Nat} (h1 : (a, c) ∈ L) (h2 : (b, c) ∈ L) (hne : a ≠ b) :
    ¬ SetBijective L := fun h => hne ((h h2).2 a h1)
/-- The relation {(0,0), (0,1)}. -/
abbrev L01 : PS := {(0, 0)} ∪ {(0, 1)}
theorem l01_bad : ¬ SetBijective L01 :=
  bij_bad1 (ps_mem_u.mpr (.inl (ps_mem.mpr rfl))) (ps_mem_u.mpr (.inr (ps_mem.mpr rfl))) (by decide)
theorem sb_elem_bad : ¬ ✓ (SetBij.auth .discard (∅ : PS) • SetBij.elem 0 0) := fun h =>
  Std.LawfulSet.mem_empty (SetBij.auth_op_elem_valid_iff.mp h).2.2
theorem sb_auth_valid : ✓ (SetBij.auth .discard (∅ : PS) • SetBij.auth .discard ∅) := by
  rw [SetBij.auth_op_auth, DFrac.op_discard]
  exact SetBij.auth_empty_valid_iff.mpr DFrac.valid_discard
end W2c4
open Iris Iris.Std W2c4
section
attribute [local instance] lexOrd
-- `Iris.SetBijective.extend` idx 7: necessary (L = {(1,0),(1,1)}, a = 0, b = 2)
theorem w2c4_75 : ¬ drop0% Iris.SetBijective.extend 7 := fun h =>
  bij_bad1 (a := 1) (b := 0) (c := 1)
    (ps_mem_u.mpr (.inr (ps_mem_u.mpr (.inl (ps_mem.mpr rfl)))))
    (ps_mem_u.mpr (.inr (ps_mem_u.mpr (.inr (ps_mem.mpr rfl))))) (by decide)
    (@h PS Nat Nat _ 0 2 ({(1, 0)} ∪ {(1, 1)})
      (fun b' hb => by simp [ps_mem_u, ps_mem] at hb)
      (fun a' ha => by simp [ps_mem_u, ps_mem] at ha))
-- `Iris.SetBijective.extend` idx 8: necessary (L = {(0,0)}, a = 0, b = 1)
theorem w2c4_76 : ¬ drop0% Iris.SetBijective.extend 8 := fun h =>
  bij_bad1 (a := 0) (b := 1) (c := 0)
    (ps_mem_u.mpr (.inl (ps_mem.mpr rfl))) (ps_mem_u.mpr (.inr (ps_mem.mpr rfl))) (by decide)
    (@h PS Nat Nat _ 0 1 {(0, 0)} (bij_sg 0 0) (fun a' ha => by simp [ps_mem] at ha))
-- `Iris.SetBijective.extend` idx 9: necessary (L = {(0,0)}, a = 1, b = 0)
theorem w2c4_77 : ¬ drop0% Iris.SetBijective.extend 9 := fun h =>
  bij_bad2 (a := 1) (b := 0) (c := 0)
    (ps_mem_u.mpr (.inl (ps_mem.mpr rfl))) (ps_mem_u.mpr (.inr (ps_mem.mpr rfl))) (by decide)
    (@h PS Nat Nat _ 1 0 {(0, 0)} (bij_sg 0 0) (fun b' hb => by simp [ps_mem] at hb))
-- `Iris.SetBijective.eq_iff` idx 9: necessary (L = {(0,0),(0,1)})
theorem w2c4_78 : ¬ drop0% Iris.SetBijective.eq_iff 9 := fun h =>
  absurd ((@h PS Nat Nat _ 0 0 0 1 L01 (ps_mem_u.mpr (.inl (ps_mem.mpr rfl)))
    (ps_mem_u.mpr (.inr (ps_mem.mpr rfl)))).mp rfl) (by decide)
-- `Iris.SetBijective.eq_iff` idx 10: necessary (L = {(0,0)}, (a1,b1) = (0,1) not in L)
theorem w2c4_79 : ¬ drop0% Iris.SetBijective.eq_iff 10 := fun h =>
  absurd ((@h PS Nat Nat _ 0 0 1 0 {(0, 0)} (bij_sg 0 0) (ps_mem.mpr rfl)).mp rfl) (by decide)
-- `Iris.SetBijective.pair` idx 8: necessary (a1 = a2 = 0, b1 = 0, b2 = 1)
theorem w2c4_80 : ¬ drop0% Iris.SetBijective.pair 8 := fun h =>
  absurd ((@h PS Nat Nat _ 0 0 0 1).mp rfl) (by decide)
-- `Iris.SetBijective.mono` idx 6: necessary (L = L' = {(0,0),(0,1)})
theorem w2c4_81 : ¬ drop0% Iris.SetBijective.mono 6 := fun h =>
  l01_bad (@h PS Nat Nat _ L01 L01 (fun _ hx => hx))
-- `Iris.SetBijective.mono` idx 7: necessary (L = ∅, L' = {(0,0),(0,1)})
theorem w2c4_82 : ¬ drop0% Iris.SetBijective.mono 7 := fun h =>
  l01_bad (@h PS Nat Nat _ ∅ L01 SetBijective.empty)
-- `Iris.SetBij.elem_agree` idx 8: necessary (a1 = a2 = 0, b1 = 0, b2 = 1)
theorem w2c4_83 : ¬ drop0% Iris.SetBij.elem_agree 8 := fun h =>
  absurd ((@h PS Nat Nat _ 0 0 0 1).mp rfl) (by decide)
-- `Iris.SetBij.elem_ord_auth` idx 8: necessary (L = ∅, dq = discard)
theorem w2c4_84 : ¬ drop0% Iris.SetBij.elem_ord_auth 8 := fun h =>
  sb_elem_bad (ORA.valid_of_ord (ORA.op_mono_right_ord (SetBij.auth .discard (∅ : PS))
    (@h PS Nat Nat _ 0 0 ∅ .discard)) sb_auth_valid)
-- `Iris.SetBij.elem_inc_auth` idx 8: necessary (L = ∅, dq = discard)
theorem w2c4_85 : ¬ drop0% Iris.SetBij.elem_inc_auth 8 := fun h =>
  sb_elem_bad (ORA.valid_of_inc (ORA.op_mono_right (SetBij.auth .discard (∅ : PS))
    (@h PS Nat Nat _ 0 0 ∅ .discard)) sb_auth_valid)
-- `Iris.SetBij.auth_extend` idx 7: necessary (L = {(0,0)}, a = 0, b = 1)
theorem w2c4_86 : ¬ drop0% Iris.SetBij.auth_extend 7 := fun h => by
  have := @h PS Nat Nat _ 0 1 {(0, 0)} (fun a' ha => by simp [ps_mem] at ha) 0 none
    (SetBij.auth_one_valid_iff.mpr (bij_sg 0 0)).validN
  exact bij_bad1 (a := 0) (b := 1) (c := 0)
    (ps_mem_u.mpr (.inl (ps_mem.mpr rfl))) (ps_mem_u.mpr (.inr (ps_mem.mpr rfl))) (by decide)
    (SetBij.auth_one_valid_iff.mp (ORA.discrete_valid this))
-- `Iris.SetBij.auth_extend` idx 8: necessary (L = {(0,0)}, a = 1, b = 0)
theorem w2c4_87 : ¬ drop0% Iris.SetBij.auth_extend 8 := fun h => by
  have := @h PS Nat Nat _ 1 0 {(0, 0)} (fun b' hb => by simp [ps_mem] at hb) 0 none
    (SetBij.auth_one_valid_iff.mpr (bij_sg 0 0)).validN
  exact bij_bad2 (a := 1) (b := 0) (c := 0)
    (ps_mem_u.mpr (.inl (ps_mem.mpr rfl))) (ps_mem_u.mpr (.inr (ps_mem.mpr rfl))) (by decide)
    (SetBij.auth_one_valid_iff.mp (ORA.discrete_valid this))
end
