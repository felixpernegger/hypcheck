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
set_option warn.classDefReducibility false
namespace W2c0
open Iris Iris.OFE Iris.ORA

/-- Discrete ORA on Bool: op = and, no core, order = equality. Not IncOrd; false not Increasing. -/
structure BA where b : Bool
deriving DecidableEq
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
instance baRefl : OrderRefl BA := ⟨fun _ => (rfl : _ = _)⟩
theorem ba_not_inc : ¬ Increasing (⟨false⟩ : BA) := fun h => by
  have := h.increasing ⟨true⟩
  cases this

/-- Discrete ORA on Nat: x • y = x + y + 1, no core, order is strict <. IsInc, not OrderRefl, x ⋠ x. -/
structure SN where n : Nat
def snData : DiscreteORAData SN where
  pcore _ := none
  op x y := ⟨x.n + y.n + 1⟩
  Valid _ := True
  Order x y := x.n < y.n
  assoc x y z := by simp only [SN.mk.injEq]; omega
  comm x y := by simp only [SN.mk.injEq]; omega
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := Nat.lt_trans h1 h2
  op_mono_left _ _ _ h := by show _ < _; simp only; omega
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ _ z := by show _ < _; simp only; omega
instance : OFE SN := OFE.ofDiscrete SN
instance : OFE.Discrete SN := ⟨fun h => h⟩
instance snORA : ORA SN := ORA.ofDiscreteORAData snData
theorem sn_ord {x y : SN} : x ≼ₒ y ↔ x.n < y.n := Iff.rfl
theorem sn_ordN {n} {x y : SN} : x ≼ₒ{n} y ↔ x.n < y.n := Iff.rfl
theorem sn_op (x y : SN) : x • y = ⟨x.n + y.n + 1⟩ := rfl
instance snIsInc : IsInc SN where
  inc_ord := fun ⟨z, hz⟩ => by subst hz; show _ < _; simp only [sn_op]; omega
  ord_inc {x y} h := ⟨⟨y.n - x.n - 1⟩, by
    have : x.n < y.n := h
    cases x; cases y; simp only [sn_op, SN.mk.injEq] at *; omega⟩
  ordN_incN {_ x y} h := ⟨⟨y.n - x.n - 1⟩, by
    have : x.n < y.n := h
    cases x; cases y; apply OFE.Dist.of_eq; simp only [sn_op, SN.mk.injEq] at *; omega⟩
theorem sn_not_inc (x : SN) : ¬ x ≼ x := fun ⟨z, hz⟩ => by
  have := congrArg SN.n hz; simp only [sn_op] at this; omega
theorem sn_not_incN {n} (x : SN) : ¬ x ≼{n} x := fun ⟨z, hz⟩ => by
  have := congrArg SN.n (OFE.discrete hz); simp only [sn_op] at this; omega
instance snCancel (x : SN) : Cancelable x := ⟨fun {n y z} _ h => by
  have := congrArg SN.n (OFE.discrete h)
  apply OFE.Dist.of_eq; cases y; cases z; simp only [sn_op] at this; simp only [SN.mk.injEq]; omega⟩

/-- Discrete total ORA on Bool: op = or, core = id, order = implication. IsInc, IsTotal. -/
structure BT where b : Bool
deriving DecidableEq
def btData : DiscreteORAData BT where
  pcore x := some x
  op x y := ⟨x.b || y.b⟩
  Valid _ := True
  Order x y := x.b = true → y.b = true
  assoc x y z := congrArg BT.mk (Bool.or_assoc x.b y.b z.b).symm
  comm x y := congrArg BT.mk (Bool.or_comm x.b y.b)
  pcore_op_left x _ h := by cases h; cases x; simp
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := fun h => h2 (h1 h)
  op_mono_left x y z h := by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> simp_all
  valid_of_ord _ _ _ _ := trivial
  pcore_mono x y _ h e := by cases e; exact ⟨y, rfl, h⟩
  pcore_order_op x _ e y := by cases e; exact ⟨_, rfl, by intro h; simp [h]⟩
  pcore_increasing _ _ e y := by intro h; simp [h]
  increasing_closed _ _ _ _ z := by intro h; simp [h]
instance : OFE BT := OFE.ofDiscrete BT
instance : OFE.Discrete BT := ⟨fun h => h⟩
instance btORA : ORA BT := ORA.ofDiscreteORAData btData
theorem bt_op (x y : BT) : x • y = ⟨x.b || y.b⟩ := rfl
instance btTotal : IsTotal BT := ⟨fun x => ⟨x, rfl⟩⟩
instance btIsInc : IsInc BT where
  inc_ord := fun ⟨z, hz⟩ => by subst hz; intro h; simp [bt_op, h]
  ord_inc {x y} h := by
    cases x with | mk a => cases y with | mk b =>
    cases a <;> cases b
    · exact ⟨⟨false⟩, rfl⟩
    · exact ⟨⟨true⟩, rfl⟩
    · exact absurd (h rfl) (by decide)
    · exact ⟨⟨true⟩, rfl⟩
  ordN_incN {_ x y} h := by
    cases x with | mk a => cases y with | mk b =>
    cases a <;> cases b
    · exact ⟨⟨false⟩, .rfl⟩
    · exact ⟨⟨true⟩, .rfl⟩
    · exact absurd (h rfl) (by decide)
    · exact ⟨⟨true⟩, .rfl⟩
theorem bt_not_inc : ¬ (⟨true⟩ : BT) ≼ ⟨false⟩ := fun ⟨z, hz⟩ => by
  have := congrArg BT.b hz; simp [bt_op] at this
theorem bt_not_incN {n} : ¬ (⟨true⟩ : BT) ≼{n} ⟨false⟩ := fun ⟨z, hz⟩ => by
  have := congrArg BT.b (OFE.discrete hz); simp [bt_op] at this

/-- Data on Bool: op = or, core only at true, order = implication (partial core). -/
def boData : DiscreteORAData BT where
  pcore x := if x.b then some x else none
  op x y := ⟨x.b || y.b⟩
  Valid _ := True
  Order x y := x.b = true → y.b = true
  assoc x y z := congrArg BT.mk (Bool.or_assoc x.b y.b z.b).symm
  comm x y := congrArg BT.mk (Bool.or_comm x.b y.b)
  pcore_op_left x _ h := by cases x with | mk a => cases a <;> simp at h; cases h; rfl
  pcore_idem x _ h := by cases x with | mk a => cases a <;> simp at h; cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := fun h => h2 (h1 h)
  op_mono_left x y z h := by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> simp_all
  valid_of_ord _ _ _ _ := trivial
  pcore_mono x y _ h e := by
    rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> simp_all
  pcore_order_op x _ e y := by
    cases x with | mk a => cases a <;> simp at e; cases e; exact ⟨⟨true⟩, by simp, fun _ => rfl⟩
  pcore_increasing x _ e y := by
    cases x with | mk a => cases a <;> simp at e; cases e; intro _; rfl
  increasing_closed _ _ _ _ z := by intro h; simp [h]

/-- Data on Bool: op = and, validity = the bit, order = equality, no core. -/
def bvData : DiscreteORAData BA where
  pcore _ := none
  op x y := ⟨x.b && y.b⟩
  Valid x := x.b = true
  Order := Eq
  assoc x y z := congrArg BA.mk (Bool.and_assoc x.b y.b z.b).symm
  comm x y := congrArg BA.mk (Bool.and_comm x.b y.b)
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left x y h := by simp at h; exact h.1
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ h := h ▸ rfl
  valid_of_ord _ _ h v := h ▸ v
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ hx hxy := hxy ▸ hx

/-- Three elements: a, b valid, bot invalid; every product is bot; order = equality plus a ≤ b.
`a` is exclusive and below `b`, but not included in it: not OrdInc. -/
inductive T3 where | a | b | bot
deriving DecidableEq
def t3Data : DiscreteORAData T3 where
  pcore _ := none
  op _ _ := .bot
  Valid x := x ≠ .bot
  Order x y := x = y ∨ (x = .a ∧ y = .b)
  assoc _ _ _ := rfl
  comm _ _ := rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ h := absurd rfl h
  ord_trans x y z h1 h2 := by
    rcases h1 with rfl | ⟨rfl, rfl⟩ <;> rcases h2 with rfl | ⟨h, rfl⟩ <;> simp_all
  op_mono_left _ _ _ _ := .inl rfl
  valid_of_ord x y h v := by rcases h with rfl | ⟨rfl, rfl⟩ <;> simp_all
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed x _ hx _ := by
    have := hx .a; rcases this with h | ⟨_, h⟩ <;> cases h
instance : OFE T3 := OFE.ofDiscrete T3
instance : OFE.Discrete T3 := ⟨fun h => h⟩
instance t3ORA : ORA T3 := ORA.ofDiscreteORAData t3Data
instance t3Excl : Exclusive T3.a := ⟨fun _ h => absurd rfl h⟩
theorem t3_ab : T3.a ≼ₒ T3.b := .inr ⟨rfl, rfl⟩
theorem t3_vb : ✓ T3.b := fun h => nomatch h

/-- Total discrete ORA on Nat: op = +, core = 0, order = ≤. 0 is cancelable but not IdFree. -/
structure NP where n : Nat
def npData : DiscreteORAData NP where
  pcore _ := some ⟨0⟩
  op x y := ⟨x.n + y.n⟩
  Valid _ := True
  Order x y := x.n ≤ y.n
  assoc x y z := by simp only [NP.mk.injEq]; omega
  comm x y := by simp only [NP.mk.injEq]; omega
  pcore_op_left x _ h := by cases h; simp
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := Nat.le_trans h1 h2
  op_mono_left _ _ _ h := by show _ ≤ _; simp only; omega
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ e := by cases e; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_order_op _ _ e _ := by cases e; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_increasing _ _ e _ := by cases e; show _ ≤ _; simp
  increasing_closed _ _ _ _ z := by show _ ≤ _; simp
instance : OFE NP := OFE.ofDiscrete NP
instance : OFE.Discrete NP := ⟨fun h => h⟩
instance npORA : ORA NP := ORA.ofDiscreteORAData npData
theorem np_op (x y : NP) : x • y = ⟨x.n + y.n⟩ := rfl
instance npTotal : IsTotal NP := ⟨fun _ => ⟨_, rfl⟩⟩
instance npCancel0 : Cancelable (⟨0⟩ : NP) := ⟨fun {n y z} _ h => by
  have := congrArg NP.n (OFE.discrete h)
  apply OFE.Dist.of_eq; cases y; cases z; simp only [NP.mk.injEq]
  simp only [np_op] at this; omega⟩

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
theorem tn_dist {n} {x y : TN} : x ≡{n}≡ y ↔ min x.v (n+1) = min y.v (n+1) := Iff.rfl
theorem tn12 : (⟨1⟩ : TN) ≡{0}≡ ⟨2⟩ := rfl
theorem tn12ne : (⟨1⟩ : TN) ≠ ⟨2⟩ := by simp
instance tn0disc : DiscreteE (⟨0⟩ : TN) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩

/-- Discrete ORA on Nat × Bool: (a, p) • (b, q) = (a + b + 1, p && q), no core, order = equality.
Every element is IdFree, but (0, false) is not cancelable. -/
structure NB where
  n : Nat
  b : Bool
instance : OFE NB := OFE.ofDiscrete NB
instance : OFE.Discrete NB := ⟨fun h => h⟩
def nbData : DiscreteORAData NB where
  pcore _ := none
  op x y := ⟨x.n + y.n + 1, x.b && y.b⟩
  Valid _ := True
  Order := Eq
  assoc x y z := by cases x; cases y; cases z; simp [Bool.and_assoc]; try omega
  comm x y := by cases x; cases y; simp [Bool.and_comm]; try omega
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
instance nbORA : ORA NB := ORA.ofDiscreteORAData nbData
instance nbIdFree : ∀ x : NB, ORA.IdFree x := fun x => ⟨fun y _ h => by
  have : x.n + y.n + 1 = x.n := congrArg NB.n h
  omega⟩

theorem ba_tf_ordN {n} : ¬ (some (⟨true⟩ : BA)) ≼ₒ{n} some ⟨false⟩ := by
  intro h; rcases h with e | e <;> cases e
theorem ba_tf_ord : ¬ (some (⟨true⟩ : BA)) ≼ₒ some ⟨false⟩ := by
  intro h; rcases h with e | e <;> cases e
theorem bt_some_tf_incN {n} : ¬ (some (⟨true⟩ : BT)) ≼{n} some ⟨false⟩ := by
  intro h; rcases Option.some_incN_some_iff.mp h with e | e
  · cases (OFE.discrete e : (⟨true⟩ : BT) = ⟨false⟩)
  · exact bt_not_incN e
theorem bt_some_tf_inc : ¬ (some (⟨true⟩ : BT)) ≼ some ⟨false⟩ := by
  intro h; rcases Option.some_inc_some_iff.mp h with e | e
  · cases e
  · exact bt_not_inc e

end W2c0
namespace W2c0
open Iris Iris.OFE Iris.ORA

-- `Iris.Option.some_ord_some_iff_orderRefl` (hypothesis 2): necessary, SN (order <, not reflexive): a=b=0, some 0 ≼ some 0 by equality
theorem w2c0_1 : ¬ drop0% Iris.Option.some_ord_some_iff_orderRefl 2 := fun h =>
  Nat.lt_irrefl 0 ((@h SN _ ⟨0⟩ ⟨0⟩).mp (Or.inl rfl))
-- `Iris.Option.some_ordN_some_iff_orderRefl` (hypothesis 2): necessary, SN: a=b=0
theorem w2c0_2 : ¬ drop0% Iris.Option.some_ordN_some_iff_orderRefl 2 := fun h =>
  Nat.lt_irrefl 0 ((@h SN _ 0 ⟨0⟩ ⟨0⟩).mp (Or.inl (OFE.Dist.of_eq rfl)))
-- `Iris.Option.ord_iff` (hypothesis 2): necessary, BA (not IncOrd): none ≼ some false fails
theorem w2c0_3 : ¬ drop0% Iris.Option.ord_iff 2 := fun h =>
  ba_not_inc ((@h BA _ none (some ⟨false⟩)).mpr (Or.inl rfl))
-- `Iris.Option.ordN_iff` (hypothesis 2): necessary, BA: none ≼{0} some false fails
theorem w2c0_4 : ¬ drop0% Iris.Option.ordN_iff 2 := fun h =>
  ba_not_inc ((@h BA _ 0 none (some ⟨false⟩)).mpr (Or.inl rfl))
-- `Iris.Option.ord_iff_orderRefl` (hypothesis 2): necessary, BA (reflexive, not IncOrd): none ≼ some false fails
theorem w2c0_5 : ¬ drop0% Iris.Option.ord_iff_orderRefl 2 := fun h =>
  ba_not_inc ((@h BA _ _ none (some ⟨false⟩)).mpr (Or.inl rfl))
-- `Iris.Option.ord_iff_orderRefl` (hypothesis 3): necessary, SN (IsInc, not reflexive): ma=mb=some 0
theorem w2c0_6 : ¬ drop0% Iris.Option.ord_iff_orderRefl 3 := fun h => by
  rcases (@h SN _ _ (some ⟨0⟩) (some ⟨0⟩)).mp (Or.inl rfl) with e | ⟨a, b, ha, hb, hab⟩
  · cases e
  · cases ha; cases hb; exact Nat.lt_irrefl 0 hab
-- `Iris.Option.ordN_iff_orderRefl` (hypothesis 2): necessary, BA: none ≼{0} some false fails
theorem w2c0_7 : ¬ drop0% Iris.Option.ordN_iff_orderRefl 2 := fun h =>
  ba_not_inc ((@h BA _ _ 0 none (some ⟨false⟩)).mpr (Or.inl rfl))
-- `Iris.Option.ordN_iff_orderRefl` (hypothesis 3): necessary, SN: ma=mb=some 0
theorem w2c0_8 : ¬ drop0% Iris.Option.ordN_iff_orderRefl 3 := fun h => by
  rcases (@h SN _ _ 0 (some ⟨0⟩) (some ⟨0⟩)).mp (Or.inl (OFE.Dist.of_eq rfl)) with e | ⟨a, b, ha, hb, hab⟩
  · cases e
  · cases ha; cases hb; exact Nat.lt_irrefl 0 hab
-- `Iris.Option.eqv_of_ord_exclusive` (hypothesis 3): necessary, T3: a exclusive, a below b in the order, b valid, a ≠ b
theorem w2c0_9 : ¬ drop0% Iris.Option.eqv_of_ord_exclusive 3 := fun h =>
  nomatch (@h T3 _ .a _ .b (Or.inr t3_ab) t3_vb)
-- `Iris.Option.eqv_of_ord_exclusive` (hypothesis 4): necessary, BT (or): a=false ≼ b=true, false not exclusive
theorem w2c0_10 : ¬ drop0% Iris.Option.eqv_of_ord_exclusive 4 := fun h => by
  have := @h BT _ ⟨false⟩ _ ⟨true⟩ (Or.inr fun _ => rfl) trivial
  cases this
-- `Iris.Option.eqv_of_ord_exclusive` (hypothesis 7): necessary, Excl Unit: a = excl (), b = invalid
theorem w2c0_11 : ¬ drop0% Iris.Option.eqv_of_ord_exclusive 7 := fun h => by
  have := @h (Excl Unit) _ (.excl ()) _ _ .invalid (Or.inr (IncOrd.inc_ord ⟨.invalid, rfl⟩))
  cases this
-- `Iris.Option.dist_of_ord_exclusive` (hypothesis 3): necessary, T3 at n = 0
theorem w2c0_12 : ¬ drop0% Iris.Option.dist_of_ord_exclusive 3 := fun h =>
  nomatch (OFE.discrete (@h T3 _ .a _ 0 .b (Or.inr t3_ab) t3_vb) : T3.a = T3.b)
-- `Iris.Option.dist_of_ord_exclusive` (hypothesis 4): necessary, BT at n = 0: false ≼ true
theorem w2c0_13 : ¬ drop0% Iris.Option.dist_of_ord_exclusive 4 := fun h => by
  have := OFE.discrete (@h BT _ ⟨false⟩ _ 0 ⟨true⟩ (Or.inr fun _ => rfl) trivial)
  cases this
-- `Iris.Option.dist_of_ord_exclusive` (hypothesis 8): necessary, Excl Unit: a = excl (), b = invalid
theorem w2c0_14 : ¬ drop0% Iris.Option.dist_of_ord_exclusive 8 := fun h => by
  have := @h (Excl Unit) _ (.excl ()) _ _ 0 .invalid (Or.inr (IncOrd.incN_ordN ⟨.invalid, OFE.Dist.of_eq rfl⟩))
  cases this
-- `Iris.Option.map_mono_ord` (hypothesis 4): necessary, beta = BA (not IncOrd), f constant false, none ≼ some true
theorem w2c0_15 : ¬ drop0% Iris.Option.map_mono_ord 4 := fun h =>
  ba_not_inc (@h BA _ BA _ (fun _ => ⟨false⟩) none (some ⟨true⟩) (fun _ _ _ => rfl) ⟨fun _ => rfl⟩)
-- `Iris.Option.map_mono_ord` (hypothesis 8): necessary, SN, f swaps 0 and 1 (not monotone), some 0 ≼ some 1
theorem w2c0_16 : ¬ drop0% Iris.Option.map_mono_ord 8 := fun h => by
  have := @h SN _ SN _ _ (fun x => if x.n = 0 then ⟨1⟩ else ⟨0⟩) (some ⟨0⟩) (some ⟨1⟩) (Or.inr Nat.zero_lt_one)
  rcases this with e | e
  · cases e
  · exact Nat.not_lt_zero _ e
-- `Iris.Option.map_mono_ord` (hypothesis 9): necessary, SN, f = id, ma = some 0, mb = none
theorem w2c0_17 : ¬ drop0% Iris.Option.map_mono_ord 9 := fun h =>
  @h SN _ SN _ _ id (some ⟨0⟩) none (fun _ _ h => h)
-- `Iris.Option.instOrdInc` (hypothesis 2): necessary, T3 (not OrdInc): some a ≼ some b, no frame
theorem w2c0_18 : ¬ drop0% Iris.Option.instOrdInc 2 := fun h => by
  obtain ⟨z, hz⟩ := (@h T3 _).ord_inc (x := some .a) (y := some .b) (Or.inr t3_ab)
  cases z <;> cases hz
-- `Iris.Option.instIsInc` (hypothesis 2): necessary, BA: some true included in some false but not ordered
theorem w2c0_19 : ¬ drop0% Iris.Option.instIsInc 2 := fun h =>
  ba_tf_ord ((@h BA _).inc_ord (x := some ⟨true⟩) (y := some ⟨false⟩) ⟨some ⟨false⟩, rfl⟩)
-- `Iris.Option.some_ordN_some_of_dist_opM` (hypothesis 2): necessary, BA: x = false = true • false
theorem w2c0_20 : ¬ drop0% Iris.Option.some_ordN_some_of_dist_opM 2 := fun h =>
  ba_tf_ordN (@h BA _ 0 ⟨false⟩ ⟨true⟩ (some ⟨false⟩) (OFE.Dist.of_eq rfl))
-- `Iris.Option.inc_of_some_inc_some` (hypothesis 5): necessary, BT: true not included in false
theorem w2c0_21 : ¬ drop0% Iris.Option.inc_of_some_inc_some 5 := fun h =>
  bt_not_inc (@h BT _ _ ⟨false⟩ ⟨true⟩)
-- `Iris.Option.some_incN_some_iff_some` (hypothesis 2): necessary, SN (no core): x=y=0, 0 not included in 0
theorem w2c0_22 : ¬ drop0% Iris.Option.some_incN_some_iff_some 2 := fun h =>
  sn_not_incN _ (@h SN _ 0 ⟨0⟩ ⟨0⟩ ⟨none, OFE.Dist.of_eq rfl⟩)
-- `Iris.Option.some_incN_some_iff_some` (hypothesis 6): necessary, BT: y = true, x = false
theorem w2c0_23 : ¬ drop0% Iris.Option.some_incN_some_iff_some 6 := fun h =>
  bt_not_incN (@h BT _ _ 0 ⟨false⟩ ⟨true⟩)
-- `Iris.Option.inc_iff_isTotal` (hypothesis 2): necessary, SN: ma=mb=some 0
theorem w2c0_24 : ¬ drop0% Iris.Option.inc_iff_isTotal 2 := fun h => by
  rcases (@h SN _ (some ⟨0⟩) (some ⟨0⟩)).mp ⟨none, rfl⟩ with e | ⟨a, b, ha, hb, hab⟩
  · cases e
  · cases ha; cases hb; exact sn_not_inc _ hab
-- `Iris.Option.incN_iff_is_total` (hypothesis 2): necessary, SN: ma=mb=some 0
theorem w2c0_25 : ¬ drop0% Iris.Option.incN_iff_is_total 2 := fun h => by
  rcases (@h SN _ 0 (some ⟨0⟩) (some ⟨0⟩)).mp ⟨none, OFE.Dist.of_eq rfl⟩ with e | ⟨a, b, ha, hb, hab⟩
  · cases e
  · cases ha; cases hb; exact sn_not_incN _ hab
-- `Iris.Option.eqv_of_inc_exclusive` (hypothesis 3): necessary, BT: some false ≼ some true
theorem w2c0_26 : ¬ drop0% Iris.Option.eqv_of_inc_exclusive 3 := fun h => by
  have := @h BT _ ⟨false⟩ ⟨true⟩ ⟨some ⟨true⟩, rfl⟩ trivial
  cases this
-- `Iris.Option.eqv_of_inc_exclusive` (hypothesis 6): necessary, Excl Unit: a = excl (), b = invalid
theorem w2c0_27 : ¬ drop0% Iris.Option.eqv_of_inc_exclusive 6 := fun h => by
  have := @h (Excl Unit) _ (.excl ()) _ .invalid ⟨some .invalid, rfl⟩
  cases this
-- `Iris.Option.dist_of_inc_exclusive` (hypothesis 3): necessary, BT: some false ≼{0} some true
theorem w2c0_28 : ¬ drop0% Iris.Option.dist_of_inc_exclusive 3 := fun h => by
  have := OFE.discrete (@h BT _ ⟨false⟩ 0 ⟨true⟩ ⟨some ⟨true⟩, OFE.Dist.of_eq rfl⟩ trivial)
  cases this
-- `Iris.Option.dist_of_inc_exclusive` (hypothesis 7): necessary, Excl Unit: a = excl (), b = invalid
theorem w2c0_29 : ¬ drop0% Iris.Option.dist_of_inc_exclusive 7 := fun h => by
  have := @h (Excl Unit) _ (.excl ()) _ 0 .invalid ⟨some .invalid, OFE.Dist.of_eq rfl⟩
  cases this
-- `Iris.Option.some_inc_some_iff_is_total` (hypothesis 2): necessary, SN: a=b=0
theorem w2c0_30 : ¬ drop0% Iris.Option.some_inc_some_iff_is_total 2 := fun h =>
  sn_not_inc _ ((@h SN _ ⟨0⟩ ⟨0⟩).mp ⟨none, rfl⟩)
-- `Iris.Option.map_mono` (hypothesis 7): necessary, BT, f = not, some false ≼ some true
theorem w2c0_31 : ¬ drop0% Iris.Option.map_mono 7 := fun h =>
  bt_some_tf_inc (@h BT _ BT _ (fun x => ⟨!x.b⟩) (some ⟨false⟩) (some ⟨true⟩) ⟨some ⟨true⟩, rfl⟩)
-- `Iris.Option.map_mono` (hypothesis 8): necessary, BT, f = id, ma = some true, mb = none
theorem w2c0_32 : ¬ drop0% Iris.Option.map_mono 8 := fun h => by
  obtain ⟨z, hz⟩ := @h BT _ BT _ id (some ⟨true⟩) none (fun _ _ h => h)
  cases z <;> cases hz
-- `Iris.Option.some_incN_some_iff_is_total` (hypothesis 2): necessary, SN: a=b=0
theorem w2c0_33 : ¬ drop0% Iris.Option.some_incN_some_iff_is_total 2 := fun h =>
  sn_not_incN _ ((@h SN _ 0 ⟨0⟩ ⟨0⟩).mp ⟨none, OFE.Dist.of_eq rfl⟩)
-- `Iris.Option.instCancelableOptionSomeOfIdFree` (hypothesis 3): necessary, NP (+): 0 cancelable, some 0 • none = some 0 • some 0
theorem w2c0_34 : ¬ drop0% Iris.Option.instCancelableOptionSomeOfIdFree 3 := fun h => by
  have := (@h NP _ ⟨0⟩ _).cancelableN (n := 0) (y := none) (z := some ⟨0⟩) trivial (OFE.Dist.of_eq rfl)
  cases this
-- `Iris.Option.instCancelableOptionSomeOfIdFree` (hypothesis 4): necessary, NB: (0,false) IdFree, not cancelable
theorem w2c0_35 : ¬ drop0% Iris.Option.instCancelableOptionSomeOfIdFree 4 := fun h => by
  have := (@h NB _ ⟨0, false⟩ (nbIdFree _)).cancelableN (n := 0) (y := some ⟨0, true⟩) (z := some ⟨0, false⟩) trivial (OFE.Dist.of_eq rfl)
  cases (OFE.discrete this : some (⟨0, true⟩ : NB) = some ⟨0, false⟩)
-- `Iris.Option.instDiscreteOption` (hypothesis 2): necessary, Excl TN (non-discrete OFE)
theorem w2c0_36 : ¬ drop0% Iris.Option.instDiscreteOption 2 := fun h =>
  tn12ne (Excl.excl.inj (Option.some.inj ((@h (Excl TN) _).discrete_0 (x := some (.excl ⟨1⟩)) (y := some (.excl ⟨2⟩)) tn12)))

end W2c0
namespace W2c0
open Iris Iris.OFE Iris.ORA

-- `Iris.Prod.mk_core` (hypothesis 4): necessary, alpha = BA (no core), beta = NP (core 0): core (true, 1) = (true, 1) ≠ (true, 0)
theorem w2c0_37 : ¬ drop0% Iris.Prod.mk_core 4 := fun h => by
  have := congrArg (fun p => p.2.n) (@h BA NP _ _ _ ⟨true⟩ ⟨1⟩)
  exact absurd this (by decide)
-- `Iris.Prod.mk_core` (hypothesis 5): necessary, alpha = NP, beta = BA
theorem w2c0_38 : ¬ drop0% Iris.Prod.mk_core 5 := fun h => by
  have := congrArg (fun p => p.1.n) (@h NP BA _ _ _ ⟨1⟩ ⟨true⟩)
  exact absurd this (by decide)
-- `Iris.Prod.instIsTotalProd` (hypothesis 4): necessary, alpha = BA (no core), beta = NP
theorem w2c0_39 : ¬ drop0% Iris.Prod.instIsTotalProd 4 := fun h => by
  obtain ⟨cx, hcx⟩ := (@h BA NP _ _ _).total (⟨true⟩, ⟨0⟩)
  cases hcx
-- `Iris.Prod.instIsTotalProd` (hypothesis 5): necessary, alpha = NP, beta = BA
theorem w2c0_40 : ¬ drop0% Iris.Prod.instIsTotalProd 5 := fun h => by
  obtain ⟨cx, hcx⟩ := (@h NP BA _ _ _).total (⟨0⟩, ⟨true⟩)
  cases hcx
-- `Iris.Prod.instCmraDiscreteProd` (hypothesis 4): necessary, alpha = Excl TN (not discrete), beta = BA
theorem w2c0_41 : ¬ drop0% Iris.Prod.instCmraDiscreteProd 4 := fun h =>
  tn12ne (Excl.excl.inj (congrArg Prod.fst ((@h (Excl TN) BA _ _ (ORA.ofDiscreteORAData_discrete baData)).discrete_0
    (x := (.excl ⟨1⟩, ⟨true⟩)) (y := (.excl ⟨2⟩, ⟨true⟩)) (dist_prod_ext tn12 .rfl))))
-- `Iris.Prod.instCmraDiscreteProd` (hypothesis 5): necessary, alpha = BA, beta = Excl TN
theorem w2c0_42 : ¬ drop0% Iris.Prod.instCmraDiscreteProd 5 := fun h =>
  tn12ne (Excl.excl.inj (congrArg Prod.snd ((@h BA (Excl TN) _ _ (ORA.ofDiscreteORAData_discrete baData)).discrete_0
    (x := (⟨true⟩, .excl ⟨1⟩)) (y := (⟨true⟩, .excl ⟨2⟩)) (dist_prod_ext .rfl tn12))))
-- `Iris.Prod.instOrderRefl` (hypothesis 4): necessary, alpha = SN (order <), beta = BA
theorem w2c0_43 : ¬ drop0% Iris.Prod.instOrderRefl 4 := fun h =>
  Nat.lt_irrefl 0 ((@h SN BA _ _ baRefl).ord_refl (⟨0⟩, ⟨true⟩)).1
-- `Iris.Prod.instOrderRefl` (hypothesis 5): necessary, alpha = BA, beta = SN
theorem w2c0_44 : ¬ drop0% Iris.Prod.instOrderRefl 5 := fun h =>
  Nat.lt_irrefl 0 ((@h BA SN _ _ baRefl).ord_refl (⟨true⟩, ⟨0⟩)).2
-- `Iris.Prod.instIncOrd` (hypothesis 4): necessary, alpha = BA (not IncOrd), beta = SN: (true,0) included in (false,1)
theorem w2c0_45 : ¬ drop0% Iris.Prod.instIncOrd 4 := fun h => by
  have := (@h BA SN _ _ _).inc_ord (x := (⟨true⟩, ⟨0⟩)) (y := (⟨false⟩, ⟨1⟩)) ⟨(⟨false⟩, ⟨0⟩), rfl⟩
  cases this.1
-- `Iris.Prod.instOrdInc` (hypothesis 4): necessary, alpha = T3 (not OrdInc), beta = BT
theorem w2c0_46 : ¬ drop0% Iris.Prod.instOrdInc 4 := fun h => by
  obtain ⟨z, hz⟩ := (@h T3 BT _ _ _).ord_inc (x := (.a, ⟨true⟩)) (y := (.b, ⟨true⟩)) ⟨t3_ab, fun _ => rfl⟩
  cases congrArg Prod.fst hz
-- `Iris.Prod.instOrdInc` (hypothesis 5): necessary, alpha = BT, beta = T3
theorem w2c0_47 : ¬ drop0% Iris.Prod.instOrdInc 5 := fun h => by
  obtain ⟨z, hz⟩ := (@h BT T3 _ _ _).ord_inc (x := (⟨true⟩, .a)) (y := (⟨true⟩, .b)) ⟨fun _ => rfl, t3_ab⟩
  cases congrArg Prod.snd hz
-- `Iris.Prod.instIsInc` (hypothesis 5): necessary, alpha = SN, beta = BA (not IncOrd)
theorem w2c0_48 : ¬ drop0% Iris.Prod.instIsInc 5 := fun h => by
  have := (@h SN BA _ _ _).inc_ord (x := (⟨0⟩, ⟨true⟩)) (y := (⟨1⟩, ⟨false⟩)) ⟨(⟨0⟩, ⟨false⟩), rfl⟩
  cases this.2
-- `Iris.Prod.instExclusivePairLeft` (hypothesis 5): necessary, BT × BT, everything valid: (false,false) not exclusive
theorem w2c0_49 : ¬ drop0% Iris.Prod.instExclusivePairLeft 5 := fun h =>
  (@h BT BT _ _ ⟨false⟩ ⟨false⟩).exclusive0_l (⟨false⟩, ⟨false⟩) ⟨trivial, trivial⟩
-- `Iris.Prod.instExclusivePairRight` (hypothesis 6): necessary, BT × BT
theorem w2c0_50 : ¬ drop0% Iris.Prod.instExclusivePairRight 6 := fun h =>
  (@h BT BT _ _ ⟨false⟩ ⟨false⟩).exclusive0_l (⟨false⟩, ⟨false⟩) ⟨trivial, trivial⟩
-- `Iris.Prod.instCancelablePair` (hypothesis 6): necessary, alpha = BT (true not cancelable), beta = SN
theorem w2c0_51 : ¬ drop0% Iris.Prod.instCancelablePair 6 := fun h => by
  have := (@h BT SN _ _ ⟨true⟩ ⟨0⟩ (snCancel _)).cancelableN (n := 0) (y := (⟨false⟩, ⟨0⟩)) (z := (⟨true⟩, ⟨0⟩))
    ⟨trivial, trivial⟩ (OFE.Dist.of_eq rfl)
  cases (OFE.discrete this : ((⟨false⟩, ⟨0⟩) : BT × SN) = (⟨true⟩, ⟨0⟩))
-- `Iris.Prod.instCancelablePair` (hypothesis 7): necessary, alpha = SN, beta = BT
theorem w2c0_52 : ¬ drop0% Iris.Prod.instCancelablePair 7 := fun h => by
  have := (@h SN BT _ _ ⟨0⟩ ⟨true⟩ (snCancel _)).cancelableN (n := 0) (y := (⟨0⟩, ⟨false⟩)) (z := (⟨0⟩, ⟨true⟩))
    ⟨trivial, trivial⟩ (OFE.Dist.of_eq rfl)
  cases (OFE.discrete this : ((⟨0⟩, ⟨false⟩) : SN × BT) = (⟨0⟩, ⟨true⟩))
-- `Iris.Prod.instIdFreePairLeft` (hypothesis 5): necessary, BT × BT: (false,false) • (false,false) = (false,false)
theorem w2c0_53 : ¬ drop0% Iris.Prod.instIdFreePairLeft 5 := fun h =>
  (@h BT BT _ _ ⟨false⟩ ⟨false⟩).id_free0_r (⟨false⟩, ⟨false⟩) ⟨trivial, trivial⟩ (OFE.Dist.of_eq rfl)
-- `Iris.Prod.instIdFreePairRight` (hypothesis 6): necessary, BT × BT
theorem w2c0_54 : ¬ drop0% Iris.Prod.instIdFreePairRight 6 := fun h =>
  (@h BT BT _ _ ⟨false⟩ ⟨false⟩).id_free0_r (⟨false⟩, ⟨false⟩) ⟨trivial, trivial⟩ (OFE.Dist.of_eq rfl)
-- `Iris.Option.some_mk_ordN_left` (hypothesis 9): necessary, BA: a1 = true, a2 = false
theorem w2c0_55 : ¬ drop0% Iris.Option.some_mk_ordN_left 9 := fun h =>
  ba_tf_ordN (@h BA BA _ _ 0 ⟨true⟩ ⟨false⟩ ⟨true⟩ ⟨true⟩)
-- `Iris.Option.some_mk_ordN_right` (hypothesis 9): necessary, BA: b1 = true, b2 = false
theorem w2c0_56 : ¬ drop0% Iris.Option.some_mk_ordN_right 9 := fun h =>
  ba_tf_ordN (@h BA BA _ _ 0 ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨false⟩)
-- `Iris.Option.some_mk_ord_left` (hypothesis 8): necessary, BA: a1 = true, a2 = false
theorem w2c0_57 : ¬ drop0% Iris.Option.some_mk_ord_left 8 := fun h =>
  ba_tf_ord (@h BA BA _ _ ⟨true⟩ ⟨false⟩ ⟨true⟩ ⟨true⟩)
-- `Iris.Option.some_mk_ord_right` (hypothesis 8): necessary, BA: b1 = true, b2 = false
theorem w2c0_58 : ¬ drop0% Iris.Option.some_mk_ord_right 8 := fun h =>
  ba_tf_ord (@h BA BA _ _ ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨false⟩)
-- `Iris.Option.some_mk_incN_left` (hypothesis 9): necessary, BT: a1 = true, a2 = false
theorem w2c0_59 : ¬ drop0% Iris.Option.some_mk_incN_left 9 := fun h =>
  bt_some_tf_incN (@h BT BT _ _ 0 ⟨true⟩ ⟨false⟩ ⟨true⟩ ⟨true⟩)
-- `Iris.Option.some_mk_incN_right` (hypothesis 9): necessary, BT: b1 = true, b2 = false
theorem w2c0_60 : ¬ drop0% Iris.Option.some_mk_incN_right 9 := fun h =>
  bt_some_tf_incN (@h BT BT _ _ 0 ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨false⟩)
-- `Iris.Option.some_mk_inc_left` (hypothesis 8): necessary, BT: a1 = true, a2 = false
theorem w2c0_61 : ¬ drop0% Iris.Option.some_mk_inc_left 8 := fun h =>
  bt_some_tf_inc (@h BT BT _ _ ⟨true⟩ ⟨false⟩ ⟨true⟩ ⟨true⟩)
-- `Iris.Option.some_mk_inc_right` (hypothesis 8): necessary, BT: b1 = true, b2 = false
theorem w2c0_62 : ¬ drop0% Iris.Option.some_mk_inc_right 8 := fun h =>
  bt_some_tf_inc (@h BT BT _ _ ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨false⟩)
-- `Iris.Option.some_mk_incN_total_fst` (hypothesis 4): necessary, alpha = SN (no core): a1 = a2 = 0
theorem w2c0_63 : ¬ drop0% Iris.Option.some_mk_incN_total_fst 4 := fun h =>
  sn_not_incN _ (@h SN BT _ _ 0 ⟨0⟩ ⟨0⟩ ⟨false⟩ ⟨false⟩ ⟨none, OFE.Dist.of_eq rfl⟩).1
-- `Iris.Option.some_mk_incN_total_fst` (hypothesis 10): necessary, BT: a1 = true, a2 = false
theorem w2c0_64 : ¬ drop0% Iris.Option.some_mk_incN_total_fst 10 := fun h =>
  bt_not_incN (@h BT BT _ _ _ 0 ⟨true⟩ ⟨false⟩ ⟨false⟩ ⟨false⟩).1
-- `Iris.Option.some_mk_incN_total_snd` (hypothesis 4): necessary, beta = SN: b1 = b2 = 0
theorem w2c0_65 : ¬ drop0% Iris.Option.some_mk_incN_total_snd 4 := fun h =>
  sn_not_incN _ (@h BT SN _ _ 0 ⟨false⟩ ⟨false⟩ ⟨0⟩ ⟨0⟩ ⟨none, OFE.Dist.of_eq rfl⟩).2
-- `Iris.Option.some_mk_incN_total_snd` (hypothesis 10): necessary, BT: b1 = true, b2 = false
theorem w2c0_66 : ¬ drop0% Iris.Option.some_mk_incN_total_snd 10 := fun h =>
  bt_not_incN (@h BT BT _ _ _ 0 ⟨false⟩ ⟨false⟩ ⟨true⟩ ⟨false⟩).2
-- `Iris.Option.some_mk_inc_total_fst` (hypothesis 4): necessary, alpha = SN: a1 = a2 = 0
theorem w2c0_67 : ¬ drop0% Iris.Option.some_mk_inc_total_fst 4 := fun h =>
  sn_not_inc _ (@h SN BT _ _ ⟨0⟩ ⟨0⟩ ⟨false⟩ ⟨false⟩ ⟨none, rfl⟩).1
-- `Iris.Option.some_mk_inc_total_fst` (hypothesis 9): necessary, BT: a1 = true, a2 = false
theorem w2c0_68 : ¬ drop0% Iris.Option.some_mk_inc_total_fst 9 := fun h =>
  bt_not_inc (@h BT BT _ _ _ ⟨true⟩ ⟨false⟩ ⟨false⟩ ⟨false⟩).1
-- `Iris.Option.some_mk_inc_total_snd` (hypothesis 4): necessary, beta = SN: b1 = b2 = 0
theorem w2c0_69 : ¬ drop0% Iris.Option.some_mk_inc_total_snd 4 := fun h =>
  sn_not_inc _ (@h BT SN _ _ ⟨false⟩ ⟨false⟩ ⟨0⟩ ⟨0⟩ ⟨none, rfl⟩).2
-- `Iris.Option.some_mk_inc_total_snd` (hypothesis 9): necessary, BT: b1 = true, b2 = false
theorem w2c0_70 : ¬ drop0% Iris.Option.some_mk_inc_total_snd 9 := fun h =>
  bt_not_inc (@h BT BT _ _ _ ⟨false⟩ ⟨false⟩ ⟨true⟩ ⟨false⟩).2
-- `Iris.instRFunctorAffineProdOF` (hypothesis 4): necessary, F1 = constOF BA (not IncOrd), F2 = constOF SN
theorem w2c0_71 : ¬ drop0% Iris.instRFunctorAffineProdOF 4 := fun h => by
  have := (@(@h (constOF BA) (constOF SN) _ _ _).affine Unit Unit _ _).inc_ord
    (x := ((⟨true⟩, ⟨0⟩) : BA × SN)) (y := (⟨false⟩, ⟨1⟩)) ⟨(⟨false⟩, ⟨0⟩), rfl⟩
  cases this.1
-- `Iris.instRFunctorAffineProdOF` (hypothesis 5): necessary, F1 = constOF SN, F2 = constOF BA
theorem w2c0_72 : ¬ drop0% Iris.instRFunctorAffineProdOF 5 := fun h => by
  have := (@(@h (constOF SN) (constOF BA) _ _ _).affine Unit Unit _ _).inc_ord
    (x := ((⟨0⟩, ⟨true⟩) : SN × BA)) (y := (⟨1⟩, ⟨false⟩)) ⟨(⟨0⟩, ⟨false⟩), rfl⟩
  cases this.2
-- `Iris.instRFunctorAffineOptionOF` (hypothesis 2): necessary, F = constOF BA: some true included in some false, not ordered
theorem w2c0_73 : ¬ drop0% Iris.instRFunctorAffineOptionOF 2 := fun h =>
  ba_tf_ord ((@(@h (constOF BA) _).affine Unit Unit _ _).inc_ord
    (x := (some ⟨true⟩ : Option BA)) (y := some ⟨false⟩) ⟨some ⟨false⟩, rfl⟩)

end W2c0
namespace W2c0
open Iris Iris.OFE Iris.ORA

/-- Discrete OFE on Nat (fresh structure, Dist = Eq). -/
structure DN where n : Nat
deriving DecidableEq
instance : OFE DN := OFE.ofDiscrete DN
instance : OFE.Discrete DN := ⟨fun h => h⟩
instance : IsCOFE BA := ⟨fun c => c 0, fun {n c} => (c.cauchy (Nat.zero_le n)).symm⟩

-- `Iris.CMRA.ofDiscrete_discrete` (hypothesis 2): necessary, TN (not discrete) with constant op, no core, all valid
theorem w2c0_74 : ¬ indep0% Iris.CMRA.ofDiscrete_discrete 2 := fun h =>
  tn12ne ((@h TN _ (fun _ => none) (fun _ _ => ⟨0⟩) (fun _ => True) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ => trivial) (fun _ _ h => nomatch h)).discrete_0 tn12)
-- `Iris.CMRA.ofDiscrete_discrete` (hypothesis 6): necessary, DN, op x y = x*y+1 (commutative, not associative), no core
theorem w2c0_75 : ¬ indep0% Iris.CMRA.ofDiscrete_discrete 6 := fun h => by
  have := @h DN _ _ (fun _ => none) (fun x y => ⟨x.n * y.n + 1⟩) (fun _ => True)
    (fun x y => by simp only [DN.mk.injEq]; rw [Nat.mul_comm])
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ => trivial) (fun _ _ h => nomatch h) ⟨0⟩ ⟨0⟩ ⟨1⟩
  exact absurd this (by decide)
-- `Iris.CMRA.ofDiscrete_discrete` (hypothesis 7): necessary, DN, op x y = x (associative, not commutative), no core
theorem w2c0_76 : ¬ indep0% Iris.CMRA.ofDiscrete_discrete 7 := fun h => by
  have := @h DN _ _ (fun _ => none) (fun x _ => x) (fun _ => True) (fun _ _ _ => rfl)
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ => trivial) (fun _ _ h => nomatch h) ⟨0⟩ ⟨1⟩
  exact absurd this (by decide)
-- `Iris.CMRA.ofDiscrete_discrete` (hypothesis 8): necessary, DN, op = max, core constantly 1: max 1 0 ≠ 0
theorem w2c0_77 : ¬ indep0% Iris.CMRA.ofDiscrete_discrete 8 := fun h => by
  have := @h DN _ _ (fun _ => some ⟨1⟩) (fun x y => ⟨max x.n y.n⟩) (fun _ => True)
    (fun x y z => by simp only [DN.mk.injEq]; omega) (fun x y => by simp only [DN.mk.injEq]; omega)
    (fun _ _ e => by cases e; rfl) (fun _ _ _ => trivial)
    (fun _ _ e y => by cases e; exact ⟨⟨1⟩, rfl⟩) ⟨0⟩ ⟨1⟩ rfl
  exact absurd this (by decide)
-- `Iris.CMRA.ofDiscrete_discrete` (hypothesis 9): necessary, DN, op = max, core x = x - 1: core of 1 is 0, not 1
theorem w2c0_78 : ¬ indep0% Iris.CMRA.ofDiscrete_discrete 9 := fun h => by
  have := @h DN _ _ (fun x => some ⟨x.n - 1⟩) (fun x y => ⟨max x.n y.n⟩) (fun _ => True)
    (fun x y z => by simp only [DN.mk.injEq]; omega) (fun x y => by simp only [DN.mk.injEq]; omega)
    (fun x _ e => by cases e; cases x; simp only [DN.mk.injEq]; omega) (fun _ _ _ => trivial)
    (fun x _ e y => by cases e; exact ⟨⟨y.n - 1⟩, by simp only [Option.some.injEq, DN.mk.injEq]; omega⟩) ⟨2⟩ ⟨1⟩ rfl
  exact absurd this (by decide)
-- `Iris.CMRA.ofDiscrete_discrete` (hypothesis 10): necessary, DN, op = +, valid iff = 1: 0 + 1 valid, 0 not
theorem w2c0_79 : ¬ indep0% Iris.CMRA.ofDiscrete_discrete 10 := fun h => by
  have := @h DN _ _ (fun _ => none) (fun x y => ⟨x.n + y.n⟩) (fun x => x.n = 1)
    (fun x y z => by simp only [DN.mk.injEq]; omega) (fun x y => by simp only [DN.mk.injEq]; omega)
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) ⟨0⟩ ⟨1⟩ rfl
  exact absurd this (by decide)
-- `Iris.CMRA.ofDiscrete_discrete` (hypothesis 11): necessary, DN, op = max, core only at 0: max 0 1 = 1 has no core
theorem w2c0_80 : ¬ indep0% Iris.CMRA.ofDiscrete_discrete 11 := fun h => by
  have := @h DN _ _ (fun x => if x.n = 0 then some x else none) (fun x y => ⟨max x.n y.n⟩) (fun _ => True)
    (fun x y z => by simp only [DN.mk.injEq]; omega) (fun x y => by simp only [DN.mk.injEq]; omega)
    (fun x _ e => by
      by_cases h0 : x.n = 0
      · simp only [h0, ite_true, Option.some.injEq] at e; subst e; cases x; simp at h0; subst h0; rfl
      · simp only [h0, ite_false] at e; cases e)
    (fun x _ e => by
      by_cases h0 : x.n = 0
      · simp only [h0, ite_true, Option.some.injEq] at e; subst e; simp [h0]
      · simp only [h0, ite_false] at e; cases e)
    (fun _ _ _ => trivial) ⟨0⟩ ⟨0⟩ rfl ⟨1⟩
  obtain ⟨cy, hcy⟩ := this
  exact absurd hcy (by simp)
/-- Discrete-ORA data on the non-discrete TN: constant op, order Eq, no core. -/
def tnData : DiscreteORAData TN where
  pcore _ := none
  op _ _ := ⟨0⟩
  Valid _ := True
  Order := Eq
  assoc _ _ _ := rfl
  comm _ _ := rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ _ := rfl
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ hx _ := hx
-- `Iris.ORA.ofDiscreteORAData_discrete` (hypothesis 2): necessary, TN (not discrete) with constant op, order Eq, no core
theorem w2c0_81 : ¬ indep0% Iris.ORA.ofDiscreteORAData_discrete 2 := fun h =>
  tn12ne ((@h TN _ tnData).discrete_0 tn12)
-- `Iris.DiscreteORAData.pcore_op_left` (hypothesis 4): necessary, BT data (core = id, op = or): cx = true, x = false
theorem w2c0_82 : ¬ drop0% Iris.DiscreteORAData.pcore_op_left 4 := fun h =>
  absurd (@h BT btData ⟨false⟩ ⟨true⟩) (by decide)
-- `Iris.DiscreteORAData.pcore_idem` (hypothesis 4): necessary, BA data (no core)
theorem w2c0_83 : ¬ drop0% Iris.DiscreteORAData.pcore_idem 4 := fun h =>
  absurd (@h BA baData ⟨true⟩ ⟨true⟩) (by decide)
-- `Iris.DiscreteORAData.valid_op_left` (hypothesis 4): necessary, bvData (valid = the bit): x = false
theorem w2c0_84 : ¬ drop0% Iris.DiscreteORAData.valid_op_left 4 := fun h =>
  Bool.false_ne_true (@h BA bvData ⟨false⟩ ⟨true⟩)
-- `Iris.DiscreteORAData.ord_trans` (hypothesis 5): necessary, BA data (order Eq): x = true, y = z = false
theorem w2c0_85 : ¬ drop0% Iris.DiscreteORAData.ord_trans 5 := fun h =>
  nomatch (@h BA baData ⟨true⟩ ⟨false⟩ ⟨false⟩ rfl : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.DiscreteORAData.ord_trans` (hypothesis 6): necessary, BA data: x = y = false, z = true
theorem w2c0_86 : ¬ drop0% Iris.DiscreteORAData.ord_trans 6 := fun h =>
  nomatch (@h BA baData ⟨false⟩ ⟨false⟩ ⟨true⟩ rfl : (⟨false⟩ : BA) = ⟨true⟩)
-- `Iris.DiscreteORAData.op_mono_left` (hypothesis 5): necessary, BA data: x = true, y = false, z = true
theorem w2c0_87 : ¬ drop0% Iris.DiscreteORAData.op_mono_left 5 := fun h =>
  nomatch (@h BA baData ⟨true⟩ ⟨false⟩ ⟨true⟩ : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.DiscreteORAData.valid_of_ord` (hypothesis 4): necessary, bvData: x = false, y = true
theorem w2c0_88 : ¬ drop0% Iris.DiscreteORAData.valid_of_ord 4 := fun h =>
  Bool.false_ne_true (@h BA bvData ⟨false⟩ ⟨true⟩ rfl)
-- `Iris.DiscreteORAData.valid_of_ord` (hypothesis 5): necessary, bvData: x = y = false
theorem w2c0_89 : ¬ drop0% Iris.DiscreteORAData.valid_of_ord 5 := fun h =>
  Bool.false_ne_true (@h BA bvData ⟨false⟩ ⟨false⟩ rfl)
-- `Iris.DiscreteORAData.pcore_mono` (hypothesis 5): necessary, boData (core only at true): x = true, y = false
theorem w2c0_90 : ¬ drop0% Iris.DiscreteORAData.pcore_mono 5 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h BT boData ⟨true⟩ ⟨false⟩ ⟨true⟩ rfl
  cases hcy
-- `Iris.DiscreteORAData.pcore_mono` (hypothesis 6): necessary, BA data (no core)
theorem w2c0_91 : ¬ drop0% Iris.DiscreteORAData.pcore_mono 6 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h BA baData ⟨true⟩ ⟨true⟩ ⟨true⟩ rfl
  cases hcy
-- `Iris.DiscreteORAData.pcore_order_op` (hypothesis 4): necessary, BA data (no core)
theorem w2c0_92 : ¬ drop0% Iris.DiscreteORAData.pcore_order_op 4 := fun h => by
  obtain ⟨c, hc, -⟩ := @h BA baData ⟨true⟩ ⟨true⟩ ⟨true⟩
  cases hc
-- `Iris.DiscreteORAData.pcore_increasing` (hypothesis 4): necessary, BA data: cx = false, y = true
theorem w2c0_93 : ¬ drop0% Iris.DiscreteORAData.pcore_increasing 4 := fun h =>
  nomatch (@h BA baData ⟨true⟩ ⟨false⟩ ⟨true⟩ : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.DiscreteORAData.increasing_closed` (hypothesis 4): necessary, BA data: x = y = false, z = true
theorem w2c0_94 : ¬ drop0% Iris.DiscreteORAData.increasing_closed 4 := fun h =>
  nomatch (@h BA baData ⟨false⟩ ⟨false⟩ rfl ⟨true⟩ : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.DiscreteORAData.increasing_closed` (hypothesis 5): necessary, BA data: x = true increasing, y = false, z = true
theorem w2c0_95 : ¬ drop0% Iris.DiscreteORAData.increasing_closed 5 := fun h =>
  nomatch (@h BA baData ⟨true⟩ ⟨false⟩ (fun _ => rfl) ⟨true⟩ : (⟨true⟩ : BA) = ⟨false⟩)

end W2c0
namespace W2c0
open Iris Iris.OFE Iris.ORA

instance : Inhabited BA := ⟨⟨true⟩⟩
/-- Two distinct towers of the solver for the constant functor `constOF BA` (level 0 is Unit, every later level is BA). -/
def twr (b : Bool) : COFE.OFunctor.Fix.Impl.Tower (constOF BA) where
  val k := match k with | 0 => ⟨()⟩ | _ + 1 => (⟨b⟩ : BA)
  down {k} := by cases k <;> rfl

-- `Iris.COFE.OFunctor.Fix.Impl.Tower.ext` (hypothesis 6): necessary, F = constOF BA: the towers with value true / false differ
theorem w2c0_96 : ¬ drop0% Iris.COFE.OFunctor.Fix.Impl.Tower.ext 6 := fun h => by
  have := congrArg (fun t => (t.val 1 : BA)) (@h (constOF BA) _ _ _ (twr true) (twr false))
  cases this
-- `Iris.COFE.OFunctor.Fix.Impl.eqToHom_up` (hypothesis 7): necessary, F = constOF BA, k = 0, k' = 1
theorem w2c0_97 : ¬ indep0% Iris.COFE.OFunctor.Fix.Impl.eqToHom_up 7 := fun h =>
  absurd (@h (constOF BA) _ _ _ 0 1 ⟨()⟩) (by decide)
-- `Iris.COFE.OFunctor.Fix.Impl.down_eqToHom` (hypothesis 7): necessary, F = constOF BA, k = 0, k' = 1
theorem w2c0_98 : ¬ indep0% Iris.COFE.OFunctor.Fix.Impl.down_eqToHom 7 := fun h =>
  absurd (@h (constOF BA) _ _ _ 0 1 (⟨true⟩ : BA)) (by decide)

/-- Constant chains on BA. -/
abbrev cb (b : Bool) : Chain BA := Chain.const ⟨b⟩
/-- Chains on TN: n ↦ n + 1 + k (pairwise equivalent, pointwise different). -/
def tch (k : Nat) : Chain TN where
  chain n := ⟨n + 1 + k⟩
  cauchy {n i} h := by show min _ _ = min _ _; simp only; omega

-- `Iris.Completion.Raw.dist_lt` (hypothesis 6): necessary, BA, constant chains true / false, n = 1, m = 0
theorem w2c0_99 : ¬ drop0% Iris.Completion.Raw.dist_lt 6 := fun h =>
  nomatch (@h BA _ 1 0 (cb true) (cb false) Nat.zero_lt_one 0 (Nat.le_refl 0) : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Completion.Raw.dist_lt` (hypothesis 7): necessary, TN, constant chains 1 / 2 agree up to 0, not at 1
theorem w2c0_100 : ¬ drop0% Iris.Completion.Raw.dist_lt 7 := fun h => by
  have := @h TN _ 0 1 (Chain.const ⟨1⟩) (Chain.const ⟨2⟩) (fun k hk => by
    have : k = 0 := Nat.le_zero.mp hk
    subst this; exact tn12) 1 (Nat.le_refl 1)
  have h2 : min 1 (1 + 1) = min 2 (1 + 1) := this
  exact absurd h2 (by decide)
-- `Iris.Completion.ind` (hypothesis 3): necessary, motive = False on Completion BA
theorem w2c0_101 : ¬ drop0% Iris.Completion.ind 3 := fun h =>
  @h BA _ (fun _ => False) (Completion.mk (cb true))
-- `Iris.Completion.ind₂` (hypothesis 3): necessary, motive = False on Completion BA
theorem w2c0_102 : ¬ drop0% Iris.Completion.ind₂ 3 := fun h =>
  @h BA _ (fun _ _ => False) (Completion.mk (cb true)) (Completion.mk (cb true))
-- `Iris.Completion.sound` (hypothesis 4): necessary, BA, constant chains true / false are not identified
theorem w2c0_103 : ¬ drop0% Iris.Completion.sound 4 := fun h =>
  nomatch (Completion.exact (@h BA _ (cb true) (cb false)) 0 : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Completion.exact` (hypothesis 4): necessary, BA, constant chains true / false
theorem w2c0_104 : ¬ drop0% Iris.Completion.exact 4 := fun h =>
  nomatch (@h BA _ (cb true) (cb false) 0 : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Completion.lift_mk` (hypothesis 4): necessary (at beta : Type), TN, f c = (c 0).v separates the equivalent chains tch 0 and tch 4
theorem w2c0_105 : ¬ ∀ {α : Type} [inst : OFE α] {β : Type} (f : Chain α → β) (c : Chain α),
    ∀ (x y : Chain α), Completion.Raw.Equiv x y → f x = f y := fun h => by
  have := @h TN _ Nat (fun c => (c.chain 0).v) (tch 0) (tch 0) (tch 4) (fun n => by
    show min _ _ = min _ _; simp only [tch]; omega)
  exact absurd this (by decide)
/-- The constant non-expansive map to `b`. -/
def kb {α : Type} [OFE α] (b : Bool) : α -n> BA := ⟨fun _ => ⟨b⟩, ⟨fun _ _ _ _ => .rfl⟩⟩
-- `Iris.Completion.map_ext_ne` (hypothesis 8): necessary, BA, f = const true, g = const false
theorem w2c0_106 : ¬ drop0% Iris.Completion.map_ext_ne 8 := fun h => by
  have := @h BA _ BA _ (kb true) (kb false) (Completion.mk (cb true)) 0
  rw [Completion.map_mk, Completion.map_mk, Completion.dist_mk] at this
  exact nomatch (this 0 (Nat.le_refl 0) : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Completion.map_ext` (hypothesis 7): necessary, BA, f = const true, g = const false
theorem w2c0_107 : ¬ drop0% Iris.Completion.map_ext 7 := fun h => by
  have := @h BA _ BA _ (kb true) (kb false) (Completion.mk (cb true))
  rw [Completion.map_mk, Completion.map_mk] at this
  exact nomatch (Completion.exact this 0 : (⟨true⟩ : BA) = ⟨false⟩)

-- `Iris.Csum.inl_inj` (hypothesis 6): necessary, BA: true ≠ false
theorem w2c0_108 : ¬ drop0% Iris.Csum.inl_inj 6 := fun h =>
  nomatch (h (α := BA) (β := BA) (a := ⟨true⟩) (a' := ⟨false⟩) : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Csum.inl_injN` (hypothesis 7): necessary, BA: true, false at n = 0
theorem w2c0_109 : ¬ drop0% Iris.Csum.inl_injN 7 := fun h =>
  nomatch (h (α := BA) (β := BA) (n := 0) (a := ⟨true⟩) (a' := ⟨false⟩) : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Csum.inr_inj` (hypothesis 6): necessary, BA: true ≠ false
theorem w2c0_110 : ¬ drop0% Iris.Csum.inr_inj 6 := fun h =>
  nomatch (h (α := BA) (β := BA) (b := ⟨true⟩) (b' := ⟨false⟩) : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Csum.inr_injN` (hypothesis 7): necessary, BA: true, false at n = 0
theorem w2c0_111 : ¬ drop0% Iris.Csum.inr_injN 7 := fun h =>
  nomatch (h (α := BA) (β := BA) (n := 0) (b := ⟨true⟩) (b' := ⟨false⟩) : (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Csum.instDiscrete` (hypothesis 4): necessary, alpha = TN (not discrete), beta = BA
theorem w2c0_112 : ¬ drop0% Iris.Csum.instDiscrete 4 := fun h => by
  have := (h (α := TN) (β := BA)).discrete_0 (x := Csum.inl ⟨1⟩) (y := Csum.inl ⟨2⟩) tn12
  cases this
-- `Iris.Csum.instDiscrete` (hypothesis 5): necessary, alpha = BA, beta = TN
theorem w2c0_113 : ¬ drop0% Iris.Csum.instDiscrete 5 := fun h => by
  have := (h (α := BA) (β := TN)).discrete_0 (x := Csum.inr ⟨1⟩) (y := Csum.inr ⟨2⟩) tn12
  cases this
-- `Iris.Csum.instDiscreteEInl` (hypothesis 5): necessary, TN, a = 1 (1 and 2 agree at 0)
theorem w2c0_114 : ¬ drop0% Iris.Csum.instDiscreteEInl 5 := fun h => by
  have := (h (α := TN) (β := BA) (a := ⟨1⟩)).discrete (y := Csum.inl ⟨2⟩) tn12
  cases this
-- `Iris.Csum.instDiscreteEInr` (hypothesis 5): necessary, TN, b = 1
theorem w2c0_115 : ¬ drop0% Iris.Csum.instDiscreteEInr 5 := fun h => by
  have := (h (α := BA) (β := TN) (b := ⟨1⟩)).discrete (y := Csum.inr ⟨2⟩) tn12
  cases this
-- `_private.Iris.Algebra.Csum.0.Iris.Csum.pcore_map_inl_eq` (hypothesis 5): necessary, BA (no core)
theorem w2c0_116 : ¬ drop0% _private.Iris.Algebra.Csum.«0».Iris.Csum.pcore_map_inl_eq 5 := fun h => by
  obtain ⟨ca, hca, -⟩ := @h BA Unit _ ⟨true⟩ (Csum.inl ⟨true⟩)
  cases hca
-- `_private.Iris.Algebra.Csum.0.Iris.Csum.pcore_map_inr_eq` (hypothesis 5): necessary, BA (no core)
theorem w2c0_117 : ¬ drop0% _private.Iris.Algebra.Csum.«0».Iris.Csum.pcore_map_inr_eq 5 := fun h => by
  obtain ⟨cb, hcb, -⟩ := @h BA Unit _ ⟨true⟩ (Csum.inr ⟨true⟩)
  cases hcb
-- `Iris.Csum.ordNR_inl` (hypothesis 7): necessary, BA: true, false
theorem w2c0_118 : ¬ drop0% Iris.Csum.ordNR_inl 7 := fun h => by
  rcases h (α := BA) (β := BA) (n := 0) (a := ⟨true⟩) (a' := ⟨false⟩) with e | e <;> cases e
-- `Iris.Csum.ordNR_inr` (hypothesis 7): necessary, BA: true, false
theorem w2c0_119 : ¬ drop0% Iris.Csum.ordNR_inr 7 := fun h => by
  rcases h (α := BA) (β := BA) (n := 0) (b := ⟨true⟩) (b' := ⟨false⟩) with e | e <;> cases e
-- `Iris.Csum.instOrderRefl` (hypothesis 4): necessary, alpha = SN (order <), beta = BA
theorem w2c0_120 : ¬ drop0% Iris.Csum.instOrderRefl 4 := fun h =>
  Nat.lt_irrefl 0 ((h (α := SN) (β := BA)).ord_refl (Csum.inl ⟨0⟩))
-- `Iris.Csum.instOrderRefl` (hypothesis 5): necessary, alpha = BA, beta = SN
theorem w2c0_121 : ¬ drop0% Iris.Csum.instOrderRefl 5 := fun h =>
  Nat.lt_irrefl 0 ((h (α := BA) (β := SN)).ord_refl (Csum.inr ⟨0⟩))
-- `Iris.Csum.instIncOrd` (hypothesis 4): necessary, alpha = BA (not IncOrd), beta = SN
theorem w2c0_122 : ¬ drop0% Iris.Csum.instIncOrd 4 := fun h =>
  nomatch ((h (α := BA) (β := SN)).inc_ord (x := Csum.inl ⟨true⟩) (y := Csum.inl ⟨false⟩) ⟨Csum.inl ⟨false⟩, rfl⟩ :
    (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Csum.instIncOrd` (hypothesis 5): necessary, alpha = SN, beta = BA
theorem w2c0_123 : ¬ drop0% Iris.Csum.instIncOrd 5 := fun h =>
  nomatch ((h (α := SN) (β := BA)).inc_ord (x := Csum.inr ⟨true⟩) (y := Csum.inr ⟨false⟩) ⟨Csum.inr ⟨false⟩, rfl⟩ :
    (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Csum.instDiscrete_1` (hypothesis 5): necessary, alpha = BA (discrete), beta = Excl TN (not discrete)
theorem w2c0_124 : ¬ drop0% Iris.Csum.instDiscrete_1 5 := fun h => by
  have := (@h BA (Excl TN) _ _ (ORA.ofDiscreteORAData_discrete baData)).toDiscrete.discrete_0
    (x := Csum.inr (.excl ⟨1⟩)) (y := Csum.inr (.excl ⟨2⟩)) tn12
  cases this
-- `Iris.Csum.instExclusiveInl` (hypothesis 5): necessary, BT (all valid): inl false not exclusive
theorem w2c0_125 : ¬ drop0% Iris.Csum.instExclusiveInl 5 := fun h =>
  (h (α := BT) (β := BT) (a := ⟨false⟩)).exclusive0_l (Csum.inl ⟨false⟩) trivial
-- `Iris.Csum.instExclusiveInr` (hypothesis 5): necessary, BT: inr false not exclusive
theorem w2c0_126 : ¬ drop0% Iris.Csum.instExclusiveInr 5 := fun h =>
  (h (α := BT) (β := BT) (b := ⟨false⟩)).exclusive0_l (Csum.inr ⟨false⟩) trivial
-- `Iris.Csum.instCancelableInl` (hypothesis 5): necessary, BT: true • false = true • true
theorem w2c0_127 : ¬ drop0% Iris.Csum.instCancelableInl 5 := fun h => by
  have := (h (α := BT) (β := BT) (a := ⟨true⟩)).cancelableN (n := 0) (y := Csum.inl ⟨false⟩) (z := Csum.inl ⟨true⟩)
    trivial (OFE.Dist.of_eq rfl)
  cases (OFE.discrete this : (Csum.inl ⟨false⟩ : Csum BT BT) = Csum.inl ⟨true⟩)
-- `Iris.Csum.instCancelableInr` (hypothesis 5): necessary, BT: true • false = true • true
theorem w2c0_128 : ¬ drop0% Iris.Csum.instCancelableInr 5 := fun h => by
  have := (h (α := BT) (β := BT) (b := ⟨true⟩)).cancelableN (n := 0) (y := Csum.inr ⟨false⟩) (z := Csum.inr ⟨true⟩)
    trivial (OFE.Dist.of_eq rfl)
  cases (OFE.discrete this : (Csum.inr ⟨false⟩ : Csum BT BT) = Csum.inr ⟨true⟩)
-- `Iris.Csum.instIdFreeInl` (hypothesis 5): necessary, BT: false • false = false
theorem w2c0_129 : ¬ drop0% Iris.Csum.instIdFreeInl 5 := fun h =>
  (h (α := BT) (β := BT) (a := ⟨false⟩)).id_free0_r (Csum.inl ⟨false⟩) trivial (OFE.Dist.of_eq rfl)
-- `Iris.Csum.instIdFreeInr` (hypothesis 5): necessary, BT: false • false = false
theorem w2c0_130 : ¬ drop0% Iris.Csum.instIdFreeInr 5 := fun h =>
  (h (α := BT) (β := BT) (b := ⟨false⟩)).id_free0_r (Csum.inr ⟨false⟩) trivial (OFE.Dist.of_eq rfl)
-- `Iris.Csum.instOrdInc` (hypothesis 4): necessary, alpha = T3 (not OrdInc), beta = BT
theorem w2c0_131 : ¬ drop0% Iris.Csum.instOrdInc 4 := fun h => by
  obtain ⟨z, hz⟩ := (h (α := T3) (β := BT)).ord_inc (x := Csum.inl .a) (y := Csum.inl .b) t3_ab
  cases z <;> cases hz
-- `Iris.Csum.instOrdInc` (hypothesis 5): necessary, alpha = BT, beta = T3
theorem w2c0_132 : ¬ drop0% Iris.Csum.instOrdInc 5 := fun h => by
  obtain ⟨z, hz⟩ := (h (α := BT) (β := T3)).ord_inc (x := Csum.inr .a) (y := Csum.inr .b) t3_ab
  cases z <;> cases hz
-- `Iris.Csum.instIsInc` (hypothesis 4): necessary, alpha = BA (not IncOrd), beta = SN
theorem w2c0_133 : ¬ drop0% Iris.Csum.instIsInc 4 := fun h =>
  nomatch ((h (α := BA) (β := SN)).inc_ord (x := Csum.inl ⟨true⟩) (y := Csum.inl ⟨false⟩) ⟨Csum.inl ⟨false⟩, rfl⟩ :
    (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Csum.instIsInc` (hypothesis 5): necessary, alpha = SN, beta = BA
theorem w2c0_134 : ¬ drop0% Iris.Csum.instIsInc 5 := fun h =>
  nomatch ((h (α := SN) (β := BA)).inc_ord (x := Csum.inr ⟨true⟩) (y := Csum.inr ⟨false⟩) ⟨Csum.inr ⟨false⟩, rfl⟩ :
    (⟨true⟩ : BA) = ⟨false⟩)
-- `Iris.Csum.update_l` (hypothesis 6): necessary, T3: a valid, bot invalid
theorem w2c0_135 : ¬ drop0% Iris.Csum.update_l 6 := fun h =>
  (h (α := T3) (β := T3) (a₁ := .a) (a₂ := .bot)) 0 none (fun e => nomatch e) rfl
-- `Iris.Csum.update_r` (hypothesis 6): necessary, T3: a valid, bot invalid
theorem w2c0_136 : ¬ drop0% Iris.Csum.update_r 6 := fun h =>
  (h (α := T3) (β := T3) (b₁ := .a) (b₂ := .bot)) 0 none (fun e => nomatch e) rfl
-- `Iris.Csum.updateP_l` (hypothesis 7): necessary, BT, P = Q = False
theorem w2c0_137 : ¬ drop0% Iris.Csum.updateP_l 7 := fun h => by
  obtain ⟨y, hy, -⟩ := (h (α := BT) (β := BT) (P := fun _ => False) (Q := fun _ => False) (a := ⟨true⟩) (fun _ h => h)) 0 none trivial
  exact hy
-- `Iris.Csum.updateP_l` (hypothesis 8): necessary, BT, P = True, Q = False
theorem w2c0_138 : ¬ drop0% Iris.Csum.updateP_l 8 := fun h => by
  obtain ⟨y, hy, -⟩ := (h (α := BT) (β := BT) (P := fun _ => True) (Q := fun _ => False) (a := ⟨true⟩)
    (fun _ _ hv => ⟨⟨true⟩, trivial, hv⟩)) 0 none trivial
  exact hy
-- `Iris.Csum.updateP_r` (hypothesis 7): necessary, BT, P = Q = False
theorem w2c0_139 : ¬ drop0% Iris.Csum.updateP_r 7 := fun h => by
  obtain ⟨y, hy, -⟩ := (h (α := BT) (β := BT) (P := fun _ => False) (Q := fun _ => False) (b := ⟨true⟩) (fun _ h => h)) 0 none trivial
  exact hy
-- `Iris.Csum.updateP_r` (hypothesis 8): necessary, BT, P = True, Q = False
theorem w2c0_140 : ¬ drop0% Iris.Csum.updateP_r 8 := fun h => by
  obtain ⟨y, hy, -⟩ := (h (α := BT) (β := BT) (P := fun _ => True) (Q := fun _ => False) (b := ⟨true⟩)
    (fun _ _ hv => ⟨⟨true⟩, trivial, hv⟩)) 0 none trivial
  exact hy
-- `Iris.Csum.updateP'_l` (hypothesis 6): necessary, BT, P = False
theorem w2c0_141 : ¬ drop0% Iris.Csum.updateP'_l 6 := fun h => by
  obtain ⟨y, ⟨a', -, ha'⟩, -⟩ := (h (α := BT) (β := BT) (P := fun _ => False) (a := ⟨true⟩)) 0 none trivial
  exact ha'
-- `Iris.Csum.updateP'_r` (hypothesis 6): necessary, BT, P = False
theorem w2c0_142 : ¬ drop0% Iris.Csum.updateP'_r 6 := fun h => by
  obtain ⟨y, ⟨b', -, hb'⟩, -⟩ := (h (α := BT) (β := BT) (P := fun _ => False) (b := ⟨true⟩)) 0 none trivial
  exact hb'
-- `Iris.Csum.local_update_l` (hypothesis 8): necessary, BT: (false, false) to (true, false), frame none
theorem w2c0_143 : ¬ drop0% Iris.Csum.local_update_l 8 := fun h => by
  have := ((h (α := BT) (β := BT) (a₁ := ⟨false⟩) (a₂ := ⟨false⟩) (a₁' := ⟨true⟩) (a₂' := ⟨false⟩)) 0 none trivial
    (OFE.Dist.of_eq rfl)).2
  cases (OFE.discrete this : (Csum.inl ⟨true⟩ : Csum BT BT) = Csum.inl ⟨false⟩)
-- `Iris.Csum.local_update_r` (hypothesis 8): necessary, BT: (false, false) to (true, false), frame none
theorem w2c0_144 : ¬ drop0% Iris.Csum.local_update_r 8 := fun h => by
  have := ((h (α := BT) (β := BT) (b₁ := ⟨false⟩) (b₂ := ⟨false⟩) (b₁' := ⟨true⟩) (b₂' := ⟨false⟩)) 0 none trivial
    (OFE.Dist.of_eq rfl)).2
  cases (OFE.discrete this : (Csum.inr ⟨true⟩ : Csum BT BT) = Csum.inr ⟨false⟩)
-- `Iris.Csum.map_ext` (hypothesis 12): necessary, BA, f = const true, f' = const false, x = inl true
theorem w2c0_145 : ¬ drop0% Iris.Csum.map_ext 12 := fun h => by
  have := @h BA BA BA BA _ _ _ _ (fun _ => ⟨true⟩) (fun _ => ⟨false⟩) id id (fun _ => rfl) (Csum.inl ⟨true⟩)
  cases this
-- `Iris.Csum.map_ext` (hypothesis 13): necessary, BA, g = const true, g' = const false, x = inr true
theorem w2c0_146 : ¬ drop0% Iris.Csum.map_ext 13 := fun h => by
  have := @h BA BA BA BA _ _ _ _ id id (fun _ => ⟨true⟩) (fun _ => ⟨false⟩) (fun _ => rfl) (Csum.inr ⟨true⟩)
  cases this
-- `Iris.Csum.map_ne` (hypothesis 11): necessary, BA, f = const true, f' = const false, x = y = inl true
theorem w2c0_147 : ¬ drop0% Iris.Csum.map_ne 11 := fun h => by
  have := h (α := BA) (α' := BA) (β := BA) (β' := BA) (n := 0) (f := fun _ => ⟨true⟩) (f' := fun _ => ⟨false⟩)
    (g := id) (g' := id) (fun _ _ e => e) (x := Csum.inl ⟨true⟩) (y := Csum.inl ⟨true⟩) (OFE.Dist.of_eq rfl)
  cases (OFE.discrete this : (Csum.inl ⟨true⟩ : Csum BA BA) = Csum.inl ⟨false⟩)
-- `Iris.Csum.map_ne` (hypothesis 14): necessary, BA, g = const true, g' = const false, x = y = inr true
theorem w2c0_148 : ¬ drop0% Iris.Csum.map_ne 14 := fun h => by
  have := h (α := BA) (α' := BA) (β := BA) (β' := BA) (n := 0) (f := id) (f' := id) (fun _ _ e => e)
    (g := fun _ => ⟨true⟩) (g' := fun _ => ⟨false⟩) (x := Csum.inr ⟨true⟩) (y := Csum.inr ⟨true⟩) (OFE.Dist.of_eq rfl)
  cases (OFE.discrete this : (Csum.inr ⟨true⟩ : Csum BA BA) = Csum.inr ⟨false⟩)
-- `Iris.Csum.map_ne` (hypothesis 17): necessary, BA, f = g = id, x = inl true, y = inl false
theorem w2c0_149 : ¬ drop0% Iris.Csum.map_ne 17 := fun h => by
  have := h (α := BA) (α' := BA) (β := BA) (β' := BA) (n := 0) (f := id) (f' := id) (fun _ _ e => e)
    (g := id) (g' := id) (fun _ _ e => e) (x := Csum.inl ⟨true⟩) (y := Csum.inl ⟨false⟩)
  cases (OFE.discrete this : (Csum.inl ⟨true⟩ : Csum BA BA) = Csum.inl ⟨false⟩)
-- `Iris.Csum.instRFunctorAffine` (hypothesis 4): necessary, Fa = constOF BA (not IncOrd), Fb = constOF SN
theorem w2c0_150 : ¬ drop0% Iris.Csum.instRFunctorAffine 4 := fun h =>
  nomatch ((@(@h (constOF BA) (constOF SN) _ _ _).affine Unit Unit _ _).inc_ord
    (x := (Csum.inl ⟨true⟩ : Csum BA SN)) (y := Csum.inl ⟨false⟩) ⟨Csum.inl ⟨false⟩, rfl⟩ : (⟨true⟩ : BA) = ⟨false⟩)

end W2c0
