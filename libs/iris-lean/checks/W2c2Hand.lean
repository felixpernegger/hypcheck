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
namespace W2c2
open Iris Iris.OFE Iris.Std

local notation "FM" => (fun V => Nat → Option V)
@[simp] theorem fm_get {V : Type} (m : Nat → Option V) (k : Nat) : get? (M := FM) m k = m k := rfl

/-- Truncation OFE on naturals (copy of Probe1 TN): 1 and 2 agree at step 0. -/
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
instance tn0disc : DiscreteE (⟨0⟩ : TN) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩

/-- Discrete OFE on naturals (copy of W1c2 AN) with addition and the constant-zero operation. -/
structure AN where v : Nat
instance anOFE : OFE AN := OFE.ofDiscrete AN
theorem an_dist {n} {x y : AN} : x ≡{n}≡ y ↔ x = y := Iff.rfl
def addAN (a b : AN) : AN := ⟨a.v + b.v⟩
instance anAdd : Algebra.MonoidOps addAN ⟨0⟩ where
  op_ne := ⟨fun _ _ _ h _ _ h' => by cases h; cases h'; rfl⟩
  op_assoc := by intro a b c; simp [addAN, Nat.add_assoc]
  op_comm := by intro a b; simp [addAN, Nat.add_comm]
  op_left_id := by intro a; simp [addAN]
def zAN (_ _ : AN) : AN := ⟨0⟩
theorem z_bad : ¬ Algebra.MonoidOps zAN ⟨0⟩ := fun h => absurd (congrArg AN.v (h.op_left_id (a := ⟨1⟩))) (by decide)

end W2c2
namespace W2c2
open Iris Iris.OFE Iris.Std

/-- Discrete ORA on Bool (copy of Probe1 BA): op = and, no core, all valid, order = equality. -/
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
/-- In `Option BA`, `some true` is not below `some false`. -/
theorem ba_ord_tf : ¬ (some ⟨true⟩ : Option BA) ≼ₒ some ⟨false⟩ := fun h => by
  rcases h with h | h <;> cases h

/-- Discrete ORA on Bool (copy of W1c3 BOV): op = or, core only at true, valid iff false. -/
structure BOV where b : Bool
instance : OFE BOV := OFE.ofDiscrete BOV
instance : OFE.Discrete BOV := ⟨fun h => h⟩
def bovData : DiscreteORAData BOV where
  pcore x := if x.b then some x else none
  op x y := ⟨or x.b y.b⟩
  Valid x := x.b = false
  Order _ y := y.b = true
  assoc x y z := congrArg BOV.mk (Bool.or_assoc x.b y.b z.b).symm
  comm x y := congrArg BOV.mk (Bool.or_comm x.b y.b)
  pcore_op_left x cx h := by
    rcases x with ⟨_|_⟩ <;> simp at h; subst h; rfl
  pcore_idem x cx h := by
    rcases x with ⟨_|_⟩ <;> simp at h; subst h; rfl
  valid_op_left x y h := by simp at h; exact h.1
  ord_trans _ _ _ _ h := h
  op_mono_left _ _ _ h := by simp [h]
  valid_of_ord _ _ h1 h2 := by simp_all
  pcore_mono x y cx h e := ⟨y, by simp [h], h⟩
  pcore_order_op x cx e y := by
    rcases x with ⟨_|_⟩ <;> simp at e; exact ⟨⟨true⟩, rfl, rfl⟩
  pcore_increasing x cx e y := by
    rcases x with ⟨_|_⟩ <;> simp at e; subst e; rfl
  increasing_closed _ y _ h z := by simp [h]
instance bovORA : ORA BOV := ORA.ofDiscreteORAData bovData
theorem bov_invN {n} : ¬ ✓{n} (⟨true⟩ : BOV) := fun h => by have h' : true = false := h; cases h'
theorem bov_inv : ¬ ✓ (⟨true⟩ : BOV) := fun h => by have h' : true = false := h; cases h'

/-- Discrete ORA on Bool (copy of W1c3 BX): op = xor, no core, all valid, empty order. -/
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

/-- Discrete ORA on Bool (copy of W1c3 BT): op = or, no core, all valid, full order. -/
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
end W2c2
namespace W2c2
open Iris Iris.OFE Iris.Std

theorem ba_not_inc : ¬ Increasing (⟨false⟩ : BA) := fun h => by
  have := h.increasing ⟨true⟩
  cases this

/-- Discrete ORA on Bool (copy of W1c3 BU): op = or, total core false, all valid, order = implication (= inclusion). -/
structure BU where b : Bool
instance : OFE BU := OFE.ofDiscrete BU
instance : OFE.Discrete BU := ⟨fun h => h⟩
def buData : DiscreteORAData BU where
  pcore _ := some ⟨false⟩
  op x y := ⟨or x.b y.b⟩
  Valid _ := True
  Order x y := (or (!x.b) y.b) = true
  assoc x y z := congrArg BU.mk (Bool.or_assoc x.b y.b z.b).symm
  comm x y := congrArg BU.mk (Bool.or_comm x.b y.b)
  pcore_op_left x cx h := by cases h; rfl
  pcore_idem x cx h := by cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans x y z := by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> decide
  op_mono_left x y z := by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> decide
  valid_of_ord _ _ _ _ := trivial
  pcore_mono x y cx h e := ⟨⟨false⟩, rfl, by cases e; rfl⟩
  pcore_order_op x cx e y := ⟨⟨false⟩, rfl, by cases e; rfl⟩
  pcore_increasing x cx e y := by cases e; rcases y with ⟨_|_⟩ <;> rfl
  increasing_closed _ y _ _ z := by rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> rfl
instance buORA : ORA BU := ORA.ofDiscreteORAData buData
instance buIncOrd : IncOrd BU := ⟨fun {x y} ⟨z, hz⟩ => by
  subst hz; rcases x with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> rfl⟩
instance buOrdInc : OrdInc BU where
  ord_inc {x y} h := ⟨y, by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> first | rfl | cases h⟩
  ordN_incN {n x y} h := ⟨y, by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> first | rfl | cases h⟩

/-- Discrete ORA on three elements: every product is `bot` (the only invalid element), no core,
order: equality, anything below `bot`, and `e` below `y`. IncOrd, every element exclusive, `e ≼ₒ y`. -/
inductive E3 | e | y | bot deriving DecidableEq
instance : OFE E3 := OFE.ofDiscrete E3
instance : OFE.Discrete E3 := ⟨fun h => h⟩
def e3Data : DiscreteORAData E3 where
  pcore _ := none
  op _ _ := .bot
  Valid a := a ≠ .bot
  Order a b := a = b ∨ b = .bot ∨ (a = .e ∧ b = .y)
  assoc _ _ _ := rfl
  comm _ _ := rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ h := absurd rfl h
  ord_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  op_mono_left _ _ _ _ := Or.inl rfl
  valid_of_ord x y := by cases x <;> cases y <;> decide
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ _ _ := Or.inr (Or.inl rfl)
instance e3ORA : ORA E3 := ORA.ofDiscreteORAData e3Data
instance e3IncOrd : IncOrd E3 := ⟨fun {_ _} ⟨_, hz⟩ => Or.inr (Or.inl hz)⟩
instance e3Excl : ORA.Exclusive E3.e := ⟨fun _ h => h rfl⟩

/-- Discrete ORA on three elements: `w • w = w`, all other products `bot` (the only invalid element),
no core, order: target is `bot`. OrdInc, `x` exclusive and valid, `w` valid and not increasing. -/
inductive XW | x | w | bot deriving DecidableEq
instance : OFE XW := OFE.ofDiscrete XW
instance : OFE.Discrete XW := ⟨fun h => h⟩
def xwOp : XW → XW → XW
  | .w, .w => .w
  | _, _ => .bot
def xwData : DiscreteORAData XW where
  pcore _ := none
  op := xwOp
  Valid a := a ≠ .bot
  Order _ b := b = .bot
  assoc x y z := by cases x <;> cases y <;> cases z <;> rfl
  comm x y := by cases x <;> cases y <;> rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left x y := by cases x <;> cases y <;> decide
  ord_trans _ _ _ _ h := h
  op_mono_left x y z h := by subst h; cases z <;> rfl
  valid_of_ord _ _ h hv := absurd h hv
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ h z := by subst h; cases z <;> rfl
instance xwORA : ORA XW := ORA.ofDiscreteORAData xwData
instance xwOrdInc : OrdInc XW where
  ord_inc {a b} h := ⟨.bot, by subst h; cases a <;> rfl⟩
  ordN_incN {n a b} h := ⟨.bot, by subst h; cases a <;> rfl⟩
instance xwExcl : ORA.Exclusive XW.x := ⟨fun y h => by cases y <;> exact h rfl⟩
theorem xw_not_inc : ¬ Increasing XW.w := fun h => by
  have := h.increasing .w
  cases this
end W2c2
namespace W2c2
open Iris Iris.OFE Iris.Std
/-- In `Option BT`, `some true • w` is never `some false` (or never forgets `true`). -/
theorem bt_ne_tf (w : Option BT) : some (⟨false⟩ : BT) ≠ Op.op (α := Option BT) (some ⟨true⟩) w := fun e => by
  rcases w with _ | ⟨b⟩ <;> cases e
end W2c2
namespace W2c2
open Iris Iris.OFE Iris.Std

/-- One-point ORA (copy of W1c3 UZ): never valid, order only at step 0, no core. -/
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
/-- In UZ nothing can be updated from (every frame is invalid). -/
theorem uz_upd {P : UZ → Prop} : ⟨⟩ ~~>: P := fun _ mz hv => by cases mz <;> exact hv.elim

/-- Discrete ORA on naturals: `x • y = x + y + 1`, all valid, no core, order = equality.
Every element is cancelable and id-free, so `some x` is cancelable in `Option NP`. -/
structure NP where v : Nat
instance : OFE NP := OFE.ofDiscrete NP
instance : OFE.Discrete NP := ⟨fun h => h⟩
def npData : DiscreteORAData NP where
  pcore _ := none
  op x y := ⟨x.v + y.v + 1⟩
  Valid _ := True
  Order := Eq
  assoc x y z := by simp only [NP.mk.injEq]; omega
  comm x y := by simp only [NP.mk.injEq]; omega
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
instance npORA : ORA NP := ORA.ofDiscreteORAData npData
instance npCanc {x : NP} : ORA.Cancelable x := ⟨fun {n y z} _ h => by
  have h' : (⟨x.v + y.v + 1⟩ : NP) = ⟨x.v + z.v + 1⟩ := h
  cases y; cases z; simp only [NP.mk.injEq] at h' ⊢; show NP.mk _ = NP.mk _; congr 1; omega⟩
instance npIdFree {x : NP} : ORA.IdFree x := ⟨fun _ _ h => by
  have h' : (⟨x.v + _ + 1⟩ : NP) = x := h
  cases x; simp only [NP.mk.injEq] at h'; omega⟩

theorem emp_valid0 {M : Type → Type} {K V : Type} [LawfulPartialMap M K] [ORA V] {n} : ✓{n} (∅ : M V) :=
  fun k => by rw [LawfulPartialMap.get?_empty]; exact trivial
end W2c2
namespace W2c2
open Iris Iris.OFE Iris.Std
local notation "FM" => (fun V => Nat → Option V)
-- `PartialMap.eqv_of_Equiv` (hypothesis 7, H): necessary, V=Unit, M=Nat→Option: t1 empty, t2 everywhere (); maps differ
theorem w2c2_0 : ¬ drop0% PartialMap.eqv_of_Equiv 7 := fun h => by
  have := congrFun (@h Unit FM Nat _ _ (fun _ => none) (fun _ => some ())) 0
  simp at this
-- `PartialMap.bindAlter_dist` (hypothesis 12, Hf): necessary, V=V'=Unit, f=const none, g=const (some ()), m1=m2 full: results none vs some at key 0
theorem w2c2_2 : ¬ drop0% PartialMap.bindAlter_dist 12 := fun h => by
  have := @h FM Nat Unit Unit _ _ _ 0 (fun _ _ => none) (fun _ _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.bindAlter_dist` (hypothesis 13, Hm): necessary, f=g=some, m1 empty, m2 full: bindAlter results differ at key 0
theorem w2c2_3 : ¬ drop0% PartialMap.bindAlter_dist 13 := fun h => by
  have := @h FM Nat Unit Unit _ _ _ 0 (fun _ v => some v) (fun _ v => some v) (fun _ => none) (fun _ => some ()) (fun h => some_dist_some.mpr h) 0
  simp [OFE.Dist, Option.Forall₂, Iris.Std.bindAlter, PartialMap.bindAlter] at this
end W2c2

namespace W2c2
open Iris Iris.OFE Iris.Std
local notation "FM" => (fun V => Nat → Option V)
-- `PartialMap.instNonExpansive₂Merge` (hypothesis 6, inst): necessary, V=TN (non-discrete), op k a _ = if a=1 then 0 else 1: maps 1 and 2 agree at step 0, merged values 0 and 1 do not
theorem w2c2_1 : ¬ drop0% PartialMap.instNonExpansive₂Merge 6 := fun h => by
  have := (@h FM Nat TN _ _ (fun _ a _ => if a.v = 1 then ⟨0⟩ else ⟨1⟩)).ne (n := 0)
    (x₁ := fun _ => some ⟨1⟩) (x₂ := fun _ => some ⟨2⟩) (fun _ => some_dist_some.mpr tn12)
    (y₁ := fun _ => some ⟨0⟩) (y₂ := fun _ => some ⟨0⟩) (fun _ => .rfl) 0
  change (some ⟨0⟩ : Option TN) ≡{0}≡ some ⟨1⟩ at this
  simp [some_dist_some, tn_dist] at this
-- `PartialMap.merge_dist` (hypothesis 12, Hf): necessary, V=AN (discrete Nat), f takes left, g takes right, m1=m1'={0}, m2=m2'={1}: 0 vs 1
theorem w2c2_4 : ¬ drop0% PartialMap.merge_dist 12 := fun h => by
  have := @h FM Nat AN _ _ 0 (fun _ a _ => a) (fun _ _ b => b) (fun _ => some ⟨0⟩) (fun _ => some ⟨0⟩) (fun _ => some ⟨1⟩) (fun _ => some ⟨1⟩) (fun _ => .rfl) (fun _ => .rfl) 0
  change (some ⟨0⟩ : Option AN) ≡{0}≡ some ⟨1⟩ at this
  simp [some_dist_some, an_dist] at this
-- `PartialMap.merge_dist` (hypothesis 13, H₁): necessary, V=Unit, m1 empty, m1' full, m2=m2' empty: merge results none vs some
theorem w2c2_5 : ¬ drop0% PartialMap.merge_dist 13 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ a _ => a) (fun _ a _ => a) (fun _ => none) (fun _ => some ()) (fun _ => none) (fun _ => none) (fun h _ => h) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, Iris.Std.merge, PartialMap.merge] at this
-- `PartialMap.merge_dist` (hypothesis 14, H₂): necessary, V=Unit, m2 empty, m2' full, m1=m1' empty: merge results none vs some
theorem w2c2_6 : ¬ drop0% PartialMap.merge_dist 14 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ a _ => a) (fun _ a _ => a) (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => some ()) (fun h _ => h) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, Iris.Std.merge, PartialMap.merge] at this
-- `PartialMap.zipWith_dist` (hypothesis 16, Hf): necessary, V''=AN, f=const 0, g=const 1 on full Unit maps: 0 vs 1
theorem w2c2_7 : ¬ drop0% PartialMap.zipWith_dist 16 := fun h => by
  have := @h FM Nat Unit Unit AN _ _ _ _ 0 (fun _ _ => ⟨0⟩) (fun _ _ => ⟨1⟩) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => .rfl) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, PartialMap.zipWith, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.zipWith_dist` (hypothesis 17, H₁): necessary, V=Unit, m1 empty, m1' full, m2=m2' full: zipWith none vs some
theorem w2c2_8 : ¬ drop0% PartialMap.zipWith_dist 17 := fun h => by
  have := @h FM Nat Unit Unit Unit _ _ _ _ 0 (fun _ _ => ()) (fun _ _ => ()) (fun _ => none) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ _ => .rfl) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, PartialMap.zipWith, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.zipWith_dist` (hypothesis 18, H₂): necessary, m1=m1' full, m2 empty, m2' full: zipWith none vs some
theorem w2c2_9 : ¬ drop0% PartialMap.zipWith_dist 18 := fun h => by
  have := @h FM Nat Unit Unit Unit _ _ _ _ 0 (fun _ _ => ()) (fun _ _ => ()) (fun _ => some ()) (fun _ => some ()) (fun _ => none) (fun _ => some ()) (fun _ _ => .rfl) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, PartialMap.zipWith, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.isSome_get?_eq_of_dist` (hypothesis 8, H): necessary, m1 empty, m2 full: isSome differs at key 0
theorem w2c2_10 : ¬ drop0% PartialMap.isSome_get?_eq_of_dist 8 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ => none) (fun _ => some ()) 0
  simp at this
-- `PartialMap.intersectionWith_dist` (hypothesis 12, Hf): necessary, f=const none, g=const (some ()) on full maps: none vs some
theorem w2c2_11 : ¬ drop0% PartialMap.intersectionWith_dist 12 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ _ _ => none) (fun _ _ _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => .rfl) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, PartialMap.intersectionWith, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.intersectionWith_dist` (hypothesis 13, H₁): necessary, m1 empty, m1' full, m2=m2' full, f=g keep left: none vs some
theorem w2c2_12 : ¬ drop0% PartialMap.intersectionWith_dist 13 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ v _ => some v) (fun _ v _ => some v) (fun _ => none) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun h _ => some_dist_some.mpr h) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, PartialMap.intersectionWith, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.intersectionWith_dist` (hypothesis 14, H₂): necessary, m1=m1' full, m2 empty, m2' full: intersection none vs some
theorem w2c2_13 : ¬ drop0% PartialMap.intersectionWith_dist 14 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ v _ => some v) (fun _ v _ => some v) (fun _ => some ()) (fun _ => some ()) (fun _ => none) (fun _ => some ()) (fun h _ => some_dist_some.mpr h) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, PartialMap.intersectionWith, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.differenceWith_dist` (hypothesis 12, Hf): necessary, f=const none, g=const (some ()) on full maps: differenceWith none vs some
theorem w2c2_14 : ¬ drop0% PartialMap.differenceWith_dist 12 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ _ _ => none) (fun _ _ _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => .rfl) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, PartialMap.differenceWith, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.differenceWith_dist` (hypothesis 13, H₁): necessary, m1 empty, m1' full, m2=m2' full: differenceWith none vs some
theorem w2c2_15 : ¬ drop0% PartialMap.differenceWith_dist 13 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ v _ => some v) (fun _ v _ => some v) (fun _ => none) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun h _ => some_dist_some.mpr h) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, PartialMap.differenceWith, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.differenceWith_dist` (hypothesis 14, H₂): necessary, m1=m1' full, m2 empty, m2' full, f=g=const none: some vs none
theorem w2c2_16 : ¬ drop0% PartialMap.differenceWith_dist 14 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ _ _ => none) (fun _ _ _ => none) (fun _ => some ()) (fun _ => some ()) (fun _ => none) (fun _ => some ()) (fun _ _ => .rfl) (fun _ => .rfl) 0
  simp [OFE.Dist, Option.Forall₂, PartialMap.differenceWith, Iris.Std.bindAlter, PartialMap.bindAlter] at this
-- `PartialMap.disjoint_dist_iff` (hypothesis 10, H₁): necessary, m1 empty, m1' full, m2=m2' full: disjoint m1 m2 holds, m1' m2' not
theorem w2c2_17 : ¬ drop0% PartialMap.disjoint_dist_iff 10 := fun h => by
  have := (@h FM Nat Unit _ _ 0 (fun _ => none) (fun _ => some ()) (fun _ => some ()) (fun _ => some ()) (fun _ => .rfl)).mp
    (fun k hk => by simp at hk) 0
  simp at this
-- `PartialMap.disjoint_dist_iff` (hypothesis 11, H₂): necessary, m2 empty, m2' full, m1=m1' full: disjoint m1 m2 holds, m1' m2' not
theorem w2c2_18 : ¬ drop0% PartialMap.disjoint_dist_iff 11 := fun h => by
  have := (@h FM Nat Unit _ _ 0 (fun _ => some ()) (fun _ => some ()) (fun _ => none) (fun _ => some ()) (fun _ => .rfl)).mp
    (fun k hk => by simp at hk) 0
  simp at this
-- `PartialMap.dom_eq_of_dist` (hypothesis 8, H): necessary, m1 empty, m2 full: dom differs at key 0
theorem w2c2_22 : ¬ drop0% PartialMap.dom_eq_of_dist 8 := fun h => by
  have := congrFun (@h FM Nat Unit _ _ 0 (fun _ => none) (fun _ => some ())) 0
  simp [PartialMap.dom] at this
-- `instDiscreteHeap` (hypothesis 5, inst): necessary, V=TN: maps of 1 and 2 agree at step 0 but differ
theorem w2c2_23 : ¬ drop0% instDiscreteHeap 5 := fun h => by
  have := congrFun ((@h FM Nat TN _ _).discrete_0 (x := fun _ => some ⟨1⟩) (y := fun _ => some ⟨2⟩) (fun _ => some_dist_some.mpr tn12)) 0
  simp at this
-- `instDiscreteESingleton` (hypothesis 7, ha): necessary, V=TN, v=1 not discrete: singleton 0 1 agrees at step 0 with singleton 0 2
theorem w2c2_24 : ¬ drop0% instDiscreteESingleton 7 := fun h => by
  have := congrFun ((@h FM Nat TN _ _ _ ⟨1⟩ 0).discrete (y := fun k => if k = 0 then some ⟨2⟩ else none)
    (fun k => by rcases k with _ | k <;> simp [PartialMap.singleton, Iris.Std.insert, PartialMap.insert] <;> first | exact some_dist_some.mpr tn12 | exact .of_eq rfl)) 0
  simp [PartialMap.singleton, Iris.Std.insert, PartialMap.insert] at this
-- `singleton_dist` (hypothesis 9, h): necessary, V=TN, x=0, y=1 differ at step 0
theorem w2c2_25 : ¬ drop0% singleton_dist 9 := fun h => by
  have := @h FM Nat TN _ _ _ 0 ⟨0⟩ ⟨1⟩ 0 0
  simp [PartialMap.singleton, Iris.Std.insert, PartialMap.insert, some_dist_some, tn_dist] at this
-- `insert_idN` (hypothesis 9, h): necessary, m empty, x=(): insert adds key 0
theorem w2c2_26 : ¬ drop0% insert_idN 9 := fun h => by
  have := @h FM Nat Unit _ _ 0 (fun _ => none) 0 () 0
  simp [OFE.Dist, Option.Forall₂, Iris.Std.insert, PartialMap.insert] at this
-- `instDiscreteEGet?` (hypothesis 6, inst): necessary, V=TN, m=const 1: some 1 is not discrete
theorem w2c2_27 : ¬ drop0% instDiscreteEGet? 6 := fun h => by
  have := (@h FM Nat TN _ _ (fun _ => some ⟨1⟩) 0).discrete (y := some ⟨2⟩) (some_dist_some.mpr tn12)
  simp at this
-- `instDiscreteEInsert` (hypothesis 8, inst): necessary, V=TN, m empty (discrete), x=1: insert m 0 1 agrees at step 0 with insert m 0 2
theorem w2c2_28 : ¬ drop0% instDiscreteEInsert 8 := fun h => by
  have := congrFun ((@h FM Nat TN _ _ (fun _ => none) 0 ⟨1⟩ ⟨fun {y} hy => funext fun k => by
      have := hy k; simp [OFE.Dist, Option.Forall₂] at this; split at this <;> simp_all⟩).discrete
    (y := fun k => if k = 0 then some ⟨2⟩ else none)
    (fun k => by rcases k with _ | k <;> simp [Iris.Std.insert, PartialMap.insert] <;> first | exact some_dist_some.mpr tn12 | exact .of_eq rfl)) 0
  simp [Iris.Std.insert, PartialMap.insert] at this
-- `instDiscreteEInsert` (hypothesis 9, inst): necessary, V=TN, x=0 (discrete), m=const 1: insert m 0 0 agrees at step 0 with a map having 2 at key 1
theorem w2c2_29 : ¬ drop0% instDiscreteEInsert 9 := fun h => by
  have := congrFun ((@h FM Nat TN _ _ (fun _ => some ⟨1⟩) 0 ⟨0⟩ tn0disc).discrete
    (y := fun k => if k = 0 then some ⟨0⟩ else some ⟨2⟩)
    (fun k => by rcases k with _ | k <;> simp [Iris.Std.insert, PartialMap.insert] <;> first | exact some_dist_some.mpr tn12 | exact .of_eq rfl)) 1
  simp [Iris.Std.insert, PartialMap.insert] at this
end W2c2

namespace W2c2
open Iris Iris.OFE Iris.Std
local notation "FM" => (fun V => Nat → Option V)
-- `Heap.increasing_get?` (hypothesis 6, h): necessary, V=BA (and, order Eq), m=const false: some false is not increasing
theorem w2c2_30 : ¬ drop0% Heap.increasing_get? 6 := fun h =>
  ba_ord_tf ((@h FM Nat BA _ _ (fun _ => some ⟨false⟩) 0).increasing (some ⟨true⟩))
-- `Heap.instIncOrd` (hypothesis 5, inst): necessary, V=BA: const true included in const false (true&&false=false) but not ordered
theorem w2c2_31 : ¬ drop0% Heap.instIncOrd 5 := fun h =>
  ba_ord_tf ((@h FM Nat BA _ _).inc_ord (x := fun _ => some ⟨true⟩) (y := fun _ => some ⟨false⟩) ⟨fun _ => some ⟨false⟩, rfl⟩ 0)
-- `Heap.instIsInc` (hypothesis 5, inst): necessary, V=BA: inclusion does not imply order (as idx of instIncOrd)
theorem w2c2_33 : ¬ drop0% Heap.instIsInc 5 := fun h =>
  ba_ord_tf ((@h FM Nat BA _ _).inc_ord (x := fun _ => some ⟨true⟩) (y := fun _ => some ⟨false⟩) ⟨fun _ => some ⟨false⟩, rfl⟩ 0)
-- `Heap.instOrdInc` (hypothesis 5, inst): necessary, V=BT (or, full order): const true ordered below const false but not included
theorem w2c2_32 : ¬ drop0% Heap.instOrdInc 5 := fun h => by
  obtain ⟨z, hz⟩ := (@h FM Nat BT _ _).ord_inc (x := fun _ => some ⟨true⟩) (y := fun _ => some ⟨false⟩) (fun _ => Or.inr trivial)
  have := (congrFun hz 0).trans (Heap.get?_op (M := FM) (fun _ => some (⟨true⟩ : BT)) z (i := 0))
  change some (⟨false⟩ : BT) = Op.op (α := Option BT) (some ⟨true⟩) (z 0) at this
  rcases hz0 : z 0 with _ | ⟨b⟩ <;> rw [hz0] at this <;> cases this
-- `Heap.validN_get?_validN` (hypothesis 9, Hv): necessary, V=BOV (valid iff false), m=const true (invalid): x=true
theorem w2c2_34 : ¬ drop0% Heap.validN_get?_validN 9 := fun h =>
  bov_invN (n := 0) (@h FM Nat BOV _ _ 0 0 ⟨true⟩ (fun _ => some ⟨true⟩) (.of_eq rfl))
-- `Heap.validN_get?_validN` (hypothesis 10, He): necessary, V=BOV, m empty (valid), x=true invalid
theorem w2c2_35 : ¬ drop0% Heap.validN_get?_validN 10 := fun h =>
  bov_invN (n := 0) (@h FM Nat BOV _ _ 0 0 ⟨true⟩ (fun _ => none) (fun _ => by first | exact trivial | simp | constructor))
-- `Heap.validN_get?` (hypothesis 8, v): necessary, V=BOV, m=const true
theorem w2c2_36 : ¬ drop0% Heap.validN_get? 8 := fun h =>
  bov_invN (n := 0) (@h FM Nat BOV _ _ 0 0 (fun _ => some ⟨true⟩))
-- `Heap.valid_get?_valid` (hypothesis 8, Hv): necessary, V=BOV, m=const true, x=true
theorem w2c2_37 : ¬ drop0% Heap.valid_get?_valid 8 := fun h =>
  bov_inv (@h FM Nat BOV _ _ 0 ⟨true⟩ (fun _ => some ⟨true⟩) rfl)
-- `Heap.valid_get?_valid` (hypothesis 9, He): necessary, V=BOV, m empty, x=true invalid
theorem w2c2_38 : ¬ drop0% Heap.valid_get?_valid 9 := fun h =>
  bov_inv (@h FM Nat BOV _ _ 0 ⟨true⟩ (fun _ => none) (fun _ => by first | exact trivial | simp | constructor))
-- `Heap.valid_get?` (hypothesis 7, v): necessary, V=BOV, m=const true
theorem w2c2_39 : ¬ drop0% Heap.valid_get? 7 := fun h =>
  bov_inv (@h FM Nat BOV _ _ 0 (fun _ => some ⟨true⟩))
-- `Heap.insert_validN` (hypothesis 9, Hx): necessary, V=BOV, m empty, x=true invalid
theorem w2c2_40 : ¬ drop0% Heap.insert_validN 9 := fun h =>
  bov_invN (n := 0) (@h FM Nat BOV _ _ 0 ⟨true⟩ 0 (fun _ => none) (fun _ => by first | exact trivial | simp | constructor) 0)
-- `Heap.insert_validN` (hypothesis 10, Hm): necessary, V=BOV, x=false, m=const true: key 1 invalid
theorem w2c2_41 : ¬ drop0% Heap.insert_validN 10 := fun h =>
  bov_invN (n := 0) (@h FM Nat BOV _ _ 0 ⟨false⟩ 0 (fun _ => some ⟨true⟩) rfl 1)
-- `Heap.insert_valid` (hypothesis 8, Hx): necessary, V=BOV, m empty, x=true invalid
theorem w2c2_42 : ¬ drop0% Heap.insert_valid 8 := fun h =>
  bov_inv (@h FM Nat BOV _ _ ⟨true⟩ 0 (fun _ => none) (fun _ => by first | exact trivial | simp | constructor) 0)
-- `Heap.insert_valid` (hypothesis 9, Hm): necessary, V=BOV, x=false, m=const true: key 1 invalid
theorem w2c2_43 : ¬ drop0% Heap.insert_valid 9 := fun h =>
  bov_inv (@h FM Nat BOV _ _ ⟨false⟩ 0 (fun _ => some ⟨true⟩) rfl 1)
-- `Heap.delete_validN` (hypothesis 8, Hv): necessary, V=BOV, m=const true: key 1 stays invalid
theorem w2c2_44 : ¬ drop0% Heap.delete_validN 8 := fun h =>
  bov_invN (n := 0) (@h FM Nat BOV _ _ 0 0 (fun _ => some ⟨true⟩) 1)
-- `Heap.delete_valid` (hypothesis 7, Hv): necessary, V=BOV, m=const true: key 1 stays invalid
theorem w2c2_45 : ¬ drop0% Heap.delete_valid 7 := fun h =>
  bov_inv (@h FM Nat BOV _ _ 0 (fun _ => some ⟨true⟩) 1)
-- `Heap.insert_equiv_singleton_op_singleton` (hypothesis 8, Hemp): necessary, V=BA, x=true, m=const false: true vs true&&false at key 0
theorem w2c2_46 : ¬ drop0% Heap.insert_equiv_singleton_op_singleton 8 := fun h => by
  have := @h FM Nat BA _ _ 0 ⟨true⟩ (fun _ => some ⟨false⟩) 0
  change (some ⟨true⟩ : Option BA) = some ⟨false⟩ at this
  simp at this
-- `Heap.insert_eq_singleton_op_singleton` (hypothesis 8, Hemp): necessary, V=BA, x=true, m=const false: true vs true&&false at key 0
theorem w2c2_47 : ¬ drop0% Heap.insert_eq_singleton_op_singleton 8 := fun h => by
  have := congrFun (@h FM Nat BA _ _ 0 ⟨true⟩ (fun _ => some ⟨false⟩)) 0
  change (some ⟨true⟩ : Option BA) = some ⟨false⟩ at this
  simp at this
-- `Heap.core_singleton_equiv` (hypothesis 8, Hpcore): necessary, V=BA (no core), x=cx=true: core of singleton is empty at key 0
theorem w2c2_48 : ¬ drop0% Heap.core_singleton_equiv 8 := fun h => by
  have := @h FM Nat BA _ _ 0 ⟨true⟩ ⟨true⟩ 0
  change (none : Option BA) = some ⟨true⟩ at this
  cases this
-- `Heap.singleton_core_eq` (hypothesis 8, Hpcore): necessary, V=BA (no core), x=cx=true: core of singleton is empty at key 0
theorem w2c2_49 : ¬ drop0% Heap.singleton_core_eq 8 := fun h => by
  have := congrFun (@h FM Nat BA _ _ 0 ⟨true⟩ ⟨true⟩) 0
  change (none : Option BA) = some ⟨true⟩ at this
  cases this
-- `Heap.singleton_core_total_eq` (hypothesis 5, inst): necessary, V=BA (no core, not total): core (singleton 0 true) is empty, singleton 0 (core true) is not
theorem w2c2_50 : ¬ drop0% Heap.singleton_core_total_eq 5 := fun h => by
  have := congrFun (@h FM Nat BA _ _ 0 ⟨true⟩) 0
  change (none : Option BA) = some _ at this
  cases this
-- `Heap.instIsOpSingleton` (hypothesis 10, h): necessary, V=BA, x=true, x1=x2=false: false&&false != true
theorem w2c2_51 : ¬ drop0% Heap.instIsOpSingleton 10 := fun h => by
  have := congrFun (@h FM Nat BA _ _ .merge 0 ⟨true⟩ ⟨false⟩ ⟨false⟩).is_op 0
  change (some ⟨true⟩ : Option BA) = some ⟨false⟩ at this
  simp at this
-- `Heap.coreId_of_get?` (hypothesis 6, h): necessary, V=BA (no core), m=const false: pcore m = empty map != m
theorem w2c2_52 : ¬ drop0% Heap.coreId_of_get? 6 := fun h => by
  have := congrFun (Option.some.inj (@h FM Nat BA _ _ (fun _ => some ⟨false⟩)).core_id) 0
  change (none : Option BA) = some ⟨false⟩ at this
  cases this
-- `Heap.instCoreId` (hypothesis 6, I): necessary, V=BA (no core), m=const false: not CoreId
theorem w2c2_53 : ¬ drop0% Heap.instCoreId 6 := fun h => by
  have := congrFun (Option.some.inj (@h FM Nat BA _ _ (fun _ => some ⟨false⟩)).core_id) 0
  change (none : Option BA) = some ⟨false⟩ at this
  cases this
-- `Heap.instCoreIdSingleton` (hypothesis 7, inst): necessary, V=BA (no core), x=false: singleton not CoreId
theorem w2c2_54 : ¬ drop0% Heap.instCoreIdSingleton 7 := fun h => by
  have := congrFun (Option.some.inj (@h FM Nat BA _ _ ⟨false⟩ 0).core_id) 0
  change (none : Option BA) = some ⟨false⟩ at this
  cases this
-- `Heap.singleton_ord_singleton_mono` (hypothesis 8, Hinc): necessary, V=BA (order Eq), x=true, y=false
theorem w2c2_55 : ¬ drop0% Heap.singleton_ord_singleton_mono 8 := fun h =>
  ba_ord_tf (@h FM Nat BA _ _ ⟨true⟩ ⟨false⟩ 0 0)
-- `Heap.total_singleton_ord_singleton_iff` (hypothesis 8, inst): necessary, V=BX (empty order, not OrderRefl): singletons of true ordered (Option order has equality), true not below true
theorem w2c2_56 : ¬ drop0% Heap.total_singleton_ord_singleton_iff 8 := fun h =>
  (@h FM Nat BX _ _ 0 ⟨true⟩ ⟨true⟩).mp (fun k => by rcases k with _ | k; exact Or.inl rfl; exact trivial)
-- `Heap.ord_dom_ord` (hypothesis 7, Hinc): necessary, m1 full, m2 empty
theorem w2c2_58 : ¬ drop0% Heap.ord_dom_ord 7 := fun h => by
  have := @h FM Nat BA _ _ (fun _ => some ⟨true⟩) (fun _ => none) 0 rfl
  cases this
end W2c2

namespace W2c2
open Iris Iris.OFE Iris.Std
local notation "FM" => (fun V => Nat → Option V)
-- `Heap.singleton_ord_iff` (hypothesis 7, inst): necessary, V=BA (not IncOrd): m = 0:true, else false; none below some false fails (false not increasing)
theorem w2c2_57 : ¬ drop0% Heap.singleton_ord_iff 7 := fun h =>
  ba_not_inc ((@h FM Nat BA _ _ 0 ⟨true⟩ (fun k => if k = 0 then some ⟨true⟩ else some ⟨false⟩)).mpr
    ⟨⟨true⟩, rfl, Or.inl rfl⟩ 1)
-- `Heap.exclusive_singleton_inc_iff` (hypothesis 8, He): necessary, V=BA (true not exclusive), x=true, m=const false: singleton 0 true included in m, m 0 != some true
theorem w2c2_59 : ¬ drop0% Heap.exclusive_singleton_inc_iff 8 := fun h => by
  have := (@h FM Nat BA _ _ ⟨true⟩ 0 (fun _ => some ⟨false⟩) (fun _ => by exact trivial)).mp
    ⟨fun _ => some ⟨false⟩, funext fun k => by rcases k with _ | k <;> rfl⟩
  cases this
-- `Heap.exclusive_singleton_inc_iff` (hypothesis 9, Hv): necessary, V=Excl Unit, x=excl, m = 0:invalid (= excl•excl), rest excl: included, m invalid
theorem w2c2_60 : ¬ drop0% Heap.exclusive_singleton_inc_iff 9 := fun h => by
  have := (@h FM Nat (Excl Unit) _ _ (.excl ()) 0 (fun k => if k = 0 then some .invalid else some (.excl ())) inferInstance).mp
    ⟨fun _ => some (.excl ()), funext fun k => by rcases k with _ | k <;> rfl⟩
  cases this
-- `Heap.exclusive_singleton_ord_iff` (hypothesis 7, inst): necessary, V=XW (OrdInc, w•w=w, not IncOrd), x exclusive, m = 0:x, rest w: m 0 = x but none below some w fails (w not increasing)
theorem w2c2_61 : ¬ drop0% Heap.exclusive_singleton_ord_iff 7 := fun h =>
  xw_not_inc ((@h FM Nat XW _ _ .x 0 inferInstance (fun k => if k = 0 then some .x else some .w) inferInstance
    (fun k => by rcases k with _ | k; exact (by decide : XW.x ≠ .bot); exact (by decide : XW.w ≠ .bot))).mpr rfl 1)
-- `Heap.exclusive_singleton_ord_iff` (hypothesis 8, inst): necessary, V=E3 (IncOrd, all products bot, e below y), x=e exclusive, m=singleton 0 y: ordered but m 0 != e
theorem w2c2_62 : ¬ drop0% Heap.exclusive_singleton_ord_iff 8 := fun h => by
  have := (@h FM Nat E3 _ _ .e 0 inferInstance (fun k => if k = 0 then some .y else none) inferInstance
    (fun k => by rcases k with _ | k; exact (by decide : E3.y ≠ .bot); exact trivial)).mp
    (fun k => by rcases k with _ | k; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)); exact trivial)
  cases this
-- `Heap.exclusive_singleton_ord_iff` (hypothesis 10, He): necessary, V=BU (or, order = inclusion, IsInc), x=false not exclusive, m=singleton 0 true
theorem w2c2_63 : ¬ drop0% Heap.exclusive_singleton_ord_iff 10 := fun h => by
  have := (@h FM Nat BU _ _ ⟨false⟩ 0 inferInstance inferInstance (fun k => if k = 0 then some ⟨true⟩ else none)
    (fun k => by rcases k with _ | k <;> first | exact trivial | decide)).mp
    (fun k => by rcases k with _ | k; exact Or.inr rfl; exact trivial)
  cases this
-- `Heap.exclusive_singleton_ord_iff` (hypothesis 11, Hv): necessary, V=Excl Unit, x=excl, m=singleton 0 invalid: excl included in invalid, m invalid
theorem w2c2_64 : ¬ drop0% Heap.exclusive_singleton_ord_iff 11 := fun h => by
  have := (@h FM Nat (Excl Unit) _ _ (.excl ()) 0 inferInstance inferInstance (fun k => if k = 0 then some .invalid else none)
    inferInstance).mp
    (fun k => by rcases k with _ | k; exact Or.inr ⟨.excl (), rfl⟩; exact trivial)
  cases this
end W2c2

namespace W2c2
open Iris Iris.OFE Iris.Std
local notation "FM" => (fun V => Nat → Option V)
-- `Heap.total_singleton_inc_singleton_iff` (hypothesis 8, inst): necessary, V=Excl Unit (not total): singleton excl included in itself, excl not included in excl
theorem w2c2_65 : ¬ drop0% Heap.total_singleton_inc_singleton_iff 8 := fun h => by
  obtain ⟨z, hz⟩ := (@h FM Nat (Excl Unit) _ _ 0 (.excl ()) (.excl ())).mp ⟨fun _ => none, funext fun k => by rcases k with _ | k <;> rfl⟩
  cases hz
-- `Heap.singleton_inc_singleton_mono` (hypothesis 8, Hinc): necessary, V=BT (or): x=true, y=false: true not included in false
theorem w2c2_66 : ¬ drop0% Heap.singleton_inc_singleton_mono 8 := fun h => by
  obtain ⟨z, hz⟩ := @h FM Nat BT _ _ ⟨true⟩ ⟨false⟩ 0
  exact bt_ne_tf (z 0) ((congrFun hz 0).trans (Heap.get?_op (M := FM) _ z (i := 0)))
-- `Heap.instCancelableSingletonOfOptionSome` (hypothesis 7, H): necessary, V=BA, x=false: false&&true=false&&none, but frames singleton true and empty differ
theorem w2c2_67 : ¬ drop0% Heap.instCancelableSingletonOfOptionSome 7 := fun h => by
  have := (@h FM Nat BA _ _ ⟨false⟩ 0).cancelableN (n := 0) (y := fun k => if k = 0 then some ⟨true⟩ else none)
    (z := fun _ => none) (fun k => by rcases k with _ | k <;> exact trivial)
    (fun k => by rcases k with _ | k <;> exact .of_eq rfl) 0
  cases this
-- `Heap.instCancelableOfIdFree` (hypothesis 6, Hid): necessary, V=Unit (cancelable, not id-free): m=const (), frames empty and const () give equal products
theorem w2c2_68 : ¬ drop0% Heap.instCancelableOfIdFree 6 := fun h => by
  have := (@h FM Nat Unit _ _ (fun _ => some ()) (fun _ => ⟨fun _ _ => .of_eq rfl⟩)).cancelableN (n := 0)
    (y := fun _ => none) (z := fun _ => some ()) (fun k => by exact trivial) (fun k => .of_eq rfl) 0
  cases this
-- `Heap.disjoint_op_equiv_union` (hypothesis 7, Hd): necessary, V=BA, m1=const true, m2=const false: op gives false, union keeps true
theorem w2c2_69 : ¬ drop0% Heap.disjoint_op_equiv_union 7 := fun h => by
  have := @h FM Nat BA _ _ (fun _ => some ⟨true⟩) (fun _ => some ⟨false⟩) 0
  change (some ⟨false⟩ : Option BA) = some ⟨true⟩ at this
  cases this
-- `Heap.disjoint_op_eq_union` (hypothesis 7, H): necessary, V=BA, m1=const true, m2=const false: op gives false, union keeps true
theorem w2c2_70 : ¬ drop0% Heap.disjoint_op_eq_union 7 := fun h => by
  have := congrFun (@h FM Nat BA _ _ (fun _ => some ⟨true⟩) (fun _ => some ⟨false⟩)) 0
  change (some ⟨false⟩ : Option BA) = some ⟨true⟩ at this
  cases this
-- `Heap.valid0_disjoint_dom` (hypothesis 7, Hv): necessary, V=Excl Unit, m1=m2=const excl: domains overlap
theorem w2c2_71 : ¬ drop0% Heap.valid0_disjoint_dom 7 := fun h =>
  @h FM Nat (Excl Unit) _ _ (fun _ => some (.excl ())) (fun _ => some (.excl ())) (fun _ => by exact inferInstance) 0 ⟨rfl, rfl⟩
-- `Heap.valid0_disjoint_dom` (hypothesis 8, H): necessary, V=BA (all valid), m1=m2=const true: domains overlap
theorem w2c2_72 : ¬ drop0% Heap.valid0_disjoint_dom 8 := fun h =>
  @h FM Nat BA _ _ (fun _ => some ⟨true⟩) (fun _ => some ⟨true⟩) (fun _ => by exact trivial) 0 ⟨rfl, rfl⟩
-- `Heap.valid_disjoint_dom` (hypothesis 7, Hv): necessary, V=Excl Unit, m1=m2=const excl: domains overlap
theorem w2c2_73 : ¬ drop0% Heap.valid_disjoint_dom 7 := fun h =>
  @h FM Nat (Excl Unit) _ _ (fun _ => some (.excl ())) (fun _ => some (.excl ())) (fun _ => by exact inferInstance) 0 ⟨rfl, rfl⟩
-- `Heap.valid_disjoint_dom` (hypothesis 8, H): necessary, V=BA (all valid), m1=m2=const true: domains overlap
theorem w2c2_74 : ¬ drop0% Heap.valid_disjoint_dom 8 := fun h =>
  @h FM Nat BA _ _ (fun _ => some ⟨true⟩) (fun _ => some ⟨true⟩) (fun _ => by exact trivial) 0 ⟨rfl, rfl⟩
-- `Heap.inc_dom_inc` (hypothesis 7, Hinc): necessary, m1 full, m2 empty
theorem w2c2_75 : ¬ drop0% Heap.inc_dom_inc 7 := fun h => by
  have := @h FM Nat BA _ _ (fun _ => some ⟨true⟩) (fun _ => none) 0 rfl
  cases this
-- `Heap.map_mono_ord` (hypothesis 7, inst): necessary, V=Unit, V'=BA (not IncOrd), f=const false: none below some () but not below some false
theorem w2c2_76 : ¬ drop0% Heap.map_mono_ord 7 := fun h =>
  ba_not_inc (@h FM Nat Unit _ _ BA _ (fun _ => ⟨false⟩) (fun _ _ _ => by exact rfl) (fun _ => none) (fun _ => some ())
    (fun _ => by exact (inferInstance : Increasing ())) 0)
-- `Heap.map_mono_ord` (hypothesis 9, hf): necessary, V=BT (full order), V'=BU, f=id on bits: true below false in BT, not in BU
theorem w2c2_77 : ¬ drop0% Heap.map_mono_ord 9 := fun h => by
  have := @h FM Nat BT _ _ BU _ _ (fun x => ⟨x.b⟩) (fun _ => some ⟨true⟩) (fun _ => some ⟨false⟩) (fun _ => by exact Or.inr trivial) 0
  rcases this with e | e <;> cases e
-- `Heap.map_mono_ord` (hypothesis 12, Hinc): necessary, V=V'=BU, f=id, m1 full, m2 empty
theorem w2c2_78 : ¬ drop0% Heap.map_mono_ord 12 := fun h =>
  @h FM Nat BU _ _ BU _ _ id (fun _ _ e => e) (fun _ => some ⟨true⟩) (fun _ => none) 0
-- `Heap.map_mono` (hypothesis 8, hf): necessary, V=V'=BT, f=not: false included in true, true not included in false
theorem w2c2_79 : ¬ drop0% Heap.map_mono 8 := fun h => by
  obtain ⟨z, hz⟩ := @h FM Nat BT _ _ BT _ (fun x => ⟨!x.b⟩) (fun _ => some ⟨false⟩) (fun _ => some ⟨true⟩)
    ⟨fun _ => some ⟨true⟩, rfl⟩
  exact bt_ne_tf (z 0) ((congrFun hz 0).trans (Heap.get?_op (M := FM) _ z (i := 0)))
-- `Heap.map_mono` (hypothesis 11, Hinc): necessary, V=V'=BT, f=id, m1 full, m2 empty
theorem w2c2_80 : ¬ drop0% Heap.map_mono 11 := fun h => by
  obtain ⟨z, hz⟩ := @h FM Nat BT _ _ BT _ id (fun _ _ e => e) (fun _ => some ⟨true⟩) (fun _ => none)
  have := (congrFun hz 0).trans (Heap.get?_op (M := FM) _ z (i := 0))
  change (none : Option BT) = Op.op (α := Option BT) (some ⟨true⟩) (z 0) at this
  rcases hz0 : z 0 with _ | ⟨b⟩ <;> rw [hz0] at this <;> cases this
-- `Heap.instDiscrete` (hypothesis 4, HD): necessary, V=Excl TN (ORA not discrete): maps of excl 1 and excl 2 agree at step 0
theorem w2c2_81 : ¬ drop0% Heap.instDiscrete 4 := fun h => by
  have := congrFun ((@h FM Nat (Excl TN) _ _).discrete_0 (x := fun _ => some (.excl ⟨1⟩)) (y := fun _ => some (.excl ⟨2⟩))
    (fun _ => some_dist_some.mpr tn12)) 0
  simp at this
end W2c2

namespace W2c2
open Iris Iris.OFE Iris.Std
local notation "FM" => (fun V => Nat → Option V)
local notation "TM" => (fun V => Std.ExtTreeMap Nat V compare)
/-- Inserting the invalid BOV element into an ExtTreeMap gives an invalid map. -/
theorem tm_ins_inv {i : Nat} (hv : ∀ k, ✓{0} get? (M := TM) (insert (M := TM) (∅ : Std.ExtTreeMap Nat BOV compare) i (⟨true⟩ : BOV)) k) : False := by
  have := hv i
  rw [LawfulPartialMap.get?_insert_eq rfl] at this
  exact bov_invN (n := 0) this
-- `Heap.insert_updateP` (hypothesis 10, hx): necessary, V=BA, P=Q=False: hQ vacuous, insert m 0 true is valid so Q must be inhabited
theorem w2c2_82 : ¬ drop0% Heap.insert_updateP 10 := fun h => by
  obtain ⟨_, hq, _⟩ := @h FM Nat BA _ _ (fun _ => False) (fun _ => False) (fun _ => none) 0 ⟨true⟩ (fun _ hp => hp.elim) 0 none
    (fun k => by rcases k with _ | k <;> exact trivial)
  exact hq
-- `Heap.insert_updateP` (hypothesis 11, hQ): necessary, V=BA, P=True, Q=False: x~~>:True holds
theorem w2c2_83 : ¬ drop0% Heap.insert_updateP 11 := fun h => by
  obtain ⟨_, hq, _⟩ := @h FM Nat BA _ _ (fun _ => True) (fun _ => False) (fun _ => none) 0 ⟨true⟩ (fun _ _ hv => ⟨⟨true⟩, trivial, hv⟩) 0 none
    (fun k => by rcases k with _ | k <;> exact trivial)
  exact hq
-- `Heap.insert_updateP'` (hypothesis 9, hx): necessary, V=BA, P=False: no witness
theorem w2c2_84 : ¬ drop0% Heap.insert_updateP' 9 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h FM Nat BA _ _ (fun _ => False) (fun _ => none) 0 ⟨true⟩ 0 none
    (fun k => by rcases k with _ | k <;> exact trivial)
  exact hp
-- `Heap.insert_update` (hypothesis 9, h): necessary, V=BOV, x=false, y=true: valid update target invalid
theorem w2c2_85 : ¬ drop0% Heap.insert_update 9 := fun h =>
  bov_invN (n := 0) (@h FM Nat BOV _ _ (fun _ => none) 0 ⟨false⟩ ⟨true⟩ 0 none
    (fun k => by rcases k with _ | k; exact (rfl : false = false); exact trivial) 0)
-- `Heap.singleton_updateP` (hypothesis 9, hx): necessary, V=BA, P=Q=False
theorem w2c2_86 : ¬ drop0% Heap.singleton_updateP 9 := fun h => by
  obtain ⟨_, hq, _⟩ := @h FM Nat BA _ _ (fun _ => False) (fun _ => False) 0 ⟨true⟩ (fun _ hp => hp.elim) 0 none
    (fun k => by rcases k with _ | k <;> exact trivial)
  exact hq
-- `Heap.singleton_updateP` (hypothesis 10, hQ): necessary, V=BA, P=True, Q=False
theorem w2c2_87 : ¬ drop0% Heap.singleton_updateP 10 := fun h => by
  obtain ⟨_, hq, _⟩ := @h FM Nat BA _ _ (fun _ => True) (fun _ => False) 0 ⟨true⟩ (fun _ _ hv => ⟨⟨true⟩, trivial, hv⟩) 0 none
    (fun k => by rcases k with _ | k <;> exact trivial)
  exact hq
-- `Heap.singleton_updateP'` (hypothesis 8, hx): necessary, V=BA, P=False
theorem w2c2_88 : ¬ drop0% Heap.singleton_updateP' 8 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h FM Nat BA _ _ (fun _ => False) 0 ⟨true⟩ 0 none
    (fun k => by rcases k with _ | k <;> exact trivial)
  exact hp
-- `Heap.singleton_update` (hypothesis 8, h): necessary, V=BOV, x=false, y=true
theorem w2c2_89 : ¬ drop0% Heap.singleton_update 8 := fun h =>
  bov_invN (n := 0) (@h FM Nat BOV _ _ 0 ⟨false⟩ ⟨true⟩ 0 none
    (fun k => by rcases k with _ | k; exact (rfl : false = false); exact trivial) 0)
-- `Heap.alloc_updateP_strong_dep` (hypothesis 9, hI): necessary, I=False (not infinite), Q=False, ExtTreeMap: empty map valid
theorem w2c2_90 : ¬ drop0% Heap.alloc_updateP_strong_dep 9 := fun h => by
  obtain ⟨_, hq, _⟩ := @h TM Nat BA _ _ (fun _ => False) (fun _ => False) ∅ (fun _ => ⟨true⟩)
    (fun _ _ hi => hi.elim) (fun _ _ hi => hi.elim) 0 none emp_valid0
  exact hq
-- `Heap.alloc_updateP_strong_dep` (hypothesis 11, hQ): necessary, I=True, Q=False, V=BA
theorem w2c2_91 : ¬ drop0% Heap.alloc_updateP_strong_dep 11 := fun h => by
  obtain ⟨_, hq, _⟩ := @h TM Nat BA _ _ (fun _ => False) (fun _ => True) ∅ (fun _ => ⟨true⟩)
    PredInfinite.true (fun _ _ _ => by exact trivial) 0 none emp_valid0
  exact hq
-- `Heap.alloc_updateP_strong` (hypothesis 9, hI): necessary, I=False, Q=False
theorem w2c2_92 : ¬ drop0% Heap.alloc_updateP_strong 9 := fun h => by
  obtain ⟨_, hq, _⟩ := @h TM Nat BA _ _ (fun _ => False) (fun _ => False) ∅ ⟨true⟩
    (by exact trivial) (fun _ _ hi => hi.elim) 0 none emp_valid0
  exact hq
-- `Heap.alloc_updateP_strong` (hypothesis 11, hQ): necessary, I=True, Q=False
theorem w2c2_93 : ¬ drop0% Heap.alloc_updateP_strong 11 := fun h => by
  obtain ⟨_, hq, _⟩ := @h TM Nat BA _ _ (fun _ => False) (fun _ => True) ∅ ⟨true⟩
    PredInfinite.true (by exact trivial) 0 none emp_valid0
  exact hq
-- `Heap.alloc_updateP` (hypothesis 9, hx): necessary, V=BOV, x=true invalid, Q = {insert empty i true}: all invalid
theorem w2c2_94 : ¬ drop0% Heap.alloc_updateP 9 := fun h => by
  obtain ⟨y, ⟨i, hy⟩, hv⟩ := @h TM Nat BOV _ _ _ (fun y => ∃ i, y = insert (M := TM) ∅ i ⟨true⟩) ∅ ⟨true⟩
    (fun i _ => ⟨i, rfl⟩) 0 none emp_valid0
  subst hy
  exact tm_ins_inv hv
-- `Heap.alloc_updateP` (hypothesis 10, hQ): necessary, Q=False, x valid
theorem w2c2_95 : ¬ drop0% Heap.alloc_updateP 10 := fun h => by
  obtain ⟨_, hq, _⟩ := @h TM Nat BA _ _ _ (fun _ => False) ∅ ⟨true⟩ (by exact trivial) 0 none emp_valid0
  exact hq
-- `Heap.alloc_updateP_cofinite` (hypothesis 11, hQ): necessary, Q=False, x valid
theorem w2c2_96 : ¬ drop0% Heap.alloc_updateP_cofinite 11 := fun h => by
  obtain ⟨_, hq, _⟩ := @h TM Nat BA _ _ _ (fun _ => False) ∅ ⟨true⟩ [] (by exact trivial) 0 none emp_valid0
  exact hq
-- `Heap.alloc_updateP_strong_dep'` (hypothesis 8, hI): necessary, I=False: no witness i
theorem w2c2_97 : ¬ drop0% Heap.alloc_updateP_strong_dep' 8 := fun h => by
  obtain ⟨_, ⟨_, hi, _⟩, _⟩ := @h TM Nat BA _ _ (fun _ => False) ∅ (fun _ => ⟨true⟩) (fun _ _ hi => hi.elim) 0 none emp_valid0
  exact hi
-- `Heap.alloc_updateP_strong_dep'` (hypothesis 9, hf): necessary, V=BOV, f=const true invalid: every candidate invalid
theorem w2c2_98 : ¬ drop0% Heap.alloc_updateP_strong_dep' 9 := fun h => by
  obtain ⟨y, ⟨i, _, hy, _⟩, hv⟩ := @h TM Nat BOV _ _ (fun _ => True) ∅ (fun _ => ⟨true⟩) PredInfinite.true 0 none emp_valid0
  subst hy
  exact tm_ins_inv hv
-- `Heap.alloc_updateP_strong'` (hypothesis 8, hI): necessary, I=False: no witness i
theorem w2c2_99 : ¬ drop0% Heap.alloc_updateP_strong' 8 := fun h => by
  obtain ⟨_, ⟨_, hi, _⟩, _⟩ := @h TM Nat BA _ _ (fun _ => False) ∅ ⟨true⟩ (by exact trivial) 0 none emp_valid0
  exact hi
-- `Heap.alloc_updateP_strong'` (hypothesis 9, hx): necessary, V=BOV, x=true invalid
theorem w2c2_100 : ¬ drop0% Heap.alloc_updateP_strong' 9 := fun h => by
  obtain ⟨y, ⟨i, _, hy, _⟩, hv⟩ := @h TM Nat BOV _ _ (fun _ => True) ∅ ⟨true⟩ PredInfinite.true 0 none emp_valid0
  subst hy
  exact tm_ins_inv hv
-- `Heap.alloc_updateP'` (hypothesis 8, hx): necessary, V=BOV, x=true invalid
theorem w2c2_101 : ¬ drop0% Heap.alloc_updateP' 8 := fun h => by
  obtain ⟨y, ⟨i, hy, _⟩, hv⟩ := @h TM Nat BOV _ _ _ ∅ ⟨true⟩ 0 none emp_valid0
  subst hy
  exact tm_ins_inv hv
-- `Heap.alloc_updateP_cofinite'` (hypothesis 9, hx): necessary, V=BOV, x=true invalid
theorem w2c2_102 : ¬ drop0% Heap.alloc_updateP_cofinite' 9 := fun h => by
  obtain ⟨y, ⟨i, _, hy, _⟩, hv⟩ := @h TM Nat BOV _ _ _ ∅ ⟨true⟩ [] 0 none emp_valid0
  subst hy
  exact tm_ins_inv hv
-- `Heap.alloc_unit_singleton_updateP` (hypothesis 9, hu): necessary, V=UZ (one point, never valid): u is a unit, u~~>:False vacuous, empty map valid
theorem w2c2_103 : ¬ drop0% Heap.alloc_unit_singleton_updateP 9 := fun h => by
  obtain ⟨_, hq, _⟩ := @h FM Nat UZ _ _ (fun _ => False) (fun _ => False) ⟨⟩ 0 (fun _ => rfl) uz_upd
    (fun _ hp => hp.elim) 0 none emp_valid0
  exact hq
-- `Heap.alloc_unit_singleton_updateP` (hypothesis 10, hid): necessary, V=E3: u=e valid not unit, P=(=e), frame singleton 0 y valid but e•y=bot
theorem w2c2_104 : ¬ drop0% Heap.alloc_unit_singleton_updateP 10 := fun h => by
  obtain ⟨m', hm', hv⟩ := @h FM Nat E3 _ _ (· = E3.e) (· = PartialMap.singleton (M := FM) 0 E3.e) E3.e 0
    (by exact (show E3.e ≠ .bot by decide)) (fun _ _ hv => ⟨E3.e, rfl, hv⟩) (fun _ hy => by subst hy; rfl) 0
    (some (PartialMap.singleton (M := FM) 0 E3.y))
    (fun k => by rcases k with _ | k; exact (show E3.y ≠ .bot by decide); exact trivial)
  subst hm'
  exact absurd rfl (show E3.bot ≠ E3.bot from hv 0)
-- `Heap.alloc_unit_singleton_updateP` (hypothesis 11, hx): necessary, V=BU, u=false unit, P=Q=False
theorem w2c2_105 : ¬ drop0% Heap.alloc_unit_singleton_updateP 11 := fun h => by
  obtain ⟨_, hq, _⟩ := @h FM Nat BU _ _ (fun _ => False) (fun _ => False) ⟨false⟩ 0 (by exact trivial)
    (fun x => by rcases x with ⟨_ | _⟩ <;> rfl) (fun _ hp => hp.elim) 0 none emp_valid0
  exact hq
-- `Heap.alloc_unit_singleton_updateP` (hypothesis 12, hQ): necessary, V=BU, u=false, P=True, Q=False
theorem w2c2_106 : ¬ drop0% Heap.alloc_unit_singleton_updateP 12 := fun h => by
  obtain ⟨_, hq, _⟩ := @h FM Nat BU _ _ (fun _ => True) (fun _ => False) ⟨false⟩ 0 (by exact trivial)
    (fun x => by rcases x with ⟨_ | _⟩ <;> rfl) (fun _ _ hv => ⟨⟨false⟩, trivial, hv⟩) 0 none emp_valid0
  exact hq
-- `Heap.alloc_unit_singleton_updateP'` (hypothesis 8, hu): necessary, V=UZ, P=False
theorem w2c2_107 : ¬ drop0% Heap.alloc_unit_singleton_updateP' 8 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h FM Nat UZ _ _ (fun _ => False) ⟨⟩ 0 (fun _ => rfl) uz_upd 0 none emp_valid0
  exact hp
-- `Heap.alloc_unit_singleton_updateP'` (hypothesis 9, hid): necessary, V=E3, u=e, frame singleton 0 y
theorem w2c2_108 : ¬ drop0% Heap.alloc_unit_singleton_updateP' 9 := fun h => by
  obtain ⟨m', ⟨y, hm', hy⟩, hv⟩ := @h FM Nat E3 _ _ (· = E3.e) E3.e 0
    (by exact (show E3.e ≠ .bot by decide)) (fun _ _ hv => ⟨E3.e, rfl, hv⟩) 0
    (some (PartialMap.singleton (M := FM) 0 E3.y))
    (fun k => by rcases k with _ | k; exact (show E3.y ≠ .bot by decide); exact trivial)
  subst hm' hy
  exact absurd rfl (show E3.bot ≠ E3.bot from hv 0)
-- `Heap.alloc_unit_singleton_updateP'` (hypothesis 10, hx): necessary, V=BU, u=false, P=False
theorem w2c2_109 : ¬ drop0% Heap.alloc_unit_singleton_updateP' 10 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h FM Nat BU _ _ (fun _ => False) ⟨false⟩ 0 (by exact trivial)
    (fun x => by rcases x with ⟨_ | _⟩ <;> rfl) 0 none emp_valid0
  exact hp
-- `Heap.alloc_unit_singleton_update` (hypothesis 8, hu): necessary, V=UZ: singleton never valid
theorem w2c2_110 : ¬ drop0% Heap.alloc_unit_singleton_update 8 := fun h =>
  @h FM Nat UZ _ _ ⟨⟩ 0 ⟨⟩ (fun _ => rfl) (fun _ mz hv => by cases mz <;> exact hv.elim) 0 none emp_valid0 0
-- `Heap.alloc_unit_singleton_update` (hypothesis 9, hid): necessary, V=E3, u=y=e, frame singleton 0 y: e•y=bot
theorem w2c2_111 : ¬ drop0% Heap.alloc_unit_singleton_update 9 := fun h => absurd rfl (show E3.bot ≠ E3.bot from
  @h FM Nat E3 _ _ E3.e 0 E3.e (by exact (show E3.e ≠ .bot by decide)) (fun _ _ hv => hv) 0
    (some (PartialMap.singleton (M := FM) 0 E3.y))
    (fun k => by rcases k with _ | k; exact (show E3.y ≠ .bot by decide); exact trivial) 0)
-- `Heap.alloc_unit_singleton_update` (hypothesis 10, h): necessary, V=BOV, u=false, y=true invalid
theorem w2c2_112 : ¬ drop0% Heap.alloc_unit_singleton_update 10 := fun h =>
  bov_invN (n := 0) (@h FM Nat BOV _ _ ⟨false⟩ 0 ⟨true⟩ (by exact (rfl : false = false))
    (fun x => by rcases x with ⟨_ | _⟩ <;> rfl) 0 none emp_valid0 0)
end W2c2

namespace W2c2
open Iris Iris.OFE Iris.Std
local notation "FM" => (fun V => Nat → Option V)
local notation "TM" => (fun V => Std.ExtTreeMap Nat V compare)
/-- The function map with the single entry `0 ↦ x`. -/
abbrev s0 {V : Type} (x : V) : Nat → Option V := PartialMap.singleton (M := FM) 0 x
theorem opt_none_some {α : Type} [OFE α] {n} {a : α} : ¬ (none : Option α) ≡{n}≡ some a := fun h => by
  simp [OFE.Dist, Option.Forall₂] at h
theorem ba_some_dist {n} : ¬ (some (⟨true⟩ : BA)) ≡{n}≡ some ⟨false⟩ := fun h => by
  have h' : (⟨true⟩ : BA) = ⟨false⟩ := some_dist_some.mp h
  cases h'
theorem bx_some_dist {n} : ¬ (some (⟨true⟩ : BX)) ≡{n}≡ some ⟨false⟩ := fun h => by
  have h' : (⟨true⟩ : BX) = ⟨false⟩ := some_dist_some.mp h
  cases h'
-- `Heap.local_update` (hypothesis 9, h): necessary, V=BOV, m1=m2=empty, m1'=const true invalid
theorem w2c2_113 : ¬ drop0% Heap.local_update 9 := fun h =>
  bov_invN (n := 0) ((@h FM Nat BOV _ _ (fun _ => none) (fun _ => none) (fun _ => some ⟨true⟩) (fun _ => none) 0 none
    emp_valid0 (.of_eq rfl)).1 0)
-- `Heap.alloc_local_update` (hypothesis 9, hi): necessary, V=BA, m1=singleton 0 false, m2 empty, x=true, frame m1: true vs true&&false
theorem w2c2_114 : ¬ drop0% Heap.alloc_local_update 9 := fun h =>
  ba_some_dist ((@h FM Nat BA _ _ (s0 ⟨false⟩) (fun _ => none) 0 ⟨true⟩ (by exact trivial) 0 (some (s0 ⟨false⟩))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.alloc_local_update` (hypothesis 10, hx): necessary, V=BOV, m1=m2 empty, x=true invalid
theorem w2c2_115 : ¬ drop0% Heap.alloc_local_update 10 := fun h =>
  bov_invN (n := 0) ((@h FM Nat BOV _ _ (fun _ => none) (fun _ => none) 0 ⟨true⟩ rfl 0 none emp_valid0 (.of_eq rfl)).1 0)
-- `Heap.alloc_singleton_local_update` (hypothesis 8, hi): necessary, V=BA, m=singleton 0 false, x=true, frame m: true vs true&&false
theorem w2c2_116 : ¬ drop0% Heap.alloc_singleton_local_update 8 := fun h =>
  ba_some_dist ((@h FM Nat BA _ _ (s0 ⟨false⟩) 0 ⟨true⟩ (by exact trivial) 0 (some (s0 ⟨false⟩))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.alloc_singleton_local_update` (hypothesis 9, hx): necessary, V=BOV, m empty, x=true invalid
theorem w2c2_117 : ¬ drop0% Heap.alloc_singleton_local_update 9 := fun h =>
  bov_invN (n := 0) ((@h FM Nat BOV _ _ (fun _ => none) 0 ⟨true⟩ rfl 0 none emp_valid0 (.of_eq rfl)).1 0)
-- `Heap.insert_local_update` (hypothesis 12, hi1): necessary, V=BA, m1=singleton 0 false, m2=singleton 0 true, all values true, frame singleton 0 false
theorem w2c2_118 : ¬ drop0% Heap.insert_local_update 12 := fun h =>
  ba_some_dist ((@h FM Nat BA _ _ (s0 ⟨false⟩) (s0 ⟨true⟩) 0 ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨true⟩ rfl (LocalUpdate.id _) 0
    (some (s0 ⟨false⟩)) (fun k => by rcases k with _ | k <;> exact trivial)
    (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.insert_local_update` (hypothesis 13, hi2): necessary, V=BX (xor), m1=singleton 0 true, m2 empty, all values true, frame m1: true xor true = false
theorem w2c2_119 : ¬ drop0% Heap.insert_local_update 13 := fun h =>
  bx_some_dist ((@h FM Nat BX _ _ (s0 ⟨true⟩) (fun _ => none) 0 ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨true⟩ rfl (LocalUpdate.id _) 0
    (some (s0 ⟨true⟩)) (fun k => by rcases k with _ | k <;> exact trivial)
    (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.insert_local_update` (hypothesis 14, h): necessary, V=BOV, m1=m2=singleton 0 false, x'=true invalid
theorem w2c2_120 : ¬ drop0% Heap.insert_local_update 14 := fun h =>
  bov_invN (n := 0) ((@h FM Nat BOV _ _ (s0 ⟨false⟩) (s0 ⟨false⟩) 0 ⟨false⟩ ⟨false⟩ ⟨true⟩ ⟨true⟩ rfl rfl 0 none
    (fun k => by rcases k with _ | k; exact (rfl : false = false); exact trivial) (.of_eq rfl)).1 0)
-- `Heap.singleton_local_update_any` (hypothesis 10, h): necessary, V=BOV, m=singleton 0 false, y=false, x'=true invalid
theorem w2c2_121 : ¬ drop0% Heap.singleton_local_update_any 10 := fun h =>
  bov_invN (n := 0) ((@h FM Nat BOV _ _ (s0 ⟨false⟩) 0 ⟨false⟩ ⟨true⟩ ⟨false⟩ 0 none
    (fun k => by rcases k with _ | k; exact (rfl : false = false); exact trivial) (.of_eq rfl)).1 0)
-- `Heap.singleton_local_update` (hypothesis 11, hi): necessary, V=BA, m=singleton 0 false, all values true, frame singleton 0 false
theorem w2c2_122 : ¬ drop0% Heap.singleton_local_update 11 := fun h =>
  ba_some_dist ((@h FM Nat BA _ _ (s0 ⟨false⟩) 0 ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨true⟩ (LocalUpdate.id _) 0
    (some (s0 ⟨false⟩)) (fun k => by rcases k with _ | k <;> exact trivial)
    (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.singleton_local_update` (hypothesis 12, h): necessary, V=BOV, m=singleton 0 false, x'=true invalid
theorem w2c2_123 : ¬ drop0% Heap.singleton_local_update 12 := fun h =>
  bov_invN (n := 0) ((@h FM Nat BOV _ _ (s0 ⟨false⟩) 0 ⟨false⟩ ⟨false⟩ ⟨true⟩ ⟨false⟩ rfl 0 none
    (fun k => by rcases k with _ | k; exact (rfl : false = false); exact trivial) (.of_eq rfl)).1 0)
-- `Heap.delete_local_update` (hypothesis 9, inst): necessary, V=BA, x=true not exclusive, m1=m2=frame=singleton 0 true: deleting leaves the frame
theorem w2c2_124 : ¬ drop0% Heap.delete_local_update 9 := fun h =>
  opt_none_some ((@h FM Nat BA _ _ (s0 ⟨true⟩) (s0 ⟨true⟩) 0 ⟨true⟩ rfl 0 (some (s0 ⟨true⟩))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.delete_local_update` (hypothesis 10, hi): necessary, V=Excl Unit, m1=frame=singleton 0 excl, m2 empty
theorem w2c2_125 : ¬ drop0% Heap.delete_local_update 10 := fun h =>
  opt_none_some ((@h FM Nat (Excl Unit) _ _ (s0 (.excl ())) (fun _ => none) 0 (.excl ()) inferInstance 0 (some (s0 (.excl ())))
    (fun k => by rcases k with _ | k <;> first | exact trivial | simp) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.delete_singleton_local_update` (hypothesis 8, inst): necessary, V=BA, x=true, m=frame=singleton 0 true
theorem w2c2_126 : ¬ drop0% Heap.delete_singleton_local_update 8 := fun h =>
  opt_none_some ((@h FM Nat BA _ _ (s0 ⟨true⟩) 0 ⟨true⟩ 0 (some (s0 ⟨true⟩))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.delete_local_update_cancelable` (hypothesis 9, inst): necessary, V=Unit, mx=some () not cancelable, m1=m2=frame=singleton 0 ()
theorem w2c2_127 : ¬ drop0% Heap.delete_local_update_cancelable 9 := fun h =>
  opt_none_some ((@h FM Nat Unit _ _ (s0 ()) (s0 ()) 0 (some ()) rfl rfl 0 (some (s0 ()))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.delete_local_update_cancelable` (hypothesis 10, hi1): necessary, V=NP (x•y=x+y+1, some 0 cancelable), m2=singleton 0 0, frame singleton 0 1, m1=singleton 0 2
theorem w2c2_128 : ¬ drop0% Heap.delete_local_update_cancelable 10 := fun h =>
  opt_none_some ((@h FM Nat NP _ _ (s0 ⟨2⟩) (s0 ⟨0⟩) 0 (some ⟨0⟩) inferInstance rfl 0 (some (s0 ⟨1⟩))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.delete_local_update_cancelable` (hypothesis 11, hi2): necessary, V=NP, m1=frame=singleton 0 0, m2 empty
theorem w2c2_129 : ¬ drop0% Heap.delete_local_update_cancelable 11 := fun h =>
  opt_none_some ((@h FM Nat NP _ _ (s0 ⟨0⟩) (fun _ => none) 0 (some ⟨0⟩) inferInstance rfl 0 (some (s0 ⟨0⟩))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.delete_singleton_local_update_cancelable` (hypothesis 8, inst): necessary, V=Unit, x=(), m=frame=singleton 0 ()
theorem w2c2_130 : ¬ drop0% Heap.delete_singleton_local_update_cancelable 8 := fun h =>
  opt_none_some ((@h FM Nat Unit _ _ (s0 ()) 0 () rfl 0 (some (s0 ()))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.delete_singleton_local_update_cancelable` (hypothesis 9, hi): necessary, V=NP, x=0, m=singleton 0 1, frame singleton 0 0
theorem w2c2_131 : ¬ drop0% Heap.delete_singleton_local_update_cancelable 9 := fun h =>
  opt_none_some ((@h FM Nat NP _ _ (s0 ⟨1⟩) 0 ⟨0⟩ inferInstance 0 (some (s0 ⟨0⟩))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0)
-- `Heap.insert_alloc_local_update` (hypothesis 11, hi1): necessary, V=Option BA (unit none), m1=frame=singleton 0 (some true), m2 empty, x=x'=y'=none
theorem w2c2_132 : ¬ drop0% Heap.insert_alloc_local_update 11 := fun h =>
  opt_none_some (some_dist_some.mp ((@h FM Nat (Option BA) _ _ (s0 (some ⟨true⟩)) (fun _ => none) 0 none none none rfl
    (LocalUpdate.id _) 0 (some (s0 (some ⟨true⟩)))
    (fun k => by rcases k with _ | k <;> exact trivial) (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).2 0))
-- `Heap.insert_alloc_local_update` (hypothesis 12, hi2): necessary, V=Option BA, m1=m2=singleton 0 (some true), x=x'=some true, y'=none, no frame
theorem w2c2_133 : ¬ drop0% Heap.insert_alloc_local_update 12 := fun h =>
  opt_none_some (some_dist_some.mp ((@h FM Nat (Option BA) _ _ (s0 (some ⟨true⟩)) (s0 (some ⟨true⟩)) 0 (some ⟨true⟩)
    (some ⟨true⟩) none rfl (LocalUpdate.id _) 0 none
    (fun k => by rcases k with _ | k <;> exact trivial) (.of_eq rfl)).2 0)).symm
-- `Heap.insert_alloc_local_update` (hypothesis 13, h): necessary, V=Option BOV, x'=some true invalid
theorem w2c2_134 : ¬ drop0% Heap.insert_alloc_local_update 13 := fun h =>
  bov_invN (n := 0) ((@h FM Nat (Option BOV) _ _ (s0 (some ⟨false⟩)) (fun _ => none) 0 (some ⟨false⟩) (some ⟨true⟩) none
    rfl rfl 0 (some (s0 (some ⟨false⟩)))
    (fun k => by rcases k with _ | k; exact (rfl : false = false); exact trivial)
    (fun k => by rcases k with _ | k <;> exact .of_eq rfl)).1 0)
-- `PartialMap.instNonExpansiveMap` (hypothesis 8, hne): necessary, V=TN, f a = if a=1 then 0 else 1 not non-expansive
theorem w2c2_135 : ¬ drop0% PartialMap.instNonExpansiveMap 8 := fun h => by
  have := (@h Nat FM _ TN TN _ _ (fun a => if a.v = 1 then ⟨0⟩ else ⟨1⟩)).ne (n := 0)
    (x₁ := fun _ => some ⟨1⟩) (x₂ := fun _ => some ⟨2⟩) (fun _ => some_dist_some.mpr tn12) 0
  change (some ⟨0⟩ : Option TN) ≡{0}≡ some ⟨1⟩ at this
  simp [some_dist_some, tn_dist] at this
-- `PartialMap.map_ne` (hypothesis 11, heq): necessary, V=Unit to AN, f=const 0, g=const 1
theorem w2c2_136 : ¬ drop0% PartialMap.map_ne 11 := fun h => by
  have := @h Nat FM _ Unit AN 0 (fun _ => some ()) _ _ (fun _ => ⟨0⟩) (fun _ => ⟨1⟩) 0
  change (some ⟨0⟩ : Option AN) ≡{0}≡ some ⟨1⟩ at this
  simp [some_dist_some, an_dist] at this
-- `PartialMap.instRFunctorAffine` (hypothesis 5, inst): necessary, F=constOF BA (not affine): maps over BA not IncOrd (as instIncOrd)
theorem w2c2_137 : ¬ drop0% PartialMap.instRFunctorAffine 5 := fun h =>
  ba_ord_tf ((@h Nat FM _ (constOF BA) _).affine (α := Unit) (β := Unit) |>.inc_ord
    (x := fun _ => some ⟨true⟩) (y := fun _ => some ⟨false⟩) ⟨fun _ => some ⟨false⟩, rfl⟩ 0)
-- `PartialMap.bigOpM_dist_2` (hypothesis 8, inst): necessary, dependent: AN with constant-zero op (z_bad: not MonoidOps), empty ExtTreeMaps make both premises hold
theorem w2c2_19 : ¬ indep0% PartialMap.bigOpM_dist_2 8 := fun h =>
  z_bad (@h TM Nat AN zAN ⟨0⟩ Unit _ _ _ (fun _ _ => ⟨0⟩) (fun _ _ => ⟨0⟩) ∅ ∅ 0 (by exact fun _ => .of_eq rfl)
    (fun h1 _ _ => by simp [LawfulPartialMap.get?_empty] at h1))
-- `PartialMap.bigOpM_dist_2` (hypothesis 15, hm): necessary, AN with +, Phi=Psi=const 1, m1 empty, m2={0:()} (ExtTreeMap): big sums 0 vs 1
theorem w2c2_20 : ¬ drop0% PartialMap.bigOpM_dist_2 15 := fun h => by
  have := @h TM Nat AN addAN ⟨0⟩ Unit _ _ _ _ (fun _ _ => ⟨1⟩) (fun _ _ => ⟨1⟩) ∅ (PartialMap.singleton (M := TM) 0 ()) 0
    (fun h1 _ _ => by simp [LawfulPartialMap.get?_empty] at h1)
  rw [Algebra.BigOpM.bigOpM_empty, Algebra.BigOpM.bigOpM_singleton_eq] at this
  exact absurd (congrArg AN.v (an_dist.mp this)) (by decide)
-- `PartialMap.bigOpM_dist_2` (hypothesis 16, hf): necessary, AN with +, m1=m2={0:()}, Phi=const 0, Psi=const 1: 0 vs 1
theorem w2c2_21 : ¬ drop0% PartialMap.bigOpM_dist_2 16 := fun h => by
  have := @h TM Nat AN addAN ⟨0⟩ Unit _ _ _ _ (fun _ _ => ⟨0⟩) (fun _ _ => ⟨1⟩) (PartialMap.singleton (M := TM) 0 ())
    (PartialMap.singleton (M := TM) 0 ()) 0 (by exact fun _ => .of_eq rfl)
  rw [Algebra.BigOpM.bigOpM_singleton_eq, Algebra.BigOpM.bigOpM_singleton_eq] at this
  exact absurd (congrArg AN.v (an_dist.mp this)) (by decide)
end W2c2

