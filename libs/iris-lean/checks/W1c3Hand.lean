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
namespace W1c3
open Iris Iris.OFE

/-- Bool, or, core only at true (itself), valid iff false, order: target is true. -/
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

/-- Bool, or, unit false (total core = false), all valid, order is implication. -/
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
instance buTotal : IsTotal BU := ⟨fun _ => ⟨_, rfl⟩⟩

/-- Bool, or, core is identity (total), valid iff false, order is implication. -/
structure BL where b : Bool
instance : OFE BL := OFE.ofDiscrete BL
instance : OFE.Discrete BL := ⟨fun h => h⟩
def blData : DiscreteORAData BL where
  pcore x := some x
  op x y := ⟨or x.b y.b⟩
  Valid x := x.b = false
  Order x y := (or (!x.b) y.b) = true
  assoc x y z := congrArg BL.mk (Bool.or_assoc x.b y.b z.b).symm
  comm x y := congrArg BL.mk (Bool.or_comm x.b y.b)
  pcore_op_left x cx h := by cases h; rcases x with ⟨_|_⟩ <;> rfl
  pcore_idem x cx h := by cases h; rfl
  valid_op_left x y h := by simp at h; exact h.1
  ord_trans x y z := by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> decide
  op_mono_left x y z := by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> decide
  valid_of_ord x y := by rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> decide
  pcore_mono x y cx h e := ⟨y, rfl, by cases e; exact h⟩
  pcore_order_op x cx e y := ⟨_, rfl, by cases e; rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rfl⟩
  pcore_increasing x cx e y := by cases e; rcases x with ⟨_|_⟩ <;> rcases y with ⟨_|_⟩ <;> rfl
  increasing_closed _ y _ _ z := by rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> rfl
instance blORA : ORA BL := ORA.ofDiscreteORAData blData
instance blTotal : IsTotal BL := ⟨fun _ => ⟨_, rfl⟩⟩

/-- Bool, xor, no core, all valid, empty order. -/
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

/-- Bool, or, no core, all valid, full order. -/
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

end W1c3
namespace W1c3
open Iris Iris.OFE

/-- One-point ORA, never valid, step-indexed order holding only at step 0, no core. -/
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
theorem uz_not_inc : ¬ Increasing (⟨⟩ : UZ) := fun h => h.increasing ⟨⟩

/-- One-point ORA, valid only at step 0, empty order, no core. -/
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

/-- Truncation OFE on naturals (as TN of Probe1): op x y = x + y + 1, never valid, empty order, no core. -/
structure TI where v : Nat
instance : OFE TI where
  Dist n x y := min x.v (n+1) = min y.v (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b)
      simp only [TI.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show min x.v (m+1) = min y.v (m+1); omega
instance : Op TI where
  op x y := ⟨x.v + y.v + 1⟩
  op_ne := ⟨fun n y z h => by     have h' : min y.v (n+1) = min z.v (n+1) := h; show min _ (n+1) = min _ (n+1); simp only; omega⟩
  assoc {x y z} := congrArg TI.mk (show x.v + (y.v + z.v + 1) + 1 = (x.v + y.v + 1) + z.v + 1 by omega)
  comm {x y} := congrArg TI.mk (show x.v + y.v + 1 = y.v + x.v + 1 by omega)
instance : PCore TI where
  pcore _ := none
  pcore_ne _ h := (by cases h)
  pcore_idem h := (by cases h)
instance : Valid TI where
  ValidN _ _ := False
  Valid _ := False
  validN_ne _ h := h
  valid_iff_validN := ⟨False.elim, fun h => h 0⟩
  validN_succ h := h
instance : Ordered TI where
  OrderN _ _ _ := False
  Order _ _ := False
  ordN_ne _ _ h := h
  ordN_succ h := h
  ordN_trans h _ := h
  ord_trans h _ := h
  ordN_of_ord _ h := h
instance tiORA : ORA TI where
  validN_op_left h := h
  pcore_op_left h := (by cases h)
  extend h _ := h.elim
  op_monoN_left_ord _ h := h
  op_mono_left_ord _ h := h
  validN_of_ordN h _ := h.elim
  pcore_monoN_ord _ h := (by cases h)
  pcore_mono_ord _ h := (by cases h)
  pcore_order_op h := (by cases h)
  pcore_increasing h := (by cases h)
  increasing_closed hx _ := ⟨fun y => (hx.increasing y).elim⟩
  ordN_extend _ h := h.elim
theorem ti_dist {n} {x y : TI} : x ≡{n}≡ y ↔ min x.v (n+1) = min y.v (n+1) := Iff.rfl

/-- Truncation OFE on naturals: op is max, all valid, empty order, no core. 0 is discrete, 1 ≡{0} 2. -/
structure TM where v : Nat
instance : OFE TM where
  Dist n x y := min x.v (n+1) = min y.v (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b)
      simp only [TM.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show min x.v (m+1) = min y.v (m+1); omega
theorem tm_dist {n} {x y : TM} : x ≡{n}≡ y ↔ min x.v (n+1) = min y.v (n+1) := Iff.rfl
instance : Op TM where
  op x y := ⟨max x.v y.v⟩
  op_ne := ⟨fun n y z h => by     have h' : min y.v (n+1) = min z.v (n+1) := h; show min _ (n+1) = min _ (n+1); simp only; omega⟩
  assoc {x y z} := congrArg TM.mk (show max x.v (max y.v z.v) = max (max x.v y.v) z.v by omega)
  comm {x y} := congrArg TM.mk (show max x.v y.v = max y.v x.v by omega)
instance : PCore TM where
  pcore _ := none
  pcore_ne _ h := (by cases h)
  pcore_idem h := (by cases h)
instance : Valid TM where
  ValidN _ _ := True
  Valid _ := True
  validN_ne _ h := h
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ h := h
instance : Ordered TM where
  OrderN _ _ _ := False
  Order _ _ := False
  ordN_ne _ _ h := h
  ordN_succ h := h
  ordN_trans h _ := h
  ord_trans h _ := h
  ordN_of_ord _ h := h
instance tmORA : ORA TM where
  validN_op_left _ := trivial
  pcore_op_left h := (by cases h)
  extend {n x y₁ y₂} _ h :=
    ⟨if y₁.v ≤ n then y₁ else x, if y₂.v ≤ n then y₂ else x, by
      have h' : min x.v (n+1) = min (max y₁.v y₂.v) (n+1) := h
      cases x; show _ = TM.mk _; simp only at h' ⊢; congr 1; split <;> split <;> (try simp only) <;> omega,
     by
      have h' : min x.v (n+1) = min (max y₁.v y₂.v) (n+1) := h
      show min _ (n+1) = min _ (n+1); split <;> (try simp only) <;> omega,
     by
      have h' : min x.v (n+1) = min (max y₁.v y₂.v) (n+1) := h
      show min _ (n+1) = min _ (n+1); split <;> (try simp only) <;> omega⟩
  op_monoN_left_ord _ h := h
  op_mono_left_ord _ h := h
  validN_of_ordN _ _ := trivial
  pcore_monoN_ord _ h := (by cases h)
  pcore_mono_ord _ h := (by cases h)
  pcore_order_op h := (by cases h)
  pcore_increasing h := (by cases h)
  increasing_closed hx _ := ⟨fun y => (hx.increasing y).elim⟩
  ordN_extend _ h := h.elim
instance tm0disc : DiscreteE (⟨0⟩ : TM) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩
theorem tm12 : (⟨1⟩ : TM) ≡{0}≡ ⟨2⟩ := rfl

end W1c3
namespace W1c3
open Iris Iris.OFE

-- helper instances (no backticked names)
theorem bxOrdInc : OrdInc BX := ⟨fun h => False.elim h, fun h => False.elim h⟩
theorem btIncOrd : IncOrd BT := ⟨fun _ => trivial⟩
instance bovCancTrue : ORA.Cancelable (⟨true⟩ : BOV) := ⟨fun hv _ => by cases hv⟩
instance bovCancFalse : ORA.Cancelable (⟨false⟩ : BOV) := ⟨fun {_ y z} _ he => by
  rcases y with ⟨_|_⟩ <;> rcases z with ⟨_|_⟩ <;> first | rfl | exact he⟩
instance bovIdFreeTrue : ORA.IdFree (⟨true⟩ : BOV) := ⟨fun _ hv _ => by cases hv⟩
instance ti0disc : DiscreteE (⟨0⟩ : TI) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩
instance buNotNE : NonExpansive (fun a : BU => (⟨!a.b⟩ : BU)) := ⟨fun _ _ _ h => congrArg (fun a : BU => (⟨!a.b⟩ : BU)) h⟩
/-- core is non-expansive in every ORA, total or not. -/
theorem core_dist {α : Type _} [ORA α] {n} {x y : α} (e : x ≡{n}≡ y) : PCore.core x ≡{n}≡ PCore.core y := by
  unfold PCore.core
  cases hx : PCore.pcore x with
  | some cx =>
    obtain ⟨cy, hy, ec⟩ := PCore.pcore_ne e hx
    rw [hy]; exact ec
  | none =>
    cases hy : PCore.pcore y with
    | none => exact e
    | some cy =>
      obtain ⟨cx, hx', _⟩ := PCore.pcore_ne e.symm hy
      rw [hx] at hx'; cases hx'

end W1c3
open Iris Iris.OFE W1c3

-- `Iris.Ordered.ordN_ne` (hypothesis 8): necessary, BL (order is implication on Bool): x=y=y'=false, x'=true
theorem c3_1 : ¬ drop0% Iris.Ordered.ordN_ne 8 := fun h => by
  have := @h BL _ _ 0 ⟨false⟩ ⟨true⟩ ⟨false⟩ ⟨false⟩ rfl rfl; cases this
-- `Iris.Ordered.ordN_ne` (hypothesis 9): necessary, BL: x=x'=y=true, y'=false
theorem c3_2 : ¬ drop0% Iris.Ordered.ordN_ne 9 := fun h => by
  have := @h BL _ _ 0 ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨false⟩ rfl rfl; cases this
-- `Iris.Ordered.ordN_trans` (hypothesis 7): necessary, BL: x=true, y=z=false
theorem c3_3 : ¬ drop0% Iris.Ordered.ordN_trans 7 := fun h => by
  have := @h BL _ _ 0 ⟨true⟩ ⟨false⟩ ⟨false⟩ rfl; cases this
-- `Iris.Ordered.ordN_trans` (hypothesis 8): necessary, BL: x=y=true, z=false
theorem c3_4 : ¬ drop0% Iris.Ordered.ordN_trans 8 := fun h => by
  have := @h BL _ _ 0 ⟨true⟩ ⟨true⟩ ⟨false⟩ rfl; cases this
-- `Iris.Ordered.ord_trans` (hypothesis 6): necessary, BL: x=true, y=z=false
theorem c3_5 : ¬ drop0% Iris.Ordered.ord_trans 6 := fun h => by
  have := @h BL _ _ ⟨true⟩ ⟨false⟩ ⟨false⟩ rfl; cases this
-- `Iris.Ordered.ord_trans` (hypothesis 7): necessary, BL: x=y=true, z=false
theorem c3_6 : ¬ drop0% Iris.Ordered.ord_trans 7 := fun h => by
  have := @h BL _ _ ⟨true⟩ ⟨true⟩ ⟨false⟩ rfl; cases this
-- `Iris.OrderRefl.ord_refl` (hypothesis 3): necessary, BX (empty order)
theorem c3_7 : ¬ drop0% Iris.OrderRefl.ord_refl 3 := fun h => @h BX _ _ ⟨false⟩
-- `Iris.IncOrd.inc_ord` (hypothesis 4): necessary, BX (xor, empty order): false is included in false
theorem c3_8 : ¬ drop0% Iris.IncOrd.inc_ord 4 := fun h => @h BX inferInstance inferInstance inferInstance ⟨false⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩
-- `Iris.OrdInc.ord_inc` (hypothesis 4): necessary, BT (or, full order): true is not included in false
theorem c3_9 : ¬ drop0% Iris.OrdInc.ord_inc 4 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT inferInstance inferInstance inferInstance ⟨true⟩ ⟨false⟩ trivial <;> cases hz
-- `Iris.OrdInc.ordN_incN` (hypothesis 4): necessary, BT: true is not included in false
theorem c3_10 : ¬ drop0% Iris.OrdInc.ordN_incN 4 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT inferInstance inferInstance inferInstance 0 ⟨true⟩ ⟨false⟩ trivial <;> cases hz
-- `Iris.IsInc.toIncOrd` (hypothesis 4): necessary, BX is not IncOrd
theorem c3_11 : ¬ drop0% Iris.IsInc.toIncOrd 4 := fun h =>
  (@h BX inferInstance inferInstance inferInstance).inc_ord (x := ⟨false⟩) (y := ⟨false⟩) ⟨⟨false⟩, rfl⟩
-- `Iris.IsInc.toOrdInc` (hypothesis 4): necessary, BT is not OrdInc
theorem c3_12 : ¬ drop0% Iris.IsInc.toOrdInc 4 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT inferInstance inferInstance inferInstance).ord_inc (x := ⟨true⟩) (y := ⟨false⟩) trivial <;> cases hz
-- `Iris.IncOrd.increasing` (hypothesis 4): necessary, BX: false is not increasing (empty order)
theorem c3_13 : ¬ drop0% Iris.IncOrd.increasing 4 := fun h => (@h BX inferInstance inferInstance inferInstance ⟨false⟩).increasing ⟨false⟩
-- `Iris.IncOrd.of_increasing` (hypothesis 4): necessary, BX is not IncOrd
theorem c3_14 : ¬ drop0% Iris.IncOrd.of_increasing 4 := fun h =>
  (@h BX inferInstance inferInstance inferInstance).inc_ord (x := ⟨false⟩) (y := ⟨false⟩) ⟨⟨false⟩, rfl⟩
-- `Iris.instIncreasingOfIncOrd` (hypothesis 4): necessary, BX: false is not increasing
theorem c3_15 : ¬ drop0% Iris.instIncreasingOfIncOrd 4 := fun h => (@h BX inferInstance inferInstance inferInstance ⟨false⟩).increasing ⟨false⟩
-- `Iris.inc_iff_ord` (hypothesis 4): necessary, BX is OrdInc (vacuously) but false included in false is not ordered
theorem c3_16 : ¬ drop0% Iris.inc_iff_ord 4 := fun h =>
  (@h BX inferInstance inferInstance inferInstance bxOrdInc ⟨false⟩ ⟨false⟩).mp ⟨⟨false⟩, rfl⟩
-- `Iris.inc_iff_ord` (hypothesis 5): necessary, BT is IncOrd (full order) but true is not included in false
theorem c3_17 : ¬ drop0% Iris.inc_iff_ord 5 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT inferInstance inferInstance inferInstance btIncOrd ⟨true⟩ ⟨false⟩).mpr trivial <;> cases hz
-- `Iris.IncOrd.incN_ordN` (hypothesis 4): necessary, BX
theorem c3_18 : ¬ drop0% Iris.IncOrd.incN_ordN 4 := fun h => @h BX inferInstance inferInstance inferInstance 0 ⟨false⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩
-- `Iris.incN_iff_ordN` (hypothesis 4): necessary, BX
theorem c3_19 : ¬ drop0% Iris.incN_iff_ordN 4 := fun h =>
  (@h BX inferInstance inferInstance inferInstance bxOrdInc 0 ⟨false⟩ ⟨false⟩).mp ⟨⟨false⟩, rfl⟩
-- `Iris.incN_iff_ordN` (hypothesis 5): necessary, BT
theorem c3_20 : ¬ drop0% Iris.incN_iff_ordN 5 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT inferInstance inferInstance inferInstance btIncOrd 0 ⟨true⟩ ⟨false⟩).mpr trivial <;> cases hz
-- `Iris.ORA.incN_ne` (hypothesis 8): necessary, BT (or): x=y=y'=false, x'=true (true is not included in false)
theorem c3_21 : ¬ drop0% Iris.ORA.incN_ne 8 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ 0 ⟨false⟩ ⟨true⟩ ⟨false⟩ ⟨false⟩ rfl ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_ne` (hypothesis 9): necessary, BT: x=x'=y=true, y'=false
theorem c3_22 : ¬ drop0% Iris.ORA.incN_ne 9 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ 0 ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨false⟩ rfl ⟨⟨true⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_of_incN_of_dist` (hypothesis 8): necessary, BT: a=b=true, c=false
theorem c3_23 : ¬ drop0% Iris.ORA.incN_of_incN_of_dist 8 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ 0 ⟨true⟩ ⟨true⟩ ⟨false⟩ ⟨⟨true⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_of_dist_of_incN` (hypothesis 7): necessary, BT: a=true, b=c=false
theorem c3_24 : ¬ drop0% Iris.ORA.incN_of_dist_of_incN 7 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ 0 ⟨true⟩ ⟨false⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_iff_left` (hypothesis 7): necessary, BT: a=true, b=c=false
theorem c3_25 : ¬ drop0% Iris.ORA.incN_iff_left 7 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT _ _ 0 ⟨true⟩ ⟨false⟩ ⟨false⟩).mpr ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.OFE.Dist.incN_l` (hypothesis 7): necessary, BT: a=true, b=c=false
theorem c3_26 : ¬ drop0% Iris.OFE.Dist.incN_l 7 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT _ _ 0 ⟨true⟩ ⟨false⟩ ⟨false⟩).mpr ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_iff_right` (hypothesis 7): necessary, BT: b=a=true, c=false
theorem c3_27 : ¬ drop0% Iris.ORA.incN_iff_right 7 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT _ _ 0 ⟨true⟩ ⟨false⟩ ⟨true⟩).mp ⟨⟨true⟩, rfl⟩ <;> cases hz
-- `Iris.OFE.Dist.incN_r` (hypothesis 7): necessary, BT: b=a=true, c=false
theorem c3_28 : ¬ drop0% Iris.OFE.Dist.incN_r 7 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT _ _ 0 ⟨true⟩ ⟨false⟩ ⟨true⟩).mp ⟨⟨true⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_dist_iff` (hypothesis 8): necessary, BT: a=b=b'=false, a'=true
theorem c3_29 : ¬ drop0% Iris.ORA.incN_dist_iff 8 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT _ _ 0 ⟨false⟩ ⟨true⟩ ⟨false⟩ ⟨false⟩ rfl).mp ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_dist_iff` (hypothesis 9): necessary, BT: a=a'=b=true, b'=false
theorem c3_30 : ¬ drop0% Iris.ORA.incN_dist_iff 9 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT _ _ 0 ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨false⟩ rfl).mp ⟨⟨true⟩, rfl⟩ <;> cases hz
-- `Iris.OFE.Dist.incN` (hypothesis 8): necessary, BT: a=b=b'=false, a'=true
theorem c3_31 : ¬ drop0% Iris.OFE.Dist.incN 8 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT _ _ 0 ⟨false⟩ ⟨true⟩ ⟨false⟩ ⟨false⟩ rfl).mp ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.OFE.Dist.incN` (hypothesis 9): necessary, BT: a=a'=b=true, b'=false
theorem c3_32 : ¬ drop0% Iris.OFE.Dist.incN 9 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := (@h BT _ _ 0 ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨false⟩ rfl).mp ⟨⟨true⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.inc_trans` (hypothesis 6): necessary, BT: x=true, y=z=false
theorem c3_33 : ¬ drop0% Iris.ORA.inc_trans 6 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ ⟨true⟩ ⟨false⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.inc_trans` (hypothesis 7): necessary, BT: x=y=true, z=false
theorem c3_34 : ¬ drop0% Iris.ORA.inc_trans 7 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ ⟨true⟩ ⟨true⟩ ⟨false⟩ ⟨⟨true⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_trans` (hypothesis 7): necessary, BT: x=true, y=z=false
theorem c3_35 : ¬ drop0% Iris.ORA.incN_trans 7 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ 0 ⟨true⟩ ⟨false⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_trans` (hypothesis 8): necessary, BT: x=y=true, z=false
theorem c3_36 : ¬ drop0% Iris.ORA.incN_trans 8 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ 0 ⟨true⟩ ⟨true⟩ ⟨false⟩ ⟨⟨true⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.incN_of_incN_le` (hypothesis 7): necessary, TM (max on the truncation OFE): 2 is included in 1 at step 0, not at step 1
theorem c3_37 : ¬ drop0% Iris.ORA.incN_of_incN_le 7 := fun h => by
  obtain ⟨z, hz⟩ := @h TM _ _ 0 1 ⟨2⟩ ⟨1⟩ ⟨⟨0⟩, rfl⟩
  have : min 1 (1+1) = min (max 2 z.v) (1+1) := hz
  omega
-- `Iris.ORA.op_monoN` (hypothesis 8): necessary, BT: x=true, x'=y=y'=false
theorem c3_38 : ¬ drop0% Iris.ORA.op_monoN 8 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ 0 ⟨true⟩ ⟨false⟩ ⟨false⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.op_monoN` (hypothesis 9): necessary, BT: x=x'=y'=false, y=true
theorem c3_39 : ¬ drop0% Iris.ORA.op_monoN 9 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ 0 ⟨false⟩ ⟨false⟩ ⟨true⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.op_mono` (hypothesis 7): necessary, BT: x=true, x'=y=y'=false
theorem c3_40 : ¬ drop0% Iris.ORA.op_mono 7 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ ⟨true⟩ ⟨false⟩ ⟨false⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.op_mono` (hypothesis 8): necessary, BT: x=x'=y'=false, y=true
theorem c3_41 : ¬ drop0% Iris.ORA.op_mono 8 := fun h => by
  obtain ⟨⟨_|_⟩, hz⟩ := @h BT _ _ ⟨false⟩ ⟨false⟩ ⟨true⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩ <;> cases hz
-- `Iris.ORA.pcore_monoN_ord` (hypothesis 7): necessary, BL (or, core = id, order = implication): x=y=false, cx=true
theorem c3_42 : ¬ drop0% Iris.ORA.pcore_monoN_ord 7 := fun h => by
  obtain ⟨cy, e, o⟩ := @h BL _ 0 ⟨false⟩ ⟨false⟩ ⟨true⟩ rfl
  cases e; cases o
-- `Iris.ORA.pcore_mono_ord` (hypothesis 6): necessary, BL: x=y=false, cx=true
theorem c3_43 : ¬ drop0% Iris.ORA.pcore_mono_ord 6 := fun h => by
  obtain ⟨cy, e, o⟩ := @h BL _ ⟨false⟩ ⟨false⟩ ⟨true⟩ rfl
  cases e; cases o
-- `Iris.ORA.pcore_increasing` (hypothesis 4): necessary, BOV (or, order: right side true): false is not increasing
theorem c3_44 : ¬ drop0% Iris.ORA.pcore_increasing 4 := fun h => by
  have := (@h BOV _ ⟨true⟩ ⟨false⟩).increasing ⟨false⟩; cases this
-- `Iris.ORA.increasing_closed` (hypothesis 6): necessary, BOV: true is increasing, false is not
theorem c3_45 : ¬ drop0% Iris.ORA.increasing_closed 6 := fun h => by
  have := (@h BOV _ 0 ⟨true⟩ ⟨false⟩ ⟨fun _ => rfl⟩).increasing ⟨false⟩; cases this
-- `Iris.ORA.ordN_extend` (hypothesis 5): necessary, UZ (one point, never valid, order only at step 0)
theorem c3_46 : ¬ drop0% Iris.ORA.ordN_extend 5 := fun h => by
  obtain ⟨z, hz, _⟩ := @h UZ _ 0 ⟨⟩ ⟨⟩ (rfl : (0:Nat) = 0); cases hz
-- `Iris.ORA.ordN_extend` (hypothesis 6): necessary, BX (empty order)
theorem c3_47 : ¬ drop0% Iris.ORA.ordN_extend 6 := fun h => by
  obtain ⟨z, hz, _⟩ := @h BX _ 0 ⟨false⟩ ⟨false⟩ trivial; exact hz
-- `Iris.ORA.Cancelable.cancelableN` (hypothesis 3): necessary, BU (or, all valid): true or true = true or false
theorem c3_48 : ¬ drop0% Iris.ORA.Cancelable.cancelableN 3 := fun h => by
  have := @h BU _ ⟨true⟩ 0 ⟨true⟩ ⟨false⟩ trivial rfl; cases this
-- `Iris.ORA.Cancelable.cancelableN` (hypothesis 7): necessary, BOV: true is invalid, hence cancelable, and true or true = true or false
theorem c3_49 : ¬ drop0% Iris.ORA.Cancelable.cancelableN 7 := fun h => by
  have := @h BOV _ ⟨true⟩ bovCancTrue 0 ⟨true⟩ ⟨false⟩ rfl; cases this
-- `Iris.ORA.Cancelable.cancelableN` (hypothesis 8): necessary, BOV: false is cancelable, y=false, z=true
theorem c3_50 : ¬ drop0% Iris.ORA.Cancelable.cancelableN 8 := fun h => by
  have := @h BOV _ ⟨false⟩ bovCancFalse 0 ⟨false⟩ ⟨true⟩ rfl; cases this
-- `Iris.ORA.IdFree.id_free0_r` (hypothesis 5): necessary, BOV: true is invalid, hence IdFree, and true or true = true
theorem c3_51 : ¬ drop0% Iris.ORA.IdFree.id_free0_r 5 := fun h =>
  @h BOV _ ⟨true⟩ bovIdFreeTrue ⟨true⟩ rfl
-- `Iris.ORA.validN_dist_iff` (hypothesis 5): necessary, BOV: false valid, true not
theorem c3_52 : ¬ drop0% Iris.ORA.validN_dist_iff 5 := fun h => by
  have := (@h BOV _ 0 ⟨false⟩ ⟨true⟩).mp rfl; cases this
-- `Iris.OFE.Dist.validN` (hypothesis 5): necessary, BOV: false valid, true not
theorem c3_53 : ¬ drop0% Iris.OFE.Dist.validN 5 := fun h => by
  have := (@h BOV _ 0 ⟨false⟩ ⟨true⟩).mp rfl; cases this
-- `Iris.ORA.validN_of_le` (hypothesis 5): necessary, UV (one point valid only at step 0)
theorem c3_54 : ¬ drop0% Iris.ORA.validN_of_le 5 := fun h => by
  have := @h UV _ 0 1 ⟨⟩ rfl; cases this
-- `Iris.ORA.validN_of_lt` (hypothesis 5): necessary, UV
theorem c3_55 : ¬ drop0% Iris.ORA.validN_of_lt 5 := fun h => by
  have := @h UV _ 0 1 ⟨⟩ rfl; cases this
-- `Iris.ORA.pcore_validN` (hypothesis 6): necessary, BOV: core of true is the invalid true
theorem c3_56 : ¬ drop0% Iris.ORA.pcore_validN 6 := fun h => by
  have := @h BOV _ 0 ⟨true⟩ ⟨true⟩ rfl; cases this
-- `Iris.ORA.pcore_valid` (hypothesis 5): necessary, BOV
theorem c3_57 : ¬ drop0% Iris.ORA.pcore_valid 5 := fun h => by
  have := @h BOV _ ⟨true⟩ ⟨true⟩ rfl; cases this
-- `Iris.ORA.not_valid_exclN_op_right` (hypothesis 4): necessary, BU (all valid)
theorem c3_58 : ¬ drop0% Iris.ORA.not_valid_exclN_op_right 4 := fun h => @h BU _ 0 ⟨false⟩ ⟨false⟩ trivial
-- `Iris.ORA.not_valid_excl_op_left` (hypothesis 3): necessary, BU (all valid)
theorem c3_59 : ¬ drop0% Iris.ORA.not_valid_excl_op_left 3 := fun h => @h BU _ ⟨false⟩ ⟨false⟩ trivial
-- `Iris.ORA.not_excl_op_right` (hypothesis 3): necessary, BU (all valid)
theorem c3_60 : ¬ drop0% Iris.ORA.not_excl_op_right 3 := fun h => @h BU _ ⟨false⟩ ⟨false⟩ trivial
-- `Iris.ORA.op_core_dist` (hypothesis 2): necessary, BX (xor, no core): core true = true, true xor true = false
theorem c3_61 : ¬ drop0% Iris.ORA.op_core_dist 2 := fun h => by
  have := @h BX _ 0 ⟨true⟩; cases this
-- `Iris.ORA.core_op_dist` (hypothesis 2): necessary, BX
theorem c3_62 : ¬ drop0% Iris.ORA.core_op_dist 2 := fun h => by
  have := @h BX _ 0 ⟨true⟩; cases this
-- `Iris.ORA.validN_core` (hypothesis 2): removable, without a core core x = x, else pcore_validN
theorem c3_63 : drop% Iris.ORA.validN_core 2 := by
  intro α _ n x v
  unfold PCore.core
  cases e : PCore.pcore x with
  | none => exact v
  | some cx => exact ORA.pcore_validN e v
-- `Iris.ORA.validN_core` (hypothesis 5): necessary, BL (core = id, true invalid)
theorem c3_64 : ¬ drop0% Iris.ORA.validN_core 5 := fun h => by
  have := @h BL _ _ 0 ⟨true⟩; cases this
-- `Iris.ORA.valid_core` (hypothesis 2): removable, without a core core x = x, else pcore_valid
theorem c3_65 : drop% Iris.ORA.valid_core 2 := by
  intro α _ x v
  unfold PCore.core
  cases e : PCore.pcore x with
  | none => exact v
  | some cx => exact ORA.pcore_valid e v
-- `Iris.ORA.valid_core` (hypothesis 4): necessary, BL
theorem c3_66 : ¬ drop0% Iris.ORA.valid_core 4 := fun h => by
  have := @h BL _ _ ⟨true⟩; cases this
-- `Iris.ORA.core_ne` (hypothesis 2): removable, core is non-expansive by pcore_ne alone (helper core_dist)
theorem c3_67 : drop% Iris.ORA.core_ne 2 := fun {_} _ => ⟨fun _ _ _ e => core_dist e⟩
-- `Iris.OFE.Dist.core` (hypothesis 2): removable, helper core_dist
theorem c3_68 : drop% Iris.OFE.Dist.core 2 := fun {_} _ _ _ _ e => core_dist e
-- `Iris.OFE.Dist.core` (hypothesis 6): necessary, BL: core true = true, core false = false
theorem c3_69 : ¬ drop0% Iris.OFE.Dist.core 6 := fun h => by
  have := @h BL _ _ 0 ⟨true⟩ ⟨false⟩; cases this
-- `Iris.ORA.core_eqv_self` (hypothesis 2): removable, CoreId gives pcore x = some x
theorem c3_70 : drop% Iris.ORA.core_eqv_self 2 := by
  intro α _ x hx
  unfold PCore.core; rw [hx.core_id]; rfl
-- `Iris.ORA.core_eqv_self` (hypothesis 4): necessary, BU (unit false is the core of everything)
theorem c3_71 : ¬ drop0% Iris.ORA.core_eqv_self 4 := fun h => by
  have := @h BU _ _ ⟨true⟩; cases this
-- `Iris.ORA.coreId_iff_core_eqv_self` (hypothesis 2): necessary, BX (no core): core false = false but false is no CoreId
theorem c3_72 : ¬ drop0% Iris.ORA.coreId_iff_core_eqv_self 2 := fun h => by
  have := ((@h BX _ ⟨false⟩).mpr rfl).core_id; cases this
-- `Iris.ORA.core_idem` (hypothesis 2): removable, by cases on pcore x and pcore_idem
theorem c3_73 : drop% Iris.ORA.core_idem 2 := by
  intro α _ x
  cases e : PCore.pcore x with
  | none => simp only [PCore.core, e, Option.getD_none]
  | some cx => simp only [PCore.core, e, Option.getD_some, PCore.pcore_idem e]
-- `Iris.ORA.instOrderReflOfIsTotal` (hypothesis 2): necessary, BX (empty order)
theorem c3_74 : ¬ drop0% Iris.ORA.instOrderReflOfIsTotal 2 := fun h => (@h BX _).ord_refl ⟨false⟩
-- `Iris.ORA.discrete_op` (hypothesis 4): necessary, TI (truncation OFE, x+y+1, never valid): 0 discrete, 0•0 = 1 not
theorem c3_75 : ¬ drop0% Iris.ORA.discrete_op 4 := fun h => by
  have := congrArg TI.v ((@h TI _ ⟨0⟩ ⟨0⟩ ti0disc ti0disc).discrete (y := ⟨2⟩) rfl)
  exact absurd this (by decide)
-- `Iris.ORA.discrete_op` (hypothesis 5): necessary, TM (max): 1 not discrete, 0 discrete, max 1 0 = 1 not discrete
theorem c3_76 : ¬ drop0% Iris.ORA.discrete_op 5 := fun h => by
  have := congrArg TM.v ((@h TM _ ⟨1⟩ ⟨0⟩ trivial tm0disc).discrete (y := ⟨2⟩) rfl)
  exact absurd this (by decide)
-- `Iris.ORA.discrete_op` (hypothesis 6): necessary, TM: x=0, y=1
theorem c3_77 : ¬ drop0% Iris.ORA.discrete_op 6 := fun h => by
  have := congrArg TM.v ((@h TM _ ⟨0⟩ ⟨1⟩ trivial tm0disc).discrete (y := ⟨2⟩) rfl)
  exact absurd this (by decide)
-- `Iris.ORA.validN_of_inc` (hypothesis 6): necessary, BOV: true included in true, invalid
theorem c3_78 : ¬ drop0% Iris.ORA.validN_of_inc 6 := fun h => by
  have := @h BOV _ 0 ⟨true⟩ ⟨true⟩ ⟨⟨true⟩, rfl⟩; cases this
-- `Iris.ORA.op_core_right_of_inc` (hypothesis 4): necessary, BX: true included in true, true xor true = false
theorem c3_79 : ¬ drop0% Iris.ORA.op_core_right_of_inc 4 := fun h => by
  have := @h BX _ ⟨true⟩ ⟨true⟩ ⟨⟨false⟩, rfl⟩; cases this
-- `Iris.ORA.op_core_left_of_inc` (hypothesis 4): necessary, BX
theorem c3_80 : ¬ drop0% Iris.ORA.op_core_left_of_inc 4 := fun h => by
  have := @h BX _ ⟨true⟩ ⟨true⟩ ⟨⟨false⟩, rfl⟩; cases this
-- `Iris.ORA.included_dist_l` (hypothesis 6): necessary, BU (or): x1=x1'=true, x2=false
theorem c3_81 : ¬ drop0% Iris.ORA.included_dist_l 6 := fun h => by
  obtain ⟨x2', ⟨⟨zb⟩, hz⟩, e⟩ := @h BU _ 0 ⟨true⟩ ⟨false⟩ ⟨true⟩ rfl
  have e' : x2' = ⟨false⟩ := e
  subst e'; cases zb <;> cases hz
-- `Iris.ORA.included_dist_l` (hypothesis 7): necessary, BU: x1=x2=false, x1'=true
theorem c3_82 : ¬ drop0% Iris.ORA.included_dist_l 7 := fun h => by
  obtain ⟨x2', ⟨⟨zb⟩, hz⟩, e⟩ := @h BU _ 0 ⟨false⟩ ⟨false⟩ ⟨true⟩ ⟨⟨false⟩, rfl⟩
  have e' : x2' = ⟨false⟩ := e
  subst e'; cases zb <;> cases hz
-- `Iris.ORA.not_valid_of_exclN_inc` (hypothesis 4): necessary, BU (all valid)
theorem c3_83 : ¬ drop0% Iris.ORA.not_valid_of_exclN_inc 4 := fun h =>
  @h BU _ 0 ⟨false⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩ trivial
-- `Iris.ORA.not_valid_of_excl_inc` (hypothesis 3): necessary, BU (all valid)
theorem c3_84 : ¬ drop0% Iris.ORA.not_valid_of_excl_inc 3 := fun h =>
  @h BU _ ⟨false⟩ ⟨false⟩ ⟨⟨false⟩, rfl⟩ trivial
-- `Iris.ORA.incN_extend` (hypothesis 5): necessary, TI: 1 included in 1 at step 0, nothing 0-close to 1 included in 1 at step 1
theorem c3_85 : ¬ drop0% Iris.ORA.incN_extend 5 := fun h => by
  obtain ⟨z, ⟨w, hw⟩, hz⟩ := @h TI _ 0 ⟨1⟩ ⟨1⟩ ⟨⟨0⟩, rfl⟩
  have hw' : min 1 (1+1) = min (z.v + w.v + 1) (1+1) := hw
  have hz' : min z.v (0+1) = min 1 (0+1) := hz
  omega
-- `Iris.ORA.incN_extend` (hypothesis 6): necessary, BU: x=true, y=false
theorem c3_86 : ¬ drop0% Iris.ORA.incN_extend 6 := fun h => by
  obtain ⟨z, ⟨⟨wb⟩, hw⟩, hz⟩ := @h BU _ 0 ⟨true⟩ ⟨false⟩ trivial
  have e' : z = ⟨true⟩ := hz
  subst e'; cases wb <;> cases hw
-- `Iris.ORA.incN_map` (hypothesis 5): necessary, f : TM to BU, a maps to (2 ≤ a) is a homomorphism, not non-expansive: 2 incl. 1 at step 0
theorem c3_87 : ¬ drop0% Iris.ORA.incN_map 5 := fun h => by
  obtain ⟨⟨zb⟩, hz⟩ := @h TM _ BU _ (fun a => ⟨decide (2 ≤ a.v)⟩)
    (fun x y => congrArg BU.mk (by
      show decide (2 ≤ max x.v y.v) = or (decide (2 ≤ x.v)) (decide (2 ≤ y.v))
      by_cases h1 : 2 ≤ x.v <;> by_cases h2 : 2 ≤ y.v <;> simp [h1, h2] <;> omega))
    0 ⟨2⟩ ⟨1⟩ ⟨⟨0⟩, rfl⟩
  cases zb <;> cases hz
-- `Iris.ORA.incN_map` (hypothesis 6): necessary, f = not on BU (non-expansive, no homomorphism): false incl. true, true not incl. false
theorem c3_88 : ¬ drop0% Iris.ORA.incN_map 6 := fun h => by
  obtain ⟨⟨zb⟩, hz⟩ := @h BU _ BU _ (fun a => ⟨!a.b⟩) buNotNE 0 ⟨false⟩ ⟨true⟩ ⟨⟨true⟩, rfl⟩
  cases zb <;> cases hz
-- `Iris.ORA.incN_map` (hypothesis 10): necessary, f = id on BU, x=true, y=false
theorem c3_89 : ¬ drop0% Iris.ORA.incN_map 10 := fun h => by
  obtain ⟨⟨zb⟩, hz⟩ := @h BU _ BU _ id inferInstance (fun _ _ => rfl) 0 ⟨true⟩ ⟨false⟩
  cases zb <;> cases hz
-- `Iris.ORA.inc_map` (hypothesis 5): necessary, f = not on BU
theorem c3_90 : ¬ drop0% Iris.ORA.inc_map 5 := fun h => by
  obtain ⟨⟨zb⟩, hz⟩ := @h BU _ BU _ (fun a => ⟨!a.b⟩) ⟨false⟩ ⟨true⟩ ⟨⟨true⟩, rfl⟩
  cases zb <;> cases hz
-- `Iris.ORA.inc_map` (hypothesis 8): necessary, f = id on BU, x=true, y=false
theorem c3_91 : ¬ drop0% Iris.ORA.inc_map 8 := fun h => by
  obtain ⟨⟨zb⟩, hz⟩ := @h BU _ BU _ id (fun _ _ => rfl) ⟨true⟩ ⟨false⟩
  cases zb <;> cases hz
-- `Iris.ORA.incN_of_dist` (hypothesis 2): necessary, TI (x+y+1): 0 is not included in 0
theorem c3_92 : ¬ drop0% Iris.ORA.incN_of_dist 2 := fun h => by
  obtain ⟨z, hz⟩ := @h TI _ 0 ⟨0⟩ ⟨0⟩ rfl
  have : min 0 (0+1) = min (0 + z.v + 1) (0+1) := hz
  omega
-- `Iris.ORA.incN_of_dist` (hypothesis 6): necessary, BL (total): true not included in false
theorem c3_93 : ¬ drop0% Iris.ORA.incN_of_dist 6 := fun h => by
  obtain ⟨⟨zb⟩, hz⟩ := @h BL _ _ 0 ⟨true⟩ ⟨false⟩
  cases zb <;> cases hz
-- `Iris.OFE.Dist.to_incN` (hypothesis 2): necessary, TI: 0 is not included in 0
theorem c3_94 : ¬ drop0% Iris.OFE.Dist.to_incN 2 := fun h => by
  obtain ⟨z, hz⟩ := @h TI _ 0 ⟨0⟩ ⟨0⟩ rfl
  have : min 0 (0+1) = min (0 + z.v + 1) (0+1) := hz
  omega
-- `Iris.OFE.Dist.to_incN` (hypothesis 6): necessary, BL: true not included in false
theorem c3_95 : ¬ drop0% Iris.OFE.Dist.to_incN 6 := fun h => by
  obtain ⟨⟨zb⟩, hz⟩ := @h BL _ _ 0 ⟨true⟩ ⟨false⟩
  cases zb <;> cases hz
