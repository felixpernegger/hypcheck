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
namespace W1c4
open Iris Iris.OFE

/-- Truncation OFE on naturals: dist n x y iff min x (n+1) = min y (n+1). Not discrete (1 and 2 agree at 0). -/
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
instance tn0disc : DiscreteE (⟨0⟩ : TN) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩

/-- CMRA on TN: x • y = x + y + 2, no core, only 0 valid (0 is never a composite). Not discrete;
1 is 0-included in 0 but not included. -/
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

/-- Discrete 3-element CMRA: u • u = u, all other products bot; core u = core bot = u, e has no core;
valid = not bot. e is not included in e or u. -/
inductive K | e | u | bot
  deriving DecidableEq
instance : OFE K := OFE.ofDiscrete K
instance : OFE.Discrete K := ⟨fun h => h⟩
def kOp : K → K → K
  | .u, .u => .u
  | _, _ => .bot
def kPc : K → Option K
  | .e => none
  | _ => some .u
@[instance_reducible] def kData : CMRAData K where
  op := kOp
  op_ne := ⟨fun {_ _ _} h => congrArg _ h⟩
  assoc {x y z} := by cases x <;> cases y <;> cases z <;> rfl
  comm {x y} := by cases x <;> cases y <;> rfl
  pcore := kPc
  pcore_ne {n x y cx} h e := by obtain rfl : x = y := h; exact ⟨cx, e, Dist.rfl⟩
  pcore_idem {x cx} e := by revert e; cases x <;> cases cx <;> decide
  ValidN _ x := x ≠ .bot
  Valid x := x ≠ .bot
  validN_ne {n x y} h v := by obtain rfl : x = y := h; exact v
  valid_iff_validN := ⟨fun h _ => h, fun h => h 0⟩
  validN_succ := id
  validN_op_left {n x y} := by show kOp x y ≠ .bot → x ≠ .bot; cases x <;> cases y <;> decide
  pcore_op_left {x cx} := by show kPc x = some cx → kOp cx x = x; cases x <;> cases cx <;> decide
  extend {n x y₁ y₂} v h := ⟨y₁, y₂, h, Dist.rfl, Dist.rfl⟩
  pcore_op_mono {x cx} e y := ⟨.u, by revert e; show kPc x = some cx → kPc (kOp x y) = some (kOp cx .u); cases x <;> cases y <;> cases cx <;> decide⟩
instance kCMRA : CMRA K := ORA.ofCMRAData kData
theorem k_e_not_inc_u : ¬ (K.e ≼ K.u) := fun ⟨z, hz⟩ => by cases z <;> cases hz
theorem k_e_not_inc_e : ¬ (K.e ≼ K.e) := fun ⟨z, hz⟩ => by cases z <;> cases hz

/-- Discrete 2-element CMRA: op = or, pcore = some, valid only at step 0. Inclusion is f ≤ t;
t is not included in f; core is the identity. -/
inductive BO | f | t
  deriving DecidableEq
instance : OFE BO := OFE.ofDiscrete BO
instance : OFE.Discrete BO := ⟨fun h => h⟩
def boOp : BO → BO → BO
  | .f, .f => .f
  | _, _ => .t
@[instance_reducible] def boData : CMRAData BO where
  op := boOp
  op_ne := ⟨fun {_ _ _} h => congrArg _ h⟩
  assoc {x y z} := by cases x <;> cases y <;> cases z <;> rfl
  comm {x y} := by cases x <;> cases y <;> rfl
  pcore := some
  pcore_ne {n x y cx} h e := by obtain rfl : x = y := h; exact ⟨cx, e, Dist.rfl⟩
  pcore_idem {x cx} e := by cases e; rfl
  ValidN n _ := n = 0
  Valid _ := False
  validN_ne _ v := v
  valid_iff_validN := ⟨False.elim, fun h => absurd (h 1) (by decide)⟩
  validN_succ h := absurd h (Nat.succ_ne_zero _)
  validN_op_left := id
  pcore_op_left {x cx} e := by cases e; cases x <;> rfl
  extend {n x y₁ y₂} v h := ⟨y₁, y₂, h, Dist.rfl, Dist.rfl⟩
  pcore_op_mono {x cx} e y := ⟨y, by cases e; rfl⟩
instance boCMRA : CMRA BO := ORA.ofCMRAData boData
theorem bo_t_not_inc_f : ¬ (BO.t ≼ BO.f) := fun ⟨z, hz⟩ => by cases z <;> cases hz
theorem bo_t_not_incN_f (n) : ¬ (BO.t ≼{n} BO.f) := fun ⟨z, hz⟩ => by cases z <;> cases hz

/-- Discrete ORA on Nat: op = max, all valid, order True, core n = n except core 2 = 0.
Not OrdInc; the core is not monotone along inclusion (1 ≼ 2, core 1 = 1 not ≼ core 2 = 0). -/
structure MO where v : Nat
instance : OFE MO := OFE.ofDiscrete MO
instance : OFE.Discrete MO := ⟨fun h => h⟩
def moPc (x : MO) : Option MO := some (if x.v = 2 then ⟨0⟩ else x)
@[instance_reducible] def moData : DiscreteORAData MO where
  pcore := moPc
  op x y := ⟨max x.v y.v⟩
  Valid _ := True
  Order _ _ := True
  assoc x y z := congrArg MO.mk (Nat.max_assoc x.v y.v z.v).symm
  comm x y := congrArg MO.mk (Nat.max_comm x.v y.v)
  pcore_op_left x cx h := by
    obtain ⟨v⟩ := x; simp only [moPc, Option.some.injEq] at h; subst h
    by_cases hv : v = 2 <;> simp [hv]
  pcore_idem x cx h := by
    obtain ⟨v⟩ := x; simp only [moPc, Option.some.injEq] at h; subst h
    by_cases hv : v = 2 <;> simp [moPc, hv]
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ _ _ := trivial
  op_mono_left _ _ _ _ := trivial
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ _ := ⟨_, rfl, trivial⟩
  pcore_order_op _ _ _ _ := ⟨_, rfl, trivial⟩
  pcore_increasing _ _ _ _ := trivial
  increasing_closed _ _ _ _ _ := trivial
instance moORA : ORA MO := ORA.ofDiscreteORAData moData
theorem mo_not_inc : ¬ ((⟨1⟩ : MO) ≼ ⟨0⟩) := fun ⟨z, hz⟩ => by
  have := congrArg MO.v hz; change 0 = max 1 z.v at this; omega

theorem k_e_not_incN_e (n) : ¬ (K.e ≼{n} K.e) := fun ⟨z, hz⟩ => by cases z <;> cases hz
theorem k_e_not_incN_u (n) : ¬ (K.e ≼{n} K.u) := fun ⟨z, hz⟩ => by cases z <;> cases hz
theorem mo_not_incN (n) : ¬ ((⟨1⟩ : MO) ≼{n} ⟨0⟩) := fun ⟨z, hz⟩ => by
  have := congrArg MO.v (show (⟨0⟩ : MO) = Op.op ⟨1⟩ z from hz); change 0 = max 1 z.v at this; omega
instance moTotal : IsTotal MO := ⟨fun _ => ⟨_, rfl⟩⟩
instance boTotal : IsTotal BO := ⟨fun x => ⟨x, rfl⟩⟩
instance boRefl : OrderRefl BO := ⟨fun x => show x ≼ x from ⟨x, by cases x <;> rfl⟩⟩
/-- Partial core on BO: f has core f, t has none; core is the identity. -/
@[instance_reducible] def boPF : PCore BO where
  pcore | .f => some .f | .t => none
  pcore_ne {n x y cx} h e := by obtain rfl : x = y := h; exact ⟨cx, e, Dist.rfl⟩
  pcore_idem {x cx} e := by cases x <;> cases e; rfl

/-- Discrete ORA on booleans: op is and, no core, order is equality. Not IncOrd, false not Increasing. -/
structure BA where b : Bool
instance : OFE BA := OFE.ofDiscrete BA
instance : OFE.Discrete BA := ⟨fun h => h⟩
@[instance_reducible] def baData : DiscreteORAData BA where
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
instance baTInc : Increasing (⟨true⟩ : BA) := ⟨fun y => (rfl : y = ⟨true && y.b⟩)⟩

end W1c4
open W1c4 Iris Iris.OFE

-- `Iris.ORA.core_inc_self` (hypothesis 2): necessary, K (no core for e): core e = e is not included in e
theorem w4_1 : ¬ drop0% Iris.ORA.core_inc_self 2 := fun h => k_e_not_inc_e (@h K _ K.e)
-- `Iris.ORA.inc_iff_incN` (hypothesis 2): necessary, TC (x•y=x+y+2 on truncation naturals): 0 ≼{0} 1, not 0 ≼ 1
theorem w4_2 : ¬ drop0% Iris.ORA.inc_iff_incN 2 := fun h => tc_not_inc _ ((@h TN _ 0 ⟨0⟩ ⟨1⟩).2 tc_inc0)
-- `Iris.ORA.inc_0_iff_incN` (hypothesis 2): necessary, TC: 0 ≼{0} 1, not 0 ≼{1} 1
theorem w4_3 : ¬ drop0% Iris.ORA.inc_0_iff_incN 2 := fun h => tc_not_inc1 _ ((@h TN _ 1 ⟨0⟩ ⟨1⟩).1 tc_inc0)
-- `Iris.ORA.inc_of_inc0` (hypothesis 2): necessary, TC: 0 ≼{0} 1, not 0 ≼ 1
theorem w4_4 : ¬ drop0% Iris.ORA.inc_of_inc0 2 := fun h => tc_not_inc _ (@h TN _ ⟨0⟩ ⟨1⟩ tc_inc0)
-- `Iris.ORA.discrete_inc_l` (hypothesis 5): necessary, TC: x = 0 discrete, y = 1 invalid, 0 ≼{0} 1, not 0 ≼ 1
theorem w4_6 : ¬ drop0% Iris.ORA.discrete_inc_l 5 := fun h => tc_not_inc _ (@h TN _ ⟨0⟩ ⟨1⟩ tn0disc tc_inc0)
-- `Iris.ORA.discrete_inc_r` (hypothesis 4): necessary, TC: 0 ≼{0} 1, not 0 ≼ 1 (1 not discrete)
theorem w4_7 : ¬ drop0% Iris.ORA.discrete_inc_r 4 := fun h => tc_not_inc _ (@h TN _ ⟨0⟩ ⟨1⟩ tc_inc0)
-- `Iris.CMRAData.validN_op_left` (hypothesis 6): necessary, TC data: 1 is not valid
theorem w4_8 : ¬ drop0% Iris.CMRAData.validN_op_left 6 := fun h =>
  absurd (show (⟨1⟩ : TN).v = 0 from @h TN _ tcData 0 ⟨1⟩ ⟨0⟩) (by decide)
-- `Iris.CMRAData.pcore_op_left` (hypothesis 5): necessary, TC data: 0 • 0 = 2
theorem w4_9 : ¬ drop0% Iris.CMRAData.pcore_op_left 5 := fun h =>
  absurd (congrArg TN.v (@h TN _ tcData ⟨0⟩ ⟨0⟩)) (by decide)
-- `Iris.CMRAData.pcore_op_mono` (hypothesis 5): necessary, TC data has no core at all
theorem w4_10 : ¬ drop0% Iris.CMRAData.pcore_op_mono 5 := fun h => by
  obtain ⟨cy, hcy⟩ := @h TN _ tcData ⟨0⟩ ⟨0⟩ ⟨0⟩; cases hcy
-- `Iris.CMRAData.pcore_op_mono_of_pcore_mono` (hypothesis 4): necessary, MO (max, core 2 = 0): core (1 • 2) = 0 is not 1 • cy
theorem w4_11 : ¬ drop0% Iris.CMRAData.pcore_op_mono_of_pcore_mono 4 := fun h => by
  obtain ⟨cy, hcy⟩ := @h MO _ _ _ ⟨1⟩ ⟨1⟩ rfl ⟨2⟩
  have := congrArg (fun o => (Option.getD o ⟨5⟩).v) hcy; change 0 = max 1 cy.v at this; omega
-- `Iris.CMRAData.pcore_op_mono_of_core_mono` (hypothesis 4): necessary, BO with core f = f, none for t (core = id): f • t = t has no core
theorem w4_12 : ¬ drop0% Iris.CMRAData.pcore_op_mono_of_core_mono 4 := fun h => by
  obtain ⟨cy, hcy⟩ := @h BO _ _ boPF (fun x y hxy => by cases x <;> cases y <;> exact hxy) BO.f BO.f rfl BO.t
  cases hcy
-- `Iris.CMRAData.pcore_op_mono_of_core_mono` (hypothesis 5): necessary, MO (max, core 2 = 0): core (1 • 2) = 0 is not 1 • cy
theorem w4_13 : ¬ drop0% Iris.CMRAData.pcore_op_mono_of_core_mono 5 := fun h => by
  obtain ⟨cy, hcy⟩ := @h MO _ _ _ _ ⟨1⟩ ⟨1⟩ rfl ⟨2⟩
  have := congrArg (fun o => (Option.getD o ⟨5⟩).v) hcy; change 0 = max 1 cy.v at this; omega
-- `Iris.CMRAData.pcore_op_mono_of_core_mono` (hypothesis 8): necessary, BO (or, core = id): x = f, cx = t, y = f
theorem w4_14 : ¬ drop0% Iris.CMRAData.pcore_op_mono_of_core_mono 8 := fun h => by
  obtain ⟨cy, hcy⟩ := @h BO _ _ _ _ (fun x y hxy => by exact hxy) BO.f BO.t BO.f
  cases cy <;> cases hcy
-- `Iris.CMRAData.validN_of_incN` (hypothesis 6): necessary, K: u valid, bot not
theorem w4_15 : ¬ drop0% Iris.CMRAData.validN_of_incN 6 := fun h =>
  (@h K _ kData 0 .bot .u (show K.u ≠ K.bot by decide)) rfl
-- `Iris.CMRAData.validN_of_incN` (hypothesis 7): necessary, TC data: 1 ≼{0} 3, 1 invalid
theorem w4_16 : ¬ drop0% Iris.CMRAData.validN_of_incN 7 := fun h =>
  absurd (show (⟨1⟩ : TN).v = 0 from @h TN _ tcData 0 ⟨1⟩ ⟨3⟩ ⟨⟨0⟩, rfl⟩) (by decide)
-- `Iris.CMRAData.incN_extend` (hypothesis 6): necessary, TC data: 0 ≼{0} 1, nothing is 1-included in 1
theorem w4_17 : ¬ drop0% Iris.CMRAData.incN_extend 6 := fun h => by
  obtain ⟨z, hz, -⟩ := @h TN _ tcData 0 ⟨0⟩ ⟨1⟩ tc_inc0
  exact tc_not_inc1 z hz
-- `Iris.CMRAData.incN_extend` (hypothesis 7): necessary, K: u valid, e not included in u
theorem w4_18 : ¬ drop0% Iris.CMRAData.incN_extend 7 := fun h => by
  obtain ⟨z, hz, e⟩ := @h K _ kData 0 .e .u (show K.u ≠ K.bot by decide)
  obtain rfl : z = K.e := e
  exact k_e_not_incN_u _ hz
-- `Iris.CMRAData.pcore_mono` (hypothesis 6): necessary, K: u has core u, e has none
theorem w4_19 : ¬ drop0% Iris.CMRAData.pcore_mono 6 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h K _ kData K.u K.u K.e rfl; cases hcy
-- `Iris.CMRAData.pcore_mono` (hypothesis 7): necessary, TC data has no core
theorem w4_20 : ¬ drop0% Iris.CMRAData.pcore_mono 7 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h TN _ tcData ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨⟨0⟩, rfl⟩; cases hcy
-- `Iris.CMRAData.pcore_mono'` (hypothesis 6): necessary, K: u has core u, e has none
theorem w4_21 : ¬ drop0% Iris.CMRAData.pcore_mono' 6 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h K _ kData K.u K.e K.u rfl; cases hcy
-- `Iris.CMRAData.pcore_mono'` (hypothesis 7): necessary, TC data has no core
theorem w4_22 : ¬ drop0% Iris.CMRAData.pcore_mono' 7 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h TN _ tcData ⟨0⟩ ⟨2⟩ ⟨0⟩ ⟨⟨0⟩, rfl⟩; cases hcy
-- `Iris.CMRAData.pcore_monoN'` (hypothesis 7): necessary, K: u has core u, e has none
theorem w4_23 : ¬ drop0% Iris.CMRAData.pcore_monoN' 7 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h K _ kData 0 K.u K.e K.u (OFE.Dist.of_eq rfl); cases hcy
-- `Iris.CMRAData.pcore_monoN'` (hypothesis 8): necessary, TC data has no core
theorem w4_24 : ¬ drop0% Iris.CMRAData.pcore_monoN' 8 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h TN _ tcData 0 ⟨0⟩ ⟨2⟩ ⟨0⟩ ⟨⟨0⟩, rfl⟩; cases hcy
-- `Iris.CMRAData.pcore_monoN` (hypothesis 7): necessary, K: u has core u, e has none
theorem w4_25 : ¬ drop0% Iris.CMRAData.pcore_monoN 7 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h K _ kData 0 K.u K.e K.u rfl; cases hcy
-- `Iris.CMRAData.pcore_monoN` (hypothesis 8): necessary, TC data has no core
theorem w4_26 : ¬ drop0% Iris.CMRAData.pcore_monoN 8 := fun h => by
  obtain ⟨cy, hcy, -⟩ := @h TN _ tcData 0 ⟨0⟩ ⟨2⟩ ⟨0⟩ ⟨⟨0⟩, rfl⟩; cases hcy
-- `Iris.CMRAData.core_incN_core` (hypothesis 3): necessary, K (not total): e ≼ bot, core e = e not included in core bot = u
theorem w4_27 : ¬ drop0% Iris.CMRAData.core_incN_core 3 := fun h =>
  k_e_not_incN_u 0 (@h K _ kData 0 K.e K.bot ⟨K.e, rfl⟩)
-- `Iris.CMRAData.core_incN_core` (hypothesis 7): necessary, BO (total, core = id): t not included in f
theorem w4_28 : ¬ drop0% Iris.CMRAData.core_incN_core 7 := fun h =>
  bo_t_not_incN_f 0 (@h BO _ boData boTotal 0 BO.t BO.f)
-- `Iris.CMRAData.core_op_mono` (hypothesis 3): necessary, K (not total): core e = e not included in core (e • e) = u
theorem w4_29 : ¬ drop0% Iris.CMRAData.core_op_mono 3 := fun h =>
  k_e_not_inc_u (@h K _ kData K.e K.e)
-- `Iris.CMRAData.core_mono` (hypothesis 3): necessary, K (not total): e ≼ bot, core e = e not included in u
theorem w4_30 : ¬ drop0% Iris.CMRAData.core_mono 3 := fun h =>
  k_e_not_inc_u (@h K _ kData K.e K.bot ⟨K.e, rfl⟩)
-- `Iris.CMRAData.core_mono` (hypothesis 6): necessary, BO (total, core = id): t not included in f
theorem w4_31 : ¬ drop0% Iris.CMRAData.core_mono 6 := fun h =>
  bo_t_not_inc_f (@h BO _ boData boTotal BO.t BO.f)
-- `Iris.CMRAData.inc_refl` (hypothesis 3): necessary, K: e not included in e
theorem w4_32 : ¬ drop0% Iris.CMRAData.inc_refl 3 := fun h => k_e_not_inc_e (@h K _ kData K.e)
-- `Iris.CMRAData.instOrderRefl` (hypothesis 3): necessary, K: e not included in e
theorem w4_33 : ¬ drop0% Iris.CMRAData.instOrderRefl 3 := fun h => k_e_not_inc_e ((@h K _ kData).ord_refl K.e)
-- `Iris.CMRA.ord_of_ord0` (hypothesis 2): necessary, TC: 0 ≼{0} 1, not 0 ≼ 1
theorem w4_34 : ¬ drop0% Iris.CMRA.ord_of_ord0 2 := fun h => tc_not_inc _ (@h TN _ ⟨0⟩ ⟨1⟩ tc_inc0)
-- `Iris.Included.trans` (hypothesis 6): necessary, BO (or): f ≼ f, t not included in f
theorem w4_35 : ¬ drop0% Iris.Included.trans 6 := fun h => bo_t_not_inc_f (@h BO _ _ BO.t BO.f BO.f ⟨BO.f, rfl⟩)
-- `Iris.Included.trans` (hypothesis 7): necessary, BO (or): t ≼ t, t not included in f
theorem w4_36 : ¬ drop0% Iris.Included.trans 7 := fun h => bo_t_not_inc_f (@h BO _ _ BO.t BO.t BO.f ⟨BO.f, rfl⟩)
-- `Iris.IncludedN.trans` (hypothesis 7): necessary, BO (or): f ≼{0} f, t not included in f
theorem w4_37 : ¬ drop0% Iris.IncludedN.trans 7 := fun h => bo_t_not_incN_f 0 (@h BO _ _ 0 BO.t BO.f BO.f ⟨BO.f, rfl⟩)
-- `Iris.IncludedN.trans` (hypothesis 8): necessary, BO (or): t ≼{0} t, t not included in f
theorem w4_38 : ¬ drop0% Iris.IncludedN.trans 8 := fun h => bo_t_not_incN_f 0 (@h BO _ _ 0 BO.t BO.t BO.f ⟨BO.f, rfl⟩)
-- `Iris.IncludedN.le` (hypothesis 7): necessary, TC: 0 ≼{0} 1, not 0 ≼{1} 1
theorem w4_39 : ¬ drop0% Iris.IncludedN.le 7 := fun h => tc_not_inc1 _ (@h TN _ _ 0 1 ⟨0⟩ ⟨1⟩ tc_inc0)
-- `Iris.Included.validN` (hypothesis 6): necessary, K: bot ≼ bot, bot invalid
theorem w4_40 : ¬ drop0% Iris.Included.validN 6 := fun h =>
  (@h K _ 0 .bot .bot (show K.bot ≼ K.bot from ⟨.e, rfl⟩)) rfl
-- `Iris.ORA.Discrete.discrete_valid` (hypothesis 2): necessary, BO: valid at step 0 only
theorem w4_41 : ¬ drop0% Iris.ORA.Discrete.discrete_valid 2 := fun h => (@h BO _ BO.f rfl : False)
-- `Iris.ORA.Discrete.discrete_ord` (hypothesis 2): necessary, TC: 0 ≼{0} 1, not 0 ≼ 1
theorem w4_42 : ¬ drop0% Iris.ORA.Discrete.discrete_ord 2 := fun h => tc_not_inc _ (@h TN _ ⟨0⟩ ⟨1⟩ tc_inc0)
-- `Iris.ORA.ordN_of_ordN_of_dist` (hypothesis 8): necessary, BO (order = inclusion): t ≼{0} t, not t ≼{0} f
theorem w4_43 : ¬ drop0% Iris.ORA.ordN_of_ordN_of_dist 8 := fun h =>
  bo_t_not_incN_f 0 (@h BO _ _ 0 .t .t .f (show BO.t ≼{0} BO.t from ⟨.f, rfl⟩))
-- `Iris.ORA.ordN_of_dist_of_ordN` (hypothesis 7): necessary, BO: f ≼{0} f, not t ≼{0} f
theorem w4_44 : ¬ drop0% Iris.ORA.ordN_of_dist_of_ordN 7 := fun h =>
  bo_t_not_incN_f 0 (@h BO _ _ 0 .t .f .f (show BO.f ≼{0} BO.f from ⟨.f, rfl⟩))
-- `Iris.ORA.ordN_iff_left` (hypothesis 7): necessary, BO: a = t, b = c = f
theorem w4_45 : ¬ drop0% Iris.ORA.ordN_iff_left 7 := fun h =>
  bo_t_not_incN_f 0 ((@h BO _ _ 0 .t .f .f).2 (show BO.f ≼{0} BO.f from ⟨.f, rfl⟩))
-- `Iris.OFE.Dist.ordN_l` (hypothesis 7): necessary, BO: a = t, b = c = f
theorem w4_46 : ¬ drop0% Iris.OFE.Dist.ordN_l 7 := fun h =>
  bo_t_not_incN_f 0 ((@h BO _ _ 0 .t .f .f).2 (show BO.f ≼{0} BO.f from ⟨.f, rfl⟩))
-- `Iris.ORA.ordN_iff_right` (hypothesis 7): necessary, BO: b = t, c = f, a = t
theorem w4_47 : ¬ drop0% Iris.ORA.ordN_iff_right 7 := fun h =>
  bo_t_not_incN_f 0 ((@h BO _ _ 0 .t .f .t).1 (show BO.t ≼{0} BO.t from ⟨.f, rfl⟩))
-- `Iris.OFE.Dist.ordN_r` (hypothesis 7): necessary, BO: b = t, c = f, a = t
theorem w4_48 : ¬ drop0% Iris.OFE.Dist.ordN_r 7 := fun h =>
  bo_t_not_incN_f 0 ((@h BO _ _ 0 .t .f .t).1 (show BO.t ≼{0} BO.t from ⟨.f, rfl⟩))
-- `Iris.ORA.ordN_dist_iff` (hypothesis 8): necessary, BO: a = f, a' = t, b = b' = f
theorem w4_49 : ¬ drop0% Iris.ORA.ordN_dist_iff 8 := fun h =>
  bo_t_not_incN_f 0 ((@h BO _ _ 0 .f .t .f .f Dist.rfl).1 (show BO.f ≼{0} BO.f from ⟨.f, rfl⟩))
-- `Iris.ORA.ordN_dist_iff` (hypothesis 9): necessary, BO: a = a' = t, b = t, b' = f
theorem w4_50 : ¬ drop0% Iris.ORA.ordN_dist_iff 9 := fun h =>
  bo_t_not_incN_f 0 ((@h BO _ _ 0 .t .t .t .f Dist.rfl).1 (show BO.t ≼{0} BO.t from ⟨.f, rfl⟩))
-- `Iris.OFE.Dist.ordN` (hypothesis 8): necessary, BO: a = f, a' = t, b = b' = f
theorem w4_51 : ¬ drop0% Iris.OFE.Dist.ordN 8 := fun h =>
  bo_t_not_incN_f 0 ((@h BO _ _ 0 .f .t .f .f Dist.rfl).1 (show BO.f ≼{0} BO.f from ⟨.f, rfl⟩))
-- `Iris.OFE.Dist.ordN` (hypothesis 9): necessary, BO: a = a' = t, b = t, b' = f
theorem w4_52 : ¬ drop0% Iris.OFE.Dist.ordN 9 := fun h =>
  bo_t_not_incN_f 0 ((@h BO _ _ 0 .t .t .t .f Dist.rfl).1 (show BO.t ≼{0} BO.t from ⟨.f, rfl⟩))
-- `Iris.Ordered.Order.trans` (hypothesis 6): necessary, BO: f ≼ f, not t ≼ f
theorem w4_53 : ¬ drop0% Iris.Ordered.Order.trans 6 := fun h =>
  bo_t_not_inc_f (@h BO _ _ .t .f .f (show BO.f ≼ BO.f from ⟨.f, rfl⟩))
-- `Iris.Ordered.Order.trans` (hypothesis 7): necessary, BO: t ≼ t, not t ≼ f
theorem w4_54 : ¬ drop0% Iris.Ordered.Order.trans 7 := fun h =>
  bo_t_not_inc_f (@h BO _ _ .t .t .f (show BO.t ≼ BO.t from ⟨.f, rfl⟩))
-- `Iris.Ordered.OrderN.trans` (hypothesis 7): necessary, BO: f ≼{0} f, not t ≼{0} f
theorem w4_55 : ¬ drop0% Iris.Ordered.OrderN.trans 7 := fun h =>
  bo_t_not_incN_f 0 (@h BO _ _ 0 .t .f .f (show BO.f ≼{0} BO.f from ⟨.f, rfl⟩))
-- `Iris.Ordered.OrderN.trans` (hypothesis 8): necessary, BO: t ≼{0} t, not t ≼{0} f
theorem w4_56 : ¬ drop0% Iris.Ordered.OrderN.trans 8 := fun h =>
  bo_t_not_incN_f 0 (@h BO _ _ 0 .t .t .f (show BO.t ≼{0} BO.t from ⟨.f, rfl⟩))
-- `Iris.ORA.ordN_of_ordN_le` (hypothesis 7): necessary, TC: 0 ≼{0} 1, not 0 ≼{1} 1
theorem w4_57 : ¬ drop0% Iris.ORA.ordN_of_ordN_le 7 := fun h => tc_not_inc1 _ (@h TN _ _ 0 1 ⟨0⟩ ⟨1⟩ tc_inc0)
-- `Iris.Ordered.OrderN.le` (hypothesis 7): necessary, TC: 0 ≼{0} 1, not 0 ≼{1} 1
theorem w4_58 : ¬ drop0% Iris.Ordered.OrderN.le 7 := fun h => tc_not_inc1 _ (@h TN _ _ 0 1 ⟨0⟩ ⟨1⟩ tc_inc0)
-- `Iris.ORA.ordN_refl` (hypothesis 3): necessary, K (order = inclusion): e not included in e
theorem w4_59 : ¬ drop0% Iris.ORA.ordN_refl 3 := fun h => k_e_not_incN_e 0 (@h K _ _ 0 .e)
-- `Iris.Ordered.Order.rfl` (hypothesis 3): necessary, K: e not included in e
theorem w4_60 : ¬ drop0% Iris.Ordered.Order.rfl 3 := fun h => k_e_not_inc_e (@h K _ _ .e)
-- `Iris.Ordered.OrderN.rfl` (hypothesis 3): necessary, K: e not included in e
theorem w4_61 : ¬ drop0% Iris.Ordered.OrderN.rfl 3 := fun h => k_e_not_incN_e 0 (@h K _ _ 0 .e)
-- `Iris.ORA.ordN_of_dist` (hypothesis 3): necessary, K: e not included in e
theorem w4_62 : ¬ drop0% Iris.ORA.ordN_of_dist 3 := fun h => k_e_not_incN_e 0 (@h K _ _ 0 .e .e Dist.rfl)
-- `Iris.ORA.ordN_of_dist` (hypothesis 7): necessary, BO (reflexive inclusion): t not included in f
theorem w4_63 : ¬ drop0% Iris.ORA.ordN_of_dist 7 := fun h => bo_t_not_incN_f 0 (@h BO _ _ boRefl 0 .t .f)
-- `Iris.OFE.Dist.to_ordN` (hypothesis 3): necessary, K: e not included in e
theorem w4_64 : ¬ drop0% Iris.OFE.Dist.to_ordN 3 := fun h => k_e_not_incN_e 0 (@h K _ _ 0 .e .e Dist.rfl)
-- `Iris.OFE.Dist.to_ordN` (hypothesis 7): necessary, BO (reflexive inclusion): t not included in f
theorem w4_65 : ¬ drop0% Iris.OFE.Dist.to_ordN 7 := fun h => bo_t_not_incN_f 0 (@h BO _ _ boRefl 0 .t .f)
-- `Iris.ORA.validN_of_ord` (hypothesis 6): necessary, K (order = inclusion): bot ≼ bot, bot invalid
theorem w4_66 : ¬ drop0% Iris.ORA.validN_of_ord 6 := fun h =>
  (@h K _ 0 .bot .bot (show K.bot ≼ K.bot from ⟨.e, rfl⟩)) rfl
-- `Iris.Ordered.Order.validN` (hypothesis 6): necessary, K (order = inclusion): bot ≼ bot, bot invalid
theorem w4_67 : ¬ drop0% Iris.Ordered.Order.validN 6 := fun h =>
  (@h K _ 0 .bot .bot (show K.bot ≼ K.bot from ⟨.e, rfl⟩)) rfl
-- `Iris.ORA.pcore_mono_ord'` (hypothesis 6): necessary, K: x = y = u, cx = e, e not included in core u = u
theorem w4_68 : ¬ drop0% Iris.ORA.pcore_mono_ord' 6 := fun h => by
  obtain ⟨cy, hcy, hi⟩ := @h K _ .u .u .e (show K.u ≼ K.u from ⟨.u, rfl⟩); cases hcy
  exact k_e_not_inc_u hi
-- `Iris.ORA.pcore_monoN_ord'` (hypothesis 7): necessary, K: x = y = u, cx = e, e not included in core u = u
theorem w4_69 : ¬ drop0% Iris.ORA.pcore_monoN_ord' 7 := fun h => by
  obtain ⟨cy, hcy, hi⟩ := @h K _ 0 .u .u .e (show K.u ≼{0} K.u from ⟨.u, rfl⟩); cases hcy
  exact k_e_not_incN_u 0 hi
-- `Iris.ORA.discrete_inc_l` (hypothesis 4): necessary, Option (Excl TN): some (excl 1) ≼{0} some (excl 2) (valid) via none, not included
theorem w4_5 : ¬ drop0% Iris.ORA.discrete_inc_l 4 := fun h => by
  obtain ⟨z, hz⟩ := @h (Option (Excl TN)) _ (some (.excl ⟨1⟩)) (some (.excl ⟨2⟩)) trivial ⟨none, rfl⟩
  cases z with
  | none => cases hz
  | some w => cases w <;> cases hz
-- `Iris.ORA.pcore_mono` (hypothesis 3): necessary, MO (max, order True, core 2 = 0): 1 ≼ 2, core 1 = 1 not included in core 2 = 0
theorem w4_70 : ¬ drop0% Iris.ORA.pcore_mono 3 := fun h => by
  obtain ⟨cy, hcy, hi⟩ := @h MO _ ⟨1⟩ ⟨1⟩ ⟨2⟩ ⟨⟨2⟩, rfl⟩ rfl
  obtain rfl := Option.some.inj hcy
  exact mo_not_inc hi
-- `Iris.ORA.pcore_mono` (hypothesis 7): necessary, K: x = y = u, cx = e not included in core u = u
theorem w4_71 : ¬ drop0% Iris.ORA.pcore_mono 7 := fun h => by
  obtain ⟨cy, hcy, hi⟩ := @h K _ K.e _ K.u K.u ⟨.u, rfl⟩; cases hcy
  exact k_e_not_inc_u hi
-- `Iris.ORA.pcore_mono'` (hypothesis 2): necessary, MO (max, order True, core 2 = 0): 1 ≼ 2, core 1 = 1 not included in core 2 = 0
theorem w4_72 : ¬ drop0% Iris.ORA.pcore_mono' 2 := fun h => by
  obtain ⟨cy, hcy, hi⟩ := @h MO _ ⟨1⟩ ⟨2⟩ ⟨1⟩ ⟨⟨2⟩, rfl⟩ rfl
  obtain rfl := Option.some.inj hcy
  exact mo_not_inc hi
-- `Iris.ORA.pcore_mono'` (hypothesis 7): necessary, K: x = y = u, cx = e not included in core u = u
theorem w4_73 : ¬ drop0% Iris.ORA.pcore_mono' 7 := fun h => by
  obtain ⟨cy, hcy, hi⟩ := @h K _ _ .u .u .e ⟨.u, rfl⟩; cases hcy
  exact k_e_not_inc_u hi
-- `Iris.ORA.pcore_monoN'` (hypothesis 2): necessary, MO (max, order True, core 2 = 0): 1 ≼{0} 2, core 1 = 1 not included in core 2 = 0
theorem w4_74 : ¬ drop0% Iris.ORA.pcore_monoN' 2 := fun h => by
  obtain ⟨cy, hcy, hi⟩ := @h MO _ 0 ⟨1⟩ ⟨2⟩ ⟨1⟩ ⟨⟨2⟩, rfl⟩ (OFE.Dist.of_eq rfl)
  obtain rfl := Option.some.inj hcy
  exact mo_not_incN 0 hi
-- `Iris.ORA.pcore_monoN'` (hypothesis 8): necessary, K: x = y = u, cx = e not included in core u = u
theorem w4_75 : ¬ drop0% Iris.ORA.pcore_monoN' 8 := fun h => by
  obtain ⟨cy, hcy, hi⟩ := @h K _ _ 0 .u .u .e ⟨.u, rfl⟩; cases hcy
  exact k_e_not_incN_u 0 hi
-- `Iris.ORA.pcore_op_mono` (hypothesis 2): necessary, MO (max, core 2 = 0): core (1 • 2) = 0 is not 1 • cy
theorem w4_76 : ¬ drop0% Iris.ORA.pcore_op_mono 2 := fun h => by
  obtain ⟨cy, hcy⟩ := @h MO _ ⟨1⟩ ⟨1⟩ rfl ⟨2⟩
  have := congrArg (fun o => (Option.getD o ⟨5⟩).v) hcy; change 0 = max 1 cy.v at this; omega
-- `Iris.ORA.op_monoN_ord` (hypothesis 7): necessary, BO (or, order = inclusion): x = t, x' = f, y = y' = f
theorem w4_77 : ¬ drop0% Iris.ORA.op_monoN_ord 7 := fun h =>
  bo_t_not_incN_f 0 (@h BO _ 0 .t .f .f .f (show BO.f ≼{0} BO.f from ⟨.f, rfl⟩))
-- `Iris.ORA.op_monoN_ord` (hypothesis 8): necessary, BO: x = x' = f, y = t, y' = f
theorem w4_78 : ¬ drop0% Iris.ORA.op_monoN_ord 8 := fun h =>
  bo_t_not_incN_f 0 (@h BO _ 0 .f .f .t .f (show BO.f ≼{0} BO.f from ⟨.f, rfl⟩))
-- `Iris.ORA.op_mono_ord` (hypothesis 6): necessary, BO: x = t, x' = f, y = y' = f
theorem w4_79 : ¬ drop0% Iris.ORA.op_mono_ord 6 := fun h =>
  bo_t_not_inc_f (@h BO _ .t .f .f .f (show BO.f ≼ BO.f from ⟨.f, rfl⟩))
-- `Iris.ORA.op_mono_ord` (hypothesis 7): necessary, BO: x = x' = f, y = t, y' = f
theorem w4_80 : ¬ drop0% Iris.ORA.op_mono_ord 7 := fun h =>
  bo_t_not_inc_f (@h BO _ .f .f .t .f (show BO.f ≼ BO.f from ⟨.f, rfl⟩))
-- `Iris.ORA.op_extend_ord` (hypothesis 6): necessary, TC: 0 • 0 = 2 ≼{0} 1 (1 invalid), nothing is 1-included in 1
theorem w4_81 : ¬ drop0% Iris.ORA.op_extend_ord 6 := fun h => by
  obtain ⟨z₁, z₂, hz, -⟩ := @h TN _ 0 ⟨1⟩ ⟨0⟩ ⟨0⟩ (show (Op.op ⟨0⟩ ⟨0⟩ : TN) ≼{0} ⟨1⟩ from ⟨⟨0⟩, rfl⟩)
  exact tc_not_inc1 _ hz
-- `Iris.ORA.op_extend_ord` (hypothesis 7): necessary, K: u valid, y1 = y2 = e, e • e = bot not included in u
theorem w4_82 : ¬ drop0% Iris.ORA.op_extend_ord 7 := fun h => by
  obtain ⟨z₁, z₂, ⟨w, hw⟩, h1, h2⟩ := @h K _ 0 .u .e .e (show K.u ≠ K.bot by decide)
  obtain rfl : z₁ = K.e := h1
  obtain rfl : z₂ = K.e := h2
  have hw' : K.u = kOp (kOp .e .e) w := hw
  cases w <;> cases hw'
-- `Iris.Increasing.of_ordNR` (hypothesis 6): necessary, BA (and, order Eq): true is increasing, false is not
theorem w4_83 : ¬ drop0% Iris.Increasing.of_ordNR 6 := fun h => ba_not_inc (@h BA _ 0 ⟨true⟩ ⟨false⟩ baTInc)
-- `Iris.Increasing.of_dist` (hypothesis 5): necessary, BA: x = y = false, false not increasing
theorem w4_84 : ¬ drop0% Iris.Increasing.of_dist 5 := fun h => ba_not_inc (@h BA _ 0 ⟨false⟩ ⟨false⟩ Dist.rfl)
-- `Iris.Increasing.of_dist` (hypothesis 6): necessary, BA: true increasing, false not
theorem w4_85 : ¬ drop0% Iris.Increasing.of_dist 6 := fun h => ba_not_inc (@h BA _ 0 ⟨true⟩ ⟨false⟩ baTInc)
-- `Iris.Increasing.of_ordN` (hypothesis 5): necessary, BA: x = y = false (order Eq), false not increasing
theorem w4_86 : ¬ drop0% Iris.Increasing.of_ordN 5 := fun h =>
  ba_not_inc (@h BA _ 0 ⟨false⟩ ⟨false⟩ (show (⟨false⟩ : BA) = ⟨false⟩ from rfl))
-- `Iris.Increasing.of_ordN` (hypothesis 6): necessary, BA: true increasing, false not
theorem w4_87 : ¬ drop0% Iris.Increasing.of_ordN 6 := fun h => ba_not_inc (@h BA _ 0 ⟨true⟩ ⟨false⟩ baTInc)
-- `Iris.Increasing.of_ord` (hypothesis 4): necessary, BA: x = y = false (order Eq), false not increasing
theorem w4_88 : ¬ drop0% Iris.Increasing.of_ord 4 := fun h =>
  ba_not_inc (@h BA _ ⟨false⟩ ⟨false⟩ (show (⟨false⟩ : BA) = ⟨false⟩ from rfl))
-- `Iris.Increasing.of_ord` (hypothesis 5): necessary, BA: true increasing, false not
theorem w4_89 : ¬ drop0% Iris.Increasing.of_ord 5 := fun h => ba_not_inc (@h BA _ ⟨true⟩ ⟨false⟩ baTInc)
-- `Iris.Increasing.of_ordR` (hypothesis 4): necessary, BA: x = y = false, false not increasing
theorem w4_90 : ¬ drop0% Iris.Increasing.of_ordR 4 := fun h => ba_not_inc (@h BA _ ⟨false⟩ ⟨false⟩ Ordered.OrderR.rfl)
-- `Iris.Increasing.of_ordR` (hypothesis 5): necessary, BA: true increasing, false not
theorem w4_91 : ¬ drop0% Iris.Increasing.of_ordR 5 := fun h => ba_not_inc (@h BA _ ⟨true⟩ ⟨false⟩ baTInc)
-- `Iris.Increasing.ordN` (hypothesis 4): necessary, BA (order Eq): true ≠ false • true
theorem w4_92 : ¬ drop0% Iris.Increasing.ordN 4 := fun h => by
  have := congrArg BA.b (show (⟨true⟩ : BA) = Op.op ⟨false⟩ ⟨true⟩ from @h BA _ 0 ⟨false⟩ ⟨true⟩)
  cases this
-- `Iris.Increasing.op` (hypothesis 4): necessary, BA: x = false, y = true increasing, false • true = false not increasing
theorem w4_93 : ¬ drop0% Iris.Increasing.op 4 := fun h => ba_not_inc (@h BA _ ⟨false⟩ ⟨true⟩ baTInc)
-- `Iris.Increasing.op` (hypothesis 5): necessary, BA: x = true increasing, y = false, true • false = false not increasing
theorem w4_94 : ¬ drop0% Iris.Increasing.op 5 := fun h => ba_not_inc (@h BA _ ⟨true⟩ ⟨false⟩ baTInc)
-- `Iris.instIncreasingOfCoreId` (hypothesis 3): necessary, BA: false is not increasing
theorem w4_95 : ¬ drop0% Iris.instIncreasingOfCoreId 3 := fun h => ba_not_inc (@h BA _ ⟨false⟩)
