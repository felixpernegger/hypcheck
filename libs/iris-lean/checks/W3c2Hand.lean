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

namespace W3c2
open Iris Iris.OFE Iris.Std

/-- Truncation OFE on naturals (copied from Probe1/W2c1): dist n x y iff min x (n+1) = min y (n+1). Not discrete (1 and 2 agree at 0). -/
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

/-- Discrete ORA on booleans (copied from Probe1/W2c1): op is and, no core, order is equality. -/
structure BA where b : Bool
instance : COFE BA := COFE.ofDiscrete _
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

/-- Discrete ORA on Nat (copied from W1c4/W2c1): op = max, all valid, order True, core n = n except core 2 = 0. Not OrdInc. -/
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

/-- Discrete total CMRA on Nat: op = min, core = id, n-valid iff n ≤ value, never valid. Not ORA.Discrete. -/
structure VS where v : Nat
instance : OFE VS := OFE.ofDiscrete VS
instance : OFE.Discrete VS := ⟨fun h => h⟩
@[instance_reducible] def vsData : CMRAData VS where
  op x y := ⟨min x.v y.v⟩
  op_ne := ⟨fun {_ a b} h => by change a = b at h; subst h; rfl⟩
  assoc {x y z} := congrArg VS.mk (Nat.min_assoc x.v y.v z.v).symm
  comm {x y} := congrArg VS.mk (Nat.min_comm x.v y.v)
  pcore := some
  pcore_ne {n x y cx} h e := by obtain rfl : x = y := h; exact ⟨cx, e, Dist.rfl⟩
  pcore_idem {x cx} e := by cases e; rfl
  ValidN n x := n ≤ x.v
  Valid _ := False
  validN_ne h v := by obtain rfl := h; exact v
  valid_iff_validN {x} := ⟨False.elim, fun h => absurd (h (x.v+1)) (by omega)⟩
  validN_succ h := Nat.le_of_succ_le h
  validN_op_left {n x y} h := by
    have : n ≤ min x.v y.v := h
    show n ≤ x.v; omega
  pcore_op_left {x cx} e := by cases e; exact congrArg VS.mk (Nat.min_self _)
  extend {n x y₁ y₂} v h := ⟨y₁, y₂, h, Dist.rfl, Dist.rfl⟩
  pcore_op_mono {x cx} e y := ⟨y, by cases e; rfl⟩
instance vsCMRA : CMRA VS := ORA.ofCMRAData vsData
instance vsTotal : IsTotal VS := ⟨fun x => ⟨x, rfl⟩⟩
theorem vs_v0 : ✓{0} (⟨0⟩ : VS) := Nat.le_refl 0
theorem vs_1 : ✓{1} (⟨1⟩ : VS) := Nat.le_refl 1
theorem vs_not1 : ¬ ✓{1} (⟨0⟩ : VS) := fun h => Nat.not_succ_le_zero 0 h
theorem vs_not_valid (x : VS) : ¬ ✓ x := fun h => h

/-- Five-element discrete ORA: only T • Z = TZ is defined (valid), every other product is the invalid B. No core, order equality. -/
inductive PZ | T | F | Z | TZ | B
  deriving DecidableEq
instance : COFE PZ := COFE.ofDiscrete _
instance : OFE.Discrete PZ := ⟨fun h => h⟩
def pzOp : PZ → PZ → PZ
  | .T, .Z => .TZ
  | .Z, .T => .TZ
  | _, _ => .B
@[instance_reducible] def pzData : DiscreteORAData PZ where
  pcore _ := none
  op := pzOp
  Valid x := x ≠ .B
  Order := Eq
  assoc x y z := by cases x <;> cases y <;> cases z <;> rfl
  comm x y := by cases x <;> cases y <;> rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left x y h := by cases x <;> cases y <;> simp_all [pzOp]
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ h := h ▸ rfl
  valid_of_ord _ _ h v := h ▸ v
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ hx hxy := hxy ▸ hx
instance pzORA : ORA PZ := ORA.ofDiscreteORAData pzData
/-- Homomorphism Excl BA → PZ: excl true ↦ T, excl false ↦ F, invalid ↦ B. -/
def gEP : Excl BA → PZ
  | .excl ⟨true⟩ => .T
  | .excl ⟨false⟩ => .F
  | .invalid => .B
/-- Swap of T and F on PZ (validity preserving, not a homomorphism). -/
def swTF : PZ → PZ
  | .T => .F
  | .F => .T
  | x => x

abbrev EU := Excl Unit
abbrev xe : EU := .excl ()
abbrev xi : EU := .invalid
abbrev OEU := Option EU

theorem xe_ok (n : Nat) : ✓{n} xe := trivial
theorem xi_bad (n : Nat) : ¬ ✓{n} xi := fun h => h
theorem xe_not_upd : ¬ (xe ~~> xi) := fun h => h 0 none trivial
theorem xi_updP (P : EU → Prop) : xi ~~>: P := fun n mz v => by cases mz <;> exact v.elim

/-- UPreds: constant True/False, and true only at step 0. -/
def uT (M) [UORA M] : UPred M := ⟨fun _ _ => True, fun _ _ _ => trivial⟩
def uF (M) [UORA M] : UPred M := ⟨fun _ _ => False, fun h _ _ => h⟩
def u0 (M) [UORA M] : UPred M := ⟨fun n _ => n = 0, fun {n1 n2 _ _} h _ hle => show n2 = 0 by have : n1 = 0 := h; omega⟩
/-- On Option (Excl Unit): holds iff the resource is not none. -/
def uS : UPred OEU := ⟨fun _ x => x.val ≠ none, fun {n1 n2 x1 x2} h ho _ => by
  obtain ⟨v1, _⟩ := x1; obtain ⟨v2, _⟩ := x2
  cases v1 with
  | none => exact absurd rfl h
  | some a => cases v2 with
    | none => exact ho.elim
    | some b => exact fun e => nomatch e⟩

end W3c2
open W3c2 Iris Iris.OFE Iris.Std

namespace W3c2
open Iris Iris.OFE Iris.Std

/-- Partial maps Pos → Option V (library LawfulPartialMap instance). -/
abbrev HF := fun V : Type => Pos → Option V

theorem dls_op_empty (x : DisjointLeibnizSet CoPset) : x • (∅ : DisjointLeibnizSet CoPset) = x :=
  ORA.comm'.trans (ORA.pcore_op_left' rfl)
theorem dls_empty_op (x : DisjointLeibnizSet CoPset) : (∅ : DisjointLeibnizSet CoPset) • x = x :=
  ORA.pcore_op_left' rfl
theorem mem_one : (1 : Pos) ∈ ({1} : CoPset) := LawfulSet.mem_singleton.mpr rfl

theorem ba_tf : ¬ ((⟨true⟩ : BA) ≼ₒ* ⟨false⟩) := by
  rintro (h | h)
  · cases h.dist (n := 0)
  · cases h
theorem opt_ba_tf : ¬ ((some ⟨true⟩ : Option BA) ≼ₒ some ⟨false⟩) := ba_tf
/-- In BA-valued ReservationMaps, singleton 1 true is included in singleton 1 false but not ordered below it. -/
theorem rm_ba_inc : (ReservationMap.singleton 1 ⟨true⟩ : ReservationMap BA HF) ≼ ReservationMap.singleton 1 ⟨false⟩ :=
  ⟨ReservationMap.singleton 1 ⟨false⟩, ReservationMap.singleton_op (H := HF) 1 (⟨true⟩ : BA) ⟨false⟩⟩
theorem rm_ba_not_ord : ¬ ((ReservationMap.singleton 1 ⟨true⟩ : ReservationMap BA HF) ≼ₒ ReservationMap.singleton 1 ⟨false⟩) :=
  fun h => opt_ba_tf (h.1 1)

end W3c2
open W3c2 Iris Iris.OFE Iris.Std

namespace W3c2
open Iris

/-- The ordinal omega^2 as lexicographic pairs of naturals: a step index (SIdx) with limit elements such as (1, 0). -/
structure O2 where
  a : Nat
  b : Nat
  deriving DecidableEq
instance o2LT : LT O2 := ⟨fun x y => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b)⟩
instance o2LE : LE O2 := ⟨fun x y => x < y ∨ x = y⟩
instance o2Zero : Zero O2 := ⟨⟨0, 0⟩⟩
theorem o2_lt {x y : O2} : x < y ↔ x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b) := Iff.rfl
instance o2DecLt (x y : O2) : Decidable (x < y) := decidable_of_iff _ o2_lt.symm
theorem o2_le {x y : O2} : x ≤ y ↔ x < y ∨ x = y := Iff.rfl
theorem o2_eq {x y : O2} : x = y ↔ x.a = y.a ∧ x.b = y.b := by
  cases x; cases y; simp
theorem o2_wf : WellFounded (fun x y : O2 => x < y) := by
  refine Subrelation.wf ?_ (invImage (fun x : O2 => (x.a, x.b)) (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ ⟨_, Nat.lt_wfRel.wf⟩)).wf
  intro x y h
  show Prod.Lex _ _ (x.a, x.b) (y.a, y.b)
  rcases h with h | ⟨h1, h2⟩
  · exact Prod.Lex.left _ _ h
  · rw [h1]; exact Prod.Lex.right _ h2
instance o2SIdx : SIdx O2 where
  succ x := ⟨x.a, x.b + 1⟩
  lt_trans {n m p} h1 h2 := by rw [o2_lt] at *; omega
  lt_wf := o2_wf
  lt_trichotomyT n m :=
    if h : n < m then .inl h
    else if h' : n = m then .inr (.inl h')
    else .inr (.inr (by rw [o2_lt] at h ⊢; rw [o2_eq] at h'; omega))
  le_lteq := Iff.rfl
  not_lt_zero n h := by rw [o2_lt] at h; change n.a < 0 ∨ (n.a = 0 ∧ n.b < 0) at h; omega
  lt_succ_self n := Or.inr ⟨rfl, Nat.lt_succ_self _⟩
  succ_le_of_lt {n m} h := by
    rw [o2_le, o2_lt, o2_eq]; rw [o2_lt] at h
    show (n.a < m.a ∨ (n.a = m.a ∧ n.b + 1 < m.b)) ∨ (n.a = m.a ∧ n.b + 1 = m.b)
    omega
  weak_case n :=
    if h : n.b = 0 then .inr (fun m hm => by
      rw [o2_lt] at hm ⊢; show m.a < n.a ∨ (m.a = n.a ∧ m.b + 1 < n.b); omega)
    else .inl ⟨⟨n.a, n.b - 1⟩, by rw [o2_eq]; show n.a = n.a ∧ n.b = n.b - 1 + 1; omega⟩
/-- (1, 0) is a limit index of O2. -/
theorem o2lim : SIdx.Limit (⟨1, 0⟩ : O2) where
  succ_lt m hm := by
    rw [o2_lt] at hm ⊢; show m.a < 1 ∨ (m.a = 1 ∧ m.b + 1 < 0); change m.a < 1 ∨ (m.a = 1 ∧ m.b < 0) at hm; omega
  ne_zero e := absurd (congrArg O2.a e) (by decide)

end W3c2
open W3c2

-- `Iris.Update.of_updateP` (hypothesis 4): necessary, Excl Unit: excl () ~~> invalid fails at frame none
theorem w32_u1 : ¬ drop0% Iris.Update.of_updateP 4 := fun h => xe_not_upd (@h EU _ xe xi)
-- `Iris.UpdateP.id` (hypothesis 4): necessary, Excl Unit, P = False, x = excl ()
theorem w32_u2 : ¬ drop0% Iris.UpdateP.id 4 := fun h => by
  obtain ⟨_, hp, _⟩ := @h EU _ (fun _ => False) xe 0 none trivial; exact hp
-- `Iris.Update.trans` (hypothesis 5): necessary, Excl Unit, x = excl (), y = z = invalid
theorem w32_u3 : ¬ drop0% Iris.Update.trans 5 := fun h => xe_not_upd (@h EU _ xe xi xi Update.id)
-- `Iris.Update.trans` (hypothesis 6): necessary, Excl Unit, x = y = excl (), z = invalid
theorem w32_u4 : ¬ drop0% Iris.Update.trans 6 := fun h => xe_not_upd (@h EU _ xe xe xi Update.id)
-- `Iris.UpdateP.trans` (hypothesis 5): necessary, Excl Unit, P = Q = False, x = excl ()
theorem w32_u5 : ¬ drop0% Iris.UpdateP.trans 5 := fun h => by
  obtain ⟨_, hp, _⟩ := @h EU _ (fun _ => False) (fun _ => False) xe (fun _ h => h.elim) 0 none trivial; exact hp
-- `Iris.UpdateP.trans` (hypothesis 6): necessary, Excl Unit, P = True, Q = False, x = excl ()
theorem w32_u6 : ¬ drop0% Iris.UpdateP.trans 6 := fun h => by
  obtain ⟨_, hp, _⟩ := @h EU _ (fun _ => True) (fun _ => False) xe (UpdateP.id trivial) 0 none trivial; exact hp
-- `Iris.Update.transP` (hypothesis 5): necessary, Excl Unit, x = excl (), y = invalid (updates to anything), Q = False
theorem w32_u7 : ¬ drop0% Iris.Update.transP 5 := fun h => by
  obtain ⟨_, hp, _⟩ := @h EU _ (fun _ => False) xe xi (xi_updP _) 0 none trivial; exact hp
-- `Iris.Update.transP` (hypothesis 6): necessary, Excl Unit, x = y = excl (), Q = False
theorem w32_u8 : ¬ drop0% Iris.Update.transP 6 := fun h => by
  obtain ⟨_, hp, _⟩ := @h EU _ (fun _ => False) xe xe Update.id 0 none trivial; exact hp
-- `Iris.UpdateP.weaken` (hypothesis 5): necessary, Excl Unit, P = Q = False
theorem w32_u9 : ¬ drop0% Iris.UpdateP.weaken 5 := fun h => by
  obtain ⟨_, hp, _⟩ := @h EU _ (fun _ => False) (fun _ => False) xe (fun _ h => h) 0 none trivial; exact hp
-- `Iris.UpdateP.weaken` (hypothesis 6): necessary, Excl Unit, P = True, Q = False
theorem w32_u10 : ¬ drop0% Iris.UpdateP.weaken 6 := fun h => by
  obtain ⟨_, hp, _⟩ := @h EU _ (fun _ => True) (fun _ => False) xe (UpdateP.id trivial) 0 none trivial; exact hp
-- `Iris.Update.exclusive` (hypothesis 4): necessary, Option (Excl Unit): none ~~> some (excl ()) fails at frame some (excl ())
theorem w32_u11 : ¬ drop0% Iris.Update.exclusive 4 := fun h =>
  absurd (@h OEU _ none (some xe) trivial 0 (some (some xe)) trivial) (fun v => v)
-- `Iris.Update.exclusive` (hypothesis 5): necessary, Excl Unit, x = excl (), y = invalid
theorem w32_u12 : ¬ drop0% Iris.Update.exclusive 5 := fun h => xe_not_upd (@h EU _ xe xi inferInstance)
-- `Iris.UpdateP.op` (hypothesis 7): necessary, Unit, P = R = False, Q = True
theorem w32_u13 : ¬ drop0% Iris.UpdateP.op 7 := fun h => by
  obtain ⟨_, hr, _⟩ := @h Unit _ (fun _ => False) (fun _ => True) (fun _ => False) () () (UpdateP.id trivial)
    (fun _ _ hp _ => hp) 0 none trivial; exact hr
-- `Iris.UpdateP.op` (hypothesis 8): necessary, Unit, Q = R = False, P = True
theorem w32_u14 : ¬ drop0% Iris.UpdateP.op 8 := fun h => by
  obtain ⟨_, hr, _⟩ := @h Unit _ (fun _ => True) (fun _ => False) (fun _ => False) () () (UpdateP.id trivial)
    (fun _ _ _ hq => hq) 0 none trivial; exact hr
-- `Iris.UpdateP.op` (hypothesis 9): necessary, Unit, P = Q = True, R = False
theorem w32_u15 : ¬ drop0% Iris.UpdateP.op 9 := fun h => by
  obtain ⟨_, hr, _⟩ := @h Unit _ (fun _ => True) (fun _ => True) (fun _ => False) () () (UpdateP.id trivial)
    (UpdateP.id trivial) 0 none trivial; exact hr
-- `Iris.UpdateP.op'` (hypothesis 6): necessary, Unit, P = False, Q = True
theorem w32_u16 : ¬ drop0% Iris.UpdateP.op' 6 := fun h => by
  obtain ⟨_, ⟨_, _, _, hp, _⟩, _⟩ := @h Unit _ (fun _ => False) (fun _ => True) () () (UpdateP.id trivial) 0 none trivial
  exact hp
-- `Iris.UpdateP.op'` (hypothesis 7): necessary, Unit, P = True, Q = False
theorem w32_u17 : ¬ drop0% Iris.UpdateP.op' 7 := fun h => by
  obtain ⟨_, ⟨_, _, _, _, hq⟩, _⟩ := @h Unit _ (fun _ => True) (fun _ => False) () () (UpdateP.id trivial) 0 none trivial
  exact hq
-- `Iris.Update.op` (hypothesis 6): necessary, Option (Excl Unit), x1 = some (excl ()), y1 = some invalid, x2 = y2 = none
theorem w32_u18 : ¬ drop0% Iris.Update.op 6 := fun h =>
  absurd (@h OEU _ (some xe) none (some xi) none Update.id 0 none trivial) (fun v => v)
-- `Iris.Update.op` (hypothesis 7): necessary, Option (Excl Unit), x1 = y1 = none, x2 = some (excl ()), y2 = some invalid
theorem w32_u19 : ¬ drop0% Iris.Update.op 7 := fun h =>
  absurd (@h OEU _ none (some xe) none (some xi) Update.id 0 none trivial) (fun v => v)
-- `Iris.Update.ord` (hypothesis 4): necessary, Excl Unit, y = excl (), x = invalid
theorem w32_u20 : ¬ drop0% Iris.Update.ord 4 := fun h => xe_not_upd (@h EU _ xi xe)
-- `Iris.Update.included` (hypothesis 4): necessary, Excl Unit, y = excl (), x = invalid
theorem w32_u21 : ¬ drop0% Iris.Update.included 4 := fun h => xe_not_upd (@h EU _ xi xe)
-- `Iris.Update.valid0` (hypothesis 4): necessary, Excl Unit, x = excl (), y = invalid
theorem w32_u22 : ¬ drop0% Iris.Update.valid0 4 := fun h => xe_not_upd (@h EU _ xe xi)
-- `Iris.UpdateP.total` (hypothesis 4): necessary, Excl Unit (no core), x = excl (), P = False: right side vacuous (excl () • z invalid)
theorem w32_u23 : ¬ drop0% Iris.UpdateP.total 4 := fun h => by
  obtain ⟨_, hp, _⟩ := (@h EU _ xe (fun _ => False)).mpr (fun n z v => by cases z <;> exact v.elim) 0 none trivial
  exact hp
-- `Iris.Update.total` (hypothesis 4): necessary, Excl Unit, x = excl (), y = invalid: right side vacuous
theorem w32_u24 : ¬ drop0% Iris.Update.total 4 := fun h =>
  xe_not_upd ((@h EU _ xe xi).mpr (fun n z v => by cases z <;> exact v.elim))
-- `Iris.UpdateP.discrete` (hypothesis 4): necessary, VS (n-valid iff n ≤ v, never valid), x = 0, P = False
theorem w32_u25 : ¬ drop0% Iris.UpdateP.discrete 4 := fun h => by
  obtain ⟨_, hp, _⟩ := (@h VS _ ⟨0⟩ (fun _ => False)).mpr (fun mz v => (vs_not_valid _ v).elim) 0 none vs_v0
  exact hp
-- `Iris.Update.discrete` (hypothesis 2): necessary, VS, x = 1, y = 0: 1-valid vs not, right side vacuous
theorem w32_u26 : ¬ drop0% Iris.Update.discrete 2 := fun h =>
  vs_not1 ((@h VS _ ⟨1⟩ ⟨0⟩).mpr (fun mz v => (vs_not_valid _ v).elim) 1 none vs_1)
-- `Iris.UpdateP.discrete_total` (hypothesis 4): necessary, VS (total, not discrete), x = 0, P = False
theorem w32_u27 : ¬ drop0% Iris.UpdateP.discrete_total 4 := fun h => by
  obtain ⟨_, hp, _⟩ := (@h VS _ ⟨0⟩ (fun _ => False) vsTotal).mpr (fun z v => (vs_not_valid _ v).elim) 0 none vs_v0
  exact hp
-- `Iris.UpdateP.discrete_total` (hypothesis 5): necessary, Excl Unit (discrete, no core), x = excl (), P = False
theorem w32_u28 : ¬ drop0% Iris.UpdateP.discrete_total 5 := fun h => by
  obtain ⟨_, hp, _⟩ := (@h EU _ xe (fun _ => False) inferInstance).mpr (fun z v => by cases z <;> exact v.elim) 0 none trivial
  exact hp
-- `Iris.Update.discrete_total` (hypothesis 4): necessary, VS, x = 1, y = 0
theorem w32_u29 : ¬ drop0% Iris.Update.discrete_total 4 := fun h =>
  vs_not1 ((@h VS _ ⟨1⟩ ⟨0⟩ vsTotal).mpr (fun z v => (vs_not_valid _ v).elim) 1 none vs_1)
-- `Iris.Update.discrete_total` (hypothesis 5): necessary, Excl Unit, x = excl (), y = invalid
theorem w32_u30 : ¬ drop0% Iris.Update.discrete_total 5 := fun h =>
  xe_not_upd ((@h EU _ xe xi inferInstance).mpr (fun z v => by cases z <;> exact v.elim))

-- `Iris.UpdateP.iso` (hypothesis 9): necessary, beta = Excl BA, alpha = PZ, g = gEP homomorphism (excl true ↦ T, excl false ↦ F), y = excl true updating to excl false: frame Z fits T but not F
theorem w32_v1 : ¬ drop0% Iris.UpdateP.iso 9 := fun h => by
  obtain ⟨y', e, v⟩ := @h PZ (Excl BA) _ _ (fun _ => .invalid) gEP (.excl ⟨true⟩) (· = .excl ⟨false⟩) (· = PZ.F)
    (fun y1 y2 => by rcases y1 with ⟨⟨_ | _⟩⟩ | _ <;> rcases y2 with ⟨⟨_ | _⟩⟩ | _ <;> rfl)
    (fun n y => by
      rcases y with ⟨⟨_ | _⟩⟩ | _
      · exact ⟨fun _ => trivial, fun _ e => nomatch e⟩
      · exact ⟨fun _ => trivial, fun _ e => nomatch e⟩
      · exact ⟨fun h => (h rfl).elim, fun h => h.elim⟩)
    (fun n mz v => ⟨.excl ⟨false⟩, rfl, by cases mz with | none => exact trivial | some z => cases z <;> exact v.elim⟩)
    (fun y' e => by subst e; rfl) 0 (some PZ.Z) (fun e => nomatch e)
  subst e; exact v rfl
-- `Iris.UpdateP.iso` (hypothesis 10): necessary, alpha = beta = PZ, f = g = swap T/F (validity preserving, not a homomorphism), y = F updating to Z
theorem w32_v2 : ¬ drop0% Iris.UpdateP.iso 10 := fun h => by
  obtain ⟨y', e, v⟩ := @h PZ PZ _ _ swTF swTF PZ.F (· = PZ.Z) (· = PZ.Z)
    (fun x => by cases x <;> rfl)
    (fun n y => by cases y <;> first | exact Iff.rfl | exact ⟨fun _ e => (nomatch e), fun _ e => (nomatch e)⟩)
    (fun n mz v => ⟨PZ.Z, rfl, by cases mz with | none => exact (fun e => nomatch e) | some z => cases z <;> exact (v rfl).elim⟩)
    (fun y' e => by subst e; rfl) 0 (some PZ.Z) (fun e => nomatch e)
  subst e; exact v rfl
-- `Iris.UpdateP.iso` (hypothesis 11): necessary, alpha = Unit, beta = Excl Unit, y = invalid (updates to False), Q = False
theorem w32_v3 : ¬ drop0% Iris.UpdateP.iso 11 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit EU _ _ (fun _ => xi) (fun _ => ()) xi (fun _ => False) (fun _ => False)
    (fun _ => rfl) (fun _ _ => rfl) (xi_updP _) (fun _ h => h) 0 none trivial
  exact hq
-- `Iris.UpdateP.iso` (hypothesis 12): necessary, alpha = beta = Unit, f = g = id, P = Q = False
theorem w32_v4 : ¬ drop0% Iris.UpdateP.iso 12 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit Unit _ _ id id () (fun _ => False) (fun _ => False)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => Iff.rfl) (fun _ h => h) 0 none trivial
  exact hq
-- `Iris.UpdateP.iso` (hypothesis 13): necessary, alpha = beta = Unit, f = g = id, P = True, Q = False
theorem w32_v5 : ¬ drop0% Iris.UpdateP.iso 13 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit Unit _ _ id id () (fun _ => True) (fun _ => False)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => Iff.rfl) (UpdateP.id trivial) 0 none trivial
  exact hq
-- `Iris.UpdateP.iso'` (hypothesis 8): necessary, as for iso hypothesis 9 (beta = Excl BA, alpha = PZ, g = gEP)
theorem w32_v6 : ¬ drop0% Iris.UpdateP.iso' 8 := fun h => by
  obtain ⟨_, ⟨y', e1, e2⟩, v⟩ := @h PZ (Excl BA) _ _ (fun _ => .invalid) gEP (.excl ⟨true⟩) (· = .excl ⟨false⟩)
    (fun y1 y2 => by rcases y1 with ⟨⟨_ | _⟩⟩ | _ <;> rcases y2 with ⟨⟨_ | _⟩⟩ | _ <;> rfl)
    (fun n y => by
      rcases y with ⟨⟨_ | _⟩⟩ | _
      · exact ⟨fun _ => trivial, fun _ e => nomatch e⟩
      · exact ⟨fun _ => trivial, fun _ e => nomatch e⟩
      · exact ⟨fun h => (h rfl).elim, fun h => h.elim⟩)
    (fun n mz v => ⟨.excl ⟨false⟩, rfl, by cases mz with | none => exact trivial | some z => cases z <;> exact v.elim⟩)
    0 (some PZ.Z) (fun e => nomatch e)
  subst e2; subst e1; exact v rfl
-- `Iris.UpdateP.iso'` (hypothesis 9): necessary, as for iso hypothesis 10 (PZ, swap T/F, y = F updating to Z)
theorem w32_v7 : ¬ drop0% Iris.UpdateP.iso' 9 := fun h => by
  obtain ⟨_, ⟨y', e1, e2⟩, v⟩ := @h PZ PZ _ _ swTF swTF PZ.F (· = PZ.Z)
    (fun x => by cases x <;> rfl)
    (fun n y => by cases y <;> first | exact Iff.rfl | exact ⟨fun _ e => (nomatch e), fun _ e => (nomatch e)⟩)
    (fun n mz v => ⟨PZ.Z, rfl, by cases mz with | none => exact (fun e => nomatch e) | some z => cases z <;> exact (v rfl).elim⟩)
    0 (some PZ.Z) (fun e => nomatch e)
  subst e2; subst e1; exact v rfl
-- `Iris.UpdateP.iso'` (hypothesis 10): necessary, alpha = Unit, beta = Excl Unit, y = invalid, P = False
theorem w32_v8 : ¬ drop0% Iris.UpdateP.iso' 10 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h Unit EU _ _ (fun _ => xi) (fun _ => ()) xi (fun _ => False)
    (fun _ => rfl) (fun _ _ => rfl) (xi_updP _) 0 none trivial
  exact hp
-- `Iris.UpdateP.iso'` (hypothesis 11): necessary, alpha = beta = Unit, f = g = id, P = False
theorem w32_v9 : ¬ drop0% Iris.UpdateP.iso' 11 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h Unit Unit _ _ id id () (fun _ => False)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => Iff.rfl) 0 none trivial
  exact hp
-- `Iris.Update.lift_updateP` (hypothesis 7): necessary, alpha = beta = Excl Unit, g swaps excl () and invalid, x = invalid, y = excl ()
theorem w32_v10 : ¬ drop0% Iris.Update.lift_updateP 7 := fun h =>
  xe_not_upd (@h EU EU _ _ (fun e => match e with | .excl _ => xi | .invalid => xe) xi xe
    (fun n mz v => by cases mz <;> exact v.elim))
-- `Iris.Update.lift_updateP` (hypothesis 8): necessary, g = id on Excl Unit, x = excl (), y = invalid
theorem w32_v11 : ¬ drop0% Iris.Update.lift_updateP 8 := fun h =>
  xe_not_upd (@h EU EU _ _ id xe xi (fun _ hp => UpdateP.weaken hp (fun y py => ⟨y, rfl, py⟩)))
-- `Iris.UpdateP.prod` (hypothesis 8): necessary, Unit × Unit, P = R = False, Q = True
theorem w32_v12 : ¬ drop0% Iris.UpdateP.prod 8 := fun h => by
  obtain ⟨_, hr, _⟩ := @h Unit Unit _ _ (fun _ => False) (fun _ => True) (fun _ => False) ((), ())
    (UpdateP.id trivial) (fun _ _ hp _ => hp) 0 none ⟨trivial, trivial⟩
  exact hr
-- `Iris.UpdateP.prod` (hypothesis 9): necessary, Unit × Unit, P = True, Q = R = False
theorem w32_v13 : ¬ drop0% Iris.UpdateP.prod 9 := fun h => by
  obtain ⟨_, hr, _⟩ := @h Unit Unit _ _ (fun _ => True) (fun _ => False) (fun _ => False) ((), ())
    (UpdateP.id trivial) (fun _ _ _ hq => hq) 0 none ⟨trivial, trivial⟩
  exact hr
-- `Iris.UpdateP.prod` (hypothesis 10): necessary, Unit × Unit, P = Q = True, R = False
theorem w32_v14 : ¬ drop0% Iris.UpdateP.prod 10 := fun h => by
  obtain ⟨_, hr, _⟩ := @h Unit Unit _ _ (fun _ => True) (fun _ => True) (fun _ => False) ((), ())
    (UpdateP.id trivial) (UpdateP.id trivial) 0 none ⟨trivial, trivial⟩
  exact hr
-- `Iris.UpdateP.prod'` (hypothesis 7): necessary, Unit × Unit, P = False, Q = True
theorem w32_v15 : ¬ drop0% Iris.UpdateP.prod' 7 := fun h => by
  obtain ⟨_, ⟨hp, _⟩, _⟩ := @h Unit Unit _ _ (fun _ => False) (fun _ => True) ((), ())
    (UpdateP.id trivial) 0 none ⟨trivial, trivial⟩
  exact hp
-- `Iris.UpdateP.prod'` (hypothesis 8): necessary, Unit × Unit, P = True, Q = False
theorem w32_v16 : ¬ drop0% Iris.UpdateP.prod' 8 := fun h => by
  obtain ⟨_, ⟨_, hq⟩, _⟩ := @h Unit Unit _ _ (fun _ => True) (fun _ => False) ((), ())
    (UpdateP.id trivial) 0 none ⟨trivial, trivial⟩
  exact hq
-- `Iris.Update.prod` (hypothesis 6): necessary, Excl Unit × Unit, x = (excl (), ()), y = (invalid, ())
theorem w32_v17 : ¬ drop0% Iris.Update.prod 6 := fun h =>
  ((@h EU Unit _ _ (xi, ()) (xe, ()) Update.id) 0 none ⟨trivial, trivial⟩).1
-- `Iris.Update.prod` (hypothesis 7): necessary, Unit × Excl Unit, x = ((), excl ()), y = ((), invalid)
theorem w32_v18 : ¬ drop0% Iris.Update.prod 7 := fun h =>
  ((@h Unit EU _ _ ((), xi) ((), xe) Update.id) 0 none ⟨trivial, trivial⟩).2
-- `Iris.UpdateP.option` (hypothesis 5): necessary, Unit, P = Q = False
theorem w32_v19 : ¬ drop0% Iris.UpdateP.option 5 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit _ (fun _ => False) (fun _ => False) () (fun _ h => h) 0 none trivial
  exact hq
-- `Iris.UpdateP.option` (hypothesis 6): necessary, Unit, P = True, Q = False
theorem w32_v20 : ¬ drop0% Iris.UpdateP.option 6 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit _ (fun _ => True) (fun _ => False) () (UpdateP.id trivial) 0 none trivial
  exact hq
-- `Iris.UpdateP.option'` (hypothesis 4): necessary, Unit, P = False: no target satisfies Option.rec False P
theorem w32_v21 : ¬ drop0% Iris.UpdateP.option' 4 := fun h => by
  obtain ⟨y, hy, _⟩ := @h Unit _ (fun _ => False) () 0 none trivial
  cases y <;> exact hy

-- `Iris.UFrac.le_of_ord` (hypothesis 2): necessary, x = 2, y = 1
theorem w32_f1 : ¬ drop0% Iris.UFrac.le_of_ord 2 := fun h => by
  have := @h ⟨1 + 1⟩ ⟨1⟩
  change (1 : Rat) + 1 ≤ 1 at this
  grind
-- `Iris.UFrac.le_of_inc` (hypothesis 2): necessary, x = 2, y = 1
theorem w32_f2 : ¬ drop0% Iris.UFrac.le_of_inc 2 := fun h => by
  have := @h ⟨1 + 1⟩ ⟨1⟩
  change (1 : Rat) + 1 ≤ 1 at this
  grind
-- `Iris.ValidAt.ext` (hypothesis 5): necessary, M = Option (Excl Unit), n = 0, none vs some (excl ())
theorem w32_p1 : ¬ drop0% Iris.ValidAt.ext 5 := fun h => by
  have := congrArg ValidAt.val (@h OEU inferInstance 0 ⟨none, trivial⟩ ⟨some xe, trivial⟩)
  cases this
-- `Iris.ValidAt.le_val` (hypothesis 4): necessary (dependent), M = Unit, n = 0, m = 1
theorem w32_p2 : ¬ indep0% Iris.ValidAt.le_val 4 := fun h =>
  absurd (@h Unit _ 0 1 ⟨(), trivial⟩) (by decide)
-- `Iris.UPred.ext` (hypothesis 4): necessary, UPred Unit: constant True vs constant False
theorem w32_p3 : ¬ drop0% Iris.UPred.ext 4 := fun h => by
  have := congrArg (fun P : UPred Unit => P.holds 0 ⟨(), trivial⟩) (@h Unit inferInstance (uT Unit) (uF Unit))
  exact cast this trivial
-- `Iris.UPred.mono` (hypothesis 8): necessary, UPred over Option (Excl Unit) holding off none; some (excl ()) to none
theorem w32_p4 : ¬ drop0% Iris.UPred.mono 8 := fun h =>
  (@h OEU _ uS 0 0 ⟨some xe, trivial⟩ ⟨none, trivial⟩ (fun e => nomatch e) (Nat.le_refl 0)) rfl
-- `Iris.UPred.mono` (hypothesis 9): necessary, UPred Unit true only at step 0, n1 = 0, n2 = 1
theorem w32_p5 : ¬ drop0% Iris.UPred.mono 9 := fun h =>
  Nat.one_ne_zero (@h Unit _ (u0 Unit) 0 1 ⟨(), trivial⟩ ⟨(), trivial⟩ rfl .rfl)
-- `Iris.UPred.mono_unpacked` (hypothesis 7): necessary (dependent), M = Option VS, x1 = x2 = some 0 (valid only at step 0), n1 = 1, n2 = 0
theorem w32_p6 : ¬ indep0% Iris.UPred.mono_unpacked 7 := fun h =>
  vs_not1 (@h (Option VS) _ (uT _) 1 0 (some ⟨0⟩) (some ⟨0⟩) vs_v0 .rfl (Nat.zero_le 1))
-- `Iris.UPred.mono_unpacked` (hypothesis 8): necessary (dependent), M = Option (Excl Unit), x1 = some (excl ()) included in x2 = some invalid
theorem w32_p7 : ¬ indep0% Iris.UPred.mono_unpacked 8 := fun h =>
  xi_bad 0 (@h OEU _ (uT _) 0 0 (some xe) (some xi) trivial trivial (.inr ⟨xe, Dist.rfl⟩) (Nat.le_refl 0))
-- `Iris.UPred.mono_unpacked` (hypothesis 10): necessary, UPred holding off none, some (excl ()) to none
theorem w32_p8 : ¬ drop0% Iris.UPred.mono_unpacked 10 := fun h =>
  (@h OEU _ uS 0 0 (some xe) none trivial trivial (fun e => nomatch e) (Nat.le_refl 0)) rfl
-- `Iris.UPred.mono_unpacked` (hypothesis 11): necessary, UPred Unit true only at step 0, n1 = 0, n2 = 1
theorem w32_p9 : ¬ drop0% Iris.UPred.mono_unpacked 11 := fun h =>
  Nat.one_ne_zero (@h Unit _ (u0 Unit) 0 1 () () trivial trivial rfl .rfl)
-- `Iris.uPred_ne` (hypothesis 6): necessary, UPred holding off none, some (excl ()) vs none at step 0
theorem w32_p10 : ¬ drop0% Iris.uPred_ne 6 := fun h =>
  ((@h OEU _ uS 0 ⟨some xe, trivial⟩ ⟨none, trivial⟩).mp (fun e => nomatch e)) rfl
-- `Iris.uPred_holds_ne` (hypothesis 7): necessary, P = False, Q = True over Unit
theorem w32_p11 : ¬ drop0% Iris.uPred_holds_ne 7 := fun h =>
  @h Unit _ (uF Unit) (uT Unit) 0 0 () (Nat.le_refl 0) trivial trivial trivial
-- `Iris.uPred_holds_ne` (hypothesis 8): necessary, P = Q = true only at step 0, n1 = 0, n2 = 1
theorem w32_p12 : ¬ drop0% Iris.uPred_holds_ne 8 := fun h =>
  Nat.one_ne_zero (@h Unit _ (u0 Unit) (u0 Unit) 0 1 () Dist.rfl trivial trivial rfl)
-- `Iris.uPred_holds_ne` (hypothesis 9): removable (dependent), validity at n2 follows from validity at n1 since n2 ≤ n1
theorem w32_p13 : indep% Iris.uPred_holds_ne 9 := by
  intro M _ P Q n₁ n₂ x _ hn hx _
  exact ORA.validN_of_le hn hx
-- `Iris.uPred_holds_ne` (hypothesis 10): necessary (dependent), M = Option VS, x = some 0 (valid only at step 0), n2 = 0, n1 = 1
theorem w32_p14 : ¬ indep0% Iris.uPred_holds_ne 10 := fun h =>
  vs_not1 (@h (Option VS) _ (uT _) (uT _) 1 0 (some ⟨0⟩) Dist.rfl (Nat.zero_le 1) vs_v0)
-- `Iris.uPred_holds_ne` (hypothesis 11): necessary, P = Q = False over Unit
theorem w32_p15 : ¬ drop0% Iris.uPred_holds_ne 11 := fun h =>
  @h Unit _ (uF Unit) (uF Unit) 0 0 () Dist.rfl (Nat.le_refl 0) trivial trivial

-- `Iris.ReservationMap.ext` (hypothesis 4): necessary, A = Unit, H = Pos → Option, data none vs some, tokens equal
theorem w32_r1 : ¬ drop0% Iris.ReservationMap.ext 4 := fun h => by
  have := congrArg (fun z => z.data 1) (@h Unit HF ⟨fun _ => none, ∅⟩ ⟨fun _ => some (), ∅⟩ rfl)
  cases this
-- `Iris.ReservationMap.ext` (hypothesis 5): necessary, equal data, tokens valid empty vs error
theorem w32_r2 : ¬ drop0% Iris.ReservationMap.ext 5 := fun h => by
  have := congrArg (fun z => z.token) (@h Unit HF ⟨fun _ => none, ∅⟩ ⟨fun _ => none, .error⟩ rfl)
  cases this
-- `Iris.instDiscreteReservationMap` (hypothesis 4): necessary, A = TN (not discrete): data 1 and 2 everywhere agree at 0
theorem w32_r3 : ¬ drop0% Iris.instDiscreteReservationMap 4 := fun h => by
  have := congrArg (fun z => z.data 1) ((@h HF TN _ _).discrete_0
    (x := ⟨fun _ => some ⟨1⟩, ∅⟩) (y := ⟨fun _ => some ⟨2⟩, ∅⟩) ⟨fun _ => tn12, rfl⟩)
  simp at this
-- `Iris.instDiscreteEReservationMapMk` (hypothesis 6): necessary, A = TN, a = constant 1 (not discrete)
theorem w32_r4 : ¬ drop0% Iris.instDiscreteEReservationMapMk 6 := fun h => by
  have := congrArg (fun z => z.data 1) ((@h HF TN _ _ ∅ (fun _ => some ⟨1⟩)).discrete
    (y := ⟨fun _ => some ⟨2⟩, ∅⟩) ⟨fun _ => tn12, rfl⟩)
  simp at this
-- `Iris.instDiscreteEReservationMapSingleton` (hypothesis 6): necessary, A = TN, a = 1 (not discrete), singleton 1 1 vs singleton 1 2
theorem w32_r5 : ¬ drop0% Iris.instDiscreteEReservationMapSingleton 6 := fun h => by
  have := congrArg (fun z => z.data 1) ((@h HF TN _ _ 1 ⟨1⟩).discrete
    (y := ReservationMap.singleton 1 ⟨2⟩) (instNonExpansiveReservationMapSingleton.ne tn12))
  simp [ReservationMap.singleton, ReservationMap.mkData, PartialMap.singleton, PartialMap.insert] at this
-- `Iris.ReservationMap.validN_data_of_validN` (hypothesis 6): necessary, A = Excl Unit, data invalid everywhere
theorem w32_r6 : ¬ drop0% Iris.ReservationMap.validN_data_of_validN 6 := fun h =>
  (@h HF EU _ _ 0 ⟨fun _ => some xi, ∅⟩) 1
-- `Iris.ReservationMap.validN_token_of_validN` (hypothesis 6): necessary, token error
theorem w32_r7 : ¬ drop0% Iris.ReservationMap.validN_token_of_validN 6 := fun h =>
  DisjointLeibnizSet.not_validN_invalid (@h HF EU _ _ 0 ⟨fun _ => none, .error⟩)
-- `Iris.ReservationMap.validN_disj` (hypothesis 6): necessary, data everywhere some, token valid top
theorem w32_r8 : ¬ drop0% Iris.ReservationMap.validN_disj 6 := fun h =>
  (@h HF EU _ _ 0 ⟨fun _ => some xe, .valid ⊤⟩ 1).elim (fun e => nomatch e) (fun hn => hn CoPset.mem_full)
-- `Iris.ReservationMap.valid_data_of_valid` (hypothesis 5): necessary, data invalid everywhere
theorem w32_r9 : ¬ drop0% Iris.ReservationMap.valid_data_of_valid 5 := fun h =>
  (@h HF EU _ _ ⟨fun _ => some xi, ∅⟩) 1
-- `Iris.ReservationMap.valid_disj` (hypothesis 5): necessary, data everywhere some, token valid top
theorem w32_r10 : ¬ drop0% Iris.ReservationMap.valid_disj 5 := fun h =>
  (@h HF EU _ _ ⟨fun _ => some xe, .valid ⊤⟩ 1).elim (fun e => nomatch e) (fun hn => hn CoPset.mem_full)
-- `Iris.ReservationMap.validN_mono` (hypothesis 7): necessary, x data invalid everywhere, y data valid everywhere, tokens empty
theorem w32_r11 : ¬ drop0% Iris.ReservationMap.validN_mono 7 := fun h =>
  (ReservationMap.validN_data_of_validN (@h HF EU _ _ 0 ⟨fun _ => some xi, ∅⟩ ⟨fun _ => some xe, ∅⟩
    (fun _ e => nomatch e) ⟨∅, (dls_op_empty _).symm⟩
    (ReservationMap.validN_iff.mpr ⟨fun _ => trivial, DisjointLeibnizSet.validN_set, fun i => .inr (DisjointLeibnizSet.mem_empty i)⟩))) 1
-- `Iris.ReservationMap.validN_mono` (hypothesis 9): necessary, x = (empty, token error), y = (empty, token empty)
theorem w32_r12 : ¬ drop0% Iris.ReservationMap.validN_mono 9 := fun h =>
  DisjointLeibnizSet.not_validN_invalid (ReservationMap.validN_token_of_validN
    (@h HF EU _ _ 0 ⟨fun _ => none, .error⟩ ⟨fun _ => none, ∅⟩ (fun _ _ => trivial) (fun _ e => e)
      (ReservationMap.validN_iff.mpr ⟨fun _ => trivial, DisjointLeibnizSet.validN_set, fun i => .inl rfl⟩)))
-- `Iris.ReservationMap.validN_mono` (hypothesis 10): necessary, x = y with token error
theorem w32_r13 : ¬ drop0% Iris.ReservationMap.validN_mono 10 := fun h =>
  DisjointLeibnizSet.not_validN_invalid (ReservationMap.validN_token_of_validN
    (@h HF EU _ _ 0 ⟨fun _ => none, .error⟩ ⟨fun _ => none, .error⟩ (fun _ _ => trivial) (fun _ e => e) ⟨.error, rfl⟩))
-- `Iris.ReservationMap.increasing_data` (hypothesis 5): necessary, A = BA, data false everywhere is not increasing
theorem w32_r14 : ¬ drop0% Iris.ReservationMap.increasing_data 5 := fun h =>
  opt_ba_tf ((@h HF BA _ _ ⟨fun _ => some ⟨false⟩, ∅⟩).increasing (fun _ => some ⟨true⟩) 1)
-- `Iris.ReservationMap.increasing_token` (hypothesis 5): removable, the token CMRA (DisjointLeibnizSet) orders by inclusion, so every token is increasing
theorem w32_r15 : drop% Iris.ReservationMap.increasing_token 5 := by
  intro H A _ _ v
  exact ⟨fun y => IncOrd.inc_ord ⟨v.token, ORA.comm'⟩⟩
-- `Iris.ReservationMap.increasing_mk` (hypothesis 5): necessary, A = BA, data false everywhere: v increasing would make data increasing
theorem w32_r16 : ¬ drop0% Iris.ReservationMap.increasing_mk 5 := fun h =>
  opt_ba_tf ((ReservationMap.increasing_data (@h HF BA _ _ ⟨fun _ => some ⟨false⟩, ∅⟩
    ⟨fun y => IncOrd.inc_ord ⟨_, ORA.comm'⟩⟩)).increasing (fun _ => some ⟨true⟩) 1)
-- `Iris.ReservationMap.increasing_mk` (hypothesis 6): removable, every DisjointLeibnizSet token is increasing (inclusion order)
theorem w32_r17 : drop% Iris.ReservationMap.increasing_mk 6 := by
  intro H A _ _ v hd
  exact ReservationMap.increasing_mk hd ⟨fun y => IncOrd.inc_ord ⟨v.token, ORA.comm'⟩⟩
-- `Iris.ReservationMap.instIncOrd` (hypothesis 4): necessary, A = BA: singleton 1 true is included in singleton 1 false, not ordered
theorem w32_r18 : ¬ drop0% Iris.ReservationMap.instIncOrd 4 := fun h =>
  rm_ba_not_ord ((@h HF BA _ _).inc_ord rm_ba_inc)
-- `Iris.ReservationMap.instOrdInc` (hypothesis 4): necessary, A = MO (order True, op max): singleton 1 1 ordered below singleton 1 0, not included
theorem w32_r19 : ¬ drop0% Iris.ReservationMap.instOrdInc 4 := fun h => by
  have := (ReservationMap.inc_iff.mp ((@h HF MO _ _).ord_inc
    (ReservationMap.singleton_mono_ord (H := HF) (k := 1) (a := (⟨1⟩ : MO)) (b := ⟨0⟩) trivial))).1
  obtain ⟨z, hz⟩ := this
  have h1 : get? _ (1 : Pos) = get? _ (1 : Pos) := congrArg (get? · (1 : Pos)) hz
  rw [Heap.get?_op] at h1
  change some (⟨0⟩ : MO) = ORA.op (some (⟨1⟩ : MO)) (get? z (1 : Pos)) at h1
  cases hz1 : get? z (1 : Pos) with
  | none => rw [hz1] at h1; change some (⟨0⟩ : MO) = some ⟨1⟩ at h1; simp at h1
  | some w =>
    rw [hz1] at h1
    have := congrArg MO.v (Option.some.inj h1); change 0 = max 1 w.v at this; omega
-- `Iris.ReservationMap.instIsInc` (hypothesis 4): necessary, A = BA (not IncOrd)
theorem w32_r20 : ¬ drop0% Iris.ReservationMap.instIsInc 4 := fun h =>
  rm_ba_not_ord ((@h HF BA _ _).inc_ord rm_ba_inc)
-- `Iris.ReservationMap.instDiscrete` (hypothesis 4): necessary, A = VS (n-valid iff n ≤ v, never valid): singleton 1 0 is 0-valid, not valid
theorem w32_r21 : ¬ drop0% Iris.ReservationMap.instDiscrete 4 := fun h =>
  vs_not_valid _ ((ReservationMap.valid_singleton (H := HF) 1 (⟨0⟩ : VS)).mp
    ((@h HF VS _ _).discrete_valid ((ReservationMap.validN_singleton (H := HF) (n := 0) 1 (⟨0⟩ : VS)).mpr vs_v0)))
-- `Iris.ReservationMap.instCoreIdSingleton` (hypothesis 6): necessary, A = Excl Unit (no core): core of singleton 1 (excl ()) has empty data
theorem w32_r22 : ¬ drop0% Iris.ReservationMap.instCoreIdSingleton 6 := fun h => by
  have := congrArg (fun z => z.map (fun w => get? w.data (1 : Pos))) (@h HF EU _ _ 1 xe).core_id
  change (some none : Option (Option EU)) = some (some xe) at this
  cases this
-- `Iris.ReservationMap.split_valid` (hypothesis 5): necessary, token error is no composite of data and token
theorem w32_r23 : ¬ drop0% Iris.ReservationMap.split_valid 5 := fun h => by
  obtain ⟨d, t, e⟩ := @h HF EU _ _ ⟨fun _ => none, .error⟩
  have := congrArg ReservationMap.token e
  change (DisjointLeibnizSet.error : CoPsetDisjL) = (∅ : CoPsetDisjL) • (DisjointLeibnizSet.valid t : CoPsetDisjL) at this
  rw [dls_empty_op] at this
  cases this
-- `Iris.ReservationMap.split_validN` (hypothesis 6): necessary, token error is no composite of data and token
theorem w32_r24 : ¬ drop0% Iris.ReservationMap.split_validN 6 := fun h => by
  obtain ⟨d, t, e⟩ := @h HF EU _ _ 0 ⟨fun _ => none, .error⟩
  have := congrArg ReservationMap.token e
  change (DisjointLeibnizSet.error : CoPsetDisjL) = (∅ : CoPsetDisjL) • (DisjointLeibnizSet.valid t : CoPsetDisjL) at this
  rw [dls_empty_op] at this
  cases this
-- `Iris.ReservationMap.token_op` (hypothesis 6): necessary, a = b = top: union valid, op invalid
theorem w32_r25 : ¬ drop0% Iris.ReservationMap.token_op 6 := fun h => by
  have e := congrArg ReservationMap.token (@h HF EU _ _ ⊤ ⊤)
  rw [ReservationMap.op_token] at e
  have v : ✓ ((ReservationMap.mkToken (H := HF) (A := EU) ⊤).token • (ReservationMap.mkToken (H := HF) (A := EU) ⊤).token) := by
    rw [← e]; exact DisjointLeibnizSet.valid_set
  exact DisjointLeibnizSet.valid_op_iff_disj.mp v 1 ⟨CoPset.mem_full, CoPset.mem_full⟩
-- `Iris.ReservationMap.disj_of_validN_data_op_token` (hypothesis 7): necessary, a everywhere some, b = top, i = 1
theorem w32_r26 : ¬ drop0% Iris.ReservationMap.disj_of_validN_data_op_token 7 := fun h =>
  (@h HF EU _ _ 0 (fun _ => some xe) ⊤ 1).elim (fun e => nomatch e) (fun hn => hn CoPset.mem_full)
-- `Iris.ReservationMap.disj_of_valid_data_op_token` (hypothesis 6): necessary, a everywhere some, b = top, i = 1
theorem w32_r27 : ¬ drop0% Iris.ReservationMap.disj_of_valid_data_op_token 6 := fun h =>
  (@h HF EU _ _ (fun _ => some xe) ⊤ 1).elim (fun e => nomatch e) (fun hn => hn CoPset.mem_full)
-- `Iris.ReservationMap.validN_data_op_token` (hypothesis 7): necessary, a invalid everywhere, b = empty
theorem w32_r28 : ¬ drop0% Iris.ReservationMap.validN_data_op_token 7 := fun h =>
  (ReservationMap.validN_data_of_validN (ORA.validN_op_left (@h HF EU _ _ 0 (fun _ => some xi) ∅
    (fun i => .inr (LawfulSet.mem_empty))))) (1 : Pos)
-- `Iris.ReservationMap.validN_data_op_token` (hypothesis 8): necessary, a everywhere some, b = {1}
theorem w32_r29 : ¬ drop0% Iris.ReservationMap.validN_data_op_token 8 := fun h =>
  (ReservationMap.disj_of_validN_data_op_token (@h HF EU _ _ 0 (fun _ => some xe) {1}
    (ReservationMap.validN_data.mpr (fun _ => trivial))) 1).elim (fun e => nomatch e) (fun hn => hn mem_one)
-- `Iris.ReservationMap.valid_data_op_token` (hypothesis 6): necessary, a invalid everywhere, b = empty
theorem w32_r30 : ¬ drop0% Iris.ReservationMap.valid_data_op_token 6 := fun h =>
  (ReservationMap.validN_data_of_validN (ORA.validN_op_left ((@h HF EU _ _ (fun _ => some xi) ∅
    (fun i => .inr (LawfulSet.mem_empty))).validN (n := 0)))) (1 : Pos)
-- `Iris.ReservationMap.valid_data_op_token` (hypothesis 7): necessary, a everywhere some, b = {1}
theorem w32_r31 : ¬ drop0% Iris.ReservationMap.valid_data_op_token 7 := fun h =>
  (ReservationMap.disj_of_valid_data_op_token _ _ (@h HF EU _ _ (fun _ => some xe) {1}
    (ReservationMap.valid_data.mpr (fun _ => trivial))) 1).elim (fun e => nomatch e) (fun hn => hn mem_one)
-- `Iris.ReservationMap.singleton_mono_ord` (hypothesis 7): necessary, A = BA (order equality): true, false
theorem w32_r32 : ¬ drop0% Iris.ReservationMap.singleton_mono_ord 7 := fun h =>
  rm_ba_not_ord (@h HF BA _ _ 1 ⟨true⟩ ⟨false⟩)
-- `Iris.ReservationMap.singleton_mono` (hypothesis 7): necessary, A = Excl Unit: invalid is not included in excl ()
theorem w32_r33 : ¬ drop0% Iris.ReservationMap.singleton_mono 7 := fun h => by
  obtain ⟨z, hz⟩ := (ReservationMap.inc_iff.mp (@h HF EU _ _ 1 xi xe)).1
  have h1 : get? _ (1 : Pos) = get? _ (1 : Pos) := congrArg (get? · (1 : Pos)) hz
  rw [Heap.get?_op] at h1
  change some xe = ORA.op (some xi) (get? z (1 : Pos)) at h1
  cases hz1 : get? z (1 : Pos) with
  | none => rw [hz1] at h1; change some xe = some xi at h1; cases h1
  | some w => rw [hz1] at h1; change some xe = some xi at h1; cases h1
-- `Iris.ReservationMap.instIsOpSingleton` (hypothesis 9): necessary, A = Excl Unit, a = b1 = b2 = excl (): excl () • excl () is invalid
theorem w32_r34 : ¬ drop0% Iris.ReservationMap.instIsOpSingleton 9 := fun h => by
  have e := (@h HF EU _ _ 1 .merge xe xe xe).is_op
  rw [← ReservationMap.singleton_op] at e
  have := congrArg (fun w => get? w.data (1 : Pos)) e
  change some xe = some xi at this
  cases this
-- `Iris.ReservationMap.token_union` (hypothesis 6): necessary, e1 = e2 = top: union valid, op invalid
theorem w32_r35 : ¬ drop0% Iris.ReservationMap.token_union 6 := fun h => by
  have e := congrArg ReservationMap.token (@h HF EU _ _ ⊤ ⊤)
  rw [ReservationMap.op_token] at e
  have v : ✓ ((ReservationMap.mkToken (H := HF) (A := EU) ⊤).token • (ReservationMap.mkToken (H := HF) (A := EU) ⊤).token) := by
    rw [← e]; exact DisjointLeibnizSet.valid_set
  exact DisjointLeibnizSet.valid_op_iff_disj.mp v 1 ⟨CoPset.mem_full, CoPset.mem_full⟩
-- `Iris.ReservationMap.token_difference` (hypothesis 6): necessary, e1 = top, e2 = empty: 1 is in the op, not in empty
theorem w32_r36 : ¬ drop0% Iris.ReservationMap.token_difference 6 := fun h => by
  have e := congrArg ReservationMap.token (@h HF EU _ _ ⊤ ∅)
  rw [ReservationMap.op_token] at e
  have v : ✓{0} ((ReservationMap.mkToken (H := HF) (A := EU) ⊤).token • (ReservationMap.mkToken (H := HF) (A := EU) ((∅ : CoPset) \ ⊤)).token) :=
    e ▸ DisjointLeibnizSet.validN_set
  have m := (DisjointLeibnizSet.mem_iff_of_validN_union v (1 : Pos)).mpr (.inl CoPset.mem_full)
  rw [← e] at m
  exact LawfulSet.mem_empty (show (1 : Pos) ∈ (∅ : CoPset) from m)
-- `Iris.ReservationMap.valid_op?_of_valid_singleton_op` (hypothesis 8): necessary, a invalid, x empty
theorem w32_r37 : ¬ drop0% Iris.ReservationMap.valid_op?_of_valid_singleton_op 8 := fun h =>
  (@h HF EU _ _ 0 1 xi (fun _ => none) : ✓{0} xi)
-- `Iris.ReservationMap.valid_singleton_op_of_valid_op?` (hypothesis 8): necessary, a = excl (), x invalid at 2 only
theorem w32_r38 : ¬ drop0% Iris.ReservationMap.valid_singleton_op_of_valid_op? 8 := fun h =>
  (ReservationMap.validN_data_of_validN (ORA.validN_op_right
    (@h HF EU _ _ 0 1 xe (fun i => if i = 1 then none else some xi) trivial))) (2 : Pos)
-- `Iris.ReservationMap.valid_singleton_op_of_valid_op?` (hypothesis 9): necessary, a invalid, x empty
theorem w32_r39 : ¬ drop0% Iris.ReservationMap.valid_singleton_op_of_valid_op? 9 := fun h =>
  (ReservationMap.valid_op?_of_valid_singleton_op (@h HF EU _ _ 0 1 xi (fun _ => none) (fun _ => trivial)) : ✓{0} xi)
-- `Iris.ReservationMap.alloc` (hypothesis 7): necessary, e = empty, a = excl (): frame singleton 1 (excl ()) is compatible with mkToken empty only
theorem w32_r40 : ¬ drop0% Iris.ReservationMap.alloc 7 := fun h => by
  have := @h HF EU _ _ ∅ 1 xe trivial 0 (some (ReservationMap.singleton 1 xe))
    (by
      change ✓{0} (UORA.unit • ReservationMap.singleton (H := HF) 1 xe)
      rw [UORA.unit_left_id]; exact (ReservationMap.validN_singleton 1 xe).mpr trivial)
  change ✓{0} (ReservationMap.singleton (H := HF) 1 xe • ReservationMap.singleton 1 xe) at this
  rw [← ReservationMap.singleton_op] at this
  exact xi_bad 0 ((ReservationMap.validN_singleton 1 _).mp this)
-- `Iris.ReservationMap.alloc` (hypothesis 8): necessary, e = {1}, k = 1, a invalid, no frame
theorem w32_r41 : ¬ drop0% Iris.ReservationMap.alloc 8 := fun h =>
  xi_bad 0 ((ReservationMap.validN_singleton 1 xi).mp
    (@h HF EU _ _ {1} 1 xi mem_one 0 none (ReservationMap.valid_token (H := HF) (A := EU)).validN))
-- `Iris.ReservationMap.updateP` (hypothesis 8): necessary, P = Q = False, a = excl () (valid)
theorem w32_r42 : ¬ drop0% Iris.ReservationMap.updateP 8 := fun h => by
  obtain ⟨_, hq, _⟩ := @h HF EU _ _ (fun _ => False) (fun _ => False) 1 xe (fun _ hp => hp) 0 none
    ((ReservationMap.validN_singleton 1 xe).mpr trivial)
  exact hq
-- `Iris.ReservationMap.updateP` (hypothesis 9): necessary, P = True, Q = False, a = excl ()
theorem w32_r43 : ¬ drop0% Iris.ReservationMap.updateP 9 := fun h => by
  obtain ⟨_, hq, _⟩ := @h HF EU _ _ (fun _ => True) (fun _ => False) 1 xe (UpdateP.id trivial) 0 none
    ((ReservationMap.validN_singleton 1 xe).mpr trivial)
  exact hq
-- `Iris.ReservationMap.reservation_map_update` (hypothesis 7): necessary, a = excl (), b invalid, no frame
theorem w32_r44 : ¬ drop0% Iris.ReservationMap.reservation_map_update 7 := fun h =>
  xi_bad 0 ((ReservationMap.validN_singleton 1 xi).mp
    (@h HF EU _ _ 1 xe xi 0 none ((ReservationMap.validN_singleton 1 xe).mpr trivial)))

-- `Iris.SIdx.lt_trans` (hypothesis 5): necessary, I = O2 (omega^2), n = p = (0,1), m = (0,0)
theorem w32_s1 : ¬ drop0% Iris.SIdx.lt_trans 5 := fun h =>
  absurd (o2_lt.mp (@h O2 _ ⟨0,1⟩ ⟨0,0⟩ ⟨0,1⟩ (o2_lt.mpr (by decide)))) (by decide)
-- `Iris.SIdx.lt_trans` (hypothesis 6): necessary, I = O2, n = p = (0,0), m = (0,1)
theorem w32_s2 : ¬ drop0% Iris.SIdx.lt_trans 6 := fun h =>
  absurd (o2_lt.mp (@h O2 _ ⟨0,0⟩ ⟨0,1⟩ ⟨0,0⟩ (o2_lt.mpr (by decide)))) (by decide)
-- `Iris.SIdx.succ_le_of_lt` (hypothesis 4): necessary, I = O2, n = m = 0: succ 0 is not ≤ 0
theorem w32_s3 : ¬ drop0% Iris.SIdx.succ_le_of_lt 4 := fun h =>
  (o2_le.mp (@h O2 _ ⟨0,0⟩ ⟨0,0⟩)).elim (fun hl => absurd (o2_lt.mp hl) (by decide))
    (fun e => absurd (congrArg O2.b e) (by decide))
-- `Iris.SIdxFinite.finite_index` (hypothesis 2): necessary, I = O2 (omega^2): (1,0) is neither 0 nor a successor
theorem w32_s4 : ¬ drop0% Iris.SIdxFinite.finite_index 2 := fun h =>
  (@h O2 inferInstance ⟨1,0⟩).elim (fun e => absurd (congrArg O2.a e) (by decide))
    (fun ⟨m, e⟩ => Nat.succ_ne_zero _ (congrArg O2.b e).symm)
-- `Iris.SIdx.lt_succ_diag_r'` (hypothesis 4): necessary, I = O2, m = n = 0
theorem w32_s5 : ¬ drop0% Iris.SIdx.lt_succ_diag_r' 4 := fun h =>
  absurd (o2_lt.mp (@h O2 _ ⟨0,0⟩ ⟨0,0⟩)) (by decide)
-- `Iris.SIdx.lt_asymm` (hypothesis 4): necessary, I = O2, m = (0,0) < n = (0,1)
theorem w32_s6 : ¬ drop0% Iris.SIdx.lt_asymm 4 := fun h =>
  @h O2 _ ⟨0,0⟩ ⟨0,1⟩ (o2_lt.mpr (by decide))
-- `Iris.SIdx.lt_le_incl` (hypothesis 4): necessary, I = O2, m = (0,0), n = (0,1)
theorem w32_s7 : ¬ drop0% Iris.SIdx.lt_le_incl 4 := fun h =>
  (o2_le.mp (@h O2 _ ⟨0,0⟩ ⟨0,1⟩)).elim (fun hl => absurd (o2_lt.mp hl) (by decide))
    (fun e => absurd (congrArg O2.b e) (by decide))
-- `Iris.SIdx.le_trans` (hypothesis 5): necessary, I = O2, m = p = (0,0), n = (0,1)
theorem w32_s8 : ¬ drop0% Iris.SIdx.le_trans 5 := fun h =>
  (o2_le.mp (@h O2 _ ⟨0,0⟩ ⟨0,1⟩ ⟨0,0⟩ (o2_le.mpr (.inr rfl)))).elim (fun hl => absurd (o2_lt.mp hl) (by decide))
    (fun e => absurd (congrArg O2.b e) (by decide))
-- `Iris.SIdx.le_trans` (hypothesis 6): necessary, I = O2, n = m = (0,1), p = (0,0)
theorem w32_s9 : ¬ drop0% Iris.SIdx.le_trans 6 := fun h =>
  (o2_le.mp (@h O2 _ ⟨0,1⟩ ⟨0,1⟩ ⟨0,0⟩ (o2_le.mpr (.inr rfl)))).elim (fun hl => absurd (o2_lt.mp hl) (by decide))
    (fun e => absurd (congrArg O2.b e) (by decide))
-- `Iris.SIdx.le_antisymm` (hypothesis 4): necessary, I = O2, m = (0,1), n = (0,0)
theorem w32_s10 : ¬ drop0% Iris.SIdx.le_antisymm 4 := fun h =>
  absurd (congrArg O2.b (@h O2 _ ⟨0,1⟩ ⟨0,0⟩ (o2_le.mpr (.inl (o2_lt.mpr (by decide)))))) (by decide)
-- `Iris.SIdx.le_antisymm` (hypothesis 5): necessary, I = O2, m = (0,0), n = (0,1)
theorem w32_s11 : ¬ drop0% Iris.SIdx.le_antisymm 5 := fun h =>
  absurd (congrArg O2.b (@h O2 _ ⟨0,0⟩ ⟨0,1⟩ (o2_le.mpr (.inl (o2_lt.mpr (by decide)))))) (by decide)
-- `Iris.SIdx.lt_le_trans` (hypothesis 5): necessary, I = O2, m = n = p = 0
theorem w32_s12 : ¬ drop0% Iris.SIdx.lt_le_trans 5 := fun h =>
  absurd (o2_lt.mp (@h O2 _ ⟨0,0⟩ ⟨0,0⟩ ⟨0,0⟩ (o2_le.mpr (.inr rfl)))) (by decide)
-- `Iris.SIdx.lt_le_trans` (hypothesis 6): necessary, I = O2, n = p = (0,0), m = (0,1)
theorem w32_s13 : ¬ drop0% Iris.SIdx.lt_le_trans 6 := fun h =>
  absurd (o2_lt.mp (@h O2 _ ⟨0,1⟩ ⟨0,0⟩ ⟨0,0⟩ (o2_lt.mpr (by decide)))) (by decide)
-- `Iris.SIdx.le_lt_trans` (hypothesis 5): necessary, I = O2, n = p = (0,1), m = (0,0)
theorem w32_s14 : ¬ drop0% Iris.SIdx.le_lt_trans 5 := fun h =>
  absurd (o2_lt.mp (@h O2 _ ⟨0,0⟩ ⟨0,1⟩ ⟨0,1⟩ (o2_lt.mpr (by decide)))) (by decide)
-- `Iris.SIdx.le_lt_trans` (hypothesis 6): necessary, I = O2, m = n = p = 0
theorem w32_s15 : ¬ drop0% Iris.SIdx.le_lt_trans 6 := fun h =>
  absurd (o2_lt.mp (@h O2 _ ⟨0,0⟩ ⟨0,0⟩ ⟨0,0⟩ (o2_le.mpr (.inr rfl)))) (by decide)
-- `Iris.SIdx.succ_inj` (hypothesis 4): necessary, I = O2, n = (0,0), m = (0,1)
theorem w32_s16 : ¬ drop0% Iris.SIdx.succ_inj 4 := fun h =>
  absurd (congrArg O2.b (@h O2 _ ⟨0,0⟩ ⟨0,1⟩)) (by decide)
-- `Iris.SIdx.Limit.succ_lt` (hypothesis 3): necessary, I = O2, n = (0,1) (a successor), m = 0
theorem w32_s17 : ¬ drop0% Iris.SIdx.Limit.succ_lt 3 := fun h =>
  absurd (o2_lt.mp (@h O2 ⟨0,1⟩ _ ⟨0,0⟩ (o2_lt.mpr (by decide)))) (by decide)
-- `Iris.SIdx.Limit.succ_lt` (hypothesis 5): necessary, I = O2, n = m = (1,0) (a limit)
theorem w32_s18 : ¬ drop0% Iris.SIdx.Limit.succ_lt 5 := fun h =>
  absurd (o2_lt.mp (@h O2 ⟨1,0⟩ _ o2lim ⟨1,0⟩)) (by decide)
-- `Iris.SIdx.Limit.ne_zero` (hypothesis 3): necessary, I = O2, n = 0
theorem w32_s19 : ¬ drop0% Iris.SIdx.Limit.ne_zero 3 := fun h =>
  @h O2 ⟨0,0⟩ _ rfl
-- `Iris.SIdx.Limit.limit_lt_0` (hypothesis 3): necessary, I = O2, n = 0
theorem w32_s20 : ¬ drop0% Iris.SIdx.Limit.limit_lt_0 3 := fun h =>
  absurd (o2_lt.mp (@h O2 _ ⟨0,0⟩)) (by decide)
-- `Iris.SIdx.limit_finite` (hypothesis 2): necessary, I = O2 (omega^2) has the limit (1,0)
theorem w32_s21 : ¬ drop0% Iris.SIdx.limit_finite 2 := fun h =>
  @h O2 _ ⟨1,0⟩ o2lim
-- `Iris.SIdx.rec_lim` (hypothesis 7): necessary (dependent), I = O2, P = True, n = 0 is no limit
theorem w32_s22 : ¬ indep0% Iris.SIdx.rec_lim 7 := fun h =>
  SIdx.limit_0 (@h O2 _ (fun _ => True) trivial (fun _ _ => trivial) (fun _ _ _ => trivial) 0)
