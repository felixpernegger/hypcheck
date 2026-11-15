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

namespace W2c1
open Iris Iris.OFE Iris.Std

/-- Truncation OFE on naturals (copied from Probe1): dist n x y iff min x (n+1) = min y (n+1). Not discrete (1 and 2 agree at 0). -/
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

/-- Discrete ORA on booleans (copied from Probe1): op is and, no core, order is equality. -/
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

/-- Discrete total CMRA on 2 elements (copied from W1c4): op = or, core = id, valid only at step 0. -/
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

/-- Discrete ORA on Nat (copied from W1c4): op = max, all valid, order True, core n = n except core 2 = 0. Not OrdInc. -/
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

/-- Partial maps Pos → Option V (library LawfulPartialMap instance). -/
abbrev HF := fun V : Type => Pos → Option V
abbrev EU := Excl Unit
abbrev xe : EU := .excl ()
abbrev xi : EU := .invalid

theorem not_inf_top_top : ¬ LawfulSet.setInfinite ((⊤ : CoPset) \ ⊤) := fun h => by
  obtain ⟨x, hx, -⟩ := h []
  exact (LawfulSet.mem_diff.mp hx).2 CoPset.mem_full
theorem inf_top_one : LawfulSet.setInfinite ((⊤ : CoPset) \ {(1 : Pos)}) :=
  LawfulSet.difference_infinite top_infinite LawfulSet.singleton_finite
theorem inf_top_empty : LawfulSet.setInfinite ((⊤ : CoPset) \ ∅) := by
  rw [LawfulSet.diff_empty]; exact top_infinite

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
theorem ba_not_inc : ¬ Increasing (⟨false⟩ : BA) := fun h => by
  have := h.increasing ⟨true⟩
  cases this
theorem ba_inc_tf : (⟨true⟩ : BA) ≼ ⟨false⟩ := ⟨⟨false⟩, rfl⟩
/-- In BA-valued DynReservationMaps, mkData 1 true is included in mkData 1 false but not ordered below it. -/
theorem drm_ba_inc : (DynReservationMap.mkData 1 ⟨true⟩ : DynReservationMap BA HF) ≼ DynReservationMap.mkData 1 ⟨false⟩ :=
  ⟨DynReservationMap.mkData 1 ⟨false⟩, DynReservationMap.mkData_op (H := HF) 1 (⟨true⟩ : BA) ⟨false⟩⟩
theorem drm_ba_not_ord : ¬ ((DynReservationMap.mkData 1 ⟨true⟩ : DynReservationMap BA HF) ≼ₒ DynReservationMap.mkData 1 ⟨false⟩) :=
  fun h => opt_ba_tf (h.1 1)

theorem mk_xi_bad (n : Nat) : ¬ ✓{n} (DynReservationMap.mkData (H := HF) 1 xi) :=
  fun h => (DynReservationMap.validN_mkData (H := HF) 1 xi).mp h
theorem mk_xe_ok (n : Nat) : ✓{n} (DynReservationMap.mkData (H := HF) 1 xe) :=
  (DynReservationMap.validN_mkData (H := HF) 1 xe).mpr trivial

theorem tn01 : ¬ ((⟨0⟩ : TN) ≡{0}≡ ⟨1⟩) := fun h => by
  have h' : min 0 (0+1) = min 1 (0+1) := h
  omega
instance tn0disc : DiscreteE (⟨0⟩ : TN) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩

/-- OFE on Bool in which all elements agree at step 0 (and only equal ones later). -/
structure NU where b : Bool
  deriving DecidableEq
instance nuOFE : OFE NU where
  Dist n x y := n = 0 ∨ x = y
  dist_eqv := ⟨fun _ => .inr rfl, fun h => h.elim .inl (fun e => .inr e.symm),
    fun h1 h2 => h1.elim .inl (fun e1 => h2.elim .inl (fun e2 => .inr (e1.trans e2)))⟩
  eq_dist' {x y} := ⟨fun h _ => .inr h, fun h => (h 1).resolve_left (by decide)⟩
  dist_lt {n x y m} h hm := h.elim (fun h0 => absurd hm (by omega)) .inr
/-- Unital CMRA on NU: op = and, unit true, core = identity, everything valid. The unit is not discrete. -/
@[instance_reducible] def nuData : CMRAData NU where
  op x y := ⟨x.b && y.b⟩
  op_ne := ⟨fun {n a b} h => h.elim .inl (fun e => .inr (e ▸ rfl))⟩
  assoc {x y z} := by cases x with | mk a => cases y with | mk b => cases z with | mk c => cases a <;> cases b <;> cases c <;> rfl
  comm {x y} := by cases x with | mk a => cases y with | mk b => cases a <;> cases b <;> rfl
  pcore := some
  pcore_ne {n x y cx} h e := ⟨y, rfl, by cases e; exact h⟩
  pcore_idem {x cx} e := by cases e; rfl
  ValidN _ _ := True
  Valid _ := True
  validN_ne _ _ := trivial
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ _ := trivial
  validN_op_left _ := trivial
  pcore_op_left {x cx} e := by cases e; cases x with | mk b => cases b <;> rfl
  extend {n x y₁ y₂} v h :=
    if hx : x = ⟨y₁.b && y₂.b⟩ then ⟨y₁, y₂, hx, .inr rfl, .inr rfl⟩
    else ⟨x, ⟨true⟩, by cases x with | mk b => cases b <;> rfl,
      .inl (h.resolve_right hx), .inl (h.resolve_right hx)⟩
  pcore_op_mono {x cx} e y := ⟨y, by cases e; rfl⟩
instance nuCMRA : CMRA NU := ORA.ofCMRAData nuData
@[instance_reducible] def nuUData : UCMRAData NU where
  unit := ⟨true⟩
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl
instance nuUCMRA : UCMRA NU := UORA.ofUCMRAData nuUData

/-- Bool-indexed family: Unit at true, NU at false. -/
def βB : Bool → Type
  | true => Unit
  | false => NU
instance instβB : ∀ i, UORA (βB i)
  | true => (inferInstance : UORA Unit)
  | false => (inferInstance : UORA NU)

end W2c1
open W2c1 Iris Iris.OFE Iris.Std

-- `Iris.DynReservationMap.ext` (hypothesis 4): necessary, A = Unit, H = Pos → Option, data none vs some, tokens equal
theorem w21_1 : ¬ drop0% Iris.DynReservationMap.ext 4 := fun h => by
  have := congrArg (fun z => z.data 1) (@h Unit HF ⟨fun _ => none, ∅⟩ ⟨fun _ => some (), ∅⟩ rfl)
  cases this
-- `Iris.DynReservationMap.ext` (hypothesis 5): necessary, equal data, tokens valid empty vs error
theorem w21_2 : ¬ drop0% Iris.DynReservationMap.ext 5 := fun h => by
  have := congrArg (fun z => z.token) (@h Unit HF ⟨fun _ => none, ∅⟩ ⟨fun _ => none, .error⟩ rfl)
  cases this
-- `Iris.instDiscreteDynReservationMap` (hypothesis 4): necessary, A = TN (not discrete): data 1 and 2 everywhere agree at 0
theorem w21_3 : ¬ drop0% Iris.instDiscreteDynReservationMap 4 := fun h => by
  have := congrArg (fun z => z.data 1) ((@h TN HF _ _).discrete_0
    (x := ⟨fun _ => some ⟨1⟩, ∅⟩) (y := ⟨fun _ => some ⟨2⟩, ∅⟩) ⟨fun _ => tn12, rfl⟩)
  simp at this
-- `Iris.instDiscreteEDynReservationMapMk` (hypothesis 6): necessary, A = TN, a = constant 1 (not discrete)
theorem w21_4 : ¬ drop0% Iris.instDiscreteEDynReservationMapMk 6 := fun h => by
  have := congrArg (fun z => z.data 1) ((@h TN HF _ _ ∅ (fun _ => some ⟨1⟩)).discrete
    (y := ⟨fun _ => some ⟨2⟩, ∅⟩) ⟨fun _ => tn12, rfl⟩)
  simp at this
-- `Iris.instDiscreteEDynReservationMapSingleton` (hypothesis 6): necessary, A = TN, a = 1 (not discrete), mkData 1 1 vs mkData 1 2
theorem w21_5 : ¬ drop0% Iris.instDiscreteEDynReservationMapSingleton 6 := fun h => by
  have := congrArg (fun z => z.data 1) ((@h TN HF _ _ 1 ⟨1⟩).discrete
    (y := DynReservationMap.mkData 1 ⟨2⟩) (instNonExpansiveDynReservationMapSingleton.ne tn12))
  simp [DynReservationMap.mkData, PartialMap.singleton, PartialMap.insert] at this
-- `Iris.DynReservationMap.validN_data_of_validN` (hypothesis 6): necessary, A = Excl Unit, data invalid everywhere
theorem w21_6 : ¬ drop0% Iris.DynReservationMap.validN_data_of_validN 6 := fun h =>
  (@h EU HF _ _ 0 ⟨fun _ => some xi, ∅⟩) 1
-- `Iris.DynReservationMap.validN_token_of_validN` (hypothesis 6): necessary, token error
theorem w21_7 : ¬ drop0% Iris.DynReservationMap.validN_token_of_validN 6 := fun h =>
  DisjointLeibnizSet.not_validN_invalid (@h EU HF _ _ 0 ⟨fun _ => none, .error⟩)
-- `Iris.DynReservationMap.validN_infinite` (hypothesis 6): necessary, token valid top: complement empty
theorem w21_8 : ¬ drop0% Iris.DynReservationMap.validN_infinite 6 := fun h =>
  not_inf_top_top (@h EU HF _ _ 0 ⟨fun _ => none, .valid ⊤⟩)
-- `Iris.DynReservationMap.validN_disj` (hypothesis 6): necessary, data everywhere some, token valid top
theorem w21_9 : ¬ drop0% Iris.DynReservationMap.validN_disj 6 := fun h =>
  (@h EU HF _ _ 0 ⟨fun _ => some xe, .valid ⊤⟩ 1).elim (fun e => nomatch e) (fun hn => hn CoPset.mem_full)
-- `Iris.DynReservationMap.valid_data_of_valid` (hypothesis 5): necessary, data invalid everywhere
theorem w21_10 : ¬ drop0% Iris.DynReservationMap.valid_data_of_valid 5 := fun h =>
  (@h EU HF _ _ ⟨fun _ => some xi, ∅⟩) 1
-- `Iris.DynReservationMap.valid_token_of_valid` (hypothesis 5): necessary, token error
theorem w21_11 : ¬ drop0% Iris.DynReservationMap.valid_token_of_valid 5 := fun h =>
  DisjointLeibnizSet.not_valid_invalid (@h EU HF _ _ ⟨fun _ => none, .error⟩)
-- `Iris.DynReservationMap.valid_infinite` (hypothesis 5): necessary, token valid top
theorem w21_12 : ¬ drop0% Iris.DynReservationMap.valid_infinite 5 := fun h =>
  not_inf_top_top (@h EU HF _ _ ⟨fun _ => none, .valid ⊤⟩)
-- `Iris.DynReservationMap.valid_disj` (hypothesis 5): necessary, data everywhere some, token valid top
theorem w21_13 : ¬ drop0% Iris.DynReservationMap.valid_disj 5 := fun h =>
  (@h EU HF _ _ ⟨fun _ => some xe, .valid ⊤⟩ 1).elim (fun e => nomatch e) (fun hn => hn CoPset.mem_full)
-- `Iris.DynReservationMap.infinite_op_left` (hypothesis 7): necessary, x token top, y token error: op Infinite trivially
theorem w21_14 : ¬ drop0% Iris.DynReservationMap.infinite_op_left 7 := fun h =>
  not_inf_top_top (@h EU HF _ _ 0 ⟨fun _ => none, .valid ⊤⟩ ⟨fun _ => none, .error⟩ trivial)
-- `Iris.DynReservationMap.infinite_op_left` (hypothesis 8): necessary, x token top, y token empty: valid, x not Infinite
theorem w21_15 : ¬ drop0% Iris.DynReservationMap.infinite_op_left 8 := fun h =>
  not_inf_top_top (@h EU HF _ _ 0 ⟨fun _ => none, .valid ⊤⟩ ⟨fun _ => none, ∅⟩
    (DisjointLeibnizSet.valid_op_iff_disj.mpr LawfulSet.disjoint_empty_right).validN)
-- `Iris.DynReservationMap.validN_mono` (hypothesis 7): necessary, x data invalid everywhere, y data valid everywhere, tokens empty
theorem w21_16 : ¬ drop0% Iris.DynReservationMap.validN_mono 7 := fun h =>
  (DynReservationMap.validN_data_of_validN (@h EU HF _ _ 0 ⟨fun _ => some xi, ∅⟩ ⟨fun _ => some xe, ∅⟩
    (fun _ e => nomatch e) ⟨∅, (dls_op_empty _).symm⟩
    (DynReservationMap.validN_iff.mpr ⟨fun _ => trivial, trivial, inf_top_empty, fun i => .inr (DisjointLeibnizSet.mem_empty i)⟩))) 1
-- `Iris.DynReservationMap.validN_mono` (hypothesis 8): necessary, x = (everywhere some, token {1}), y = (empty, token {1}): x not disjoint
theorem w21_17 : ¬ drop0% Iris.DynReservationMap.validN_mono 8 := fun h =>
  ((DynReservationMap.validN_disj (@h EU HF _ _ 0 ⟨fun _ => some xe, .valid {1}⟩ ⟨fun _ => none, .valid {1}⟩
    (fun _ _ => trivial) ⟨∅, (dls_op_empty _).symm⟩
    (DynReservationMap.validN_iff.mpr ⟨fun _ => trivial, trivial, inf_top_one, fun i => .inl rfl⟩)) 1)).elim
    (fun e => nomatch e) (fun hn => hn mem_one)
-- `Iris.DynReservationMap.validN_mono` (hypothesis 10): necessary, x = y with token error
theorem w21_18 : ¬ drop0% Iris.DynReservationMap.validN_mono 10 := fun h =>
  DisjointLeibnizSet.not_validN_invalid (DynReservationMap.validN_token_of_validN
    (@h EU HF _ _ 0 ⟨fun _ => none, .error⟩ ⟨fun _ => none, .error⟩ (fun _ _ => trivial) (fun _ e => e) ⟨.error, rfl⟩))
-- `Iris.DynReservationMap.increasing_data` (hypothesis 5): necessary, A = BA, data false everywhere is not increasing
theorem w21_19 : ¬ drop0% Iris.DynReservationMap.increasing_data 5 := fun h =>
  opt_ba_tf ((@h BA HF _ _ ⟨fun _ => some ⟨false⟩, ∅⟩).increasing (fun _ => some ⟨true⟩) 1)
-- `Iris.DynReservationMap.increasing_token` (hypothesis 5): removable, the token CMRA (DisjointLeibnizSet) orders by inclusion, so every token is increasing
theorem w21_20 : drop% Iris.DynReservationMap.increasing_token 5 := by
  intro A H _ _ v
  exact ⟨fun y => IncOrd.inc_ord ⟨v.token, ORA.comm'⟩⟩
-- `Iris.DynReservationMap.increasing_mk` (hypothesis 5): necessary, A = BA, data false everywhere: v increasing would make data increasing
theorem w21_21 : ¬ drop0% Iris.DynReservationMap.increasing_mk 5 := fun h =>
  opt_ba_tf ((DynReservationMap.increasing_data (@h BA HF _ _ ⟨fun _ => some ⟨false⟩, ∅⟩
    ⟨fun y => IncOrd.inc_ord ⟨_, ORA.comm'⟩⟩)).increasing (fun _ => some ⟨true⟩) 1)
-- `Iris.DynReservationMap.increasing_mk` (hypothesis 6): removable, every DisjointLeibnizSet token is increasing (inclusion order)
theorem w21_22 : drop% Iris.DynReservationMap.increasing_mk 6 := by
  intro A H _ _ v hd
  exact DynReservationMap.increasing_mk hd ⟨fun y => IncOrd.inc_ord ⟨v.token, ORA.comm'⟩⟩
-- `Iris.DynReservationMap.instIncOrd` (hypothesis 4): necessary, A = BA: mkData 1 true is included in mkData 1 false, not ordered
theorem w21_23 : ¬ drop0% Iris.DynReservationMap.instIncOrd 4 := fun h =>
  drm_ba_not_ord ((@h BA HF _ _).inc_ord drm_ba_inc)
-- `Iris.DynReservationMap.instOrdInc` (hypothesis 4): necessary, A = MO (order True, op max): mkData 1 1 ordered below mkData 1 0, not included
theorem w21_24 : ¬ drop0% Iris.DynReservationMap.instOrdInc 4 := fun h => by
  have := (DynReservationMap.inc_iff.mp ((@h MO HF _ _).ord_inc
    (DynReservationMap.mkData_mono_ord (H := HF) (k := 1) (a := (⟨1⟩ : MO)) (b := ⟨0⟩) trivial))).1
  obtain ⟨z, hz⟩ := this
  have h1 : get? _ (1 : Pos) = get? _ (1 : Pos) := congrArg (get? · (1 : Pos)) hz
  rw [Heap.get?_op] at h1
  change some (⟨0⟩ : MO) = ORA.op (some (⟨1⟩ : MO)) (get? z (1 : Pos)) at h1
  cases hz1 : get? z (1 : Pos) with
  | none => rw [hz1] at h1; change some (⟨0⟩ : MO) = some ⟨1⟩ at h1; simp at h1
  | some w =>
    rw [hz1] at h1
    have := congrArg MO.v (Option.some.inj h1); change 0 = max 1 w.v at this; omega
-- `Iris.DynReservationMap.instIsInc` (hypothesis 4): necessary, A = BA (not IncOrd)
theorem w21_25 : ¬ drop0% Iris.DynReservationMap.instIsInc 4 := fun h =>
  drm_ba_not_ord ((@h BA HF _ _).inc_ord drm_ba_inc)
-- `Iris.DynReservationMap.data_proj_validN` (hypothesis 6): necessary, data invalid everywhere
theorem w21_26 : ¬ drop0% Iris.DynReservationMap.data_proj_validN 6 := fun h =>
  (@h EU HF _ _ 0 ⟨fun _ => some xi, ∅⟩) 1
-- `Iris.DynReservationMap.token_proj_validN` (hypothesis 6): necessary, token error
theorem w21_27 : ¬ drop0% Iris.DynReservationMap.token_proj_validN 6 := fun h =>
  DisjointLeibnizSet.not_validN_invalid (@h EU HF _ _ 0 ⟨fun _ => none, .error⟩)
-- `Iris.DynReservationMap.instDiscrete` (hypothesis 4): necessary, A = BO (valid only at step 0): mkData 1 t is 0-valid, not valid
theorem w21_28 : ¬ drop0% Iris.DynReservationMap.instDiscrete 4 := fun h =>
  (DynReservationMap.valid_mkData (H := HF) 1 BO.t).mp
    ((@h BO HF _ _).discrete_valid ((DynReservationMap.validN_mkData (H := HF) (n := 0) 1 BO.t).mpr rfl))
-- `Iris.DynReservationMap.instCoreIdSingleton` (hypothesis 6): necessary, A = Excl Unit (no core): core of mkData 1 (excl ()) has empty data
theorem w21_29 : ¬ drop0% Iris.DynReservationMap.instCoreIdSingleton 6 := fun h => by
  have := congrArg (fun z => z.map (fun w => w.data 1)) (@h EU HF _ _ 1 xe).core_id
  change (some none : Option (Option EU)) = some (some xe) at this
  cases this
-- `Iris.DynReservationMap.split_validN` (hypothesis 6): necessary, token error is no composite of data and token
theorem w21_30 : ¬ drop0% Iris.DynReservationMap.split_validN 6 := fun h => by
  obtain ⟨d, t, e⟩ := @h EU HF _ _ 0 ⟨fun _ => none, .error⟩
  have := congrArg DynReservationMap.token e
  rw [DynReservationMap.op_token, DynReservationMap.mkToken, dls_empty_op] at this
  cases this
-- `Iris.DynReservationMap.mkData_mono_ord` (hypothesis 7): necessary, A = BA (order equality): true, false
theorem w21_31 : ¬ drop0% Iris.DynReservationMap.mkData_mono_ord 7 := fun h =>
  drm_ba_not_ord (@h BA HF _ _ 1 ⟨true⟩ ⟨false⟩)
-- `Iris.DynReservationMap.mkData_mono` (hypothesis 7): necessary, A = Excl Unit: invalid is not included in excl ()
theorem w21_32 : ¬ drop0% Iris.DynReservationMap.mkData_mono 7 := fun h => by
  obtain ⟨z, hz⟩ := (DynReservationMap.inc_iff.mp (@h EU HF _ _ 1 xi xe)).1
  have h1 : get? _ (1 : Pos) = get? _ (1 : Pos) := congrArg (get? · (1 : Pos)) hz
  rw [Heap.get?_op] at h1
  change some xe = ORA.op (some xi) (get? z (1 : Pos)) at h1
  cases hz1 : get? z (1 : Pos) with
  | none => rw [hz1] at h1; change some xe = some xi at h1; cases h1
  | some w => rw [hz1] at h1; change some xe = some xi at h1; cases h1
-- `Iris.DynReservationMap.instIsOpMkData` (hypothesis 9): necessary, A = Excl Unit, a = b1 = b2 = excl (): excl () • excl () is invalid
theorem w21_33 : ¬ drop0% Iris.DynReservationMap.instIsOpMkData 9 := fun h => by
  have e := (@h EU HF _ _ 1 .merge xe xe xe).is_op
  rw [← DynReservationMap.mkData_op] at e
  have := congrArg (fun w => w.data (1 : Pos)) e
  change some xe = some xi at this
  cases this
-- `Iris.DynReservationMap.token_union` (hypothesis 6): necessary, e1 = e2 = top: union valid, op invalid
theorem w21_34 : ¬ drop0% Iris.DynReservationMap.token_union 6 := fun h => by
  have e := congrArg DynReservationMap.token (@h EU HF _ _ ⊤ ⊤)
  rw [DynReservationMap.op_token] at e
  have v : ✓ ((DynReservationMap.mkToken (H := HF) (A := EU) ⊤).token • (DynReservationMap.mkToken (H := HF) (A := EU) ⊤).token) := by
    rw [← e]; exact DisjointLeibnizSet.valid_set
  exact DisjointLeibnizSet.valid_op_iff_disj.mp v 1 ⟨CoPset.mem_full, CoPset.mem_full⟩
-- `Iris.DynReservationMap.token_difference` (hypothesis 6): necessary, e1 = top, e2 = empty: 1 is in the op, not in empty
theorem w21_35 : ¬ drop0% Iris.DynReservationMap.token_difference 6 := fun h => by
  have e := congrArg DynReservationMap.token (@h EU HF _ _ ⊤ ∅)
  rw [DynReservationMap.op_token] at e
  have v : ✓{0} ((DynReservationMap.mkToken (H := HF) (A := EU) ⊤).token • (DynReservationMap.mkToken (H := HF) (A := EU) ((∅ : CoPset) \ ⊤)).token) :=
    e ▸ DisjointLeibnizSet.validN_set
  have m := (DisjointLeibnizSet.mem_iff_of_validN_union v (1 : Pos)).mpr (.inl CoPset.mem_full)
  rw [← e] at m
  exact LawfulSet.mem_empty (show (1 : Pos) ∈ (∅ : CoPset) from m)
-- `Iris.DynReservationMap.disj_of_validN_data_op_token` (hypothesis 7): necessary, a everywhere some, b = top, i = 1
theorem w21_36 : ¬ drop0% Iris.DynReservationMap.disj_of_validN_data_op_token 7 := fun h =>
  (@h EU HF _ _ 0 (fun _ => some xe) ⊤ 1).elim (fun e => nomatch e) (fun hn => hn CoPset.mem_full)
-- `Iris.DynReservationMap.infinite_data_op_token` (hypothesis 7): necessary, b = top
theorem w21_37 : ¬ drop0% Iris.DynReservationMap.infinite_data_op_token 7 := fun h =>
  not_inf_top_top (@h EU HF _ _ 0 (fun _ => none) ⊤)
-- `Iris.DynReservationMap.validN_data_op_token` (hypothesis 7): necessary, a invalid everywhere, b = empty
theorem w21_38 : ¬ drop0% Iris.DynReservationMap.validN_data_op_token 7 := fun h =>
  (DynReservationMap.validN_data_of_validN (ORA.validN_op_left (@h EU HF _ _ 0 (fun _ => some xi) ∅ inf_top_empty
    (fun i => .inr (LawfulSet.mem_empty))))) (1 : Pos)
-- `Iris.DynReservationMap.validN_data_op_token` (hypothesis 8): necessary, a empty, b = top
theorem w21_39 : ¬ drop0% Iris.DynReservationMap.validN_data_op_token 8 := fun h =>
  not_inf_top_top (DynReservationMap.infinite_data_op_token (@h EU HF _ _ 0 (fun _ => none) ⊤ (fun _ => trivial) (fun _ => .inl rfl)))
-- `Iris.DynReservationMap.validN_data_op_token` (hypothesis 9): necessary, a everywhere some, b = {1}
theorem w21_40 : ¬ drop0% Iris.DynReservationMap.validN_data_op_token 9 := fun h =>
  (DynReservationMap.disj_of_validN_data_op_token (@h EU HF _ _ 0 (fun _ => some xe) {1} (fun _ => trivial) inf_top_one) 1).elim
    (fun e => nomatch e) (fun hn => hn mem_one)
-- `Iris.DynReservationMap.valid_op?_of_valid_mkData_op_data` (hypothesis 8): necessary, a invalid, x empty
theorem w21_41 : ¬ drop0% Iris.DynReservationMap.valid_op?_of_valid_mkData_op_data 8 := fun h =>
  (@h EU HF _ _ 0 1 xi (fun _ => none) : ✓{0} xi)
-- `Iris.DynReservationMap.valid_mkData_op_data_of_valid_op?` (hypothesis 8): necessary, a = excl (), x invalid at 2 only
theorem w21_42 : ¬ drop0% Iris.DynReservationMap.valid_mkData_op_data_of_valid_op? 8 := fun h =>
  (DynReservationMap.validN_data_of_validN (ORA.validN_op_right
    (@h EU HF _ _ 0 1 xe (fun i => if i = 1 then none else some xi) trivial))) (2 : Pos)
-- `Iris.DynReservationMap.valid_mkData_op_data_of_valid_op?` (hypothesis 9): necessary, a invalid, x empty
theorem w21_43 : ¬ drop0% Iris.DynReservationMap.valid_mkData_op_data_of_valid_op? 9 := fun h =>
  (DynReservationMap.valid_op?_of_valid_mkData_op_data (@h EU HF _ _ 0 1 xi (fun _ => none) (fun _ => trivial)) : ✓{0} xi)
-- `Iris.DynReservationMap.alloc` (hypothesis 7): necessary, e = empty, a = excl (): frame mkData 1 (excl ()) is compatible with mkToken empty only
theorem w21_44 : ¬ drop0% Iris.DynReservationMap.alloc 7 := fun h => by
  have := @h EU HF _ _ ∅ 1 xe trivial 0 (some (DynReservationMap.mkData 1 xe))
    (by
      change ✓{0} (UORA.unit • DynReservationMap.mkData (H := HF) 1 xe)
      rw [UORA.unit_left_id]; exact mk_xe_ok 0)
  change ✓{0} (DynReservationMap.mkData (H := HF) 1 xe • DynReservationMap.mkData 1 xe) at this
  rw [← DynReservationMap.mkData_op] at this
  exact mk_xi_bad 0 this
-- `Iris.DynReservationMap.alloc` (hypothesis 8): necessary, e = {1}, k = 1, a invalid, no frame
theorem w21_45 : ¬ drop0% Iris.DynReservationMap.alloc 8 := fun h =>
  mk_xi_bad 0 (@h EU HF _ _ {1} 1 xi mem_one 0 none ((DynReservationMap.valid_token (H := HF) (A := EU)).mpr inf_top_one).validN)
-- `Iris.DynReservationMap.updateP` (hypothesis 8): necessary, P = Q = False, a = excl () (valid)
theorem w21_46 : ¬ drop0% Iris.DynReservationMap.updateP 8 := fun h => by
  obtain ⟨_, hq, _⟩ := @h EU HF _ _ (fun _ => False) (fun _ => False) 1 xe (fun _ hp => hp) 0 none (mk_xe_ok 0)
  exact hq
-- `Iris.DynReservationMap.updateP` (hypothesis 9): necessary, P = True, Q = False, a = excl ()
theorem w21_47 : ¬ drop0% Iris.DynReservationMap.updateP 9 := fun h => by
  obtain ⟨_, hq, _⟩ := @h EU HF _ _ (fun _ => True) (fun _ => False) 1 xe (fun _ _ v => ⟨xe, trivial, v⟩) 0 none (mk_xe_ok 0)
  exact hq
-- `Iris.DynReservationMap.update` (hypothesis 7): necessary, a = excl (), b invalid, no frame
theorem w21_48 : ¬ drop0% Iris.DynReservationMap.update 7 := fun h =>
  mk_xi_bad 0 (@h EU HF _ _ 1 xe xi 0 none (mk_xe_ok 0))
-- `Iris.DynReservationMap.reserve` (hypothesis 5): necessary, H = ExtTreeMap over Pos, Q = False: the unit is valid
theorem w21_49 : ¬ drop0% Iris.DynReservationMap.reserve 5 := fun h => by
  obtain ⟨_, hq, _⟩ := @h EU (fun V => Std.ExtTreeMap Pos V compare) _ _ (fun _ => False) 0 none UORA.unit_valid.validN
  exact hq
-- `Iris.DFrac.isOp_dfrac_own` (hypothesis 4): necessary, q = q1 = q2 = 1: own 1 is not own 1 • own 1 = own 2
theorem w21_50 : ¬ drop0% Iris.DFrac.isOp_dfrac_own 4 := fun h => by
  have := (@h .merge 1 1 1).is_op
  change DFrac.own 1 = DFrac.own (1 + 1) at this
  injection this with e
  have := congrArg Subtype.val e
  change (1 : Rat) = 1 + 1 at this
  grind
-- `Iris.Frac.le_of_ord` (hypothesis 2): necessary, p = 2, q = 1
theorem w21_51 : ¬ drop0% Iris.Frac.le_of_ord 2 := fun h => by
  have := @h (1 + 1) 1
  change (1 : Rat) + 1 ≤ 1 at this
  grind
-- `Iris.Frac.le_of_inc` (hypothesis 2): necessary, p = 2, q = 1
theorem w21_52 : ¬ drop0% Iris.Frac.le_of_inc 2 := fun h => by
  have := @h (1 + 1) 1
  change (1 : Rat) + 1 ≤ 1 at this
  grind
-- `Iris.Excl.ne_match` (hypothesis 5): necessary, alpha = B = TN, f maps 1 to 0 and else to 1 (not non-expansive)
theorem w21_53 : ¬ drop0% Iris.Excl.ne_match 5 := fun h =>
  tn01 ((@h TN _ TN _ (fun a => if a.v = 1 then ⟨0⟩ else ⟨1⟩) ⟨0⟩).ne (n := 0) (x₁ := .excl ⟨1⟩) (x₂ := .excl ⟨2⟩) tn12)
-- `Iris.Excl.instDiscrete` (hypothesis 2): necessary, alpha = TN: excl 1 and excl 2 agree at 0
theorem w21_54 : ¬ drop0% Iris.Excl.instDiscrete 2 := fun h =>
  tn12ne (Excl.excl.inj ((@h TN _).discrete_0 (x := .excl ⟨1⟩) (y := .excl ⟨2⟩) tn12))
-- `Iris.Excl.instDiscreteEExcl` (hypothesis 3): necessary, alpha = TN, a = 1
theorem w21_55 : ¬ drop0% Iris.Excl.instDiscreteEExcl 3 := fun h =>
  tn12ne (Excl.excl.inj ((@h TN _ ⟨1⟩).discrete (y := .excl ⟨2⟩) tn12))
-- `Iris.Excl.validN_inv_some_l` (hypothesis 5): necessary, mx = some (excl ())
theorem w21_56 : ¬ drop0% Iris.Excl.validN_inv_some_l 5 := fun h => nomatch (@h Unit _ 0 (some (.excl ())) ())
-- `Iris.Excl.validN_inv_some_r` (hypothesis 5): necessary, mx = some (excl ())
theorem w21_57 : ¬ drop0% Iris.Excl.validN_inv_some_r 5 := fun h => nomatch (@h Unit _ 0 (some (.excl ())) ())
-- `Iris.Excl.instDiscreteOfDiscrete` (hypothesis 2): necessary, alpha = TN: Excl TN is not discrete
theorem w21_58 : ¬ drop0% Iris.Excl.instDiscreteOfDiscrete 2 := fun h =>
  tn12ne (Excl.excl.inj ((@h TN _).toDiscrete.discrete_0 (x := .excl ⟨1⟩) (y := .excl ⟨2⟩) tn12))
-- `Iris.Excl.map_ext` (hypothesis 7): necessary, alpha = beta = TN, x = excl 0, f = id, g = const 1
theorem w21_59 : ¬ drop0% Iris.Excl.map_ext 7 := fun h => by
  have := @h TN TN (.excl ⟨0⟩) _ _ id (fun _ => ⟨1⟩)
  simp at this
-- `Iris.discreteFunInsert_of_ne` (hypothesis 7): necessary, iota = Unit, x = x', y = true, f = const false
theorem w21_60 : ¬ drop0% Iris.discreteFunInsert_of_ne 7 := fun h => by
  have := @h Unit _ (fun _ => Bool) (fun _ => false) () () true
  simp [discreteFunInsert] at this
-- `Iris.instDiscreteFunOfeDiscrete` (hypothesis 3): necessary, iota = Unit, beta = TN (not discrete)
theorem w21_61 : ¬ drop0% Iris.instDiscreteFunOfeDiscrete 3 := fun h =>
  tn12ne (congrFun ((@h Unit (fun _ => TN) _).discrete_0 (x := fun _ => ⟨1⟩) (y := fun _ => ⟨2⟩) (fun _ => tn12)) ())
-- `Iris.discreteE_pi` (hypothesis 4): necessary, iota = Unit, f = const 1 in TN
theorem w21_62 : ¬ drop0% Iris.discreteE_pi 4 := fun h =>
  tn12ne (congrFun ((@h Unit (fun _ => TN) _ (fun _ => ⟨1⟩)).discrete (y := fun _ => ⟨2⟩) (fun _ => tn12)) ())
-- `Iris.discreteE_apply` (hypothesis 5): necessary, iota = Unit, f = const 1 in TN
theorem w21_63 : ¬ drop0% Iris.discreteE_apply 5 := fun h =>
  tn12ne ((@h Unit _ (fun _ => TN) _ (fun _ => ⟨1⟩) ()).discrete (y := ⟨2⟩) tn12)
-- `Iris.instDiscreteFunInsertDiscrete` (hypothesis 7): necessary, iota = Bool, f = const 1 in TN, insert 0 at true; differs from (true:0, false:2) only at false
theorem w21_64 : ¬ drop0% Iris.instDiscreteFunInsertDiscrete 7 := fun h => by
  have := congrFun ((@h Bool _ (fun _ => TN) _ (fun _ => ⟨1⟩) true ⟨0⟩ tn0disc).discrete
    (y := fun b => if b then ⟨0⟩ else ⟨2⟩) (fun b => by cases b <;> simp [discreteFunInsert] <;> first | exact tn12 | exact OFE.Dist.rfl)) false
  simp [discreteFunInsert] at this
-- `Iris.instDiscreteFunInsertDiscrete` (hypothesis 8): necessary, iota = Unit, f = const 0 (discrete), y = 1 in TN
theorem w21_65 : ¬ drop0% Iris.instDiscreteFunInsertDiscrete 8 := fun h => by
  have := congrFun ((@h Unit _ (fun _ => TN) _ (fun _ => ⟨0⟩) () ⟨1⟩ (discreteE_pi fun _ => tn0disc)).discrete
    (y := fun _ => ⟨2⟩) (fun b => by simp [discreteFunInsert]; exact tn12)) ()
  simp [discreteFunInsert] at this
-- `Iris.instDiscreteFunCmraDiscrete` (hypothesis 3): necessary, iota = Unit, beta = Option BO: some t is 0-valid, not valid
theorem w21_66 : ¬ drop0% Iris.instDiscreteFunCmraDiscrete 3 := fun h =>
  ((@h Unit (fun _ => Option BO) _).discrete_valid (x := fun _ => some BO.t) (fun _ => (rfl : 0 = 0))) ()
-- `Iris.discreteFunSingleton_of_ne` (hypothesis 7): necessary, iota = Unit, beta = Option (Excl Unit), y = some (excl ()) is not the unit none
theorem w21_67 : ¬ drop0% Iris.discreteFunSingleton_of_ne 7 := fun h => by
  have := @h Unit _ (fun _ => Option EU) _ () () (some xe)
  simp [discreteFunSingleton, discreteFunInsert] at this
-- `Iris.instDiscreteFunSingletonDiscrete` (hypothesis 6): necessary, iota = Bool, beta true = Unit, beta false = NU (non-discrete unit true)
theorem w21_68 : ¬ drop0% Iris.instDiscreteFunSingletonDiscrete 6 := fun h => by
  have := congrFun ((@h Bool _ βB instβB true () ⟨fun _ => rfl⟩).discrete
    (y := fun i => match i with | true => () | false => (⟨false⟩ : NU))
    (fun i => match i with | true => OFE.Dist.of_eq rfl | false => by exact Or.inl rfl)) false
  change (⟨true⟩ : NU) = ⟨false⟩ at this
  cases this
-- `Iris.instDiscreteFunSingletonDiscrete` (hypothesis 7): necessary, iota = Unit, beta = Option (Excl TN), y = some (excl 1)
theorem w21_69 : ¬ drop0% Iris.instDiscreteFunSingletonDiscrete 7 := fun h => by
  have := congrFun ((@h Unit _ (fun _ => Option (Excl TN)) _ () (some (.excl ⟨1⟩)) (fun _ => (OFE.Option.none_is_discrete : DiscreteE (none : Option (Excl TN))))).discrete
    (y := fun _ => some (.excl ⟨2⟩)) (fun _ => by simp [discreteFunSingleton, discreteFunInsert]; exact tn12)) ()
  simp [discreteFunSingleton, discreteFunInsert] at this
-- `Iris.instDiscreteFunSingletonCoreId` (hypothesis 6): necessary, iota = Unit, beta = Option (Excl Unit), y = some (excl ()) has core none
theorem w21_70 : ¬ drop0% Iris.instDiscreteFunSingletonCoreId 6 := fun h => by
  have := congrArg (fun o => o.map (fun f => f ())) (@h Unit _ (fun _ => Option EU) _ () (some xe)).core_id
  change (some none : Option (Option EU)) = some (some xe) at this
  cases this
-- `Iris.discreteFunSingleton_op_insert` (hypothesis 8): necessary, iota = Unit, y = y' = none, f = const some (excl ())
theorem w21_71 : ¬ drop0% Iris.discreteFunSingleton_op_insert 8 := fun h => by
  have := congrFun (@h Unit _ (fun _ => Option EU) _ () none none (fun _ => some xe)) ()
  change (none : Option EU) = some xe at this
  cases this
-- `Iris.discreteFunInsert_updateP` (hypothesis 9): necessary, iota = Unit, beta = Option (Excl Unit), P = Q = False, everything none (valid)
theorem w21_72 : ¬ drop0% Iris.discreteFunInsert_updateP 9 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit _ (fun _ => Option EU) _ () (fun _ => False) (fun _ => False) (fun _ => none) none
    (fun _ hp => hp) 0 none (fun _ => by simp [discreteFunInsert]; trivial)
  exact hq
-- `Iris.discreteFunInsert_updateP` (hypothesis 10): necessary, P = True, Q = False
theorem w21_73 : ¬ drop0% Iris.discreteFunInsert_updateP 10 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit _ (fun _ => Option EU) _ () (fun _ => True) (fun _ => False) (fun _ => none) none
    (fun _ _ v => ⟨_, trivial, v⟩) 0 none (fun _ => by simp [discreteFunInsert]; trivial)
  exact hq
-- `Iris.discreteFunInsert_updateP'` (hypothesis 8): necessary, P = False
theorem w21_74 : ¬ drop0% Iris.discreteFunInsert_updateP' 8 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h Unit _ (fun _ => Option EU) _ () (fun _ => False) (fun _ => none) none
    0 none (fun _ => by simp [discreteFunInsert]; trivial)
  exact hp
-- `Iris.discreteFunInsert_update` (hypothesis 8): necessary, y1 = none, y2 = some invalid
theorem w21_75 : ¬ drop0% Iris.discreteFunInsert_update 8 := fun h => by
  have := (@h Unit _ (fun _ => Option EU) _ (fun _ => none) () none (some xi)
    0 none (fun _ => by simp [discreteFunInsert]; trivial)) ()
  simp [discreteFunInsert] at this
  exact this
-- `Iris.discreteFunSingleton_updateP` (hypothesis 8): necessary, P = Q = False, y1 = none
theorem w21_76 : ¬ drop0% Iris.discreteFunSingleton_updateP 8 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit _ (fun _ => Option EU) _ () (fun _ => False) (fun _ => False) none
    (fun _ hp => hp) 0 none (fun _ => by simp [discreteFunSingleton, discreteFunInsert]; trivial)
  exact hq
-- `Iris.discreteFunSingleton_updateP` (hypothesis 9): necessary, P = True, Q = False
theorem w21_77 : ¬ drop0% Iris.discreteFunSingleton_updateP 9 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit _ (fun _ => Option EU) _ () (fun _ => True) (fun _ => False) none
    (fun _ _ v => ⟨_, trivial, v⟩) 0 none (fun _ => by simp [discreteFunSingleton, discreteFunInsert]; trivial)
  exact hq
-- `Iris.discreteFunSingleton_updateP'` (hypothesis 7): necessary, P = False
theorem w21_78 : ¬ drop0% Iris.discreteFunSingleton_updateP' 7 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h Unit _ (fun _ => Option EU) _ () (fun _ => False) none
    0 none (fun _ => by simp [discreteFunSingleton, discreteFunInsert]; trivial)
  exact hp
-- `Iris.discreteFunSingleton_update` (hypothesis 7): necessary, y1 = none, y2 = some invalid
theorem w21_79 : ¬ drop0% Iris.discreteFunSingleton_update 7 := fun h => by
  have := (@h Unit _ (fun _ => Option EU) _ () none (some xi)
    0 none (fun _ => by simp [discreteFunSingleton, discreteFunInsert]; trivial)) ()
  simp [discreteFunSingleton, discreteFunInsert] at this
  exact this
-- `Iris.discreteFunSingleton_updateP_unit` (hypothesis 7): necessary, P = Q = False: the unit is valid
theorem w21_80 : ¬ drop0% Iris.discreteFunSingleton_updateP_unit 7 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit _ (fun _ => Option EU) _ () (fun _ => False) (fun _ => False)
    (fun _ hp => hp) 0 none (fun _ => trivial)
  exact hq
-- `Iris.discreteFunSingleton_updateP_unit` (hypothesis 8): necessary, P = True, Q = False
theorem w21_81 : ¬ drop0% Iris.discreteFunSingleton_updateP_unit 8 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit _ (fun _ => Option EU) _ () (fun _ => True) (fun _ => False)
    (fun _ _ v => ⟨_, trivial, v⟩) 0 none (fun _ => trivial)
  exact hq
-- `Iris.discreteFunSingleton_updateP_unit'` (hypothesis 6): necessary, P = False
theorem w21_82 : ¬ drop0% Iris.discreteFunSingleton_updateP_unit' 6 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h Unit _ (fun _ => Option EU) _ () (fun _ => False) 0 none (fun _ => trivial)
  exact hp
-- `Iris.discreteFunSingleton_update_unit` (hypothesis 6): necessary, y = some invalid
theorem w21_83 : ¬ drop0% Iris.discreteFunSingleton_update_unit 6 := fun h => by
  have := (@h Unit _ (fun _ => Option EU) _ () (some xi) 0 none (fun _ => trivial)) ()
  simp [discreteFunSingleton, discreteFunInsert] at this
  exact this
-- `Iris.discreteFun_updateP` (hypothesis 6): necessary, iota = Unit, P = Q = False, f = const none
theorem w21_84 : ¬ drop0% Iris.discreteFun_updateP 6 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit (fun _ => Option EU) _ (fun _ => none) (fun _ _ => False) (fun _ => False)
    (fun _ hp => hp ()) 0 none (fun _ => trivial)
  exact hq
-- `Iris.discreteFun_updateP` (hypothesis 7): necessary, P = True, Q = False
theorem w21_85 : ¬ drop0% Iris.discreteFun_updateP 7 := fun h => by
  obtain ⟨_, hq, _⟩ := @h Unit (fun _ => Option EU) _ (fun _ => none) (fun _ _ => True) (fun _ => False)
    (fun _ _ _ v => ⟨_, trivial, v⟩) 0 none (fun _ => trivial)
  exact hq
-- `Iris.discreteFun_updateP'` (hypothesis 5): necessary, P = False
theorem w21_86 : ¬ drop0% Iris.discreteFun_updateP' 5 := fun h => by
  obtain ⟨_, hp, _⟩ := @h Unit (fun _ => Option EU) _ (fun _ => none) (fun _ _ => False) 0 none (fun _ => trivial)
  exact hp ()
-- `Iris.discreteFun_update` (hypothesis 5): necessary, f = const none, g = const some invalid
theorem w21_87 : ¬ drop0% Iris.discreteFun_update 5 := fun h =>
  ((@h Unit (fun _ => Option EU) _ (fun _ => none) (fun _ => some xi) 0 none (fun _ => trivial)) () : ✓{0} xi)
-- `Iris.GenMap.exists_fresh_sat` (hypothesis 3): necessary, P = False
theorem w21_88 : ¬ drop0% Iris.GenMap.exists_fresh_sat 3 := fun h => by
  obtain ⟨_, _, hp⟩ := @h Unit GenMap.empty (fun _ => False)
  exact hp
-- `Iris.GenMap.singleton_discreteE` (hypothesis 4): necessary, beta = TN, v = 1: singleton 0 1 and singleton 0 2 agree at 0
theorem w21_89 : ¬ drop0% Iris.GenMap.singleton_discreteE 4 := fun h => by
  have := congrArg (fun g => g.car 0) ((@h TN 0 ⟨1⟩ _).discrete (y := GenMap.singleton 0 ⟨2⟩)
    (fun k => by cases k <;> first | exact tn12 | exact OFE.Dist.rfl))
  change some (⟨1⟩ : TN) = some ⟨2⟩ at this
  simp at this
-- `Iris.GenMap.ext` (hypothesis 3): necessary, empty vs singleton 0 ()
theorem w21_90 : ¬ drop0% Iris.GenMap.ext 3 := fun h => by
  have := congrArg (fun g => g.car 0) (@h Unit GenMap.empty (GenMap.singleton 0 ()))
  cases this
-- `Iris.GenMap.alter_of_lookup` (hypothesis 4): necessary, g = empty, x = 0, y = some ()
theorem w21_91 : ¬ drop0% Iris.GenMap.alter_of_lookup 4 := fun h => by
  have := congrArg (fun g => g.car 0) (@h Unit GenMap.empty 0 (some ()))
  cases this
-- `Iris.pcore_bound` (hypothesis 4): necessary, cx = const some (excl ())
theorem w21_92 : ¬ drop0% Iris.pcore_bound 4 := fun h => by
  obtain ⟨N, hN⟩ := @h EU _ GenMap.empty (fun _ => some xe)
  cases hN N (Nat.le_refl N)
-- `Iris.extend_bound` (hypothesis 6): necessary, beta = Excl Unit, x = singleton 0 invalid, y1 = empty, y2 = x.car
theorem w21_93 : ¬ indep0% Iris.extend_bound 6 := fun h =>
  (@h EU _ 0 (GenMap.singleton 0 xi) (fun _ => none) (GenMap.singleton 0 xi).car
    (OFE.Dist.of_eq (funext fun k => by cases k <;> rfl))) 0
-- `Iris.extend_bound` (hypothesis 7): necessary, x = empty, y1 = const some (excl ()), y2 = empty
theorem w21_94 : ¬ indep0% Iris.extend_bound 7 := fun h => by
  have := (@h EU _ 0 GenMap.empty (fun _ => some xe) (fun _ => none) (fun _ => trivial)) 0
  change (none : Option EU) ≡{0}≡ some xe at this
  exact this
-- `Iris.GenMap.increasing_apply` (hypothesis 3): necessary, beta = BA, x = singleton 0 false, k = 0
theorem w21_95 : ¬ drop0% Iris.GenMap.increasing_apply 3 := fun h =>
  opt_ba_tf ((@h BA _ (GenMap.singleton 0 ⟨false⟩) 0).increasing (some ⟨true⟩))
-- `Iris.GenMap.increasing_car` (hypothesis 3): necessary, beta = BA, x = singleton 0 false
theorem w21_96 : ¬ drop0% Iris.GenMap.increasing_car 3 := fun h =>
  opt_ba_tf ((@h BA _ (GenMap.singleton 0 ⟨false⟩)).increasing (fun _ => some ⟨true⟩) 0)
-- `Iris.GenMap.increasing_of_car` (hypothesis 3): necessary, beta = BA, x = singleton 0 false
theorem w21_97 : ¬ drop0% Iris.GenMap.increasing_of_car 3 := fun h =>
  opt_ba_tf ((@h BA _ (GenMap.singleton 0 ⟨false⟩)).increasing (GenMap.singleton 0 ⟨true⟩) 0)
-- `Iris.instIncOrdGenMap` (hypothesis 2): necessary, beta = BA: singleton 0 true included in singleton 0 false, not ordered
theorem w21_98 : ¬ drop0% Iris.instIncOrdGenMap 2 := fun h =>
  opt_ba_tf (((@h BA _).inc_ord (x := GenMap.singleton 0 ⟨true⟩) (y := GenMap.singleton 0 ⟨false⟩)
    ⟨GenMap.singleton 0 ⟨false⟩, (GenMap.singleton_map_op BA 0 ⟨true⟩ ⟨false⟩).symm⟩) 0)
-- `Iris.instOrdIncGenMap` (hypothesis 2): necessary, beta = MO (order True, op max): singleton 0 1 ordered below singleton 0 0, not included
theorem w21_99 : ¬ drop0% Iris.instOrdIncGenMap 2 := fun h => by
  obtain ⟨z, hz⟩ := (@h MO _).ord_inc (GenMap.singleton_ord_mono MO (x := 0) (y := ⟨1⟩) (y' := ⟨0⟩) trivial)
  have h1 := congrArg (fun g => g.car 0) hz
  change some (⟨0⟩ : MO) = ORA.op (some (⟨1⟩ : MO)) (z.car 0) at h1
  cases hz1 : z.car 0 with
  | none => rw [hz1] at h1; change some (⟨0⟩ : MO) = some ⟨1⟩ at h1; simp at h1
  | some w =>
    rw [hz1] at h1
    have := congrArg MO.v (Option.some.inj h1); change 0 = max 1 w.v at this; omega
-- `Iris.instIsIncGenMap` (hypothesis 2): necessary, beta = BA (not IncOrd)
theorem w21_100 : ¬ drop0% Iris.instIsIncGenMap 2 := fun h =>
  opt_ba_tf (((@h BA _).inc_ord (x := GenMap.singleton 0 ⟨true⟩) (y := GenMap.singleton 0 ⟨false⟩)
    ⟨GenMap.singleton 0 ⟨false⟩, (GenMap.singleton_map_op BA 0 ⟨true⟩ ⟨false⟩).symm⟩) 0)
-- `Iris.GenMap.singleton_ord_mono` (hypothesis 5): necessary, beta = BA, y = true, y' = false
theorem w21_101 : ¬ drop0% Iris.GenMap.singleton_ord_mono 5 := fun h =>
  opt_ba_tf ((@h BA _ 0 ⟨true⟩ ⟨false⟩) 0)
-- `Iris.GenMap.alter_valid` (hypothesis 6): necessary, b = some invalid, g = empty, a = 0
theorem w21_102 : ¬ drop0% Iris.GenMap.alter_valid 6 := fun h =>
  ((@h EU _ 0 (some xi) 0 GenMap.empty (fun _ => trivial)) 0 : ✓{0} xi)
-- `Iris.GenMap.alter_valid` (hypothesis 7): necessary, b = none, a = 0, g = singleton 1 invalid
theorem w21_103 : ¬ drop0% Iris.GenMap.alter_valid 7 := fun h =>
  ((@h EU _ 0 none 0 (GenMap.singleton 1 xi) trivial) 1 : ✓{0} xi)
-- `Iris.GenMap.op_singleton_comm` (hypothesis 5): necessary, mf = singleton 0 (excl ()), y = excl ()
theorem w21_104 : ¬ drop0% Iris.GenMap.op_singleton_comm 5 := fun h => by
  have := congrArg (fun g => g.car 0) (@h EU _ (GenMap.singleton 0 xe) 0 xe)
  change some xi = some xe at this
  cases this
-- `Iris.GenMap.singleton_op_alter_none` (hypothesis 5): necessary, g = empty
theorem w21_105 : ¬ drop0% Iris.GenMap.singleton_op_alter_none 5 := fun h => by
  have := congrArg (fun g => g.car 0) (@h EU _ GenMap.empty 0 xe)
  change some xe = none at this
  cases this
-- `Iris.GenMap.validN_op_comm` (hypothesis 7): necessary, m = empty, mf = singleton 0 (excl ()), y = excl (): only the right side is valid
theorem w21_106 : ¬ drop0% Iris.GenMap.validN_op_comm 7 := fun h =>
  ((@h EU _ 0 GenMap.empty (GenMap.singleton 0 xe) 0 xe).mpr (fun k => by cases k <;> trivial) 0 : ✓{0} xi)
-- `Iris.instRFunctorAffineGenMapOF` (hypothesis 2): necessary, F = constOF BA: GenMap BA is not IncOrd
theorem w21_107 : ¬ drop0% Iris.instRFunctorAffineGenMapOF 2 := fun h =>
  opt_ba_tf ((((@h (constOF BA) _).affine (α := Unit) (β := Unit)).inc_ord (x := GenMap.singleton 0 ⟨true⟩) (y := GenMap.singleton 0 ⟨false⟩)
    ⟨GenMap.singleton 0 ⟨false⟩, (GenMap.singleton_map_op BA 0 ⟨true⟩ ⟨false⟩).symm⟩) 0)
