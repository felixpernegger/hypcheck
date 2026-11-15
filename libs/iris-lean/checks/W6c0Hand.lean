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
namespace W6c0
set_option linter.constructorNameAsVariable false
open Iris Iris.BI Iris.Std Iris.Algebra

-- helper: step-indexed prop true only at step 0 (not timeless; copied from W5c0)
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩

-- helper: a SiProp holding at 0 but not at 1 is not timeless
theorem nt {Q : SiProp} (h : iprop(▷ Q) ⊢ iprop(◇ Q)) (h0 : Q.holds 0) (h1 : ¬ Q.holds 1) : False := by
  rcases h 1 h0 with h' | h'
  · exact h'
  · exact h1 h'

-- helper: two-element UORA with equality order (copied from Probe3): UPred NA is non-affine
inductive NA | e | a deriving DecidableEq
def NA.op : NA → NA → NA
  | .e, y => y
  | .a, _ => .a
instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨id⟩
instance instORA : ORA NA := ORA.ofDiscreteORAData {
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
instance instUORA : UORA NA where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

-- helper: in UPred NA, True does not entail emp
theorem na_true_not_emp : ¬ ((iprop(True) : UPred NA) ⊢ iprop(emp)) := fun h => by
  have H := h 0 ⟨.a, trivial⟩ trivial
  cases H

-- helper: in UPred NA a prop holding at a but not at the unit e is neither plain nor persistent
theorem naE {X : UPred NA} (h : X ⊢ UPred.persistently X) (ha : X.holds 0 ⟨.a, trivial⟩)
    (he : ¬ X.holds 0 ⟨.e, trivial⟩) : False := he (h 0 ⟨.a, trivial⟩ ha)

theorem naP {X : UPred NA} (h : X ⊢ ■ X) (ha : X.holds 0 ⟨.a, trivial⟩)
    (he : ¬ X.holds 0 ⟨.e, trivial⟩) : False := he (h 0 ⟨.a, trivial⟩ ha)
-- helper: emp → False holds at a, not at e in UPred NA
theorem ne_a : (iprop(emp → False) : UPred NA).holds 0 ⟨.a, trivial⟩ :=
  fun x' h1 _ h2 => by rcases x' with ⟨x', _⟩; cases h1; cases h2
theorem ne_e : ¬ (iprop(emp → False) : UPred NA).holds 0 ⟨.e, trivial⟩ :=
  fun H => H ⟨.e, trivial⟩ rfl (Nat.le_refl 0) rfl
abbrev TM := fun V => Std.ExtTreeMap Nat V compare

-- helper: Bool with xor (copied from W4c5): UPred X2 is non-affine and not positive
inductive X2 | o | i deriving DecidableEq
def X2.op : X2 → X2 → X2
  | .o, y => y
  | .i, .o => .i
  | .i, .i => .o
instance : OFE X2 := OFE.ofDiscrete X2
instance : OFE.Discrete X2 := ⟨id⟩
instance x2ORA : ORA X2 := ORA.ofDiscreteORAData {
  pcore := fun _ => some .o
  op := X2.op
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
  pcore_mono := by intro x y cx h1 h2; exact ⟨.o, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.o, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; rfl
  increasing_closed := by intro x y _ h; cases h; assumption }
instance : OrderRefl X2 := ⟨fun x => show x = x from rfl⟩
instance x2UORA : UORA X2 where
  unit := .o
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl
abbrev oI : UPred X2 := UPred.ownM X2.i

-- helper: four-element affine UORA, e unit, all other products z (invalid), extension order:
-- ownM a and ownM b are incomparable; core is constantly e, so plain = persistent
inductive X4 | e | a | b | z deriving DecidableEq
def X4.op : X4 → X4 → X4
  | .e, y => y
  | .a, .e => .a
  | .b, .e => .b
  | _, _ => .z
instance : OFE X4 := OFE.ofDiscrete X4
instance : OFE.Discrete X4 := ⟨id⟩
instance instORAX4 : ORA X4 := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := X4.op
  Valid := fun x => x ≠ .z
  Order := fun x y => x = .e ∨ x = y ∨ y = .z
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y h; cases x <;> cases y <;> simp_all [X4.op]
  ord_trans := by intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all
  op_mono_left := by intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [X4.op]
  valid_of_ord := by intro x y h1 h2; cases x <;> cases y <;> simp_all
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; exact .inl rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; exact .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact .inr (.inl rfl)
  increasing_closed := by intro x y hx h z; cases x <;> cases y <;> cases z <;> simp_all [X4.op] }
instance : OrderRefl X4 := ⟨fun x => show x = .e ∨ x = x ∨ x = .z from .inr (.inl rfl)⟩
instance instUORAX4 : UORA X4 where
  unit := .e
  unit_valid := by show X4.e ≠ X4.z; decide
  unit_left_id := rfl
  pcore_unit := rfl
instance : IncOrd X4 := ⟨by
  intro x y ⟨z, hz⟩
  show x = .e ∨ x = y ∨ y = .z
  cases x <;> cases z <;> simp_all [Op.op, X4.op]⟩
abbrev oA : UPred X4 := UPred.ownM X4.a
abbrev oB : UPred X4 := UPred.ownM X4.b
abbrev vA : ValidAt X4 0 := ⟨.a, by show X4.a ≠ X4.z; decide⟩
abbrev vB : ValidAt X4 0 := ⟨.b, by show X4.b ≠ X4.z; decide⟩
abbrev vE : ValidAt X4 0 := ⟨.e, by show X4.e ≠ X4.z; decide⟩
theorem x4aff : BIAffine (UPred X4) := inferInstance

-- helper: in UPred X4 a prop holding at a but not at e is neither plain nor persistent
theorem x4E {X : UPred X4} (h : X ⊢ UPred.persistently X) (ha : X.holds 0 vA) (he : ¬ X.holds 0 vE) : False :=
  he (h 0 vA ha)
theorem x4P {X : UPred X4} (h : X ⊢ ■ X) (ha : X.holds 0 vA) (he : ¬ X.holds 0 vE) : False :=
  he (h 0 vA ha)
theorem oA_a : oA.holds 0 vA := Or.inr (Or.inl rfl)
theorem oA_e : ¬ oA.holds 0 vE := fun h => by rcases h with h | h | h <;> cases h
-- helper: ownM a is not plain and not persistent in UPred X4
theorem oA_np (h : oA ⊢ ■ oA) : False := x4P h oA_a oA_e
theorem oA_npers (h : oA ⊢ <pers> oA) : False := x4E h oA_a oA_e
-- helper: ownM b → False holds at a, not at e
theorem nb_imp_a : (iprop(oB → False) : UPred X4).holds 0 vA := by
  intro n' x' h1 _ h2
  rcases x' with ⟨x', hv⟩
  have hv' : x' ≠ X4.z := hv
  rcases h1 with h1 | h1 | h1
  · cases h1
  · subst h1; rcases h2 with h2 | h2 | h2 <;> cases h2
  · subst h1; exact absurd rfl hv'
theorem nb_imp_e : ¬ (iprop(oB → False) : UPred X4).holds 0 vE := fun H =>
  H vB (Or.inl rfl) (Nat.le_refl 0) (Or.inr (Or.inl rfl))
-- helper: ownM b -∗ False holds at a, not at e
theorem nb_wand_a : (iprop(oB -∗ False) : UPred X4).holds 0 vA := by
  intro n' x' _ hv h2
  have hv' : X4.op X4.a x' ≠ X4.z := hv
  rcases h2 with h2 | h2 | h2
  · cases h2
  · subst h2; exact absurd rfl hv'
  · subst h2; exact absurd rfl hv'
theorem nb_wand_e : ¬ (iprop(oB -∗ False) : UPred X4).holds 0 vE := fun H =>
  H 0 .b (Nat.le_refl 0) (show X4.b ≠ X4.z by decide) (Or.inr (Or.inl rfl))

-- helper: Bool with the discrete order (copied from Probe4): MonPred DIdx SiProp is an Sbi without SbiEmpValidExist
def DB := Bool
instance : LE DB := ⟨fun a b => a = b⟩
instance : Inhabited DB := ⟨(true : Bool)⟩
instance : Std.IsPreorder DB where
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2
abbrev DIdx : BiIndex := { car := DB, rel := inferInstance }
def phiD (a : Bool) : MonPred DIdx SiProp := ⟨fun i => iprop(⌜(i : Bool) = a⌝), fun hij _ h => hij ▸ h⟩
abbrev iT : DIdx.car := (true : Bool)
abbrev iF : DIdx.car := (false : Bool)

-- helper: ■ P at any index and step means P at every index
theorem dpl {X : MonPred DIdx SiProp} {i : DIdx.car} {n : Nat} (H : (iprop(■ X) : MonPred DIdx SiProp).monPred_at i |>.holds n)
    (j : DIdx.car) : (X.monPred_at j).holds n :=
  SiProp.forall_holds.1 ((MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) i X).mp n H) j
-- helper: a MonPred DIdx SiProp holding at index true but not false (same step) is not plain
theorem dnp {X : MonPred DIdx SiProp} (n : Nat) (h : X ⊢ ■ X) (ht : (X.monPred_at iT).holds n)
    (hf : ¬ (X.monPred_at iF).holds n) : False := hf (dpl (h iT n ht) iF)
theorem phT : ((phiD true).monPred_at iT).holds 0 := rfl
theorem phF : ¬ ((phiD true).monPred_at iF).holds 0 := fun e => Bool.noConfusion e
-- helper: phiD true is not plain; sandwich version
theorem phi_np (h : phiD true ⊢ ■ phiD true) : False := dnp 0 h phT phF
theorem dsand {X : MonPred DIdx SiProp} (h1 : phiD true ⊢ X) (h2 : X ⊢ phiD true) (h : X ⊢ ■ X) : False :=
  phi_np (h1.trans (h.trans (plainly_mono h2)))
-- helper: ■ (phiD true ∨ phiD false) holds, ■ phiD true ∨ ■ phiD false does not
theorem dor (H : (iprop(■ (phiD true ∨ phiD false)) : MonPred DIdx SiProp) ⊢ iprop(■ phiD true ∨ ■ phiD false)) : False := by
  have hl : ((iprop(■ (phiD true ∨ phiD false)) : MonPred DIdx SiProp).monPred_at iT).holds 0 :=
    (MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) iT _).mpr 0
      (SiProp.forall_holds.2 fun j => by
        show (j : Bool) = true ∨ (j : Bool) = false
        exact Bool.eq_false_or_eq_true j)
  rcases H iT 0 hl with h | h
  · exact Bool.noConfusion (dpl h iF : (false : Bool) = true)
  · exact Bool.noConfusion (dpl h iT : (true : Bool) = false)

-- helper: non-affine UORA {e, a, c, z}: e unit, other products z (invalid), order: equality, everything below z,
-- and e below c. emp holds at e and c only; True -∗ emp holds at c (only c • e is valid) but not at e (e • a = a)
inductive EC | e | a | c | z deriving DecidableEq
def EC.op : EC → EC → EC
  | .e, y => y
  | .a, .e => .a
  | .c, .e => .c
  | _, _ => .z
instance : OFE EC := OFE.ofDiscrete EC
instance : OFE.Discrete EC := ⟨id⟩
instance instORAEC : ORA EC := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := EC.op
  Valid := fun x => x ≠ .z
  Order := fun x y => x = y ∨ y = .z ∨ (x = .e ∧ y = .c)
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y h; cases x <;> cases y <;> simp_all [EC.op]
  ord_trans := by intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all
  op_mono_left := by intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [EC.op]
  valid_of_ord := by intro x y h1 h2; cases x <;> cases y <;> simp_all
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; exact .inl rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; exact .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> exact .inl rfl
  increasing_closed := by
    intro x y hx h z
    have h1 := hx .e
    cases x <;> cases y <;> cases z <;> simp_all [EC.op] }
instance : OrderRefl EC := ⟨fun x => show x = x ∨ _ from .inl rfl⟩
instance instUORAEC : UORA EC where
  unit := .e
  unit_valid := by show EC.e ≠ EC.z; decide
  unit_left_id := rfl
  pcore_unit := rfl
abbrev vC : ValidAt EC 0 := ⟨.c, by show EC.c ≠ EC.z; decide⟩
abbrev vEc : ValidAt EC 0 := ⟨.e, by show EC.e ≠ EC.z; decide⟩
theorem ec_c : (iprop(True -∗ emp) : UPred EC).holds 0 vC := by
  intro n' x' _ hv _
  have hv' : EC.op EC.c x' ≠ EC.z := hv
  cases x' <;> first | exact absurd rfl hv' | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
theorem ec_e : ¬ (iprop(True -∗ emp) : UPred EC).holds 0 vEc := fun H => by
  have h := H 0 .a (Nat.le_refl 0) (show EC.a ≠ EC.z by decide) trivial
  rcases h with h | h | ⟨_, h⟩ <;> cases h

-- helper: LawfulFiniteSet ExtTreeSet Nat is countable (via its sorted list)
abbrev TS := Std.ExtTreeSet Nat compare
instance tsCount : Pos.Countable TS where
  encode s := Pos.Countable.encode s.toList
  decode p := (Pos.Countable.decode p).map (fun l : List Nat => Std.ExtTreeSet.ofList l compare)
  decode_encode s := by
    simp only [Pos.Countable.decode_encode, Option.map_some]
    congr 1
    ext k
    simp

-- helper: Bool streams, a non-discrete COFE (copied from W3c1/W4c5), and a chain escaping to the all-false limit
structure CS where s : Nat → Bool
open Iris.OFE in
instance csOFE : OFE CS where
  Dist n x y := ∀ k, k ≤ n → x.s k = y.s k
  dist_eqv := ⟨fun _ _ _ => rfl, fun h k hk => (h k hk).symm, fun h1 h2 k hk => (h1 k hk).trans (h2 k hk)⟩
  eq_dist' {x y} := ⟨fun h n k _ => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      congr; funext k; exact h k k (Nat.le_refl k)⟩
  dist_lt {n x y m} h hm k hk := h k (by omega)
instance csCOFE : IsCOFE CS where
  compl c := ⟨fun k => (c.chain k).s k⟩
  conv_compl {n c} k hk := ((c.cauchy hk) k (Nat.le_refl k)).symm
def cF : CS := ⟨fun _ => false⟩
def escC : Chain CS where
  chain i := ⟨fun k => decide (k = i + 1)⟩
  cauchy {n i} h k hk := by
    show decide (k = i + 1) = decide (k = n + 1)
    have h1 : k ≠ i + 1 := by omega
    have h2 : k ≠ n + 1 := by omega
    simp [h1, h2]
theorem escC_compl : COFE.compl escC = cF := by
  show (⟨fun k => decide (k = k + 1)⟩ : CS) = ⟨fun _ => false⟩
  congr; funext k; simp
def hasT (x : CS) : Prop := ∃ k, x.s k = true
theorem hasT_esc (n : Nat) : hasT (escC n) := ⟨n+1, by simp [escC]⟩
theorem not_hasT_lim : ¬ hasT (COFE.compl escC) := escC_compl ▸ fun ⟨_, h⟩ => nomatch h
end W6c0

namespace W6c0
open Iris Iris.BI Iris.Std
/-- helper: step-indexed predicates over the Bool-or monoid with exact splitting, resource-blind at step 0
(the TP model of W4c1), now with the step-indexed OFE, so that it is an Sbi (with Löb) whose emp is not timeless. -/
structure TQ where
  holds : Nat → Bool → Prop
  mono {n n' : Nat} {m : Bool} : holds n m → n' ≤ n → holds n' m
  irr {m m' : Bool} : holds 0 m → holds 0 m'

theorem TQ.ext' : {P Q : TQ} → (∀ n m, P.holds n m ↔ Q.holds n m) → P = Q
  | ⟨p, _, _⟩, ⟨q, _, _⟩, h => by
    have : p = q := funext fun n => funext fun m => propext (h n m)
    subst this; rfl

def TQ.emp : TQ where
  holds n m := n = 0 ∨ m = false
  mono h hle := by rcases h with h | h; exact .inl (by omega); exact .inr h
  irr _ := .inl rfl
def TQ.pure (φ : Prop) : TQ where
  holds _ _ := φ
  mono h _ := h
  irr h := h
def TQ.and (P Q : TQ) : TQ where
  holds n m := P.holds n m ∧ Q.holds n m
  mono h hle := ⟨P.mono h.1 hle, Q.mono h.2 hle⟩
  irr h := ⟨P.irr h.1, Q.irr h.2⟩
def TQ.or (P Q : TQ) : TQ where
  holds n m := P.holds n m ∨ Q.holds n m
  mono h hle := h.elim (fun h => .inl (P.mono h hle)) (fun h => .inr (Q.mono h hle))
  irr h := h.elim (fun h => .inl (P.irr h)) (fun h => .inr (Q.irr h))
def TQ.imp (P Q : TQ) : TQ where
  holds n m := ∀ n', n' ≤ n → P.holds n' m → Q.holds n' m
  mono h hle n'' h'' hp := h n'' (Nat.le_trans h'' hle) hp
  irr h n' hn' hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) (P.irr hp))
def TQ.sForall (Ψ : TQ → Prop) : TQ where
  holds n m := ∀ p, Ψ p → p.holds n m
  mono h hle p hp := p.mono (h p hp) hle
  irr h p hp := p.irr (h p hp)
def TQ.sExists (Ψ : TQ → Prop) : TQ where
  holds n m := ∃ p, Ψ p ∧ p.holds n m
  mono h hle := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.mono h hle⟩
  irr h := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.irr h⟩
def TQ.sep (P Q : TQ) : TQ where
  holds n m := ∃ a b, m = Bool.or a b ∧ P.holds n a ∧ Q.holds n b
  mono h hle := let ⟨a, b, e, hp, hq⟩ := h; ⟨a, b, e, P.mono hp hle, Q.mono hq hle⟩
  irr {_ m'} h := let ⟨_, _, _, hp, hq⟩ := h; ⟨m', false, by cases m' <;> rfl, P.irr hp, Q.irr hq⟩
def TQ.wand (P Q : TQ) : TQ where
  holds n m := ∀ n', n' ≤ n → ∀ b, P.holds n' b → Q.holds n' (Bool.or m b)
  mono h hle n'' h'' b hp := h n'' (Nat.le_trans h'' hle) b hp
  irr h n' hn' b hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) b hp)
def TQ.pers (P : TQ) : TQ where
  holds n _ := P.holds n false
  mono h hle := P.mono h hle
  irr h := h
def TQ.later (P : TQ) : TQ where
  holds n m := match n with | 0 => True | k+1 => P.holds k m
  mono {n n' m} h hle := by
    cases n' with
    | zero => trivial
    | succ k' => cases n with
      | zero => omega
      | succ k => exact P.mono h (by omega)
  irr _ := trivial

instance : BIBase TQ where
  Entails P Q := ∀ n m, P.holds n m → Q.holds n m
  emp := TQ.emp
  pure := TQ.pure
  and := TQ.and
  or := TQ.or
  imp := TQ.imp
  sForall := TQ.sForall
  sExists := TQ.sExists
  sep := TQ.sep
  wand := TQ.wand
  persistently := TQ.pers
  later := TQ.later

instance tqOFE : OFE TQ where
  Dist n P Q := ∀ k, k ≤ n → ∀ m, (P.holds k m ↔ Q.holds k m)
  dist_eqv := ⟨fun _ _ _ _ => Iff.rfl, fun h k hk m => (h k hk m).symm,
    fun h1 h2 k hk m => (h1 k hk m).trans (h2 k hk m)⟩
  eq_dist' {x y} := ⟨fun h n k _ m => h ▸ Iff.rfl, fun h => TQ.ext' fun n m => h n n (Nat.le_refl n) m⟩
  dist_lt {n x y m} h hm k hk := h k (by omega)
instance tqCOFE : IsCOFE TQ where
  compl c := ⟨fun n m => (c.chain n).holds n m,
    fun {n n' m} h hle => ((c.cauchy hle) n' (Nat.le_refl n') m).1 ((c.chain n).mono h hle),
    fun h => (c.chain 0).irr h⟩
  conv_compl {n c} k hk m := ((c.cauchy hk) k (Nat.le_refl k) m).symm

instance tqBI : BI TQ where
  entails_refl _ _ h := h
  entails_trans h1 h2 n m h := h2 n m (h1 n m h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ _ h => h, fun _ _ h => h⟩,
    fun ⟨h1, h2⟩ => TQ.ext' fun n m => ⟨h1 n m, h2 n m⟩⟩
  and_ne := ⟨by intro n P P' hP Q Q' hQ k hk m; exact and_congr (hP k hk m) (hQ k hk m)⟩
  or_ne := ⟨by intro n P P' hP Q Q' hQ k hk m; exact or_congr (hP k hk m) (hQ k hk m)⟩
  imp_ne := ⟨by
    intro n P P' hP Q Q' hQ k hk m
    exact ⟨fun h n' hn' hp => (hQ n' (by omega) m).1 (h n' hn' ((hP n' (by omega) m).2 hp)),
      fun h n' hn' hp => (hQ n' (by omega) m).2 (h n' hn' ((hP n' (by omega) m).1 hp))⟩⟩
  sep_ne := ⟨by
    intro n P P' hP Q Q' hQ k hk m
    exact ⟨fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, (hP k hk a).1 hp, (hQ k hk b).1 hq⟩,
      fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, (hP k hk a).2 hp, (hQ k hk b).2 hq⟩⟩⟩
  wand_ne := ⟨by
    intro n P P' hP Q Q' hQ k hk m
    exact ⟨fun h n' hn' b hp => (hQ n' (by omega) _).1 (h n' hn' b ((hP n' (by omega) b).2 hp)),
      fun h n' hn' b hp => (hQ n' (by omega) _).2 (h n' hn' b ((hP n' (by omega) b).1 hp))⟩⟩
  persistently_ne := ⟨by intro n P P' hP k hk m; exact hP k hk false⟩
  later_ne := ⟨by
    intro n P P' hP k hk m
    cases k with
    | zero => exact Iff.rfl
    | succ j => exact hP j (by omega) m⟩
  sForall_ne {n P₁ P₂} h k hk m :=
    ⟨fun H q hq => let ⟨p, hp, d⟩ := h.2 q hq; (d k hk m).1 (H p hp),
     fun H p hp => let ⟨q, hq, d⟩ := h.1 p hp; (d k hk m).2 (H q hq)⟩
  sExists_ne {n P₁ P₂} h k hk m :=
    ⟨fun ⟨p, hp, H⟩ => let ⟨q, hq, d⟩ := h.1 p hp; ⟨q, hq, (d k hk m).1 H⟩,
     fun ⟨q, hq, H⟩ => let ⟨p, hp, d⟩ := h.2 q hq; ⟨p, hp, (d k hk m).2 H⟩⟩
  pure_intro h _ _ _ := h
  pure_elim' h n m hφ := h hφ n m trivial
  and_elim_l _ _ h := h.1
  and_elim_r _ _ h := h.2
  and_intro h1 h2 n m h := ⟨h1 n m h, h2 n m h⟩
  or_intro_l _ _ h := .inl h
  or_intro_r _ _ h := .inr h
  or_elim h1 h2 n m h := h.elim (h1 n m) (h2 n m)
  imp_intro {P _ _} h n m hp n' hle hq := h n' m ⟨P.mono hp hle, hq⟩
  imp_elim h n m hpq := h n m hpq.1 n (Nat.le_refl n) hpq.2
  sForall_intro h n m hp p hΨ := h p hΨ n m hp
  sForall_elim hΨ n m h := h _ hΨ
  sExists_intro hΨ n m h := ⟨_, hΨ, h⟩
  sExists_elim h n m := fun ⟨p, hp, hh⟩ => h p hp n m hh
  sep_mono h1 h2 n m := fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, h1 n a hp, h2 n b hq⟩
  emp_sep {P} := ⟨fun n m ⟨a, b, e, he, hp⟩ => by
      rcases he with he | he
      · subst he; exact P.irr hp
      · subst he; cases b <;> (subst e; exact hp),
    fun n m hp => ⟨false, m, by cases m <;> rfl, .inr rfl, hp⟩⟩
  sep_symm n m := fun ⟨a, b, e, hp, hq⟩ => ⟨b, a, by rw [e, Bool.or_comm], hq, hp⟩
  sep_assoc_l n m := fun ⟨_, c, e, ⟨a, b, e', hp, hq⟩, hr⟩ =>
    ⟨a, Bool.or b c, by rw [e, e', Bool.or_assoc], hp, b, c, rfl, hq, hr⟩
  wand_intro {P _ _} h n m hp n' hle b hq := h n' (Bool.or m b) ⟨m, b, rfl, P.mono hp hle, hq⟩
  wand_elim h n m := fun ⟨a, b, e, hp, hq⟩ => e ▸ h n a hp n (Nat.le_refl n) b hq
  persistently_mono h n _ hp := h n false hp
  persistently_idem_2 _ _ h := h
  persistently_emp_2 _ _ _ := .inr rfl
  persistently_and_2 _ _ h := h
  persistently_absorb_l n m := fun ⟨_, _, _, hp, _⟩ => hp
  persistently_and_l n m := fun ⟨hp, hq⟩ => ⟨false, m, by cases m <;> rfl, hp, hq⟩
  later_mono h n m hp := by
    cases n with
    | zero => trivial
    | succ k => exact h k m hp
  later_intro {P} n m hp := by
    cases n with
    | zero => trivial
    | succ k => exact P.mono hp (Nat.le_succ k)
  later_sForall_2 n m h := by
    cases n with
    | zero => trivial
    | succ k => exact fun p hp => h _ ⟨p, rfl⟩ (k+1) (Nat.le_refl _) hp
  later_sExists_false n m h := by
    cases n with
    | zero => exact .inl trivial
    | succ k =>
      obtain ⟨p, hp, hh⟩ := h
      exact .inr ⟨_, ⟨p, rfl⟩, hp, hh⟩
  later_sep := ⟨fun n m h => by
      cases n with
      | zero => exact ⟨m, false, by cases m <;> rfl, trivial, trivial⟩
      | succ k => exact h,
    fun n m h => by
      cases n with
      | zero => trivial
      | succ k => exact h⟩
  later_persistently := ⟨fun n m h => by cases n <;> exact h, fun n m h => by cases n <;> exact h⟩
  later_false_em {P} n m h := by
    cases n with
    | zero => exact .inl trivial
    | succ k =>
      refine .inr fun n' hle hf => ?_
      cases n' with
      | zero => exact P.mono h (Nat.zero_le _)
      | succ j => exact hf.elim

instance : SiPure TQ := ⟨fun Pi => ⟨fun n _ => Pi.holds n, fun h hle => Pi.closed h hle, fun h => h⟩⟩
instance : SiEmpValid TQ := ⟨fun P => ⟨fun n => P.holds n false, fun h hle => P.mono h hle⟩⟩

instance tqSbi : Sbi TQ where
  siPure_ne := ⟨by intro n Pi Qi h k hk m; exact h hk⟩
  siEmpValid_ne := ⟨by intro n P Q h k hk; exact h k hk false⟩
  siPure_mono h n _ hp := h n hp
  siEmpValid_mono h n hp := h n false hp
  siEmpValid_siPure := ⟨fun _ h => h, fun _ h => h⟩
  siPure_siEmpValid _ _ h := h
  siPure_imp_mpr _ _ h := h
  siPure_sForall_mpr n m h P hP := h _ ⟨P, rfl⟩ n (Nat.le_refl n) hP
  persistently_imp_siPure _ _ h := h
  siPure_later := ⟨fun n m h => by cases n <;> exact h, fun n m h => by cases n <;> exact h⟩
  siPure_absorbing Pi := ⟨fun n m ⟨_, _, _, _, hp⟩ => hp⟩
  siEmpValid_later_mp n h := by cases n <;> exact h
  siEmpValid_affinely_mpr n h := ⟨.inr rfl, h⟩
  prop_ext_siEmpValid n h k hk m := ⟨fun hp => h.1 k hk m hp, fun hq => h.2 k hk m hq⟩
end W6c0

open Iris Iris.BI Iris.Std Iris.Algebra W6c0

-- `Iris.BI.plainly_elim` idx 3: necessary (non-affine UPred NA, P = emp: ■ emp holds everywhere, emp fails at a)
theorem w6c0_1 : ¬ drop0% Iris.BI.plainly_elim 3 :=
  fun h => na_true_not_emp (plainly_emp_intro.trans (@h (UPred NA) _ iprop(emp)))

-- `Iris.BI.plainly_intro_plainly` idx 4: necessary (SiProp, P = True, Q = False)
theorem w6c0_2 : ¬ drop0% Iris.BI.plainly_intro_plainly 4 :=
  fun h => (@h SiProp _ iprop(True) iprop(False)) 0 trivial

-- `Iris.BI.plainly_or` idx 4: necessary (MonPred over discrete Bool index into SiProp (no SbiEmpValidExist), P = phiD true, Q = phiD false)
theorem w6c0_3 : ¬ drop0% Iris.BI.plainly_or 4 :=
  fun h => dor (@h (MonPred DIdx SiProp) _ (phiD true) (phiD false)).1

-- `Iris.BI.plainly_sep` idx 4: necessary (non-positive UPred X2 (xor), P = Q = ownM i: ■ (P ∗ Q) holds at the unit, ■ P does not)
theorem w6c0_4 : ¬ drop0% Iris.BI.plainly_sep 4 :=
  fun h => by
    have H := (@h (UPred X2) _ oI oI).1 0 ⟨.o, trivial⟩ ⟨.i, .i, rfl, rfl, rfl⟩
    obtain ⟨_, _, _, h1, _⟩ := H
    cases h1

-- `Iris.BI.plainly_entails_left` idx 4: necessary (SiProp, P = True, Q = False)
theorem w6c0_5 : ¬ drop0% Iris.BI.plainly_entails_left 4 :=
  fun h => ((@h SiProp _ iprop(True) iprop(False)) 0 trivial).1

-- `Iris.BI.plainly_entails_right` idx 4: necessary (SiProp, P = True, Q = False)
theorem w6c0_6 : ¬ drop0% Iris.BI.plainly_entails_right 4 :=
  fun h => ((@h SiProp _ iprop(True) iprop(False)) 0 trivial).2

-- `Iris.BI.plainly_emp` idx 2: necessary (non-affine UPred NA: ■ emp holds everywhere, emp fails at a)
theorem w6c0_7 : ¬ drop0% Iris.BI.plainly_emp 2 :=
  fun h => na_true_not_emp (plainly_emp_intro.trans (@h (UPred NA) _).1)

-- `Iris.BI.plainly_and_sep_left` idx 4: necessary (non-affine UPred NA, P = Q = emp: ■ emp ∗ emp ⊣⊢ True but ■ emp ∧ emp ⊢ emp)
theorem w6c0_8 : ¬ drop0% Iris.BI.plainly_and_sep_left 4 :=
  fun h => na_true_not_emp ((sep_emp.2.trans (sep_mono_left plainly_emp_intro)).trans
    ((@h (UPred NA) _ iprop(emp) iprop(emp)).2.trans and_elim_r))

-- `Iris.BI.plainly_and_sep_right` idx 4: necessary (non-affine UPred NA, P = Q = emp)
theorem w6c0_9 : ¬ drop0% Iris.BI.plainly_and_sep_right 4 :=
  fun h => na_true_not_emp ((emp_sep.2.trans (sep_mono_right plainly_emp_intro)).trans
    ((@h (UPred NA) _ iprop(emp) iprop(emp)).2.trans and_elim_l))

-- `Iris.BI.plainly_impl_wand` idx 4: necessary (non-affine UPred NA, P = True, Q = emp: ■ (True → emp) holds, ■ (True -∗ emp) would give True ⊢ emp)
theorem w6c0_10 : ¬ drop0% Iris.BI.plainly_impl_wand 4 :=
  fun h => na_true_not_emp <|
    ((and_intro (plainly_emp_intro.trans ((plainly_mono (BI.imp_intro and_elim_l)).trans
      (@h (UPred NA) _ iprop(True) iprop(emp)).1)) .rfl).trans plainly_and_sep_elim).trans
      ((sep_mono_left and_elim_r).trans wand_elim_left)

-- `Iris.BI.impl_wand_plainly` idx 4: necessary (non-affine UPred NA, P = Q = emp: ■ emp → emp holds at emp, ■ emp -∗ emp would give True ⊢ emp)
theorem w6c0_11 : ¬ drop0% Iris.BI.impl_wand_plainly 4 :=
  fun h => na_true_not_emp <| plainly_emp_intro.trans <| emp_sep.2.trans <|
    (sep_mono_left ((BI.imp_intro and_elim_l).trans (@h (UPred NA) _ iprop(emp) iprop(emp)).1)).trans wand_elim_left

-- `Iris.BI.plainly_if_or` idx 5: necessary (p = true, MonPred DIdx SiProp, P = phiD true, Q = phiD false)
theorem w6c0_12 : ¬ drop0% Iris.BI.plainly_if_or 5 :=
  fun h => dor (@h (MonPred DIdx SiProp) _ (phiD true) (phiD false) true).1

-- `Iris.BI.plainly_if_absorbing` idx 3: necessary (p = false, non-affine UPred NA, P = emp)
theorem w6c0_13 : ¬ drop0% Iris.BI.plainly_if_absorbing 3 :=
  fun h => na_true_not_emp (sep_emp.2.trans (@h (UPred NA) _ iprop(emp) false).absorbing)

-- `Iris.BI.plain_plainly_2` idx 3: necessary (affine UPred X4, P = ownM a)
theorem w6c0_14 : ¬ drop0% Iris.BI.plain_plainly_2 3 :=
  fun h => oA_np (@h (UPred X4) _ oA)

-- `Iris.BI.plain_plainly` idx 3: necessary (affine UPred X4, P = ownM a (absorbing))
theorem w6c0_15 : ¬ drop0% Iris.BI.plain_plainly 3 :=
  fun h => oA_np (@h (UPred X4) _ oA _).2

-- `Iris.BI.plain_plainly` idx 4: necessary (non-affine UPred NA, P = emp (plain, not absorbing))
theorem w6c0_16 : ¬ drop0% Iris.BI.plain_plainly 4 :=
  fun h => na_true_not_emp (plainly_emp_intro.trans (@h (UPred NA) _ iprop(emp) _).1)

-- `Iris.BI.plainly_intro` idx 4: necessary (affine UPred X4, P = Q = ownM a)
theorem w6c0_17 : ¬ drop0% Iris.BI.plainly_intro 4 :=
  fun h => oA_np (@h (UPred X4) _ oA oA .rfl)

-- `Iris.BI.plainly_intro` idx 5: necessary (SiProp, P = True (plain), Q = False)
theorem w6c0_18 : ¬ drop0% Iris.BI.plainly_intro 5 :=
  fun h => (@h SiProp _ iprop(True) iprop(False) _) 0 trivial

-- `Iris.BI.plain_persistent` idx 3: necessary (affine UPred X4, P = ownM a (core constantly e))
theorem w6c0_19 : ¬ drop0% Iris.BI.plain_persistent 3 :=
  fun h => oA_npers (@h (UPred X4) _ oA).persistent

-- `Iris.BI.impl_persistent` idx 4: necessary (non-affine UPred NA, P = emp (plain, not absorbing), Q = False: emp → False holds at a, not at e)
theorem w6c0_20 : ¬ drop0% Iris.BI.impl_persistent 4 :=
  fun h => naE (@h (UPred NA) _ iprop(emp) iprop(False) _ _).persistent
    (fun x' h1 _ h2 => by rcases x' with ⟨x', _⟩; cases h1; cases h2) (fun H => H ⟨.e, trivial⟩ rfl (Nat.le_refl 0) rfl)

-- `Iris.BI.impl_persistent` idx 5: necessary (affine UPred X4, P = ownM b (not plain), Q = False: ownM b → False holds at a, not at e)
theorem w6c0_21 : ¬ drop0% Iris.BI.impl_persistent 5 :=
  fun h => x4E (@h (UPred X4) _ oB iprop(False) _ _).persistent nb_imp_a nb_imp_e

-- `Iris.BI.impl_persistent` idx 6: necessary (affine UPred X4, P = True, Q = ownM a: True → ownM a holds at a, not at e)
theorem w6c0_22 : ¬ drop0% Iris.BI.impl_persistent 6 :=
  fun h => x4E (@h (UPred X4) _ iprop(True) oA _ _).persistent (fun x' h1 _ _ => h1)
    (fun H => oA_e (H vE (Or.inl rfl) (Nat.le_refl 0) trivial))

-- `Iris.BI.wand_persistent` idx 4: necessary (affine UPred X4, P = ownM b (not plain), Q = False: ownM b -∗ False holds at a, not at e)
theorem w6c0_23 : ¬ drop0% Iris.BI.wand_persistent 4 :=
  fun h => x4E (@h (UPred X4) _ oB iprop(False) _ _).persistent nb_wand_a nb_wand_e

-- `Iris.BI.wand_persistent` idx 5: necessary (affine UPred X4, P = emp, Q = ownM a: emp -∗ ownM a ⊣⊢ ownM a is not persistent)
theorem w6c0_24 : ¬ drop0% Iris.BI.wand_persistent 5 :=
  fun h => oA_npers ((wand_intro sep_emp.1).trans ((@h (UPred X4) _ iprop(emp) oA _ _).persistent.trans
    (persistently_mono (sep_emp.2.trans wand_elim_left))))

-- `Iris.BI.plainly_or_weak_homomorphism` idx 2: necessary (MonPred DIdx SiProp (no SbiEmpValidExist): map_op at phiD true, phiD false fails)
theorem w6c0_25 : ¬ drop0% Iris.BI.plainly_or_weak_homomorphism 2 :=
  fun h => dor ((@h (MonPred DIdx SiProp) _).map_op (x := phiD true) (y := phiD false)).1

-- `Iris.BI.plainly_or_homomorphism` idx 2: necessary (MonPred DIdx SiProp (no SbiEmpValidExist): map_op at phiD true, phiD false fails)
theorem w6c0_26 : ¬ drop0% Iris.BI.plainly_or_homomorphism 2 :=
  fun h => dor ((@h (MonPred DIdx SiProp) _).map_op (x := phiD true) (y := phiD false)).1

-- `Iris.BI.bigOrL_plainly` idx 2: necessary (MonPred DIdx SiProp (no SbiEmpValidExist), list [true, false], Φ _ b = phiD b)
theorem w6c0_27 : ¬ drop0% Iris.BI.bigOrL_plainly 2 :=
  fun h => by
    have H := (@h (MonPred DIdx SiProp) _ Bool (fun _ b => phiD b) [true, false]).1
    have hl : ((iprop(■ ([∨list] k ↦ x ∈ [true, false], (fun _ b => phiD b) k x)) : MonPred DIdx SiProp).monPred_at iT).holds 0 :=
      (MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) iT _).mpr 0
        (SiProp.forall_holds.2 fun j => by
          show (j : Bool) = true ∨ ((j : Bool) = false ∨ False)
          rcases Bool.eq_false_or_eq_true j with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e))
    rcases H iT 0 hl with h | h | h
    · exact Bool.noConfusion (dpl h iF : (false : Bool) = true)
    · exact Bool.noConfusion (dpl h iT : (true : Bool) = false)
    · exact h

-- `Iris.BI.bigSepM_plainly` idx 4: necessary (non-affine UPred NA, empty map: ■ emp ⊢ emp fails)
theorem w6c0_28 : ¬ drop0% Iris.BI.bigSepM_plainly 4 :=
  fun h => na_true_not_emp (plainly_emp_intro.trans ((plainly_mono BigSepM.bigSepM_empty.2).trans
    (((@h (UPred NA) _ TM Nat _ Unit (fun _ _ => iprop(emp)) ∅).1).trans BigSepM.bigSepM_empty.1)))

-- `Iris.BI.bigSepM2_plainly` idx 4: necessary (non-affine UPred NA, empty maps: ■ emp ⊢ emp fails)
theorem w6c0_29 : ¬ drop0% Iris.BI.bigSepM2_plainly 4 :=
  fun h => na_true_not_emp (plainly_emp_intro.trans ((plainly_mono (BigSepM2.bigSepM2_empty _).2).trans
    (((@h (UPred NA) _ TM Nat _ Unit Unit (fun _ _ _ => iprop(emp)) ∅ ∅).1).trans (BigSepM2.bigSepM2_empty _).1)))

-- `Iris.BI.bigSepS_plainly` idx 4: necessary (non-affine UPred NA, empty set: ■ emp ⊢ emp fails)
theorem w6c0_30 : ¬ drop0% Iris.BI.bigSepS_plainly 4 :=
  fun h => na_true_not_emp (plainly_emp_intro.trans ((plainly_mono BigSepS.bigSepS_empty.2).trans
    (((@h (UPred NA) _ (Std.ExtTreeSet Nat compare) Nat _ (fun _ => iprop(emp)) ∅).1).trans BigSepS.bigSepS_empty.1)))

-- `Iris.BI.bigSepMS_plainly` idx 4: necessary (non-affine UPred NA, empty multiset: ■ emp ⊢ emp fails)
theorem w6c0_31 : ¬ drop0% Iris.BI.bigSepMS_plainly 4 :=
  fun h => na_true_not_emp (plainly_emp_intro.trans ((plainly_mono BigSepMS.bigSepMS_empty.2).trans
    (((@h (UPred NA) _ (ListPerm Nat) Nat _ (fun _ => iprop(emp)) ∅).1).trans BigSepMS.bigSepMS_empty.1)))

-- `Iris.BI.and_plain` idx 4: necessary (MonPred DIdx SiProp, P = phiD true (persistent, not plain), Q = True)
theorem w6c0_32 : ¬ drop0% Iris.BI.and_plain 4 :=
  fun h => dsand (and_intro .rfl true_intro) and_elim_l (@h (MonPred DIdx SiProp) _ (phiD true) iprop(True) _).plain

-- `Iris.BI.or_plain` idx 4: necessary (MonPred DIdx SiProp, P = phiD true, Q = False)
theorem w6c0_33 : ¬ drop0% Iris.BI.or_plain 4 :=
  fun h => dsand or_intro_l (or_elim .rfl false_elim) (@h (MonPred DIdx SiProp) _ (phiD true) iprop(False) _).plain

-- `Iris.BI.or_plain` idx 5: necessary (MonPred DIdx SiProp, P = False, Q = phiD true)
theorem w6c0_34 : ¬ drop0% Iris.BI.or_plain 5 :=
  fun h => dsand or_intro_r (or_elim false_elim .rfl) (@h (MonPred DIdx SiProp) _ iprop(False) (phiD true) _).plain

-- `Iris.BI.forall_plain` idx 4: necessary (MonPred DIdx SiProp, A = True, Ψ _ = phiD true)
theorem w6c0_35 : ¬ drop0% Iris.BI.forall_plain 4 :=
  fun h => dsand (forall_intro fun _ => .rfl) (forall_elim trivial) (@h (MonPred DIdx SiProp) _ True (fun _ => phiD true)).plain

-- `Iris.BI.impl_plain` idx 4: necessary (non-affine UPred NA, P = emp (plain, not absorbing), Q = False: emp → False holds at a, not at e)
theorem w6c0_36 : ¬ drop0% Iris.BI.impl_plain 4 :=
  fun h => naP (@h (UPred NA) _ iprop(emp) iprop(False) _ _).plain ne_a ne_e

-- `Iris.BI.impl_plain` idx 5: necessary (affine UPred X4, P = ownM b, Q = False: ownM b → False holds at a, not at e)
theorem w6c0_37 : ¬ drop0% Iris.BI.impl_plain 5 :=
  fun h => x4P (@h (UPred X4) _ oB iprop(False) _ _).plain nb_imp_a nb_imp_e

-- `Iris.BI.impl_plain` idx 6: necessary (MonPred DIdx SiProp, P = True, Q = phiD true)
theorem w6c0_38 : ¬ drop0% Iris.BI.impl_plain 6 :=
  fun h => dsand (BI.imp_intro and_elim_l) ((and_intro .rfl true_intro).trans (imp_elim .rfl))
    (@h (MonPred DIdx SiProp) _ iprop(True) (phiD true) _ _).plain

-- `Iris.BI.wand_plain` idx 5: necessary (affine UPred X4, P = ownM b, Q = False: ownM b -∗ False holds at a, not at e)
theorem w6c0_39 : ¬ drop0% Iris.BI.wand_plain 5 :=
  fun h => x4P (@h (UPred X4) _ oB iprop(False) _ _).plain nb_wand_a nb_wand_e

-- `Iris.BI.wand_plain` idx 6: necessary (MonPred DIdx SiProp, P = emp, Q = phiD true)
theorem w6c0_40 : ¬ drop0% Iris.BI.wand_plain 6 :=
  fun h => dsand (wand_intro sep_emp.1) (sep_emp.2.trans wand_elim_left)
    (@h (MonPred DIdx SiProp) _ iprop(emp) (phiD true) _ _).plain

-- `Iris.BI.sep_plain` idx 4: necessary (MonPred DIdx SiProp, P = phiD true, Q = emp)
theorem w6c0_41 : ¬ drop0% Iris.BI.sep_plain 4 :=
  fun h => dsand sep_emp.2 sep_emp.1 (@h (MonPred DIdx SiProp) _ (phiD true) iprop(emp) _).plain

-- `Iris.BI.sep_plain` idx 5: necessary (MonPred DIdx SiProp, P = emp, Q = phiD true)
theorem w6c0_42 : ¬ drop0% Iris.BI.sep_plain 5 :=
  fun h => dsand emp_sep.2 emp_sep.1 (@h (MonPred DIdx SiProp) _ iprop(emp) (phiD true) _).plain

-- `Iris.BI.persistently_plain` idx 3: necessary (MonPred DIdx SiProp, P = phiD true: <pers> is pointwise, ■ quantifies over indices)
theorem w6c0_43 : ¬ drop0% Iris.BI.persistently_plain 3 :=
  fun h => dnp 0 (@h (MonPred DIdx SiProp) _ (phiD true)).plain phT phF

-- `Iris.BI.affinely_plain` idx 3: necessary (MonPred DIdx SiProp, P = phiD true)
theorem w6c0_44 : ¬ drop0% Iris.BI.affinely_plain 3 :=
  fun h => dnp 0 (@h (MonPred DIdx SiProp) _ (phiD true)).plain ⟨trivial, phT⟩ (fun e => phF e.2)

-- `Iris.BI.intuitionistically_plain` idx 3: necessary (MonPred DIdx SiProp, P = phiD true)
theorem w6c0_45 : ¬ drop0% Iris.BI.intuitionistically_plain 3 :=
  fun h => dnp 0 (@h (MonPred DIdx SiProp) _ (phiD true)).plain ⟨trivial, phT⟩ (fun e => phF e.2)

-- `Iris.BI.absorbingly_plain` idx 3: necessary (MonPred DIdx SiProp, P = phiD true)
theorem w6c0_46 : ¬ drop0% Iris.BI.absorbingly_plain 3 :=
  fun h => dnp 0 (@h (MonPred DIdx SiProp) _ (phiD true)).plain ⟨trivial, phT⟩ (fun e => phF e.2)

-- `Iris.BI.from_option_plain` idx 7: necessary (MonPred DIdx SiProp, x? = none, P = phiD true, Ψ _ = True)
theorem w6c0_47 : ¬ drop0% Iris.BI.from_option_plain 7 :=
  fun h => dnp 0 (@h (MonPred DIdx SiProp) _ Unit (phiD true) (fun _ => iprop(True)) none _).plain phT phF

-- `Iris.BI.from_option_plain` idx 6: necessary (MonPred DIdx SiProp, x? = some (), P = True, Ψ _ = phiD true)
theorem w6c0_48 : ¬ drop0% Iris.BI.from_option_plain 6 :=
  fun h => dnp 0 (@h (MonPred DIdx SiProp) _ Unit iprop(True) (fun _ => phiD true) (some ()) _).plain phT phF

-- `Iris.BI.bigSepL_plain` idx 5: necessary (MonPred DIdx SiProp, l = [()], Φ _ _ = phiD true)
theorem w6c0_49 : ¬ drop0% Iris.BI.bigSepL_plain 5 :=
  fun h => dsand (BigSepL.bigSepL_singleton (Φ := fun _ _ => phiD true) (x := ())).2 (BigSepL.bigSepL_singleton (Φ := fun _ _ => phiD true) (x := ())).1
    (@h (MonPred DIdx SiProp) _ Unit (fun _ _ => phiD true) [()]).plain

-- `Iris.BI.bigAndL_plain` idx 5: necessary (MonPred DIdx SiProp, l = [()], Φ _ _ = phiD true)
theorem w6c0_50 : ¬ drop0% Iris.BI.bigAndL_plain 5 :=
  fun h => dsand (BigAndL.bigAndL_singleton (Φ := fun _ _ => phiD true) (x := ())).2 (BigAndL.bigAndL_singleton (Φ := fun _ _ => phiD true) (x := ())).1
    (@h (MonPred DIdx SiProp) _ Unit (fun _ _ => phiD true) [()]).plain

-- `Iris.BI.bigOrL_plain` idx 5: necessary (MonPred DIdx SiProp, l = [()], Φ _ _ = phiD true)
theorem w6c0_51 : ¬ drop0% Iris.BI.bigOrL_plain 5 :=
  fun h => dsand (BigOrL.bigOrL_singleton (Φ := fun _ _ => phiD true) (x := ())).2 (BigOrL.bigOrL_singleton (Φ := fun _ _ => phiD true) (x := ())).1
    (@h (MonPred DIdx SiProp) _ Unit (fun _ _ => phiD true) [()]).plain

-- `Iris.BI.bigSepL2_plain` idx 7: necessary (MonPred DIdx SiProp, l1 = l2 = [()], Φ _ _ _ = phiD true)
theorem w6c0_52 : ¬ drop0% Iris.BI.bigSepL2_plain 7 :=
  fun h => dsand (BigSepL2.bigSepL2_singleton (Φ := fun _ _ _ => phiD true) (x := ()) (y := ())).2 (BigSepL2.bigSepL2_singleton (Φ := fun _ _ _ => phiD true) (x := ()) (y := ())).1
    (@h (MonPred DIdx SiProp) _ Unit Unit (fun _ _ _ => phiD true) [()] [()]).plain

-- `Iris.BI.bigSepM_plain` idx 9: necessary (MonPred DIdx SiProp, one-key map {0 ↦ ()}, Φ _ _ = phiD true)
theorem w6c0_53 : ¬ drop0% Iris.BI.bigSepM_plain 9 :=
  fun h => dsand (BigSepM.bigSepM_singleton (M := TM) (Φ := fun _ _ => phiD true) (i := 0) (x := ())).2
    (BigSepM.bigSepM_singleton (M := TM) (Φ := fun _ _ => phiD true) (i := 0) (x := ())).1
    (@h (MonPred DIdx SiProp) _ Nat _ TM Unit _ (fun _ _ => phiD true) (PartialMap.singleton 0 () : TM Unit)).plain

-- `Iris.BI.bigSepM2_plain` idx 11: necessary (MonPred DIdx SiProp, one-key maps {0 ↦ ()}, Φ _ _ _ = phiD true)
theorem w6c0_54 : ¬ drop0% Iris.BI.bigSepM2_plain 11 :=
  fun h => dsand (BigSepM2.bigSepM2_singleton (M := TM) (fun _ _ _ => phiD true) 0 () ()).2
    (BigSepM2.bigSepM2_singleton (M := TM) (fun _ _ _ => phiD true) 0 () ()).1
    (@h (MonPred DIdx SiProp) _ Nat _ TM Unit Unit _ (fun _ _ _ => phiD true) (PartialMap.singleton 0 () : TM Unit) (PartialMap.singleton 0 () : TM Unit)).plain

-- `Iris.BI.bigSepMS_plain` idx 7: necessary (MonPred DIdx SiProp, multiset {0} in ListPerm Nat, Φ _ = phiD true)
theorem w6c0_55 : ¬ drop0% Iris.BI.bigSepMS_plain 7 :=
  fun h => dsand (BigSepMS.bigSepMS_singleton (MS := ListPerm Nat) (Φ := fun _ => phiD true) (x := 0)).2
    (BigSepMS.bigSepMS_singleton (MS := ListPerm Nat) (Φ := fun _ => phiD true) (x := 0)).1
    (@h (MonPred DIdx SiProp) _ (ListPerm Nat) Nat _ (fun _ => phiD true) {0}).plain

-- `Iris.BI.plainly_timeless` idx 3: necessary (SiProp, P = s0 (true only at step 0))
theorem w6c0_56 : ¬ drop0% Iris.BI.plainly_timeless 3 :=
  fun h => nt (Q := s0) (@h SiProp _ s0).timeless rfl Nat.one_ne_zero

-- `Iris.BI.plainly_alt_absorbing` idx 3: necessary (non-affine UPred NA, P = emp: ■ emp holds at a, emp ≡ True does not)
theorem w6c0_57 : ¬ drop0% Iris.BI.plainly_alt_absorbing 3 :=
  fun h => by
    have H := ((@h (UPred NA) _ iprop(emp)).1 0 ⟨.a, trivial⟩ rfl) 0 .a (Nat.le_refl 0) trivial
    cases H.2 trivial

-- `Iris.BI.internalEq_timeless` idx 4: necessary (SiProp, P = s0, Q = True: s0 ≡ True holds at step 0, not at 1)
theorem w6c0_58 : ¬ drop0% Iris.BI.internalEq_timeless 4 :=
  fun h => nt (Q := iprop(s0 ≡ iprop(True))) (@h SiProp _ s0 iprop(True) _).timeless
    (fun {m} hm => ⟨fun _ => trivial, fun _ => Nat.le_zero.mp hm⟩) (fun d => Nat.one_ne_zero ((d (Nat.le_refl 1)).2 trivial))

-- `Iris.BI.internalEq_timeless` idx 5: necessary (SiProp, P = True, Q = s0)
theorem w6c0_59 : ¬ drop0% Iris.BI.internalEq_timeless 5 :=
  fun h => nt (Q := iprop(iprop(True) ≡ s0)) (@h SiProp _ iprop(True) s0 _).timeless
    (fun {m} hm => ⟨fun _ => Nat.le_zero.mp hm, fun _ => trivial⟩) (fun d => Nat.one_ne_zero ((d (Nat.le_refl 1)).1 trivial))

-- `Iris.BI.later_plain` idx 3: necessary (MonPred DIdx SiProp, P = phiD true, at step 1)
theorem w6c0_60 : ¬ drop0% Iris.BI.later_plain 3 :=
  fun h => dnp 1 (@h (MonPred DIdx SiProp) _ (phiD true)).plain phT phF

-- `Iris.BI.laterN_plain` idx 4: necessary (MonPred DIdx SiProp, n = 1, P = phiD true, at step 1)
theorem w6c0_61 : ¬ drop0% Iris.BI.laterN_plain 4 :=
  fun h => dnp 1 (@h (MonPred DIdx SiProp) _ 1 (phiD true)).plain phT phF

-- `Iris.BI.except0_plain` idx 3: necessary (MonPred DIdx SiProp, P = phiD true, at step 1)
theorem w6c0_62 : ¬ drop0% Iris.BI.except0_plain 3 :=
  fun h => dnp 1 (@h (MonPred DIdx SiProp) _ (phiD true)).plain (Or.inr phT) (fun e => e.elim id phF)

-- `Iris.SiProp.closed` idx 4: necessary (s0 (true only at step 0), n₁ = 0, n₂ = 1)
theorem w6c0_63 : ¬ drop0% Iris.SiProp.closed 4 :=
  fun h => Nat.one_ne_zero (h s0 (n₁ := 0) (n₂ := 1) rfl)

-- `Iris.SiProp.biEntails_of_iff` idx 2: necessary (P = True, Q = False)
theorem w6c0_64 : ¬ drop0% Iris.SiProp.biEntails_of_iff 2 :=
  fun h => (@h iprop(True) iprop(False)).1 0 trivial

-- `Iris.SiProp.pure_dist_of_iff` idx 3: necessary (n = 0, Φ = True, Ψ = False)
theorem w6c0_65 : ¬ drop0% Iris.SiProp.pure_dist_of_iff 3 :=
  fun h => ((@h 0 True False) (Nat.le_refl 0)).1 trivial

-- `Iris.SiProp.internalEq_rewrite` idx 5: necessary (A = SiProp, a = True, b = s0 (0-close), Ψ x = ⌜x = True⌝ (not non-expansive))
theorem w6c0_66 : ¬ drop0% Iris.SiProp.internalEq_rewrite 5 :=
  fun h => by
    have H := (h (A := SiProp) iprop(True) s0 (fun x => iprop(⌜x = iprop(True)⌝)))
      0 (fun {m} hm => ⟨fun _ => Nat.le_zero.mp hm, fun _ => trivial⟩) 0 (Nat.le_refl 0) rfl
    have H1 := congrArg (fun p : SiProp => p.holds 1) H
    exact Nat.one_ne_zero (cast H1.symm trivial)

-- `Iris.SiProp.later_soundness` idx 1: necessary (P = False)
theorem w6c0_67 : ¬ drop0% Iris.SiProp.later_soundness 1 :=
  fun h => (@h iprop(False)) 0 trivial

-- `Iris.Sbi.siPure_mono` idx 4: necessary (SiProp, Pi = True, Qi = False)
theorem w6c0_68 : ¬ drop0% Iris.Sbi.siPure_mono 4 :=
  fun h => (@h SiProp _ iprop(True) iprop(False)) 0 trivial

-- `Iris.Sbi.siEmpValid_mono` idx 4: necessary (SiProp, P = True, Q = False)
theorem w6c0_69 : ¬ drop0% Iris.Sbi.siEmpValid_mono 4 :=
  fun h => (@h SiProp _ iprop(True) iprop(False)) 0 trivial

-- `Iris.siPure_mono_bi` idx 4: necessary (SiProp, Pi = True, Qi = False)
theorem w6c0_70 : ¬ drop0% Iris.siPure_mono_bi 4 :=
  fun h => (@h SiProp _ iprop(True) iprop(False)).1 0 trivial

-- `Iris.siPure_timeless` idx 3: necessary (SiProp, Pi = s0)
theorem w6c0_71 : ¬ drop0% Iris.siPure_timeless 3 :=
  fun h => nt (Q := s0) (@h SiProp _ s0).timeless rfl Nat.one_ne_zero

-- `Iris.siPure_siEmpValid_elim` idx 3: necessary (non-affine UPred NA, P = emp: <si_pure> <si_emp_valid> emp = ■ emp holds everywhere)
theorem w6c0_72 : ¬ drop0% Iris.siPure_siEmpValid_elim 3 :=
  fun h => na_true_not_emp (plainly_emp_intro.trans (@h (UPred NA) _ iprop(emp)))

-- `Iris.siEmpValid_congr` idx 4: necessary (SiProp, P = True, Q = False)
theorem w6c0_73 : ¬ drop0% Iris.siEmpValid_congr 4 :=
  fun h => (@h SiProp _ iprop(True) iprop(False)).1 0 trivial

-- `Iris.siEmpValid_or` idx 2: necessary (MonPred DIdx SiProp (no SbiEmpValidExist), P = phiD true, Q = phiD false)
theorem w6c0_74 : ¬ drop0% Iris.siEmpValid_or 2 :=
  fun h => by
    have H := (@h (MonPred DIdx SiProp) _ (phiD true) (phiD false)).1 0
      (SiProp.forall_holds.2 fun j => show (j : Bool) = true ∨ (j : Bool) = false from Bool.eq_false_or_eq_true j)
    rcases H with H | H
    · exact Bool.noConfusion (SiProp.forall_holds.1 H iF : (false : Bool) = true)
    · exact Bool.noConfusion (SiProp.forall_holds.1 H iT : (true : Bool) = false)

-- `Iris.siEmpValid_sep` idx 2: necessary (non-positive UPred X2 (xor), P = Q = ownM i: P ∗ Q holds at the unit, P does not)
theorem w6c0_75 : ¬ drop0% Iris.siEmpValid_sep 2 :=
  fun h => by
    have H := (@h (UPred X2) _ oI oI).1 0 ⟨.i, .i, rfl, rfl, rfl⟩
    cases H.1

-- `Iris.siEmpValid_timeless` idx 3: necessary (SiProp, P = s0)
theorem w6c0_76 : ¬ drop0% Iris.siEmpValid_timeless 3 :=
  fun h => nt (Q := s0) (@h SiProp _ s0).timeless rfl Nat.one_ne_zero

-- `Iris.only0_persistent` idx 3: necessary (non-affine UPred NA, P = ownM a: <only0> ownM a holds at a, not at e (step 0))
theorem w6c0_77 : ¬ drop0% Iris.only0_persistent 3 :=
  fun h => naE (@h (UPred NA) _ (UPred.ownM NA.a)).persistent
    (fun x' h1 _ _ => h1) (fun H => by cases H ⟨.e, trivial⟩ rfl (Nat.le_refl 0) trivial)

-- `Iris.siPure_inj` idx 4: necessary (SiProp, Pi = True, Qi = False)
theorem w6c0_78 : ¬ drop0% Iris.siPure_inj 4 :=
  fun h => (@h SiProp _ iprop(True) iprop(False)).1 0 trivial

-- `Iris.pure_soundness` idx 3: necessary (SiProp, φ = False)
theorem w6c0_79 : ¬ drop0% Iris.pure_soundness 3 :=
  fun h => @h SiProp _ False

-- `Iris.later_soundness` idx 3: necessary (SiProp, P = False)
theorem w6c0_80 : ¬ drop0% Iris.later_soundness 3 :=
  fun h => (@h SiProp _ iprop(False)) 0 trivial

-- `Iris.laterN_soundness` idx 4: necessary (SiProp, P = False, n = 0)
theorem w6c0_81 : ¬ drop0% Iris.laterN_soundness 4 :=
  fun h => (@h SiProp _ iprop(False) 0) 0 trivial

-- `Iris.plainly_mono` idx 4: necessary (SiProp, P = True, Q = False)
theorem w6c0_82 : ¬ drop0% Iris.plainly_mono 4 :=
  fun h => (@h SiProp _ iprop(True) iprop(False)) 0 trivial

-- `Iris.plainly_sExists` idx 2: necessary (MonPred DIdx SiProp (no SbiEmpValidExist), Φ p = (p = phiD true ∨ p = phiD false))
theorem w6c0_83 : ¬ drop0% Iris.plainly_sExists 2 :=
  fun h => by
    have H := @h (MonPred DIdx SiProp) _ (fun p => p = phiD true ∨ p = phiD false)
    have hl : ((iprop(■ BIBase.sExists (fun p => p = phiD true ∨ p = phiD false)) : MonPred DIdx SiProp).monPred_at iT).holds 0 := by
      have e : (BIBase.sExists (fun p => p = phiD true ∨ p = phiD false) : MonPred DIdx SiProp) = iprop(phiD true ∨ phiD false) :=
        BiEntails.to_eq ⟨sExists_elim fun p hp => hp.elim (fun e => e ▸ or_intro_l) (fun e => e ▸ or_intro_r),
          or_elim (sExists_intro (Or.inl rfl)) (sExists_intro (Or.inr rfl))⟩
      rw [e]
      exact (MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) iT _).mpr 0
        (SiProp.forall_holds.2 fun j => show (j : Bool) = true ∨ (j : Bool) = false from Bool.eq_false_or_eq_true j)
    obtain ⟨p, hp, hpl⟩ := SiProp.exists_holds.1
      ((MonPred.monPred_at_exist (I := DIdx) (PROP := SiProp) iT _).mp 0 (H iT 0 hl))
    rcases hp with e | e <;> subst e
    · exact Bool.noConfusion (dpl hpl iF : (false : Bool) = true)
    · exact Bool.noConfusion (dpl hpl iT : (true : Bool) = false)

-- `Iris.plainly_if_mono` idx 5: necessary (SiProp, p = true, P = True, Q = False)
theorem w6c0_84 : ¬ drop0% Iris.plainly_if_mono 5 :=
  fun h => (@h SiProp _ true iprop(True) iprop(False)) 0 trivial

-- `Iris.SbiUnfold.closed` idx 5: necessary (SiProp, Pi n = (n = 1) (not down closed), n₁ = 1, n₂ = 0)
theorem w6c0_85 : ¬ drop0% Iris.SbiUnfold.closed 5 :=
  fun h => Nat.zero_ne_one (@h SiProp instSbiSiProp .downClosed iprop(True) (fun n => n = 1) 1 0 rfl rfl (Nat.zero_le 1))

-- `Iris.SbiUnfold.closed` idx 8: necessary (SiProp, clo = notClosed, P = downClose Pi with Pi n = (n = 1), n₁ = 1, n₂ = 0)
theorem w6c0_86 : ¬ drop0% Iris.SbiUnfold.closed 8 :=
  fun h => Nat.zero_ne_one (@h SiProp instSbiSiProp .notClosed (SiProp.downClose fun n => n = 1) (fun n => n = 1)
    (SbiUnfold.of_downClose (clo := .notClosed) .rfl) 1 0 rfl (Nat.zero_le 1))

-- `Iris.SbiUnfold.closed` idx 10: necessary (SiProp, P = s0 with its own interpretation, n₁ = 0, n₂ = 1)
theorem w6c0_87 : ¬ drop0% Iris.SbiUnfold.closed 10 :=
  fun h => Nat.one_ne_zero (@h SiProp instSbiSiProp .downClosed s0 s0.holds (sbiUnfold_siProp _ _) 0 1 rfl rfl)

-- `Iris.SbiUnfold.as_siPure` idx 5: necessary (SiProp, P = False, Pi = True)
theorem w6c0_88 : ¬ drop0% Iris.SbiUnfold.as_siPure 5 :=
  fun h => (@h SiProp _ .notClosed iprop(False) (fun _ => True)).2 0 (fun _ _ => trivial)

-- `Iris.SbiUnfold.downClose_of_closed` idx 1: necessary (Pi n = (n = 1), n = 1)
theorem w6c0_89 : ¬ drop0% Iris.SbiUnfold.downClose_of_closed 1 :=
  fun h => Nat.zero_ne_one ((@h (fun n => n = 1) 1).2 rfl 0 (Nat.zero_le 1))

-- `Iris.SbiUnfold.of_closed` idx 5: necessary (SiProp, Pi n = (n = 1), n₁ = 1, n₂ = 0)
theorem w6c0_90 : ¬ indep0% Iris.SbiUnfold.of_closed 5 :=
  fun h => Nat.zero_ne_one (@h SiProp _ .notClosed iprop(True) (fun n => n = 1) 1 0 rfl (Nat.zero_le 1))

-- `Iris.SbiUnfold.of_closed` idx 6: necessary (SiProp, P = False, Pi = True)
theorem w6c0_91 : ¬ drop0% Iris.SbiUnfold.of_closed 6 :=
  fun h => (@h SiProp _ .notClosed iprop(False) (fun _ => True) (fun _ _ => trivial)).as_siPure.2 0 (fun _ _ => trivial)

-- `Iris.SbiUnfold.of_downClose` idx 5: necessary (SiProp, clo = notClosed, P = False, Pi = True)
theorem w6c0_92 : ¬ drop0% Iris.SbiUnfold.of_downClose 5 :=
  fun h => (@h SiProp _ .notClosed iprop(False) (fun _ => True)).as_siPure.2 0 (fun _ _ => trivial)

-- `Iris.SbiUnfold.weaken` idx 5: necessary (SiProp, clo = notClosed, P = False, Pi = True)
theorem w6c0_93 : ¬ drop0% Iris.SbiUnfold.weaken 5 :=
  fun h => (@h SiProp _ .notClosed iprop(False) (fun _ => True)).as_siPure.2 0 (fun _ _ => trivial)

-- `Iris.SbiUnfold.entails_iff` idx 7: necessary (SiProp, P = True, Q = False, Qi = True)
theorem w6c0_94 : ¬ drop0% Iris.SbiUnfold.entails_iff 7 :=
  fun h => (((@h SiProp _ iprop(True) iprop(False) (fun _ => True) (fun _ => True) sbiUnfold_pure).2
    (fun _ _ => trivial)) 0 trivial)

-- `Iris.SbiUnfold.biEntails_iff` idx 7: necessary (SiProp, P = True, Q = False, Qi = True)
theorem w6c0_95 : ¬ drop0% Iris.SbiUnfold.biEntails_iff 7 :=
  fun h => (((@h SiProp _ iprop(True) iprop(False) (fun _ => True) (fun _ => True) sbiUnfold_pure).2
    (fun _ => Iff.rfl)).1 0 trivial)

-- `Iris.SbiUnfold.empValid_iff` idx 4: necessary (SiProp, Q = False, Qi = True)
theorem w6c0_96 : ¬ drop0% Iris.SbiUnfold.empValid_iff 4 :=
  fun h => (((@h SiProp _ iprop(False) (fun _ => True)).2 (fun _ => trivial)) 0 trivial)

-- `Iris.sbiUnfold_siPure` idx 5: necessary (SiProp, Psi = False, Pi = True)
theorem w6c0_97 : ¬ drop0% Iris.sbiUnfold_siPure 5 :=
  fun h => (@h SiProp _ .notClosed (fun _ => True) iprop(False)).as_siPure.2 0 (fun _ _ => trivial)

-- `Iris.sbiUnfold_and` idx 7: necessary (SiProp, P = False with Pi = True, Q = True)
theorem w6c0_98 : ¬ drop0% Iris.sbiUnfold_and 7 :=
  fun h => ((@h SiProp _ .notClosed iprop(False) iprop(True) (fun _ => True) (fun _ => True) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => ⟨trivial, trivial⟩)).1

-- `Iris.sbiUnfold_and` idx 8: necessary (SiProp, P = True, Q = False with Qi = True)
theorem w6c0_99 : ¬ drop0% Iris.sbiUnfold_and 8 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => True) (fun _ => True) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => ⟨trivial, trivial⟩)).2

-- `Iris.sbiUnfold_sep` idx 7: necessary (SiProp, P = False with Pi = True, Q = True)
theorem w6c0_100 : ¬ drop0% Iris.sbiUnfold_sep 7 :=
  fun h => ((@h SiProp _ .notClosed iprop(False) iprop(True) (fun _ => True) (fun _ => True) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => ⟨trivial, trivial⟩)).1

-- `Iris.sbiUnfold_sep` idx 8: necessary (SiProp, P = True, Q = False with Qi = True)
theorem w6c0_101 : ¬ drop0% Iris.sbiUnfold_sep 8 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => True) (fun _ => True) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => ⟨trivial, trivial⟩)).2

-- `Iris.sbiUnfold_or` idx 7: necessary (SiProp, P = False with Pi = True, Q = False)
theorem w6c0_102 : ¬ drop0% Iris.sbiUnfold_or 7 :=
  fun h => ((@h SiProp _ .notClosed iprop(False) iprop(False) (fun _ => True) (fun _ => False) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => Or.inl trivial)).elim id id

-- `Iris.sbiUnfold_or` idx 8: necessary (SiProp, P = False, Q = False with Qi = True)
theorem w6c0_103 : ¬ drop0% Iris.sbiUnfold_or 8 :=
  fun h => ((@h SiProp _ .notClosed iprop(False) iprop(False) (fun _ => False) (fun _ => True) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => Or.inr trivial)).elim id id

-- `Iris.sbiUnfold_imp` idx 7: necessary (SiProp, P = True with Pi = False, Q = False)
theorem w6c0_104 : ¬ drop0% Iris.sbiUnfold_imp 7 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => False) (fun _ => False) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => id)) 0 (Nat.le_refl 0) trivial

-- `Iris.sbiUnfold_imp` idx 8: necessary (SiProp, P = True, Q = False with Qi = True)
theorem w6c0_105 : ¬ drop0% Iris.sbiUnfold_imp 8 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => True) (fun _ => True) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ _ => trivial)) 0 (Nat.le_refl 0) trivial

-- `Iris.sbiUnfold_wand` idx 7: necessary (SiProp, P = True with Pi = False, Q = False)
theorem w6c0_106 : ¬ drop0% Iris.sbiUnfold_wand 7 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => False) (fun _ => False) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => id)) 0 (Nat.le_refl 0) trivial

-- `Iris.sbiUnfold_wand` idx 8: necessary (SiProp, P = True, Q = False with Qi = True)
theorem w6c0_107 : ¬ drop0% Iris.sbiUnfold_wand 8 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => True) (fun _ => True) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ _ => trivial)) 0 (Nat.le_refl 0) trivial

-- `Iris.sbiUnfold_iff` idx 7: necessary (SiProp, P = True with Pi = False, Q = False)
theorem w6c0_108 : ¬ drop0% Iris.sbiUnfold_iff 7 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => False) (fun _ => False) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => Iff.rfl)).1 0 (Nat.le_refl 0) trivial

-- `Iris.sbiUnfold_iff` idx 8: necessary (SiProp, P = True, Q = False with Qi = True)
theorem w6c0_109 : ¬ drop0% Iris.sbiUnfold_iff 8 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => True) (fun _ => True) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => Iff.rfl)).1 0 (Nat.le_refl 0) trivial

-- `Iris.sbiUnfold_wandIff` idx 7: necessary (SiProp, P = True with Pi = False, Q = False)
theorem w6c0_110 : ¬ drop0% Iris.sbiUnfold_wandIff 7 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => False) (fun _ => False) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => Iff.rfl)).1 0 (Nat.le_refl 0) trivial

-- `Iris.sbiUnfold_wandIff` idx 8: necessary (SiProp, P = True, Q = False with Qi = True)
theorem w6c0_111 : ¬ drop0% Iris.sbiUnfold_wandIff 8 :=
  fun h => ((@h SiProp _ .notClosed iprop(True) iprop(False) (fun _ => True) (fun _ => True) sbiUnfold_pure).as_siPure.2 0
    (fun _ _ => Iff.rfl)).1 0 (Nat.le_refl 0) trivial

-- `Iris.sbiUnfold_forall` idx 6: necessary (SiProp, A = True, Φ _ = False, Φi _ _ = True)
theorem w6c0_112 : ¬ drop0% Iris.sbiUnfold_forall 6 :=
  fun h => SiProp.forall_holds.1 ((@h SiProp _ .notClosed True (fun _ => iprop(False)) (fun _ _ => True)).as_siPure.2 0
    (fun _ _ _ => trivial)) trivial

-- `Iris.sbiUnfold_exists` idx 6: necessary (SiProp, A = True, Φ _ = False, Φi _ _ = True)
theorem w6c0_113 : ¬ drop0% Iris.sbiUnfold_exists 6 :=
  fun h => (SiProp.exists_holds.1 ((@h SiProp _ .notClosed True (fun _ => iprop(False)) (fun _ _ => True)).as_siPure.2 0
    (fun _ _ => ⟨trivial, trivial⟩))).2

-- `Iris.sbiUnfold_later` idx 5: necessary (SiProp, P = False, Pi = True, at step 1)
theorem w6c0_114 : ¬ drop0% Iris.sbiUnfold_later 5 :=
  fun h => (@h SiProp _ .notClosed iprop(False) (fun _ => True)).as_siPure.2 1
    (fun n _ => by cases n <;> trivial)

-- `Iris.BI.plainly_if_exists` idx 3: necessary (p = true, MonPred DIdx SiProp (no SbiEmpValidExist), A = Bool, Ψ = phiD)
theorem w6c0_115 : ¬ drop0% Iris.BI.plainly_if_exists 3 :=
  fun h => by
    have H := (@h (MonPred DIdx SiProp) _ true Bool phiD).1
    have hl : ((iprop(■ ∃ a, phiD a) : MonPred DIdx SiProp).monPred_at iT).holds 0 :=
      (MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) iT _).mpr 0
        (SiProp.forall_holds.2 fun j =>
          (MonPred.monPred_at_exist (I := DIdx) (PROP := SiProp) j phiD).mpr 0 (SiProp.exists_holds.2 ⟨(j : Bool), rfl⟩))
    obtain ⟨a, ha⟩ := SiProp.exists_holds.1
      ((MonPred.monPred_at_exist (I := DIdx) (PROP := SiProp) iT (fun a => iprop(■ phiD a))).mp 0 (H iT 0 hl))
    have e1 : (true : Bool) = a := dpl ha iT
    have e2 : (false : Bool) = a := dpl ha iF
    exact Bool.noConfusion (e1.trans e2.symm)

-- `Iris.BI.wand_persistent` idx 6: necessary (non-affine UPred EC, P = True (plain), Q = emp (persistent, not absorbing): True -∗ emp holds at c, not at core c = e)
theorem w6c0_116 : ¬ drop0% Iris.BI.wand_persistent 6 :=
  fun h => ec_e ((@h (UPred EC) _ iprop(True) iprop(emp) _ _).persistent 0 vC ec_c)

-- `Iris.BI.wand_plain` idx 4: necessary (non-affine UPred EC, P = True, Q = emp (plain, not absorbing): True -∗ emp holds at c, not at e)
theorem w6c0_117 : ¬ drop0% Iris.BI.wand_plain 4 :=
  fun h => ec_e ((@h (UPred EC) _ iprop(True) iprop(emp) _ _).plain 0 vC ec_c)

-- `Iris.BI.limitPreserving_plain` idx 5: necessary (MonPred DIdx SiProp, A = Bool streams (COFE), Φ x = True if x has a true entry, else phiD true (not non-expansive); escaping chain)
theorem w6c0_118 : ¬ drop0% Iris.BI.limitPreserving_plain 5 :=
  fun h => by
    classical
    have H := (@h (MonPred DIdx SiProp) _ CS _ (fun x => if hasT x then iprop(True) else phiD true)).compl escC
      (fun n => by rw [if_pos (hasT_esc n)]; exact inferInstance)
    rw [if_neg not_hasT_lim] at H
    exact phi_np H.plain

-- `Iris.BI.bigSepS_plain` idx 8: necessary (MonPred DIdx SiProp, S = ExtTreeSet Nat (countable), s = {0}, Φ _ = phiD true)
theorem w6c0_119 : ¬ drop0% Iris.BI.bigSepS_plain 8 :=
  fun h => dsand (BigSepS.bigSepS_singleton (S := TS) (Φ := fun _ => phiD true) (x := 0)).2
    (BigSepS.bigSepS_singleton (S := TS) (Φ := fun _ => phiD true) (x := 0)).1
    (@h (MonPred DIdx SiProp) _ TS _ Nat _ (fun _ => phiD true) _).plain

-- `Iris.only0_intuitionistically` idx 3: necessary (Sbi TQ (step-indexed Bool-or predicates, resource-blind at step 0; Löb from sbi_later_contractive) with non-timeless emp, P = True: <only0> □ True holds at (1, true), □ <only0> True does not)
theorem w6c0_120 : ¬ drop0% Iris.only0_intuitionistically 3 :=
  fun h => by
    have H := (@h TQ tqSbi _ iprop(True)).1 1 true (fun n' _ hf => by
      cases n' with
      | zero => exact ⟨.inl rfl, trivial⟩
      | succ j => exact (hf : False).elim)
    rcases H.1 with h1 | h1 <;> cases h1
