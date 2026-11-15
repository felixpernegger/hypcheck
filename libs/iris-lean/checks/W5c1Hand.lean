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
namespace W5c1
open Iris Iris.BI Iris.OFE

/-- Discrete Bool OFE. -/
structure DB where b : Bool
instance : OFE DB := OFE.ofDiscrete DB
instance : OFE.Discrete DB := ⟨id⟩
def dT : DB := ⟨true⟩
def dF : DB := ⟨false⟩
theorem dTF : dT ≠ dF := by simp [dT, dF]
/-- Every map out of the discrete DB is non-expansive. -/
theorem db_ne {B : Type} [OFE B] (f : DB → B) : NonExpansive f := ⟨fun _ _ _ h => (h : _ = _) ▸ OFE.Dist.rfl⟩

/-- Truncation OFE on naturals (copied from Probe1): 1 and 2 agree at step 0. -/
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

/-- Non-positive BI over (Bool, xor) (copied from W4c0). -/
structure ZP where p : Bool → Prop

theorem ZP.ext' {P Q : ZP} (h : ∀ w, P.p w ↔ Q.p w) : P = Q := by
  cases P; cases Q; congr; funext w; exact propext (h w)

instance : COFE ZP := COFE.ofDiscrete _

instance zpBase : BIBase ZP where
  Entails P Q := ∀ w, P.p w → Q.p w
  emp := ⟨fun w => w = false⟩
  pure φ := ⟨fun _ => φ⟩
  and P Q := ⟨fun w => P.p w ∧ Q.p w⟩
  or P Q := ⟨fun w => P.p w ∨ Q.p w⟩
  imp P Q := ⟨fun w => P.p w → Q.p w⟩
  sForall Ψ := ⟨fun w => ∀ p, Ψ p → p.p w⟩
  sExists Ψ := ⟨fun w => ∃ p, Ψ p ∧ p.p w⟩
  sep P Q := ⟨fun w => ∃ x y, w = xor x y ∧ P.p x ∧ Q.p y⟩
  wand P Q := ⟨fun w => ∀ y, P.p y → Q.p (xor w y)⟩
  persistently P := ⟨fun _ => ∀ w, w = false → P.p w⟩
  later P := P

instance zpBI : BI ZP := BI.ofPersistentlyDiscrete
  (entails_refl := fun _ h => h)
  (entails_trans := fun h1 h2 w h => h2 w (h1 w h))
  (equiv_iff := fun {P Q} => ⟨fun e => e ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h1, h2⟩ => ZP.ext' fun w => ⟨h1 w, h2 w⟩⟩)
  (pure_intro := fun h _ _ => h)
  (pure_elim' := fun h w hφ => h hφ w trivial)
  (and_elim_l := fun _ h => h.1)
  (and_elim_r := fun _ h => h.2)
  (and_intro := fun h1 h2 w h => ⟨h1 w h, h2 w h⟩)
  (or_intro_l := fun _ h => .inl h)
  (or_intro_r := fun _ h => .inr h)
  (or_elim := fun h1 h2 w h => h.elim (h1 w) (h2 w))
  (imp_intro := fun h w hP hQ => h w ⟨hP, hQ⟩)
  (imp_elim := fun h w hPQ => h w hPQ.1 hPQ.2)
  (sForall_intro := fun h w hP p hp => h p hp w hP)
  (sForall_elim := fun hp _ h => h _ hp)
  (sExists_intro := fun hp _ h => ⟨_, hp, h⟩)
  (sExists_elim := fun h w ⟨p, hp, hpw⟩ => h p hp w hpw)
  (sep_mono := fun h1 h2 _ ⟨x, y, e, hx, hy⟩ => ⟨x, y, e, h1 x hx, h2 y hy⟩)
  (emp_sep := ⟨fun w ⟨x, y, e, hx, hy⟩ => by
      have hx' : x = false := hx
      subst hx'; rw [Bool.false_xor] at e; exact e ▸ hy,
    fun w h => ⟨false, w, (Bool.false_xor w).symm, rfl, h⟩⟩)
  (sep_symm := fun _ ⟨x, y, e, hx, hy⟩ => ⟨y, x, e.trans (Bool.xor_comm x y), hy, hx⟩)
  (sep_assoc_l := fun _ ⟨u, z, e, ⟨x, y, eu, hx, hy⟩, hz⟩ =>
    ⟨x, xor y z, by rw [e, eu, Bool.xor_assoc], hx, ⟨y, z, rfl, hy, hz⟩⟩)
  (wand_intro := fun h w hP y hQ => h _ ⟨w, y, rfl, hP, hQ⟩)
  (wand_elim := fun h _ ⟨x, y, e, hx, hy⟩ => e ▸ h x hx y hy)
  (later_mono := fun h => h)
  (later_intro := fun _ h => h)
  (later_sForall_2 := fun _ h p hp => h _ ⟨p, rfl⟩ hp)
  (later_sExists_false := fun _ ⟨p, hp, hpw⟩ => .inr ⟨_, ⟨p, rfl⟩, hp, hpw⟩)
  (later_sep := ⟨fun _ h => h, fun _ h => h⟩)
  (later_persistently := ⟨fun _ h => h, fun _ h => h⟩)
  (later_false_em := fun _ h => .inr (fun _ => h))
  (discrete := fun h => h)
  (persistently_eq := fun _ => rfl)

def zT : ZP := ⟨fun w => w = true⟩

/-- Non-affine HeapProp Unit (copied from Probe4). -/
abbrev HP := Iris.Instances.Classical.HeapProp Unit
open Iris.Instances.Data in
def s1 : State Unit := fun _ => result ()
open Iris.Instances.Data in
theorem s1_ne : s1 ≠ ∅ := fun h => by have h0 := congrFun h 0; cases h0
theorem heap_not_affine : ¬ ((iprop(True) : HP) ⊢ emp) := fun h => s1_ne (h s1 trivial)

/-- Two-element UORA with the extension order (copied from Probe3): UPred AF affine, ownM a not persistent. -/
inductive AF | e | a deriving DecidableEq

def AF.op : AF → AF → AF
  | .e, y => y
  | .a, _ => .a

instance : OFE AF := OFE.ofDiscrete AF
instance : OFE.Discrete AF := ⟨id⟩

instance instORAAF : ORA AF := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := AF.op
  Valid := fun _ => True
  Order := fun x y => x = .e ∨ x = y
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := by intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all
  op_mono_left := by intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [AF.op]
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; exact .inl rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; exact .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact .inr rfl
  increasing_closed := by intro x y hx h z; cases x <;> cases y <;> cases z <;> simp_all [AF.op] }

instance : OrderRefl AF := ⟨fun x => show x = .e ∨ x = x from .inr rfl⟩

instance instUORAAF : UORA AF where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

instance : IncOrd AF := ⟨by
  intro x y ⟨z, hz⟩
  show x = .e ∨ x = y
  cases x <;> cases z <;> simp_all [Op.op, AF.op]⟩

/-- Two-element UORA with the equality order (copied from Probe3): UPred NA is a non-affine Sbi. -/
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

theorem na_true_not_emp : ¬ ((iprop(True) : UPred NA) ⊢ iprop(emp)) := fun h => by
  have H := h 0 ⟨.a, trivial⟩ trivial
  cases H

/-- Constant-True basic update on SiProp: a lawful BIUpdate that is not plain-preserving. -/
@[reducible] def topBupd : BIUpdate SiProp where
  bupd _ := iprop(True)
  bupd_ne := ⟨fun _ _ _ _ _ _ => Iff.rfl⟩
  intro := fun _ _ => trivial
  mono _ := fun _ h => h
  trans := fun _ h => h
  frame_right := fun _ _ => trivial

/-- Identity basic update on SiProp (copied from Probe4). -/
@[reducible] def idBupd : BIUpdate SiProp where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h

/-- Later credits on SiProp: £ n holds iff n = 0. -/
@[reducible] def lcZ : BILaterCredits SiProp where
  lc n := iprop(⌜n = 0⌝)
  lc_split {n m} := ⟨fun _ h => ⟨by have : n + m = 0 := h; show n = 0; omega, by have : n + m = 0 := h; show m = 0; omega⟩,
    fun _ h => by have h1 : n = 0 := h.1; have h2 : m = 0 := h.2; show n + m = 0; omega⟩
  lc_timeless _ := inferInstance
  lc_0_persistent := inferInstance
  lc_affine _ := inferInstance

/-- Later credits on SiProp: £ n is False. -/
@[reducible] def lcF : BILaterCredits SiProp where
  lc _ := iprop(False)
  lc_split := ⟨fun _ h => ⟨h, h⟩, fun _ h => h.1⟩
  lc_timeless _ := inferInstance
  lc_0_persistent := inferInstance
  lc_affine _ := inferInstance

end W5c1

namespace W5c1
open Iris Iris.BI Iris.OFE

-- `Iris.BI.BIPositive.affinely_sep_l` idx 2: necessary (ZP (Bool, xor) non-positive BI: <affine>(zT ∗ zT) holds at false, <affine> zT ∗ zT is empty)
theorem w5c1_0 : ¬ drop0% Iris.BI.BIPositive.affinely_sep_l 2 := fun h => by
  have H0 : ∀ w, _ → _ := @h ZP _ zT zT
  have H := H0 false ⟨rfl, true, true, rfl, rfl, rfl⟩
  obtain ⟨x, y, e, ⟨hx1, hx2⟩, _⟩ := H
  subst hx1; cases hx2

-- `Iris.BI.BILoeb.loeb_weak` idx 2: necessary (HeapProp Unit (later = id): ▷False ⊢ False holds but True ⊢ False fails)
theorem w5c1_1 : ¬ drop0% Iris.BI.BILoeb.loeb_weak 2 := fun h =>
  (@h HP _ iprop(False) (fun _ h => h)) ∅ trivial

-- `Iris.BI.BILoeb.loeb_weak` idx 4: necessary (SiProp (BILoeb): P = False)
theorem w5c1_2 : ¬ drop0% Iris.BI.BILoeb.loeb_weak 4 := fun h =>
  (@h SiProp _ _ iprop(False)) 0 trivial

-- `Iris.BI.BILaterContractive.toContractive` idx 2: necessary (HeapProp Unit is a discrete OFE with later = id, which is not contractive (True, False))
theorem w5c1_3 : ¬ drop0% Iris.BI.BILaterContractive.toContractive 2 := fun h => by
  have H := (@h HP _).distLater_dist (n := 0) (x := iprop(True)) (y := iprop(False)) (fun _ hm => absurd hm (Nat.not_lt_zero _))
  have := (H : iprop(▷ True) = iprop(▷ False))
  exact cast (congrFun this ∅) trivial

-- `Iris.BI.and_intuitionistic` idx 4: necessary (affine UPred AF: P = ownM a, Q = emp; ownM a ∧ emp is not persistent)
theorem w5c1_7 : ¬ drop0% Iris.BI.and_intuitionistic 4 := fun h => by
  have H := (@h (UPred AF) _ (UPred.ownM .a) iprop(emp) inferInstance).intuitionistic 0 ⟨.a, trivial⟩ ⟨.inr rfl, .inl rfl⟩
  obtain ⟨_, h2, _⟩ := H
  rcases h2 with h2 | h2 <;> cases h2

-- `Iris.BI.or_intuitionistic` idx 4: necessary (HeapProp Unit: P = True, Q = False; True ∨ False ⊬ emp)
theorem w5c1_8 : ¬ drop0% Iris.BI.or_intuitionistic 4 := fun h =>
  heap_not_affine ((or_intro_l (Q := iprop(False))).trans
    ((@h HP _ iprop(True) iprop(False) ⟨false_elim⟩).intuitionistic.trans
      ((intuitionistically_mono (or_elim .rfl false_elim)).trans intuitionistically_elim_emp)))

-- `Iris.BI.or_intuitionistic` idx 5: necessary (HeapProp Unit: P = False, Q = True)
theorem w5c1_9 : ¬ drop0% Iris.BI.or_intuitionistic 5 := fun h =>
  heap_not_affine ((or_intro_r (P := iprop(False))).trans
    ((@h HP _ iprop(False) iprop(True) ⟨false_elim⟩).intuitionistic.trans
      ((intuitionistically_mono (or_elim false_elim .rfl)).trans intuitionistically_elim_emp)))

-- `Iris.BI.exists_intuitionistic` idx 4: necessary (HeapProp Unit: α = True (Prop at universe 0), Φ _ = True; ∃ _, True ⊬ emp)
theorem w5c1_10 : ¬ drop0% Iris.BI.exists_intuitionistic 4 := fun h =>
  heap_not_affine ((exists_intro (Ψ := fun _ : True => iprop(True)) trivial).trans
    ((@h HP True _ (fun _ => iprop(True))).intuitionistic.trans intuitionistically_elim_emp))

-- `Iris.BI.sep_intuitionistic` idx 4: necessary (HeapProp Unit: P = True, Q = emp)
theorem w5c1_11 : ¬ drop0% Iris.BI.sep_intuitionistic 4 := fun h =>
  heap_not_affine (sep_emp.2.trans
    ((@h HP _ iprop(True) iprop(emp) inferInstance).intuitionistic.trans intuitionistically_elim_emp))

-- `Iris.BI.sep_intuitionistic` idx 5: necessary (HeapProp Unit: P = emp, Q = True)
theorem w5c1_12 : ¬ drop0% Iris.BI.sep_intuitionistic 5 := fun h =>
  heap_not_affine (emp_sep.2.trans
    ((@h HP _ iprop(emp) iprop(True) inferInstance).intuitionistic.trans intuitionistically_elim_emp))

-- `Iris.BI.internalEq.of_equiv` idx 7: necessary (SiProp, A = discrete Bool, a ≠ b: internalEq_soundness gives a = b)
theorem w5c1_13 : ¬ drop0% Iris.BI.internalEq.of_equiv 7 := fun h =>
  dTF.symm (internalEq_soundness (PROP := SiProp) _ _ (@h SiProp _ DB _ iprop(True) dF dT))

-- `Iris.BI.internalEq.rewrite` idx 7: necessary (SiProp, A = TN (1 and 2 agree at step 0), Ψ x = ⌜x = 1⌝ not non-expansive)
theorem w5c1_14 : ¬ drop0% Iris.BI.internalEq.rewrite 7 := fun h => by
  have H := (@h SiProp _ TN _ ⟨1⟩ ⟨2⟩ (fun x => iprop(⌜x = ⟨1⟩⌝))) 0 tn12 0 (Nat.le_refl 0) rfl
  exact absurd H (by simp)

-- `Iris.BI.internalEq.rewrite'` idx 8: necessary (SiProp, A = TN, P = (1 ≡ 2), Ψ x = ⌜x = 1⌝ not non-expansive)
theorem w5c1_15 : ¬ drop0% Iris.BI.internalEq.rewrite' 8 := fun h => by
  have H := (@h SiProp _ iprop(internalEq (⟨1⟩ : TN) ⟨2⟩) TN _ ⟨1⟩ ⟨2⟩ (fun x => iprop(⌜x = ⟨1⟩⌝)) .rfl (fun _ _ => rfl)) 0 tn12
  exact absurd H (by simp)

-- `Iris.BI.internalEq.rewrite'` idx 9: necessary (SiProp, discrete Bool, a = true, b = false, Ψ x = ⌜x = true⌝, P = True)
theorem w5c1_16 : ¬ drop0% Iris.BI.internalEq.rewrite' 9 := fun h => by
  have H := (@h SiProp _ iprop(True) DB _ dT dF (fun x => iprop(⌜x = dT⌝)) (db_ne _) (fun _ _ => rfl)) 0 trivial
  exact dTF H.symm

-- `Iris.BI.internalEq.rewrite'` idx 10: necessary (SiProp, a = b, Ψ = const False, P = True)
theorem w5c1_17 : ¬ drop0% Iris.BI.internalEq.rewrite' 10 := fun h =>
  (@h SiProp _ iprop(True) DB _ dT dT (fun _ => iprop(False)) (db_ne _) internalEq.refl) 0 trivial

-- `Iris.BI.f_equivI_contractive` idx 7: necessary (SiProp, f = id on discrete Bool (not contractive): ▷(true ≡ false) holds at step 0)
theorem w5c1_18 : ¬ drop0% Iris.BI.f_equivI_contractive 7 := fun h => by
  have H := (@h SiProp _ DB DB _ _ id dT dF) 0 trivial
  exact dTF H

-- `Iris.BI.internalEq_soundness` idx 6: necessary (SiProp, discrete Bool true ≠ false)
theorem w5c1_23 : ¬ drop0% Iris.BI.internalEq_soundness 6 := fun h =>
  dTF (@h SiProp _ DB _ dT dF)

-- `Iris.BIBUpdLaterCredits.lc_zero` idx 4: necessary (SiProp with identity bupd and £ n := False)
theorem w5c1_24 : ¬ drop0% Iris.BIBUpdLaterCredits.lc_zero 4 := fun h =>
  (@h SiProp _ lcF idBupd) 0 trivial

-- `Iris.lc_weaken` idx 5: necessary (SiProp with £ n := ⌜n = 0⌝: £ 0 ⊬ £ 1)
theorem w5c1_26 : ¬ drop0% Iris.lc_weaken 5 := fun h => by
  have H := (@h SiProp _ lcZ 0 1) 0 rfl
  exact Nat.one_ne_zero H

end W5c1

namespace W5c1
open Iris Iris.BI Iris.OFE

/-- ▷ ⌜x = dT⌝ is contractive on the discrete DB. -/
instance laterDT : Contractive (fun x : DB => (iprop(▷ ⌜x = dT⌝) : SiProp)) := ⟨fun {n x y} h => by
  cases n with
  | zero => intro m hm; cases m with | zero => exact Iff.rfl | succ m => omega
  | succ n => have e : x = y := h n (Nat.lt_succ_self n); subst e; exact OFE.Dist.rfl⟩

-- `Iris.BI.internalEq_rewrite_contractive` idx 7: necessary (SiProp, discrete Bool, Ψ x = ⌜x = true⌝ (not contractive), step 0)
theorem w5c1_19 : ¬ drop0% Iris.BI.internalEq_rewrite_contractive 7 := fun h =>
  dTF ((@h SiProp _ DB _ dT dF (fun x => iprop(⌜x = dT⌝))) 0 trivial 0 (Nat.le_refl 0) rfl).symm

-- `Iris.BI.internalEq_rewrite_contractive'` idx 8: necessary (SiProp, P = ▷(true ≡ false), Ψ x = ⌜x = true⌝ (not contractive))
theorem w5c1_20 : ¬ drop0% Iris.BI.internalEq_rewrite_contractive' 8 := fun h =>
  dTF ((@h SiProp _ iprop(▷ internalEq dT dF) DB _ dT dF (fun x => iprop(⌜x = dT⌝)) .rfl (fun _ _ => rfl)) 0 trivial).symm

-- `Iris.BI.internalEq_rewrite_contractive'` idx 9: necessary (SiProp, P = True, Ψ x = ▷⌜x = true⌝ (contractive), a = true, b = false, step 1)
theorem w5c1_21 : ¬ drop0% Iris.BI.internalEq_rewrite_contractive' 9 := fun h =>
  dTF ((@h SiProp _ iprop(True) DB _ dT dF (fun x => iprop(▷ ⌜x = dT⌝)) laterDT (fun n _ => by
    cases n with | zero => trivial | succ n => exact (rfl : dT = dT))) 1 trivial).symm

-- `Iris.BI.internalEq_rewrite_contractive'` idx 10: necessary (SiProp, a = b, Ψ = const False (contractive), P = True)
theorem w5c1_22 : ¬ drop0% Iris.BI.internalEq_rewrite_contractive' 10 := fun h =>
  (@h SiProp _ iprop(True) DB _ dT dT (fun _ => iprop(False)) inferInstance (later_intro.trans (later_mono internalEq.refl))) 0 trivial

-- `Iris.BUpdPlain.BUpdPlain_mono` idx 4: necessary (SiProp: BUpdPlain True ⊢ BUpdPlain (■ False) fails)
theorem w5c1_58 : ¬ drop0% Iris.BUpdPlain.BUpdPlain_mono 4 := fun h =>
  (BUpdPlain.BUpdPlain_intro.trans ((@h SiProp _ iprop(True) iprop(■ False)).trans BUpdPlain.BUpdPlain_plainly)) 0 trivial

-- `Iris.BUpdPlain.BUpd_BUpdPlain` idx 3: necessary (SiProp with constant-True bupd (lawful): |==> ■False ⊬ BUpdPlain (■False) = False)
theorem w5c1_59 : ¬ drop0% Iris.BUpdPlain.BUpd_BUpdPlain 3 := fun h =>
  ((@h SiProp _ topBupd iprop(■ False)).trans BUpdPlain.BUpdPlain_plainly) 0 trivial

-- `Iris.BUpdPlain.own_updateP` idx 7: necessary (SiProp, M = Option (Excl Unit), x = some invalid (vacuous update to False), own _ = True)
theorem w5c1_60 : ¬ drop0% Iris.BUpdPlain.own_updateP 7 := fun h =>
  ((@h SiProp _ (Option (Excl Unit)) _ (fun _ => iprop(True)) (some .invalid) (fun _ => False)
    (fun _ mz hv => by cases mz with | none => exact False.elim hv | some z => exact False.elim (ORA.validN_op_left hv))).trans
    ((BUpdPlain.BUpdPlain_mono (exists_elim fun _ => and_elim_l.trans (pure_elim' False.elim)) :
      _ ⊢ BUpdPlain (PROP := SiProp) iprop(■ False)).trans BUpdPlain.BUpdPlain_plainly)) 0 trivial

-- `Iris.BUpdPlain.own_updateP` idx 8: necessary (SiProp, M = Option (Excl Unit), own x = ⌜✓{0} x⌝ (satisfies own_updateP_plainly), x = none, Φ = False)
theorem w5c1_61 : ¬ drop0% Iris.BUpdPlain.own_updateP 8 := fun h =>
  ((@h SiProp _ (Option (Excl Unit)) _ (fun x => iprop(⌜✓{0} x⌝)) none (fun _ => False)
    (fun x Φ R hup n ⟨hx, hall⟩ => by
      obtain ⟨y, hy, hv⟩ := hup 0 none hx
      exact hall _ ⟨y, rfl⟩ n (Nat.le_refl n) hy n (Nat.le_refl n) hv)).trans
    ((BUpdPlain.BUpdPlain_mono (exists_elim fun _ => and_elim_l.trans (pure_elim' False.elim)) :
      _ ⊢ BUpdPlain (PROP := SiProp) iprop(■ False)).trans BUpdPlain.BUpdPlain_plainly)) 0 trivial

-- `Iris.coreP_affine` idx 3: necessary (non-affine UPred NA: P = True, coreP True ⊣⊢ True is not affine)
theorem w5c1_63 : ¬ drop0% Iris.coreP_affine 3 := fun h =>
  na_true_not_emp ((wand_entails coreP_intro).trans (@h (UPred NA) _ iprop(True)).affine)

-- `Iris.coreP_elim` idx 3: necessary (affine UPred AF: P = ownM a; coreP P is persistent there, so ownM a ⊢ <pers> ownM a would follow)
theorem w5c1_64 : ¬ drop0% Iris.coreP_elim 3 := fun h => by
  have H := ((wand_entails coreP_intro).trans ((coreP_persistent (PROP := UPred AF) (UPred.ownM .a)).persistent.trans
    (persistently_mono (wand_entails (@h (UPred AF) _ (UPred.ownM .a)))))) 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases H with H | H <;> cases H

-- `Iris.coreP_mono` idx 4: necessary (SiProp: coreP True ⊢ coreP False gives True ⊢ False)
theorem w5c1_65 : ¬ drop0% Iris.coreP_mono 4 := fun h =>
  ((wand_entails coreP_intro).trans ((@h SiProp _ iprop(True) iprop(False)).trans (wand_entails (coreP_elim _)))) 0 trivial

-- `Iris.coreP_proper` idx 4: necessary (SiProp: coreP True ⊣⊢ coreP False gives True ⊢ False)
theorem w5c1_66 : ¬ drop0% Iris.coreP_proper 4 := fun h =>
  ((wand_entails coreP_intro).trans ((@h SiProp _ iprop(True) iprop(False)).1.trans (wand_entails (coreP_elim _)))) 0 trivial

-- `Iris.coreP_entails'` idx 5: necessary (non-affine UPred NA: P = Q = True, True ⊢ □ True ⊢ emp fails)
theorem w5c1_69 : ¬ drop0% Iris.coreP_entails' 5 := fun h =>
  na_true_not_emp (((@h (UPred NA) _ _ iprop(True) iprop(True)).mp true_intro).trans intuitionistically_elim_emp)

-- `Iris.tac_aacc_intro` idx 10: necessary (SiProp, pa = false, A = False (hspec vacuous), e = True, Q = False)
theorem w5c1_53 : ¬ drop0% Iris.tac_aacc_intro 10 := fun h =>
  (@h SiProp _ false false iprop(True) iprop(True) iprop(False) iprop(True) iprop(True) iprop(False)
    (fun _ _ hs => hs.2) .rfl .rfl) 0 trivial

-- `Iris.tac_aacc_intro` idx 11: necessary (SiProp, pa = false, A = True, e = True, Q = False)
theorem w5c1_54 : ¬ drop0% Iris.tac_aacc_intro 11 := fun h =>
  (@h SiProp _ false false iprop(True) iprop(True) iprop(True) iprop(True) iprop(True) iprop(False)
    true_intro .rfl .rfl) 0 trivial

-- `Iris.tac_aacc_intro` idx 12: necessary (SiProp, R1 = False makes the premise of hspec unsatisfiable, e = True, Q = False)
theorem w5c1_55 : ¬ drop0% Iris.tac_aacc_intro 12 := fun h =>
  (@h SiProp _ false false iprop(True) iprop(True) iprop(True) iprop(False) iprop(True) iprop(False)
    true_intro (fun hp => absurd (hp 0 ⟨trivial, fun _ _ hr => hr.1⟩) id) .rfl) 0 trivial

-- `Iris.tac_aacc_intro` idx 13: necessary (SiProp, R2 = False makes the premise of hspec unsatisfiable, e = True, Q = False)
theorem w5c1_56 : ¬ drop0% Iris.tac_aacc_intro 13 := fun h =>
  (@h SiProp _ false false iprop(True) iprop(True) iprop(True) iprop(True) iprop(False) iprop(False)
    true_intro (fun hp => absurd (hp 0 ⟨trivial, fun _ _ hr => hr.2⟩) id) .rfl) 0 trivial

end W5c1

namespace W5c1
open Iris Iris.BI Iris.OFE

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF

/-- Later credits on IProp with £ n := True. -/
@[reducible] noncomputable def lcT : BILaterCredits (IProp CGF) where
  lc _ := iprop(True)
  lc_split := ⟨emp_sep.2.trans (sep_mono_left true_intro), true_intro⟩
  lc_timeless _ := inferInstance
  lc_0_persistent := inferInstance
  lc_affine _ := inferInstance

/-- If ▷ Q ⊢ Q for Q := |={⊤}=> False in IProp, Löb and fupd soundness give False. -/
theorem fupd_loeb_false (H : ∀ [InvGS_gen .hasNoLC CGF],
    (iprop(▷ |={⊤}=> ⌜False⌝) : IProp CGF) ⊢ iprop(|={⊤}=> ⌜False⌝)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (true_intro.trans (loeb_weak H))))

-- `Iris.BIFUpdLaterCredits.lc_fupd_elim_later` idx 4: necessary (IProp (closed-proofs GF) with £ n := True: ▷Q ⊢ Q for Q = |={⊤}=> False, Löb and fupd_soundness give False)
theorem w5c1_25 : ¬ drop0% Iris.BIFUpdLaterCredits.lc_fupd_elim_later 4 := fun h =>
  fupd_loeb_false fun {_} => (emp_sep.2.trans (sep_mono_left true_intro)).trans
    ((wand_elim (wand_entails (@h (IProp CGF) _ lcT _ ⊤ iprop(|={⊤}=> ⌜False⌝)))).trans BIFUpdate.trans)

-- `Iris.lc_fupd_add_later` idx 4: necessary (IProp with £ n := True, E1 = E2 = ⊤, P = False: Löb on |={⊤}=> False)
theorem w5c1_27 : ¬ drop0% Iris.lc_fupd_add_later 4 := fun h =>
  fupd_loeb_false fun {_} => (emp_sep.2.trans (sep_mono_left true_intro)).trans
    (wand_elim (wand_entails (@h (IProp CGF) _ lcT _ ⊤ ⊤ iprop(⌜False⌝))))

-- `Iris.lc_fupd_add_laterN` idx 4: necessary (IProp with £ n := True, n = 1: Löb on |={⊤}=> False)
theorem w5c1_28 : ¬ drop0% Iris.lc_fupd_add_laterN 4 := fun h =>
  fupd_loeb_false fun {_} => (emp_sep.2.trans (sep_mono_left true_intro)).trans
    (wand_elim (wand_entails (@h (IProp CGF) _ lcT _ 1 ⊤ ⊤ iprop(⌜False⌝))))

-- `Iris.lc_fupd_add_step_fupdN` idx 4: necessary (IProp with £ n := True, n = 1, all masks ⊤: Löb on |={⊤}=> False)
theorem w5c1_29 : ¬ drop0% Iris.lc_fupd_add_step_fupdN 4 := fun h =>
  fupd_loeb_false fun {_} => (emp_sep.2.trans (sep_mono true_intro
    ((later_mono fupd_intro).trans fupd_intro))).trans
    (wand_elim (wand_entails (@h (IProp CGF) _ lcT _ ⊤ ⊤ ⊤ iprop(⌜False⌝) 1)))

end W5c1

namespace W5c1
open Iris Iris.BI Iris.OFE Iris.Std

theorem acc_top (E : CoPset) [InvGS_gen .hasNoLC CGF] : ⊢ atomic_acc (PROP := IProp CGF) (TA := .nil) (TB := .nil) E E
    (fun _ => iprop(True)) iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) := by
  unfold atomic_acc
  iintro
  imodintro
  iexists ⟨⟩
  isplitl
  · itrivial
  isplit
  · iintro _
    imodintro
    itrivial
  · iintro %_ _
    imodintro
    itrivial

theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩

/-- ⊢ |={∅,⊤}=> Q is unsound in IProp (mask framing with ⊤). -/
theorem open_top_false (H0 : ∀ [InvGS_gen .hasNoLC CGF], ∃ Q : IProp CGF, ⊢ |={∅,⊤}=> Q) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ => by
      obtain ⟨Q, H⟩ := H0
      have H2 := H.trans (BIFUpdate.mono (Q := iprop(⌜(⊤ : CoPset) ## ⊤⌝ → ⌜False⌝)) (by
        iintro _ %hd
        exact absurd hd full_not_disj))
      have H3 := H2.trans (fupd_mask_frame_right_strong (E1 := ∅) (E2 := ⊤) (Ef := ⊤) (fun x ⟨h1, _⟩ => CoPset.mem_empty h1))
      have e1 : (∅ ∪ ⊤ : CoPset) = ⊤ := rfl
      have e2 : (⊤ ∪ ⊤ : CoPset) = ⊤ := rfl
      rw [e1, e2] at H3
      exact wand_intro (sep_elim_left.trans H3))

-- `Iris.atomic_acc_mask_weaken` idx 12: necessary (IProp, nil telescopes, Eo1 = Ei = ⊤, Eo2 = ∅: ⊢ |={∅,⊤}=> _ is unsound (mask framing with ⊤))
theorem w5c1_30 : ¬ drop0% Iris.atomic_acc_mask_weaken 12 := fun h =>
  open_top_false fun {_} => ⟨_, (acc_top ⊤).trans (wand_entails (@h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} ⊤ ∅ ⊤
    (fun _ => iprop(True)) iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))))⟩

end W5c1

namespace W5c1
open Iris Iris.BI Iris.OFE Iris.Std

theorem acc_gen (E : CoPset) [InvGS_gen .hasNoLC CGF] (P : IProp CGF) (Φ : Tele.Arg Tele.nil.{0} → Tele.Arg Tele.nil.{0} → IProp CGF)
    (hP : ⊢ P) (hΦ : ∀ x y, ⊢ Φ x y) :
    ⊢ atomic_acc (PROP := IProp CGF) (TA := .nil) (TB := .nil) E E
      (fun _ => iprop(True)) P (fun _ _ => iprop(True)) Φ := by
  unfold atomic_acc
  iintro
  imodintro
  iexists ⟨⟩
  isplitl
  · itrivial
  isplit
  · iintro _
    imodintro
    iapply hP
  · iintro %y _
    imodintro
    iapply (hΦ PUnit.unit y)

theorem aupd_top (E : CoPset) [InvGS_gen .hasNoLC CGF] :
    ⊢ atomic_update (PROP := IProp CGF) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) E E
      (fun _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) :=
  (and_intro true_intro true_intro).trans (aupd_intro (P := iprop(True)) (Q := iprop(True)) ((Affine.affine (P := iprop(True ∧ True))).trans (acc_top E)))

/-- ⊢ False under any IProp invariant setup is unsound. -/
theorem iprop_false (H : ∀ [InvGS_gen .hasNoLC CGF], ⊢ (iprop(⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (H.trans fupd_intro)))

-- `Iris.atomic_update_mask_weaken` idx 11: necessary (IProp, Eo1 = Ei = ⊤, Eo2 = ∅: trivial AU is provable, AU ∅ ⊤ gives ⊢ |={∅,⊤}=> _)
theorem w5c1_38 : ¬ drop0% Iris.atomic_update_mask_weaken 11 := fun h =>
  open_top_false fun {_} => ⟨_, (aupd_top ⊤).trans ((@h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} ⊤ ∅ ⊤
    (fun _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))).trans aupd_aacc)⟩

-- `Iris.aupd_intro` idx 14: necessary (IProp, P = Q = True, Eo = ∅, Ei = ⊤: AU unfolds to ⊢ |={∅,⊤}=> _)
theorem w5c1_42 : ¬ drop0% Iris.aupd_intro 14 := fun h =>
  open_top_false fun {_} => ⟨_, (and_intro true_intro true_intro).trans ((@h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} ∅ ⊤
    iprop(True) iprop(True) (fun _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) inferInstance inferInstance).trans aupd_aacc)⟩

-- `Iris.elim_mod_aupd` idx 15: necessary (IProp, φ = True, all masks ⊤, Q = False, Q' = True: trivial AU would prove False)
theorem w5c1_39 : ¬ drop0% Iris.elim_mod_aupd 15 := fun h =>
  iprop_false fun {_} => (emp_sep.2.trans (sep_mono (aupd_top ⊤) (wand_intro (sep_elim_left.trans true_intro)))).trans
    ((@h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} True .in ⊤ ⊤ ⊤ (fun _ => iprop(True)) (fun _ _ => iprop(True))
      (fun _ _ => iprop(True)) iprop(⌜False⌝) iprop(True)).elim_modal ⟨trivial, fun _ h => h⟩)

-- `Iris.elim_modal_acc` idx 17: necessary (IProp, p = false, P = True, P' = False: ⊢ atomic_acc ∅ ⊤ _ unsound)
theorem w5c1_45 : ¬ drop0% Iris.elim_modal_acc 17 := fun h =>
  open_top_false fun {_} => ⟨_, (emp_sep.2.trans (sep_mono true_intro (wand_intro (sep_elim_right.trans false_elim)))).trans
    ((@h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} false .in false True iprop(True) iprop(False) ∅ ⊤ (fun _ => iprop(True))
      iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))).elim_modal trivial)⟩

-- `Iris.tac_aupd_intro` idx 15: necessary (IProp, e = eI = eS = True, Eo = ∅, Ei = ⊤: AU unfolds to ⊢ |={∅,⊤}=> _)
theorem w5c1_52 : ¬ drop0% Iris.tac_aupd_intro 15 := fun h =>
  open_top_false fun {_} => ⟨_, true_intro.trans ((@h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} iprop(True) iprop(True) iprop(True) ∅ ⊤
    (fun _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
    ⟨emp_sep.2.trans (sep_mono_left true_intro), true_intro⟩
    ((Affine.affine (P := iprop(True))).trans (intuitionistically_emp.2.trans (intuitionistically_mono true_intro)))).trans aupd_aacc)⟩

-- `Iris.aacc_intro_wand` idx 11: necessary (IProp, Eo = ∅, Ei = ⊤, all True: atomic_acc ∅ ⊤ gives ⊢ |={∅,⊤}=> _)
theorem w5c1_57 : ¬ drop0% Iris.aacc_intro_wand 11 := fun h =>
  open_top_false fun {_} => by
    have H := @h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} ∅ ⊤ (fun _ => iprop(True)) iprop(True)
      (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) ⟨⟩
    have H2 : ⊢ atomic_acc (PROP := IProp CGF) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) ∅ ⊤ (fun _ => iprop(True))
      iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) := by
      iapply H
      · itrivial
      · isplit
        · iintro _
          imodintro
          itrivial
        · iintro %_ _
          imodintro
          itrivial
    exact ⟨_, H2⟩

end W5c1

namespace W5c1
open Iris Iris.BI Iris.OFE Iris.Std

-- `Rocq.aacc_intro` idx 11: necessary (IProp, Eo = ∅, Ei = ⊤, all True: atomic_acc ∅ ⊤ gives ⊢ |={∅,⊤}=> _)
theorem w5c1_43 : ¬ drop0% Rocq.aacc_intro 11 := fun h =>
  open_top_false fun {_} => by
    have H := @h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} ∅ ⊤ (fun _ => iprop(True)) iprop(True)
      (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
    have H2 : ⊢ atomic_acc (PROP := IProp CGF) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) ∅ ⊤ (fun _ => iprop(True))
      iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) := by
      iapply H
      · exact PUnit.unit
      · itrivial
      · isplit
        · iintro _
          imodintro
          itrivial
        · iintro %_ _
          imodintro
          itrivial
    exact ⟨_, H2⟩

-- `_private.Iris.BI.Lib.Atomic.0.Iris.aacc_intro` idx 11: necessary (IProp, Eo = ∅, Ei = ⊤, all True: atomic_acc ∅ ⊤ gives ⊢ |={∅,⊤}=> _)
theorem w5c1_44 : ¬ drop0% _private.Iris.BI.Lib.Atomic.«0».Iris.aacc_intro 11 := fun h =>
  open_top_false fun {_} => by
    have H := @h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} ∅ ⊤ (fun _ => iprop(True)) iprop(True)
      (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
    have H2 : ⊢ atomic_acc (PROP := IProp CGF) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) ∅ ⊤ (fun _ => iprop(True))
      iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) := by
      iapply H
      · exact PUnit.unit
      · itrivial
      · isplit
        · iintro _
          imodintro
          itrivial
        · iintro %_ _
          imodintro
          itrivial
    exact ⟨_, H2⟩

-- `Iris.aacc_aacc` idx 19: necessary (IProp, E1' = E2 = E3 = ⊤, E1 = ∅, all True: atomic_acc ∅ ⊤ gives ⊢ |={∅,⊤}=> _)
theorem w5c1_46 : ¬ drop0% Iris.aacc_aacc 19 := fun h =>
  open_top_false fun {_} => by
    have H := @h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} Tele.nil.{0} Tele.nil.{0} ∅ ⊤ ⊤ ⊤
      (fun _ => iprop(True)) iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
      (fun _ => iprop(True)) iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
    have H2 : ⊢ atomic_acc (PROP := IProp CGF) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) ∅ ⊤ (fun _ => iprop(True))
      iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) := by
      iapply H
      · iapply (acc_top ⊤)
      · iintro %x _
        unfold atomic_acc
        imodintro
        iexists ⟨⟩
        isplitl
        · itrivial
        isplit
        · iintro _
          imodintro
          isplitl
          · itrivial
          · iintro _
            imodintro
            itrivial
        · iintro %_ _
          imodintro
          simp only [Tele.lam, Tele.app, Tele.bind]
          ileft
          isplitl
          · itrivial
          · iintro _
            imodintro
            itrivial
    exact ⟨_, H2⟩

end W5c1

namespace W5c1
open Iris Iris.BI Iris.OFE Iris.Std

-- `Iris.aacc_aupd` idx 18: necessary (IProp, E1' = E2 = E3 = ⊤, E1 = ∅, all True)
theorem w5c1_47 : ¬ drop0% Iris.aacc_aupd 18 := fun h =>
  open_top_false fun {_} => by
    have H := @h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} Tele.nil.{0} Tele.nil.{0} ∅ ⊤ ⊤ ⊤
      (fun _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
      (fun _ => iprop(True)) iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
    have H2 : ⊢ atomic_acc (PROP := IProp CGF) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) ∅ ⊤ (fun _ => iprop(True))
      iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) := by
      iapply H
      · iapply (aupd_top ⊤)
      · iintro %x _
        unfold atomic_acc
        imodintro
        iexists ⟨⟩
        isplitl
        · itrivial
        isplit
        · iintro _
          imodintro
          isplitl
          · itrivial
          · iintro _
            imodintro
            itrivial
        · iintro %_ _
          imodintro
          simp only [Tele.lam, Tele.app, Tele.bind]
          iright
          iexists ⟨⟩
          isplitl
          · itrivial
          · iintro _
            imodintro
            itrivial
    exact ⟨_, H2⟩

-- `Iris.aacc_aupd_commit` idx 18: necessary (IProp, E1' = E2 = E3 = ⊤, E1 = ∅, all True)
theorem w5c1_48 : ¬ drop0% Iris.aacc_aupd_commit 18 := fun h =>
  open_top_false fun {_} => by
    have H := @h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} Tele.nil.{0} Tele.nil.{0} ∅ ⊤ ⊤ ⊤
      (fun _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
      (fun _ => iprop(True)) iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
    have H2 : ⊢ atomic_acc (PROP := IProp CGF) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) ∅ ⊤ (fun _ => iprop(True))
      iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) := by
      iapply H
      · iapply (aupd_top ⊤)
      · iintro %x _
        unfold atomic_acc
        imodintro
        iexists ⟨⟩
        isplitl
        · itrivial
        isplit
        · iintro _
          imodintro
          isplitl
          · itrivial
          · iintro _
            imodintro
            itrivial
        · iintro %_ _
          imodintro
          simp only [Tele.lam, Tele.app, Tele.bind]
          iexists ⟨⟩
          isplitl
          · itrivial
          · iintro _
            imodintro
            itrivial
    exact ⟨_, H2⟩

-- `Iris.aacc_aupd_abort` idx 18: necessary (IProp, E1' = E2 = E3 = ⊤, E1 = ∅, all True)
theorem w5c1_49 : ¬ drop0% Iris.aacc_aupd_abort 18 := fun h =>
  open_top_false fun {_} => by
    have H := @h (IProp CGF) _ _ Tele.nil.{0} Tele.nil.{0} Tele.nil.{0} Tele.nil.{0} ∅ ⊤ ⊤ ⊤
      (fun _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
      (fun _ => iprop(True)) iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True))
    have H2 : ⊢ atomic_acc (PROP := IProp CGF) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) ∅ ⊤ (fun _ => iprop(True))
      iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) := by
      iapply H
      · iapply (aupd_top ⊤)
      · iintro %x _
        unfold atomic_acc
        imodintro
        iexists ⟨⟩
        isplitl
        · itrivial
        isplit
        · iintro _
          imodintro
          isplitl
          · itrivial
          · iintro _
            imodintro
            itrivial
        · iintro %_ _
          imodintro
          simp only [Tele.lam, Tele.app, Tele.bind]
          isplitl
          · itrivial
          · iintro _
            imodintro
            itrivial
    exact ⟨_, H2⟩

end W5c1

namespace W5c1
open Iris Iris.BI

/-- Two-world classical propositions; persistently P := ⌜emp ⊢ P⌝ ("P holds in every world").
A discrete BI in which persistently does not commute with disjunction (no BIPersistentlyExist). -/
structure KP where p : Bool → Prop

theorem KP.ext' {P Q : KP} (h : ∀ w, P.p w ↔ Q.p w) : P = Q := by
  cases P; cases Q; congr; funext w; exact propext (h w)

instance : COFE KP := COFE.ofDiscrete _

instance kpBase : BIBase KP where
  Entails P Q := ∀ w, P.p w → Q.p w
  emp := ⟨fun _ => True⟩
  pure φ := ⟨fun _ => φ⟩
  and P Q := ⟨fun w => P.p w ∧ Q.p w⟩
  or P Q := ⟨fun w => P.p w ∨ Q.p w⟩
  imp P Q := ⟨fun w => P.p w → Q.p w⟩
  sForall Ψ := ⟨fun w => ∀ p, Ψ p → p.p w⟩
  sExists Ψ := ⟨fun w => ∃ p, Ψ p ∧ p.p w⟩
  sep P Q := ⟨fun w => P.p w ∧ Q.p w⟩
  wand P Q := ⟨fun w => P.p w → Q.p w⟩
  persistently P := ⟨fun _ => ∀ w, True → P.p w⟩
  later P := P

instance kpBI : BI KP := BI.ofPersistentlyDiscrete
  (entails_refl := fun _ h => h)
  (entails_trans := fun h1 h2 w h => h2 w (h1 w h))
  (equiv_iff := fun {P Q} => ⟨fun e => e ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h1, h2⟩ => KP.ext' fun w => ⟨h1 w, h2 w⟩⟩)
  (pure_intro := fun h _ _ => h)
  (pure_elim' := fun h w hφ => h hφ w trivial)
  (and_elim_l := fun _ h => h.1)
  (and_elim_r := fun _ h => h.2)
  (and_intro := fun h1 h2 w h => ⟨h1 w h, h2 w h⟩)
  (or_intro_l := fun _ h => .inl h)
  (or_intro_r := fun _ h => .inr h)
  (or_elim := fun h1 h2 w h => h.elim (h1 w) (h2 w))
  (imp_intro := fun h w hP hQ => h w ⟨hP, hQ⟩)
  (imp_elim := fun h w hPQ => h w hPQ.1 hPQ.2)
  (sForall_intro := fun h w hP p hp => h p hp w hP)
  (sForall_elim := fun hp _ h => h _ hp)
  (sExists_intro := fun hp _ h => ⟨_, hp, h⟩)
  (sExists_elim := fun h w ⟨p, hp, hpw⟩ => h p hp w hpw)
  (sep_mono := fun h1 h2 w h => ⟨h1 w h.1, h2 w h.2⟩)
  (emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩)
  (sep_symm := fun _ h => ⟨h.2, h.1⟩)
  (sep_assoc_l := fun _ h => ⟨h.1.1, h.1.2, h.2⟩)
  (wand_intro := fun h w hP hQ => h w ⟨hP, hQ⟩)
  (wand_elim := fun h w hPQ => h w hPQ.1 hPQ.2)
  (later_mono := fun h => h)
  (later_intro := fun _ h => h)
  (later_sForall_2 := fun _ h p hp => h _ ⟨p, rfl⟩ hp)
  (later_sExists_false := fun _ ⟨p, hp, hpw⟩ => .inr ⟨_, ⟨p, rfl⟩, hp, hpw⟩)
  (later_sep := ⟨fun _ h => h, fun _ h => h⟩)
  (later_persistently := ⟨fun _ h => h, fun _ h => h⟩)
  (later_false_em := fun _ h => .inr (fun _ => h))
  (discrete := fun h => h)
  (persistently_eq := fun _ => rfl)

def kT : KP := ⟨fun w => w = true⟩
def kF : KP := ⟨fun w => w = false⟩

-- `Iris.BI.BIPersistentlyExist.ofDiscrete` idx 2: necessary (KP two-world BI: persistently = ⌜emp ⊢ P⌝ but <pers>(kT ∨ kF) ⊬ ∃ p, <pers> p)
theorem w5c1_5 : ¬ drop0% Iris.BI.BIPersistentlyExist.ofDiscrete 2 := fun h => by
  have H := (@h KP kpBI (fun _ => rfl)).persistently_sExists_1 (fun p => p = kT ∨ p = kF) true
    (fun w _ => match w with
      | true => ⟨kT, .inl rfl, rfl⟩
      | false => ⟨kF, .inr rfl, rfl⟩)
  obtain ⟨_, ⟨p, rfl⟩, hp, hall⟩ := H
  rcases hp with rfl | rfl
  · exact Bool.false_ne_true (hall false trivial)
  · exact Bool.false_ne_true (hall true trivial).symm

end W5c1

namespace W5c1
open Iris Iris.BI Iris.OFE

/-- Up-sets on the V-shaped frame 0 ≤ 1, 0 ≤ 2 (a predicate holding at 0 holds everywhere). -/
structure VP where
  p : Fin 3 → Prop
  up : p 0 → ∀ w, p w

theorem VP.ext' {P Q : VP} (h : ∀ w, P.p w ↔ Q.p w) : P = Q := by
  cases P; cases Q; congr; funext w; exact propext (h w)

instance : COFE VP := COFE.ofDiscrete _

/-- Kripke implication on VP. -/
def VP.imp (P Q : VP) : VP :=
  ⟨fun w => if w = 0 then ∀ v, P.p v → Q.p v else (P.p w → Q.p w),
   fun h w => by
     simp only at h
     by_cases hw : w = 0
     · subst hw; simpa using h
     · simp only [if_neg hw]; exact h w⟩

theorem VP.imp_p {P Q : VP} {w} (h : (VP.imp P Q).p w) : P.p w → Q.p w := by
  unfold VP.imp at h
  by_cases hw : w = 0
  · subst hw; simp only at h; exact h 0
  · simp only [if_neg hw] at h; exact h

theorem VP.imp_mk {P Q : VP} {w} (h : ∀ v, (w = 0 ∨ v = w) → P.p v → Q.p v) : (VP.imp P Q).p w := by
  unfold VP.imp
  by_cases hw : w = 0
  · simp only [hw]; exact fun v => h v (.inl hw)
  · simp only [if_neg hw]; exact h w (.inr rfl)

/-- R ⊢ P → Q from R ∧ P ⊢ Q needs R upward closed. -/
theorem VP.imp_intro' {R P Q : VP} (h : ∀ w, R.p w ∧ P.p w → Q.p w) : ∀ w, R.p w → (VP.imp P Q).p w :=
  fun w hR => VP.imp_mk fun v hv hP => h v ⟨hv.elim (fun e => R.up (e ▸ hR) v) (fun e => e ▸ hR), hP⟩

instance vpBase : BIBase VP where
  Entails P Q := ∀ w, P.p w → Q.p w
  emp := ⟨fun _ => True, fun _ _ => trivial⟩
  pure φ := ⟨fun _ => φ, fun h _ => h⟩
  and P Q := ⟨fun w => P.p w ∧ Q.p w, fun h w => ⟨P.up h.1 w, Q.up h.2 w⟩⟩
  or P Q := ⟨fun w => P.p w ∨ Q.p w, fun h w => h.elim (fun h => .inl (P.up h w)) (fun h => .inr (Q.up h w))⟩
  imp := VP.imp
  sForall Ψ := ⟨fun w => ∀ p, Ψ p → p.p w, fun h w p hp => p.up (h p hp) w⟩
  sExists Ψ := ⟨fun w => ∃ p, Ψ p ∧ p.p w, fun ⟨p, hp, h⟩ w => ⟨p, hp, p.up h w⟩⟩
  sep P Q := ⟨fun w => P.p w ∧ Q.p w, fun h w => ⟨P.up h.1 w, Q.up h.2 w⟩⟩
  wand := VP.imp
  persistently P := ⟨fun w => P.p 1 ∧ P.p 2 ∧ P.p w, fun h w => ⟨h.1, h.2.1, P.up h.2.2 w⟩⟩
  later P := P

instance vpBI : BI VP where
  entails_refl _ h := h
  entails_trans h1 h2 w h := h2 w (h1 w h)
  equiv_iff {P Q} := ⟨fun e => e ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h1, h2⟩ => VP.ext' fun w => ⟨h1 w, h2 w⟩⟩
  and_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  or_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  imp_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  sForall_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sExists_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sep_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  wand_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  later_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  persistently_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  pure_intro h _ _ := h
  pure_elim' h w hφ := h hφ w trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 w h := ⟨h1 w h, h2 w h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 w h := h.elim (h1 w) (h2 w)
  imp_intro h := VP.imp_intro' h
  imp_elim h w hPQ := VP.imp_p (h w hPQ.1) hPQ.2
  sForall_intro h w hP p hp := h p hp w hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h w := fun ⟨p, hp, hpw⟩ => h p hp w hpw
  sep_mono h1 h2 w h := ⟨h1 w h.1, h2 w h.2⟩
  emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩
  sep_symm _ h := ⟨h.2, h.1⟩
  sep_assoc_l _ h := ⟨h.1.1, h.1.2, h.2⟩
  wand_intro h := VP.imp_intro' h
  wand_elim h w hPQ := VP.imp_p (h w hPQ.1) hPQ.2
  persistently_mono h _ hp := ⟨h 1 hp.1, h 2 hp.2.1, h _ hp.2.2⟩
  persistently_idem_2 _ hp := ⟨⟨hp.1, hp.2.1, hp.1⟩, ⟨hp.1, hp.2.1, hp.2.1⟩, hp⟩
  persistently_emp_2 _ _ := ⟨trivial, trivial, trivial⟩
  persistently_and_2 _ h := ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2.1, h.2.2.1⟩, ⟨h.1.2.2, h.2.2.2⟩⟩
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1.2.2, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h p hp := VP.imp_p (h _ ⟨p, rfl⟩) hp
  later_sExists_false _ := fun ⟨p, hp, hpw⟩ => .inr ⟨_, ⟨p, rfl⟩, hp, hpw⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr (VP.imp_mk fun _ _ hf => False.elim hf)

def vA : VP := ⟨fun w => w = 1, fun h => absurd h (by decide)⟩
def vB : VP := ⟨fun w => w = 2, fun h => absurd h (by decide)⟩

-- `Iris.BI.BIPersistentlyExist.ofDiscrete` idx 3: necessary (V-frame up-set BI VP: existential property holds, <pers> P := P₁ ∧ P₂ ∧ P does not commute with {1} ∨ {2})
theorem w5c1_6 : ¬ drop0% Iris.BI.BIPersistentlyExist.ofDiscrete 3 := fun h => by
  have H := (@h VP vpBI (fun {Ψ} he => by
      obtain ⟨p, hp, h0⟩ := he 0 trivial
      exact ⟨p, hp, fun w _ => p.up h0 w⟩)).persistently_sExists_1 (fun p => p = vA ∨ p = vB) 1
    ⟨⟨vA, .inl rfl, rfl⟩, ⟨vB, .inr rfl, rfl⟩, ⟨vA, .inl rfl, rfl⟩⟩
  obtain ⟨_, ⟨p, rfl⟩, hp, hall⟩ := H
  rcases hp with rfl | rfl
  · have e : (2 : Fin 3) = 1 := hall.2.1
    exact absurd e (by decide)
  · have e : (1 : Fin 3) = 2 := hall.1
    exact absurd e (by decide)

end W5c1

namespace W5c1
open Iris Iris.BI Iris.OFE

/-- Predicates on Nat (pointwise classical BI); persistently keeps only cofinite predicates. -/
structure CP where p : Nat → Prop

theorem CP.ext' {P Q : CP} (h : ∀ w, P.p w ↔ Q.p w) : P = Q := by
  cases P; cases Q; congr; funext w; exact propext (h w)

instance : COFE CP := COFE.ofDiscrete _

/-- P holds from some point on. -/
def CP.cof (P : CP) : Prop := ∃ N, ∀ k, N ≤ k → P.p k

instance cpBase : BIBase CP where
  Entails P Q := ∀ w, P.p w → Q.p w
  emp := ⟨fun _ => True⟩
  pure φ := ⟨fun _ => φ⟩
  and P Q := ⟨fun w => P.p w ∧ Q.p w⟩
  or P Q := ⟨fun w => P.p w ∨ Q.p w⟩
  imp P Q := ⟨fun w => P.p w → Q.p w⟩
  sForall Ψ := ⟨fun w => ∀ p, Ψ p → p.p w⟩
  sExists Ψ := ⟨fun w => ∃ p, Ψ p ∧ p.p w⟩
  sep P Q := ⟨fun w => P.p w ∧ Q.p w⟩
  wand P Q := ⟨fun w => P.p w → Q.p w⟩
  persistently P := ⟨fun w => P.cof ∧ P.p w⟩
  later P := P

instance cpBI : BI CP where
  entails_refl _ h := h
  entails_trans h1 h2 w h := h2 w (h1 w h)
  equiv_iff {P Q} := ⟨fun e => e ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h1, h2⟩ => CP.ext' fun w => ⟨h1 w, h2 w⟩⟩
  and_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  or_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  imp_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  sForall_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sExists_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sep_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  wand_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  later_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  persistently_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  pure_intro h _ _ := h
  pure_elim' h w hφ := h hφ w trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 w h := ⟨h1 w h, h2 w h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 w h := h.elim (h1 w) (h2 w)
  imp_intro h w hP hQ := h w ⟨hP, hQ⟩
  imp_elim h w hPQ := h w hPQ.1 hPQ.2
  sForall_intro h w hP p hp := h p hp w hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h w := fun ⟨p, hp, hpw⟩ => h p hp w hpw
  sep_mono h1 h2 w h := ⟨h1 w h.1, h2 w h.2⟩
  emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩
  sep_symm _ h := ⟨h.2, h.1⟩
  sep_assoc_l _ h := ⟨h.1.1, h.1.2, h.2⟩
  wand_intro h w hP hQ := h w ⟨hP, hQ⟩
  wand_elim h w hPQ := h w hPQ.1 hPQ.2
  persistently_mono h _ hp := ⟨let ⟨N, hN⟩ := hp.1; ⟨N, fun k hk => h k (hN k hk)⟩, h _ hp.2⟩
  persistently_idem_2 _ hp := ⟨let ⟨N, hN⟩ := hp.1; ⟨N, fun k hk => ⟨hp.1, hN k hk⟩⟩, hp⟩
  persistently_emp_2 _ _ := ⟨⟨0, fun _ _ => trivial⟩, trivial⟩
  persistently_and_2 _ h := ⟨let ⟨N, hN⟩ := h.1.1; let ⟨M, hM⟩ := h.2.1;
    ⟨N + M, fun k hk => ⟨hN k (by omega), hM k (by omega)⟩⟩, h.1.2, h.2.2⟩
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1.2, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h p hp := h _ ⟨p, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp, hpw⟩ => .inr ⟨_, ⟨p, rfl⟩, hp, hpw⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr (fun _ => h)

/-- Evens, or at least n: cofinite for each n, with intersection the (not cofinite) evens. -/
def evAbove (n : Nat) : CP := ⟨fun k => k % 2 = 0 ∨ n ≤ k⟩

-- `Iris.BI.BIPersistentlyForall.persistently_sForall_2` idx 2: necessary (cofinite-persistently BI CP on Nat-predicates: <pers> commutes with finite but not infinite meets (evens or ≥ n))
theorem w5c1_4 : ¬ drop0% Iris.BI.BIPersistentlyForall.persistently_sForall_2 2 := fun h => by
  have H := (@h CP cpBI (fun p => ∃ n, p = evAbove n)) 0
    (fun _ ⟨p, hp⟩ => by
      obtain ⟨q, rfl⟩ := hp
      exact fun ⟨n, e⟩ => by subst e; exact ⟨⟨n, fun k hk => .inr hk⟩, .inl rfl⟩)
  obtain ⟨⟨N, hN⟩, _⟩ := H
  have := hN (2 * N + 1) (by omega) (evAbove (2 * N + 2)) ⟨_, rfl⟩
  rcases this with h1 | h1 <;> omega

end W5c1

