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
namespace W4c5
open Iris Iris.BI Iris.Instances.Classical Iris.Instances.Data

-- helper: non-affine BI on heaps over Unit
abbrev HP := HeapProp Unit
def s1 : State Unit := fun _ => result ()
def h0 : State Unit := fun i => if i = 0 then result () else unknown
def h1 : State Unit := fun i => if i = 1 then result () else unknown
def h01 : State Unit := fun i => if i = 0 ∨ i = 1 then result () else unknown
theorem s1_ne : s1 ≠ ∅ := fun h => by have h0 := congrFun h 0; cases h0
theorem h0_ne : h0 ≠ ∅ := fun h => by have := congrFun h 0; simp [h0, EmptyCollection.emptyCollection] at this
theorem h1_ne : h1 ≠ ∅ := fun h => by have := congrFun h 1; simp [h1, EmptyCollection.emptyCollection] at this
theorem h0_ne01 : h0 ≠ h01 := fun h => by have := congrFun h 1; simp [h0, h01] at this
theorem h1_ne01 : h1 ≠ h01 := fun h => by have := congrFun h 0; simp [h1, h01] at this
theorem h01_ne : h01 ≠ ∅ := fun h => by have := congrFun h 0; simp [h01, EmptyCollection.emptyCollection] at this
theorem h01_eq : h01 = h0 ∪ h1 := by
  funext i; by_cases a : i = 0
  · subst a; simp [h0, h1, h01, Union.union]
  · by_cases b : i = 1
    · subst b; simp [h0, h1, h01, Union.union]
    · simp [h0, h1, h01, Union.union, a, b]
theorem h01_disj : h0 || h1 := fun i => by
  by_cases a : i = 0
  · subst a; simp [h1]
  · simp [h0, a]
theorem union_emp_r (σ : State Unit) : σ = σ ∪ ∅ := (union_comm.trans empty_union.symm).symm
theorem disj_emp_r (σ : State Unit) : σ || ∅ := disjoint_comm.1 empty_disjoint

/-- owns cell 0 (absorbing, not persistent, own0 ∗ own0 unsatisfiable) -/
def own0 : HP := fun σ => σ 0 ≠ unknown
theorem own0_s1 : own0 s1 := fun h => nomatch h
theorem own0_h0 : own0 h0 := fun h => nomatch h
theorem not_own0_emp : ¬ own0 ∅ := fun h => h rfl
theorem own0_sep (σ : State Unit) : ¬ iprop(own0 ∗ own0) σ := fun ⟨_, _, _, hd, a, b⟩ => (hd 0).elim a b
theorem absorb_aux (a b : State Unit) (h : b 0 ≠ unknown) : (a ∪ b) 0 ≠ unknown := by
  simp only [Union.union]; split <;> simp_all
instance own0_absorbing : Absorbing own0 := ⟨fun _ ⟨σ1, σ2, he, _, _, h2⟩ => he ▸ absorb_aux σ1 σ2 h2⟩
theorem own0_not_pers : ¬ Persistent own0 := fun h => not_own0_emp (h.persistent s1 own0_s1)

/-- empty or exactly cells 0 and 1: persistent, not absorbing -/
def e01 : HP := fun σ => σ = ∅ ∨ σ = h01
instance e01_pers : Persistent e01 := ⟨fun _ _ => Or.inl rfl⟩
/-- exactly the heap h -/
def ex (h : State Unit) : HP := fun σ => σ = h

end W4c5

namespace W4c5
open Iris Iris.BI

-- helper: affine Kripke BI on Bool worlds, sep = and, persistently = box over all worlds (no BIPersistentlyExist)
def KB : Type := Bool → Prop
instance : BIBase KB where
  Entails P Q    := ∀ w, P w → Q w
  emp          _ := True
  pure φ       _ := φ
  and P Q      w := P w ∧ Q w
  or P Q       w := P w ∨ Q w
  imp P Q      w := P w → Q w
  sForall Ψ    w := ∀ p, Ψ p → p w
  sExists Ψ    w := ∃ p, Ψ p ∧ p w
  sep P Q      w := P w ∧ Q w
  wand P Q     w := P w → Q w
  persistently P _ := ∀ w, P w
  later P      w := P w
instance : COFE KB := COFE.ofDiscrete _
instance kbBI : BI KB where
  entails_refl _ h := h
  entails_trans h1 h2 w hp := h2 w (h1 w hp)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h₁, h₂⟩ => funext fun σ => propext ⟨h₁ σ, h₂ σ⟩⟩
  and_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne           := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne         := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne        := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  pure_intro h _ _ := h
  pure_elim' h_φP σ h_φ := h_φP h_φ σ ⟨⟩
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 w hp := ⟨h1 w hp, h2 w hp⟩
  or_intro_l _ h := Or.inl h
  or_intro_r _ h := Or.inr h
  or_elim h1 h2 w h := h.elim (h1 w) (h2 w)
  imp_intro h w hp hq := h w ⟨hp, hq⟩
  imp_elim h w hpq := h w hpq.1 hpq.2
  sForall_intro h w hp p hΨ := h p hΨ w hp
  sForall_elim hΨ w h := h _ hΨ
  sExists_intro hΨ w hp := ⟨_, hΨ, hp⟩
  sExists_elim h w hex := hex.elim fun p hp => h p hp.1 w hp.2
  sep_mono h1 h2 w h := ⟨h1 w h.1, h2 w h.2⟩
  emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩
  sep_symm _ h := ⟨h.2, h.1⟩
  sep_assoc_l _ h := ⟨h.1.1, h.1.2, h.2⟩
  wand_intro h w hp hq := h w ⟨hp, hq⟩
  wand_elim h w hpq := h w hpq.1 hpq.2
  persistently_mono h _ hp w := h w (hp w)
  persistently_idem_2 _ h _ := h
  persistently_emp_2 _ _ _ := trivial
  persistently_and_2 _ h w := ⟨h.1 w, h.2 w⟩
  persistently_absorb_l _ h := h.1
  persistently_and_l w h := ⟨h.1 w, h.2⟩
  later_mono := id
  later_intro _ := id
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ => id, fun _ => id⟩
  later_persistently := ⟨fun _ => id, fun _ => id⟩
  later_false_em _ h := .inr fun _ => h
def kT : KB := fun w => w = true
def kF : KB := fun w => w = false
theorem kb_or : (iprop(<pers> (kT ∨ kF)) : KB) true := fun w => by cases w; exact Or.inr rfl; exact Or.inl rfl
theorem kb_not_or : ¬ (iprop(<pers> kT ∨ <pers> kF) : KB) true := fun h =>
  h.elim (fun h => nomatch h false) (fun h => nomatch h true)

-- helper: Bool with xor (unit o, i • i = o), equality order: UPred X2 is non-affine and not positive
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


-- helper: Probe3's AF (e unit, a absorbing, extension order): UPred AF affine, ownM a not persistent
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
abbrev oA : UPred AF := UPred.ownM AF.a
theorem af_aff : BIAffine (UPred AF) := inferInstance

-- helper: Cantor-space COFE and an escaping chain (copy of W3c1's CS / escC / hasT)
open Iris.OFE in
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
theorem h0_not_disj : ¬ (h0 || h0) := fun hd => by have := hd 0; simp [h0] at this
instance cNE (P : HP) : OFE.NonExpansive (fun _ : CS => P) := ⟨fun _ _ _ _ => .rfl⟩

end W4c5
namespace W4c5
open Iris Iris.BI Iris.Instances.Classical Iris.Instances.Data

-- `Iris.BI.intuitionistically_sep` idx 2: necessary (UPred X2, non-positive: P = Q = ownM i, i • i = o)
theorem w4c5_1 : ¬ drop0% Iris.BI.intuitionistically_sep 2 := fun h => by
  have H := (h (PROP := UPred X2) (P := oI) (Q := oI)).1 0 ⟨.o, trivial⟩ ⟨rfl, ⟨.i, .i, rfl, rfl, rfl⟩⟩
  obtain ⟨_, _, _, ⟨_, hp⟩, _⟩ := H
  cases hp

-- `Iris.BI.intuitionistically_intro_intuitionistically` idx 4: necessary (SiProp: P = True, Q = False)
theorem w4c5_2 : ¬ drop0% Iris.BI.intuitionistically_intro_intuitionistically 4 := fun h =>
  ((h (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))) 0 ⟨trivial, trivial⟩).2

-- `Iris.BI.intuitionistically_of_intuitionistic` idx 3: necessary (HeapProp: P = True, persistent, not affine)
theorem w4c5_3 : ¬ drop0% Iris.BI.intuitionistically_of_intuitionistic 3 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(True))).2 s1 trivial).1

end W4c5
namespace W4c5
open Iris Iris.BI Iris.Instances.Classical Iris.Instances.Data

-- `Iris.BI.intuitionistically_of_intuitionistic` idx 4: necessary (UPred AF affine: P = ownM a not persistent)
theorem w4c5_4 : ¬ drop0% Iris.BI.intuitionistically_of_intuitionistic 4 := fun h => by
  have H := (h (PROP := UPred AF) (P := oA)).2 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases H.2 with h | h <;> cases h

-- `Iris.BI.intuitionistic_intuitionistically_alias` idx 3: necessary (UPred AF affine: P = ownM a not persistent)
theorem w4c5_5 : ¬ drop0% Iris.BI.intuitionistic_intuitionistically_alias 3 := fun h => by
  have H := (h (PROP := UPred AF) (P := oA)).2 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases H.2 with h | h <;> cases h

-- `Iris.BI.intuitionistic_intuitionistically_alias` idx 4: necessary (HeapProp: P = True persistent, not affine)
theorem w4c5_6 : ¬ drop0% Iris.BI.intuitionistic_intuitionistically_alias 4 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(True))).2 s1 trivial).1

-- `Iris.BI.intuitionistic_alias` idx 3: necessary (UPred AF affine: P = ownM a not persistent)
theorem w4c5_7 : ¬ drop0% Iris.BI.intuitionistic_alias 3 := fun h => by
  have H := (h (PROP := UPred AF) (P := oA)) 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases H.2 with h | h <;> cases h

-- `Iris.BI.intuitionistic_alias` idx 4: necessary (HeapProp: P = True persistent, not affine)
theorem w4c5_8 : ¬ drop0% Iris.BI.intuitionistic_alias 4 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(True))) s1 trivial).1

-- `Iris.BI.intuitionistically_intro` idx 4: necessary (HeapProp: P = Q = True, not affine)
theorem w4c5_9 : ¬ drop0% Iris.BI.intuitionistically_intro 4 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(True)) (Q := iprop(True)) .rfl) s1 trivial).1

-- `Iris.BI.intuitionistically_intro` idx 5: necessary (UPred AF: P = Q = ownM a, not persistent)
theorem w4c5_10 : ¬ drop0% Iris.BI.intuitionistically_intro 5 := fun h => by
  have H := (h (PROP := UPred AF) (P := oA) (Q := oA) .rfl) 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases H.2 with h | h <;> cases h

-- `Iris.BI.intuitionistically_intro` idx 6: necessary (SiProp: P = True, Q = False)
theorem w4c5_11 : ¬ drop0% Iris.BI.intuitionistically_intro 6 := fun h =>
  ((h (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))) 0 trivial).2

-- `Iris.BI.intuitionistically_iff_persistently` idx 2: necessary (HeapProp: P = True, <pers> True is not emp)
theorem w4c5_12 : ¬ drop0% Iris.BI.intuitionistically_iff_persistently 2 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(True))).2 s1 trivial).1

-- `Iris.BI.intuitionistically_into_persistently` idx 3: necessary (HeapProp: P = True)
theorem w4c5_13 : ¬ drop0% Iris.BI.intuitionistically_into_persistently 3 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(True))).2 s1 trivial).1

-- `Iris.BI.affinelyIf_mono` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_14 : ¬ drop0% Iris.BI.affinelyIf_mono 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))) 0 trivial

-- `Iris.BI.affinelyIf_congr` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_15 : ¬ drop0% Iris.BI.affinelyIf_congr 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))).1 0 trivial

-- `Iris.BI.affinelyIf_affine` idx 4: necessary (p = false, HeapProp: P = True not affine)
theorem w4c5_16 : ¬ drop0% Iris.BI.affinelyIf_affine 4 := fun h =>
  s1_ne ((h (PROP := HP) false iprop(True)).affine s1 trivial)

-- `Iris.BI.affinelyIf_persistent` idx 4: necessary (p = false, HeapProp: P = own0 not persistent)
theorem w4c5_17 : ¬ drop0% Iris.BI.affinelyIf_persistent 4 := fun h =>
  not_own0_emp ((h (PROP := HP) false own0).persistent s1 own0_s1)

-- `Iris.BI.affinelyIf_flag_mono` idx 5: necessary (p = false, q = true, HeapProp: P = True)
theorem w4c5_18 : ¬ drop0% Iris.BI.affinelyIf_flag_mono 5 := fun h =>
  s1_ne ((h (p := false) (q := true) (PROP := HP) (P := iprop(True))) s1 trivial).1

-- `Iris.BI.affinelyIf_intro_affinelyIf` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_19 : ¬ drop0% Iris.BI.affinelyIf_intro_affinelyIf 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))) 0 trivial

-- `Iris.BI.affinelyIf_sep` idx 3: necessary (p = true, UPred X2 non-positive: P = Q = ownM i)
theorem w4c5_20 : ¬ drop0% Iris.BI.affinelyIf_sep 3 := fun h => by
  have H := (h (p := true) (PROP := UPred X2) (P := oI) (Q := oI)).1 0 ⟨.o, trivial⟩ ⟨rfl, .i, .i, rfl, rfl, rfl⟩
  obtain ⟨_, _, _, ⟨e1, p1⟩, _⟩ := H
  cases e1; cases p1

-- `Iris.BI.absorbinglyIf_mono` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_21 : ¬ drop0% Iris.BI.absorbinglyIf_mono 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))) 0 trivial

-- `Iris.BI.absorbinglyIf_congr` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_22 : ¬ drop0% Iris.BI.absorbinglyIf_congr 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))).1 0 trivial

-- `Iris.BI.absorbinglyIf_persistent` idx 4: necessary (p = false, HeapProp: P = own0 not persistent)
theorem w4c5_23 : ¬ drop0% Iris.BI.absorbinglyIf_persistent 4 := fun h =>
  not_own0_emp ((h (PROP := HP) false own0).persistent s1 own0_s1)

-- `Iris.BI.absorbinglyIf_flag_mono` idx 5: necessary (p = true, q = false, HeapProp: P = emp not absorbing)
theorem w4c5_24 : ¬ drop0% Iris.BI.absorbinglyIf_flag_mono 5 := fun h =>
  s1_ne ((h (p := true) (q := false) (PROP := HP) (P := iprop(emp))) s1
    ⟨s1, ∅, union_emp_r s1, disj_emp_r s1, trivial, rfl⟩)

-- `Iris.BI.affinelyIf_absorbinglyIf` idx 3: necessary (p = true, UPred X2 non-positive: P = ownM i)
theorem w4c5_25 : ¬ drop0% Iris.BI.affinelyIf_absorbinglyIf 3 := fun h => by
  have H := (h (p := true) (PROP := UPred X2) (P := oI)).1 0 ⟨.o, trivial⟩ ⟨rfl, .i, .i, rfl, trivial, rfl⟩
  cases H.2

-- `Iris.BI.affinely_if_absorbingly_if_elim` idx 4: necessary (p = true, UPred X2 non-positive: P = ownM i)
theorem w4c5_26 : ¬ drop0% Iris.BI.affinely_if_absorbingly_if_elim 4 := fun h => by
  have H := (h (p := true) (PROP := UPred X2) (P := oI)).1 0 ⟨.o, trivial⟩ ⟨rfl, .i, .i, rfl, trivial, rfl⟩
  cases H.2

-- `Iris.BI.persistentlyIf_mono` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_27 : ¬ drop0% Iris.BI.persistentlyIf_mono 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))) 0 trivial

-- `Iris.BI.persistentlyIf_congr` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_28 : ¬ drop0% Iris.BI.persistentlyIf_congr 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))).1 0 trivial

-- `Iris.BI.persistentlyIf_absorbing` idx 4: necessary (p = false, HeapProp: P = emp not absorbing)
theorem w4c5_29 : ¬ drop0% Iris.BI.persistentlyIf_absorbing 4 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(emp)) (p := false)).absorbing s1
    ⟨s1, ∅, union_emp_r s1, disj_emp_r s1, trivial, rfl⟩)

-- `Iris.BI.persistentlyIf_or` idx 3: necessary (p = true, Kripke BI KB with <pers> = box: P = (w = true), Q = (w = false))
theorem w4c5_30 : ¬ drop0% Iris.BI.persistentlyIf_or 3 := fun h =>
  kb_not_or ((h (p := true) (PROP := KB) (P := kT) (Q := kF)).1 true kb_or)

-- `Iris.BI.persistentlyIf_sep` idx 3: necessary (p = true, UPred X2 non-positive: P = Q = ownM i)
theorem w4c5_31 : ¬ drop0% Iris.BI.persistentlyIf_sep 3 := fun h => by
  have H := (h (p := true) (PROP := UPred X2) (P := oI) (Q := oI)).1 0 ⟨.o, trivial⟩ ⟨.i, .i, rfl, rfl, rfl⟩
  obtain ⟨_, _, _, p1, _⟩ := H
  cases p1

-- `Iris.BI.intuitionisticallyIf_mono` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_32 : ¬ drop0% Iris.BI.intuitionisticallyIf_mono 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))) 0 trivial

-- `Iris.BI.intuitionisticallyIf_congr` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_33 : ¬ drop0% Iris.BI.intuitionisticallyIf_congr 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))).1 0 trivial

-- `Iris.BI.intuitionisticallyIf_affine` idx 4: necessary (p = false, HeapProp: P = True not affine)
theorem w4c5_34 : ¬ drop0% Iris.BI.intuitionisticallyIf_affine 4 := fun h =>
  s1_ne ((h (PROP := HP) false iprop(True)).affine s1 trivial)

-- `Iris.BI.intuitionisticallyIf_flag_mono` idx 5: necessary (p = false, q = true, HeapProp: P = True)
theorem w4c5_35 : ¬ drop0% Iris.BI.intuitionisticallyIf_flag_mono 5 := fun h =>
  s1_ne ((h (p := false) (q := true) (PROP := HP) (P := iprop(True))) s1 trivial).1

-- `Iris.BI.intuitionisticallyIf_intro_intuitionisticallyIf` idx 5: necessary (p = false, SiProp: P = True, Q = False)
theorem w4c5_36 : ¬ drop0% Iris.BI.intuitionisticallyIf_intro_intuitionisticallyIf 5 := fun h =>
  (h (p := false) (PROP := SiProp) (P := iprop(True)) (Q := iprop(False))) 0 trivial

-- `Iris.BI.intuitionisticallyIf_or` idx 3: necessary (p = true, Kripke BI KB: P = (w = true), Q = (w = false))
theorem w4c5_37 : ¬ drop0% Iris.BI.intuitionisticallyIf_or 3 := fun h =>
  ((h (PROP := KB) true (P := kT) (Q := kF)).1 true ⟨trivial, kb_or⟩).elim
    (fun h => nomatch h.2 false) (fun h => nomatch h.2 true)

-- `Iris.BI.intuitionisticallyIf_sep` idx 3: necessary (p = true, UPred X2 non-positive: P = Q = ownM i)
theorem w4c5_38 : ¬ drop0% Iris.BI.intuitionisticallyIf_sep 3 := fun h => by
  have H := (h (p := true) (PROP := UPred X2) (P := oI) (Q := oI)).1 0 ⟨.o, trivial⟩ ⟨rfl, ⟨.i, .i, rfl, rfl, rfl⟩⟩
  obtain ⟨_, _, _, ⟨_, hp⟩, _⟩ := H
  cases hp

end W4c5
namespace W4c5
open Iris Iris.BI Iris.Instances.Classical Iris.Instances.Data

-- `Iris.BI.persistentlyIf_exists` idx 4: necessary (at α : Type; p = true, Kripke BI KB: Φ b = (w = b)) (universe 1: at α : Prop the claim holds)
theorem w4c5_39 : ¬ ∀ {PROP : Type} {α : Type} {p : Bool} [BI PROP] {Φ : α → PROP},
    (<pers>?p ∃ a, Φ a) ⊣⊢ ∃ a, <pers>?p Φ a := fun h => by
  have H := (h (p := true) (PROP := KB) (α := Bool) (Φ := fun b => if b then kT else kF)).1 true
    (fun w => ⟨_, ⟨w, rfl⟩, by cases w <;> rfl⟩)
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := H
  cases b
  · exact nomatch hb true
  · exact nomatch hb false

-- `Iris.BI.intuitionisticallyIf_exists` idx 4: necessary (at α : Type; p = true, Kripke BI KB: Ψ b = (w = b)) (universe 1: at α : Prop the claim holds)
theorem w4c5_40 : ¬ ∀ {PROP : Type} {α : Type} {p : Bool} [BI PROP] {Ψ : α → PROP},
    (□?p ∃ a, Ψ a) ⊣⊢ ∃ a, □?p Ψ a := fun h => by
  have H := (h (p := true) (PROP := KB) (α := Bool) (Ψ := fun b => if b then kT else kF)).1 true
    ⟨trivial, fun w => ⟨_, ⟨w, rfl⟩, by cases w <;> rfl⟩⟩
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := H
  cases b
  · exact nomatch hb.2 true
  · exact nomatch hb.2 false

-- `Iris.BI.persistent_congr` idx 4: necessary (HeapProp: P = True persistent, Q = own0 not)
theorem w4c5_41 : ¬ drop0% Iris.BI.persistent_congr 4 := fun h =>
  own0_not_pers ((h (PROP := HP) (P := iprop(True)) (Q := own0)).1 inferInstance)

-- `Iris.BI.persistently_iff` idx 3: necessary (HeapProp: P = own0 absorbing, not persistent)
theorem w4c5_42 : ¬ drop0% Iris.BI.persistently_iff 3 := fun h =>
  not_own0_emp ((h (PROP := HP) (P := own0)).2 s1 own0_s1)

-- `Iris.BI.persistently_iff` idx 4: necessary (HeapProp: P = emp persistent, not absorbing)
theorem w4c5_43 : ¬ drop0% Iris.BI.persistently_iff 4 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(emp))).1 s1 rfl)

-- `Iris.BI.persistently_intro_of_persistent` idx 4: necessary (HeapProp: P = Q = own0)
theorem w4c5_44 : ¬ drop0% Iris.BI.persistently_intro_of_persistent 4 := fun h =>
  not_own0_emp ((h (PROP := HP) (P := own0) (Q := own0) .rfl) s1 own0_s1)

-- `Iris.BI.persistently_intro_of_persistent` idx 5: necessary (HeapProp: P = True, Q = False)
theorem w4c5_45 : ¬ drop0% Iris.BI.persistently_intro_of_persistent 5 := fun h =>
  (h (PROP := HP) (P := iprop(True)) (Q := iprop(False))) s1 trivial

-- `Iris.BI.persistent_and_affinely_sep_left` idx 4: necessary (HeapProp: P = own0, Q = True)
theorem w4c5_46 : ¬ drop0% Iris.BI.persistent_and_affinely_sep_left 4 := fun h => by
  obtain ⟨_, _, _, _, ⟨e, p⟩, _⟩ := (h (PROP := HP) (P := own0) (Q := iprop(True))).1 s1 ⟨own0_s1, trivial⟩
  subst e; exact not_own0_emp p

-- `Iris.BI.persistent_and_affinely_sep_left` idx 5: necessary (HeapProp: P = emp, Q = True)
theorem w4c5_47 : ¬ drop0% Iris.BI.persistent_and_affinely_sep_left 5 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(emp)) (Q := iprop(True))).2 s1
    ⟨∅, s1, empty_union, empty_disjoint, ⟨rfl, rfl⟩, trivial⟩).1

-- `Iris.BI.persistent_and_affinely_sep_right` idx 4: necessary (HeapProp: P = True, Q = own0)
theorem w4c5_48 : ¬ drop0% Iris.BI.persistent_and_affinely_sep_right 4 := fun h => by
  obtain ⟨_, _, _, _, _, ⟨e, p⟩⟩ := (h (PROP := HP) (P := iprop(True)) (Q := own0)).1 s1 ⟨trivial, own0_s1⟩
  subst e; exact not_own0_emp p

-- `Iris.BI.persistent_and_affinely_sep_right` idx 5: necessary (HeapProp: P = True, Q = emp)
theorem w4c5_49 : ¬ drop0% Iris.BI.persistent_and_affinely_sep_right 5 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(True)) (Q := iprop(emp))).2 s1
    ⟨s1, ∅, union_emp_r s1, disj_emp_r s1, trivial, ⟨rfl, rfl⟩⟩).2

-- `Iris.BI.persistent_and_sep` idx 2: necessary (HeapProp: P = emp, Q = True)
theorem w4c5_50 : ¬ drop0% Iris.BI.persistent_and_sep 2 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(emp)) (Q := iprop(True))).2 s1
    ⟨∅, s1, empty_union, empty_disjoint, rfl, trivial⟩).1

-- `Iris.BI.imp_wand_2` idx 4: necessary (HeapProp: P = exactly h0, Q = False; P -∗ False holds at h0)
theorem w4c5_51 : ¬ drop0% Iris.BI.imp_wand_2 4 := fun h =>
  (h (PROP := HP) (P := ex h0) (Q := iprop(False))) h0
    (fun σ' hd he => by subst he; exact h0_not_disj hd) rfl

-- `Iris.BI.imp_wand` idx 2: necessary (HeapProp: P = emp, Q = False)
theorem w4c5_52 : ¬ drop0% Iris.BI.imp_wand 2 := fun h =>
  (h (PROP := HP) (P := iprop(emp)) (Q := iprop(False))).1 s1 (fun e => s1_ne e) ∅ (disj_emp_r s1) rfl

-- `Iris.BI.persistent_sep_dup_mp` idx 3: necessary (HeapProp: P = own0)
theorem w4c5_53 : ¬ drop0% Iris.BI.persistent_sep_dup_mp 3 := fun h =>
  own0_sep s1 ((h (PROP := HP) (P := own0)) s1 own0_s1)

-- `Iris.BI.persistent_sep_dup` idx 3: necessary (HeapProp: P = own0 absorbing)
theorem w4c5_54 : ¬ drop0% Iris.BI.persistent_sep_dup 3 := fun h =>
  own0_sep s1 ((h (PROP := HP) (P := own0)).1 s1 own0_s1)

-- `Iris.BI.persistent_and_sep_distrib` idx 5: necessary (HeapProp: P = own0, Q = R = True)
theorem w4c5_55 : ¬ drop0% Iris.BI.persistent_and_sep_distrib 5 := fun h => by
  obtain ⟨_, _, _, hd, ⟨a, _⟩, ⟨b, _⟩⟩ := (h (PROP := HP) (P := own0) (Q := iprop(True)) (R := iprop(True))) s1
    ⟨own0_s1, s1, ∅, union_emp_r s1, disj_emp_r s1, trivial, trivial⟩
  exact (hd 0).elim a b

-- `Iris.BI.persistent_and_sep_distrib` idx 6: necessary (HeapProp: P = empty or exactly cells 0,1; Q = exactly h0, R = exactly h1)
theorem w4c5_56 : ¬ drop0% Iris.BI.persistent_and_sep_distrib 6 := fun h => by
  obtain ⟨_, _, _, _, ⟨p, q⟩, _⟩ := (h (PROP := HP) (P := e01) (Q := ex h0) (R := ex h1)) h01
    ⟨Or.inr rfl, h0, h1, h01_eq, h01_disj, rfl, rfl⟩
  cases q; exact p.elim h0_ne h0_ne01

-- `Iris.BI.persistent_entails_right` idx 4: necessary (HeapProp: P = Q = own0)
theorem w4c5_57 : ¬ drop0% Iris.BI.persistent_entails_right 4 := fun h =>
  own0_sep s1 ((h (PROP := HP) (P := own0) (Q := own0) .rfl) s1 own0_s1)

-- `Iris.BI.persistent_entails_right` idx 5: necessary (HeapProp: P = True, Q = False)
theorem w4c5_58 : ¬ drop0% Iris.BI.persistent_entails_right 5 := fun h => by
  obtain ⟨_, _, _, _, f, _⟩ := (h (PROP := HP) (P := iprop(True)) (Q := iprop(False))) s1 trivial
  exact f

-- `Iris.BI.persistent_entails_left` idx 4: necessary (HeapProp: P = Q = own0)
theorem w4c5_59 : ¬ drop0% Iris.BI.persistent_entails_left 4 := fun h =>
  own0_sep s1 ((h (PROP := HP) (P := own0) (Q := own0) .rfl) s1 own0_s1)

-- `Iris.BI.persistent_entails_left` idx 5: necessary (HeapProp: P = True, Q = False)
theorem w4c5_60 : ¬ drop0% Iris.BI.persistent_entails_left 5 := fun h => by
  obtain ⟨_, _, _, _, _, f⟩ := (h (PROP := HP) (P := iprop(True)) (Q := iprop(False))) s1 trivial
  exact f

-- `Iris.BI.absorbingly_affinely_intro_of_persistent` idx 3: necessary (HeapProp: P = own0)
theorem w4c5_61 : ¬ drop0% Iris.BI.absorbingly_affinely_intro_of_persistent 3 := fun h => by
  obtain ⟨_, _, _, _, _, ⟨e, p⟩⟩ := (h (PROP := HP) (P := own0)) s1 own0_s1
  subst e; exact not_own0_emp p

-- `Iris.BI.imp_absorbing` idx 4: necessary (HeapProp: P = own0, Q = False)
theorem w4c5_62 : ¬ drop0% Iris.BI.imp_absorbing 4 := fun h =>
  (h (PROP := HP) own0 iprop(False)).absorbing h0
    ⟨h0, ∅, union_emp_r h0, disj_emp_r h0, trivial, not_own0_emp⟩ own0_h0

-- `Iris.BI.imp_absorbing` idx 5: necessary (HeapProp: P = empty or exactly cells 0,1 (persistent), Q = False)
theorem w4c5_63 : ¬ drop0% Iris.BI.imp_absorbing 5 := fun h =>
  (h (PROP := HP) e01 iprop(False)).absorbing h01
    ⟨h0, h1, h01_eq, h01_disj, trivial, fun p => p.elim h1_ne h1_ne01⟩ (Or.inr rfl)

-- `Iris.BI.imp_absorbing` idx 6: necessary (HeapProp: P = True, Q = emp)
theorem w4c5_64 : ¬ drop0% Iris.BI.imp_absorbing 6 := fun h =>
  s1_ne ((h (PROP := HP) iprop(True) iprop(emp)).absorbing s1
    ⟨s1, ∅, union_emp_r s1, disj_emp_r s1, trivial, fun _ => rfl⟩ trivial)

-- `Iris.BI.persistent_absorbingly_affinely` idx 3: necessary (HeapProp: P = own0)
theorem w4c5_65 : ¬ drop0% Iris.BI.persistent_absorbingly_affinely 3 := fun h => by
  obtain ⟨_, _, _, _, _, ⟨e, p⟩⟩ := (h (PROP := HP) (P := own0)).2 s1 own0_s1
  subst e; exact not_own0_emp p

-- `Iris.BI.persistent_absorbingly_affinely` idx 4: necessary (HeapProp: P = emp)
theorem w4c5_66 : ¬ drop0% Iris.BI.persistent_absorbingly_affinely 4 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(emp))).1 s1 ⟨s1, ∅, union_emp_r s1, disj_emp_r s1, trivial, ⟨rfl, rfl⟩⟩)

-- `Iris.BI.persistent_and_sep_assoc` idx 5: necessary (HeapProp: P = own0, Q = emp, R = own0)
theorem w4c5_67 : ¬ drop0% Iris.BI.persistent_and_sep_assoc 5 := fun h => by
  obtain ⟨_, _, _, _, ⟨p, e⟩, _⟩ := (h (PROP := HP) (P := own0) (Q := iprop(emp)) (R := own0)).1 h0
    ⟨own0_h0, ∅, h0, empty_union, empty_disjoint, rfl, own0_h0⟩
  subst e; exact not_own0_emp p

-- `Iris.BI.persistent_and_sep_assoc` idx 6: necessary (HeapProp: P = Q = emp, R = True)
theorem w4c5_68 : ¬ drop0% Iris.BI.persistent_and_sep_assoc 6 := fun h =>
  s1_ne ((h (PROP := HP) (P := iprop(emp)) (Q := iprop(emp)) (R := iprop(True))).2 s1
    ⟨∅, s1, empty_union, empty_disjoint, ⟨rfl, rfl⟩, trivial⟩).1

-- `Iris.BI.persistent_impl_wand_affinely` idx 4: necessary (HeapProp: P = own0, Q = False)
theorem w4c5_69 : ¬ drop0% Iris.BI.persistent_impl_wand_affinely 4 := fun h =>
  (h (PROP := HP) (P := own0) (Q := iprop(False))).2 s1
    (fun _ _ ⟨e, p⟩ => by subst e; exact not_own0_emp p) own0_s1

-- `Iris.BI.persistent_impl_wand_affinely` idx 5: necessary (HeapProp: P = emp, Q = False)
theorem w4c5_70 : ¬ drop0% Iris.BI.persistent_impl_wand_affinely 5 := fun h =>
  (h (PROP := HP) (P := iprop(emp)) (Q := iprop(False))).1 s1 (fun e => s1_ne e) ∅ (disj_emp_r s1) ⟨rfl, rfl⟩

-- `Iris.BI.from_option_persistent` idx 6: necessary (HeapProp: mx = some (), Ψ = own0)
theorem w4c5_71 : ¬ drop0% Iris.BI.from_option_persistent 6 := fun h =>
  not_own0_emp ((h (α := Unit) (PROP := HP) (P := iprop(True)) (Ψ := fun _ => own0) (mx := some ())).persistent
    s1 own0_s1)

-- `Iris.BI.from_option_persistent` idx 7: necessary (HeapProp: mx = none, P = own0)
theorem w4c5_72 : ¬ drop0% Iris.BI.from_option_persistent 7 := fun h =>
  not_own0_emp ((h (α := Unit) (PROP := HP) (P := own0) (Ψ := fun _ => iprop(True)) (mx := none)).persistent
    s1 own0_s1)

-- `Iris.BI.LimitPreserving.entails` idx 6: necessary (A = Cantor space, HeapProp: Φ x = ⌜x has no true⌝ not non-expansive, Ψ = False)
theorem w4c5_73 : ¬ drop0% Iris.BI.LimitPreserving.entails 6 := fun h =>
  ((h (PROP := HP) (A := CS) (fun x => iprop(⌜¬ hasT x⌝)) (fun _ => iprop(False))).compl escC
    (fun n _ hn => hn (hasT_esc n))) s1 not_hasT_lim

-- `Iris.BI.LimitPreserving.entails` idx 7: necessary (A = Cantor space, HeapProp: Φ = True, Ψ x = ⌜x has a true⌝ not non-expansive)
theorem w4c5_74 : ¬ drop0% Iris.BI.LimitPreserving.entails 7 := fun h =>
  not_hasT_lim (((h (PROP := HP) (A := CS) (fun _ => iprop(True)) (fun x => iprop(⌜hasT x⌝))).compl escC
    (fun n _ _ => hasT_esc n)) s1 trivial)

-- `Iris.BI.limitPreserving_emp_valid` idx 5: necessary (A = Cantor space, HeapProp: Φ x = ⌜x has a true⌝)
theorem w4c5_75 : ¬ drop0% Iris.BI.limitPreserving_emp_valid 5 := fun h =>
  not_hasT_lim (((h (PROP := HP) (A := CS) (fun x => iprop(⌜hasT x⌝))).compl escC
    (fun n _ _ => hasT_esc n)) ∅ rfl)

-- `Iris.BI.limitPreserving_persistent` idx 5: necessary (A = Cantor space, HeapProp: Φ x = ⌜x has a true⌝ ∨ own0)
theorem w4c5_76 : ¬ drop0% Iris.BI.limitPreserving_persistent 5 := fun h =>
  (((h (PROP := HP) (A := CS) (fun x σ => hasT x ∨ own0 σ)).compl escC
    (fun n => ⟨fun _ _ => Or.inl (hasT_esc n)⟩)).persistent s1 (Or.inr own0_s1)).elim not_hasT_lim not_own0_emp

-- `Iris.BI.limitPreserving_absorbing` idx 5: necessary (A = Cantor space, HeapProp: Φ x = ⌜x has a true⌝ ∨ emp)
theorem w4c5_77 : ¬ drop0% Iris.BI.limitPreserving_absorbing 5 := fun h =>
  (((h (PROP := HP) (A := CS) (fun x σ => hasT x ∨ σ = ∅)).compl escC
    (fun n => ⟨fun _ _ => Or.inl (hasT_esc n)⟩)).absorbing s1
    ⟨s1, ∅, union_emp_r s1, disj_emp_r s1, trivial, Or.inr rfl⟩).elim not_hasT_lim s1_ne

-- `Iris.BI.limitPreserving_affine` idx 5: necessary (A = Cantor space, HeapProp: Φ x = emp ∨ ⌜x has no true⌝)
theorem w4c5_78 : ¬ drop0% Iris.BI.limitPreserving_affine 5 := fun h =>
  s1_ne (((h (PROP := HP) (A := CS) (fun x σ => σ = ∅ ∨ ¬ hasT x)).compl escC
    (fun n => ⟨fun _ hσ => hσ.elim id (fun h' => (h' (hasT_esc n)).elim)⟩)).affine s1 (Or.inr not_hasT_lim))

-- `Iris.BI.iter_modal_intro` idx 5: necessary (HeapProp: M = const False, n = 1, P = True)
theorem w4c5_79 : ¬ drop0% Iris.BI.iter_modal_intro 5 := fun h =>
  (h (PROP := HP) (fun _ => iprop(False)) 1 (P := iprop(True))) s1 trivial

-- `Iris.BI.iter_modal_mono` idx 6: necessary (HeapProp: M X = (X → False), n = 1, P = False, Q = True)
theorem w4c5_80 : ¬ drop0% Iris.BI.iter_modal_mono 6 := fun h =>
  (h (PROP := HP) (fun X => iprop(X → False)) 1 (P := iprop(False)) (Q := iprop(True))) s1
    (fun _ _ _ => trivial) ∅ (disj_emp_r s1) (fun f => f) trivial

-- `Iris.BI.bi_emp_valid_mono` idx 4: necessary (HeapProp: P = True, Q = False)
theorem w4c5_81 : ¬ drop0% Iris.BI.bi_emp_valid_mono 4 := fun h =>
  (h (PROP := HP) (P := iprop(True)) (Q := iprop(False)) (fun _ _ => trivial)) ∅ rfl

-- `Iris.BI.bi_emp_valid_mono` idx 5: necessary (HeapProp: P = Q = False)
theorem w4c5_82 : ¬ drop0% Iris.BI.bi_emp_valid_mono 5 := fun h =>
  (h (PROP := HP) (P := iprop(False)) (Q := iprop(False)) .rfl) ∅ rfl

-- `Iris.BI.bi_emp_valid_flip_mono` idx 4: necessary (HeapProp: P = True, Q = False)
theorem w4c5_83 : ¬ drop0% Iris.BI.bi_emp_valid_flip_mono 4 := fun h =>
  (h (PROP := HP) (P := iprop(True)) (Q := iprop(False))).1 (fun _ _ => trivial) ∅ rfl

end W4c5
namespace W4c5
open Iris Iris.BI

-- helper: e unit, a • a = b invalid, b absorbing; order x = e ∨ x = y ∨ y = b: UPred AX affine, ownM a -∗ False holds at a
inductive AX | e | a | b deriving DecidableEq
def AX.op : AX → AX → AX
  | .e, y => y
  | .a, .e => .a
  | _, _ => .b
instance : OFE AX := OFE.ofDiscrete AX
instance : OFE.Discrete AX := ⟨id⟩
instance instORAAX : ORA AX := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := AX.op
  Valid := fun x => x ≠ .b
  Order := fun x y => x = .e ∨ x = y ∨ y = .b
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y h; cases x <;> cases y <;> simp_all [AX.op]
  ord_trans := by intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all
  op_mono_left := by intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [AX.op]
  valid_of_ord := by intro x y h1 h2; cases x <;> cases y <;> simp_all
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; exact .inl rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; exact .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact .inr (.inl rfl)
  increasing_closed := by intro x y hx h z; cases x <;> cases y <;> cases z <;> simp_all [AX.op] }
instance : OrderRefl AX := ⟨fun x => show x = .e ∨ x = x ∨ x = .b from .inr (.inl rfl)⟩
instance instUORAAX : UORA AX where
  unit := .e
  unit_valid := by show AX.e ≠ AX.b; decide
  unit_left_id := rfl
  pcore_unit := rfl
instance : IncOrd AX := ⟨by
  intro x y ⟨z, hz⟩
  show x = .e ∨ x = y ∨ y = .b
  cases x <;> cases z <;> simp_all [Op.op, AX.op]⟩
abbrev oX : UPred AX := UPred.ownM AX.a
theorem ax_aff : BIAffine (UPred AX) := inferInstance

-- `Iris.BI.imp_wand` idx 5: necessary (affine UPred AX: P = ownM a with a • a invalid, Q = False; P -∗ False holds at a, P → False does not)
theorem w4c5_84 : ¬ drop0% Iris.BI.imp_wand 5 := fun h =>
  (h (PROP := UPred AX) (P := oX) (Q := iprop(False))).2 0 ⟨.a, by show AX.a ≠ AX.b; decide⟩
    (fun n' x' _ hv hp => by
      have hv' : AX.op AX.a x' ≠ AX.b := hv
      have hp' : AX.a = .e ∨ AX.a = x' ∨ x' = AX.b := hp
      cases x' <;> simp_all [AX.op])
    (n' := 0) ⟨.a, by show AX.a ≠ AX.b; decide⟩ (.inr (.inl rfl)) (Nat.le_refl 0) (.inr (.inl rfl))

end W4c5
