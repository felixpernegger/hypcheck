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
namespace Probe3
open Iris Iris.BI

/-- Two-element commutative monoid (e unit, a idempotent) with the equality order: a non-affine UORA. -/
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


/-- Two-element monoid (e unit, a absorbing) with the extension order: an affine UORA. -/
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

example : BIAffine (UPred AF) := inferInstance

/-- Toy language: expressions `Nat`, `0` is the only value, `1` is stuck, `2` steps to itself and forks a thread `2`. -/
instance tlToVal : Iris.ProgramLogic.ToVal Nat Unit where
  toVal n := if n = 0 then some () else none
  ofVal _ := 0
  coe_of_toVal_eq_some {e v} h := by cases e <;> simp_all
  toVal_coe _ := rfl

instance tlLang : Iris.ProgramLogic.Language Nat Unit Unit Unit where
  primStep c _ c' := c.1 = 2 ∧ c'.2.2 = [2]
  val_stuck {e} := by intro _ _ _ _ _ ⟨h, _⟩; simp only at h; subst h; rfl

open Iris.ProgramLogic in
theorem tl_rtc1 {c : List Nat × Unit} :
    FromMathlib.Relation.ReflTransGen Language.ErasedStep ([1], ()) c → c = ([1], ()) := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨_, hs⟩ := hs
    generalize hb : (([1] : List Nat), ()) = b at hs
    cases hs with
    | @atomic e σ obs e' σ' eₜ H t₁ t₂ =>
      obtain ⟨he, _⟩ := H
      have h1 : [1] = t₁ ++ e :: t₂ := congrArg Prod.fst hb
      have hm : e ∈ t₁ ++ e :: t₂ := List.mem_append_right t₁ List.mem_cons_self
      rw [← h1] at hm
      simp at hm he
      omega

open Iris.ProgramLogic in
/-- From the stuck expression `1` nothing is reachable, so the toy language is adequate for any postcondition. -/
theorem tl_adeq (φ : Unit → Unit → Prop) : AdequateNoFork .MaybeStuck (1 : Nat) () φ where
  no_fork h := by have := congrArg Prod.fst (tl_rtc1 h); simp at this; simp [this]
  result h := by have := tl_rtc1 h; simp [ToVal.ofVal] at this
  not_stuck hs := by cases hs

/-- Index Nat with its order. -/
abbrev NatIdx : BiIndex := { car := Nat, rel := inferInstance }

/-- Monotone predicate that is `⌜1 ≤ i⌝` at index `i`: not objective. -/
def stepPred (PROP : Type) [BI PROP] : MonPred NatIdx PROP :=
  ⟨fun (i : Nat) => iprop(⌜1 ≤ i⌝), fun h => pure_mono fun h' => Nat.le_trans h' h⟩


/-- Constant fractional predicate `emp`. -/
theorem empFrac {PROP : Type} [BI PROP] : Fractional (fun _ : Qp => (iprop(emp) : PROP)) := ⟨fun _ _ => emp_sep.symm⟩
/-- Three distinct masks. -/
def mk0 : CoPset := CoPset.full
def mk1 : CoPset := ⟨.leaf false, rfl⟩
def mk2 : CoPset := CoPset.singleton .xH

/-- A reflexive, non-transitive relation on masks: `mk0 → mk1 → mk2` but not `mk0 → mk2`. -/
def vcond (E1 E2 : CoPset) : Prop := E1 = E2 ∨ (E1 = mk0 ∧ E2 = mk1) ∨ (E1 = mk1 ∧ E2 = mk2)

theorem not_vcond02 : ¬ vcond mk0 mk2 := by
  intro h
  rcases h with h | ⟨_, h⟩ | ⟨h, _⟩ <;> have := congrArg CoPset.tree h <;> revert this <;> decide

/-- View shifts on `UPred AF` given by `vcond`, or trivially true when the precondition is unsatisfiable. -/
def vsM (E1 E2 : CoPset) (P _Q : UPred AF) : UPred AF := iprop(⌜vcond E1 E2 ∨ (P ⊢ False)⌝)

open COFE
/-- Slot 1 (disjoint sets of masks) of the closed-proofs GF as an `ElemG`. -/
instance elem1 : ElemG Iris.Examples.ClosedProofs.GF (constOF CoPsetDisjL) where
  τ := 1
  transp := by unfold Iris.Examples.ClosedProofs.GF; rfl

/-- Owning the invalid element under an update is contradictory. -/
theorem bupd_own_error_false (γ : GName)
    (H : ⊢ |==> iOwn (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL) γ .error) : False :=
  UPred.bupd_soundness (H.trans (BIUpdate.mono iOwn_cmraValid)) 0 ⟨UORA.unit, UORA.unit_valid.validN⟩
    (OrderRefl.ord_refl _ |> Ordered.ordN_of_ord 0)

theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩

set_option linter.deprecated false in
/-- Owning `valid ⊤` twice at the same name is contradictory. -/
theorem own_full_dup_false (γ : GName) :
    iOwn (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL) γ (.valid CoPset.full) ∗
    iOwn (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL) γ (.valid CoPset.full) ⊢ iprop(⌜False⌝) :=
  iOwn_cmraValid_op.trans fun n x h => by
    have h' : ✓{n} ((DisjointLeibnizSet.valid CoPset.full : CoPsetDisjL) • DisjointLeibnizSet.valid CoPset.full) := h
    change ✓{n} (if CoPset.full ## CoPset.full then _ else _) at h'
    rw [if_neg full_not_disj] at h'
    exact h'
/-- Every slot is the mono-nat functor. -/
def GFmn : BundledGFunctors := fun _ => ⟨MonoNatRF⟩

instance monoZG_GFmn : MonoZG GFmn where
  natG := { elem := { τ := 0, transp := rfl }, name := 0 }

/-- An update to `⌜False⌝` cannot be valid. -/
theorem bupd_false_unsound {GF : BundledGFunctors} (H : ⊢ (|==> iprop(⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF) (UPred.bupd_soundness H)

/-- Every slot is the mono-list functor over `Unit`. -/
def GFml : BundledGFunctors := fun _ => ⟨constOF (MonoList (DiscreteO Unit))⟩

instance monoListG_GFml : MonoListG GFml Unit where
  elem := { τ := 0, transp := rfl }
/-- Fancy update for the leak model: identity on equal masks, `True` otherwise. -/
def lfupd (E1 E2 : Iris.Linear.Mask) (Q : UPred NA) : UPred NA := if E1 = E2 then Q else iprop(True)

theorem lfupd_mono {E1 E2 : Iris.Linear.Mask} {P Q : UPred NA} (h : P ⊢ Q) : lfupd E1 E2 P ⊢ lfupd E1 E2 Q := by
  unfold lfupd
  split
  · exact h
  · exact .rfl

theorem lfupd_frame {E1 E2 : Iris.Linear.Mask} {P Q : UPred NA} : P ∗ lfupd E1 E2 Q ⊢ lfupd E1 E2 iprop(P ∗ Q) := by
  unfold lfupd
  split
  · exact .rfl
  · exact true_intro

theorem lfupd_alloc {E : Iris.Linear.Mask} (P : UPred NA) :
    ▷ P ⊢ lfupd E E iprop(∃ _γ : Unit, iprop(True) ∗ iprop(True)) := by
  unfold lfupd
  rw [if_pos rfl]
  exact true_intro.trans (emp_sep.mpr.trans ((sep_mono_left true_intro).trans
    (exists_intro (Ψ := fun _ : Unit => iprop(True ∗ True)) ())))

theorem lfupd_acc (P : UPred NA) :
    ⊢ iprop(True) -∗ iprop(True) -∗ lfupd .M1 .M0 iprop(▷ P ∗ True ∗ (▷ P -∗ lfupd .M0 .M1 iprop(emp))) := by
  unfold lfupd
  rw [if_neg (by decide)]
  exact wand_intro (wand_intro true_intro)
/-- Resource with a valid entry at name 0 and an invalid one at name 1 in slot 1. -/
noncomputable def mzBad : IResUR Iris.Examples.ClosedProofs.GF := fun τ' =>
  if h : τ' = 1 then h ▸ (show GenMap ((Iris.Examples.ClosedProofs.GF 1).F (IPre Iris.Examples.ClosedProofs.GF) (IPre Iris.Examples.ClosedProofs.GF)) from
    ⟨fun k => if k = 0 then some (DisjointLeibnizSet.valid ∅ : CoPsetDisjL) else if k = 1 then some (DisjointLeibnizSet.error : CoPsetDisjL) else none,
     ⟨2, fun k hk => by
       have h0 : k ≠ 0 := by omega
       have h1 : k ≠ 1 := by omega
       rw [if_neg h0, if_neg h1]⟩⟩) else GenMap.empty

theorem empty_disj : (∅ : CoPset) ## ∅ := fun _ ⟨h1, _⟩ => CoPset.mem_empty h1
/-- Every slot is the agreement algebra over the non-discrete OFE `SiProp`. -/
def GFag : BundledGFunctors := fun _ => ⟨constOF (Agree SiProp)⟩

instance elemAg : ElemG GFag (constOF (Agree SiProp)) := { τ := 0, transp := rfl }

/-- `n = 0` and `True` agree at level 0 but differ. -/
def sp0 : SiProp := { holds := fun n => n = 0, closed := fun h hle => by omega }
def sp1 : SiProp := { holds := fun _ => True, closed := fun h _ => h }

theorem sp_dist0 : sp0 ≡{0}≡ sp1 := by
  intro m hm
  exact ⟨fun _ => trivial, fun _ => by show m = 0; omega⟩

theorem sp_ne : sp0 ≠ sp1 := fun e => by
  have : sp0.holds 1 = sp1.holds 1 := congrArg (·.holds 1) e
  have h1 : sp1.holds 1 := trivial
  rw [← this] at h1
  have h2 : (1 : Nat) = 0 := h1
  exact absurd h2 (by decide)
/-- Owning `valid ⊤` at some name is not valid in the empty context. -/
theorem own_full_not_valid
    (H : ⊢ iprop(∃ γ, iOwn (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL) γ (DisjointLeibnizSet.valid CoPset.full))) :
    False :=
  pure_soundness (PROP := IProp Iris.Examples.ClosedProofs.GF)
    ((persistently_emp_intro.trans (persistently_mono H)).trans
      (persistently_exists.mp.trans (exists_elim fun γ =>
        persistently_sep_persistently.mpr.trans ((sep_mono persistently_elim persistently_elim).trans (own_full_dup_false γ)))))
end Probe3

open Iris Iris.BI Probe3 COFE


-- `Iris.BI.and_plain` idx 5: necessary (UPred NA, P = True, Q = ownM a)
theorem p3_21 : ¬ drop0% Iris.BI.and_plain 5 := fun h => by
  have H := (@h (UPred NA) _ iprop(True) (UPred.ownM .a) (pure_plain True)).plain 0 ⟨.a, trivial⟩ ⟨trivial, rfl⟩
  cases H.2

-- `Iris.BI.exists_plain` idx 4: necessary (UPred NA, Ψ _ = ownM a)
theorem p3_22 : ¬ drop0% Iris.BI.exists_plain 4 := fun h => by
  have H := (@h (UPred NA) _ True (fun _ => UPred.ownM .a)).plain 0 ⟨.a, trivial⟩ ⟨_, ⟨trivial, rfl⟩, rfl⟩
  obtain ⟨_, ⟨_, rfl⟩, hp⟩ := H
  cases hp

-- `Iris.BI.bigSepL2_plainly` idx 2: necessary (non-affine UPred NA, empty lists: ■ emp does not entail emp)
theorem p3_20 : ¬ drop0% Iris.BI.bigSepL2_plainly 2 := fun h => by
  have H := (@h (UPred NA) _ Unit Unit (fun _ _ _ => iprop(emp)) [] []).mp 0 ⟨.a, trivial⟩ rfl
  cases H

-- `Iris.BI.plainly_sep_entails_homomorphism` idx 2: removable (map_unit is plainly_emp_intro, which needs no affinity)
theorem p3_19 : drop% Iris.BI.plainly_sep_entails_homomorphism 2 := fun {PROP} _ =>
  { plainly_sep_entails_weak_homomorphism with map_unit := plainly_emp_intro }

-- `Iris.BI.and_intuitionistic` idx 5: necessary (affine UPred AF, P = emp, Q = ownM a)
theorem p3_1 : ¬ drop0% Iris.BI.and_intuitionistic 5 := fun h => by
  have H := (@h (UPred AF) _ iprop(emp) (UPred.ownM .a) inferInstance).intuitionistic 0 ⟨.a, trivial⟩ ⟨.inl rfl, .inr rfl⟩
  obtain ⟨_, _, h2⟩ := H
  rcases h2 with h2 | h2 <;> cases h2


-- `Iris.BI.MonPred.exists_objective` idx 5: necessary (SiProp, index Nat, Φ _ = ⌜1 ≤ i⌝)
theorem p3_16 : ¬ drop0% Iris.BI.MonPred.exists_objective 5 := fun h => by
  have H := (@h NatIdx SiProp _ True (fun _ => stepPred SiProp)).objective_at (1 : Nat) (0 : Nat)
  have H2 := ((MonPred.monPred_at_exist (I := NatIdx) (1 : Nat) _).mpr.trans (H.trans (MonPred.monPred_at_exist (I := NatIdx) (0 : Nat) _).mp)) 0 ⟨_, ⟨trivial, rfl⟩, Nat.le_refl 1⟩
  obtain ⟨_, ⟨_, rfl⟩, h3⟩ := H2
  exact Nat.not_succ_le_zero 0 h3

-- `Iris.BI.MonPred.bupd_objective` idx 5: necessary (UPred NA, index Nat, P = ⌜1 ≤ i⌝)
theorem p3_17 : ¬ drop0% Iris.BI.MonPred.bupd_objective 5 := fun h => by
  have H := (@h NatIdx (UPred NA) _ _ (stepPred (UPred NA))).objective_at (1 : Nat) (0 : Nat) 0 ⟨.e, trivial⟩
    (fun k yf _ _ => ⟨.e, trivial, Nat.le_refl 1⟩)
  obtain ⟨_, _, h3⟩ := H 0 .e (Nat.le_refl 0) trivial
  exact Nat.not_succ_le_zero 0 h3

-- `Iris.BI.MonPred.monPred_at_plain` idx 4: necessary (UPred NA, constant predicate ownM a)
theorem p3_18 : ¬ drop0% Iris.BI.MonPred.monPred_at_plain 4 := fun h => by
  have H := (@h NatIdx (UPred NA) _ ⟨fun _ => UPred.ownM .a, fun _ => .rfl⟩ (0 : Nat)).plain 0 ⟨.a, trivial⟩ rfl
  cases H


-- `Iris.fromSepFractional` idx 6: necessary (SiProp, P = False, Φ _ = True)
theorem p3_8 : ¬ drop0% Iris.fromSepFractional 6 := fun h => by
  have H := (@h SiProp _ iprop(False) (fun _ => iprop(True)) 1 1).from_sep 0 ⟨trivial, trivial⟩
  exact H


-- `Iris.fractional_split` idx 10: necessary (SiProp, P = False, P1 = P2 = emp, Φ _ = emp)
theorem p3_7 : ¬ drop0% Iris.fractional_split 10 := fun h => by
  have H := (@h SiProp _ iprop(False) iprop(emp) iprop(emp) (fun _ => iprop(emp)) 1 1 .out .out
    ⟨.rfl, empFrac⟩ ⟨.rfl, empFrac⟩).mpr 0 ⟨trivial, trivial⟩
  exact H

-- `Iris.combineSepAsFractional` idx 8: necessary (non-affine UPred NA, P1 = Φ _ = emp, P2 = True)
theorem p3_9 : ¬ drop0% Iris.combineSepAsFractional 8 := fun h => by
  have H := (@h (UPred NA) _ iprop(emp) iprop(True) (fun _ => iprop(emp)) 1 1
    ⟨.rfl, empFrac⟩).combine_sep_as 0 ⟨.a, trivial⟩ ⟨.e, .a, rfl, rfl, trivial⟩
  cases H

-- `Iris.fractional_bigSepL2` idx 7: necessary (SiProp, one-element lists, Ψ q = ⌜q = 1⌝, p = q = 1)
theorem p3_10 : ¬ drop0% Iris.fractional_bigSepL2 7 := fun h => by
  have H := (@h SiProp _ Unit Unit [()] [()] (fun _ _ _ q => iprop(⌜q.val = 1⌝))).fractional 1 1
  have H2 := H.mpr 0 ⟨⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩
  obtain ⟨h1, _⟩ := H2
  have h2 : ((1 : Qp) + 1).val = 1 := h1
  have h3 : (1 : Rat) + 1 = 1 := h2
  grind

-- `UPred.intoAnd_ownM` idx 8: necessary (UPred NA, a = a, b1 = e, b2 = a, p = false)
theorem p3_44 : ¬ drop0% UPred.intoAnd_ownM 8 := fun h => by
  have H := (@h NA _ false .a .e .a ⟨rfl⟩ ⟨fun _ => rfl⟩).into_and 0 ⟨.a, trivial⟩ rfl
  cases H.1

-- `Iris.HeapLang.toVal_erase_none` idx 1: necessary (e a value)
theorem p3_29 : ¬ drop0% Iris.HeapLang.toVal_erase_none 1 := fun h => by
  have H := @h (.val (.lit .unit))
  simp [Iris.ProgramLogic.ToVal.toVal] at H


-- `Iris.ProgramLogic.AdequateNoFork.result` idx 13: necessary (toy language, stuck e₁ = 1, φ = False)
theorem p3_47 : ¬ drop0% Iris.ProgramLogic.AdequateNoFork.result 13 := fun h =>
  @h Nat Unit Unit Unit _ _ 1 () (fun _ _ => False) (tl_adeq _) [] () ()

-- `Iris.ProgramLogic.adequateNoFork_efs_nil` idx 14: necessary (toy language, unreachable forking expression 2)
theorem p3_48 : ¬ drop0% Iris.ProgramLogic.adequateNoFork_efs_nil 14 := fun h => by
  have H := @h Nat Unit Unit Unit _ 1 () .MaybeStuck (fun _ _ => False) (tl_adeq _) [1] () 2 .refl [] 2 () [2] ⟨rfl, rfl⟩
  cases H


-- `Iris.fupd_finally_soundness` idx 6: necessary (GF of the closed-proofs example, P = False, pure soundness)
theorem p3_40 : ¬ drop0% Iris.fupd_finally_soundness 6 := fun h =>
  pure_soundness (PROP := IProp Iris.Examples.ClosedProofs.GF)
    (@h Iris.Examples.ClosedProofs.GF .hasNoLC _ 0 ∅ iprop(⌜False⌝))

-- `Iris.ProgramLogic.wp_adequacy_gen` idx 12: necessary (toy language, value e = 0, φ = False)
theorem p3_49 : ¬ drop0% Iris.ProgramLogic.wp_adequacy_gen 12 := fun h =>
  (@h .hasNoLC Nat Unit Unit Unit _ Iris.Examples.ClosedProofs.GF _ .MaybeStuck 0 () (fun _ => False)).adequate_result
    [] () () .refl

-- `Iris.Inv.saved_alloc` idx 12: necessary (SiProp, fupd = id, inv = False, start = True)
theorem p3_2 : ¬ drop0% Iris.Inv.saved_alloc 12 := fun h => by
  have H := @h SiProp _ _ (fun _ P => P) Unit (fun _ _ => iprop(False)) (fun _ _ => inferInstance)
    .rfl id .rfl .rfl .rfl Unit (fun _ => iprop(True)) (fun _ => iprop(True))
    (fun _ _ => ⟨_, ⟨(), rfl⟩, trivial⟩) (fun _ => iprop(True)) 0 trivial
  obtain ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, H'⟩ := H
  exact H'

-- `Iris.fupd_vs_trans` idx 12: removable (the library proof without the final vs_impl step)
theorem p3_43 : drop% Iris.fupd_vs_trans 12 := by
  intro M _ vs _ E1 E2 E3 P _ vs_trans vs_exists vs_persistent_intro_r
  simp only [fupd_vs]
  iintro ⟨%R, HR, Hvs⟩
  iexists R
  iframe HR
  iapply vs_trans $$ [$Hvs]
  clear R
  iapply vs_exists
  iintro %R
  iapply vs_persistent_intro_r
  iintro Hvs
  iexact Hvs


-- `Iris.fupd_vs_trans` idx 9: necessary (UPred AF, vs = vsM: all other laws hold, masks mk0 → mk1 → mk2)
theorem p3_42 : ¬ drop0% Iris.fupd_vs_trans 9 := fun h => by
  have H := @h AF _ vsM _ mk0 mk1 mk2 iprop(emp) (fun {_ _ _ _} => by unfold vsM; infer_instance)
    (fun {A} E1 E2 Φ Q n x hx => by
      by_cases hc : vcond E1 E2
      · exact .inl hc
      · refine .inr (exists_elim fun a => ?_)
        rcases hx _ ⟨a, rfl⟩ with h | h
        · exact absurd h hc
        · exact h)
    (fun E1 E2 P Q R _ n x hw => by
      by_cases hc : vcond E1 E2
      · exact .inl hc
      · refine .inr fun n' y hPR => ?_
        obtain ⟨x1, x2, Hx, hP, hR⟩ := hPR
        rcases hw 0 x2 (Nat.zero_le _) trivial (R.mono hR (Ordered.ordN_of_ord _ (OrderRefl.ord_refl _)) (Nat.zero_le _)) with h | h
        · exact absurd h hc
        · exact (h n' _ hP).elim)
    (fun E P Q n x _ => .inl (.inl rfl))
    0 ⟨.e, trivial⟩ ⟨_, ⟨iprop(emp), rfl⟩, .e, .e, .inl rfl, .inl rfl, .inl (.inr (.inl ⟨rfl, rfl⟩))⟩
  obtain ⟨_, ⟨R, rfl⟩, x1, x2, _, hR, hc⟩ := H
  rcases hc with hc | hc
  · exact not_vcond02 hc
  · exact hc _ _ hR

set_option linter.deprecated false in
-- `Rocq.heap_lang.erased_base_step_base_step_CmpXchg` idx 6: necessary (empty heap: cmpXchg cannot step)
theorem p3_30 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_CmpXchg 6 := fun h => by
  obtain ⟨κ, e2, σ2, efs, hs, _⟩ := h default (.lit .unit) (.lit .unit) ⟨(∅ : Iris.HeapLang.HeapF (Option Iris.HeapLang.Val)), default⟩ (.lit .unit) true rfl rfl
  cases hs
  rename_i hg _
  have := Iris.Std.get?_empty (M := Iris.HeapLang.HeapF) (V := Option Iris.HeapLang.Val) (default : Iris.HeapLang.Loc)
  simp only [Iris.HeapLang.State.get?] at hg
  rw [this] at hg
  cases hg

-- `_private.Iris.ProgramLogic.AbstractLangCompleteness.0.Iris.ProgramLogic.bigSepL_const_congr` idx 6: necessary (l1 = [()], l2 = [], P = False)
theorem p3_45 : ¬ drop0% _private.Iris.ProgramLogic.AbstractLangCompleteness.«0».Iris.ProgramLogic.bigSepL_const_congr 6 :=
  fun h => pure_soundness (PROP := IProp Iris.Examples.ClosedProofs.GF)
    ((@h Iris.Examples.ClosedProofs.GF Unit Unit iprop(⌜False⌝) [()] []).mpr.trans false_sep.mp)

-- `Iris.IProp.validN_unfoldi_mp` idx 4: necessary (closed-proofs GF, slot 1 = disjoint sets, the invalid element)
theorem p3_33 : ¬ drop0% Iris.IProp.validN_unfoldi_mp 4 := fun h => by
  have H := @h Iris.Examples.ClosedProofs.GF 1 0 (show CoPsetDisjL from .error)
  exact H

-- `Iris.iOwn_unit` idx 6: necessary (closed-proofs GF slot 1, ε = invalid element)
theorem p3_36 : ¬ drop0% Iris.iOwn_unit 6 := fun h =>
  bupd_own_error_false 0 (@h Iris.Examples.ClosedProofs.GF (constOF CoPsetDisjL) _ elem1 0 .error)

-- `Iris.iOwn_ord_mono` idx 7: necessary (closed-proofs GF slot 1, a1 = unit, a2 = invalid element)
theorem p3_34 : ¬ drop0% Iris.iOwn_ord_mono 7 := fun h =>
  bupd_own_error_false 0 ((iOwn_unit (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL) (γ := 0) (ε := UORA.unit)).trans
    (BIUpdate.mono (@h Iris.Examples.ClosedProofs.GF (constOF CoPsetDisjL) _ elem1 0 UORA.unit .error)))

-- `Iris.fupd_soundness` idx 7: necessary (P = ∃ γ, own γ (valid ⊤) is obtained by allocation but is not valid: ⊢ P would make it persistent, hence duplicable)
theorem p3_41 : ¬ drop0% Iris.fupd_soundness 7 := fun h => by
  have H := @h Iris.Examples.ClosedProofs.GF .hasNoLC _ 0 ⊤ ⊤
    iprop(∃ γ, iOwn (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL) γ (DisjointLeibnizSet.valid CoPset.full))
    (fun _ => by
      iintro _
      imod iOwn_alloc (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL)
        (DisjointLeibnizSet.valid CoPset.full) trivial with H
      iexact H)
  refine pure_soundness (PROP := IProp Iris.Examples.ClosedProofs.GF) ?_
  refine (persistently_emp_intro.trans (persistently_mono H)).trans ?_
  refine persistently_exists.mp.trans (exists_elim fun γ => ?_)
  exact persistently_sep_persistently.mpr.trans ((sep_mono persistently_elim persistently_elim).trans (own_full_dup_false γ))

-- `Iris.fupd_pure_forall` idx 7: necessary (A = Empty, E1 = ∅, E2 = ⊤: ⊢ |={∅,⊤}=> True, mask framing with ⊤ gives |={⊤}=> False)
theorem p3_39 : ¬ drop0% Iris.fupd_pure_forall 7 := fun h => by
  refine pure_soundness (PROP := IProp Iris.Examples.ClosedProofs.GF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ => ?_)
  have H1 := (forall_intro (P := iprop(emp)) (Ψ := fun _ : Empty => iprop(|={∅,⊤}=> ⌜False⌝)) (fun x => x.elim)).trans
    (@h Iris.Examples.ClosedProofs.GF .hasNoLC _ Empty ∅ ⊤ (fun _ => False)).mpr
  have H2 := H1.trans (BIFUpdate.mono (Q := iprop(⌜(⊤ : CoPset) ## ⊤⌝ → ⌜False⌝)) (by
    iintro _ %hd
    exact absurd hd full_not_disj))
  have H3 := H2.trans (fupd_mask_frame_right_strong (E1 := ∅) (E2 := ⊤) (Ef := ⊤) (fun x ⟨h1, _⟩ => CoPset.mem_empty h1))
  have e1 : (∅ ∪ ⊤ : CoPset) = ⊤ := rfl
  have e2 : (⊤ ∪ ⊤ : CoPset) = ⊤ := rfl
  rw [e1, e2] at H3
  exact wand_intro (sep_elim_left.trans H3)

-- `Iris.MonoZ.own_alloc` idx 3: necessary (n = -1: the authoritative assertion contains ⌜0 ≤ n⌝)
theorem p3_14 : ¬ drop0% Iris.MonoZ.own_alloc 3 := fun h =>
  bupd_false_unsound ((@h GFmn _ (-1)).trans (BIUpdate.mono (exists_elim fun _ =>
    sep_elim_left.trans (sep_elim_left.trans (pure_mono (fun h => absurd h (by decide)))))))

-- `Iris.MonoList.auth_own_update` idx 6: necessary (l = [()], l' = []: a kept fragment ◯[()] is no prefix of [])
theorem p3_13 : ¬ drop0% Iris.MonoList.auth_own_update 6 := fun h => by
  refine bupd_false_unsound (GF := GFml) ?_
  imod MonoList.own_alloc (GF := GFml) [()] with ⟨%γ, Ha, Hl⟩
  imod (@h GFml Unit _ γ [()] []) $$ Ha with ⟨Ha', _⟩
  ihave %Hv := MonoList.auth_lb_own_valid γ _ [] [()] $$ Ha' Hl
  exact absurd Hv.2 (by simp)


-- `Iris.step_fupd_mask_mono` idx 8: necessary (IProp, Eo = ∅, Ei₁ = ∅, Ei₂ = ⊤, P = True: ⊢ |={∅,⊤}=> _ framed with ⊤ gives |={⊤}=> False)
theorem p3_23 : ¬ drop0% Iris.step_fupd_mask_mono 8 := fun h => by
  refine pure_soundness (PROP := IProp Iris.Examples.ClosedProofs.GF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ => ?_)
  have H0 : ⊢ (|={∅}[∅]▷=> (iprop(True) : IProp Iris.Examples.ClosedProofs.GF)) := by
    iintro
    imodintro
    inext
    imodintro
    itrivial
  have H1 := H0.trans (@h (IProp Iris.Examples.ClosedProofs.GF) _ _ ∅ ∅ ∅ ⊤ iprop(True) (fun _ h => h))
  have H2 := H1.trans (BIFUpdate.mono (Q := iprop(⌜(⊤ : CoPset) ## ⊤⌝ → ⌜False⌝)) (by
    iintro _ %hd
    exact absurd hd full_not_disj))
  have H3 := H2.trans (fupd_mask_frame_right_strong (E1 := ∅) (E2 := ⊤) (Ef := ⊤) (fun x ⟨h1, _⟩ => CoPset.mem_empty h1))
  have e1 : (∅ ∪ ⊤ : CoPset) = ⊤ := rfl
  have e2 : (⊤ ∪ ⊤ : CoPset) = ⊤ := rfl
  rw [e1, e2] at H3
  exact wand_intro (sep_elim_left.trans H3)

-- `Iris.Linear.leak` idx 10: necessary (non-affine UPred NA, fupd E1 E2 Q = Q if E1 = E2 else True, cinv = cinv_own = True, P = True)
theorem p3_4 : ¬ drop0% Iris.Linear.leak 10 := fun h => by
  have H := @h .M1 .M0 (UPred NA) _ iprop(True) lfupd Unit (fun _ _ => iprop(True)) (fun _ => iprop(True))
    lfupd_mono lfupd_frame lfupd_alloc (fun P _ => lfupd_acc P)
  have H2 := H 0 ⟨.a, trivial⟩ trivial
  cases H2

-- `Iris.bi_rtc_timeless` idx 7: removable (A is a discrete OFE, so every R : A → A → PROP is non-expansive)
theorem p3_15 : drop% Iris.bi_rtc_timeless 7 := by
  intro PROP A _ _ _ _ R _ x y
  exact @bi_rtc_timeless PROP A _ _ _ _ R
    ⟨fun _ _ _ h1 _ _ h2 => (OFE.Discrete.discrete h1) ▸ (OFE.Discrete.discrete h2) ▸ OFE.Dist.rfl⟩ _ x y

-- `Iris.validN_iSingleton_op_notfree` idx 10: necessary (closed-proofs GF slot 1, mz' with valid ∅ at name 0 and the invalid element at name 1)
theorem p3_35 : ¬ drop0% Iris.validN_iSingleton_op_notfree 10 := fun h => by
  have H := @h Iris.Examples.ClosedProofs.GF (constOF CoPsetDisjL) _ elem1 0 0 (DisjointLeibnizSet.valid ∅)
    (DisjointLeibnizSet.valid ∅) (DisjointLeibnizSet.valid ∅) mzBad rfl (by
      change ✓{0} ((DisjointLeibnizSet.valid ∅ : CoPsetDisjL) • DisjointLeibnizSet.valid ∅)
      change ✓{0} (if (∅ : CoPset) ## ∅ then _ else _)
      rw [if_pos empty_disj]
      trivial)
  have H1 := H 1
  change ✓{0} ((none : Option CoPsetDisjL) • some DisjointLeibnizSet.error) at H1
  exact H1

-- `Iris.iOwn_ord_and_discrete_total_false` idx 5: necessary (agreement over SiProp: toAgree sp0 and toAgree sp1 have no common valid upper bound but agree at level 0)
theorem p3_37 : ¬ drop0% Iris.iOwn_ord_and_discrete_total_false 5 := fun h => by
  have hx : ∀ c' : Agree SiProp, ✓ c' → toAgree sp0 ≼ₒ c' → toAgree sp1 ≼ₒ c' → False := fun c' hv h1 h2 => by
    have e := (Agree.valid_ord hv h1).trans (Agree.valid_ord hv h2).symm
    exact sp_ne (OFE.eq_dist.mpr fun n => Agree.toAgree_injN (OFE.eq_dist.mp e n))
  have H := @h GFag (constOF (Agree SiProp)) _ elemAg 0 _ (toAgree sp0) (toAgree sp1) hx
  have hd : iSingleton (GF := GFag) (constOF (Agree SiProp)) 0 (toAgree sp0) ≡{0}≡ iSingleton (GF := GFag) (constOF (Agree SiProp)) 0 (toAgree sp1) :=
    OFE.NonExpansive.ne (OFE.NonExpansive.ne @sp_dist0)
  have hr := Ordered.ordN_of_ord 0 (OrderRefl.ord_refl (iSingleton (GF := GFag) (constOF (Agree SiProp)) 0 (toAgree sp0)))
  exact H 0 ⟨iSingleton (GF := GFag) (constOF (Agree SiProp)) 0 (toAgree sp0), validN_iSingleton.mpr Agree.toAgree_validN⟩
    ⟨by unfold iOwn; exact hr, by unfold iOwn; exact Ordered.ordN_ne hd .rfl hr⟩


-- `Iris.LawfulAbstractWP.wp_fupd` idx 9: necessary (toy language, wp E e Φ = ⌜∀ v, ⊢ Φ v⌝, Φ _ = ∃ γ, own γ (valid ⊤): allocatable under fupd but not valid)
theorem p3_46 : ¬ drop0% Iris.LawfulAbstractWP.wp_fupd 9 := fun h => by
  refine pure_soundness (PROP := IProp Iris.Examples.ClosedProofs.GF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun x => ?_)
  exfalso
  letI ι : IrisGS_gen .hasNoLC Nat Iris.Examples.ClosedProofs.GF :=
    { invGS := x, stateInterp := fun _ _ _ _ => iprop(True), numLatersPerStep := fun _ => 0,
      forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }
  have Hf : ⊢ |={⊤}=> iprop(∃ γ, iOwn (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL) γ
      (DisjointLeibnizSet.valid CoPset.full)) := by
    imod iOwn_alloc (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL)
      (DisjointLeibnizSet.valid CoPset.full) trivial with H
    iexact H
  have H := @h Nat Unit Unit Unit tlLang Iris.Examples.ClosedProofs.GF .hasNoLC ι
    (fun _ _ Φ => iprop(⌜∀ v, ⊢ Φ v⌝)) ⊤ 0
    (fun _ => iprop(∃ γ, iOwn (GF := Iris.Examples.ClosedProofs.GF) (F := constOF CoPsetDisjL) γ (DisjointLeibnizSet.valid CoPset.full)))
  exact own_full_not_valid (pure_soundness ((pure_intro (fun _ => Hf)).trans H) ())



-- `Iris.ProofMode.tac_wp_pure` idx 14: necessary (φ = False makes PureExec vacuous; e₁ = #0, e₂ = #1, n = 0, Δ = Δ' = emp, Φ v = ⌜v = #1⌝: WP #0 {{Φ}} is |={⊤}=> False)
theorem p3_28 : ¬ drop0% Iris.ProofMode.tac_wp_pure 14 := fun h => by
  refine pure_soundness (PROP := IProp Iris.Examples.ClosedProofs.GF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun x => ?_)
  letI ι : IrisGS_gen .hasNoLC Iris.HeapLang.Exp Iris.Examples.ClosedProofs.GF :=
    { invGS := x, stateInterp := fun _ _ _ _ => iprop(True), numLatersPerStep := fun _ => 0,
      forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }
  have H := @h .hasNoLC Iris.Examples.ClosedProofs.GF ι iprop(emp) iprop(emp) .NotStuck ⊤ []
    (Iris.ProgramLogic.ToVal.ofVal (Iris.HeapLang.Val.lit (.int 0))) (Iris.ProgramLogic.ToVal.ofVal (Iris.HeapLang.Val.lit (.int 1))) False 0
    (fun v => iprop(⌜v = Iris.HeapLang.Val.lit (.int 1)⌝)) ⟨fun h => h.elim⟩ .rfl
    ((pure_intro rfl).trans (wp_value' (Φ := fun v => iprop(⌜v = Iris.HeapLang.Val.lit (.int 1)⌝)) (v := Iris.HeapLang.Val.lit (.int 1))))
  have H2 := H.trans ((wp_value_fupd' (Φ := fun v => iprop(⌜v = Iris.HeapLang.Val.lit (.int 1)⌝)) (v := Iris.HeapLang.Val.lit (.int 0))).mp.trans (BIFUpdate.mono (pure_mono (φ2 := False) fun e => by simp at e)))
  exact wand_intro (sep_elim_left.trans H2)
