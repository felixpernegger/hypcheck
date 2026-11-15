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


namespace W5c2
open Iris Iris.BI

/-! GB: Boolean non-affine BI over Bool with xor (copied from W4c4). -/
def GB := Bool → Prop

instance : BIBase GB where
  Entails P Q      := ∀ x, P x → Q x
  emp            x := x = false
  pure φ         _ := φ
  and P Q        x := P x ∧ Q x
  or P Q         x := P x ∨ Q x
  imp P Q        x := P x → Q x
  sForall Ψ      x := ∀ p, Ψ p → p x
  sExists Ψ      x := ∃ p, Ψ p ∧ p x
  sep P Q        x := ∃ a b, x = xor a b ∧ P a ∧ Q b
  wand P Q       x := ∀ y, P y → Q (xor x y)
  persistently P _ := P false
  later P        x := P x

instance : COFE GB := COFE.ofDiscrete _

instance gbBI : BI GB where
  entails_refl _ h := h
  entails_trans h1 h2 x h := h2 x (h1 x h)
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
  pure_elim' h σ hφ := h hφ σ ⟨⟩
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 x h := ⟨h1 x h, h2 x h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 x h := h.elim (h1 x) (h2 x)
  imp_intro h x hP hQ := h x ⟨hP, hQ⟩
  imp_elim h x hPQ := h x hPQ.1 hPQ.2
  sForall_intro h x hP p hp := h p hp x hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h x := fun ⟨p, hp, hx⟩ => h p hp x hx
  sep_mono h1 h2 _ := fun ⟨a, b, e, ha, hb⟩ => ⟨a, b, e, h1 a ha, h2 b hb⟩
  emp_sep := ⟨fun _ ⟨a, b, e, ha, hb⟩ => by
      have ha' : a = false := ha
      subst ha'; subst e; simpa using hb,
    fun x h => ⟨false, x, by simp, rfl, h⟩⟩
  sep_symm _ := fun ⟨a, b, e, ha, hb⟩ => ⟨b, a, by subst e; cases a <;> cases b <;> rfl, hb, ha⟩
  sep_assoc_l _ := fun ⟨ab, c, e, ⟨a, b, e2, ha, hb⟩, hc⟩ =>
    ⟨a, xor b c, by subst e; subst e2; cases a <;> cases b <;> cases c <;> rfl, ha, b, c, rfl, hb, hc⟩
  wand_intro h x hP y hQ := h (xor x y) ⟨x, y, rfl, hP, hQ⟩
  wand_elim h _ := fun ⟨a, b, e, ha, hb⟩ => e ▸ h a ha b hb
  persistently_mono h _ hP := h false hP
  persistently_idem_2 _ h := h
  persistently_emp_2 _ _ := (rfl : false = false)
  persistently_and_2 _ h := h
  persistently_absorb_l _ := fun ⟨_, _, _, ha, _⟩ => ha
  persistently_and_l x h := ⟨false, x, by cases x <;> rfl, h.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr fun _ => h

def own1 : GB := fun x => x = true

theorem gb_true_not_emp : ¬ ((iprop(True) : GB) ⊢ iprop(emp)) := fun h =>
  Bool.noConfusion (h true trivial : true = false)

theorem gb_emp_not_absorbing : ¬ Absorbing (iprop(emp) : GB) := fun ⟨h⟩ =>
  Bool.noConfusion (h true ⟨true, false, rfl, trivial, rfl⟩ : true = false)

theorem gb_true_not_affine : ¬ Affine (iprop(True) : GB) := fun ⟨h⟩ => gb_true_not_emp h

theorem gb_own1_not_pers : ¬ Persistent own1 := fun ⟨h⟩ =>
  Bool.noConfusion (h true rfl : false = true)

theorem gb_not_biaffine : ¬ BIAffine GB := fun h => gb_true_not_affine (h.affine _)

theorem gb_not_positive : ¬ BIPositive GB := fun ⟨h⟩ => by
  have := @h own1 own1 false ⟨rfl, true, true, rfl, rfl, rfl⟩
  obtain ⟨a, b, e, ⟨ha, ha'⟩, hb⟩ := this
  have ha : a = false := ha
  subst ha
  exact Bool.noConfusion (ha' : false = true)

instance : BIPersistentlyForall GB := ⟨fun _ _ h p hp => h _ ⟨p, rfl⟩ hp⟩
instance gbPE : BIPersistentlyExist GB := ⟨fun _ _ ⟨p, hp, h⟩ => ⟨_, ⟨p, rfl⟩, hp, h⟩⟩

/-! AN: classical affine BI on Nat → Prop with sep = and, emp = True, persistently = id
(every proposition persistent and affine; BIPersistentlyExist). -/
def AN := Nat → Prop

instance : BIBase AN where
  Entails P Q      := ∀ x, P x → Q x
  emp            _ := True
  pure φ         _ := φ
  and P Q        x := P x ∧ Q x
  or P Q         x := P x ∨ Q x
  imp P Q        x := P x → Q x
  sForall Ψ      x := ∀ p, Ψ p → p x
  sExists Ψ      x := ∃ p, Ψ p ∧ p x
  sep P Q        x := P x ∧ Q x
  wand P Q       x := P x → Q x
  persistently P x := P x
  later P        x := P x

instance : COFE AN := COFE.ofDiscrete _

instance anBI : BI AN where
  entails_refl _ h := h
  entails_trans h1 h2 x h := h2 x (h1 x h)
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
  pure_elim' h σ hφ := h hφ σ ⟨⟩
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 x h := ⟨h1 x h, h2 x h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 x h := h.elim (h1 x) (h2 x)
  imp_intro h x hP hQ := h x ⟨hP, hQ⟩
  imp_elim h x hPQ := h x hPQ.1 hPQ.2
  sForall_intro h x hP p hp := h p hp x hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h x := fun ⟨p, hp, hx⟩ => h p hp x hx
  sep_mono h1 h2 x h := ⟨h1 x h.1, h2 x h.2⟩
  emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩
  sep_symm _ h := ⟨h.2, h.1⟩
  sep_assoc_l _ h := ⟨h.1.1, h.1.2, h.2⟩
  wand_intro h x hP hQ := h x ⟨hP, hQ⟩
  wand_elim h x hPQ := h x hPQ.1 hPQ.2
  persistently_mono h x hP := h x hP
  persistently_idem_2 _ h := h
  persistently_emp_2 _ _ := trivial
  persistently_and_2 _ h := h
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr fun _ => h

instance anAffine : BIAffine AN := ⟨fun _ => ⟨fun _ _ => trivial⟩⟩
instance anPE : BIPersistentlyExist AN := ⟨fun _ _ ⟨p, hp, h⟩ => ⟨_, ⟨p, rfl⟩, hp, h⟩⟩
instance anPers (P : AN) : Persistent P := ⟨fun _ h => h⟩

/-- Non-monotone modality on GB: X or X empty. Satisfies trans and both frame rules. -/
def gbE (X : GB) : GB := fun x => X x ∨ ∀ y, ¬ X y

theorem gbE_trans {X : GB} : gbE (gbE X) ⊢ gbE X := fun _ h =>
  h.elim id (fun h' => (h' false (.inr fun z hz => h' z (.inl hz))).elim)

theorem gbE_frame_r {P R : GB} : iprop(gbE P ∗ R) ⊢ gbE iprop(P ∗ R) :=
  fun x ⟨a, b, e, hP, hR⟩ => hP.elim (fun hp => .inl ⟨a, b, e, hp, hR⟩)
    (fun hn => .inr fun _ ⟨a', _, _, hP', _⟩ => hn a' hP')

theorem gbE_frame_l {P R : GB} : iprop(P ∗ gbE R) ⊢ gbE iprop(P ∗ R) :=
  fun x ⟨a, b, e, hP, hR⟩ => hR.elim (fun hr => .inl ⟨a, b, e, hP, hr⟩)
    (fun hn => .inr fun _ ⟨_, b', _, _, hR'⟩ => hn b' hR')

/-- AN modality "valid everywhere" (constant): monotone, no framing. -/
def anV (X : AN) : AN := fun _ => ∀ m, X m

/-- In AN, the saved-proposition rules with saved i P := (i = P), ident = AN, and bupd = True. -/
def anEq (i P : AN) : AN := fun _ => i = P

theorem an_agree : ∀ (i : AN) (P Q : AN), iprop(anEq i P ∧ anEq i Q) ⊢ iprop(□ (P ↔ Q)) :=
  fun _ _ _ _ ⟨h1, h2⟩ => by subst h1; subst h2; exact ⟨trivial, id, id⟩

/-- Non-monotone modality on AN: X or X empty. -/
def anE (X : AN) : AN := fun x => X x ∨ ∀ y, ¬ X y

theorem anE_ff {E : Iris.Inv.Mask} {X : AN} : anE (anE X) ⊢ anE X := fun _ h =>
  h.elim id (fun h' => (h' 0 (.inr fun z hz => h' z (.inl hz))).elim)

theorem anE_fl {E : Iris.Inv.Mask} {P R : AN} : iprop(P ∗ anE R) ⊢ anE iprop(P ∗ R) :=
  fun _ ⟨hP, hR⟩ => hR.elim (fun hr => .inl ⟨hP, hr⟩) (fun hn => .inr fun y h => hn y h.2)

/-- Masked modality on AN: M0 is True, M1 is the identity. -/
def anM (E : Iris.Inv.Mask) (X : AN) : AN := fun x => E = .M0 ∨ X x

theorem anM_mono {E : Iris.Inv.Mask} {P Q : AN} (h : P ⊢ Q) : anM E P ⊢ anM E Q :=
  fun x hx => hx.imp id ((h : ∀ x, P x → Q x) x)
theorem anM_ff {E : Iris.Inv.Mask} {X : AN} : anM E (anM E X) ⊢ anM E X := fun _ h => h.elim .inl id
theorem anM_fl {E : Iris.Inv.Mask} {P R : AN} : iprop(P ∗ anM E R) ⊢ anM E iprop(P ∗ R) :=
  fun _ ⟨hP, hR⟩ => hR.elim .inl (fun hr => .inr ⟨hP, hr⟩)

/-- AN modality "somewhere": intro, mono and idempotent, but no framing. -/
def anN (X : AN) : AN := fun _ => ∃ y, X y

section SavedGen
universe u v
variable {PROP : Type u} [BI PROP] (ident : Type v) (saved : ident → PROP → PROP)
  (agree : ∀ (i : ident) (P Q : PROP), saved i P ∧ saved i Q ⊢ □ (P ↔ Q))
include agree

/-- The core of saved_NA from separated facts: if □(¬P ∗ saved i P) yields ¬P and saved i P,
then saved i (A i) ∧ A i is contradictory (only ∧-reasoning and agree). -/
theorem savedNA_core (i : ident)
    (hl : ∀ P : PROP, iprop(□ (¬P ∗ saved i P)) ⊢ iprop(¬P))
    (hr : ∀ P : PROP, iprop(□ (¬P ∗ saved i P)) ⊢ saved i P) :
    saved i (Iris.SavedProp.A ident saved i) ⊢ iprop(¬ Iris.SavedProp.A ident saved i) := by
  refine imp_intro ?_
  refine (and_intro .rfl and_elim_r).trans (and_exists_left.mp.trans (exists_elim fun P => ?_))
  let X : PROP := iprop((saved i (Iris.SavedProp.A ident saved i) ∧ Iris.SavedProp.A ident saved i) ∧
      □ (¬P ∗ saved i P))
  have h1 : X ⊢ iprop(¬P) := and_elim_r.trans (hl P)
  have h2 : X ⊢ saved i P := and_elim_r.trans (hr P)
  have h3 : X ⊢ saved i (Iris.SavedProp.A ident saved i) := and_elim_l.trans and_elim_l
  have h4 : X ⊢ Iris.SavedProp.A ident saved i := and_elim_l.trans and_elim_r
  have h5 := (and_intro h2 h3).trans (agree i P (Iris.SavedProp.A ident saved i))
  have h6 := (and_intro (h5.trans (intuitionistically_elim.trans and_elim_r)) h4).trans imp_elim_left
  exact (and_intro h1 h6).trans imp_elim_left

/-- agree makes every saved i P affine. -/
theorem saved_affine (i : ident) (P : PROP) : Affine (saved i P) :=
  ⟨(and_intro .rfl .rfl).trans ((agree i P P).trans intuitionistically_elim_emp)⟩

/-- saved_NA with persistence of saved (no BIAffine, no BIPersistentlyExist). -/
theorem savedNA_pers [∀ i P, Persistent (saved i P)] (i : ident) :
    saved i (Iris.SavedProp.A ident saved i) ⊢ iprop(¬ Iris.SavedProp.A ident saved i) := by
  refine savedNA_core ident saved agree i (fun P => ?_) (fun P => ?_)
  · haveI := saved_affine ident saved agree i P
    exact intuitionistically_elim.trans sep_elim_left
  · exact (intuitionistically_mono ((sep_mono_right persistent).trans persistently_absorb_right)).trans
      ((affinely_mono persistently_idem.1).trans intuitionistically_elim)

/-- saved_NA in an affine BI (no persistence of saved, no BIPersistentlyExist). -/
theorem savedNA_aff [BIAffine PROP] (i : ident) :
    saved i (Iris.SavedProp.A ident saved i) ⊢ iprop(¬ Iris.SavedProp.A ident saved i) :=
  savedNA_core ident saved agree i (fun _ => intuitionistically_elim.trans sep_elim_left)
    (fun _ => intuitionistically_elim.trans sep_elim_right)

/-- saved_A with persistence of saved (no BIAffine, no BIPersistentlyExist). -/
theorem savedA_pers [∀ i P, Persistent (saved i P)] (i : ident) :
    saved i (Iris.SavedProp.A ident saved i) ⊢ Iris.SavedProp.A ident saved i := by
  haveI := saved_affine ident saved agree i (Iris.SavedProp.A ident saved i)
  refine intuitionistic_alias.trans (Iris.BI.BIBase.Entails.trans ?_
    (exists_intro (Ψ := fun P => iprop(□ (¬P ∗ saved i P))) (Iris.SavedProp.A ident saved i)))
  exact intuitionistically_intro_intuitionistically (intuitionistically_sep_idem.2.trans
    (sep_mono (intuitionistically_elim.trans (savedNA_pers ident saved agree i)) intuitionistically_elim))

end SavedGen

/-- Affine excluded middle without BIPersistentlyExist: P ⊢ P ∧ ((P ∗ P) ∨ (P ∗ ¬P)), and P ∧ (P ∗ ¬P) ⊢ P ∧ ¬P ⊢ False by affinity. -/
theorem sepdup_gen.{u} {PROP : Type u} [BI PROP] (em : ∀ P : PROP, ⊢ P ∨ ¬P) (P : PROP) [Affine P] :
    P ⊢ iprop(P ∗ P) := by
  have h1 : P ⊢ iprop(P ∗ P ∨ P ∗ ¬P) := sep_emp.2.trans ((sep_mono_right (em P)).trans sep_or_left.1)
  refine (and_intro .rfl h1).trans (and_or_left.1.trans (or_elim and_elim_r ?_))
  exact (and_mono_right ((sep_mono_left affine).trans emp_sep.1)).trans (imp_elim_right.trans false_elim)

/-- NP: Nat under addition as a discrete UORA (unit 0, core 0, all valid, order ≤); UPred NP is affine and ownM 1 is not duplicable. -/
structure NP where v : Nat

instance : OFE NP := OFE.ofDiscrete NP
instance : OFE.Discrete NP := ⟨id⟩

instance npORA : ORA NP := ORA.ofDiscreteORAData {
  pcore := fun _ => some ⟨0⟩
  op := fun a b => ⟨a.v + b.v⟩
  Valid := fun _ => True
  Order := fun a b => a.v ≤ b.v
  assoc := by intro x y z; cases x; cases y; cases z; simp only [NP.mk.injEq]; omega
  comm := by intro x y; cases x; cases y; simp only [NP.mk.injEq]; omega
  pcore_op_left := by intro x cx h; cases h; cases x; simp
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ h1 h2 => Nat.le_trans h1 h2
  op_mono_left := by intro x y z h; show _ ≤ _; dsimp only; have : x.v ≤ y.v := h; omega
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨⟨0⟩, rfl, Nat.le_refl 0⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨⟨0⟩, rfl, Nat.le_refl 0⟩
  pcore_increasing := by intro x cx h y; cases h; show _ ≤ _; dsimp only; omega
  increasing_closed := by intro x y _ _ z; show _ ≤ _; dsimp only; omega }

instance : OrderRefl NP := ⟨fun x => Nat.le_refl x.v⟩

instance npUORA : UORA NP where
  unit := ⟨0⟩
  unit_valid := trivial
  unit_left_id := by intro x; cases x; simp [Op.op]
  pcore_unit := rfl

instance : IncOrd NP := ⟨by
  intro x y ⟨z, hz⟩
  have : y = ⟨x.v + z.v⟩ := hz
  subst this; exact Nat.le_add_right _ _⟩

theorem np_not_dup : ¬ ((UPred.ownM (⟨1⟩ : NP)) ⊢ iprop(UPred.ownM (⟨1⟩ : NP) ∗ UPred.ownM (⟨1⟩ : NP))) := fun h => by
  have H := (h.trans (UPred.ownM_op (⟨1⟩ : NP) ⟨1⟩).2) 0 ⟨⟨1⟩, trivial⟩ (Nat.le_refl 1)
  have H2 : 2 ≤ 1 := H
  omega

/-- KN: intuitionistic Kripke BI of up-closed predicates on (Nat, ≤), sep = and, emp = True,
persistently = later = id (affine, everything persistent). Not Boolean, so non-idempotent
lax modalities exist (knShift). -/
structure KN where
  p : Nat → Prop
  mono : ∀ {a b : Nat}, a ≤ b → p a → p b

theorem KN.ext' {P Q : KN} (h : ∀ n, P.p n ↔ Q.p n) : P = Q := by
  cases P; cases Q; congr; funext n; exact propext (h n)

instance : COFE KN := COFE.ofDiscrete _

instance knBase : BIBase KN where
  Entails P Q := ∀ n, P.p n → Q.p n
  emp := ⟨fun _ => True, fun _ h => h⟩
  pure φ := ⟨fun _ => φ, fun _ h => h⟩
  and P Q := ⟨fun n => P.p n ∧ Q.p n, fun h x => ⟨P.mono h x.1, Q.mono h x.2⟩⟩
  or P Q := ⟨fun n => P.p n ∨ Q.p n, fun h x => x.imp (P.mono h) (Q.mono h)⟩
  imp P Q := ⟨fun n => ∀ m, n ≤ m → P.p m → Q.p m, fun h x m hm => x m (Nat.le_trans h hm)⟩
  sForall Ψ := ⟨fun n => ∀ p, Ψ p → KN.p p n, fun h x p hp => p.mono h (x p hp)⟩
  sExists Ψ := ⟨fun n => ∃ p, Ψ p ∧ KN.p p n, fun h ⟨p, hp, x⟩ => ⟨p, hp, p.mono h x⟩⟩
  sep P Q := ⟨fun n => P.p n ∧ Q.p n, fun h x => ⟨P.mono h x.1, Q.mono h x.2⟩⟩
  wand P Q := ⟨fun n => ∀ m, n ≤ m → P.p m → Q.p m, fun h x m hm => x m (Nat.le_trans h hm)⟩
  persistently P := P
  later P := P

instance knBI : BI KN where
  entails_refl _ h := h
  entails_trans h1 h2 x h := h2 x (h1 x h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h₁, h₂⟩ => KN.ext' fun n => ⟨h₁ n, h₂ n⟩⟩
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
  pure_elim' h n hφ := h hφ n trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 x h := ⟨h1 x h, h2 x h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 x h := h.elim (h1 x) (h2 x)
  imp_intro {P Q R} h n hP m hm hQ := h m ⟨P.mono hm hP, hQ⟩
  imp_elim h n hPQ := h n hPQ.1 n (Nat.le_refl n) hPQ.2
  sForall_intro h x hP p hp := h p hp x hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h x := fun ⟨p, hp, hx⟩ => h p hp x hx
  sep_mono h1 h2 x h := ⟨h1 x h.1, h2 x h.2⟩
  emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩
  sep_symm _ h := ⟨h.2, h.1⟩
  sep_assoc_l _ h := ⟨h.1.1, h.1.2, h.2⟩
  wand_intro {P Q R} h n hP m hm hQ := h m ⟨P.mono hm hP, hQ⟩
  wand_elim h n hPQ := h n hPQ.1 n (Nat.le_refl n) hPQ.2
  persistently_mono h x hP := h x hP
  persistently_idem_2 _ h := h
  persistently_emp_2 _ _ := trivial
  persistently_and_2 _ h := h
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 n h p hp := h _ ⟨p, rfl⟩ n (Nat.le_refl n) hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ _ := .inr fun _ _ hf => hf.elim

instance knAffine : BIAffine KN := ⟨fun _ => ⟨fun _ _ => trivial⟩⟩
instance knPers (P : KN) : Persistent P := ⟨fun _ h => h⟩

/-- Shift by one step: intro, mono, framing (up-closure), not idempotent. -/
def knShift (X : KN) : KN := ⟨fun n => X.p (n + 1), fun h x => X.mono (Nat.succ_le_succ h) x⟩
/-- Delay by one step. -/
def knDelay (X : KN) : KN :=
  ⟨fun n => 1 ≤ n ∧ X.p (n - 1), fun h x => ⟨Nat.le_trans x.1 h, X.mono (Nat.sub_le_sub_right h 1) x.2⟩⟩
def knStart : KN := ⟨fun n => 1 ≤ n, fun h x => Nat.le_trans x h⟩

theorem knShift_intro {X : KN} : X ⊢ knShift X := fun n x => X.mono (Nat.le_succ n) x
theorem knShift_fl {P Q : KN} : iprop(P ∗ knShift Q) ⊢ knShift iprop(P ∗ Q) :=
  fun n h => ⟨P.mono (Nat.le_succ n) h.1, h.2⟩
theorem knShift_alloc (P : KN) : P ⊢ knShift iprop(∃ i : Unit, knDelay P) :=
  fun n x => ⟨_, ⟨(), rfl⟩, Nat.succ_le_succ (Nat.zero_le n), by simpa using x⟩

/-- laterN_False without BIPersistentlyExist (weak Löb on the existential). -/
theorem laterNFalse_gen.{u} {PROP : Type u} [BI PROP] [BILoeb PROP] : ⊢@{PROP} ∃ n, ▷^[n] False := by
  refine true_intro.trans (loeb_weak ?_)
  exact later_exists_false.trans (or_elim (exists_intro (Ψ := fun n => iprop(▷^[n] False)) 1)
    (exists_elim fun n => exists_intro (Ψ := fun n => iprop(▷^[n] False)) (n + 1)))

end W5c2

open Iris Iris.BI W5c2

-- `Iris.AffineEM.sep_dup` idx 5: necessary (GB, P = own1: own1 ∗ own1 = emp)
theorem w5c2_1 : ¬ drop0% Iris.AffineEM.sep_dup 5 := fun h => by
  obtain ⟨a, b, e, ha, hb⟩ := @h GB _ _ (fun P x _ => Classical.em (P x)) own1 true rfl
  cases ha; cases hb; exact absurd e (by decide)

-- `Iris.AffineEM.and_sep` idx 6: necessary (GB, P = Q = own1)
theorem w5c2_2 : ¬ drop0% Iris.AffineEM.and_sep 6 := fun h => by
  obtain ⟨a, b, e, ha, hb⟩ := @h GB _ _ (fun P x _ => Classical.em (P x)) own1 own1 true ⟨rfl, rfl⟩
  cases ha; cases hb; exact absurd e (by decide)

-- `Iris.LoebEM.later_anything` idx 5: necessary (GB has no Löb: later = id, P = False)
theorem w5c2_3 : ¬ drop0% Iris.LoebEM.later_anything 5 := fun h =>
  @h GB iprop(False) _ _ (fun P x _ => Classical.em (P x)) false rfl

-- `Iris.LoebEM.later_anything` idx 4: necessary (SiProp, P = False: later False fails at step 1)
theorem w5c2_4 : ¬ drop0% Iris.LoebEM.later_anything 4 := fun h =>
  (@h SiProp iprop(False) _ _ _) 1 trivial

-- `Iris.LoebEM.later_inconsistent` idx 3: necessary (SiProp is consistent)
theorem w5c2_5 : ¬ drop0% Iris.LoebEM.later_inconsistent 3 := fun h =>
  (@h SiProp _ _) 0 trivial

-- `Iris.SavedProp.bupd_mono'` idx 5: necessary (GB, bupd = negation, False ⊢ True)
theorem w5c2_6 : ¬ drop0% Iris.SavedProp.bupd_mono' 5 := fun h =>
  (@h GB _ iprop(False) iprop(True) (fun X x => ¬ X x) (fun _ h => h.elim) true (fun h => h)) trivial

-- `Iris.SavedProp.bupd_mono'` idx 6: necessary (bupd = id, True ⊬ False)
theorem w5c2_7 : ¬ drop0% Iris.SavedProp.bupd_mono' 6 := fun h =>
  @h GB _ iprop(True) iprop(False) id (fun h => h) true trivial

-- `Iris.SavedProp.elim_modal_bupd` idx 5: necessary (GB, bupd X = X or X empty; P = False, Q = own1)
theorem w5c2_8 : ¬ drop0% Iris.SavedProp.elim_modal_bupd 5 := fun h => by
  have := (@h GB _ iprop(False) own1 gbE gbE_trans gbE_frame_r .out false).elim_modal trivial false
    ⟨false, false, rfl, .inr fun _ h => h, fun _ h => h.elim⟩
  exact this.elim (fun h => Bool.noConfusion h) (fun h => h true rfl)

-- `Iris.SavedProp.elim_modal_bupd` idx 6: necessary (GB, bupd X = X ∗ own1; P = Q = emp)
theorem w5c2_9 : ¬ drop0% Iris.SavedProp.elim_modal_bupd 6 := fun h => by
  have := (@h GB _ iprop(emp) iprop(emp) (fun X => iprop(X ∗ own1))
    (fun hPQ => sep_mono hPQ .rfl) sep_right_comm.mp .out false).elim_modal trivial false
    ⟨true, true, rfl, ⟨false, true, rfl, rfl, rfl⟩, fun y hy => by cases hy; exact ⟨false, true, rfl, rfl, rfl⟩⟩
  obtain ⟨a, b, e, ha, hb⟩ := this
  cases ha; cases hb; exact absurd e (by decide)

-- `Iris.SavedProp.elim_modal_bupd` idx 7: necessary (GB, bupd X = X ∨ own1; P = Q = False)
theorem w5c2_10 : ¬ drop0% Iris.SavedProp.elim_modal_bupd 7 := fun h => by
  have := (@h GB _ iprop(False) iprop(False) (fun X x => X x ∨ x = true)
    (fun hPQ x hx => hx.imp (hPQ x) id) (fun x h => h.elim id .inr) .out false).elim_modal trivial false
    ⟨true, true, rfl, .inr rfl, fun _ h => h.elim⟩
  exact this.elim id (fun h => Bool.noConfusion h)

-- `Iris.SavedProp.A_alloc` idx 5: necessary (empty ident, bupd = id)
theorem w5c2_11 : ¬ drop0% Iris.SavedProp.A_alloc 5 := fun h => by
  obtain ⟨_, ⟨i, _⟩, _⟩ := (@h GB _ id Empty (fun _ _ => iprop(True))) false rfl
  exact i.elim

-- `Iris.Inv.fupd_mono'` idx 5: necessary (GB, fupd = negation, False ⊢ True)
theorem w5c2_12 : ¬ drop0% Iris.Inv.fupd_mono' 5 := fun h =>
  (@h GB _ iprop(False) iprop(True) (fun _ X x => ¬ X x) .M0 (fun _ h => h.elim) true (fun h => h)) trivial

-- `Iris.Inv.fupd_mono'` idx 7: necessary (fupd = id, True ⊬ False)
theorem w5c2_13 : ¬ drop0% Iris.Inv.fupd_mono' 7 := fun h =>
  @h GB _ iprop(True) iprop(False) (fun _ X => X) (fun h => h) .M0 true trivial

-- `Iris.Inv.fupd_proper` idx 5: removable (P ⊣⊢ Q gives P = Q, `BiEntails.to_eq`)
theorem w5c2_14 : drop% Iris.Inv.fupd_proper 5 := by
  intro PROP _ P Q fupd E h
  rw [Iris.BI.BIBase.BiEntails.to_eq h]; exact Iris.BI.BIBase.BiEntails.rfl

-- `Iris.Inv.fupd_proper` idx 7: necessary (fupd = id, True ⊣⊢ False fails)
theorem w5c2_15 : ¬ drop0% Iris.Inv.fupd_proper 7 := fun h =>
  (@h GB _ iprop(True) iprop(False) (fun _ X => X) (fun h => h) .M0).1 true trivial

-- `Iris.Inv.fupd_frame_right` idx 5: removable (frame_left plus commutativity; Q ∗ P = P ∗ Q by `BiEntails.to_eq`)
theorem w5c2_16 : drop% Iris.Inv.fupd_frame_right 5 := by
  intro PROP _ P Q fupd hfl E
  have e : iprop(Q ∗ P) = iprop(P ∗ Q) := Iris.BI.BIBase.BiEntails.to_eq sep_comm
  exact sep_comm.mp.trans (e ▸ @hfl E Q P)

-- `Iris.Inv.fupd_frame_right` idx 6: necessary (AN, fupd = validity; P = True, Q = (n = 0))
theorem w5c2_17 : ¬ drop0% Iris.Inv.fupd_frame_right 6 := fun h =>
  absurd ((@h AN _ iprop(True) (fun n => n = 0) (fun _ => anV) (fun {_ P Q} (hPQ : P ⊢ Q) _ h m => (hPQ : ∀ x, P x → Q x) m (h m)) .M0)
    0 ⟨fun _ => trivial, rfl⟩ 1).2 (by decide)

-- `Iris.Inv.elim_fupd_fupd` idx 5: necessary (GB, fupd X = X or X empty; P = False, Q = own1)
theorem w5c2_18 : ¬ drop0% Iris.Inv.elim_fupd_fupd 5 := fun h => by
  have := (@h GB _ iprop(False) own1 (fun _ => gbE) gbE_trans gbE_frame_l .out false .M0).elim_modal trivial false
    ⟨false, false, rfl, .inr fun _ h => h, fun _ h => h.elim⟩
  exact this.elim (fun h => Bool.noConfusion h) (fun h => h true rfl)

-- `Iris.Inv.elim_fupd_fupd` idx 6: necessary (GB, fupd X = X ∗ own1; P = Q = emp)
theorem w5c2_19 : ¬ drop0% Iris.Inv.elim_fupd_fupd 6 := fun h => by
  have := (@h GB _ iprop(emp) iprop(emp) (fun _ X => iprop(X ∗ own1))
    (fun hPQ => sep_mono hPQ .rfl) sep_assoc.mpr .out false .M0).elim_modal trivial false
    ⟨true, true, rfl, ⟨false, true, rfl, rfl, rfl⟩, fun y hy => by cases hy; exact ⟨false, true, rfl, rfl, rfl⟩⟩
  obtain ⟨a, b, e, ha, hb⟩ := this
  cases ha; cases hb; exact absurd e (by decide)

-- `Iris.Inv.elim_fupd_fupd` idx 7: necessary (GB, fupd X = X ∨ own1; P = Q = False)
theorem w5c2_20 : ¬ drop0% Iris.Inv.elim_fupd_fupd 7 := fun h => by
  have := (@h GB _ iprop(False) iprop(False) (fun _ X x => X x ∨ x = true)
    (fun hPQ x hx => hx.imp (hPQ x) id) (fun x h => h.elim id .inr) .out false .M0).elim_modal trivial false
    ⟨true, true, rfl, .inr rfl, fun _ h => h.elim⟩
  exact this.elim id (fun h => Bool.noConfusion h)

-- `Iris.Inv.elim_fupd0_fupd1` idx 5: necessary (GB, fupd X = X or X empty; P = False, Q = own1)
theorem w5c2_21 : ¬ drop0% Iris.Inv.elim_fupd0_fupd1 5 := fun h => by
  have := (@h GB _ iprop(False) own1 (fun _ => gbE) gbE_trans gbE_frame_l (fun _ h => h) .out false).elim_modal trivial false
    ⟨false, false, rfl, .inr fun _ h => h, fun _ h => h.elim⟩
  exact this.elim (fun h => Bool.noConfusion h) (fun h => h true rfl)

-- `Iris.Inv.elim_fupd0_fupd1` idx 6: necessary (GB, fupd X = X ∗ own1; P = Q = emp)
theorem w5c2_22 : ¬ drop0% Iris.Inv.elim_fupd0_fupd1 6 := fun h => by
  have := (@h GB _ iprop(emp) iprop(emp) (fun _ X => iprop(X ∗ own1))
    (fun hPQ => sep_mono hPQ .rfl) sep_assoc.mpr (fun _ h => h) .out false).elim_modal trivial false
    ⟨true, true, rfl, ⟨false, true, rfl, rfl, rfl⟩, fun y hy => by cases hy; exact ⟨false, true, rfl, rfl, rfl⟩⟩
  obtain ⟨a, b, e, ha, hb⟩ := this
  cases ha; cases hb; exact absurd e (by decide)

-- `Iris.Inv.elim_fupd0_fupd1` idx 7: necessary (GB, fupd X = X ∨ own1; P = Q = False)
theorem w5c2_23 : ¬ drop0% Iris.Inv.elim_fupd0_fupd1 7 := fun h => by
  have := (@h GB _ iprop(False) iprop(False) (fun _ X x => X x ∨ x = true)
    (fun hPQ x hx => hx.imp (hPQ x) id) (fun x h => h.elim id .inr) (fun _ h => h) .out false).elim_modal trivial false
    ⟨true, true, rfl, .inr rfl, fun _ h => h.elim⟩
  exact this.elim id (fun h => Bool.noConfusion h)

-- `Iris.Inv.elim_fupd0_fupd1` idx 8: necessary (GB, fupd M0 = True, fupd M1 = id; P = Q = False)
theorem w5c2_24 : ¬ drop0% Iris.Inv.elim_fupd0_fupd1 8 := fun h => by
  have := (@h GB _ iprop(False) iprop(False) (fun E X x => E = .M0 ∨ X x)
    (fun hPQ x hx => hx.imp id (hPQ x)) (fun x h => h.elim .inl id)
    (fun x ⟨a, b, e, hP, hQ⟩ => hQ.elim .inl (fun hq => .inr ⟨a, b, e, hP, hq⟩)) .out false).elim_modal trivial false
    ⟨false, false, rfl, .inl rfl, fun _ h => h.elim⟩
  exact this.elim (fun e => Iris.Inv.Mask.noConfusion e) id

-- `Iris.Inv.exists_split_fupd0` idx 4: necessary (GB, fupd = negation, Φ = False, P = True)
theorem w5c2_25 : ¬ drop0% Iris.Inv.exists_split_fupd0 4 := fun h =>
  ((@h GB _ iprop(True) (fun _ X x => ¬ X x) Unit .M0 (fun _ => iprop(False)) ⟨fun _ _ => trivial⟩).from_exists
    false ⟨_, ⟨(), rfl⟩, fun h => h⟩) trivial

-- `Iris.Inv.exists_split_fupd0` idx 8: necessary (fupd = id, Φ = True, P = False)
theorem w5c2_26 : ¬ drop0% Iris.Inv.exists_split_fupd0 8 := fun h =>
  (@h GB _ iprop(False) (fun _ X => X) (fun h => h) Unit .M0 (fun _ => iprop(True))).from_exists
    false ⟨_, ⟨(), rfl⟩, trivial⟩

-- `Iris.Inv.saved_persistent` idx 4: necessary (GB, inv = own1, not persistent)
theorem w5c2_27 : ¬ drop0% Iris.Inv.saved_persistent 4 := fun h => by
  obtain ⟨hp⟩ := @h GB _ Unit (fun _ _ => own1) Unit (fun _ => iprop(True)) (fun _ => iprop(True)) () iprop(True)
  obtain ⟨_, ⟨_, e⟩, hx⟩ := hp true ⟨_, ⟨(), rfl⟩, rfl⟩
  subst e; exact Bool.noConfusion hx

-- `Iris.Inv.A_persistent` idx 5: necessary (GB, inv = own1, fupd = id: A holds at true, not at false)
theorem w5c2_28 : ¬ drop0% Iris.Inv.A_persistent 5 := fun h => by
  obtain ⟨hp⟩ := @h GB _ (fun _ X => X) Unit (fun _ _ => own1) Unit (fun _ => iprop(True)) (fun _ => iprop(True)) ()
  obtain ⟨_, ⟨_, e⟩, hx⟩ :=
    hp true ⟨_, ⟨iprop(False), rfl⟩, false, true, rfl, ⟨rfl, fun _ h => h⟩, _, ⟨(), rfl⟩, rfl⟩
  subst e
  obtain ⟨a, b, e2, ⟨ha, _⟩, hs⟩ := hx
  obtain ⟨_, ⟨_, e3⟩, hb⟩ := hs
  subst e3; cases ha; cases hb; exact absurd e2 (by decide)

-- `Iris.Linear.fupd_mono'` idx 5: necessary (GB, fupd = negation, False ⊢ True)
theorem w5c2_29 : ¬ drop0% Iris.Linear.fupd_mono' 5 := fun h =>
  (@h GB _ iprop(False) iprop(True) (fun _ _ X x => ¬ X x) .M0 .M0 (fun _ h => h.elim) true (fun h => h)) trivial

-- `Iris.Linear.fupd_mono'` idx 8: necessary (fupd = id, True ⊬ False)
theorem w5c2_30 : ¬ drop0% Iris.Linear.fupd_mono' 8 := fun h =>
  @h GB _ iprop(True) iprop(False) (fun _ _ X => X) (fun h => h) .M0 .M0 true trivial

-- `Iris.Linear.fupd_proper` idx 5: removable (P ⊣⊢ Q gives P = Q, `BiEntails.to_eq`)
theorem w5c2_31 : drop% Iris.Linear.fupd_proper 5 := by
  intro PROP _ P Q fupd E1 E2 h
  rw [Iris.BI.BIBase.BiEntails.to_eq h]; exact Iris.BI.BIBase.BiEntails.rfl

-- `Iris.Linear.fupd_proper` idx 8: necessary (fupd = id, True ⊣⊢ False fails)
theorem w5c2_32 : ¬ drop0% Iris.Linear.fupd_proper 8 := fun h =>
  (@h GB _ iprop(True) iprop(False) (fun _ _ X => X) (fun h => h) .M0 .M0).1 true trivial

-- `Iris.Linear.fupd_frame_right` idx 5: removable (frame_left plus commutativity; Q ∗ P = P ∗ Q by `BiEntails.to_eq`)
theorem w5c2_33 : drop% Iris.Linear.fupd_frame_right 5 := by
  intro PROP _ P Q fupd hfl E1 E2
  have e : iprop(Q ∗ P) = iprop(P ∗ Q) := Iris.BI.BIBase.BiEntails.to_eq sep_comm
  exact sep_comm.mp.trans (e ▸ @hfl E1 E2 Q P)

-- `Iris.Linear.fupd_frame_right` idx 6: necessary (AN, fupd = validity; P = True, Q = (n = 0))
theorem w5c2_34 : ¬ drop0% Iris.Linear.fupd_frame_right 6 := fun h =>
  absurd ((@h AN _ iprop(True) (fun n => n = 0) (fun _ _ => anV)
    (fun {_ _ P Q} (hPQ : P ⊢ Q) _ h m => (hPQ : ∀ x, P x → Q x) m (h m)) .M0 .M0)
    0 ⟨fun _ => trivial, rfl⟩ 1).2 (by decide)

-- `Iris.Linear.elim_fupd_fupd` idx 5: necessary (GB, fupd X = X or X empty; P = False, Q = own1)
theorem w5c2_35 : ¬ drop0% Iris.Linear.elim_fupd_fupd 5 := fun h => by
  have := (@h GB _ iprop(False) own1 (fun _ _ => gbE) gbE_trans gbE_frame_l .out false .M0 .M0 .M0).elim_modal trivial false
    ⟨false, false, rfl, .inr fun _ h => h, fun _ h => h.elim⟩
  exact this.elim (fun h => Bool.noConfusion h) (fun h => h true rfl)

-- `Iris.Linear.elim_fupd_fupd` idx 6: necessary (GB, fupd X = X ∗ own1; P = Q = emp)
theorem w5c2_36 : ¬ drop0% Iris.Linear.elim_fupd_fupd 6 := fun h => by
  have := (@h GB _ iprop(emp) iprop(emp) (fun _ _ X => iprop(X ∗ own1))
    (fun hPQ => sep_mono hPQ .rfl) sep_assoc.mpr .out false .M0 .M0 .M0).elim_modal trivial false
    ⟨true, true, rfl, ⟨false, true, rfl, rfl, rfl⟩, fun y hy => by cases hy; exact ⟨false, true, rfl, rfl, rfl⟩⟩
  obtain ⟨a, b, e, ha, hb⟩ := this
  cases ha; cases hb; exact absurd e (by decide)

-- `Iris.Linear.elim_fupd_fupd` idx 7: necessary (GB, fupd X = X ∨ own1; P = Q = False)
theorem w5c2_37 : ¬ drop0% Iris.Linear.elim_fupd_fupd 7 := fun h => by
  have := (@h GB _ iprop(False) iprop(False) (fun _ _ X x => X x ∨ x = true)
    (fun hPQ x hx => hx.imp (hPQ x) id) (fun x h => h.elim id .inr) .out false .M0 .M0 .M0).elim_modal trivial false
    ⟨true, true, rfl, .inr rfl, fun _ h => h.elim⟩
  exact this.elim id (fun h => Bool.noConfusion h)

-- `Iris.LoebEM.later_anything` idx 3: removable (case split on em (later False); the negative case is Löb for False)
theorem w5c2_38 : drop% Iris.LoebEM.later_anything 3 := by
  intro PROP P _ em _
  exact (em iprop(▷ False)).trans (or_elim (later_mono false_elim) (loeb.trans false_elim))

-- `Iris.LoebEM.later_inconsistent` idx 2: removable (same argument, Löb from Sbi, then later soundness)
theorem w5c2_39 : drop% Iris.LoebEM.later_inconsistent 2 := by
  intro PROP _ em
  exact later_soundness ((em iprop(▷ False)).trans (or_elim .rfl (loeb.trans false_elim)))

-- `Iris.Inv.inv_fupd'` idx 2: removable (inv_fupd with Q the wand and wand elimination, then fupd_fupd; no affinity used)
theorem w5c2_40 : drop% Iris.Inv.inv_fupd' 2 := by
  intro PROP _ P R fupd name inv _ hff hinv i
  exact (@hinv i P _ _ wand_elim_right).trans hff

-- `Iris.Inv.inv_fupd'` idx 8: removable (same proof; persistence of inv unused)
theorem w5c2_41 : drop% Iris.Inv.inv_fupd' 8 := by
  intro PROP _ _ P R fupd name inv hff hinv i
  exact (@hinv i P _ _ wand_elim_right).trans hff

-- `Iris.Inv.inv_fupd'` idx 9: necessary (AN, fupd = shift by one, inv = id; P = True, R = (2 ≤ n), at 0)
theorem w5c2_42 : ¬ drop0% Iris.Inv.inv_fupd' 9 := fun h =>
  absurd (@h AN _ _ iprop(True) (fun n => 2 ≤ n) (fun _ X n => X (n + 1)) Unit (fun _ P => P) _
    (fun P Q R hp n hx => (hp n hx).2) () 0 ⟨trivial, fun _ => ⟨trivial, by decide⟩⟩) (by decide)

-- `Iris.Inv.inv_fupd'` idx 10: necessary (AN, fupd = id, inv = True; P = R = False)
theorem w5c2_43 : ¬ drop0% Iris.Inv.inv_fupd' 10 := fun h =>
  @h AN _ _ iprop(False) iprop(False) (fun _ X => X) Unit (fun _ _ => iprop(True)) _
    (fun _ h => h) () 0 ⟨trivial, fun h => h.elim⟩

-- `Iris.SavedProp.contradiction` idx 14: necessary (AN, bupd = True, saved i P := (i = P))
theorem w5c2_44 : ¬ drop0% Iris.SavedProp.contradiction 14 := fun h =>
  @h AN _ _ _ (fun _ _ => True) AN anEq (fun _ _ => ⟨fun _ h => h⟩)
    (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) an_agree

-- `Iris.SavedProp.contradiction` idx 12: necessary (AN, empty ident, bupd = id)
theorem w5c2_45 : ¬ drop0% Iris.SavedProp.contradiction 12 := fun h =>
  @h AN _ _ _ id Empty (fun _ _ => iprop(True)) _
    (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h) (fun i => i.elim) (fun hf => hf 0 trivial)

-- `Iris.SavedProp.contradiction` idx 13: necessary (AN, ident = Unit, saved = True, bupd = id)
theorem w5c2_46 : ¬ drop0% Iris.SavedProp.contradiction 13 := fun h =>
  @h AN _ _ _ id Unit (fun _ _ => iprop(True)) _
    (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h) (fun _ _ => ⟨_, ⟨(), rfl⟩, trivial⟩)
    (fun hf => hf 0 trivial)

-- `Iris.SavedProp.saved_NA` idx 7: necessary (AN, ident = Unit, saved = True: A holds via P = False)
theorem w5c2_47 : ¬ drop0% Iris.SavedProp.saved_NA 7 := fun h =>
  @h AN _ _ _ Unit (fun _ _ => iprop(True)) _ () 0 trivial
    ⟨_, ⟨iprop(False), rfl⟩, trivial, fun h => h, trivial⟩

-- `Iris.SavedProp.contradiction` idx 8: removable (saved_A and saved_NA make the allocated name contradictory, so the allocated proposition equals False and alloc plus consistency suffice)
theorem w5c2_48 : drop% Iris.SavedProp.contradiction 8 := by
  intro PROP _ _ _ bupd ident saved _ _ _ _ alloc agree cons
  apply cons
  have hF : iprop(∃ i, saved i (Iris.SavedProp.A ident saved i)) ⊣⊢ iprop(False) :=
    ⟨exists_elim fun i => (and_intro (Iris.SavedProp.saved_NA ident saved agree i)
      (Iris.SavedProp.saved_A ident saved agree i)).trans imp_elim_left, false_elim⟩
  rw [← Iris.BI.BIBase.BiEntails.to_eq hF]
  exact alloc

-- `Iris.SavedProp.contradiction` idx 9: removable (saved_A and saved_NA make the allocated name contradictory, so the allocated proposition equals False and alloc plus consistency suffice)
theorem w5c2_49 : drop% Iris.SavedProp.contradiction 9 := by
  intro PROP _ _ _ bupd ident saved _ _ _ _ alloc agree cons
  apply cons
  have hF : iprop(∃ i, saved i (Iris.SavedProp.A ident saved i)) ⊣⊢ iprop(False) :=
    ⟨exists_elim fun i => (and_intro (Iris.SavedProp.saved_NA ident saved agree i)
      (Iris.SavedProp.saved_A ident saved agree i)).trans imp_elim_left, false_elim⟩
  rw [← Iris.BI.BIBase.BiEntails.to_eq hF]
  exact alloc

-- `Iris.SavedProp.contradiction` idx 10: removable (saved_A and saved_NA make the allocated name contradictory, so the allocated proposition equals False and alloc plus consistency suffice)
theorem w5c2_50 : drop% Iris.SavedProp.contradiction 10 := by
  intro PROP _ _ _ bupd ident saved _ _ _ _ alloc agree cons
  apply cons
  have hF : iprop(∃ i, saved i (Iris.SavedProp.A ident saved i)) ⊣⊢ iprop(False) :=
    ⟨exists_elim fun i => (and_intro (Iris.SavedProp.saved_NA ident saved agree i)
      (Iris.SavedProp.saved_A ident saved agree i)).trans imp_elim_left, false_elim⟩
  rw [← Iris.BI.BIBase.BiEntails.to_eq hF]
  exact alloc

-- `Iris.SavedProp.contradiction` idx 11: removable (saved_A and saved_NA make the allocated name contradictory, so the allocated proposition equals False and alloc plus consistency suffice)
theorem w5c2_51 : drop% Iris.SavedProp.contradiction 11 := by
  intro PROP _ _ _ bupd ident saved _ _ _ _ alloc agree cons
  apply cons
  have hF : iprop(∃ i, saved i (Iris.SavedProp.A ident saved i)) ⊣⊢ iprop(False) :=
    ⟨exists_elim fun i => (and_intro (Iris.SavedProp.saved_NA ident saved agree i)
      (Iris.SavedProp.saved_A ident saved agree i)).trans imp_elim_left, false_elim⟩
  rw [← Iris.BI.BIBase.BiEntails.to_eq hF]
  exact alloc

-- `Iris.Inv.saved_alloc` idx 16: necessary (AN, empty gname, fupd = id, inv = id)
theorem w5c2_52 : ¬ drop0% Iris.Inv.saved_alloc 16 := fun h => by
  obtain ⟨_, ⟨γ, _⟩, _⟩ := @h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h)
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun P x hp => ⟨_, ⟨(), rfl⟩, hp⟩)
    Empty (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => iprop(True)) 0 trivial
  exact γ.elim

-- `Iris.Inv.saved_alloc` idx 11: necessary (AN, fupd M0 = True, fupd M1 = id; start = finished = False)
theorem w5c2_53 : ¬ drop0% Iris.Inv.saved_alloc 11 := fun h => by
  have := @h AN _ _ anM Unit (fun _ P => P) _ (fun _ h => .inr h) anM_mono anM_ff anM_fl
    (fun P x hp => .inr ⟨_, ⟨(), rfl⟩, hp⟩) Unit (fun _ => iprop(False)) (fun _ => iprop(False))
    (fun _ _ => .inl rfl) (fun _ => iprop(True)) 0 trivial
  rcases this with e | ⟨_, ⟨γ, e⟩, hx⟩
  · exact Iris.Inv.Mask.noConfusion e
  · subst e; obtain ⟨_, ⟨_, e2⟩, hx⟩ := hx; subst e2
    rcases hx with hx | ⟨hx, _⟩ <;> exact hx

-- `Iris.Inv.saved_alloc` idx 8: necessary (AN, fupd X = X or X empty; start = False, finished = (n = 0), at 1)
theorem w5c2_54 : ¬ drop0% Iris.Inv.saved_alloc 8 := fun h => by
  have := @h AN _ _ (fun _ => anE) Unit (fun _ P => P) _ (fun _ h => .inl h) (anE_ff (E := .M0)) (anE_fl (E := .M0))
    (fun _ h => h) (fun P x hp => .inl ⟨_, ⟨(), rfl⟩, hp⟩) Unit (fun _ => iprop(False)) (fun _ n => n = 0)
    (fun _ _ => .inr fun _ ⟨_, ⟨_, e⟩, hp⟩ => by subst e; exact hp) (fun _ => iprop(True)) 1 trivial
  rcases this with ⟨_, ⟨γ, e⟩, hx⟩ | hn
  · subst e; obtain ⟨_, ⟨_, e2⟩, hx⟩ := hx; subst e2
    rcases hx with hx | ⟨hx, _⟩
    · exact hx
    · exact absurd hx (by decide)
  · exact hn 0 ⟨_, ⟨(), rfl⟩, _, ⟨(), rfl⟩, .inr ⟨rfl, trivial, trivial⟩⟩

-- `Iris.Inv.saved_alloc` idx 2: removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; no affinity used)
theorem w5c2_55 : drop% Iris.Inv.saved_alloc 2 := by
  intro PROP _ fupd name inv _ hi hm hff hfl hmm hia gname start finished sts P
  exact (sts.trans hmm).trans ((hm (exists_elim fun γ => or_intro_l.trans ((hia _).trans
    (hm (exists_intro (Ψ := fun γ => Iris.Inv.saved name inv gname start finished γ (P γ)) γ))))).trans hff)

-- `Iris.Inv.saved_alloc` idx 6: removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; persistence of inv unused)
theorem w5c2_56 : drop% Iris.Inv.saved_alloc 6 := by
  intro PROP _ _ fupd name inv hi hm hff hfl hmm hia gname start finished sts P
  exact (sts.trans hmm).trans ((hm (exists_elim fun γ => or_intro_l.trans ((hia _).trans
    (hm (exists_intro (Ψ := fun γ => Iris.Inv.saved name inv gname start finished γ (P γ)) γ))))).trans hff)

-- `Iris.Inv.saved_alloc` idx 7: removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; fupd_intro unused)
theorem w5c2_57 : drop% Iris.Inv.saved_alloc 7 := by
  intro PROP _ _ fupd name inv _ hm hff hfl hmm hia gname start finished sts P
  exact (sts.trans hmm).trans ((hm (exists_elim fun γ => or_intro_l.trans ((hia _).trans
    (hm (exists_intro (Ψ := fun γ => Iris.Inv.saved name inv gname start finished γ (P γ)) γ))))).trans hff)

-- `Iris.Inv.saved_alloc` idx 10: removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; fupd_frame_left unused)
theorem w5c2_58 : drop% Iris.Inv.saved_alloc 10 := by
  intro PROP _ _ fupd name inv _ hi hm hff hmm hia gname start finished sts P
  exact (sts.trans hmm).trans ((hm (exists_elim fun γ => or_intro_l.trans ((hia _).trans
    (hm (exists_intro (Ψ := fun γ => Iris.Inv.saved name inv gname start finished γ (P γ)) γ))))).trans hff)

-- `Iris.Inv.A_alloc` idx 2: removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; no affinity used)
theorem w5c2_59 : drop% Iris.Inv.A_alloc 2 := by
  intro PROP _ fupd name inv _ hi hm hff hfl hmm hia gname start finished sts
  exact (sts.trans hmm).trans ((hm (exists_elim fun γ => or_intro_l.trans ((hia _).trans
    (hm (exists_intro (Ψ := fun γ => Iris.Inv.saved name inv gname start finished γ (Iris.Inv.A fupd name inv gname start finished γ)) γ))))).trans hff)

-- `Iris.Inv.A_alloc` idx 6: removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; persistence of inv unused)
theorem w5c2_60 : drop% Iris.Inv.A_alloc 6 := by
  intro PROP _ _ fupd name inv hi hm hff hfl hmm hia gname start finished sts
  exact (sts.trans hmm).trans ((hm (exists_elim fun γ => or_intro_l.trans ((hia _).trans
    (hm (exists_intro (Ψ := fun γ => Iris.Inv.saved name inv gname start finished γ (Iris.Inv.A fupd name inv gname start finished γ)) γ))))).trans hff)

-- `Iris.Inv.A_alloc` idx 7: removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; fupd_intro unused)
theorem w5c2_61 : drop% Iris.Inv.A_alloc 7 := by
  intro PROP _ _ fupd name inv _ hm hff hfl hmm hia gname start finished sts
  exact (sts.trans hmm).trans ((hm (exists_elim fun γ => or_intro_l.trans ((hia _).trans
    (hm (exists_intro (Ψ := fun γ => Iris.Inv.saved name inv gname start finished γ (Iris.Inv.A fupd name inv gname start finished γ)) γ))))).trans hff)

-- `Iris.Inv.A_alloc` idx 10: removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; fupd_frame_left unused)
theorem w5c2_62 : drop% Iris.Inv.A_alloc 10 := by
  intro PROP _ _ fupd name inv _ hi hm hff hmm hia gname start finished sts
  exact (sts.trans hmm).trans ((hm (exists_elim fun γ => or_intro_l.trans ((hia _).trans
    (hm (exists_intro (Ψ := fun γ => Iris.Inv.saved name inv gname start finished γ (Iris.Inv.A fupd name inv gname start finished γ)) γ))))).trans hff)

-- `Iris.Inv.A_alloc` idx 16: necessary (AN, empty gname, fupd = id, inv = id)
theorem w5c2_63 : ¬ drop0% Iris.Inv.A_alloc 16 := fun h => by
  obtain ⟨_, ⟨γ, _⟩, _⟩ := @h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h)
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun P x hp => ⟨_, ⟨(), rfl⟩, hp⟩)
    Empty (fun _ => iprop(True)) (fun _ => iprop(True)) 0 trivial
  exact γ.elim

-- `Iris.Inv.A_alloc` idx 12: necessary (AN, inv = False, fupd = id, start = True)
theorem w5c2_64 : ¬ drop0% Iris.Inv.A_alloc 12 := fun h => by
  obtain ⟨_, ⟨_, e⟩, hx⟩ := @h AN _ _ (fun _ X => X) Unit (fun _ _ => iprop(False)) _ (fun _ h => h) (fun h => h)
    (fun _ h => h) (fun _ h => h) (fun _ h => h)
    Unit (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ _ => ⟨_, ⟨(), rfl⟩, trivial⟩) 0 trivial
  subst e; obtain ⟨_, ⟨_, e2⟩, hx⟩ := hx; subst e2; exact hx

-- `Iris.Inv.A_alloc` idx 11: necessary (AN, fupd M0 = True, fupd M1 = id; start = finished = False)
theorem w5c2_65 : ¬ drop0% Iris.Inv.A_alloc 11 := fun h => by
  have := @h AN _ _ anM Unit (fun _ P => P) _ (fun _ h => .inr h) anM_mono anM_ff anM_fl
    (fun P x hp => .inr ⟨_, ⟨(), rfl⟩, hp⟩) Unit (fun _ => iprop(False)) (fun _ => iprop(False))
    (fun _ _ => .inl rfl) 0 trivial
  rcases this with e | ⟨_, ⟨γ, e⟩, hx⟩
  · exact Iris.Inv.Mask.noConfusion e
  · subst e; obtain ⟨_, ⟨_, e2⟩, hx⟩ := hx; subst e2
    rcases hx with hx | ⟨hx, _⟩ <;> exact hx

-- `Iris.Inv.A_alloc` idx 8: necessary (AN, fupd X = X or X empty; start = False, finished = (n = 0), at 1)
theorem w5c2_66 : ¬ drop0% Iris.Inv.A_alloc 8 := fun h => by
  have := @h AN _ _ (fun _ => anE) Unit (fun _ P => P) _ (fun _ h => .inl h) (anE_ff (E := .M0)) (anE_fl (E := .M0))
    (fun _ h => h) (fun P x hp => .inl ⟨_, ⟨(), rfl⟩, hp⟩) Unit (fun _ => iprop(False)) (fun _ n => n = 0)
    (fun _ _ => .inr fun _ ⟨_, ⟨_, e⟩, hp⟩ => by subst e; exact hp) 1 trivial
  rcases this with ⟨_, ⟨γ, e⟩, hx⟩ | hn
  · subst e; obtain ⟨_, ⟨_, e2⟩, hx⟩ := hx; subst e2
    rcases hx with hx | ⟨hx, _⟩
    · exact hx
    · exact absurd hx (by decide)
  · exact hn 0 ⟨_, ⟨(), rfl⟩, _, ⟨(), rfl⟩, .inr ⟨rfl, trivial,
      ⟨_, ⟨iprop(True), rfl⟩, ⟨trivial, fun _ => .inr fun _ h => h⟩, ⟨_, ⟨(), rfl⟩, .inr ⟨rfl, trivial, trivial⟩⟩⟩⟩⟩

-- `Iris.Inv.saved_cast` idx 13: necessary (AN, fupd = id, inv = True; P = True, Q = False)
theorem w5c2_67 : ¬ drop0% Iris.Inv.saved_cast 13 := fun h =>
  (@h AN _ _ iprop(True) iprop(False) (fun _ X => X) Unit (fun _ _ => iprop(True)) _ (fun _ h => h) (fun h => h)
    (fun _ h => h) (fun _ h => h) Unit (fun _ => iprop(False)) (fun _ => iprop(False))
    (fun _ _ h => h) (fun _ _ h => h.1) (fun _ _ h => ⟨h, h⟩) () 0
    ⟨⟨_, ⟨(), rfl⟩, trivial⟩, ⟨_, ⟨(), rfl⟩, trivial⟩, trivial, trivial⟩).2

-- `Iris.Inv.saved_cast` idx 17: necessary (AN, fupd = id, inv = id; start = True, finished = False)
theorem w5c2_68 : ¬ drop0% Iris.Inv.saved_cast 17 := fun h =>
  (@h AN _ _ iprop(True) iprop(False) (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h)
    (fun _ h => h) (fun _ h => h) (fun P Q R hp x hx => (hp x hx).2) Unit (fun _ => iprop(True)) (fun _ => iprop(False))
    (fun _ _ h => h.2) (fun _ _ h => ⟨h, h⟩) () 0
    ⟨⟨_, ⟨(), rfl⟩, .inl trivial⟩, ⟨_, ⟨(), rfl⟩, .inl trivial⟩, trivial, trivial⟩).2

-- `Iris.Inv.saved_cast` idx 18: necessary (AN, fupd = id, inv = id; start = finished = True)
theorem w5c2_69 : ¬ drop0% Iris.Inv.saved_cast 18 := fun h =>
  (@h AN _ _ iprop(True) iprop(False) (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h)
    (fun _ h => h) (fun _ h => h) (fun P Q R hp x hx => (hp x hx).2) Unit (fun _ => iprop(True)) (fun _ => iprop(True))
    (fun _ _ h => h) (fun _ _ h => ⟨h, h⟩) () 0
    ⟨⟨_, ⟨(), rfl⟩, .inl trivial⟩, ⟨_, ⟨(), rfl⟩, .inl trivial⟩, trivial, trivial⟩).2

-- `Iris.Inv.saved_cast` idx 9: necessary (AN, fupd X = X ∧ (n = 0) has no intro; inv = id, start = False, finished = True, at 1)
theorem w5c2_70 : ¬ drop0% Iris.Inv.saved_cast 9 := fun h =>
  absurd (@h AN _ _ iprop(True) iprop(True) (fun _ X x => X x ∧ x = 0) Unit (fun _ P => P) _
    (fun {_ P Q} (hPQ : P ⊢ Q) x hx => ⟨(hPQ : ∀ x, P x → Q x) x hx.1, hx.2⟩) (fun _ h => h.1)
    (fun _ ⟨hp, hq, hc⟩ => ⟨⟨hp, hq⟩, hc⟩) (fun P Q R hp x hx => ⟨(hp x hx).1.2, (hp x hx).2⟩)
    Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ _ h => h.elim) (fun _ _ h => h.1) (fun _ _ h => ⟨h, h⟩) () 1
    ⟨⟨_, ⟨(), rfl⟩, .inr ⟨trivial, trivial, trivial⟩⟩, ⟨_, ⟨(), rfl⟩, .inr ⟨trivial, trivial, trivial⟩⟩, trivial, trivial⟩).2
    (by decide)

-- `Iris.Inv.saved_cast` idx 10: necessary (AN, fupd X = X or X empty, inv i X = X valid; start = True, finished = False; P = True, Q = (n = 0), at 1)
theorem w5c2_71 : ¬ drop0% Iris.Inv.saved_cast 10 := fun h => by
  have := @h AN _ _ iprop(True) (fun n => n = 0) (fun _ => anE) Unit (fun _ X _ => ∀ n, X n) (fun _ _ => anPers _)
    (fun _ h => .inl h) (anE_ff (E := .M0)) (anE_fl (E := .M0))
    (fun P Q R hp x ⟨hP, hQ⟩ => (hp x ⟨hP x, hQ⟩).elim (fun h => .inl h.2) (fun hn => .inr fun y hy => hn y ⟨hP y, hy⟩))
    Unit (fun _ => iprop(True)) (fun _ => iprop(False))
    (fun _ _ _ => .inr fun _ h => h) (fun _ _ h => h.2) (fun _ _ h => ⟨h, h⟩) () 1
    ⟨⟨_, ⟨(), rfl⟩, fun _ => .inl trivial⟩, ⟨_, ⟨(), rfl⟩, fun _ => .inl trivial⟩, trivial, trivial⟩
  rcases this with h1 | hn
  · have h2 : (1 : Nat) = 0 := h1.2
    exact absurd h2 (by decide)
  · exact hn 0 ⟨trivial, rfl⟩

-- `Iris.Inv.saved_cast` idx 12: necessary (AN, fupd X = X nonempty (no framing), inv = id; start = (n = 0), finished = (n = 1); P = True, Q = False)
theorem w5c2_72 : ¬ drop0% Iris.Inv.saved_cast 12 := fun h => by
  obtain ⟨_, _, hf⟩ := @h AN _ _ iprop(True) iprop(False) (fun _ => anN) Unit (fun _ P => P) _
    (fun x h => ⟨x, h⟩) (fun {_ P Q} (hPQ : P ⊢ Q) _ ⟨y, hy⟩ => ⟨y, (hPQ : ∀ x, P x → Q x) y hy⟩)
    (fun _ ⟨_, h⟩ => h) (fun P Q R hp x hx => let ⟨y, h⟩ := hp x hx; ⟨y, h.2⟩)
    Unit (fun _ n => n = 0) (fun _ n => n = 1)
    (fun _ _ _ => ⟨1, rfl⟩) (fun _ x h => absurd (h.1.symm.trans h.2) (by decide)) (fun _ _ h => ⟨h, h⟩) () 0
    ⟨⟨_, ⟨(), rfl⟩, .inl rfl⟩, ⟨_, ⟨(), rfl⟩, .inl rfl⟩, trivial, trivial⟩
  exact hf

-- `Iris.Inv.saved_NA` idx 11: necessary (AN, fupd = id, inv = True: A holds via P = False)
theorem w5c2_73 : ¬ drop0% Iris.Inv.saved_NA 11 := fun h =>
  (@h AN _ _ (fun _ X => X) Unit (fun _ _ => iprop(True)) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    Unit (fun _ => iprop(False)) (fun _ => iprop(False)) (fun _ _ h => h) (fun _ _ h => h.1) (fun _ _ h => ⟨h, h⟩) ()
    0 ⟨_, ⟨(), rfl⟩, trivial⟩).2 ⟨_, ⟨iprop(False), rfl⟩, ⟨trivial, fun h => h⟩, ⟨_, ⟨(), rfl⟩, trivial⟩⟩

-- `Iris.Inv.saved_NA` idx 15: necessary (AN, fupd = id, inv = id; start = True, finished = False)
theorem w5c2_74 : ¬ drop0% Iris.Inv.saved_NA 15 := fun h =>
  (@h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun P Q R hp x hx => (hp x hx).2) Unit (fun _ => iprop(True)) (fun _ => iprop(False))
    (fun _ _ h => h.2) (fun _ _ h => ⟨h, h⟩) ()
    0 ⟨_, ⟨(), rfl⟩, .inl trivial⟩).2 ⟨_, ⟨iprop(False), rfl⟩, ⟨trivial, fun h => h⟩, ⟨_, ⟨(), rfl⟩, .inl trivial⟩⟩

-- `Iris.Inv.saved_NA` idx 16: necessary (AN, fupd = id, inv = id; start = finished = True)
theorem w5c2_75 : ¬ drop0% Iris.Inv.saved_NA 16 := fun h =>
  (@h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun P Q R hp x hx => (hp x hx).2) Unit (fun _ => iprop(True)) (fun _ => iprop(True))
    (fun _ _ h => h) (fun _ _ h => ⟨h, h⟩) ()
    0 ⟨_, ⟨(), rfl⟩, .inl trivial⟩).2 ⟨_, ⟨iprop(False), rfl⟩, ⟨trivial, fun h => h⟩, ⟨_, ⟨(), rfl⟩, .inl trivial⟩⟩

-- `Iris.Inv.saved_NA` idx 10: necessary (AN, fupd X = X nonempty (no framing), inv = id; start = (n = 0), finished = (n = 1))
theorem w5c2_76 : ¬ drop0% Iris.Inv.saved_NA 10 := fun h => by
  obtain ⟨_, h⟩ := (@h AN _ _ (fun _ => anN) Unit (fun _ P => P) _
    (fun x h => ⟨x, h⟩) (fun {_ P Q} (hPQ : P ⊢ Q) _ ⟨y, hy⟩ => ⟨y, (hPQ : ∀ x, P x → Q x) y hy⟩)
    (fun _ ⟨_, h⟩ => h) (fun P Q R hp x hx => let ⟨y, h⟩ := hp x hx; ⟨y, h.2⟩)
    Unit (fun _ n => n = 0) (fun _ n => n = 1)
    (fun _ _ _ => ⟨1, rfl⟩) (fun _ x h => absurd (h.1.symm.trans h.2) (by decide)) (fun _ _ h => ⟨h, h⟩) ()
    0 ⟨_, ⟨(), rfl⟩, .inl rfl⟩).2 ⟨_, ⟨iprop(False), rfl⟩, ⟨trivial, fun h => h.elim⟩, ⟨_, ⟨(), rfl⟩, .inl rfl⟩⟩
  exact h

-- `Iris.LaterCreditsPlain.laterN_False` idx 2: removable (later of an existential splits into later False or an existential of laters, so the predicate is closed under later; weak Löb)
theorem w5c2_77 : drop% Iris.LaterCreditsPlain.laterN_False 2 := by
  intro PROP _ _
  refine true_intro.trans (loeb_weak ?_)
  exact later_exists_false.trans (or_elim (exists_intro (Ψ := fun n => iprop(▷^[n] False)) 1)
    (exists_elim fun n => exists_intro (Ψ := fun n => iprop(▷^[n] False)) (n + 1)))

-- `Iris.Inv.finished_contradiction` idx 9: necessary (AN, fupd = id, inv = True, finished = True, start = False)
theorem w5c2_78 : ¬ drop0% Iris.Inv.finished_contradiction 9 := fun h =>
  (@h AN _ _ (fun _ X => X) Unit (fun _ _ => iprop(True)) _ (fun _ h => h) (fun _ h => h)
    Unit (fun _ => iprop(False)) (fun _ => iprop(True)) _ (fun _ _ h => h.1) () () 0 ⟨trivial, trivial⟩).2

-- `Iris.Inv.finished_contradiction` idx 14: necessary (AN, fupd = id, inv = id, start = finished = True)
theorem w5c2_79 : ¬ drop0% Iris.Inv.finished_contradiction 14 := fun h =>
  (@h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun _ h => h)
    (fun P Q R hp x hx => (hp x hx).2) Unit (fun _ => iprop(True)) (fun _ => iprop(True)) _ () () 0
    ⟨trivial, .inl trivial⟩).2

-- `Iris.Inv.invariant_contradiction` idx 11: necessary (AN, fupd = id, inv = True)
theorem w5c2_80 : ¬ drop0% Iris.Inv.invariant_contradiction 11 := fun h =>
  (@h AN _ _ (fun _ X => X) Unit (fun _ _ => iprop(True)) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    Unit (fun _ => iprop(False)) (fun _ => iprop(False)) _ (fun _ _ h => h) (fun _ _ h => h.1) () () 0 trivial).2

-- `Iris.Inv.invariant_contradiction` idx 16: necessary (AN, fupd = id, inv = id, start = True, finished = False)
theorem w5c2_81 : ¬ drop0% Iris.Inv.invariant_contradiction 16 := fun h =>
  (@h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun P Q R hp x hx => (hp x hx).2) Unit (fun _ => iprop(True)) (fun _ => iprop(False)) _
    (fun _ _ h => h.2) () () 0 (.inl trivial)).2

-- `Iris.Inv.invariant_contradiction` idx 17: necessary (AN, fupd = id, inv = id, start = finished = True)
theorem w5c2_82 : ¬ drop0% Iris.Inv.invariant_contradiction 17 := fun h =>
  (@h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun P Q R hp x hx => (hp x hx).2) Unit (fun _ => iprop(True)) (fun _ => iprop(True)) _
    (fun _ _ h => h) () () 0 (.inl trivial)).2

-- `Iris.Inv.invariant_contradiction` idx 10: necessary (AN, fupd X = X nonempty (no framing), inv = id; start = (n = 0), finished = (n = 1))
theorem w5c2_83 : ¬ drop0% Iris.Inv.invariant_contradiction 10 := fun h => by
  obtain ⟨_, h⟩ := (@h AN _ _ (fun _ => anN) Unit (fun _ P => P) _
    (fun x h => ⟨x, h⟩) (fun {_ P Q} (hPQ : P ⊢ Q) _ ⟨y, hy⟩ => ⟨y, (hPQ : ∀ x, P x → Q x) y hy⟩)
    (fun _ ⟨_, h⟩ => h) (fun P Q R hp x hx => let ⟨y, h⟩ := hp x hx; ⟨y, h.2⟩)
    Unit (fun _ n => n = 0) (fun _ n => n = 1) (fun _ => anPers _)
    (fun _ _ _ => ⟨1, rfl⟩) (fun _ x h => absurd (h.1.symm.trans h.2) (by decide)) () () 0 (.inl rfl)).2
  exact h

-- `Iris.Inv.contradiction` idx 14: necessary (AN, fupd = True: all other rules hold)
theorem w5c2_84 : ¬ drop0% Iris.Inv.contradiction 14 := fun h =>
  @h AN _ _ (fun _ _ _ => True) Unit (fun _ P => P) _ (fun _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ h => h.1) (fun _ _ h => ⟨h, h⟩)

-- `Iris.Inv.contradiction` idx 18: necessary (AN, fupd = id, inv = id, empty gname)
theorem w5c2_85 : ¬ drop0% Iris.Inv.contradiction 18 := fun h =>
  @h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun _ h => h) (fun P x hp => ⟨_, ⟨(), rfl⟩, hp⟩) (fun P Q R hp x hx => (hp x hx).2) (fun hf => hf 0 trivial)
    Empty (fun _ => iprop(True)) (fun _ => iprop(True)) (fun γ => γ.elim) (fun γ => γ.elim) (fun γ => γ.elim)

-- `Iris.Inv.contradiction` idx 19: necessary (AN, fupd = id, inv = id, start = True, finished = False)
theorem w5c2_86 : ¬ drop0% Iris.Inv.contradiction 19 := fun h =>
  @h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun _ h => h) (fun P x hp => ⟨_, ⟨(), rfl⟩, hp⟩) (fun P Q R hp x hx => (hp x hx).2) (fun hf => hf 0 trivial)
    Unit (fun _ => iprop(True)) (fun _ => iprop(False)) (fun _ _ => ⟨_, ⟨(), rfl⟩, trivial⟩)
    (fun _ _ h => h.2) (fun _ _ h => ⟨h, h⟩)

-- `Iris.Inv.contradiction` idx 20: necessary (AN, fupd = id, inv = id, start = finished = True)
theorem w5c2_87 : ¬ drop0% Iris.Inv.contradiction 20 := fun h =>
  @h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun _ h => h) (fun P x hp => ⟨_, ⟨(), rfl⟩, hp⟩) (fun P Q R hp x hx => (hp x hx).2) (fun hf => hf 0 trivial)
    Unit (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ _ => ⟨_, ⟨(), rfl⟩, trivial⟩)
    (fun _ _ h => h) (fun _ _ h => ⟨h, h⟩)

-- `Iris.Inv.contradiction` idx 10: necessary (AN, fupd X = X nonempty (no framing), inv = id; start = (n = 0), finished = (n = 1))
theorem w5c2_88 : ¬ drop0% Iris.Inv.contradiction 10 := fun h =>
  @h AN _ _ (fun _ => anN) Unit (fun _ P => P) _
    (fun x h => ⟨x, h⟩) (fun {_ P Q} (hPQ : P ⊢ Q) _ ⟨y, hy⟩ => ⟨y, (hPQ : ∀ x, P x → Q x) y hy⟩)
    (fun _ ⟨_, h⟩ => h) (fun _ h => h) (fun P x hp => ⟨x, _, ⟨(), rfl⟩, hp⟩)
    (fun P Q R hp x hx => let ⟨y, h⟩ := hp x hx; ⟨y, h.2⟩) (fun hf => let ⟨_, h⟩ := hf 0 trivial; h)
    Unit (fun _ n => n = 0) (fun _ n => n = 1) (fun _ _ => ⟨0, _, ⟨(), rfl⟩, rfl⟩)
    (fun _ _ _ => ⟨1, rfl⟩) (fun _ x h => absurd (h.1.symm.trans h.2) (by decide)) (fun _ _ h => ⟨h, h⟩)

-- `Iris.Inv.contradiction'` idx 14: necessary (AN, fupd = True: all other rules hold)
theorem w5c2_89 : ¬ drop0% Iris.Inv.contradiction' 14 := fun h =>
  @h AN _ _ (fun _ _ _ => True) Unit (fun _ P => P) _ (fun _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) Unit (fun _ => iprop(False)) (fun _ => iprop(True)) _
    (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ h => h.1)

-- `Iris.Inv.contradiction'` idx 19: necessary (AN, fupd = id, inv = id, empty gname)
theorem w5c2_90 : ¬ drop0% Iris.Inv.contradiction' 19 := fun h =>
  @h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun _ h => h) (fun P x hp => ⟨_, ⟨(), rfl⟩, hp⟩) (fun P Q R hp x hx => (hp x hx).2) (fun hf => hf 0 trivial)
    Empty (fun _ => iprop(True)) (fun _ => iprop(True)) _ (fun γ => γ.elim) (fun γ => γ.elim)

-- `Iris.Inv.contradiction'` idx 20: necessary (AN, fupd = id, inv = id, start = True, finished = False)
theorem w5c2_91 : ¬ drop0% Iris.Inv.contradiction' 20 := fun h =>
  @h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun _ h => h) (fun P x hp => ⟨_, ⟨(), rfl⟩, hp⟩) (fun P Q R hp x hx => (hp x hx).2) (fun hf => hf 0 trivial)
    Unit (fun _ => iprop(True)) (fun _ => iprop(False)) _ (fun _ _ => ⟨_, ⟨(), rfl⟩, trivial⟩)
    (fun _ _ h => h.2)

-- `Iris.Inv.contradiction'` idx 21: necessary (AN, fupd = id, inv = id, start = finished = True)
theorem w5c2_92 : ¬ drop0% Iris.Inv.contradiction' 21 := fun h =>
  @h AN _ _ (fun _ X => X) Unit (fun _ P => P) _ (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun _ h => h) (fun P x hp => ⟨_, ⟨(), rfl⟩, hp⟩) (fun P Q R hp x hx => (hp x hx).2) (fun hf => hf 0 trivial)
    Unit (fun _ => iprop(True)) (fun _ => iprop(True)) _ (fun _ _ => ⟨_, ⟨(), rfl⟩, trivial⟩)
    (fun _ _ h => h)

-- `Iris.Inv.contradiction'` idx 10: necessary (AN, fupd X = X nonempty (no framing), inv = id; start = (n = 0), finished = (n = 1))
theorem w5c2_93 : ¬ drop0% Iris.Inv.contradiction' 10 := fun h =>
  @h AN _ _ (fun _ => anN) Unit (fun _ P => P) _
    (fun x h => ⟨x, h⟩) (fun {_ P Q} (hPQ : P ⊢ Q) _ ⟨y, hy⟩ => ⟨y, (hPQ : ∀ x, P x → Q x) y hy⟩)
    (fun _ ⟨_, h⟩ => h) (fun _ h => h) (fun P x hp => ⟨x, _, ⟨(), rfl⟩, hp⟩)
    (fun P Q R hp x hx => let ⟨y, h⟩ := hp x hx; ⟨y, h.2⟩) (fun hf => let ⟨_, h⟩ := hf 0 trivial; h)
    Unit (fun _ n => n = 0) (fun _ n => n = 1) (fun _ => anPers _) (fun _ _ => ⟨0, _, ⟨(), rfl⟩, rfl⟩)
    (fun _ _ _ => ⟨1, rfl⟩) (fun _ x h => absurd (h.1.symm.trans h.2) (by decide))

-- `Iris.Linear.leak` idx 12: necessary (GB, empty gname, fupd = id; True ⊬ emp)
theorem w5c2_94 : ¬ drop0% Iris.Linear.leak 12 := fun h =>
  Bool.noConfusion (@h .M1 .M0 GB _ iprop(True) (fun _ _ X => X) Empty (fun _ _ => iprop(True)) (fun _ => iprop(emp))
    (fun h => h) (fun _ h => h) (fun _ h => h) (fun _ γ => γ.elim) true trivial : true = false)

-- `Iris.Linear.leak` idx 13: necessary (GB, fupd = id, cinv = id, cinv_own = emp; True ⊬ emp)
theorem w5c2_95 : ¬ drop0% Iris.Linear.leak 13 := fun h =>
  Bool.noConfusion (@h .M1 .M0 GB _ iprop(True) (fun _ _ X => X) Unit (fun _ P => P) (fun _ => iprop(emp))
    (fun h => h) (fun _ h => h) (fun _ h => h)
    (fun P x hp => ⟨_, ⟨(), rfl⟩, x, false, by cases x <;> rfl, hp, rfl⟩) true trivial : true = false)

-- `Iris.Linear.leak` idx 9: necessary (GB, fupd X = X or X empty (not monotone), cinv = False; True ⊬ emp)
theorem w5c2_96 : ¬ drop0% Iris.Linear.leak 9 := fun h => by
  have := @h .M1 .M0 GB _ iprop(True) (fun _ _ => gbE) Unit (fun _ _ => iprop(False)) (fun _ => iprop(emp))
    gbE_trans gbE_frame_l
    (fun P x _ => .inr fun _ ⟨_, ⟨_, e⟩, hp⟩ => by subst e; obtain ⟨_, _, _, hf, _⟩ := hp; exact hf)
    (fun _ _ _ _ _ hf => hf.elim) true trivial
  rcases this with e | hn
  · exact Bool.noConfusion (e : true = false)
  · exact hn false rfl

-- `Iris.SavedProp.saved_NA` idx 2: removable (A i is used only under ∧; agree makes saved affine, persistence gives saved i P from the box)
theorem w5c2_97 : drop% Iris.SavedProp.saved_NA 2 := by
  intro PROP _ _ ident saved _ agree i
  exact savedNA_pers ident saved agree i

-- `Iris.SavedProp.saved_NA` idx 3: removable (agree makes saved affine; persistence gives saved i P from the box)
theorem w5c2_98 : drop% Iris.SavedProp.saved_NA 3 := by
  intro PROP _ _ ident saved _ agree i
  exact savedNA_pers ident saved agree i

-- `Iris.SavedProp.saved_NA` idx 6: removable (with BIAffine both halves of the boxed separating conjunction are available; only ∧-reasoning)
theorem w5c2_99 : drop% Iris.SavedProp.saved_NA 6 := by
  intro PROP _ _ _ ident saved agree i
  exact savedNA_aff ident saved agree i

-- `Iris.SavedProp.saved_A` idx 2: removable (agree makes saved affine, so saved i (A i) is intuitionistic; then saved_NA without BIPersistentlyExist)
theorem w5c2_100 : drop% Iris.SavedProp.saved_A 2 := by
  intro PROP _ _ ident saved _ agree i
  exact savedA_pers ident saved agree i

-- `Iris.SavedProp.saved_A` idx 3: removable (same proof; affinity of saved i P follows from agree)
theorem w5c2_101 : drop% Iris.SavedProp.saved_A 3 := by
  intro PROP _ _ ident saved _ agree i
  exact savedA_pers ident saved agree i

-- `Iris.SavedProp.contradiction` idx 2: removable (saved_NA and saved_A hold without BIPersistentlyExist and BIAffine, so the allocated proposition equals False and alloc plus consistency suffice)
theorem w5c2_102 : drop% Iris.SavedProp.contradiction 2 := by
  intro PROP _ _ bupd ident saved _ _ _ _ _ alloc agree cons
  apply cons
  have hF : iprop(∃ i, saved i (Iris.SavedProp.A ident saved i)) ⊣⊢ iprop(False) :=
    ⟨exists_elim fun i => (and_intro (savedNA_pers ident saved agree i)
      (savedA_pers ident saved agree i)).trans imp_elim_left, false_elim⟩
  rw [← Iris.BI.BIBase.BiEntails.to_eq hF]
  exact alloc

-- `Iris.SavedProp.contradiction` idx 3: removable (saved_NA and saved_A hold without BIPersistentlyExist and BIAffine, so the allocated proposition equals False and alloc plus consistency suffice)
theorem w5c2_103 : drop% Iris.SavedProp.contradiction 3 := by
  intro PROP _ _ bupd ident saved _ _ _ _ _ alloc agree cons
  apply cons
  have hF : iprop(∃ i, saved i (Iris.SavedProp.A ident saved i)) ⊣⊢ iprop(False) :=
    ⟨exists_elim fun i => (and_intro (savedNA_pers ident saved agree i)
      (savedA_pers ident saved agree i)).trans imp_elim_left, false_elim⟩
  rw [← Iris.BI.BIBase.BiEntails.to_eq hF]
  exact alloc

-- `Iris.AffineEM.sep_dup` idx 2: removable (case split on em P without destructing under the box: P ∧ (P ∗ ¬P) ⊢ P ∧ ¬P by affinity of P)
theorem w5c2_104 : drop% Iris.AffineEM.sep_dup 2 := by
  intro PROP _ em P _
  exact sepdup_gen em P

-- `Iris.AffineEM.and_sep` idx 2: removable (the same duplication of the affine P ∧ Q, then split)
theorem w5c2_105 : drop% Iris.AffineEM.and_sep 2 := by
  intro PROP _ em P Q _
  exact (sepdup_gen em iprop(P ∧ Q)).trans (sep_mono and_elim_l and_elim_r)

-- `Iris.AffineEM.sep_dup` idx 3: necessary (affine UPred over (Nat, +), P = ownM 1)
theorem w5c2_106 : ¬ drop0% Iris.AffineEM.sep_dup 3 := fun h =>
  np_not_dup (@h (UPred NP) _ _ (UPred.ownM ⟨1⟩) inferInstance)

-- `Iris.AffineEM.and_sep` idx 3: necessary (affine UPred over (Nat, +), P = Q = ownM 1)
theorem w5c2_107 : ¬ drop0% Iris.AffineEM.and_sep 3 := fun h =>
  np_not_dup ((and_intro .rfl .rfl).trans (@h (UPred NP) _ _ (UPred.ownM ⟨1⟩) (UPred.ownM ⟨1⟩) inferInstance))

-- `Iris.Inv.saved_alloc` idx 9: necessary (Kripke KN, fupd = shift by one, inv = delay by one; start = (1 ≤ n), finished = False, at 0)
theorem w5c2_108 : ¬ drop0% Iris.Inv.saved_alloc 9 := fun h => by
  have := @h KN _ _ (fun _ => knShift) Unit (fun _ => knDelay) (fun _ _ => knPers _)
    knShift_intro (fun {_ _ _} hPQ n x => hPQ (n + 1) x) knShift_fl (fun _ h => h)
    knShift_alloc Unit (fun _ => knStart) (fun _ => iprop(False))
    (fun n _ => ⟨_, ⟨(), rfl⟩, Nat.succ_le_succ (Nat.zero_le n)⟩) (fun _ => iprop(True)) 0 trivial
  obtain ⟨_, ⟨_, e⟩, hx⟩ := this
  subst e
  obtain ⟨_, ⟨_, e2⟩, hx⟩ := hx
  subst e2
  rcases hx.2 with hs | ⟨hf, _⟩
  · have h2 : 1 ≤ 0 := hs
    exact absurd h2 (by decide)
  · exact hf

-- `Iris.Inv.A_alloc` idx 9: necessary (Kripke KN, fupd = shift by one, inv = delay by one; start = (1 ≤ n), finished = False, at 0)
theorem w5c2_109 : ¬ drop0% Iris.Inv.A_alloc 9 := fun h => by
  have := @h KN _ _ (fun _ => knShift) Unit (fun _ => knDelay) (fun _ _ => knPers _)
    knShift_intro (fun {_ _ _} hPQ n x => hPQ (n + 1) x) knShift_fl (fun _ h => h)
    knShift_alloc Unit (fun _ => knStart) (fun _ => iprop(False))
    (fun n _ => ⟨_, ⟨(), rfl⟩, Nat.succ_le_succ (Nat.zero_le n)⟩) 0 trivial
  obtain ⟨_, ⟨_, e⟩, hx⟩ := this
  subst e
  obtain ⟨_, ⟨_, e2⟩, hx⟩ := hx
  subst e2
  rcases hx.2 with hs | ⟨hf, _⟩
  · have h2 : 1 ≤ 0 := hs
    exact absurd h2 (by decide)
  · exact hf

-- `Iris.LaterCreditsPlain.contradiction` idx 2: removable (laterN_False holds without BIPersistentlyExist; the induction over n uses lc_fupd_elim_later_keep, which does not need it)
theorem w5c2_110 : drop% Iris.LaterCreditsPlain.contradiction 2 := by
  intro PROP _ _ lc lc_fupd_elim_later lc_soundness fupd_keep_si_pure' _
  apply pure_soundness (PROP := PROP)
  apply lc_soundness _ ⊤
  refine (sep_emp.2.trans (sep_mono_right laterNFalse_gen)).trans
    (sep_exists_left.1.trans (exists_elim fun n => ?_))
  induction n with
  | zero => exact sep_comm.1.trans (wand_elim false_elim)
  | succ n ih =>
    have k := Iris.LaterCreditsPlain.lc_fupd_elim_later_keep lc_fupd_elim_later fupd_keep_si_pure'
      (E := ⊤) (P := iprop(▷^[n] False))
    exact (wand_elim (emp_sep.2.trans (wand_elim k))).trans ((BIFUpdate.mono ih).trans BIFUpdate.trans)
