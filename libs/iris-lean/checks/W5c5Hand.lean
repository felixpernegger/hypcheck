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

namespace W5c5
open Iris Iris.BI

/-- Nat index with its order (has bottom 0). -/
abbrev UIdx : BiIndex := { car := Nat, rel := inferInstance }

/-- Bool with the discrete order (no bottom element). -/
def DB := Bool
instance : LE DB := ⟨fun a b => a = b⟩
instance : Inhabited DB := ⟨(true : Bool)⟩
instance : Std.IsPreorder DB where
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2

abbrev DIdx : BiIndex := { car := DB, rel := inferInstance }
def tT : DB := (true : Bool)
def tF : DB := (false : Bool)

/-- Nat with the discrete order. -/
def DN := Nat
instance : LE DN := ⟨fun a b => a = b⟩
instance : Inhabited DN := ⟨(0 : Nat)⟩
instance : Std.IsPreorder DN where
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2
abbrev NIdx : BiIndex := { car := DN, rel := inferInstance }

/-- Over the discrete Bool index: a monotone predicate from any pair of propositions. -/
def mpD {PROP : Type} [BI PROP] (a b : PROP) : MonPred DIdx PROP :=
  ⟨fun i => cond (show Bool from i) a b, fun hij => (show _ = _ from hij) ▸ .rfl⟩

/-- `⌜i = true⌝` over the discrete Bool index: not objective. -/
def phT : MonPred DIdx SiProp := ⟨fun i => iprop(⌜(show Bool from i) = true⌝), fun hij _ h => (show _ = _ from hij) ▸ h⟩

/-- `⌜1 ≤ k⌝` over the Nat index. -/
def mp1 : MonPred UIdx SiProp := ⟨fun k => iprop(⌜(1 : Nat) ≤ k⌝), fun hij _ h => Nat.le_trans h hij⟩

def eT {I : BiIndex} : MonPred I SiProp := MonPred.embed iprop(True)
def eF {I : BiIndex} : MonPred I SiProp := MonPred.embed iprop(False)

/-- step-indexed prop true only at step 0 (not timeless) -/
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩

theorem s0_not_timeless : ¬ Timeless s0 := fun ⟨h⟩ =>
  (h 1 (rfl : (0 : Nat) = 0)).elim (fun hf => hf) (fun h1 => Nat.noConfusion (h1 : (1 : Nat) = 0))

/-- A non-objective predicate over `DIdx`, read off at two indices. -/
theorem notObj {X : MonPred DIdx SiProp} (hX : Objective X) (a b : DB) (n : Nat)
    (h1 : (X.monPred_at a).holds n) (h2 : ¬ (X.monPred_at b).holds n) : False := h2 (hX.1 a b n h1)

end W5c5

namespace W5c5
open Iris Iris.BI
/-! GB: predicates on the group Z/2 (Bool, xor) as a Boolean BI: non-affine, non-positive,
persistently P := constant P false. own1 := {true} is not persistent; emp not absorbing. -/
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


/-! PF: predicates on Nat with sep = and, emp = True (an affine BI, discrete), and
persistently P n := (P holds cofinitely) and P n. It is not BIPersistentlyExist (evens or odds)
and not BIPersistentlyForall (the family evens or n at least k). -/
def PF := Nat → Prop

def cof (P : Nat → Prop) : Prop := ∃ N, ∀ m, N ≤ m → P m

instance : BIBase PF where
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
  persistently P x := cof P ∧ P x
  later P        x := P x

instance : COFE PF := COFE.ofDiscrete _

instance pfBI : BI PF where
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
  persistently_mono h _ hP := ⟨let ⟨N, hN⟩ := hP.1; ⟨N, fun m hm => h m (hN m hm)⟩, h _ hP.2⟩
  persistently_idem_2 _ h := ⟨let ⟨N, hN⟩ := h.1; ⟨N, fun m hm => ⟨h.1, hN m hm⟩⟩, h⟩
  persistently_emp_2 _ _ := ⟨⟨0, fun _ _ => trivial⟩, trivial⟩
  persistently_and_2 _ h :=
    ⟨let ⟨N1, h1⟩ := h.1.1; let ⟨N2, h2⟩ := h.2.1;
      ⟨N1 + N2, fun m hm => ⟨h1 m (by omega), h2 m (by omega)⟩⟩, h.1.2, h.2.2⟩
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1.2, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr fun _ => h

def ev : PF := fun n => n % 2 = 0
def od : PF := fun n => n % 2 = 1
/-- evens, or at least k: each cofinite, intersection = evens. -/
def evk (k : Nat) : PF := fun n => n % 2 = 0 ∨ k ≤ n

theorem ev_not_cof : ¬ cof ev := fun ⟨N, h⟩ => by
  have := h (2 * N + 1) (by omega); simp only [ev] at this; omega
theorem od_not_cof : ¬ cof od := fun ⟨N, h⟩ => by
  have := h (2 * N) (by omega); simp only [od] at this; omega
theorem evod_cof : cof (fun n => ev n ∨ od n) := ⟨0, fun m _ => by simp only [ev, od]; omega⟩
theorem evk_cof (k : Nat) : cof (evk k) := ⟨k, fun _ hm => .inr hm⟩
theorem evk_all_not_cof : ¬ cof (fun n => ∀ k, evk k n) := fun ⟨N, h⟩ => by
  have := h (2 * N + 1) (by omega) (2 * N + 2); simp only [evk] at this; omega

end W5c5

namespace W5c5
open Iris Iris.BI

instance eT_obj {I : BiIndex} : Objective (eT : MonPred I SiProp) := ⟨fun _ _ => .rfl⟩
instance eF_obj {I : BiIndex} : Objective (eF : MonPred I SiProp) := ⟨fun _ _ => .rfl⟩

theorem ftF : ¬ ((show Bool from tF) = true) := Bool.false_ne_true

end W5c5

namespace W5c5
open Iris Iris.BI

/-! Over the discrete Bool index with PROP = GB: P2 = (own1 at true, emp at false),
Q2 = (emp at true, own1 at false). `<obj>` does not commute with `∗`. -/
def P2 : MonPred DIdx GB := mpD own1 iprop(emp)
def Q2 : MonPred DIdx GB := mpD iprop(emp) own1

theorem objPQ : (iprop(<obj> (P2 ∗ Q2)) : MonPred DIdx GB).monPred_at tT true := by
  intro p ⟨i, hi⟩; subst hi; revert i; show ∀ i : Bool, _; intro i; cases i
  · exact ⟨false, true, rfl, rfl, rfl⟩
  · exact ⟨true, false, rfl, rfl, rfl⟩

theorem objPQe : (iprop(<obj> (P2 ∗ (Q2 ∗ emp))) : MonPred DIdx GB).monPred_at tT true := by
  intro p ⟨i, hi⟩; subst hi; revert i; show ∀ i : Bool, _; intro i; cases i
  · exact ⟨false, true, rfl, rfl, true, false, rfl, rfl, rfl⟩
  · exact ⟨true, false, rfl, rfl, false, false, rfl, rfl, rfl⟩

theorem objP_false (j : DB) (x : Bool) : ¬ (iprop(<obj> P2) : MonPred DIdx GB).monPred_at j x := fun h =>
  Bool.noConfusion (((h _ ⟨tT, rfl⟩ : x = true).symm.trans (h _ ⟨tF, rfl⟩ : x = false)))

theorem objP_sep_false (R : MonPred DIdx GB) (x : Bool) :
    ¬ (iprop(<obj> P2 ∗ R) : MonPred DIdx GB).monPred_at tT x := fun ⟨a, _, _, ha, _⟩ => objP_false tT a ha

/-- `<obj>` does not distribute over `∗` without a bottom index. -/
theorem obj_sep_bad {L R : MonPred DIdx GB} (hL : iprop(<obj> (P2 ∗ Q2)) ⊢ L) (hR : R ⊢ iprop(<obj> P2 ∗ <obj> Q2))
    (H : L ⊢ R) : False := objP_sep_false _ true ((hL.trans (H.trans hR)) tT true objPQ)

/-! PF over the discrete Nat index: Pk i = <pers> (evens or ≥ i) is persistent, its `<obj>` is not. -/
def Pk : MonPred NIdx PF := ⟨fun i => iprop(<pers> evk (show Nat from i)), fun hij => (show _ = _ from hij) ▸ .rfl⟩

instance Pk_pers : Persistent Pk := ⟨fun _ => persistently_idem_2⟩

theorem obj_Pk_not_pers : ¬ Persistent (iprop(<obj> Pk) : MonPred NIdx PF) := fun ⟨h⟩ => by
  have H := h (show DN from (0 : Nat)) 0 (fun p ⟨j, hj⟩ => hj ▸ ⟨evk_cof _, Or.inl rfl⟩)
  obtain ⟨N, hN⟩ := H.1
  have := (hN (2 * N + 1) (by omega) _ ⟨show DN from (2 * N + 2 : Nat), rfl⟩).2
  simp only [evk] at this; omega

/-! PF over the discrete Bool index: evens at true, odds at false. -/
def Pe : MonPred DIdx PF := mpD ev od

theorem Pe_not_cof (i : DB) : ¬ cof (Pe.monPred_at i) := by
  revert i; show ∀ i : Bool, _; intro i; cases i
  · exact od_not_cof
  · exact ev_not_cof

theorem pers_subj_Pe : (iprop(<pers> <subj> Pe) : MonPred DIdx PF).monPred_at tT 0 := by
  refine ⟨⟨0, fun m _ => ?_⟩, ⟨_, ⟨tT, rfl⟩, (rfl : 0 % 2 = 0)⟩⟩
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · exact ⟨_, ⟨tT, rfl⟩, hm⟩
  · exact ⟨_, ⟨tF, rfl⟩, hm⟩

/-! A commutative monoid on GB with unit True other than `∧`: pointwise `↔`. -/
def iffOp (a b : GB) : GB := fun x => (a x ↔ b x)

instance iffMon : Iris.Algebra.MonoidOps iffOp (iprop(True) : GB) where
  op_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  op_assoc {a b c} := funext fun x => propext (by
    unfold iffOp
    by_cases ha : a x <;> by_cases hb : b x <;> by_cases hc : c x <;> simp [ha, hb, hc])
  op_comm := funext fun _ => propext Iff.comm
  op_left_id {a} := funext fun x => true_iff (a x)

/-- Left projection at index false, `∗` at index true: not commutative. -/
def opL (x y : MonPred DIdx SiProp) : MonPred DIdx SiProp :=
  ⟨fun j => cond (show Bool from j) iprop(x.monPred_at j ∗ y.monPred_at j) (x.monPred_at j),
   fun hij => (show _ = _ from hij) ▸ .rfl⟩

end W5c5

namespace W5c5
open Iris Iris.BI
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
end W5c5

namespace W5c5
open Iris Iris.BI Iris.Std Iris.Algebra

/-- Later credits that are all `False` (lawful). -/
def lcF : BILaterCredits SiProp where
  lc _ := iprop(False)
  lc_split := ⟨fun _ h => h.elim, fun _ h => h.1⟩
  lc_timeless _ := ⟨fun _ h => .inl h⟩
  lc_0_persistent := ⟨fun _ h => h⟩
  lc_affine _ := ⟨fun _ h => h.elim⟩

/-- Identity basic update on SiProp (lawful). -/
def idBupd : BIUpdate SiProp where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h

/-- Constant-True basic update on SiProp (lawful). -/
def topBupd : BIUpdate SiProp where
  bupd _ := iprop(True)
  bupd_ne := ⟨fun _ _ _ _ _ _ => Iff.rfl⟩
  intro := fun _ _ => trivial
  mono _ := fun _ _ => trivial
  trans := fun _ _ => trivial
  frame_right := fun _ _ => trivial

/-- Objective predicates transfer along `⊣⊢`; `phT` is not objective. -/
theorem notObjE {X : MonPred DIdx SiProp} (hX : Objective X) (e : X ⊣⊢ phT) : False :=
  ftF (((e.2 tT).trans ((hX.1 tT tF).trans (e.1 tF))) 0 rfl)

abbrev TM := fun V => Std.ExtTreeMap Nat V compare
abbrev sg {V : Type} (v : V) : TM V := PartialMap.insert ∅ 0 v
theorem sgE {PROP : Type _} [BI PROP] {V : Type} (Φ : Nat → V → PROP) (v : V) :
    bigSepM Φ (sg v) = Φ 0 v := BigOpM.bigOpM_singleton_eq (op := BIBase.sep) Φ 0 v
abbrev tw {V : Type} (a b : V) : TM V := PartialMap.insert (sg a) 1 b
theorem twE {PROP : Type _} [BI PROP] {V : Type} (Φ : Nat → V → PROP) (a b : V) :
    bigSepM Φ (tw a b) = iprop(Φ 1 b ∗ Φ 0 a) :=
  (BigOpM.bigOpM_insert_eq (op := BIBase.sep) Φ b ((get?_insert_ne (by decide)).trans (get?_empty 1))).trans
    (congrArg (BIBase.sep (Φ 1 b)) (sgE Φ a))
abbrev TS := Std.ExtTreeSet Nat compare
theorem ssE {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : bigSepS Φ ({0} : TS) ⊣⊢ Φ 0 := BigSepS.bigSepS_singleton
theorem s01 {PROP : Type _} [BI PROP] (Φ : Nat → PROP) :
    bigSepS Φ (@Insert.insert Nat TS LawfulSet.instInsert 1 {0}) ⊣⊢ iprop(Φ 1 ∗ Φ 0) :=
  (BigSepS.bigSepS_insert (by rw [LawfulSet.mem_singleton]; decide)).trans
    ⟨sep_mono_right (ssE Φ).1, sep_mono_right (ssE Φ).2⟩
abbrev MSN := ListPerm Nat
theorem msSing {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : ([∗mset] x ∈ ({0} : MSN), Φ x) ⊣⊢ Φ 0 :=
  BigSepMS.bigSepMS_singleton (MS := ListPerm Nat)
theorem msSing1 {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : ([∗mset] x ∈ ({1} : MSN), Φ x) ⊣⊢ Φ 1 :=
  BigSepMS.bigSepMS_singleton (MS := ListPerm Nat)
theorem ms01 {PROP : Type _} [BI PROP] (Φ : Nat → PROP) :
    ([∗mset] x ∈ (({0} : MSN) ⊎ {1}), Φ x) ⊣⊢ iprop(Φ 0 ∗ Φ 1) :=
  BigSepMS.bigSepMS_insert.trans ⟨sep_mono_right (msSing1 Φ).1, sep_mono_right (msSing1 Φ).2⟩

/-- `⌜i = a⌝` over the discrete Bool index. -/
def phD (a : Bool) : MonPred DIdx SiProp := ⟨fun i => iprop(⌜(show Bool from i) = a⌝), fun hij _ h => (show _ = _ from hij) ▸ h⟩

end W5c5

namespace W5c5
open Iris Iris.BI Iris.OFE

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF

/-- Later credits on IProp with £ n := True (as in W5c1). -/
@[reducible] noncomputable def lcT : BILaterCredits (IProp CGF) where
  lc _ := iprop(True)
  lc_split := ⟨emp_sep.2.trans (sep_mono_left true_intro), true_intro⟩
  lc_timeless _ := inferInstance
  lc_0_persistent := inferInstance
  lc_affine _ := inferInstance

/-- Constant-True basic update on IProp (lawful). -/
noncomputable def topBupdI : BIUpdate (IProp CGF) where
  bupd _ := iprop(True)
  bupd_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  intro := true_intro
  mono _ := .rfl
  trans := .rfl
  frame_right := true_intro

/-- If ⊢ |={⊤}=> False under every invariant setup, fupd soundness gives False. -/
theorem fupd_false (H : ∀ [InvGS_gen .hasNoLC CGF], ⊢ (iprop(|={⊤}=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))

/-- If ▷ Q ⊢ Q for Q := |={⊤}=> False in IProp, Löb and fupd soundness give False (as in W5c1). -/
theorem fupd_loeb_false (H : ∀ [InvGS_gen .hasNoLC CGF],
    (iprop(▷ |={⊤}=> ⌜False⌝) : IProp CGF) ⊢ iprop(|={⊤}=> ⌜False⌝)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (true_intro.trans (loeb_weak H))))

end W5c5

open Iris Iris.BI Iris.Std W5c5


-- `Iris.BI.BiIndexBottom.bot_le` idx 2: necessary (Nat index, bot = 1, i = 0)
theorem w5c5_1 : ¬ drop0% Iris.BI.BiIndexBottom.bot_le 2 := fun h =>
  Nat.not_succ_le_zero 0 (@h UIdx (1 : Nat) (0 : Nat))

-- `Iris.BI.MonPred.monPred_mono` idx 6: necessary (mp1 = ⌜1 ≤ k⌝ at i = 1, j = 0)
theorem w5c5_2 : ¬ drop0% Iris.BI.MonPred.monPred_mono 6 := fun h =>
  Nat.not_succ_le_zero 0 ((@h UIdx SiProp _ mp1 (1 : Nat) (0 : Nat)) 0 (Nat.le_refl 1))

-- `Iris.BI.MonPred.ext` idx 5: necessary (embed True ≠ embed False)
theorem w5c5_3 : ¬ drop0% Iris.BI.MonPred.ext 5 := fun h => by
  have e := congrArg (fun P : MonPred UIdx SiProp => (P.monPred_at (0 : Nat)).holds 0)
    (@h UIdx SiProp _ eT eF)
  exact (show True = False from e) ▸ trivial

-- `Iris.BI.MonPred.sForall_at_elim` idx 6: necessary (Ψ empty, q = embed False)
theorem w5c5_4 : ¬ drop0% Iris.BI.MonPred.sForall_at_elim 6 := fun h =>
  ((MonPred.sForall_at_intro (I := UIdx) (PROP := SiProp) (R := iprop(True)) (Ψ := fun _ => False)
    (0 : Nat) (fun _ hq => hq.elim)).trans (@h UIdx SiProp _ (fun _ => False) eF (0 : Nat))) 0 trivial

-- `Iris.BI.MonPred.sForall_at_intro` idx 6: necessary (Ψ = {embed False}, R = True)
theorem w5c5_5 : ¬ drop0% Iris.BI.MonPred.sForall_at_intro 6 := fun h =>
  ((@h UIdx SiProp _ (· = eF) iprop(True) (0 : Nat)).trans
    (MonPred.sForall_at_elim (I := UIdx) (PROP := SiProp) (q := eF) (0 : Nat) rfl)) 0 trivial

-- `Iris.BI.MonPred.sExists_at_intro` idx 6: necessary (Ψ empty, q = embed True)
theorem w5c5_6 : ¬ drop0% Iris.BI.MonPred.sExists_at_intro 6 := fun h =>
  ((@h UIdx SiProp _ (fun _ => False) eT (0 : Nat)).trans
    (MonPred.sExists_at_elim (I := UIdx) (PROP := SiProp) (R := iprop(False)) (Ψ := fun _ => False)
      (0 : Nat) (fun _ hq => hq.elim))) 0 trivial

-- `Iris.BI.MonPred.sExists_at_elim` idx 6: necessary (Ψ = {embed True}, R = False)
theorem w5c5_7 : ¬ drop0% Iris.BI.MonPred.sExists_at_elim 6 := fun h => by
  have H : (MonPred.sExists (· = (eT : MonPred UIdx SiProp))).monPred_at (0 : Nat) ⊢ iprop(False) :=
    @h UIdx SiProp _ (· = eT) iprop(False) (0 : Nat)
  exact ((MonPred.sExists_at_intro (I := UIdx) (PROP := SiProp) (Ψ := (· = eT)) (q := eT) (0 : Nat) rfl).trans H) 0 trivial

-- `Iris.BI.instBILoebMonPred` idx 3: necessary (GB, later = id: loeb would give True ⊢ False)
theorem w5c5_8 : ¬ drop0% Iris.BI.instBILoebMonPred 3 := fun h => by
  letI := @h UIdx GB gbBI
  exact (loeb_weak (P := (MonPred.embed (fun _ => False : GB) : MonPred UIdx GB))
    (fun _ _ hx => hx)) (0 : Nat) false trivial

-- `Iris.BI.instBIPositiveMonPred` idx 3: necessary (GB is not positive)
theorem w5c5_9 : ¬ drop0% Iris.BI.instBIPositiveMonPred 3 := fun h => by
  letI := @h UIdx GB gbBI
  exact gb_not_positive ⟨fun {P Q} =>
    (affinely_sep_l (P := (MonPred.embed P : MonPred UIdx GB)) (Q := MonPred.embed Q)) (0 : Nat)⟩

-- `Iris.BI.instBIAffineMonPred` idx 3: necessary (GB: True not affine)
theorem w5c5_10 : ¬ drop0% Iris.BI.instBIAffineMonPred 3 := fun h => by
  letI := @h UIdx GB gbBI
  exact gb_true_not_emp ((Affine.affine (P := (MonPred.embed iprop(True) : MonPred UIdx GB))) (0 : Nat))

-- `Iris.BI.instBILaterContractiveMonPred` idx 3: necessary (GB discrete, later = id: True ≡{0} False)
theorem w5c5_11 : ¬ drop0% Iris.BI.instBILaterContractiveMonPred 3 := fun h => by
  have e := (@h UIdx GB gbBI).distLater_dist (n := 0)
    (x := (MonPred.embed (fun _ => True) : MonPred UIdx GB)) (y := MonPred.embed (fun _ => False))
    (fun m hm => absurd hm (Nat.not_lt_zero m)) (0 : Nat)
  exact cast (congrFun (show (fun _ => True : GB) = fun _ => False from e) false) trivial

-- `Iris.BI.MonPred.monPred_at_mono` idx 7: necessary (P = embed True, Q = embed False)
theorem w5c5_12 : ¬ drop0% Iris.BI.MonPred.monPred_at_mono 7 := fun h =>
  (@h UIdx SiProp _ eT eF (0 : Nat) (0 : Nat) (Nat.le_refl 0)) 0 trivial

-- `Iris.BI.MonPred.monPred_at_mono` idx 8: necessary (P = Q = mp1, i = 1, j = 0)
theorem w5c5_13 : ¬ drop0% Iris.BI.MonPred.monPred_at_mono 8 := fun h =>
  Nat.not_succ_le_zero 0 ((@h UIdx SiProp _ mp1 mp1 (1 : Nat) (0 : Nat) (fun _ _ h => h)) 0 (Nat.le_refl 1))

-- `Iris.BI.MonPred.monPred_at_flip_mono` idx 7: necessary (Q = embed True, P = embed False)
theorem w5c5_14 : ¬ drop0% Iris.BI.MonPred.monPred_at_flip_mono 7 := fun h =>
  (@h UIdx SiProp _ eF eT (0 : Nat) (0 : Nat) (Nat.le_refl 0)) 0 trivial

-- `Iris.BI.MonPred.monPred_at_flip_mono` idx 8: necessary (P = Q = mp1, i = 0, j = 1)
theorem w5c5_15 : ¬ drop0% Iris.BI.MonPred.monPred_at_flip_mono 8 := fun h =>
  Nat.not_succ_le_zero 0 ((@h UIdx SiProp _ mp1 mp1 (0 : Nat) (1 : Nat) (fun _ _ h => h)) 0 (Nat.le_refl 1))

-- `Iris.BI.MonPred.monPred_at_persistent` idx 4: necessary (GB: embed own1)
theorem w5c5_16 : ¬ drop0% Iris.BI.MonPred.monPred_at_persistent 4 := fun h =>
  gb_own1_not_pers (@h UIdx GB gbBI (MonPred.embed own1) (0 : Nat))

-- `Iris.BI.MonPred.monPred_at_absorbing` idx 4: necessary (GB: embed emp)
theorem w5c5_17 : ¬ drop0% Iris.BI.MonPred.monPred_at_absorbing 4 := fun h =>
  gb_emp_not_absorbing (@h UIdx GB gbBI (MonPred.embed iprop(emp)) (0 : Nat))

-- `Iris.BI.MonPred.monPred_at_affine` idx 4: necessary (GB: embed True)
theorem w5c5_18 : ¬ drop0% Iris.BI.MonPred.monPred_at_affine 4 := fun h =>
  gb_true_not_affine (@h UIdx GB gbBI (MonPred.embed iprop(True)) (0 : Nat))

-- `Iris.BI.MonPred.monPred_at_timeless` idx 4: necessary (SiProp: embed s0)
theorem w5c5_19 : ¬ drop0% Iris.BI.MonPred.monPred_at_timeless 4 := fun h =>
  s0_not_timeless (@h UIdx SiProp _ (MonPred.embed s0) (0 : Nat))

-- `Iris.BI.MonPred.monPred_persistent` idx 4: necessary (GB: embed own1)
theorem w5c5_20 : ¬ drop0% Iris.BI.MonPred.monPred_persistent 4 := fun h =>
  gb_own1_not_pers ⟨(@h UIdx GB gbBI (MonPred.embed own1)).1 (0 : Nat)⟩

-- `Iris.BI.MonPred.monPred_absorbing` idx 4: necessary (GB: embed emp)
theorem w5c5_21 : ¬ drop0% Iris.BI.MonPred.monPred_absorbing 4 := fun h =>
  gb_emp_not_absorbing ⟨(@h UIdx GB gbBI (MonPred.embed iprop(emp))).1 (0 : Nat)⟩

-- `Iris.BI.MonPred.monPred_affine` idx 4: necessary (GB: embed True)
theorem w5c5_22 : ¬ drop0% Iris.BI.MonPred.monPred_affine 4 := fun h =>
  gb_true_not_affine ⟨(@h UIdx GB gbBI (MonPred.embed iprop(True))).1 (0 : Nat)⟩

-- `Iris.BI.MonPred.monPred_in_mono` idx 5: necessary (i = 0, j = 1)
theorem w5c5_23 : ¬ drop0% Iris.BI.MonPred.monPred_in_mono 5 := fun h =>
  Nat.not_succ_le_zero 0 ((@h UIdx SiProp _ (0 : Nat) (1 : Nat)) (0 : Nat) 0 (Nat.le_refl 0))

-- `Iris.BI.MonPred.monPred_in_flip_mono` idx 5: necessary (i = 1, j = 0)
theorem w5c5_24 : ¬ drop0% Iris.BI.MonPred.monPred_in_flip_mono 5 := fun h =>
  Nat.not_succ_le_zero 0 ((@h UIdx SiProp _ (1 : Nat) (0 : Nat)) (0 : Nat) 0 (Nat.le_refl 0))

-- `Iris.BI.MonPred.and_objective` idx 5: necessary (DIdx: P = ⌜i = true⌝, Q = embed True)
theorem w5c5_25 : ¬ drop0% Iris.BI.MonPred.and_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ phT eT inferInstance) tT tF 0 ⟨rfl, trivial⟩ (fun h => ftF h.1)

-- `Iris.BI.MonPred.and_objective` idx 6: necessary (DIdx: P = embed True, Q = ⌜i = true⌝)
theorem w5c5_26 : ¬ drop0% Iris.BI.MonPred.and_objective 6 := fun h =>
  notObj (@h DIdx SiProp _ eT phT inferInstance) tT tF 0 ⟨trivial, rfl⟩ (fun h => ftF h.2)

-- `Iris.BI.MonPred.or_objective` idx 5: necessary (DIdx: P = ⌜i = true⌝, Q = embed False)
theorem w5c5_27 : ¬ drop0% Iris.BI.MonPred.or_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ phT eF inferInstance) tT tF 0 (.inl rfl) (fun h => h.elim ftF id)

-- `Iris.BI.MonPred.or_objective` idx 6: necessary (DIdx: P = embed False, Q = ⌜i = true⌝)
theorem w5c5_28 : ¬ drop0% Iris.BI.MonPred.or_objective 6 := fun h =>
  notObj (@h DIdx SiProp _ eF phT inferInstance) tT tF 0 (.inr rfl) (fun h => h.elim id ftF)

-- `Iris.BI.MonPred.sep_objective` idx 5: necessary (DIdx over SiProp, sep = and: P = ⌜i = true⌝, Q = embed True)
theorem w5c5_29 : ¬ drop0% Iris.BI.MonPred.sep_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ phT eT inferInstance) tT tF 0 ⟨rfl, trivial⟩ (fun h => ftF h.1)

-- `Iris.BI.MonPred.sep_objective` idx 6: necessary (DIdx over SiProp: P = embed True, Q = ⌜i = true⌝)
theorem w5c5_30 : ¬ drop0% Iris.BI.MonPred.sep_objective 6 := fun h =>
  notObj (@h DIdx SiProp _ eT phT inferInstance) tT tF 0 ⟨trivial, rfl⟩ (fun h => ftF h.2)

-- `Iris.BI.MonPred.impl_objective` idx 5: necessary (DIdx: P = ⌜i = true⌝, Q = embed False)
theorem w5c5_31 : ¬ drop0% Iris.BI.MonPred.impl_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ phT eF inferInstance) tF tT 0
    (by intro p ⟨j, hj⟩; subst hj; intro _ _ e _ _ ht; subst e; exact ftF ht)
    (fun hx => (MonPred.monPred_impl_force (I := DIdx) (PROP := SiProp) tT phT eF) 0 hx 0 (Nat.le_refl 0) rfl)

-- `Iris.BI.MonPred.impl_objective` idx 6: necessary (DIdx: P = embed True, Q = ⌜i = true⌝)
theorem w5c5_32 : ¬ drop0% Iris.BI.MonPred.impl_objective 6 := fun h =>
  notObj (@h DIdx SiProp _ eT phT inferInstance) tT tF 0
    (by intro p ⟨j, hj⟩; subst hj; intro _ _ e _ _ _; subst e; rfl)
    (fun hx => ftF ((MonPred.monPred_impl_force (I := DIdx) (PROP := SiProp) tF eT phT) 0 hx 0 (Nat.le_refl 0) trivial))

-- `Iris.BI.MonPred.wand_objective` idx 5: necessary (DIdx over SiProp: P = ⌜i = true⌝, Q = embed False)
theorem w5c5_33 : ¬ drop0% Iris.BI.MonPred.wand_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ phT eF inferInstance) tF tT 0
    (by intro p ⟨j, hj⟩; subst hj; intro _ _ e _ _ ht; subst e; exact ftF ht)
    (fun hx => (MonPred.monPred_wand_force (I := DIdx) (PROP := SiProp) tT phT eF) 0 hx 0 (Nat.le_refl 0) rfl)

-- `Iris.BI.MonPred.wand_objective` idx 6: necessary (DIdx over SiProp: P = embed True, Q = ⌜i = true⌝)
theorem w5c5_34 : ¬ drop0% Iris.BI.MonPred.wand_objective 6 := fun h =>
  notObj (@h DIdx SiProp _ eT phT inferInstance) tT tF 0
    (by intro p ⟨j, hj⟩; subst hj; intro _ _ e _ _ _; subst e; rfl)
    (fun hx => ftF ((MonPred.monPred_wand_force (I := DIdx) (PROP := SiProp) tF eT phT) 0 hx 0 (Nat.le_refl 0) trivial))

-- `Iris.BI.MonPred.forall_objective` idx 5: necessary (DIdx: Φ _ = ⌜i = true⌝ over α = True)
theorem w5c5_35 : ¬ drop0% Iris.BI.MonPred.forall_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ True (fun _ => phT)) tT tF 0
    ((MonPred.monPred_at_forall (I := DIdx) (PROP := SiProp) tT (fun _ : True => phT)).mpr 0 (SiProp.forall_holds.2 fun _ => rfl))
    (fun hx => ftF (SiProp.forall_holds.1 ((MonPred.monPred_at_forall (I := DIdx) (PROP := SiProp) tF (fun _ : True => phT)).mp 0 hx) trivial))

-- `Iris.BI.MonPred.persistently_objective` idx 4: necessary (DIdx: P = ⌜i = true⌝)
theorem w5c5_36 : ¬ drop0% Iris.BI.MonPred.persistently_objective 4 := fun h =>
  notObj (@h DIdx SiProp _ phT) tT tF 0 rfl ftF

-- `Iris.BI.MonPred.affinely_objective` idx 4: necessary (DIdx: P = ⌜i = true⌝)
theorem w5c5_37 : ¬ drop0% Iris.BI.MonPred.affinely_objective 4 := fun h =>
  notObj (@h DIdx SiProp _ phT) tT tF 0 ⟨trivial, rfl⟩ (fun h => ftF h.2)

-- `Iris.BI.MonPred.absorbingly_objective` idx 4: necessary (DIdx: P = ⌜i = true⌝)
theorem w5c5_38 : ¬ drop0% Iris.BI.MonPred.absorbingly_objective 4 := fun h =>
  notObj (@h DIdx SiProp _ phT) tT tF 0 ⟨trivial, rfl⟩ (fun h => ftF h.2)

-- `Iris.BI.MonPred.intuitionistically_objective` idx 4: necessary (DIdx: P = ⌜i = true⌝)
theorem w5c5_39 : ¬ drop0% Iris.BI.MonPred.intuitionistically_objective 4 := fun h =>
  notObj (@h DIdx SiProp _ phT) tT tF 0 ⟨trivial, rfl⟩ (fun h => ftF h.2)

-- `Iris.BI.MonPred.persistently_if_objective` idx 5: necessary (p = false, P = ⌜i = true⌝)
theorem w5c5_40 : ¬ drop0% Iris.BI.MonPred.persistently_if_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ false phT) tT tF 0 rfl ftF

-- `Iris.BI.MonPred.affinely_if_objective` idx 5: necessary (p = false, P = ⌜i = true⌝)
theorem w5c5_41 : ¬ drop0% Iris.BI.MonPred.affinely_if_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ false phT) tT tF 0 rfl ftF

-- `Iris.BI.MonPred.absorbingly_if_objective` idx 5: necessary (p = false, P = ⌜i = true⌝)
theorem w5c5_42 : ¬ drop0% Iris.BI.MonPred.absorbingly_if_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ false phT) tT tF 0 rfl ftF

-- `Iris.BI.MonPred.intuitionistically_if_objective` idx 5: necessary (p = false, P = ⌜i = true⌝)
theorem w5c5_43 : ¬ drop0% Iris.BI.MonPred.intuitionistically_if_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ false phT) tT tF 0 rfl ftF

-- `Iris.BI.MonPred.later_objective` idx 4: necessary (P = ⌜i = true⌝, step 1)
theorem w5c5_44 : ¬ drop0% Iris.BI.MonPred.later_objective 4 := fun h =>
  notObj (@h DIdx SiProp _ phT) tT tF 1 rfl ftF

-- `Iris.BI.MonPred.laterN_objective` idx 5: necessary (n = 0, P = ⌜i = true⌝)
theorem w5c5_45 : ¬ drop0% Iris.BI.MonPred.laterN_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ 0 phT) tT tF 0 rfl ftF

-- `Iris.BI.MonPred.except0_objective` idx 4: necessary (P = ⌜i = true⌝, step 1)
theorem w5c5_46 : ¬ drop0% Iris.BI.MonPred.except0_objective 4 := fun h =>
  notObj (@h DIdx SiProp _ phT) tT tF 1 (.inr rfl) (fun h => h.elim id ftF)

-- `Iris.BI.MonPred.plainly_if_objective` idx 5: necessary (p = false, P = ⌜i = true⌝)
theorem w5c5_47 : ¬ drop0% Iris.BI.MonPred.plainly_if_objective 5 := fun h =>
  notObj (@h DIdx SiProp _ false phT) tT tF 0 rfl ftF

-- `Iris.BI.MonPred.objective_objectively` idx 4: necessary (P = ⌜i = true⌝)
theorem w5c5_48 : ¬ drop0% Iris.BI.MonPred.objective_objectively 4 := fun h =>
  ftF (SiProp.forall_holds.1 ((@h DIdx SiProp _ phT) tT 0 rfl) tF)

-- `Iris.BI.MonPred.objective_subjectively` idx 4: necessary (P = ⌜i = true⌝)
theorem w5c5_49 : ¬ drop0% Iris.BI.MonPred.objective_subjectively 4 := fun h =>
  ftF ((@h DIdx SiProp _ phT) tF 0 (SiProp.exists_holds.2 ⟨tT, rfl⟩))

-- `Iris.BI.MonPred.monPred_objectively_mono` idx 5: necessary (P = embed True, Q = embed False)
theorem w5c5_50 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_mono 5 := fun h =>
  SiProp.forall_holds.1 ((@h UIdx SiProp _ eT eF) (0 : Nat) 0 (SiProp.forall_holds.2 fun _ => trivial)) (0 : Nat)

-- `Iris.BI.MonPred.monPred_subjectively_mono` idx 5: necessary (P = embed True, Q = embed False)
theorem w5c5_51 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_mono 5 := fun h => by
  obtain ⟨_, hf⟩ := SiProp.exists_holds.1 ((@h UIdx SiProp _ eT eF) (0 : Nat) 0
    (SiProp.exists_holds.2 ⟨(0 : Nat), trivial⟩))
  exact hf

-- `Iris.BI.MonPred.monPred_objectively_affine` idx 4: necessary (GB: P = embed True)
theorem w5c5_52 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_affine 4 := fun h =>
  Bool.noConfusion ((@h UIdx GB gbBI (MonPred.embed iprop(True))).1 (0 : Nat) true
    (fun _ ⟨_, hp⟩ => hp ▸ trivial) : true = false)

-- `Iris.BI.MonPred.monPred_objectively_absorbing` idx 4: necessary (GB: P = embed emp)
theorem w5c5_53 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_absorbing 4 := fun h =>
  Bool.noConfusion (((@h UIdx GB gbBI (MonPred.embed iprop(emp))).1 (0 : Nat) true
    ⟨true, false, rfl, trivial, fun _ ⟨_, hp⟩ => hp ▸ rfl⟩) _ ⟨(0 : Nat), rfl⟩ : true = false)

-- `Iris.BI.MonPred.monPred_objectively_persistent` idx 5: necessary (GB: P = embed own1)
theorem w5c5_54 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_persistent 5 := fun h =>
  Bool.noConfusion (((@h UIdx GB gbBI _ (MonPred.embed own1)).1 (0 : Nat) true
    (fun _ ⟨_, hp⟩ => hp ▸ rfl)) _ ⟨(0 : Nat), rfl⟩ : false = true)

-- `Iris.BI.MonPred.monPred_objectively_timeless` idx 4: necessary (SiProp: P = embed s0, step 1)
theorem w5c5_55 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_timeless 4 := fun h =>
  ((@h UIdx SiProp _ (MonPred.embed s0)).1 (0 : Nat) 1 (SiProp.forall_holds.2 fun _ => rfl)).elim
    (fun hf => hf) (fun hx => Nat.noConfusion (SiProp.forall_holds.1 hx (0 : Nat) : (1 : Nat) = 0))

-- `Iris.BI.MonPred.monPred_subjectively_affine` idx 4: necessary (GB: P = embed True)
theorem w5c5_56 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_affine 4 := fun h =>
  Bool.noConfusion ((@h UIdx GB gbBI (MonPred.embed iprop(True))).1 (0 : Nat) true
    ⟨_, ⟨(0 : Nat), rfl⟩, trivial⟩ : true = false)

-- `Iris.BI.MonPred.monPred_subjectively_absorbing` idx 4: necessary (GB: P = embed emp)
theorem w5c5_57 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_absorbing 4 := fun h => by
  obtain ⟨_, ⟨_, rfl⟩, hp⟩ := (@h UIdx GB gbBI (MonPred.embed iprop(emp))).1 (0 : Nat) true
    ⟨true, false, rfl, trivial, _, ⟨(0 : Nat), rfl⟩, rfl⟩
  exact Bool.noConfusion (hp : true = false)

-- `Iris.BI.MonPred.monPred_subjectively_persistent` idx 4: necessary (GB: P = embed own1)
theorem w5c5_58 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_persistent 4 := fun h => by
  obtain ⟨_, ⟨_, rfl⟩, hp⟩ := (@h UIdx GB gbBI (MonPred.embed own1)).1 (0 : Nat) true
    ⟨_, ⟨(0 : Nat), rfl⟩, rfl⟩
  exact Bool.noConfusion (hp : false = true)

-- `Iris.BI.MonPred.monPred_subjectively_timeless` idx 4: necessary (SiProp: P = embed s0, step 1)
theorem w5c5_59 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_timeless 4 := fun h =>
  ((@h UIdx SiProp _ (MonPred.embed s0)).1 (0 : Nat) 1 (SiProp.exists_holds.2 ⟨(0 : Nat), rfl⟩)).elim
    (fun hf => hf) (fun hx => by
      obtain ⟨_, h1⟩ := SiProp.exists_holds.1 hx
      exact Nat.noConfusion (h1 : (1 : Nat) = 0))


-- `Iris.BI.MonPred.monPred_objectively_sep` idx 4: necessary (GB over the discrete Bool index without bottom: P2 = (own1 | emp), Q2 = (emp | own1))
theorem w5c5_60 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_sep 4 := fun h =>
  obj_sep_bad .rfl .rfl (@h DIdx GB gbBI tT P2 Q2).1

-- `Iris.BI.MonPred.monPred_objectively_monoid_sep_homomorphism` idx 4: necessary (map_op fails for P2, Q2 over GB, discrete Bool index)
theorem w5c5_61 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_monoid_sep_homomorphism 4 := fun h =>
  obj_sep_bad .rfl .rfl (BIBase.Entails.of_eq ((@h DIdx GB gbBI tT).map_op (x := P2) (y := Q2)))

-- `Iris.BI.MonPred.monPred_objectively_big_sepL` idx 4: necessary (list [true, false] with Φ b = P2 or Q2, GB, discrete Bool index)
theorem w5c5_62 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_big_sepL 4 := fun h =>
  objP_sep_false _ true ((@h DIdx GB gbBI tT Bool (fun _ b => cond b P2 Q2) [true, false]).1 tT true objPQe)

-- `Iris.BI.MonPred.monPred_objectively_persistent` idx 3: necessary (PF, discrete Nat index: P i = <pers> (evens or ≥ i) persistent, <obj> P not)
theorem w5c5_63 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_persistent 3 := fun h =>
  obj_Pk_not_pers (@h NIdx PF pfBI Pk inferInstance)

-- `Iris.BI.instBIPersistentlyForallMonPred` idx 3: necessary (PF: persistently_forall fails for embed (evens or ≥ k))
theorem w5c5_64 : ¬ drop0% Iris.BI.instBIPersistentlyForallMonPred 3 := fun h => by
  letI := @h UIdx PF pfBI
  have H := (persistently_forall (PROP := MonPred UIdx PF)
    (Ψ := fun k : Nat => (MonPred.embed (evk k) : MonPred UIdx PF))).2 (0 : Nat) 0
    ((MonPred.monPred_at_forall (I := UIdx) (PROP := PF) (0 : Nat)
      (fun k : Nat => iprop(<pers> (MonPred.embed (evk k) : MonPred UIdx PF)))).2 0 (fun p ⟨k, hk⟩ => hk ▸ ⟨evk_cof k, Or.inl rfl⟩))
  obtain ⟨N, hN⟩ := H.1
  have := (MonPred.monPred_at_forall (I := UIdx) (PROP := PF) (0 : Nat)
    (fun k : Nat => (MonPred.embed (evk k) : MonPred UIdx PF))).1 (2 * N + 1)
    (hN (2 * N + 1) (by omega)) _ ⟨2 * N + 2, rfl⟩
  have h2 : evk (2 * N + 2) (2 * N + 1) := this
  simp only [evk] at h2; omega

-- `Iris.BI.instBIPersistentlyExistMonPred` idx 3: necessary (PF: persistently_exists fails for embed evens / odds)
theorem w5c5_65 : ¬ drop0% Iris.BI.instBIPersistentlyExistMonPred 3 := fun h => by
  letI := @h UIdx PF pfBI
  have H := (persistently_exists (PROP := MonPred UIdx PF)
    (Ψ := fun b : Bool => (MonPred.embed (cond b ev od) : MonPred UIdx PF))).1 (0 : Nat) 0
    ⟨⟨0, fun m _ => (MonPred.monPred_at_exist (I := UIdx) (PROP := PF) (0 : Nat)
        (fun b : Bool => (MonPred.embed (cond b ev od) : MonPred UIdx PF))).2 m (by
        rcases Nat.mod_two_eq_zero_or_one m with hm | hm
        · exact ⟨_, ⟨true, rfl⟩, hm⟩
        · exact ⟨_, ⟨false, rfl⟩, hm⟩)⟩,
      (MonPred.monPred_at_exist (I := UIdx) (PROP := PF) (0 : Nat)
        (fun b : Bool => (MonPred.embed (cond b ev od) : MonPred UIdx PF))).2 0
        ⟨_, ⟨true, rfl⟩, (rfl : 0 % 2 = 0)⟩⟩
  obtain ⟨_, ⟨b, rfl⟩, hp⟩ := (MonPred.monPred_at_exist (I := UIdx) (PROP := PF) (0 : Nat)
    (fun b : Bool => iprop(<pers> (MonPred.embed (cond b ev od) : MonPred UIdx PF)))).1 0 H
  cases b
  · exact od_not_cof hp.1
  · exact ev_not_cof hp.1

-- `Iris.BI.MonPred.monPred_subjectively_persistently` idx 3: necessary (PF, discrete Bool index: P = (evens | odds))
theorem w5c5_66 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_persistently 3 := fun h => by
  obtain ⟨_, ⟨i, rfl⟩, hp⟩ := (@h DIdx PF pfBI Pe).2 tT 0 pers_subj_Pe
  exact Pe_not_cof i hp.1

-- `Iris.BI.MonPred.monPred_subjectively_intuitionistically` idx 3: necessary (PF, discrete Bool index: P = (evens | odds))
theorem w5c5_67 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_intuitionistically 3 := fun h => by
  obtain ⟨_, ⟨i, rfl⟩, hp⟩ := (@h DIdx PF pfBI Pe).2 tT 0 ⟨trivial, pers_subj_Pe⟩
  exact Pe_not_cof i hp.2.1

-- `Iris.BI.MonPred.monPred_subjectively_persistently_if` idx 3: necessary (p = true; PF, P = (evens | odds))
theorem w5c5_68 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_persistently_if 3 := fun h => by
  obtain ⟨_, ⟨i, rfl⟩, hp⟩ := (@h DIdx PF pfBI true Pe).2 tT 0 pers_subj_Pe
  exact Pe_not_cof i hp.1

-- `Iris.BI.MonPred.monPred_subjectively_intuitionistically_if` idx 3: necessary (p = true; PF, P = (evens | odds))
theorem w5c5_69 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_intuitionistically_if 3 := fun h => by
  obtain ⟨_, ⟨i, rfl⟩, hp⟩ := (@h DIdx PF pfBI true Pe).2 tT 0 ⟨trivial, pers_subj_Pe⟩
  exact Pe_not_cof i hp.2.1

-- `Iris.BI.MonPred.monPred_at_hom` idx 7: necessary (op₁ = ∗ at index true, left projection at false: not commutative; op₂ = ∗ on SiProp)
theorem w5c5_70 : ¬ indep0% Iris.BI.MonPred.monPred_at_hom 7 := fun h => by
  have H := @h DIdx SiProp _ opL BIBase.sep iprop(emp) iprop(emp) inferInstance tT (fun {_ _} => rfl) rfl
  have e := congrArg (fun P : MonPred DIdx SiProp => (P.monPred_at tF).holds 0)
    (Iris.Algebra.MonoidOps.op_comm (op := opL) (a := eT) (b := eF))
  exact (show True = False from e) ▸ trivial

-- `Iris.BI.MonPred.monPred_at_hom` idx 8: removable, derivable: by hop every op₂ a b is (op₁ ⎡a⎤ ⎡b⎤) at i, so op₂ inherits the monoid laws of op₁ (unit by hunit)
theorem w5c5_71 : indep% Iris.BI.MonPred.monPred_at_hom 8 := by
  intro I PROP _ op₁ op₂ u₁ u₂ _ i hop hunit
  have e : ∀ a b : PROP, op₂ a b = (op₁ (MonPred.embed a) (MonPred.embed b)).monPred_at i :=
    fun a b => (hop (x := MonPred.embed a) (y := MonPred.embed b)).symm
  exact {
    op_ne := ⟨fun n a a' ha b b' hb => by
      rw [e a b, e a' b']
      exact (Iris.Algebra.MonoidOps.op_ne (op := op₁)).ne
        (x₁ := MonPred.embed a) (x₂ := MonPred.embed a') (fun _ => ha)
        (y₁ := MonPred.embed b) (y₂ := MonPred.embed b') (fun _ => hb) i⟩
    op_assoc := fun {a b c} =>
      (congrArg (op₂ · c) (e a b)).trans <|
      (hop (x := op₁ (MonPred.embed a) (MonPred.embed b)) (y := MonPred.embed c)).symm.trans <|
      (congrArg (·.monPred_at i) (Iris.Algebra.MonoidOps.op_assoc (op := op₁))).trans <|
      (hop (x := MonPred.embed a) (y := op₁ (MonPred.embed b) (MonPred.embed c))).trans
        (congrArg (op₂ a) (e b c).symm)
    op_comm := fun {a b} =>
      (e a b).trans ((congrArg (·.monPred_at i) (Iris.Algebra.MonoidOps.op_comm (op := op₁))).trans (e b a).symm)
    op_left_id := fun {a} =>
      (congrArg (op₂ · a) hunit.symm).trans <|
      (hop (x := u₁) (y := MonPred.embed a)).symm.trans
        (congrArg (·.monPred_at i) (Iris.Algebra.MonoidOps.op_left_id (op := op₁))) }

-- `Iris.BI.MonPred.monPred_at_hom` idx 10: necessary (op₁ = ∧ on MonPred over GB, op₂ = pointwise ↔ on GB, both with unit True)
theorem w5c5_72 : ¬ drop0% Iris.BI.MonPred.monPred_at_hom 10 := fun h => by
  have H := @h UIdx GB gbBI BIBase.and iffOp iprop(True) iprop(True) inferInstance iffMon (0 : Nat) rfl
  have e := congrFun (H.map_op (x := (MonPred.embed (fun _ => False) : MonPred UIdx GB))
    (y := MonPred.embed (fun _ => False))) false
  exact (cast e.symm (show False ↔ False from Iff.rfl)).1

-- `Iris.BI.MonPred.monPred_at_hom` idx 11: removable, derivable: u₁ i = op₂ u₂ (u₁ i) = (op₁ ⎡u₂⎤ u₁) i = ⎡u₂⎤ i = u₂ by hop and the unit laws
theorem w5c5_73 : drop% Iris.BI.MonPred.monPred_at_hom 11 := by
  intro I PROP _ op₁ op₂ u₁ u₂ _ _ i hop
  refine MonPred.monPred_at_hom i hop ?_
  exact (Iris.Algebra.MonoidOps.op_left_id (op := op₂) (a := u₁.monPred_at i)).symm.trans <|
    (hop (x := MonPred.embed u₂) (y := u₁)).symm.trans <|
    (congrArg (·.monPred_at i) (Iris.Algebra.MonoidOps.op_comm (op := op₁))).trans
      (congrArg (·.monPred_at i) (Iris.Algebra.MonoidOps.op_left_id (op := op₁)))

-- `Iris.BI.MonPred.monPred_bi_bupd_lc` idx 5: necessary (SiProp, later credits all False, identity bupd: ⊢ |==> £ 0 fails)
theorem w5c5_74 : ¬ drop0% Iris.BI.MonPred.monPred_bi_bupd_lc 5 := fun h =>
  (@h UIdx SiProp _ lcF idBupd).lc_zero (0 : Nat) 0 trivial

-- `Iris.BI.MonPred.monPred_bi_bupd_sbi` idx 4: necessary (SiProp with constant-True bupd: |==> ⌜False⌝ holds)
theorem w5c5_75 : ¬ drop0% Iris.BI.MonPred.monPred_bi_bupd_sbi 4 := fun h => by
  have H := (@h UIdx SiProp instSbiSiProp topBupd).bupd_siPure iprop(False)
  exact H (0 : Nat) 0 trivial

-- `Iris.BI.MonPred.big_sepL_objective` idx 6: necessary (list [()], Φ = ⌜i = true⌝ over the discrete Bool index)
theorem w5c5_76 : ¬ drop0% Iris.BI.MonPred.big_sepL_objective 6 := fun h =>
  notObj (@h DIdx SiProp _ Unit (fun _ _ => phT) [()]) tT tF 0 ⟨rfl, trivial⟩ (fun h => ftF h.1)

-- `Iris.BI.MonPred.big_sepM_objective` idx 9: necessary (one-key map, Φ = ⌜i = true⌝ over the discrete Bool index)
theorem w5c5_77 : ¬ drop0% Iris.BI.MonPred.big_sepM_objective 9 := fun h =>
  notObjE (@h DIdx SiProp _ Nat Unit TM _ (fun _ _ => phT) (sg ())) (BIBase.BiEntails.of_eq (sgE _ ()))

-- `Iris.BI.MonPred.big_sepS_objective` idx 8: necessary (set {0}, Φ = ⌜i = true⌝ over the discrete Bool index)
theorem w5c5_78 : ¬ drop0% Iris.BI.MonPred.big_sepS_objective 8 := fun h =>
  notObjE (@h DIdx SiProp _ TS Nat _ (fun _ => phT) {0}) (ssE _)

-- `Iris.BI.MonPred.big_sepMS_objective` idx 8: necessary (multiset {0}, Φ = ⌜i = true⌝ over the discrete Bool index)
theorem w5c5_79 : ¬ drop0% Iris.BI.MonPred.big_sepMS_objective 8 := fun h =>
  notObjE (@h DIdx SiProp _ MSN Nat _ (fun _ => phT) {0}) (msSing _)

-- `Iris.BI.MonPred.monPred_objectively_big_sepM` idx 4: necessary (two-key map with Φ = P2 / Q2, GB, discrete Bool index)
theorem w5c5_80 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_big_sepM 4 := fun h => by
  have H := (@h DIdx GB gbBI tT Nat Bool TM _ (fun _ b => cond b P2 Q2) (tw false true)).1
  rw [twE, twE] at H
  exact obj_sep_bad .rfl .rfl H

-- `Iris.BI.MonPred.monPred_objectively_big_sepS` idx 4: necessary (set {0, 1} with Φ = P2 / Q2, GB, discrete Bool index)
theorem w5c5_81 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_big_sepS 4 := fun h => by
  have H := (@h DIdx GB gbBI tT TS Nat _ (fun n => cond (n == 1) P2 Q2)
    (@Insert.insert Nat TS LawfulSet.instInsert 1 {0})).1
  rw [(s01 _).to_eq, (s01 _).to_eq] at H
  exact obj_sep_bad .rfl .rfl H

-- `Iris.BI.MonPred.monPred_objectively_big_sepMS` idx 4: necessary (multiset {0} ⊎ {1} with Φ = P2 / Q2, GB, discrete Bool index)
theorem w5c5_82 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_big_sepMS 4 := fun h => by
  have H := (@h DIdx GB gbBI tT MSN Nat _ (fun n => cond (n == 0) P2 Q2) (({0} : MSN) ⊎ {1})).1
  rw [(ms01 _).to_eq, (ms01 _).to_eq] at H
  exact obj_sep_bad .rfl .rfl H

-- `Iris.BI.MonPred.monPred_objectively_plain` idx 4: necessary (UPred NA, P = embed (ownM a): <obj> ⎡P⎤ = ⎡P⎤ not plain)
theorem w5c5_83 : ¬ drop0% Iris.BI.MonPred.monPred_objectively_plain 4 := fun h => by
  have H := @h UIdx (UPred NA) _ (MonPred.embed (UPred.ownM .a))
  have e : iprop(<obj> (MonPred.embed (UPred.ownM NA.a) : MonPred UIdx (UPred NA))) = MonPred.embed (UPred.ownM .a) :=
    (MonPred.monPred_objectively_embed (UPred.ownM NA.a)).to_eq
  rw [e] at H
  haveI := H
  have H2 := (MonPred.monPred_at_plain (I := UIdx) (PROP := UPred NA) (MonPred.embed (UPred.ownM .a))
    (0 : Nat)).plain 0 ⟨.a, trivial⟩ rfl
  cases H2

-- `Iris.BI.MonPred.monPred_subjectively_plain` idx 4: necessary (UPred NA, P = embed (ownM a): <subj> ⎡P⎤ = ⎡P⎤ not plain)
theorem w5c5_84 : ¬ drop0% Iris.BI.MonPred.monPred_subjectively_plain 4 := fun h => by
  have H := @h UIdx (UPred NA) _ (MonPred.embed (UPred.ownM .a))
  have e : iprop(<subj> (MonPred.embed (UPred.ownM NA.a) : MonPred UIdx (UPred NA))) = MonPred.embed (UPred.ownM .a) :=
    BIBase.BiEntails.to_eq ⟨@MonPred.objective_subjectively UIdx (UPred NA) _ (MonPred.embed _) ⟨fun _ _ => .rfl⟩,
      MonPred.monPred_subjectively_intro _⟩
  rw [e] at H
  haveI := H
  have H2 := (MonPred.monPred_at_plain (I := UIdx) (PROP := UPred NA) (MonPred.embed (UPred.ownM .a))
    (0 : Nat)).plain 0 ⟨.a, trivial⟩ rfl
  cases H2

-- `Iris.BI.MonPred.monPred_sbi_emp_valid_exist` idx 4: necessary (SiProp, discrete Bool index without bottom: ■ (∃ a, ⌜i = a⌝) holds, no single a works)
theorem w5c5_85 : ¬ drop0% Iris.BI.MonPred.monPred_sbi_emp_valid_exist 4 := fun h => by
  letI := @h DIdx SiProp _ tT inferInstance
  have c : iprop(■ (MonPred.embed iprop(True) : MonPred DIdx SiProp)) ⊢ iprop(∃ a, ■ phD a) :=
    (plainly_mono (fun i n _ => (MonPred.monPred_at_exist i phD).mpr n
      (SiProp.exists_holds.2 ⟨(show Bool from i), rfl⟩))).trans plainly_exists.mp
  have hp := (MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) tT
    (MonPred.embed iprop(True))).mpr 0 (SiProp.forall_holds.2 fun _ => trivial)
  have d := (MonPred.monPred_at_exist (I := DIdx) (PROP := SiProp) tT
    (fun a => iprop(■ phD a))).mp 0 (c tT 0 hp)
  obtain ⟨a, ha⟩ := SiProp.exists_holds.1 d
  have e := SiProp.forall_holds.1 ((MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) tT (phD a)).mp 0 ha)
  have e1 : (true : Bool) = a := e tT
  have e2 : (false : Bool) = a := e tF
  exact Bool.noConfusion (e1.trans e2.symm)

-- `Iris.BI.MonPred.monPred_sbi_emp_valid_exist` idx 5: necessary (Nat index with bottom 0 over PROP = MonPred over the discrete Bool index (not SbiEmpValidExist))
theorem w5c5_86 : ¬ drop0% Iris.BI.MonPred.monPred_sbi_emp_valid_exist 5 := fun h => by
  letI := @h UIdx (MonPred DIdx SiProp) _ (0 : Nat) ⟨fun i => Nat.zero_le i⟩
  have c : iprop(■ (MonPred.embed (MonPred.embed iprop(True)) : MonPred UIdx (MonPred DIdx SiProp)))
      ⊢ iprop(∃ a, ■ (MonPred.embed (phD a) : MonPred UIdx (MonPred DIdx SiProp))) :=
    (plainly_mono (fun k i n _ => (MonPred.monPred_at_exist k
      (fun a => (MonPred.embed (phD a) : MonPred UIdx (MonPred DIdx SiProp)))).mpr i n
      ((MonPred.monPred_at_exist i (fun a => phD a)).mpr n
        (SiProp.exists_holds.2 ⟨(show Bool from i), rfl⟩)))).trans plainly_exists.mp
  have hpi := (MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) tT
    (MonPred.embed iprop(True))).mpr 0 (SiProp.forall_holds.2 fun _ => trivial)
  have hpo := (MonPred.monPred_at_plainly (I := UIdx) (PROP := MonPred DIdx SiProp) (0 : Nat)
    (MonPred.embed (MonPred.embed iprop(True)))).mpr tT 0
    ((MonPred.monPred_at_forall (I := DIdx) (PROP := SiProp) tT
      (fun _ : Nat => iprop(■ (MonPred.embed iprop(True) : MonPred DIdx SiProp)))).mpr 0
      (SiProp.forall_holds.2 fun _ => hpi))
  have d := (MonPred.monPred_at_exist (I := DIdx) (PROP := SiProp) tT _).mp 0
    ((MonPred.monPred_at_exist (I := UIdx) (PROP := MonPred DIdx SiProp) (0 : Nat)
      (fun a => iprop(■ (MonPred.embed (phD a) : MonPred UIdx (MonPred DIdx SiProp))))).mp tT 0
      (c (0 : Nat) tT 0 hpo))
  obtain ⟨a, ha⟩ := SiProp.exists_holds.1 d
  have f := (MonPred.monPred_at_plainly (I := UIdx) (PROP := MonPred DIdx SiProp) (0 : Nat)
    (MonPred.embed (phD a))).mp tT 0 ha
  have g := SiProp.forall_holds.1 ((MonPred.monPred_at_forall (I := DIdx) (PROP := SiProp) tT
    (fun _ : Nat => iprop(■ phD a))).mp 0 f) (0 : Nat)
  have e := SiProp.forall_holds.1 ((MonPred.monPred_at_plainly (I := DIdx) (PROP := SiProp) tT (phD a)).mp 0 g)
  have e1 : (true : Bool) = a := e tT
  have e2 : (false : Bool) = a := e tF
  exact Bool.noConfusion (e1.trans e2.symm)

-- `Iris.BI.MonPred.fupd_objective` idx 7: necessary (IProp, discrete Bool index, P = (True | False): objectivity would give ⊢ |={⊤}=> False)
theorem w5c5_87 : ¬ drop0% Iris.BI.MonPred.fupd_objective 7 := fun h =>
  fupd_false fun {_} => (true_intro.trans fupd_intro).trans
    ((@h DIdx (IProp CGF) _ inferInstance ⊤ ⊤ (mpD iprop(True) iprop(⌜False⌝))).1 tT tF)

-- `Iris.BI.instBIUpdateFUpdateMonPred` idx 5: necessary (IProp with constant-True bupd and the invariant fupd: |==> False ⊢ |={⊤}=> False would give ⊢ |={⊤}=> False)
theorem w5c5_88 : ¬ drop0% Iris.BI.instBIUpdateFUpdateMonPred 5 := fun h =>
  fupd_false fun {_} => true_intro.trans
    ((@h UIdx (IProp CGF) _ topBupdI inferInstance).fupd_of_bupd
      (P := MonPred.embed iprop(⌜False⌝)) (E := ⊤) (0 : Nat))

-- `Iris.BI.MonPred.monPred_bi_fupd_lc` idx 5: necessary (IProp with £ n := True: ▷Q ⊢ Q for Q = |={⊤}=> False, Löb and fupd_soundness give False)
theorem w5c5_89 : ¬ drop0% Iris.BI.MonPred.monPred_bi_fupd_lc 5 := fun h =>
  fupd_loeb_false fun {_} => by
    have H := @h UIdx (IProp CGF) _ lcT inferInstance
    have K : (iprop(▷ (MonPred.embed iprop(|={⊤}=> ⌜False⌝))) : MonPred UIdx (IProp CGF)) ⊢
        iprop(|={⊤}=> (MonPred.embed iprop(|={⊤}=> ⌜False⌝))) :=
      (emp_sep.2.trans (sep_mono_left (true_intro.trans (Iris.BI.entails_at.mpr fun _ => .rfl)))).trans
        (wand_elim (wand_entails (H.lc_fupd_elim_later (E := ⊤)
          (P := (MonPred.embed iprop(|={⊤}=> ⌜False⌝) : MonPred UIdx (IProp CGF))))))
    exact (K (0 : Nat)).trans BIFUpdate.trans
