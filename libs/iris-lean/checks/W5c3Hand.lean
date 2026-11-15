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
namespace W5c3
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
theorem tn_dist {n} {x y : TN} : x ≡{n}≡ y ↔ min x.v (n+1) = min y.v (n+1) := Iff.rfl

open OFE in
theorem lfp_iff {A} [OFE A] (F : (A → GB) → A → GB) (x : A) (w : Bool) :
    bi_least_fixpoint F x w ↔ ∀ Φ : A -n> GB, (∀ y z, F Φ y z → Φ y z) → Φ x w := by
  constructor
  · intro h Φ hΦ
    have h1 := h _ ⟨Φ, rfl⟩ false
    simp only [Bool.xor_false] at h1
    apply h1
    refine ⟨rfl, ?_⟩
    intro p hp
    obtain ⟨y, hy⟩ := hp
    subst hy
    intro z hz
    simpa using hΦ y z hz
  · intro h p hp
    obtain ⟨Φ, hp⟩ := hp
    subst hp
    intro y hy
    obtain ⟨hy, hR⟩ := hy
    have hy : y = false := hy
    subst hy
    simp only [Bool.xor_false]
    refine h Φ fun y z hz => ?_
    simpa using hR _ ⟨y, rfl⟩ z hz

open OFE in
theorem gfp_iff {A} [OFE A] (F : (A → GB) → A → GB) (x : A) (w : Bool) :
    bi_greatest_fixpoint F x w ↔ ∃ Φ : A -n> GB, (∀ y z, Φ y z → F Φ y z) ∧ Φ x w := by
  constructor
  · intro h
    obtain ⟨p, ⟨Φ, hp⟩, hr⟩ := h
    subst hp
    obtain ⟨a, b, e, ⟨ha, hR⟩, hb⟩ := hr
    have ha : a = false := ha
    subst ha
    refine ⟨Φ, fun y z hz => ?_, by simpa [e] using hb⟩
    simpa using hR _ ⟨y, rfl⟩ z hz
  · intro h
    obtain ⟨Φ, hΦ, hx⟩ := h
    refine ⟨_, ⟨Φ, rfl⟩, false, w, by simp, ⟨rfl, ?_⟩, hx⟩
    intro p hp
    obtain ⟨y, hy⟩ := hp
    subst hy
    intro z hz
    simpa using hΦ y z hz

/-! Evaluation helpers: GB entailments of the shape `⊢ □ (∀ y, P y -∗ Q y) -∗ ∀ x, R x -∗ S x`. -/
theorem ev2 {A B : Type _} {P Q : A → GB} {R S : B → GB}
    (h : ⊢ iprop(□ (∀ y, P y -∗ Q y) -∗ ∀ x, R x -∗ S x))
    (hle : ∀ y z, P y z → Q y z) : ∀ x z, R x z → S x z := by
  intro x z hz
  have h1 := h false rfl false
  simp only [Bool.xor_false] at h1
  have h2 := h1 ⟨rfl, ?_⟩
  · have h3 := h2 _ ⟨x, rfl⟩ z hz
    simpa using h3
  · intro p hp
    obtain ⟨y, hy⟩ := hp
    subst hy
    intro z hz
    simpa using hle y z hz

open OFE in
def mkH {A} [OFE A] [Discrete A] (f : A → GB) : A -n> GB := ⟨f, inferInstance⟩

/-- TN-indicator of 1: not non-expansive into GB. -/
def ind1 : TN → GB := fun x _ => x = ⟨1⟩
theorem ind1_not_ne : ¬ OFE.NonExpansive ind1 := fun h => by
  have := congrFun (h.ne tn12) false
  have h2 : ind1 ⟨1⟩ false := rfl
  rw [this] at h2
  exact absurd (congrArg TN.v h2) (by decide)

instance idMono {PROP A} [BI PROP] [OFE A] : BIMonoPred (fun Φ : A → PROP => Φ) where
  mono_pred := by
    intro Φ Ψ _ _
    iintro #H %x Hx
    iapply H $$ Hx
  mono_pred_ne := inferInstance

instance constMono {PROP A} [BI PROP] [OFE A] (P : PROP) : BIMonoPred (fun (_ : A → PROP) (_ : A) => P) where
  mono_pred := by
    intro Φ Ψ _ _
    iintro #H %x Hx
    iexact Hx
  mono_pred_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩

/-- Non-monotone F whose values are constant in the world: least fixpoint is own1 = {true}. -/
def kF : (Unit → GB) → Unit → GB := fun Φ x _ => ¬ Φ x true ∨ Φ x false
theorem kf_t : bi_least_fixpoint kF () true :=
  (lfp_iff ..).2 fun Φ hΦ => Classical.byContradiction fun hn => hn (hΦ () true (Or.inl hn))
theorem kf_f : ¬ bi_least_fixpoint kF () false := fun h => by
  have := (lfp_iff ..).1 h (mkH fun _ z => z = true) (fun y z hz => by
    simp [kF, mkH] at hz)
  exact absurd this (by simp [mkH])

instance indepMono {PROP A} [BI PROP] [OFE A] (G : A → PROP) [hG : OFE.NonExpansive G] :
    BIMonoPred (fun (_ : A → PROP) (x : A) => G x) where
  mono_pred := by
    intro Φ Ψ _ _
    iintro #H %x Hx
    iexact Hx
  mono_pred_ne := hG

/-- Non-monotone F on Unit → GB: F ∅ = {false}, F {true} = ∅, F {false} = full, F full = full.
Least fixpoint {true}; with Φ = {false} the wf-induction premise holds. -/
def iF : (Unit → GB) → Unit → GB := fun Φ x w => (Φ x true → Φ x false) ∧ (Φ x false ∨ w = false)
theorem if_t : bi_least_fixpoint iF () true := (lfp_iff ..).2 fun Ψ hΨ => Classical.byContradiction fun hn => by
  by_cases hf : Ψ () false
  · exact hn (hΨ () true ⟨fun _ => hf, .inl hf⟩)
  · exact hf (hΨ () false ⟨fun h => absurd h hn, .inr rfl⟩)
/-- Dual: Fd {false} = full, Fd full = {true}, otherwise empty; greatest fixpoint {false}. -/
def dF : (Unit → GB) → Unit → GB := fun Φ x w => (Φ x false ∧ ¬ Φ x true) ∨ (Φ x false ∧ Φ x true ∧ w = true)
theorem df_t : ¬ bi_greatest_fixpoint dF () true := fun hw => by
  obtain ⟨Ψ, hΨ, hx⟩ := (gfp_iff ..).1 hw
  have h1 : Ψ.f () false ∧ Ψ.f () true := by
    rcases hΨ () true hx with h | h
    · exact absurd hx h.2
    · exact ⟨h.1, h.2.1⟩
  rcases hΨ () false h1.1 with h | h
  · exact h.2 h1.2
  · exact absurd h.2.2 (by decide)
theorem fun_ne_disc {A} [OFE A] (F : (A → GB) → A → GB) : OFE.NonExpansive F :=
  ⟨fun n x y h => by
    have : x = y := funext fun a => h a
    subst this; exact OFE.Dist.rfl⟩
theorem if_f : ¬ bi_least_fixpoint iF () false := fun h => by
  have := (lfp_iff ..).1 h (mkH fun _ z => z = true) (fun y z hz => by
    obtain ⟨h1, _⟩ := hz
    exact absurd (h1 rfl) (by simp [mkH]))
  simp [mkH] at this

theorem own1_sep (a : Bool) (h : (iprop(own1 ∗ own1) : GB) a) : a = false := by
  obtain ⟨b, c, e, hb, hc⟩ := h
  have hb : b = true := hb
  have hc : c = true := hc
  subst hb hc e; rfl
theorem own1_not_frac : ¬ Fractional (fun (_ : Qp) => own1) := fun ⟨h⟩ =>
  Bool.noConfusion (own1_sep true ((h 1 1).1 true rfl))
theorem emp_sep_ev (a : Bool) (h : (iprop(emp ∗ emp) : GB) a) : a = false := by
  obtain ⟨b, c, e, hb, hc⟩ := h
  have hb : b = false := hb
  have hc : c = false := hc
  subst hb hc e; rfl
theorem false_sep_ev {P : GB} (a : Bool) (h : (iprop(False ∗ P) : GB) a) : False := by
  obtain ⟨b, c, e, hb, hc⟩ := h; exact hb
theorem sep_false_ev {P : GB} (a : Bool) (h : (iprop(P ∗ False) : GB) a) : False := by
  obtain ⟨b, c, e, hb, hc⟩ := h; exact hc
theorem true_emp_ev : (iprop(True ∗ emp) : GB) true := ⟨true, false, rfl, trivial, rfl⟩
theorem emp_true_ev : (iprop(emp ∗ True) : GB) true := ⟨false, true, rfl, rfl, trivial⟩
theorem true_true_ev : (iprop(True ∗ True) : GB) true := ⟨true, false, rfl, trivial, trivial⟩
theorem emp_emp_ev : (iprop(emp ∗ emp) : GB) false := ⟨false, false, rfl, rfl, rfl⟩

theorem afE (io1 io2 : ProofMode.InOut) (q : Qp) :
    AsFractional (PROP := GB) iprop(emp) io1 (fun _ => iprop(emp)) io2 q :=
  fractional_as_fractional (Φ := fun _ => iprop(emp)) q

open Iris.Std in
/-- Step-indexed predicates over the Bool-or monoid with exact splitting, downward closed in the step
and resource-blind at step 0. As a BI, emp holds at every resource at step 0 but only at false later,
so emp is not timeless (a non-affine BI with non-timeless emp). -/
structure TP where
  holds : Nat → Bool → Prop
  mono {n n' : Nat} {m : Bool} : holds n m → n' ≤ n → holds n' m
  irr {m m' : Bool} : holds 0 m → holds 0 m'

theorem TP.ext' : {P Q : TP} → (∀ n m, P.holds n m ↔ Q.holds n m) → P = Q
  | ⟨p, _, _⟩, ⟨q, _, _⟩, h => by
    have : p = q := funext fun n => funext fun m => propext (h n m)
    subst this; rfl

def TP.emp : TP where
  holds n m := n = 0 ∨ m = false
  mono h hle := by rcases h with h | h; exact .inl (by omega); exact .inr h
  irr _ := .inl rfl
def TP.pure (φ : Prop) : TP where
  holds _ _ := φ
  mono h _ := h
  irr h := h
def TP.and (P Q : TP) : TP where
  holds n m := P.holds n m ∧ Q.holds n m
  mono h hle := ⟨P.mono h.1 hle, Q.mono h.2 hle⟩
  irr h := ⟨P.irr h.1, Q.irr h.2⟩
def TP.or (P Q : TP) : TP where
  holds n m := P.holds n m ∨ Q.holds n m
  mono h hle := h.elim (fun h => .inl (P.mono h hle)) (fun h => .inr (Q.mono h hle))
  irr h := h.elim (fun h => .inl (P.irr h)) (fun h => .inr (Q.irr h))
def TP.imp (P Q : TP) : TP where
  holds n m := ∀ n', n' ≤ n → P.holds n' m → Q.holds n' m
  mono h hle n'' h'' hp := h n'' (Nat.le_trans h'' hle) hp
  irr h n' hn' hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) (P.irr hp))
def TP.sForall (Ψ : TP → Prop) : TP where
  holds n m := ∀ p, Ψ p → p.holds n m
  mono h hle p hp := p.mono (h p hp) hle
  irr h p hp := p.irr (h p hp)
def TP.sExists (Ψ : TP → Prop) : TP where
  holds n m := ∃ p, Ψ p ∧ p.holds n m
  mono h hle := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.mono h hle⟩
  irr h := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.irr h⟩
def TP.sep (P Q : TP) : TP where
  holds n m := ∃ a b, m = Bool.or a b ∧ P.holds n a ∧ Q.holds n b
  mono h hle := let ⟨a, b, e, hp, hq⟩ := h; ⟨a, b, e, P.mono hp hle, Q.mono hq hle⟩
  irr {_ m'} h := let ⟨_, _, _, hp, hq⟩ := h; ⟨m', false, by cases m' <;> rfl, P.irr hp, Q.irr hq⟩
def TP.wand (P Q : TP) : TP where
  holds n m := ∀ n', n' ≤ n → ∀ b, P.holds n' b → Q.holds n' (Bool.or m b)
  mono h hle n'' h'' b hp := h n'' (Nat.le_trans h'' hle) b hp
  irr h n' hn' b hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) b hp)
def TP.pers (P : TP) : TP where
  holds n _ := P.holds n false
  mono h hle := P.mono h hle
  irr h := h
def TP.later (P : TP) : TP where
  holds n m := match n with | 0 => True | k+1 => P.holds k m
  mono {n n' m} h hle := by
    cases n' with
    | zero => trivial
    | succ k' => cases n with
      | zero => omega
      | succ k => exact P.mono h (by omega)
  irr _ := trivial

instance : BIBase TP where
  Entails P Q := ∀ n m, P.holds n m → Q.holds n m
  emp := TP.emp
  pure := TP.pure
  and := TP.and
  or := TP.or
  imp := TP.imp
  sForall := TP.sForall
  sExists := TP.sExists
  sep := TP.sep
  wand := TP.wand
  persistently := TP.pers
  later := TP.later

instance : COFE TP := COFE.ofDiscrete _

instance tpBI : BI TP where
  entails_refl _ _ h := h
  entails_trans h1 h2 n m h := h2 n m (h1 n m h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ _ h => h, fun _ _ h => h⟩,
    fun ⟨h1, h2⟩ => TP.ext' fun n m => ⟨h1 n m, h2 n m⟩⟩
  and_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
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
    ⟨a, or b c, by rw [e, e', Bool.or_assoc], hp, b, c, rfl, hq, hr⟩
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

theorem tp_emp_not_timeless : ¬ Timeless (emp : TP) := fun ⟨h⟩ => by
  have := h 1 true (.inl rfl)
  rcases this with h1 | h1
  · exact h1
  · rcases h1 with h1 | h1 <;> simp at h1

/-! AF: affine UORA from Probe3 (UPred AF is an affine BI where ownM a is neither persistent nor plain) -/
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


theorem af_not_pers : ¬ Persistent (UPred.ownM AF.a : UPred AF) := fun ⟨h⟩ => by
  have := h 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases this with h1 | h1 <;> cases h1

theorem af_not_plain : ¬ Plain (UPred.ownM AF.a : UPred AF) := fun ⟨h⟩ => by
  have := h 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases this with h1 | h1 <;> cases h1

/-! Fixpoint rows -/

-- `Iris.BIMonoPred.mono_pred` idx 5: necessary, GB, F Φ x = "Φ x empty" is antitone: Φ = False, Ψ = True
theorem w5c3_1 : ¬ drop0% Iris.BIMonoPred.mono_pred 5 := fun h => by
  have := ev2 (@h GB Unit _ _ (fun Φ x _ => ∀ v, ¬ Φ x v) (fun _ _ => False) (fun _ _ => True) (OFE.ne_of_discrete _) (OFE.ne_of_discrete _))
    (fun _ _ h => h.elim) () false (fun _ h => h)
  exact this true trivial

-- `Iris.BIMonoPred.mono_pred` idx 8: necessary, A = TN, F Φ = ⌜¬ NonExpansive Φ⌝ is BIMonoPred; Φ = ind1 (not NE), Ψ = True
theorem w5c3_2 : ¬ drop0% Iris.BIMonoPred.mono_pred 8 := fun h => by
  let F : (TN → GB) → TN → GB := fun Φ _ _ => ¬ OFE.NonExpansive Φ
  have inst : BIMonoPred F := {
    mono_pred := fun {Φ Ψ} hΦ _ => by
      intro _ _ _ _ p hp
      obtain ⟨x, hx⟩ := hp
      subst hx
      intro z hz
      exact absurd hΦ hz
    mono_pred_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩ }
  have := ev2 (@h GB TN _ _ F inst ind1 (fun _ _ => True) ⟨fun _ _ _ _ => OFE.Dist.rfl⟩)
    (fun _ _ _ => trivial) ⟨1⟩ false ind1_not_ne
  exact this ⟨fun _ _ _ _ => OFE.Dist.rfl⟩

-- `Iris.BIMonoPred.mono_pred` idx 9: necessary, A = TN, F Φ = ⌜NonExpansive Φ⌝ is BIMonoPred; Φ = False, Ψ = ind1 (not NE)
theorem w5c3_3 : ¬ drop0% Iris.BIMonoPred.mono_pred 9 := fun h => by
  let F : (TN → GB) → TN → GB := fun Φ _ _ => OFE.NonExpansive Φ
  have inst : BIMonoPred F := {
    mono_pred := fun {Φ Ψ} _ hΨ => by
      intro _ _ _ _ p hp
      obtain ⟨x, hx⟩ := hp
      subst hx
      intro z _
      exact hΨ
    mono_pred_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩ }
  have := ev2 (@h GB TN _ _ F inst (fun _ _ => False) ind1 ⟨fun _ _ _ _ => OFE.Dist.rfl⟩)
    (fun _ _ h => h.elim) ⟨1⟩ false ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  exact ind1_not_ne this

-- `Iris.BIMonoPred.mono_pred_ne` idx 5: necessary, F Φ = ind1 on TN is not non-expansive
theorem w5c3_4 : ¬ drop0% Iris.BIMonoPred.mono_pred_ne 5 := fun h =>
  ind1_not_ne (@h GB TN _ _ (fun _ => ind1) (fun _ _ => True) ⟨fun _ _ _ _ => OFE.Dist.rfl⟩)

-- `Iris.BIMonoPred.mono_pred_ne` idx 7: necessary, F = id (BIMonoPred), Φ = ind1 not non-expansive
theorem w5c3_5 : ¬ drop0% Iris.BIMonoPred.mono_pred_ne 7 := fun h =>
  ind1_not_ne (@h GB TN _ _ (fun Φ => Φ) idMono ind1)

-- `Iris.least_fixpoint_unfold_mp` idx 6: necessary, GB, non-monotone kF with least fixpoint own1, kF own1 = False
theorem w5c3_6 : ¬ drop0% Iris.least_fixpoint_unfold_mp 6 := fun h => by
  have := @h GB Unit _ _ kF () true kf_t
  rcases this with h1 | h1
  · exact h1 kf_t
  · exact kf_f h1

-- `Iris.least_fixpoint_unfold` idx 6: necessary, as for unfold_mp (kF)
theorem w5c3_7 : ¬ drop0% Iris.least_fixpoint_unfold 6 := fun h => by
  have e := @h GB Unit _ _ kF ()
  have : kF (bi_least_fixpoint kF) () true := e ▸ kf_t
  rcases this with h1 | h1
  · exact h1 kf_t
  · exact kf_f h1

-- `Iris.least_fixpoint_unfold_mpr` idx 5: necessary, GB, F S = S, or everything if S is empty: least fixpoint empty, F of it full
theorem w5c3_8 : ¬ drop0% Iris.least_fixpoint_unfold_mpr 5 := fun h => by
  let F : (Unit → GB) → Unit → GB := fun Φ x w => Φ x w ∨ ∀ v, ¬ Φ x v
  have hl : ∀ v, ¬ bi_least_fixpoint F () v := fun v hv => by
    have := (lfp_iff ..).1 hv (mkH fun _ z => z = !v) (fun y z hz => by
      rcases hz with hz | hz
      · exact hz
      · exact absurd rfl (hz (!v)))
    cases v <;> simp [mkH] at this
  exact hl false (@h GB Unit _ _ F () false (Or.inr hl))

-- `Iris.least_fixpoint_absorbing` idx 5: necessary, GB, kF (values constant in the world, so absorbing): least fixpoint own1 not absorbing
theorem w5c3_9 : ¬ drop0% Iris.least_fixpoint_absorbing 5 := fun h => by
  have ⟨ha⟩ := @h GB Unit _ _ kF (fun Φ _ x => ⟨fun _ ⟨_, _, _, _, hb⟩ => hb⟩) ()
  exact kf_f (ha false ⟨true, true, rfl, trivial, kf_t⟩)

-- `Iris.least_fixpoint_absorbing` idx 6: necessary, GB, F = const emp: least fixpoint emp, not absorbing
theorem w5c3_10 : ¬ drop0% Iris.least_fixpoint_absorbing 6 := fun h => by
  have ha := @h GB Unit _ _ (fun _ _ => iprop(emp)) (constMono _) ()
  rw [least_fixpoint_unfold] at ha
  exact gb_emp_not_absorbing ha

-- `Iris.least_fixpoint_persistent_absorbing` idx 5: necessary, GB, kF (values constant in the world): least fixpoint own1 not persistent
theorem w5c3_11 : ¬ drop0% Iris.least_fixpoint_persistent_absorbing 5 := fun h => by
  have ⟨hp⟩ := @h GB Unit _ _ kF (fun Φ _ x => ⟨fun _ ⟨_, _, _, _, hb⟩ => hb⟩)
    (fun Φ _ x => ⟨fun _ hb => hb⟩) ()
  exact kf_f (hp true kf_t)

-- `Iris.least_fixpoint_affine` idx 5: necessary, GB, F = const True: True ⊢ least fixpoint, not affine
theorem w5c3_12 : ¬ drop0% Iris.least_fixpoint_affine 5 := fun h =>
  gb_true_not_emp ((least_fixpoint_unfold_mpr (F := fun (_ : Unit → GB) _ => iprop(True)) (x := ())).trans
    (@h GB Unit _ _ (fun _ _ => iprop(True)) ()).affine)

-- `Iris.least_fixpoint_strong_mono` idx 6: removable, the premise turns every G-prefixpoint into an F-prefixpoint
theorem w5c3_13 : drop% Iris.least_fixpoint_strong_mono 6 := by
  intro PROP A _ _ F G
  iintro #Hmon %x Hx %Φ #HΦ
  iapply Hx
  iintro !> %y Hy
  iapply HΦ
  iapply Hmon $$ Hy

-- `Iris.greatest_fixpoint_strong_mono` idx 6: removable, the premise turns every F-postfixpoint into a G-postfixpoint
theorem w5c3_14 : drop% Iris.greatest_fixpoint_strong_mono 6 := by
  intro PROP A _ _ F G
  iintro #Hmon %x ⟨%Φ, #HΦ, Hx⟩
  iexists Φ
  isplitr
  · iintro !> %y Hy
    iapply Hmon
    iapply HΦ $$ Hy
  · iexact Hx

-- `Iris.least_fixpoint_iter` idx 6: necessary, A = TN, F Φ = ⌜NonExpansive Φ⌝: least fixpoint True, ind1 a non-NE prefixpoint false at 2
theorem w5c3_15 : ¬ drop0% Iris.least_fixpoint_iter 6 := fun h => by
  let F : (TN → GB) → TN → GB := fun Φ _ _ => OFE.NonExpansive Φ
  have hl : bi_least_fixpoint F ⟨2⟩ false := (lfp_iff ..).2 fun Φ hΦ => hΦ _ _ Φ.ne
  have := ev2 (@h GB TN _ _ F ind1) (fun y z hz => absurd hz ind1_not_ne) ⟨2⟩ false hl
  exact absurd (congrArg TN.v this) (by decide)

-- `Iris.greatest_fixpoint_coiter` idx 6: necessary, A = TN, F Φ = ⌜¬ NonExpansive Φ⌝: greatest fixpoint False, ind1 a non-NE postfixpoint
theorem w5c3_16 : ¬ drop0% Iris.greatest_fixpoint_coiter 6 := fun h => by
  let F : (TN → GB) → TN → GB := fun Φ _ _ => ¬ OFE.NonExpansive Φ
  have := ev2 (@h GB TN _ _ F ind1) (fun y z _ => ind1_not_ne) ⟨1⟩ false rfl
  obtain ⟨Φ, hΦ, hx⟩ := (gfp_iff ..).1 this
  exact hΦ _ _ hx Φ.ne

-- `Iris.greatest_fixpoint_unfold_mp` idx 6: necessary, GB, F S = (S not full): greatest fixpoint full, F of it empty
theorem w5c3_17 : ¬ drop0% Iris.greatest_fixpoint_unfold_mp 6 := fun h => by
  let F : (Unit → GB) → Unit → GB := fun Φ x _ => ¬ (Φ x true ∧ Φ x false)
  have hg : ∀ w, bi_greatest_fixpoint F () w := fun w =>
    (gfp_iff ..).2 ⟨mkH fun _ z => z = w, fun y z hz => by cases w <;> simp [mkH, F], rfl⟩
  exact @h GB Unit _ _ F () false (hg false) ⟨hg true, hg false⟩

-- `Iris.greatest_fixpoint_unfold` idx 6: necessary, as for unfold_mp
theorem w5c3_18 : ¬ drop0% Iris.greatest_fixpoint_unfold 6 := fun h => by
  let F : (Unit → GB) → Unit → GB := fun Φ x _ => ¬ (Φ x true ∧ Φ x false)
  have hg : ∀ w, bi_greatest_fixpoint F () w := fun w =>
    (gfp_iff ..).2 ⟨mkH fun _ z => z = w, fun y z hz => by cases w <;> simp [mkH, F], rfl⟩
  have e := @h GB Unit _ _ F ()
  have : F (bi_greatest_fixpoint F) () false := e ▸ hg false
  exact this ⟨hg true, hg false⟩

-- `Iris.greatest_fixpoint_unfold_mpr` idx 6: necessary, GB, F S = (S empty): greatest fixpoint empty, F of it full
theorem w5c3_19 : ¬ drop0% Iris.greatest_fixpoint_unfold_mpr 6 := fun h => by
  let F : (Unit → GB) → Unit → GB := fun Φ x _ => ∀ v, ¬ Φ x v
  have hg : ∀ w, ¬ bi_greatest_fixpoint F () w := fun w hw => by
    obtain ⟨Φ, hΦ, hx⟩ := (gfp_iff ..).1 hw
    exact hΦ _ _ hx w hx
  exact hg false (@h GB Unit _ _ F () false hg)

-- `Iris.greatest_fixpoint_absorbing` idx 5: necessary, GB, F S = (false ∉ S) (constant in the world): greatest fixpoint own1, not absorbing
theorem w5c3_20 : ¬ drop0% Iris.greatest_fixpoint_absorbing 5 := fun h => by
  let F : (Unit → GB) → Unit → GB := fun Φ x _ => ¬ Φ x false
  have ht : bi_greatest_fixpoint F () true :=
    (gfp_iff ..).2 ⟨mkH fun _ z => z = true, fun y z hz => by simp [mkH, F], rfl⟩
  have hf : ¬ bi_greatest_fixpoint F () false := fun hw => by
    obtain ⟨Φ, hΦ, hx⟩ := (gfp_iff ..).1 hw
    exact hΦ _ _ hx hx
  have ⟨ha⟩ := @h GB Unit _ _ F (fun Φ _ x => ⟨fun _ ⟨_, _, _, _, hb⟩ => hb⟩) ()
  exact hf (ha false ⟨true, true, rfl, trivial, ht⟩)

-- `Iris.greatest_fixpoint_absorbing` idx 6: necessary, GB, F = const emp: greatest fixpoint emp, not absorbing
theorem w5c3_21 : ¬ drop0% Iris.greatest_fixpoint_absorbing 6 := fun h => by
  have ha := @h GB Unit _ _ (fun _ _ => iprop(emp)) (constMono _) ()
  rw [greatest_fixpoint_unfold] at ha
  exact gb_emp_not_absorbing ha

-- `Iris.greatest_fixpoint_ne_outer` idx 9: necessary, GB, F1 = const False, F2 = const True: greatest fixpoints False and True
theorem w5c3_22 : ¬ drop0% Iris.greatest_fixpoint_ne_outer 9 := fun h => by
  have e := @h GB Unit _ _ 0 () () (fun _ _ => iprop(False)) (fun _ _ => iprop(True)) trivial
  have e1 : bi_greatest_fixpoint (fun (_ : Unit → GB) _ => iprop(False)) () = iprop(False) :=
    greatest_fixpoint_unfold (F := fun (_ : Unit → GB) _ => iprop(False)) (PROP := GB)
  have e2 : bi_greatest_fixpoint (fun (_ : Unit → GB) _ => iprop(True)) () = iprop(True) :=
    greatest_fixpoint_unfold (F := fun (_ : Unit → GB) _ => iprop(True)) (PROP := GB)
  have e3 : (iprop(False) : GB) = iprop(True) := e1.symm.trans ((e : _ = _).trans e2)
  exact cast (congrFun e3 false).symm trivial

-- `Iris.greatest_fixpoint_ne_outer` idx 10: necessary, A = Bool, F Φ x = ⌜x = true⌝: greatest fixpoints at true and false differ
theorem w5c3_23 : ¬ drop0% Iris.greatest_fixpoint_ne_outer 10 := fun h => by
  letI : OFE Bool := OFE.ofDiscrete Bool
  haveI : OFE.Discrete Bool := ⟨fun h => h⟩
  let F : (Bool → GB) → Bool → GB := fun _ x => iprop(⌜x = true⌝)
  have e := @h GB Bool _ _ 0 true false F F (fun _ _ _ => OFE.Dist.rfl)
  have e1 : ∀ x, bi_greatest_fixpoint (A := Bool) F x = iprop(⌜x = true⌝) := fun x =>
    @greatest_fixpoint_unfold GB Bool _ _ F x (indepMono (fun x => iprop(⌜x = true⌝)))
  have e3 := (e1 true).symm.trans ((e : _ = _).trans (e1 false))
  exact absurd (cast (congrFun e3 false) (rfl : true = true) : false = true) (by decide)

-- `Iris.least_fixpoint_ind_wf` idx 5: necessary, GB, non-monotone iF (least fixpoint own1), Φ = emp; the inner least fixpoint is empty
theorem w5c3_24 : ¬ drop0% Iris.least_fixpoint_ind_wf 5 := fun h => by
  let Φ : Unit → GB := fun _ w => w = false
  have hL : ∀ v, ¬ bi_least_fixpoint (fun Ψ a => iprop(Φ a ∧ iF Ψ a)) () v := fun v hv => by
    cases v
    · have := (lfp_iff ..).1 hv (mkH fun _ z => z = true) (fun y z hz => by
        obtain ⟨_, h1, _⟩ := hz
        exact absurd (h1 rfl) (by simp [mkH]))
      simp [mkH] at this
    · have := (lfp_iff ..).1 hv (mkH fun _ z => z = false) (fun y z hz => hz.1)
      simp [mkH] at this
  have := ev2 (@h GB Unit _ _ iF Φ (OFE.ne_of_discrete _))
    (fun y z hz => by
      obtain ⟨_, h2⟩ := hz
      rcases h2 with h2 | h2
      · exact absurd h2 (hL false)
      · exact h2) () true if_t
  exact absurd this (by decide)

-- `Iris.least_fixpoint_ind` idx 5: necessary, GB, non-monotone iF (least fixpoint own1), Φ = emp
theorem w5c3_25 : ¬ drop0% Iris.least_fixpoint_ind 5 := fun h => by
  let Φ : Unit → GB := fun _ w => w = false
  have := ev2 (@h GB Unit _ _ iF Φ (OFE.ne_of_discrete _))
    (fun y z hz => by
      obtain ⟨h1, h2⟩ := hz
      rcases h2 with h2 | h2
      · exact absurd h2.2 (by cases y; exact if_f)
      · exact h2) () true if_t
  exact absurd this (by decide)

-- `Iris.greatest_fixpoint_paco` idx 5: necessary, GB, non-monotone dF (greatest fixpoint emp), Φ = own1; the inner greatest fixpoint is full
theorem w5c3_26 : ¬ drop0% Iris.greatest_fixpoint_paco 5 := fun h => by
  let Φ : Unit → GB := fun _ w => w = true
  have hG : ∀ v, bi_greatest_fixpoint (fun Ψ a => iprop(Φ a ∨ dF Ψ a)) () v := fun v => by
    cases v
    · exact (gfp_iff ..).2 ⟨mkH fun _ z => z = false, fun y z hz => by
        subst hz; exact .inr (.inl ⟨rfl, by simp [mkH]⟩), rfl⟩
    · exact (gfp_iff ..).2 ⟨mkH fun _ z => z = true, fun y z hz => .inl hz, rfl⟩
  have := ev2 (@h GB Unit _ _ dF Φ (OFE.ne_of_discrete _))
    (fun y z hz => by
      subst hz; exact .inr ⟨hG false, hG true, rfl⟩) () true rfl
  exact df_t this

-- `Iris.greatest_fixpoint_coind` idx 5: necessary, GB, non-monotone dF (greatest fixpoint emp), Φ = own1
theorem w5c3_27 : ¬ drop0% Iris.greatest_fixpoint_coind 5 := fun h => by
  let Φ : Unit → GB := fun _ w => w = true
  have hf : bi_greatest_fixpoint dF () false :=
    (gfp_iff ..).2 ⟨mkH fun _ z => z = false, fun y z hz => by
        subst hz; exact .inl ⟨rfl, by simp [mkH]⟩, rfl⟩
  have := ev2 (@h GB Unit _ _ dF Φ (OFE.ne_of_discrete _) (fun_ne_disc _))
    (fun y z hz => by
      subst hz; exact .inr ⟨.inr hf, .inl rfl, rfl⟩) () true rfl
  exact df_t this

-- `Iris.wf_pred_mono` idx 5: necessary, GB, F antitone (F Φ = "Φ empty"), Φ = True: True ∧ F Ψ not monotone
theorem w5c3_28 : ¬ drop0% Iris.wf_pred_mono 5 := fun h => by
  have inst := @h GB Unit _ _ (fun Φ x _ => ∀ v, ¬ Φ x v) (fun _ => iprop(True)) (OFE.ne_of_discrete _)
  have := ev2 (@BIMonoPred.mono_pred GB Unit _ _ _ inst (fun _ _ => False) (fun _ _ => True)
    (OFE.ne_of_discrete _) (OFE.ne_of_discrete _)) (fun _ _ h => h.elim) () false ⟨trivial, fun _ h => h⟩
  exact this.2 true trivial

-- `Iris.wf_pred_mono` idx 7: necessary, A = TN, F = const True, Φ = ind1: ind1 ∧ True is not non-expansive
theorem w5c3_29 : ¬ drop0% Iris.wf_pred_mono 7 := fun h => by
  have inst := @h GB TN _ _ (fun _ _ => iprop(True)) (constMono _) ind1
  have hne := @BIMonoPred.mono_pred_ne GB TN _ _ _ inst (fun _ _ => True) ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  have := congrFun (hne.ne tn12) false
  have h2 : (ind1 ⟨1⟩ false ∧ True) := ⟨rfl, trivial⟩
  have h3 : (ind1 ⟨2⟩ false ∧ True) := cast (congrArg id this) h2
  exact absurd (congrArg TN.v h3.1) (by decide)

-- `Iris.paco_mono` idx 5: necessary, GB, F antitone, Φ = False: False ∨ F Ψ not monotone
theorem w5c3_30 : ¬ drop0% Iris.paco_mono 5 := fun h => by
  have inst := @h GB Unit _ _ (fun Φ x _ => ∀ v, ¬ Φ x v) (fun _ => iprop(False)) (OFE.ne_of_discrete _)
  have := ev2 (@BIMonoPred.mono_pred GB Unit _ _ _ inst (fun _ _ => False) (fun _ _ => True)
    (OFE.ne_of_discrete _) (OFE.ne_of_discrete _)) (fun _ _ h => h.elim) () false (.inr fun _ h => h)
  rcases this with h1 | h1
  · exact h1
  · exact h1 true trivial

-- `Iris.paco_mono` idx 7: necessary, A = TN, F = const False, Φ = ind1: ind1 ∨ False is not non-expansive
theorem w5c3_31 : ¬ drop0% Iris.paco_mono 7 := fun h => by
  have inst := @h GB TN _ _ (fun _ _ => iprop(False)) (constMono _) ind1
  have hne := @BIMonoPred.mono_pred_ne GB TN _ _ _ inst (fun _ _ => True) ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  have := congrFun (hne.ne tn12) false
  have h2 : (ind1 ⟨1⟩ false ∨ False) := .inl rfl
  have h3 : (ind1 ⟨2⟩ false ∨ False) := cast (congrArg id this) h2
  rcases h3 with h3 | h3
  · exact absurd (congrArg TN.v h3) (by decide)
  · exact h3

/-! FixpointBanach rows -/

theorem fix_const {A} (P : A → GB) : fixpoint (fun (_ : A → GB) => P) = P := (fixpointP _).property

-- `Iris.fixpoint_persistent` idx 5: necessary, GB, F = const own1 (contractive), fixpoint own1 not persistent
theorem w5c3_32 : ¬ drop0% Iris.fixpoint_persistent 5 := fun h => by
  have := @h GB _ Unit (fun _ _ => own1) _ ()
  rw [fix_const] at this
  exact gb_own1_not_pers this

-- `Iris.fixpoint_absorbing` idx 5: necessary, GB, F = const emp, fixpoint emp not absorbing
theorem w5c3_33 : ¬ drop0% Iris.fixpoint_absorbing 5 := fun h => by
  have := @h GB _ Unit (fun _ _ => iprop(emp)) _ ()
  rw [fix_const] at this
  exact gb_emp_not_absorbing this

-- `Iris.fixpoint_affine` idx 5: necessary, GB, F = const True, fixpoint True not affine
theorem w5c3_34 : ¬ drop0% Iris.fixpoint_affine 5 := fun h => by
  have := @h GB _ Unit (fun _ _ => iprop(True)) _ ()
  rw [fix_const] at this
  exact gb_true_not_affine this

-- `Iris.fixpoint_persistent_absorbing` idx 5: necessary, GB, F = const own1, fixpoint own1 not persistent
theorem w5c3_35 : ¬ drop0% Iris.fixpoint_persistent_absorbing 5 := fun h => by
  have := (@h GB _ Unit (fun _ _ => own1) _ ()).1
  rw [fix_const] at this
  exact gb_own1_not_pers this

-- `Iris.fixpoint_persistent_affine` idx 5: necessary, GB, F = const own1, fixpoint own1 not persistent
theorem w5c3_36 : ¬ drop0% Iris.fixpoint_persistent_affine 5 := fun h => by
  have := (@h GB _ Unit (fun _ _ => own1) _ ()).1
  rw [fix_const] at this
  exact gb_own1_not_pers this

theorem id_not_contr : ¬ OFE.Contractive (fun Φ : Unit → GB => Φ) := fun hc => by
  have := @OFE.Contractive.zero _ _ _ _ (fun Φ : Unit → GB => Φ) hc (fun _ _ => False) (fun _ _ => True) ()
  exact cast (congrFun this false).symm trivial

theorem id_not_contr_si : ¬ OFE.Contractive (fun Φ : Unit → SiProp => Φ) := fun hc => by
  have := @OFE.Contractive.zero _ _ _ _ (fun Φ : Unit → SiProp => Φ) hc (fun _ => iprop(False)) (fun _ => iprop(True)) ()
  exact (this (Nat.le_refl 0)).2 trivial

-- `Iris.fixpoint_persistent` idx 4: necessary (dependent), GB, F = id preserves everything and is not contractive
theorem w5c3_37 : ¬ indep0% Iris.fixpoint_persistent 4 := fun h =>
  id_not_contr (@h GB _ Unit (fun Φ => Φ) (fun _ h => h) ())

-- `Iris.fixpoint_absorbing` idx 4: necessary (dependent), GB, F = id not contractive
theorem w5c3_38 : ¬ indep0% Iris.fixpoint_absorbing 4 := fun h =>
  id_not_contr (@h GB _ Unit (fun Φ => Φ) (fun _ h => h) ())

-- `Iris.fixpoint_affine` idx 4: necessary (dependent), GB, F = id not contractive
theorem w5c3_39 : ¬ indep0% Iris.fixpoint_affine 4 := fun h =>
  id_not_contr (@h GB _ Unit (fun Φ => Φ) (fun _ h => h) ())

-- `Iris.fixpoint_persistent_absorbing` idx 4: necessary (dependent), GB, F = id not contractive
theorem w5c3_40 : ¬ indep0% Iris.fixpoint_persistent_absorbing 4 := fun h =>
  id_not_contr (@h GB _ Unit (fun Φ => Φ) (fun _ h1 h2 x => ⟨h1 x, h2 x⟩) ())

-- `Iris.fixpoint_persistent_affine` idx 4: necessary (dependent), GB, F = id not contractive
theorem w5c3_41 : ¬ indep0% Iris.fixpoint_persistent_affine 4 := fun h =>
  id_not_contr (@h GB _ Unit (fun Φ => Φ) (fun _ h1 h2 x => ⟨h1 x, h2 x⟩) ())

-- `Iris.fixpoint_plain` idx 4: necessary (dependent), SiProp, F = id not contractive
theorem w5c3_42 : ¬ indep0% Iris.fixpoint_plain 4 := fun h =>
  id_not_contr_si (@h SiProp _ Unit (fun Φ => Φ) (fun _ h => h) ())

-- `Iris.fixpoint_plain_absorbing` idx 4: necessary (dependent), SiProp, F = id not contractive
theorem w5c3_43 : ¬ indep0% Iris.fixpoint_plain_absorbing 4 := fun h =>
  id_not_contr_si (@h SiProp _ Unit (fun Φ => Φ) (fun _ h1 h2 x => ⟨h1 x, h2 x⟩) ())

-- `Iris.fixpoint_plain_affine` idx 4: necessary (dependent), SiProp, F = id not contractive
theorem w5c3_44 : ¬ indep0% Iris.fixpoint_plain_affine 4 := fun h =>
  id_not_contr_si (@h SiProp _ Unit (fun Φ => Φ) (fun _ h1 h2 x => ⟨h1 x, h2 x⟩) ())

/-! Fractional rows (GB: own1 ∗ own1 = emp, so const own1 is not fractional; const emp is) -/

-- `Iris.Fractional.fractional` idx 3: necessary, GB, Φ = const own1 not fractional
theorem w5c3_45 : ¬ drop0% Iris.Fractional.fractional 3 := fun h =>
  Bool.noConfusion (own1_sep true ((@h GB _ (fun _ => own1) 1 1).1 true rfl))

-- `Iris.AsFractional.as_fractional_fractional` idx 7: necessary, GB, Φ = const own1 not fractional
theorem w5c3_46 : ¬ drop0% Iris.AsFractional.as_fractional_fractional 7 := fun h =>
  own1_not_frac (@h GB _ own1 .in (fun _ => own1) .in 1)

-- `Iris.fractional_as_fractional` idx 5: necessary, GB, Φ = const own1 not fractional
theorem w5c3_47 : ¬ drop0% Iris.fractional_as_fractional 5 := fun h =>
  own1_not_frac (@h GB _ (fun _ => own1) .in .in 1).as_fractional_fractional

-- `Iris.fractional_split` idx 11: necessary, GB, Φ = const emp, P1 = False: emp ⊣⊢ False ∗ emp fails
theorem w5c3_48 : ¬ drop0% Iris.fractional_split 11 := fun h =>
  false_sep_ev false ((@h GB _ iprop(emp) iprop(False) iprop(emp) (fun _ => iprop(emp)) 1 1 .in .in
    (afE .in .in _) (afE .in .in _)).1 false rfl)

-- `Iris.fractional_split` idx 12: necessary, GB, Φ = const emp, P2 = False
theorem w5c3_49 : ¬ drop0% Iris.fractional_split 12 := fun h =>
  sep_false_ev false ((@h GB _ iprop(emp) iprop(emp) iprop(False) (fun _ => iprop(emp)) 1 1 .in .in
    (afE .in .in _) (afE .in .in _)).1 false rfl)

-- `Iris.fractional_half` idx 8: necessary, GB, Φ = const emp, P = False: False ⊣⊢ emp ∗ emp fails
theorem w5c3_50 : ¬ drop0% Iris.fractional_half 8 := fun h =>
  (@h GB _ iprop(False) iprop(emp) (fun _ => iprop(emp)) 1 .in .in
    (afE .in .in _)).2 false emp_emp_ev

-- `Iris.fractional_half` idx 9: necessary, GB, Φ = const emp, P1 = False
theorem w5c3_51 : ¬ drop0% Iris.fractional_half 9 := fun h =>
  false_sep_ev false ((@h GB _ iprop(emp) iprop(False) (fun _ => iprop(emp)) 1 .in .in
    (afE .in .in _)).1 false rfl)

-- `Iris.fractional_merge` idx 9: removable, Fractional Φ is a field of the kept AsFractional instance hP1
theorem w5c3_52 : drop% Iris.fractional_merge 9 := by
  intro PROP _ P1 P2 Φ q1 q2 ioΦ ioq hP1 hP2
  haveI := hP1.as_fractional_fractional
  exact fractional_merge (hP1 := hP1) (hP2 := hP2)

-- `Iris.fractional_merge` idx 10: necessary, GB, Φ = const emp, P1 = True: True ∗ emp ⊬ emp
theorem w5c3_53 : ¬ drop0% Iris.fractional_merge 10 := fun h =>
  Bool.noConfusion (@h GB _ iprop(True) iprop(emp) (fun _ => iprop(emp)) 1 1 .in .in _
    (afE .in .in _) true true_emp_ev)

-- `Iris.fractional_merge` idx 11: necessary, GB, Φ = const emp, P2 = True
theorem w5c3_54 : ¬ drop0% Iris.fractional_merge 11 := fun h =>
  Bool.noConfusion (@h GB _ iprop(emp) iprop(True) (fun _ => iprop(emp)) 1 1 .in .in _
    (afE .in .in _) true emp_true_ev)

-- `Iris.intoSepFractional` idx 6: necessary, GB, P = True, Φ = const emp: True ⊬ emp ∗ emp
theorem w5c3_55 : ¬ drop0% Iris.intoSepFractional 6 := fun h =>
  Bool.noConfusion (emp_sep_ev true ((@h GB _ iprop(True) (fun _ => iprop(emp)) 1 1).into_sep true trivial))

-- `Iris.fromSepFractionalHalf` idx 5: necessary, GB, P = False, Φ = const emp
theorem w5c3_56 : ¬ drop0% Iris.fromSepFractionalHalf 5 := fun h =>
  (@h GB _ iprop(False) (fun _ => iprop(emp)) 1).from_sep false emp_emp_ev

-- `Iris.intoSepFractionalHalf` idx 5: necessary, GB, P = True, Φ = const emp
theorem w5c3_57 : ¬ drop0% Iris.intoSepFractionalHalf 5 := fun h =>
  Bool.noConfusion (emp_sep_ev true ((@h GB _ iprop(True) (fun _ => iprop(emp)) 1).into_sep true trivial))

-- `Iris.combineSepAsFractional` idx 7: necessary, GB, P1 = True, P2 = emp, Φ = const emp
theorem w5c3_58 : ¬ drop0% Iris.combineSepAsFractional 7 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) iprop(emp) (fun _ => iprop(emp)) 1 1
    (afE .in .out _)).combine_sep_as true true_emp_ev)

-- `Iris.combineSepAsFractionalHalf` idx 5: necessary, GB, P = True, Φ = const emp
theorem w5c3_59 : ¬ drop0% Iris.combineSepAsFractionalHalf 5 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) (fun _ => iprop(emp)) 1).combine_sep_as true true_true_ev)

-- `Iris.fractional_sep` idx 4: necessary, GB, Φ = const own1, Ψ = const emp: own1 ∗ emp = own1 not fractional
theorem w5c3_60 : ¬ drop0% Iris.fractional_sep 4 := fun h => by
  have := @h GB _ (fun _ => own1) (fun _ => iprop(emp)) _
  have e : (fun (_ : Qp) => (iprop(own1 ∗ emp) : GB)) = fun _ => own1 := funext fun _ => BI.BiEntails.to_eq sep_emp
  rw [e] at this
  exact own1_not_frac this

-- `Iris.fractional_sep` idx 5: necessary, GB, Φ = const emp, Ψ = const own1
theorem w5c3_61 : ¬ drop0% Iris.fractional_sep 5 := fun h => by
  have := @h GB _ (fun _ => iprop(emp)) (fun _ => own1) _
  have e : (fun (_ : Qp) => (iprop(emp ∗ own1) : GB)) = fun _ => own1 := funext fun _ => BI.BiEntails.to_eq emp_sep
  rw [e] at this
  exact own1_not_frac this

-- `Iris.fractional_bigSepL` idx 5: necessary, GB, l = [()], Ψ = const own1: the big sep is own1
theorem w5c3_62 : ¬ drop0% Iris.fractional_bigSepL 5 := fun h => by
  have := @h GB _ Unit [()] (fun _ _ _ => own1)
  have e : (fun (q : Qp) => (iprop([∗list] k ↦ x ∈ [()], (fun _ _ _ => own1 : Nat → Unit → Qp → GB) k x q) : GB)) = fun _ => own1 :=
    funext fun _ => BI.BiEntails.to_eq BI.BigSepL.bigSepL_singleton
  exact own1_not_frac (e ▸ this)

-- `Iris.fractional_divide_equal` idx 3: necessary, GB, Φ = const own1, n = 1: own1 ⊬ own1 ∗ own1 ∗ emp
theorem w5c3_63 : ¬ drop0% Iris.fractional_divide_equal 3 := fun h => by
  have := @h GB _ (fun _ => own1) 1 1 true rfl
  obtain ⟨a, b, e, ha, c, d, e2, hc, hd⟩ := this
  have ha : a = true := ha
  have hc : c = true := hc
  have hd : d = false := hd
  subst ha hc hd e2
  exact Bool.noConfusion e

-- `Iris.fractional_internalFractional` idx 3: necessary, GB, Φ = const own1
theorem w5c3_64 : ¬ drop0% Iris.fractional_internalFractional 3 := fun h => by
  have := (@h GB _ (fun _ => own1)) false rfl
  have h2 := this.2 _ ⟨1, rfl⟩ _ ⟨1, rfl⟩
  have h3 := h2.1 true rfl
  exact Bool.noConfusion (own1_sep _ h3)

-- `Iris.frame_fractional` idx 9: necessary, GB, Φ = const emp, R = True, p = false: True ∗ emp ⊬ emp
theorem w5c3_65 : ¬ drop0% Iris.frame_fractional 9 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp) (fun _ => iprop(emp)) 1 (1 + 1) 1 false iprop(True)
    (afE .in .in _) ⟨rfl⟩).frame true true_emp_ev)

-- `Iris.frame_fractional` idx 10: necessary, GB, Φ = const emp, R = emp, P = False
theorem w5c3_66 : ¬ drop0% Iris.frame_fractional 10 := fun h =>
  (@h GB _ iprop(False) (fun _ => iprop(emp)) 1 (1 + 1) 1 false iprop(emp)
    (afE .in .in _) ⟨rfl⟩).frame false emp_emp_ev

/-! Laterable rows -/

-- `Iris.IntoLaterable.into_laterable` idx 4: necessary, GB, P = True, Q = False
theorem w5c3_67 : ¬ drop0% Iris.IntoLaterable.into_laterable 4 := fun h => by
  have h1 := @h GB _ iprop(True) iprop(False)
  exact h1 false trivial

-- `Iris.make_laterable_mono` idx 4: necessary, GB (later = id, everything timeless): emp ⊢ make_laterable emp ⊢ make_laterable False ⊢ ◇ False
theorem w5c3_68 : ¬ drop0% Iris.make_laterable_mono 4 := fun h => by
  haveI : Timeless (iprop(emp) : GB) := ⟨fun _ h => .inr h⟩
  have := ((make_laterable_intro' (Q := (iprop(emp) : GB))).trans
    ((@h GB _ iprop(emp) iprop(False)).trans make_laterable_elim)) false rfl
  rcases this with h1 | h1
  · exact h1
  · exact h1

-- `Iris.fromModal_make_laterable` idx 2: necessary (dependent), BI TP where emp is not timeless
theorem w5c3_69 : ¬ indep0% Iris.fromModal_make_laterable 2 := fun h =>
  tp_emp_not_timeless (@h TP _ .in iprop(emp))

-- `Iris.fractional_bigSepL_replicate` idx 3: necessary, GB, Φ = const own1, r = 1, k = 1, q = 1 + 1: own1 ⊬ own1 ∗ own1 ∗ emp
theorem w5c3_70 : ¬ drop0% Iris.fractional_bigSepL_replicate 3 := fun h => by
  have := @h GB _ (fun _ => own1) 1 1 (1 + 1) (by grind) true rfl
  obtain ⟨a, b, e, ha, c, d, e2, hc, hd⟩ := this
  have ha : a = true := ha
  have hc : c = true := hc
  have hd : d = false := hd
  subst ha hc hd e2
  exact Bool.noConfusion e

/-! InvHeap map rows (H = Std.ExtTreeMap Nat · compare, V = Unit) -/

abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare

-- `Iris.get?_toInvHeap_none` idx 6: necessary, h = {[0 := ((), True)]}: toInvHeap h has an entry at 0
theorem w5c3_71 : ¬ drop0% Iris.get?_toInvHeap_none 6 := fun h => by
  have h1 := @h Nat Unit TM _ (Iris.Std.PartialMap.insert ∅ 0 ((), fun _ => True)) 0
  rw [get?_heap_some_toInvHeap (Iris.Std.LawfulPartialMap.get?_insert_eq rfl)] at h1
  cases h1

-- `Iris.get?_heap_some_toInvHeap` idx 8: necessary, h = ∅: toInvHeap ∅ has no entry
theorem w5c3_72 : ¬ drop0% Iris.get?_heap_some_toInvHeap 8 := fun h => by
  have h1 := @h Nat Unit TM _ ∅ 0 () (fun _ => True)
  rw [get?_toInvHeap_none (Iris.Std.LawfulPartialMap.get?_empty 0)] at h1
  cases h1

-- `Iris.get?_toInvHeap_some` idx 8: necessary, h = ∅: get? ∅ 0 = none
theorem w5c3_73 : ¬ drop0% Iris.get?_toInvHeap_some 8 := fun h => by
  obtain ⟨_, _, _, _, h1⟩ := @h Nat Unit TM _ ∅ 0 none (toAgree ⟨fun _ => True⟩)
  rw [Iris.Std.LawfulPartialMap.get?_empty] at h1
  cases h1

-- `_private.Iris.BI.Lib.InvHeap.0.Iris.singleton_inc_toInvHeap` idx 8: necessary, h = ∅: get? ∅ 0 = none
theorem w5c3_74 : ¬ drop0% _private.Iris.BI.Lib.InvHeap.«0».Iris.singleton_inc_toInvHeap 8 := fun h => by
  obtain ⟨_, h1, _⟩ := @h Nat Unit TM _ ∅ 0 (fun _ => True) none
  rw [Iris.Std.LawfulPartialMap.get?_empty] at h1
  cases h1

-- `Iris.least_fixpoint_persistent_affine` idx 7: necessary, affine BI UPred AF, F = const (ownM a) (monotone): least fixpoint ownM a not persistent
theorem w5c3_75 : ¬ drop0% Iris.least_fixpoint_persistent_affine 7 := fun h => by
  have hp := @h (UPred AF) Unit _ _ (fun _ _ => UPred.ownM AF.a) (constMono _) (fun _ _ _ => inferInstance) ()
  rw [least_fixpoint_unfold] at hp
  exact af_not_pers hp

-- `Iris.least_fixpoint_persistent_absorbing` idx 7: necessary, affine BI UPred AF, F = const (ownM a): least fixpoint ownM a not persistent
theorem w5c3_76 : ¬ drop0% Iris.least_fixpoint_persistent_absorbing 7 := fun h => by
  have hp := @h (UPred AF) Unit _ _ (fun _ _ => UPred.ownM AF.a) (constMono _) (fun _ _ _ => inferInstance) ()
  rw [least_fixpoint_unfold] at hp
  exact af_not_pers hp


theorem fixP_eq {α} {c : COFE α} {i : Inhabited α} {f : α → α} {hf : OFE.Contractive f} :
    @fixpoint α c i f hf = f (@fixpoint α c i f hf) := (@fixpointP α c i f hf).property

-- `Iris.fixpoint_plain` idx 5: necessary, Sbi UPred AF, F = const (ownM a) (contractive): fixpoint ownM a not plain
theorem w5c3_77 : ¬ drop0% Iris.fixpoint_plain 5 := fun h => by
  have := @h (UPred AF) _ Unit (fun _ _ => UPred.ownM AF.a) _ ()
  rw [fixP_eq] at this
  exact af_not_plain this

-- `Iris.fixpoint_plain_absorbing` idx 5: necessary, Sbi UPred AF, F = const (ownM a): fixpoint ownM a not plain
theorem w5c3_78 : ¬ drop0% Iris.fixpoint_plain_absorbing 5 := fun h => by
  have := (@h (UPred AF) _ Unit (fun _ _ => UPred.ownM AF.a) _ ()).1
  rw [fixP_eq] at this
  exact af_not_plain this

-- `Iris.fixpoint_plain_affine` idx 5: necessary, Sbi UPred AF, F = const (ownM a): fixpoint ownM a not plain
theorem w5c3_79 : ¬ drop0% Iris.fixpoint_plain_affine 5 := fun h => by
  have := (@h (UPred AF) _ Unit (fun _ _ => UPred.ownM AF.a) _ ()).1
  rw [fixP_eq] at this
  exact af_not_plain this

/-- Finite sets of Bool as characteristic functions (copied from Probe4). -/
def BS := Bool → Bool

instance : Iris.Std.Set BS Bool where
  mem X x := X x = true
  singleton y := fun x => x == y
  union X Y := fun x => or (X x) (Y x)
  inter X Y := fun x => and (X x) (Y x)
  sdiff X Y := fun x => and (X x) (not (Y x))
  emptyCollection := fun _ => false

def bsList (X : BS) : List Bool := (if X false then [false] else []) ++ (if X true then [true] else [])

instance bsLFS : Iris.Std.LawfulFiniteSet BS Bool where
  ext {X Y} h := funext fun x => by
    have := h x; cases hx : X x <;> cases hy : Y x <;> simp_all [Membership.mem]
  mem_empty := by intro x h; cases h
  mem_singleton := by intro x y; show (x == y) = true ↔ x = y; simp
  mem_union := by intro X Y x; show (or (X x) (Y x)) = true ↔ X x = true ∨ Y x = true; simp
  mem_inter := by intro X Y x; show (and (X x) (Y x)) = true ↔ X x = true ∧ Y x = true; simp
  mem_diff := by intro X Y x; show (and (X x) (not (Y x))) = true ↔ X x = true ∧ ¬ Y x = true; simp
  toList := bsList
  mem_toList := by
    intro m k; show k ∈ bsList m ↔ m k = true
    cases hf : m false <;> cases ht : m true <;> cases k <;> simp [bsList, hf, ht]
  toList_nodup := by
    intro m; cases hf : m false <;> cases ht : m true <;> simp [bsList, hf, ht]


abbrev UIdx : Iris.BI.BiIndex := { car := Nat, rel := inferInstance }

-- `Iris.fractional_embed` idx 6: necessary, embedding GB into MonPred UIdx GB, Φ = const own1: at index 0 own1 ⊬ own1 ∗ own1
theorem w5c3_80 : ¬ drop0% Iris.fractional_embed 6 := fun h =>
  Bool.noConfusion (own1_sep true ((@h GB _ (fun _ => own1) (MonPred UIdx GB) _ _).fractional 1 1 |>.1 (0 : Nat) true rfl))

-- `Iris.as_fractional_embed` idx 10: necessary, embedding GB into MonPred UIdx GB, P = False, Φ = const emp: ⎡False⎤ ⊣⊢ ⎡emp⎤ fails
theorem w5c3_81 : ¬ drop0% Iris.as_fractional_embed 10 := fun h =>
  (@h GB _ iprop(False) (fun _ => iprop(emp)) 1 .in .in (MonPred UIdx GB) _ _).as_fractional.2 (0 : Nat) false rfl

-- `Iris.fractional_bigSepM` idx 8: necessary, GB, m = {[0 := ()]} in ExtTreeMap, Ψ = const own1: the big sep is own1
theorem w5c3_82 : ¬ drop0% Iris.fractional_bigSepM 8 := fun h => by
  have := @h GB _ Nat Unit TM _ (Iris.Std.PartialMap.singleton 0 ()) (fun _ _ _ => own1)
  have e : (fun (q : Qp) => (iprop([∗map] k ↦ x ∈ (Iris.Std.PartialMap.singleton 0 () : TM Unit), (fun _ _ _ => own1 : Nat → Unit → Qp → GB) k x q) : GB)) = fun _ => own1 :=
    funext fun _ => BI.BiEntails.to_eq BI.BigSepM.bigSepM_singleton
  exact own1_not_frac (e ▸ this)

-- `Iris.fractional_bigSepS` idx 7: necessary, GB, X = {true} in Bool sets, Ψ = const own1: the big sep is own1
theorem w5c3_83 : ¬ drop0% Iris.fractional_bigSepS 7 := fun h => by
  have := @h GB _ BS Bool _ ({true} : BS) (fun _ _ => own1)
  have e : (fun (q : Qp) => (iprop([∗set] x ∈ ({true} : BS), (fun _ _ => own1 : Bool → Qp → GB) x q) : GB)) = fun _ => own1 :=
    funext fun _ => BI.BiEntails.to_eq BI.BigSepS.bigSepS_singleton
  exact own1_not_frac (e ▸ this)

-- `Iris.fractional_bigSepMS` idx 7: necessary, GB, X = {0} in Iris.Std.ListPerm Nat, Ψ = const own1: the big sep is own1
theorem w5c3_84 : ¬ drop0% Iris.fractional_bigSepMS 7 := fun h => by
  have := @h GB _ (Iris.Std.ListPerm Nat) Nat _ ({0} : Iris.Std.ListPerm Nat) (fun _ _ => own1)
  have e : (fun (q : Qp) => (iprop([∗mset] x ∈ ({0} : Iris.Std.ListPerm Nat), (fun _ _ => own1 : Nat → Qp → GB) x q) : GB)) = fun _ => own1 :=
    funext fun _ => BI.BiEntails.to_eq (BI.BigSepMS.bigSepMS_singleton (MS := Iris.Std.ListPerm Nat))
  exact own1_not_frac (e ▸ this)

/-- In UPred AF: F Φ = ⌜Φ ≠ const (ownM a)⌝ (pure, so persistent; not monotone). Its prefixpoints are const (ownM a) and True. -/
abbrev pF : (Unit → UPred AF) → Unit → UPred AF := fun Φ _ => iprop(⌜Φ ≠ fun _ => UPred.ownM AF.a⌝)

theorem pf_lfp_le : bi_least_fixpoint pF () ⊢ UPred.ownM AF.a := by
  iintro H
  ispecialize H $$ %(OFE.Hom.mk (fun (_ : Unit) => UPred.ownM AF.a) (OFE.ne_of_discrete _))
  iapply H
  iintro !> %y %hy
  exact absurd rfl hy

theorem pf_le_lfp : UPred.ownM AF.a ⊢ bi_least_fixpoint pF () := by
  iintro Ha %Φ #HΦ
  by_cases e : Φ.f = fun _ => UPred.ownM AF.a
  · rw [e]
    iexact Ha
  · iapply HΦ
    ipureintro
    exact e

-- `Iris.least_fixpoint_persistent_affine` idx 5: necessary, affine BI UPred AF, non-monotone pure F Φ = ⌜Φ ≠ const (ownM a)⌝: least fixpoint ownM a not persistent
theorem w5c3_85 : ¬ drop0% Iris.least_fixpoint_persistent_affine 5 := fun h => by
  have hp := @h (UPred AF) Unit _ _ pF (fun _ _ _ => inferInstance) (fun _ _ _ => BI.pure_persistent _) ()
  exact af_not_pers ⟨pf_le_lfp.trans (hp.persistent.trans (persistently_mono pf_lfp_le))⟩

/-! UPred (Option Qp): Φ q = ownM (some q) is fractional (ownM_op) and not constant -/

abbrev OQ := Option Qp
abbrev fQ : Qp → UPred OQ := fun q => UPred.ownM (some q : OQ)
instance fQ_frac : Fractional fQ := ⟨fun p q => UPred.ownM_op (some p : OQ) (some q)⟩
theorem one_valid : ✓{0} (some (1 : Qp) : OQ) := (Qp.validN_iff (n := 0) (x := 1)).2 (by decide)
theorem fQ_bad {q : Qp} (hq : ¬ q.val ≤ 1) (h : fQ 1 ⊢ fQ q) : False := by
  have := h 0 ⟨some 1, one_valid⟩ (ORA.ordN_refl _)
  exact hq (this.validN one_valid)

-- `Iris.fractional_bigSepL_replicate` idx 7: necessary, UPred (Option Qp), Φ q = ownM (some q), k = 0, q = 1, r = 1 + 1: ownM 1 ⊬ ownM 2 (invalid)
theorem w5c3_86 : ¬ drop0% Iris.fractional_bigSepL_replicate 7 := fun h =>
  fQ_bad (q := 1 + 1) (by simp; grind)
    ((@h (UPred OQ) _ fQ _ (1 + 1) 0 1).trans BI.BigSepL.bigSepL_singleton.1)

-- `Iris.frame_fractional` idx 11: necessary, UPred (Option Qp), Φ q = ownM (some q), qR = r = 1/2, qP = 2: ownM 1/2 ∗ ownM 1/2 ⊬ ownM 2
theorem w5c3_87 : ¬ drop0% Iris.frame_fractional 11 := fun h => by
  have hf := (@h (UPred OQ) _ (fQ (1 + 1)) fQ (Qp.half 1) (1 + 1) (Qp.half 1) false (fQ (Qp.half 1))
    (fractional_as_fractional (Φ := fQ) _) (fractional_as_fractional (Φ := fQ) _)).frame
  have e : fQ 1 ⊢ iprop(□?false fQ (Qp.half 1) ∗ fQ (Qp.half 1)) := by
    have h2 := (fQ_frac.fractional (Qp.half 1) (Qp.half 1)).1
    rw [Qp.half_add_half] at h2
    exact h2
  exact fQ_bad (q := 1 + 1) (by simp; grind) (e.trans hf)

-- `Iris.persistent_fractional` idx 3: necessary, affine UPred (Option Qp), P = ownM (some 1): P ⊣⊢ P ∗ P would give ownM (some 1) ⊢ ownM (some 2), invalid
theorem w5c3_122 : ¬ drop0% Iris.persistent_fractional 3 := fun h => by
  have hf := (@h (UPred OQ) _ (fQ 1) (Iris.Std.TCOr.l (t := inferInstance))).fractional 1 1
  exact fQ_bad (q := 1 + 1) (by simp; grind) (hf.1.trans (fQ_frac.fractional 1 1).2)

/-! Rows dropping `NonExpansive Φ` from the (co)induction principles -/

/-- On TN → GB: F Ψ = ⌜NonExpansive Ψ⌝ is a BIMonoPred (constant True on non-expansive inputs). -/
abbrev neF : (TN → GB) → TN → GB := fun Φ _ _ => OFE.NonExpansive Φ
instance neF_mono : BIMonoPred neF where
  mono_pred := fun {Φ Ψ} _ hΨ => by
    intro _ _ _ _ p hp
    obtain ⟨x, hx⟩ := hp
    subst hx
    intro z _
    exact hΨ
  mono_pred_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
theorem neF_lfp (x : TN) (w : Bool) : bi_least_fixpoint neF x w := (lfp_iff ..).2 fun Φ hΦ => hΦ _ _ Φ.ne

-- `Iris.least_fixpoint_ind` idx 7: necessary, A = TN, F Ψ = ⌜NonExpansive Ψ⌝ (least fixpoint True), Φ = ind1: Φ ∧ lfp is not NE, so the premise is vacuous
theorem w5c3_88 : ¬ drop0% Iris.least_fixpoint_ind 7 := fun h => by
  have hne : ¬ OFE.NonExpansive (fun x => (iprop(ind1 x ∧ bi_least_fixpoint neF x) : GB)) := fun hn => by
    have := congrFun (hn.ne tn12) false
    have h2 : (ind1 ⟨1⟩ false ∧ bi_least_fixpoint neF ⟨1⟩ false) := ⟨rfl, neF_lfp _ _⟩
    have h3 : (ind1 ⟨2⟩ false ∧ bi_least_fixpoint neF ⟨2⟩ false) := cast (congrArg id this) h2
    exact absurd (congrArg TN.v h3.1) (by decide)
  have := ev2 (@h GB TN _ _ neF neF_mono ind1) (fun y z hz => absurd hz hne) ⟨2⟩ false (neF_lfp _ _)
  exact absurd (congrArg TN.v this) (by decide)

-- `Iris.greatest_fixpoint_coind` idx 7: necessary, A = TN, F Ψ = ⌜¬ NonExpansive Ψ⌝ (greatest fixpoint False), Φ = ind1: Φ ∨ gfp is not NE, so the premise holds
theorem w5c3_89 : ¬ drop0% Iris.greatest_fixpoint_coind 7 := fun h => by
  let F : (TN → GB) → TN → GB := fun Φ _ _ => ¬ OFE.NonExpansive Φ
  have inst : BIMonoPred F := {
    mono_pred := fun {Φ Ψ} hΦ _ => by
      intro _ _ _ _ p hp
      obtain ⟨x, hx⟩ := hp
      subst hx
      intro z hz
      exact absurd hΦ hz
    mono_pred_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩ }
  have hg : ∀ x w, ¬ bi_greatest_fixpoint F x w := fun x w hw => by
    obtain ⟨Φ, hΦ, hx⟩ := (gfp_iff ..).1 hw
    exact hΦ _ _ hx Φ.ne
  have hne : ¬ OFE.NonExpansive (fun x => (iprop(ind1 x ∨ bi_greatest_fixpoint F x) : GB)) := fun hn => by
    have := congrFun (hn.ne tn12) false
    have h2 : (ind1 ⟨1⟩ false ∨ bi_greatest_fixpoint F ⟨1⟩ false) := .inl rfl
    have h3 : (ind1 ⟨2⟩ false ∨ bi_greatest_fixpoint F ⟨2⟩ false) := cast (congrArg id this) h2
    rcases h3 with h3 | h3
    · exact absurd (congrArg TN.v h3) (by decide)
    · exact hg _ _ h3
  have := ev2 (@h GB TN _ _ F inst ind1 (fun_ne_disc _)) (fun y z _ => hne) ⟨1⟩ false rfl
  exact hg _ _ this

-- `Iris.least_fixpoint_ind_wf` idx 7: removable, the inner least fixpoint L is non-expansive for any F, F L ⊢ L follows from the premise, so lfp F ⊢ F (lfp F) ⊢ F L ⊢ Φ
theorem w5c3_90 : drop% Iris.least_fixpoint_ind_wf 7 := by
  intro PROP A _ _ F IF Φ
  iintro #HM %x Hx
  iapply HM
  have hu := least_fixpoint_unfold_mp F (x := x)
  iapply (mono_pred (F := F) (Φ := bi_least_fixpoint F)
    (Ψ := bi_least_fixpoint (fun Ψ a => iprop(Φ a ∧ F Ψ a)))) $$ [] [Hx]
  · iintro !> %z Hz
    iapply (least_fixpoint_iter F (Φ := bi_least_fixpoint (fun Ψ a => iprop(Φ a ∧ F Ψ a)))) $$ [] Hz
    iintro !> %y Hy %Ψ #HΨ
    iapply HΨ
    isplit
    · iapply HM $$ Hy
    · iapply (@mono_pred _ _ _ _ F IF (bi_least_fixpoint (fun Ψ a => iprop(Φ a ∧ F Ψ a))) Ψ.f _ Ψ.ne) $$ [] Hy
      iintro !> %z Hz
      iapply Hz
      iexact HΨ
  · iapply hu $$ Hx

-- `Iris.greatest_fixpoint_paco` idx 7: removable, the inner greatest fixpoint U is non-expansive for any F, U ⊢ F U follows from the premise, so Φ ⊢ F U ⊢ F (gfp F) ⊢ gfp F
theorem w5c3_91 : drop% Iris.greatest_fixpoint_paco 7 := by
  intro PROP A _ _ F IF Φ
  iintro #Hmon %x HΦ
  iapply greatest_fixpoint_unfold_mpr
  iapply (mono_pred (F := F) (Φ := bi_greatest_fixpoint (fun Ψ a => iprop(Φ a ∨ F Ψ a)))
    (Ψ := bi_greatest_fixpoint F)) $$ [] [HΦ]
  · iintro !> %y Hy
    iapply greatest_fixpoint_coiter $$ [] Hy
    iintro !> %z ⟨%Ψ, #HΨ, Hz⟩
    ihave Hc : Φ z ∨ F Ψ z $$ [Hz]
    · iapply HΨ $$ Hz
    icases Hc with ⟨H|H⟩
    · iapply Hmon $$ H
    · iapply (@mono_pred _ _ _ _ F IF Ψ.f (bi_greatest_fixpoint (fun Ψ a => iprop(Φ a ∨ F Ψ a))) Ψ.ne _) $$ [] H
      iintro !> %w Hw
      iexists Ψ
      isplitr
      · iexact HΨ
      · iexact Hw
  · iapply Hmon $$ HΦ

/-! Laterable rows in TP (step-indexed, resource-blind at step 0): a laterable P holding at step 1
somewhere holds at step 1 everywhere, so emp and ownT are not laterable. -/

theorem tp_lat_at {P : TP} (hl : Laterable P) {m c : Bool} (hm : P.holds 1 m) : P.holds 1 c := by
  obtain ⟨hl⟩ := hl
  have h1 := hl 1 m hm
  obtain ⟨p, ⟨Q, hp⟩, hpm⟩ := h1
  subst hp
  obtain ⟨a, b, _, hQ, _, hw⟩ := hpm
  have hQ0 : Q.holds 0 c := Q.irr hQ
  have h2 := hw 1 (Nat.le_refl 1) c hQ0
  rcases h2 with h3 | h3
  · exact h3.elim
  · simpa using h3

theorem tp_nonlat {P : TP} (m c : Bool) (hm : P.holds 1 m) (hc : ¬ P.holds 1 c) : ¬ Laterable P :=
  fun hl => hc (tp_lat_at hl hm)

def ownT : TP where
  holds n m := n = 0 ∨ m = true
  mono h hle := by rcases h with h | h; exact .inl (by omega); exact .inr h
  irr _ := .inl rfl

theorem tp_emp_nonlat : ¬ Laterable (iprop(emp) : TP) :=
  tp_nonlat false true (.inr rfl) (by rintro (h | h) <;> cases h)
theorem ownT_nonlat : ¬ Laterable ownT :=
  tp_nonlat true false (.inr rfl) (by rintro (h | h) <;> cases h)
instance tp_true_lat : Laterable (iprop(True) : TP) :=
  @timeless_laterable TP _ _ ⟨fun n _ _ => .inr trivial⟩

-- `Iris.Laterable.laterable` idx 3: necessary, TP, P = emp is not laterable
theorem w5c3_92 : ¬ drop0% Iris.Laterable.laterable 3 := fun h => tp_emp_nonlat ⟨@h TP _ iprop(emp)⟩

-- `Iris.IntoLaterable.into_laterable_result_laterable` idx 4: necessary, TP, Q = emp is not laterable
theorem w5c3_93 : ¬ drop0% Iris.IntoLaterable.into_laterable_result_laterable 4 := fun h =>
  tp_emp_nonlat (@h TP _ iprop(emp) iprop(emp))

-- `Iris.timeless_laterable` idx 3: necessary, TP, P = emp is not laterable
theorem w5c3_94 : ¬ drop0% Iris.timeless_laterable 3 := fun h => tp_emp_nonlat (@h TP _ iprop(emp))

-- `Iris.intuitionistic_laterable` idx 3: necessary, TP, P = emp (affine, persistent, not laterable; emp not timeless)
theorem w5c3_95 : ¬ drop0% Iris.intuitionistic_laterable 3 := fun h => tp_emp_nonlat (@h TP _ iprop(emp) _ _)

-- `Iris.persistent_laterable` idx 2: necessary, TP (not affine), P = emp persistent, not laterable
theorem w5c3_96 : ¬ drop0% Iris.persistent_laterable 2 := fun h => tp_emp_nonlat (@h TP _ iprop(emp) _)

-- `Iris.sep_laterable` idx 4: necessary, TP, P = ownT, Q = True (laterable): ownT ∗ True not laterable
theorem w5c3_97 : ¬ drop0% Iris.sep_laterable 4 := fun h => by
  refine absurd (@h TP _ ownT iprop(True) tp_true_lat) (tp_nonlat true false ?_ ?_)
  · exact ⟨true, false, rfl, .inr rfl, trivial⟩
  · rintro ⟨a, b, e, ha, _⟩; cases a <;> cases b <;> simp at e <;> rcases ha with h | h <;> cases h

-- `Iris.sep_laterable` idx 5: necessary, TP, P = True (laterable), Q = ownT: True ∗ ownT not laterable
theorem w5c3_98 : ¬ drop0% Iris.sep_laterable 5 := fun h => by
  refine absurd (@h TP _ iprop(True) ownT tp_true_lat) (tp_nonlat true false ?_ ?_)
  · exact ⟨false, true, rfl, trivial, .inr rfl⟩
  · rintro ⟨a, b, e, _, hb⟩; cases a <;> cases b <;> simp at e <;> rcases hb with h | h <;> cases h

-- `Iris.exist_laterable` idx 4: necessary, TP, A = True, Φ = const emp: ∃ _, emp not laterable
theorem w5c3_99 : ¬ drop0% Iris.exist_laterable 4 := fun h => by
  refine absurd (@h TP _ True (fun _ => iprop(emp))) (tp_nonlat false true ?_ ?_)
  · exact ⟨_, ⟨trivial, rfl⟩, .inr rfl⟩
  · rintro ⟨p, ⟨_, hp⟩, hq⟩; subst hp; rcases hq with h | h <;> cases h

-- `Iris.laterable_congr` idx 4: necessary, TP, P = True (laterable), Q = emp
theorem w5c3_100 : ¬ drop0% Iris.laterable_congr 4 := fun h =>
  tp_emp_nonlat (@h TP _ iprop(True) iprop(emp) tp_true_lat)

-- `Iris.laterable_congr` idx 5: necessary, TP, P = Q = emp
theorem w5c3_101 : ¬ drop0% Iris.laterable_congr 5 := fun h =>
  tp_emp_nonlat (@h TP _ iprop(emp) iprop(emp) .rfl)

-- `Iris.big_sep_sepL_laterable` idx 4: necessary, TP, Q = emp, Ps = []: emp ∗ emp not laterable
theorem w5c3_102 : ¬ drop0% Iris.big_sep_sepL_laterable 4 := fun h => by
  refine absurd (@h TP _ iprop(emp) [] (fun _ hP => by cases hP)) (tp_nonlat false true ?_ ?_)
  · exact (⟨false, false, rfl, .inr rfl, .inr rfl⟩ : (iprop(emp ∗ emp) : TP).holds 1 false)
  · intro hx
    obtain ⟨a, b, e, ha, hb⟩ := (hx : (iprop(emp ∗ emp) : TP).holds 1 true)
    have ha' : a = false := by rcases (ha : (iprop(emp) : TP).holds 1 a) with h | h; cases h; exact h
    have hb' : b = false := by rcases (hb : (iprop(emp) : TP).holds 1 b) with h | h; cases h; exact h
    subst ha' hb'; cases e

-- `Iris.big_sep_sepL_laterable` idx 5: necessary, TP, Q = True (laterable), Ps = [ownT]: True ∗ (ownT ∗ emp) not laterable
theorem w5c3_103 : ¬ drop0% Iris.big_sep_sepL_laterable 5 := fun h => by
  have hl := @h TP _ iprop(True) [ownT] tp_true_lat
  rw [show ([∗] [ownT] : TP) = ownT from rfl] at hl
  refine absurd hl (tp_nonlat true false ?_ ?_)
  · exact ⟨false, true, rfl, trivial, .inr rfl⟩
  · rintro ⟨a, b, e, _, hb⟩; cases a <;> cases b <;> simp at e <;> rcases hb with h | h <;> cases h

-- `Iris.big_sepL_laterable` idx 3: necessary, TP, Ps = []: the big sep is emp, not laterable
theorem w5c3_104 : ¬ drop0% Iris.big_sepL_laterable 3 := fun h =>
  tp_emp_nonlat (@h TP _ [] Iris.Std.TCForall.nil)

-- `Iris.make_laterable_intro'` idx 3: necessary, TP, Q = emp: emp ⊢ make_laterable emp would make emp laterable
theorem w5c3_105 : ¬ drop0% Iris.make_laterable_intro' 3 := fun h =>
  tp_emp_nonlat (laterable_alt.2 (@h TP _ iprop(emp)))

-- `Iris.make_laterable_intro` idx 4: necessary, TP, P = Q = emp: emp ⊢ make_laterable emp would make emp laterable
theorem w5c3_106 : ¬ drop0% Iris.make_laterable_intro 4 := fun h => by
  refine tp_emp_nonlat (laterable_alt.2 ?_)
  iintro H
  iapply (@h TP _ iprop(emp) iprop(emp)) $$ [] H
  iintro !> H2
  iexact H2

-- `Iris.intoLaterable_laterable` idx 3: necessary, TP, P = emp: the IntoLaterable result emp is not laterable
theorem w5c3_107 : ¬ drop0% Iris.intoLaterable_laterable 3 := fun h =>
  tp_emp_nonlat (@h TP _ iprop(emp)).into_laterable_result_laterable

/-! TPA: affine variant of TP (W4c1): step-indexed predicates over the Bool-or monoid, resource-blind at
step 0 and upward closed in the resource, emp = True. emp is timeless, but ownT is not laterable. -/
structure TPA where
  holds : Nat → Bool → Prop
  mono {n n' : Nat} {m : Bool} : holds n m → n' ≤ n → holds n' m
  irr {m m' : Bool} : holds 0 m → holds 0 m'
  up {n : Nat} : holds n false → holds n true

theorem TPA.upm (P : TPA) {n : Nat} {m m' : Bool} (hm : m = true → m' = true) (h : P.holds n m) :
    P.holds n m' := by
  cases m <;> cases m'
  · exact h
  · exact P.up h
  · exact absurd (hm rfl) (by decide)
  · exact h

theorem TPA.ext' : {P Q : TPA} → (∀ n m, P.holds n m ↔ Q.holds n m) → P = Q
  | ⟨p, _, _, _⟩, ⟨q, _, _, _⟩, h => by
    have : p = q := funext fun n => funext fun m => propext (h n m)
    subst this; rfl

def TPA.emp : TPA where
  holds _ _ := True
  mono h _ := h
  irr h := h
  up h := h
def TPA.pure (φ : Prop) : TPA where
  holds _ _ := φ
  mono h _ := h
  irr h := h
  up h := h
def TPA.and (P Q : TPA) : TPA where
  holds n m := P.holds n m ∧ Q.holds n m
  mono h hle := ⟨P.mono h.1 hle, Q.mono h.2 hle⟩
  irr h := ⟨P.irr h.1, Q.irr h.2⟩
  up h := ⟨P.up h.1, Q.up h.2⟩
def TPA.or (P Q : TPA) : TPA where
  holds n m := P.holds n m ∨ Q.holds n m
  mono h hle := h.elim (fun h => .inl (P.mono h hle)) (fun h => .inr (Q.mono h hle))
  irr h := h.elim (fun h => .inl (P.irr h)) (fun h => .inr (Q.irr h))
  up h := h.elim (fun h => .inl (P.up h)) (fun h => .inr (Q.up h))
def TPA.imp (P Q : TPA) : TPA where
  holds n m := ∀ n', n' ≤ n → ∀ m', (m = true → m' = true) → P.holds n' m' → Q.holds n' m'
  mono h hle n'' h'' m' hm hp := h n'' (Nat.le_trans h'' hle) m' hm hp
  irr h n' hn' m'' _ hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) true (fun _ => rfl) (P.irr hp))
  up h n' hle m' hm hp := by
    have : m' = true := hm rfl
    subst this
    exact h n' hle true (fun h => absurd h (by decide)) hp
def TPA.sForall (Ψ : TPA → Prop) : TPA where
  holds n m := ∀ p, Ψ p → p.holds n m
  mono h hle p hp := p.mono (h p hp) hle
  irr h p hp := p.irr (h p hp)
  up h p hp := p.up (h p hp)
def TPA.sExists (Ψ : TPA → Prop) : TPA where
  holds n m := ∃ p, Ψ p ∧ p.holds n m
  mono h hle := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.mono h hle⟩
  irr h := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.irr h⟩
  up h := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.up h⟩
def TPA.sep (P Q : TPA) : TPA where
  holds n m := ∃ a b, m = Bool.or a b ∧ P.holds n a ∧ Q.holds n b
  mono h hle := let ⟨a, b, e, hp, hq⟩ := h; ⟨a, b, e, P.mono hp hle, Q.mono hq hle⟩
  irr {_ m'} h := let ⟨_, _, _, hp, hq⟩ := h; ⟨m', false, by cases m' <;> rfl, P.irr hp, Q.irr hq⟩
  up {n} h := by
    obtain ⟨a, b, e, hp, hq⟩ := h
    exact ⟨true, b, rfl, P.upm (fun _ => rfl) hp, hq⟩
def TPA.wand (P Q : TPA) : TPA where
  holds n m := ∀ n', n' ≤ n → ∀ b, P.holds n' b → Q.holds n' (Bool.or m b)
  mono h hle n'' h'' b hp := h n'' (Nat.le_trans h'' hle) b hp
  irr h n' hn' b hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) b hp)
  up h n' hle b hp := Q.upm (fun _ => by simp) (h n' hle b hp)
def TPA.pers (P : TPA) : TPA where
  holds n _ := P.holds n false
  mono h hle := P.mono h hle
  irr h := h
  up h := h
def TPA.later (P : TPA) : TPA where
  holds n m := match n with | 0 => True | k+1 => P.holds k m
  mono {n n' m} h hle := by
    cases n' with
    | zero => trivial
    | succ k' => cases n with
      | zero => omega
      | succ k => exact P.mono h (by omega)
  irr _ := trivial
  up {n} h := by
    cases n with
    | zero => trivial
    | succ k => exact P.up h

instance : BIBase TPA where
  Entails P Q := ∀ n m, P.holds n m → Q.holds n m
  emp := TPA.emp
  pure := TPA.pure
  and := TPA.and
  or := TPA.or
  imp := TPA.imp
  sForall := TPA.sForall
  sExists := TPA.sExists
  sep := TPA.sep
  wand := TPA.wand
  persistently := TPA.pers
  later := TPA.later

instance : COFE TPA := COFE.ofDiscrete _

instance tpaBI : BI TPA where
  entails_refl _ _ h := h
  entails_trans h1 h2 n m h := h2 n m (h1 n m h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ _ h => h, fun _ _ h => h⟩,
    fun ⟨h1, h2⟩ => TPA.ext' fun n m => ⟨h1 n m, h2 n m⟩⟩
  and_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  pure_intro h _ _ _ := h
  pure_elim' h n m hφ := h hφ n m trivial
  and_elim_l _ _ h := h.1
  and_elim_r _ _ h := h.2
  and_intro h1 h2 n m h := ⟨h1 n m h, h2 n m h⟩
  or_intro_l _ _ h := .inl h
  or_intro_r _ _ h := .inr h
  or_elim h1 h2 n m h := h.elim (h1 n m) (h2 n m)
  imp_intro {P _ _} h n m hp n' hle m' hm hq := h n' m' ⟨P.upm hm (P.mono hp hle), hq⟩
  imp_elim h n m hpq := h n m hpq.1 n (Nat.le_refl n) m id hpq.2
  sForall_intro h n m hp p hΨ := h p hΨ n m hp
  sForall_elim hΨ n m h := h _ hΨ
  sExists_intro hΨ n m h := ⟨_, hΨ, h⟩
  sExists_elim h n m := fun ⟨p, hp, hh⟩ => h p hp n m hh
  sep_mono h1 h2 n m := fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, h1 n a hp, h2 n b hq⟩
  emp_sep {P} := ⟨fun n m ⟨a, b, e, _, hp⟩ => P.upm (fun hb => by subst e; simp [hb]) hp,
    fun n m hp => ⟨false, m, by cases m <;> rfl, trivial, hp⟩⟩
  sep_symm n m := fun ⟨a, b, e, hp, hq⟩ => ⟨b, a, by rw [e, Bool.or_comm], hq, hp⟩
  sep_assoc_l n m := fun ⟨_, c, e, ⟨a, b, e', hp, hq⟩, hr⟩ =>
    ⟨a, Bool.or b c, by rw [e, e', Bool.or_assoc], hp, b, c, rfl, hq, hr⟩
  wand_intro {P _ _} h n m hp n' hle b hq := h n' (Bool.or m b) ⟨m, b, rfl, P.mono hp hle, hq⟩
  wand_elim h n m := fun ⟨a, b, e, hp, hq⟩ => e ▸ h n a hp n (Nat.le_refl n) b hq
  persistently_mono h n _ hp := h n false hp
  persistently_idem_2 _ _ h := h
  persistently_emp_2 _ _ _ := trivial
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
    | succ k => exact fun p hp => h _ ⟨p, rfl⟩ (k+1) (Nat.le_refl _) m id hp
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
      refine .inr fun n' hle m' _ hf => ?_
      cases n' with
      | zero => exact P.irr (P.mono h (Nat.zero_le _))
      | succ j => exact hf.elim

instance : BIAffine TPA := ⟨fun _ => ⟨fun _ _ _ => trivial⟩⟩
instance tpa_emp_timeless : Timeless (iprop(emp) : TPA) := ⟨fun _ _ _ => .inr trivial⟩

theorem tpa_lat_at {P : TPA} (hl : Laterable P) {m c : Bool} (hm : P.holds 1 m) : P.holds 1 c := by
  obtain ⟨hl⟩ := hl
  have h1 := hl 1 m hm
  obtain ⟨p, ⟨Q, hp⟩, hpm⟩ := h1
  subst hp
  obtain ⟨a, b, _, hQ, _, hw⟩ := hpm
  have hQ0 : Q.holds 0 c := Q.irr hQ
  have h2 := hw 1 (Nat.le_refl 1) c hQ0
  rcases h2 with h3 | h3
  · exact h3.elim
  · simpa using h3

def ownTA : TPA where
  holds n m := n = 0 ∨ m = true
  mono h hle := by rcases h with h | h; exact .inl (by omega); exact .inr h
  irr _ := .inl rfl
  up _ := .inr rfl

theorem ownTA_nonlat : ¬ Laterable ownTA := fun hl => by
  rcases tpa_lat_at hl (m := true) (c := false) (.inr rfl) with h | h <;> cases h

-- `Iris.persistent_laterable` idx 4: necessary, affine BI TPA, P = ownTA is not laterable
theorem w5c3_108 : ¬ drop0% Iris.persistent_laterable 4 := fun h => ownTA_nonlat (@h TPA _ _ ownTA)

-- `Iris.intuitionistic_laterable` idx 5: necessary, affine BI TPA (emp timeless), P = ownTA affine, not laterable
theorem w5c3_109 : ¬ drop0% Iris.intuitionistic_laterable 5 := fun h =>
  ownTA_nonlat (@h TPA _ ownTA tpa_emp_timeless inferInstance)

-- `Iris.big_sepL_laterable` idx 4: necessary, affine BI TPA (emp timeless, so laterable), Ps = [ownTA]
theorem w5c3_110 : ¬ drop0% Iris.big_sepL_laterable 4 := fun h =>
  ownTA_nonlat (@h TPA _ [ownTA] (timeless_laterable _))

/-! A concrete gen-heap ghost state: GF with slots 0/1 the HeapViews of the heap and of the meta names
(ExtTreeMap over Nat), slot 2 MetaUR; L = Nat, V = Unit. -/
abbrev HV0 := HeapView Nat (Agree (DiscreteO Unit)) TM
abbrev HV1 := HeapView Nat (Agree (DiscreteO GName)) TM
def GFh : BundledGFunctors := fun i => match i with
  | 0 => ⟨constOF HV0⟩
  | 1 => ⟨constOF HV1⟩
  | _ => ⟨constOF MetaUR⟩
instance ghPre : genHeapPreS Nat Unit GFh TM where
  heap := ⟨{ τ := 0, transp := rfl }⟩
  metaInfo := ⟨{ τ := 1, transp := rfl }⟩
  metaData := { τ := 2, transp := rfl }

theorem gh_false_unsound (H : ⊢ (|==> iprop(⌜False⌝) : IProp GFh)) : False :=
  pure_soundness (PROP := IProp GFh) (UPred.bupd_soundness H)

/-- From the initial heap {[0 := ()]}: if Q follows from genHeapInterp σ ∗ 0 ↦ () (under an update), False. -/
theorem gh_init_false
    (K : ∀ G : genHeapGS Nat Unit GFh TM,
      genHeapInterp (G := G) (Iris.Std.PartialMap.singleton 0 ()) ∗ pointsTo (G := G) 0 (.own 1) () ⊢
        |==> iprop(⌜False⌝)) : False := by
  refine gh_false_unsound ((genHeap_init (L := Nat) (V := Unit) (GF := GFh) (H := TM)
    (Iris.Std.PartialMap.singleton 0 ())).trans ?_)
  iintro H
  imod H with ⟨%G, Hi, Hp, -⟩
  ihave Hp2 : pointsTo (G := G) 0 (.own 1) () $$ [Hp]
  · iapply (BI.BigSepM.bigSepM_singleton (M := TM) (Φ := fun l v => pointsTo (G := G) l (.own 1) v) (i := 0) (x := ())).1
    iexact Hp
  iapply (K G)
  isplitl [Hi]
  · iexact Hi
  · iexact Hp2

-- `Iris.genHeapInterp_eqv` idx 8: necessary, concrete GFh: genHeapInterp {[0 := ()]} ⊢ genHeapInterp ∅ contradicts genHeap_valid for 0 ↦ ()
theorem w5c3_111 : ¬ drop0% Iris.genHeapInterp_eqv 8 := fun h => gh_init_false fun G => by
  iintro ⟨Hi, Hp⟩
  ihave Hi2 : genHeapInterp (G := G) (∅ : TM Unit) $$ [Hi]
  · iapply (@h GFh Nat Unit TM _ G (Iris.Std.PartialMap.singleton 0 ()) ∅)
    iexact Hi
  imod (genHeap_valid (σ := (∅ : TM Unit)) (l := 0)) $$ [Hi2 Hp] with %hv
  · isplitl [Hi2]
    · iexact Hi2
    · iexact Hp
  rw [Iris.Std.LawfulPartialMap.get?_empty] at hv
  cases hv

theorem two_full (G : genHeapGS Nat Unit GFh TM) (dq : DFrac) :
    pointsTo (G := G) 0 (.own 1) () ∗ pointsTo (G := G) 0 dq () ⊢ iprop(⌜False⌝) :=
  pointsTo_op_cmraValid.trans (and_elim_l.trans (pure_mono fun hv => absurd (DFrac.valid_own_op hv) (by simp)))

-- `Iris.genHeap_alloc` idx 10: necessary, concrete GFh, σ = {[0 := ()]}: allocating 0 again gives a second full 0 ↦ ()
theorem w5c3_112 : ¬ drop0% Iris.genHeap_alloc 10 := fun h => gh_init_false fun G => by
  iintro ⟨Hi, Hp⟩
  ihave H2 := (@h GFh Nat Unit TM _ G _ (Iris.Std.PartialMap.singleton 0 ()) 0 ()) $$ Hi
  imod H2 with ⟨-, Hp2, -⟩
  imodintro
  iapply (two_full G (.own 1))
  isplitl [Hp]
  · iexact Hp
  · iexact Hp2

-- `Iris.genHeap_alloc_big` idx 9: necessary, concrete GFh, σ' = σ = {[0 := ()]}: allocating σ' gives a second full 0 ↦ ()
theorem w5c3_113 : ¬ drop0% Iris.genHeap_alloc_big 9 := fun h => gh_init_false fun G => by
  iintro ⟨Hi, Hp⟩
  ihave H2 := (@h GFh Nat Unit TM _ G _ (Iris.Std.PartialMap.singleton 0 ()) (Iris.Std.PartialMap.singleton 0 ())) $$ Hi
  imod H2 with ⟨-, Hp2, -⟩
  ihave Hp3 : pointsTo (G := G) 0 (.own 1) () $$ [Hp2]
  · iapply (BI.BigSepM.bigSepM_singleton (M := TM) (Φ := fun l v => pointsTo (G := G) l (.own 1) v) (i := 0) (x := ())).1
    iexact Hp2
  imodintro
  iapply (two_full G (.own 1))
  isplitl [Hp]
  · iexact Hp
  · iexact Hp3

-- `Iris.pointsTo_frac_ne` idx 12: necessary, concrete GFh: the persistent 0 ↦□ () duplicates, giving ⌜0 ≠ 0⌝
theorem w5c3_114 : ¬ drop0% Iris.pointsTo_frac_ne 12 := fun h => gh_init_false fun G => by
  iintro ⟨-, Hp⟩
  ihave H2 := (pointsTo_persist (L := Nat) (V := Unit) (GF := GFh) (H := TM) (l := 0) (dq := .own 1) (v := ())) $$ Hp
  imod H2 with #Hd
  ihave %hne := (@h GFh Nat Unit TM _ G 0 0 .discard .discard () ()) $$ Hd Hd
  exact absurd rfl hne

-- `Iris.instFramePointsTo` idx 12: necessary, concrete GFh, q₁ = r = 1/2, q₂ = 2: framing 0 ↦{1/2} () against 0 ↦{1/2} () would give 0 ↦{2} (), invalid
theorem w5c3_115 : ¬ drop0% Iris.instFramePointsTo 12 := fun h => gh_init_false fun G => by
  have hs : pointsTo (G := G) 0 (.own 1) () ⊢
      pointsTo (G := G) 0 (.own (Qp.half 1)) () ∗ pointsTo (G := G) 0 (.own (Qp.half 1)) () := by
    have h2 := (instFractionalPointsTo (GF := GFh) (H := TM) (l := (0 : Nat)) (v := ())).fractional (Qp.half 1) (Qp.half 1)
    rw [Qp.half_add_half] at h2
    exact h2.1
  have hf := (@h GFh Nat Unit TM _ G false 0 () (Qp.half 1) (1 + 1) (Qp.half 1)).frame
  have hv : pointsTo (G := G) 0 (.own (1 + 1)) () ⊢ iprop(⌜False⌝) :=
    pointsTo_cmraValid.trans (pure_mono fun hv => absurd (DFrac.valid_own.1 hv) (by simp; grind))
  iintro ⟨-, Hp⟩
  imodintro
  iapply hv
  iapply hf
  iapply hs $$ Hp

theorem top_not_disj : ¬ ((⊤ : CoPset) ## ⊤) := fun hd => hd .xH ⟨rfl, rfl⟩

/-- From the initial heap {[0 := ()]} with its meta token: if False follows under an update, False. -/
theorem gh_init_false3
    (K : ∀ G : genHeapGS Nat Unit GFh TM,
      metaToken (G := G) 0 ⊤ ∗ metaToken (G := G) 0 (⊤ \ ⊤) ⊢ |==> iprop(⌜False⌝)) : False := by
  refine gh_false_unsound ((genHeap_init (L := Nat) (V := Unit) (GF := GFh) (H := TM)
    (Iris.Std.PartialMap.singleton 0 ())).trans ?_)
  iintro H
  imod H with ⟨%G, -, -, Hm⟩
  ihave Hm2 : metaToken (G := G) 0 ⊤ $$ [Hm]
  · iapply (BI.BigSepM.bigSepM_singleton (M := TM) (Φ := fun l _ => metaToken (G := G) l ⊤) (i := 0) (x := ())).1
    iexact Hm
  iapply (K G)
  iapply (metaToken_difference (GF := GFh) (L := Nat) (V := Unit) (H := TM) (l := 0) (E1 := ⊤) (E2 := ⊤)
    (fun _ h => h)).1
  iexact Hm2

theorem two_top (G : genHeapGS Nat Unit GFh TM) :
    metaToken (G := G) 0 ⊤ ∗ metaToken (G := G) 0 ⊤ ⊢ iprop(⌜False⌝) := by
  iintro ⟨H1, H2⟩
  ihave %hd := (metaToken_valid_2 (GF := GFh) (L := Nat) (V := Unit) (H := TM) (l := 0) (E1 := ⊤) (E2 := ⊤)) $$ H1 H2
  exact absurd hd top_not_disj

-- `Iris.metaToken_ne` idx 9: necessary, concrete GFh, E = ⊤ \ ⊤ (a token obtained by splitting ⊤): ⌜0 ≠ 0⌝
theorem w5c3_116 : ¬ drop0% Iris.metaToken_ne 9 := fun h => gh_init_false3 fun G => by
  iintro ⟨H1, H2⟩
  ihave %hne := (@h GFh Nat Unit TM _ G 0 0 (⊤ \ ⊤)) $$ H1 H2
  exact absurd rfl hne

-- `Iris.metaToken_difference` idx 9: necessary, concrete GFh, E1 = ⊤, E2 = ⊤ \ ⊤: splitting gives a second token for ⊤
theorem w5c3_117 : ¬ drop0% Iris.metaToken_difference 9 := fun h => gh_init_false3 fun G => by
  iintro ⟨H1, H2⟩
  ihave H3 := (@h GFh Nat Unit TM _ G 0 ⊤ (⊤ \ ⊤)).1 $$ H2
  icases H3 with ⟨H4, -⟩
  imodintro
  iapply (two_top G)
  isplitl [H1]
  · iexact H1
  · iexact H4

-- `Iris.metaToken_union_1` idx 9: necessary, concrete GFh, E1 = E2 = ⊤ (⊤ ∪ ⊤ = ⊤): two tokens for ⊤
theorem w5c3_118 : ¬ drop0% Iris.metaToken_union_1 9 := fun h => gh_init_false3 fun G => by
  iintro ⟨H1, -⟩
  have e : (⊤ : CoPset) ∪ ⊤ = ⊤ := Iris.Std.LawfulSet.union_idem
  have h2 := @h GFh Nat Unit TM _ G 0 ⊤ ⊤
  rw [e] at h2
  ihave H3 := h2 $$ H1
  imodintro
  iapply (two_top G) $$ H3

-- `Iris.metaToken_union` idx 9: necessary, concrete GFh, E1 = E2 = ⊤ (⊤ ∪ ⊤ = ⊤): two tokens for ⊤
theorem w5c3_119 : ¬ drop0% Iris.metaToken_union 9 := fun h => gh_init_false3 fun G => by
  iintro ⟨H1, -⟩
  have e : (⊤ : CoPset) ∪ ⊤ = ⊤ := Iris.Std.LawfulSet.union_idem
  have h2 := (@h GFh Nat Unit TM _ G 0 ⊤ ⊤).1
  rw [e] at h2
  ihave H3 := h2 $$ H1
  imodintro
  iapply (two_top G) $$ H3

-- `Iris.meta_set` idx 12: necessary, concrete GFh: setting meta 0 N to 0 from the ⊤ \ ⊤ token and to 1 from the ⊤ token contradicts meta_agree
theorem w5c3_120 : ¬ drop0% Iris.meta_set 12 := fun h => gh_init_false3 fun G => by
  iintro ⟨H1, H2⟩
  ihave M1 := (@h GFh Nat Unit TM _ G Nat _ 0 (⊤ \ ⊤) nroot 0) $$ H2
  ihave M2 := (meta_set (GF := GFh) (L := Nat) (V := Unit) (H := TM) (l := 0) (E := ⊤) (N := nroot) (1 : Nat)
    CoPset.subseteq_top) $$ H1
  imod M1 with #M1
  imod M2 with #M2
  ihave %he := (meta_agree (GF := GFh) (L := Nat) (V := Unit) (H := TM) (l := 0) (N := nroot) (x1 := (0 : Nat)) (x2 := 1)) $$ M1 M2
  exact absurd he (by decide)

-- `Iris.meta_metaToken_valid'` idx 12: necessary, concrete GFh: meta 0 N 0 (set from the ⊤ token) together with the ⊤ \ ⊤ token
theorem w5c3_121 : ¬ drop0% Iris.meta_metaToken_valid' 12 := fun h => gh_init_false3 fun G => by
  iintro ⟨H1, H2⟩
  ihave M := (meta_set (GF := GFh) (L := Nat) (V := Unit) (H := TM) (l := 0) (E := ⊤) (N := nroot) (0 : Nat)
    CoPset.subseteq_top) $$ H1
  imod M with #M
  ihave F := (@h GFh Nat Unit TM _ G Nat _ 0 nroot 0 (⊤ \ ⊤)) $$ M H2
  icases F with %hf
  exact hf.elim

end W5c3
