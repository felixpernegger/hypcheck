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

namespace W8c0
open Iris Iris.BI

/-! GB (copied from W4c4): predicates on Bool with sep over xor, emp = (x = false): non-affine BI,
emp not absorbing, persistently = value at false. -/
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

/-! KB (copied from W4c5): affine Kripke BI on Bool worlds, persistently = box over all worlds;
not BIPersistentlyExist. -/
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

/-! AU: classical affine BI on Unit → Prop (sep = and, persistently = id, later = id); every
proposition is except-0. Embedding it into SiProp by the pure modality does not commute with later. -/
def AU := Unit → Prop

instance : BIBase AU where
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

instance : COFE AU := COFE.ofDiscrete _

instance auBI : BI AU where
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


-- helper: AU embeds into SiProp as pure propositions (P ↦ ⌜P ()⌝)
@[instance_reducible] def auE : BiEmbed AU SiProp where
  embed P := SiProp.pure (P ())
  ne := ⟨fun _ _ _ h => (h : _ = _) ▸ fun _ => Iff.rfl⟩
  mono := fun h _ hp => h () hp
  emp_valid_inj := fun _ h x _ => h 0 trivial
  emp_2 := fun _ _ => trivial
  impl_2 := fun _ _ n h hp => h n (Nat.le_refl n) hp
  forall_2 := fun _ _ h n hr p hp => h p hp n hr
  exist_1 := fun _ _ h n => fun ⟨p, hp, hx⟩ => h p hp n hx
  sep := fun _ _ => ⟨fun _ h => h, fun _ h => h⟩
  wand_2 := fun _ _ n h hp => h n (Nat.le_refl n) hp
  persistently := fun _ => ⟨fun _ h => h, fun _ h => h⟩

-- helper (copied from W5c0): identity embedding with Later/Sbi instances
@[instance_reducible] def idEmb (PROP : Type _) [BI PROP] : BiEmbed PROP PROP where
  embed := id
  ne := ⟨fun _ _ _ h => h⟩
  mono := fun h => h
  emp_valid_inj := fun _ h => h
  emp_2 := .rfl
  impl_2 := fun _ _ => .rfl
  forall_2 := fun _ _ h => sForall_intro h
  exist_1 := fun _ _ h => sExists_elim h
  sep := fun _ _ => .rfl
  wand_2 := fun _ _ => .rfl
  persistently := fun _ => .rfl
theorem idEmp (PROP : Type _) [BI PROP] : @BiEmbedEmp PROP PROP _ _ (idEmb PROP) :=
  @BiEmbedEmp.mk PROP PROP _ _ (idEmb PROP) .rfl
theorem idLat (PROP : Type _) [BI PROP] : @BiEmbedLater PROP PROP _ _ (idEmb PROP) :=
  @BiEmbedLater.mk PROP PROP _ _ (idEmb PROP) (fun _ => .rfl)
theorem idSbi (PROP : Type _) [Sbi PROP] : @BiEmbedSbi PROP PROP _ _ (idEmb PROP) _ _ :=
  @BiEmbedSbi.mk PROP PROP _ _ (idEmb PROP) _ _ (fun _ => .rfl) (fun _ => .rfl)

-- helper (copied from W5c0): delay embedding of SiProp into itself; does not commute with later
def dl (P : SiProp) : SiProp := ⟨fun n => P.holds (n - 1), fun h hle => P.closed h (by omega)⟩
@[instance_reducible] def delayE : BiEmbed SiProp SiProp where
  embed := dl
  ne := ⟨fun {n x y} h m hle => h (by omega)⟩
  mono := fun h n hp => h _ hp
  emp_valid_inj := fun P h n _ => h (n + 1) trivial
  emp_2 := fun _ _ => trivial
  impl_2 := fun P Q n h m hm hp => by
    cases n with
    | zero => have e : m = 0 := by omega
              subst e; exact h 0 (Nat.le_refl 0) hp
    | succ k => exact h (m + 1) (by omega) hp
  forall_2 := fun Ψ R h n hr P hP => h P hP n hr
  exist_1 := fun Ψ R h n ⟨P, hP, hp⟩ => h P hP n hp
  sep := fun P Q => ⟨fun _ h => h, fun _ h => h⟩
  wand_2 := fun P Q n h m hm hp => by
    cases n with
    | zero => have e : m = 0 := by omega
              subst e; exact h 0 (Nat.le_refl 0) hp
    | succ k => exact h (m + 1) (by omega) hp
  persistently := fun P => ⟨fun _ h => h, fun _ h => h⟩
-- helper: SiProp true only at step 0, and True as a named SiProp
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩
def sT : SiProp := iprop(True)

-- helper (copied from W5c0/W5c1): identity and constant-True basic updates on SiProp
@[instance_reducible] def idBupd : BIUpdate SiProp where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h
@[reducible] def topBupd : BIUpdate SiProp where
  bupd _ := iprop(True)
  bupd_ne := ⟨fun _ _ _ _ _ _ => Iff.rfl⟩
  intro := fun _ _ => trivial
  mono _ := fun _ h => h
  trans := fun _ h => h
  frame_right := fun _ _ => trivial
theorem idBU (B : BIUpdate SiProp) : @BiEmbedBUpd SiProp SiProp _ _ (idEmb _) B B :=
  @BiEmbedBUpd.mk SiProp SiProp _ _ (idEmb _) B B (fun _ => .rfl)

end W8c0

namespace W8c0
open Iris Iris.BI Iris.OFE

-- helper (copied from W2c1): Bool OFE where all elements agree at step 0, CMRA with op = and
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

-- helper (copied from W1c3): one-point ORAs: UZ never valid with order only at step 0; UV valid only at step 0
/-- One-point ORA, never valid, step-indexed order holding only at step 0, no core. -/
structure UZ where
instance : OFE UZ := OFE.ofDiscrete UZ
instance : Op UZ where
  op _ _ := ⟨⟩
  op_ne := ⟨fun _ _ _ _ => rfl⟩
  assoc := rfl
  comm := rfl
instance : PCore UZ where
  pcore _ := none
  pcore_ne _ h := (by cases h)
  pcore_idem h := (by cases h)
instance : Valid UZ where
  ValidN _ _ := False
  Valid _ := False
  validN_ne _ h := h
  valid_iff_validN := ⟨False.elim, fun h => h 0⟩
  validN_succ h := h
instance : Ordered UZ where
  OrderN n _ _ := n = 0
  Order _ _ := False
  ordN_ne _ _ h := h
  ordN_succ h := absurd h (Nat.succ_ne_zero _)
  ordN_trans h _ := h
  ord_trans h _ := h
  ordN_of_ord _ h := h.elim
instance uzORA : ORA UZ where
  validN_op_left h := h
  pcore_op_left h := (by cases h)
  extend h _ := h.elim
  op_monoN_left_ord _ h := h
  op_mono_left_ord _ h := h
  validN_of_ordN _ h := h
  pcore_monoN_ord _ h := (by cases h)
  pcore_mono_ord _ h := (by cases h)
  pcore_order_op h := (by cases h)
  pcore_increasing h := (by cases h)
  increasing_closed hx _ := hx
  ordN_extend hv _ := hv.elim
/-- One-point ORA, valid only at step 0, empty order, no core. -/
structure UV where
instance : OFE UV := OFE.ofDiscrete UV
instance : Op UV where
  op _ _ := ⟨⟩
  op_ne := ⟨fun _ _ _ _ => rfl⟩
  assoc := rfl
  comm := rfl
instance : PCore UV where
  pcore _ := none
  pcore_ne _ h := (by cases h)
  pcore_idem h := (by cases h)
instance : Valid UV where
  ValidN n _ := n = 0
  Valid _ := False
  validN_ne _ h := h
  valid_iff_validN := ⟨False.elim, fun h => absurd (h 1) (by decide)⟩
  validN_succ h := absurd h (Nat.succ_ne_zero _)
instance : Ordered UV where
  OrderN _ _ _ := False
  Order _ _ := False
  ordN_ne _ _ h := h
  ordN_succ h := h
  ordN_trans h _ := h
  ord_trans h _ := h
  ordN_of_ord _ h := h
instance uvORA : ORA UV where
  validN_op_left h := h
  pcore_op_left h := (by cases h)
  extend _ _ := ⟨⟨⟩, ⟨⟩, rfl, rfl, rfl⟩
  op_monoN_left_ord _ h := h
  op_mono_left_ord _ h := h
  validN_of_ordN h _ := h.elim
  pcore_monoN_ord _ h := (by cases h)
  pcore_mono_ord _ h := (by cases h)
  pcore_order_op h := (by cases h)
  pcore_increasing h := (by cases h)
  increasing_closed hx _ := hx
  ordN_extend _ h := h.elim

-- helper (copied from W4c3): the SiProp internal inclusion from n-inclusion
theorem incH' {A : Type} [ORA A] {a b : A} {n : Nat}
    (h : a ≼{n} b) : (internalCmraIncluded (PROP := SiProp) a b).holds n := by
  obtain ⟨c, hc⟩ := h; exact SiProp.exists_holds.mpr ⟨c, hc⟩

-- helper: constant-True fancy update on SiProp (lawful; all mask laws hold trivially)
@[reducible] def topFupd : BIFUpdate SiProp where
  fupd _ _ _ := iprop(True)
  ne := ⟨fun _ _ _ _ _ _ => Iff.rfl⟩
  subset _ := fun _ _ => trivial
  except0 := fun _ _ => trivial
  mono _ := fun _ h => h
  trans := fun _ h => h
  mask_frame_right_strong _ := fun _ h => h
  frame_right := fun _ _ => trivial
theorem topFU : @BiEmbedFUpd SiProp SiProp _ _ (idEmb _) topFupd topFupd :=
  @BiEmbedFUpd.mk SiProp SiProp _ _ (idEmb _) topFupd topFupd (fun _ _ _ => .rfl)

end W8c0

namespace W8c0
open Iris Iris.BI Iris.Std Iris.Algebra Iris.Instances.Data

-- helpers (copied from W4c2/W5c5): one-key maps, singleton sets and multisets, with their big separating conjunctions
abbrev TM := fun V => Std.ExtTreeMap Nat V compare
abbrev sg {V : Type} (v : V) : TM V := PartialMap.insert ∅ 0 v
theorem sg_get {V : Type} (v : V) : get? (sg v) 0 = some v := get?_insert_eq rfl
theorem sgE {PROP : Type _} [BI PROP] {V : Type} (Φ : Nat → V → PROP) (v : V) :
    bigSepM Φ (sg v) = Φ 0 v := BigOpM.bigOpM_singleton_eq (op := BIBase.sep) Φ 0 v
abbrev TS := Std.ExtTreeSet Nat compare
theorem ssE {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : bigSepS Φ ({0} : TS) ⊣⊢ Φ 0 := BigSepS.bigSepS_singleton
abbrev MSN := ListPerm Nat
theorem msSing {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : ([∗mset] x ∈ ({0} : MSN), Φ x) ⊣⊢ Φ 0 :=
  BigSepMS.bigSepMS_singleton (MS := ListPerm Nat)

end W8c0

namespace W8c0
open Iris Iris.BI Iris.Std Iris.Std.LawfulSet

-- helper (copied from W6c1): MK, a non-affine discrete BI on mask predicates with the lawful
-- mask-sensitive fancy update mkFupd; at masks empty/empty mkFupd is the identity
/-! MK: predicates on masks (CoPset) with sep = disjoint union, emp = {∅}, persistently P := P ∅,
later = id: a non-affine discrete BI. With W E := {E} (exact ownership of the mask tokens),
fupd E1 E2 P := W E1 -∗ W E2 ∗ P is a lawful, mask-sensitive BIFUpdate. -/
def MK := CoPset → Prop

theorem mU {p : Pos} {A B : CoPset} : p ∈ A ∪ B ↔ p ∈ A ∨ p ∈ B := mem_union
theorem me {p : Pos} {A B : CoPset} (e : A = B) : p ∈ A ↔ p ∈ B := by rw [e]
theorem dj0 {A : CoPset} : (∅ : CoPset) ## A := fun _ ⟨h, _⟩ => CoPset.mem_empty h
theorem djs {A B : CoPset} (d : A ## B) : B ## A := fun p ⟨h1, h2⟩ => d p ⟨h2, h1⟩

instance : BIBase MK where
  Entails P Q      := ∀ x, P x → Q x
  emp            x := x = ∅
  pure φ         _ := φ
  and P Q        x := P x ∧ Q x
  or P Q         x := P x ∨ Q x
  imp P Q        x := P x → Q x
  sForall Ψ      x := ∀ p, Ψ p → p x
  sExists Ψ      x := ∃ p, Ψ p ∧ p x
  sep P Q        x := ∃ a b, a ## b ∧ x = a ∪ b ∧ P a ∧ Q b
  wand P Q       x := ∀ y, x ## y → P y → Q (x ∪ y)
  persistently P _ := P ∅
  later P        x := P x

instance : COFE MK := COFE.ofDiscrete _

instance mkBI : BI MK where
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
  sep_mono h1 h2 _ := fun ⟨a, b, d, e, ha, hb⟩ => ⟨a, b, d, e, h1 a ha, h2 b hb⟩
  emp_sep := ⟨fun _ ⟨a, b, _, e, ha, hb⟩ => by
      have ha' : a = ∅ := ha
      subst ha'; rw [union_empty_left] at e; subst e; exact hb,
    fun x h => ⟨∅, x, dj0, union_empty_left.symm, rfl, h⟩⟩
  sep_symm _ := fun ⟨a, b, d, e, ha, hb⟩ => ⟨b, a, djs d, e.trans union_comm, hb, ha⟩
  sep_assoc_l _ := fun ⟨ab, c, d2, e1, ⟨a, b, d1, e2, ha, hb⟩, hc⟩ =>
    ⟨a, b ∪ c,
      fun p ⟨h1, h2⟩ => (mU.1 h2).elim (fun hb => d1 p ⟨h1, hb⟩)
        (fun hc => d2 p ⟨(me e2).2 (mU.2 (.inl h1)), hc⟩),
      by rw [e1, e2, union_assoc], ha, b, c,
      fun p ⟨h1, h2⟩ => d2 p ⟨(me e2).2 (mU.2 (.inr h1)), h2⟩, rfl, hb, hc⟩
  wand_intro h x hP y hd hQ := h (x ∪ y) ⟨x, y, hd, rfl, hP, hQ⟩
  wand_elim h _ := fun ⟨a, b, d, e, ha, hb⟩ => e ▸ h a ha b d hb
  persistently_mono h _ hP := h ∅ hP
  persistently_idem_2 _ h := h
  persistently_emp_2 _ _ := (rfl : (∅ : CoPset) = ∅)
  persistently_and_2 _ h := h
  persistently_absorb_l _ := fun ⟨_, _, _, _, ha, _⟩ => ha
  persistently_and_l x h := ⟨∅, x, dj0, union_empty_left.symm, h.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr fun _ => h

/-- Mask-ownership fancy update on MK. -/
def mfupd (E1 E2 : CoPset) (P : MK) : MK := fun S =>
  S ## E1 → ∃ B, E2 ## B ∧ S ∪ E1 = E2 ∪ B ∧ P B

theorem sub_eq {E1 E2 : CoPset} (h : E2 ⊆ E1) : E1 = E2 ∪ (E1 \ E2) :=
  CoPset.ext fun p => ⟨fun hp => by
      by_cases h2 : p ∈ E2
      · exact mU.2 (.inl h2)
      · exact mU.2 (.inr (mem_diff.2 ⟨hp, h2⟩)),
    fun hp => (mU.1 hp).elim (h p) (fun h' => (mem_diff.1 h').1)⟩

instance mkFupd : BIFUpdate MK where
  fupd := mfupd
  ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  subset {E1 E2} h S hS _ := ⟨E1 \ E2, fun p ⟨h1, h2⟩ => (mem_diff.1 h2).2 h1,
    by rw [show S = ∅ from hS, union_empty_left]; exact sub_eq h,
    fun _ => ⟨∅, djs dj0, by
      rw [union_comm, union_empty_right]; exact (sub_eq h).symm, rfl⟩⟩
  except0 _ h := h.elim (fun f => f.elim) id
  mono h _ hf hd := let ⟨B, d, e, hp⟩ := hf hd; ⟨B, d, e, h B hp⟩
  trans {E1 E2 E3} _ S hf hd :=
    let ⟨B, d, e, hq⟩ := hf hd
    let ⟨B', d', e', hp⟩ := hq (djs d)
    ⟨B', d', e.trans (union_comm.trans e'), hp⟩
  mask_frame_right_strong {E1 E2 Ef _} hdisj S hf hd := by
    have hd1 : S ## E1 := fun p ⟨h1, h2⟩ => hd p ⟨h1, mU.2 (.inl h2)⟩
    obtain ⟨B, d, e, hp⟩ := hf hd1
    have hin : ∀ p, p ∈ E2 ∨ p ∈ B → p ∈ Ef → False := fun p h hf' => by
      have h' : p ∈ S ∪ E1 := (me e).2 (mU.2 h)
      rcases mU.1 h' with h' | h'
      · exact hd p ⟨h', mU.2 (.inr hf')⟩
      · exact hdisj p ⟨h', hf'⟩
    refine ⟨B, fun p ⟨h1, h2⟩ => (mU.1 h1).elim (fun h1 => d p ⟨h1, h2⟩) (fun h1 => hin p (.inr h2) h1), ?_,
      hp (fun p ⟨h1, h2⟩ => hin p (.inl h1) h2)⟩
    apply CoPset.ext; intro p
    have := @me p _ _ e
    simp only [mU] at this ⊢
    constructor
    · rintro (h | h | h)
      · rcases this.1 (.inl h) with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases this.1 (.inr h) with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · exact .inl (.inr h)
    · rintro ((h | h) | h)
      · rcases this.2 (.inl h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact .inr (.inr h)
      · rcases this.2 (.inr h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
  frame_right {E1 E2} _ _ S := fun ⟨A, C, dAC, eS, hf, hR⟩ hd => by
    have hA : A ## E1 := fun p ⟨h1, h2⟩ => hd p ⟨(me eS).2 (mU.2 (.inl h1)), h2⟩
    have hC : C ## E1 := fun p ⟨h1, h2⟩ => hd p ⟨(me eS).2 (mU.2 (.inr h1)), h2⟩
    obtain ⟨B, d, e, hp⟩ := hf hA
    have hin : ∀ p, p ∈ E2 ∨ p ∈ B → p ∈ C → False := fun p h hc => by
      rcases mU.1 ((me e).2 (mU.2 h)) with h' | h'
      · exact dAC p ⟨h', hc⟩
      · exact hC p ⟨hc, h'⟩
    refine ⟨B ∪ C, fun p ⟨h1, h2⟩ => (mU.1 h2).elim (fun h2 => d p ⟨h1, h2⟩) (fun h2 => hin p (.inl h1) h2), ?_,
      B, C, fun p ⟨h1, h2⟩ => hin p (.inr h1) h2, rfl, hp, hR⟩
    rw [eS]
    apply CoPset.ext; intro p
    have := @me p _ _ e
    simp only [mU] at this ⊢
    constructor
    · rintro ((h | h) | h)
      · rcases this.1 (.inl h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact .inr (.inr h)
      · rcases this.1 (.inr h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
    · rintro (h | h | h)
      · rcases this.2 (.inl h) with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases this.2 (.inr h) with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · exact .inl (.inr h)

-- helper: constant-True fancy update on any BI (lawful; all laws hold trivially)
@[reducible] def topF (PROP : Type _) [BI PROP] : BIFUpdate PROP where
  fupd _ _ _ := iprop(True)
  ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  subset _ := true_intro
  except0 := true_intro
  mono _ := .rfl
  trans := true_intro
  mask_frame_right_strong _ := true_intro
  frame_right := true_intro
theorem mkFU : @BiEmbedFUpd MK MK _ _ (idEmb _) mkFupd mkFupd :=
  @BiEmbedFUpd.mk MK MK _ _ (idEmb _) mkFupd mkFupd (fun _ _ _ => .rfl)
-- helper: at empty masks the update of False fails at the empty mask
theorem mk_false : ¬ mfupd ∅ ∅ (iprop(False) : MK) ∅ := fun h =>
  let ⟨_, _, _, f⟩ := h dj0; f
-- helper: True ∗ (True -∗ True) holds at the empty mask
theorem mk_lhs : (iprop(True ∗ (True -∗ True)) : MK) ∅ :=
  ⟨∅, ∅, dj0, union_empty_left.symm, trivial, fun _ _ _ => trivial⟩

end W8c0

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.LawfulSet W8c0


-- `Iris.ProofMode.intoSep_bigSepL2_cons` idx 11: necessary (SiProp, Φ = True, l₁ = [()] with l₁' = [()] (h₁ dropped), l₂ = [()]: tail [∗list] over [()];[] is False)
theorem w8c0_1 : ¬ drop0% Iris.ProofMode.intoSep_bigSepL2_cons 11 := fun h =>
  ((@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] () [()] [()] () [] ⟨rfl⟩).into_sep 0
    ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoSep_bigSepL2_cons` idx 12: necessary (SiProp, Φ = True, l₂ = [()] with l₂' = [()] (h₂ dropped), l₁ = [()]: tail [∗list] over [];[()] is False)
theorem w8c0_2 : ¬ drop0% Iris.ProofMode.intoSep_bigSepL2_cons 12 := fun h =>
  ((@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] () [] [()] () [()] ⟨rfl⟩).into_sep 0
    ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.fromOr_affinely` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_3 : ¬ drop0% Iris.ProofMode.fromOr_affinely 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_or 0 (Or.inl ⟨trivial, trivial⟩)).2

-- `Iris.ProofMode.fromOr_intuitionistically` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_4 : ¬ drop0% Iris.ProofMode.fromOr_intuitionistically 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_or 0 (Or.inl ⟨trivial, trivial⟩)).2

-- `Iris.ProofMode.fromOr_absorbingly` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_5 : ¬ drop0% Iris.ProofMode.fromOr_absorbingly 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_or 0 (Or.inl ⟨trivial, trivial⟩)).2

-- `Iris.ProofMode.fromOr_persistently` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_6 : ¬ drop0% Iris.ProofMode.fromOr_persistently 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_or 0 (Or.inl trivial))

-- `Iris.ProofMode.intoOr_affinely` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_7 : ¬ drop0% Iris.ProofMode.intoOr_affinely 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(False)).into_or 0 ⟨trivial, trivial⟩).elim (·.2) (·.2)

-- `Iris.ProofMode.intoOr_intuitionistically` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_8 : ¬ drop0% Iris.ProofMode.intoOr_intuitionistically 6 := fun h =>
  ((@h SiProp _ _ iprop(True) iprop(False) iprop(False)).into_or 0 ⟨trivial, trivial⟩).elim (·.2) (·.2)

-- `Iris.ProofMode.intoOr_absorbingly` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_9 : ¬ drop0% Iris.ProofMode.intoOr_absorbingly 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(False)).into_or 0 ⟨trivial, trivial⟩).elim (·.2) (·.2)

-- `Iris.ProofMode.intoOr_persistently` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_10 : ¬ drop0% Iris.ProofMode.intoOr_persistently 6 := fun h =>
  ((@h SiProp _ _ iprop(True) iprop(False) iprop(False)).into_or 0 trivial).elim id id

-- `Iris.ProofMode.intoPersistently_persistently` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_11 : ¬ drop0% Iris.ProofMode.intoPersistently_persistently 5 := fun h =>
  (@h SiProp false _ iprop(True) iprop(False)).into_persistently 0 trivial

-- `Iris.ProofMode.intoPersistently_affinely` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_12 : ¬ drop0% Iris.ProofMode.intoPersistently_affinely 5 := fun h =>
  (@h SiProp false _ iprop(True) iprop(False)).into_persistently 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoPersistently_intuitionistically` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_13 : ¬ drop0% Iris.ProofMode.intoPersistently_intuitionistically 5 := fun h =>
  (@h SiProp false _ iprop(True) iprop(False)).into_persistently 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoAbsorbingly_absorbing` idx 3: removable (P ⊢ <absorb> P holds in every BI (absorbingly_intro), so the instance needs no Absorbing P)
theorem w8c0_14 : drop% Iris.ProofMode.intoAbsorbingly_absorbing 3 := by
  intro PROP _ P; exact ⟨absorbingly_intro⟩


-- `Iris.ProofMode.fromAssumption_persistently_right` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_15 : ¬ drop0% Iris.ProofMode.fromAssumption_persistently_right 5 := fun h =>
  (@h SiProp _ .in iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAssumption_affinely_right` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_16 : ¬ drop0% Iris.ProofMode.fromAssumption_affinely_right 5 := fun h =>
  ((@h SiProp _ .in iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.fromAssumption_intuitionistically_right` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_17 : ¬ drop0% Iris.ProofMode.fromAssumption_intuitionistically_right 5 := fun h =>
  ((@h SiProp _ .in iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.fromAssumption_absorbingly_right` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_18 : ¬ drop0% Iris.ProofMode.fromAssumption_absorbingly_right 6 := fun h =>
  ((@h SiProp false _ .in iprop(True) iprop(False)).from_assumption 0 trivial).2

-- `Iris.ProofMode.fromAssumption_intuitionistically_left` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_19 : ¬ drop0% Iris.ProofMode.fromAssumption_intuitionistically_left 5 := fun h =>
  (@h SiProp false _ iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAssumption_intuitionistically_l_true` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_20 : ¬ drop0% Iris.ProofMode.fromAssumption_intuitionistically_l_true 5 := fun h =>
  (@h SiProp false _ iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAssumption_persistently_l_true` idx 4: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_21 : ¬ drop0% Iris.ProofMode.fromAssumption_persistently_l_true 4 := fun h =>
  (@h SiProp _ iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAssumption_persistently_l_false` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_22 : ¬ drop0% Iris.ProofMode.fromAssumption_persistently_l_false 5 := fun h =>
  (@h SiProp _ _ iprop(True) iprop(False)).from_assumption 0 trivial

-- `Iris.ProofMode.fromAssumption_affinely_left` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_23 : ¬ drop0% Iris.ProofMode.fromAssumption_affinely_left 5 := fun h =>
  (@h SiProp false _ iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAssumption_forall` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_24 : ¬ drop0% Iris.ProofMode.fromAssumption_forall 7 := fun h =>
  (@h SiProp True false _ (fun _ => iprop(True)) trivial iprop(False)).from_assumption 0
    (SiProp.forall_holds.2 fun _ => trivial)

-- `Iris.ProofMode.fromAssumption_and_left` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_25 : ¬ drop0% Iris.ProofMode.fromAssumption_and_left 6 := fun h =>
  (@h SiProp _ false iprop(True) iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAssumption_and_right` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_26 : ¬ drop0% Iris.ProofMode.fromAssumption_and_right 6 := fun h =>
  (@h SiProp _ false iprop(True) iprop(True) iprop(False)).from_assumption 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAssumption_tforall` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_27 : ¬ drop0% Iris.ProofMode.fromAssumption_tforall 7 := fun h =>
  (@h SiProp .nil false _ (fun _ => iprop(True)) PUnit.unit iprop(False)).from_assumption 0 trivial

-- `Iris.ProofMode.intoPure_pure_and` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_28 : ¬ drop0% Iris.ProofMode.intoPure_pure_and 6 := fun h =>
  ((@h SiProp False True _ iprop(True) iprop(True) ⟨fun _ _ => trivial⟩).into_pure 0 ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.intoPure_pure_and` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_29 : ¬ drop0% Iris.ProofMode.intoPure_pure_and 7 := fun h =>
  ((@h SiProp True False _ iprop(True) iprop(True) ⟨fun _ _ => trivial⟩).into_pure 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoPure_pure_or` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_30 : ¬ drop0% Iris.ProofMode.intoPure_pure_or 6 := fun h =>
  ((@h SiProp False False _ iprop(True) iprop(False) ⟨fun _ h => h⟩).into_pure 0 (Or.inl trivial)).elim id id

-- `Iris.ProofMode.intoPure_pure_or` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_31 : ¬ drop0% Iris.ProofMode.intoPure_pure_or 7 := fun h =>
  ((@h SiProp False False _ iprop(False) iprop(True) ⟨fun _ h => h⟩).into_pure 0 (Or.inr trivial)).elim id id

-- `Iris.ProofMode.intoPure_pure_imp` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_32 : ¬ drop0% Iris.ProofMode.intoPure_pure_imp 7 := fun h =>
  (@h SiProp false True False _ iprop(False) iprop(False) (@Iris.Std.TCOr.l _ _ Iris.Std.TCEq.refl)
    ⟨fun _ h => h⟩).into_pure 0 (fun _ _ h => h) trivial

-- `Iris.ProofMode.intoPure_pure_imp` idx 9: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_33 : ¬ drop0% Iris.ProofMode.intoPure_pure_imp 9 := fun h =>
  (@h SiProp false True False _ iprop(True) iprop(True) ⟨fun _ _ => trivial⟩
    (@Iris.Std.TCOr.l _ _ Iris.Std.TCEq.refl)).into_pure 0 (fun _ _ _ => trivial) trivial

-- `Iris.ProofMode.intoPure_exists` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_34 : ¬ drop0% Iris.ProofMode.intoPure_exists 5 := fun h =>
  match ((@h SiProp True _ (fun _ => iprop(True)) (fun _ => False)).into_pure 0
    (SiProp.exists_holds.2 ⟨trivial, trivial⟩)) with
  | ⟨_, hx⟩ => hx

-- `Iris.ProofMode.intoPure_pure_sep` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_35 : ¬ drop0% Iris.ProofMode.intoPure_pure_sep 6 := fun h =>
  ((@h SiProp False True _ iprop(True) iprop(True) ⟨fun _ _ => trivial⟩).into_pure 0 ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.intoPure_pure_sep` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_36 : ¬ drop0% Iris.ProofMode.intoPure_pure_sep 7 := fun h =>
  ((@h SiProp True False _ iprop(True) iprop(True) ⟨fun _ _ => trivial⟩).into_pure 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoPure_affinely` idx 4: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_37 : ¬ drop0% Iris.ProofMode.intoPure_affinely 4 := fun h =>
  (@h SiProp _ iprop(True) False).into_pure 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoPure_intuitionistically` idx 4: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_38 : ¬ drop0% Iris.ProofMode.intoPure_intuitionistically 4 := fun h =>
  (@h SiProp _ iprop(True) False).into_pure 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoPure_absorbingly` idx 4: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_39 : ¬ drop0% Iris.ProofMode.intoPure_absorbingly 4 := fun h =>
  (@h SiProp _ iprop(True) False).into_pure 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoPure_persistently` idx 4: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_40 : ¬ drop0% Iris.ProofMode.intoPure_persistently 4 := fun h =>
  (@h SiProp _ iprop(True) False).into_pure 0 trivial

-- `Iris.ProofMode.intoPure_forall` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_41 : ¬ drop0% Iris.ProofMode.intoPure_forall 5 := fun h =>
  (@h SiProp True _ (fun _ => iprop(True)) (fun _ => False)).into_pure 0
    (SiProp.forall_holds.2 fun _ => trivial) trivial

-- `Iris.ProofMode.intoPure_pure_wand` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_42 : ¬ drop0% Iris.ProofMode.intoPure_pure_wand 7 := fun h =>
  (@h SiProp _ false True False iprop(False) iprop(False) ⟨fun _ h => h⟩).into_pure 0 (fun _ _ h => h) trivial

-- `Iris.ProofMode.intoPure_pure_wand` idx 8: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_43 : ¬ drop0% Iris.ProofMode.intoPure_pure_wand 8 := fun h =>
  (@h SiProp _ false True False iprop(True) iprop(True) ⟨fun _ _ => trivial⟩).into_pure 0
    (fun _ _ _ => trivial) trivial

-- `Iris.ProofMode.intoPure_tforall` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_44 : ¬ drop0% Iris.ProofMode.intoPure_tforall 5 := fun h =>
  (@h SiProp .nil _ (fun _ => iprop(True)) (fun _ => False)).into_pure 0 trivial

-- `Iris.ProofMode.intoPure_texist` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_45 : ¬ drop0% Iris.ProofMode.intoPure_texist 5 := fun h =>
  (@h SiProp .nil _ (fun _ => iprop(True)) (fun _ => False)).into_pure 0 trivial


-- `Iris.ProofMode.intoOr_intuitionistically` idx 2: necessary (KB (affine Kripke BI, persistently = box over worlds, no BIPersistentlyExist): <pers>(kT ∨ kF) holds at world true but neither <pers>kT nor <pers>kF)
theorem w8c0_46 : ¬ drop0% Iris.ProofMode.intoOr_intuitionistically 2 := fun h =>
  ((@h KB _ iprop(kT ∨ kF) kT kF ⟨.rfl⟩).into_or true ⟨trivial, kb_or⟩).elim
    (fun h => kb_not_or (Or.inl h.2)) (fun h => kb_not_or (Or.inr h.2))

-- `Iris.ProofMode.intoOr_persistently` idx 2: necessary (KB (affine Kripke BI, persistently = box over worlds, no BIPersistentlyExist): <pers>(kT ∨ kF) holds at world true but neither <pers>kT nor <pers>kF)
theorem w8c0_47 : ¬ drop0% Iris.ProofMode.intoOr_persistently 2 := fun h =>
  kb_not_or ((@h KB _ iprop(kT ∨ kF) kT kF ⟨.rfl⟩).into_or true kb_or)

-- `Iris.ProofMode.fromAssumption_persistently_l_false` idx 2: necessary (GB (non-affine Boolean BI): with P = True, Q = □True the premise holds but <pers>True ⊬ □True (fails at world true))
theorem w8c0_48 : ¬ drop0% Iris.ProofMode.fromAssumption_persistently_l_false 2 := fun h =>
  Bool.noConfusion (((@h GB _ iprop(True) iprop(□ True) ⟨.rfl⟩).from_assumption true trivial).1 : true = false)

-- `Iris.ProofMode.fromPure_pure_and` idx 9: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_49 : ¬ drop0% Iris.ProofMode.fromPure_pure_and 9 := fun h =>
  ((@h SiProp .in false false True True _ iprop(False) iprop(True) ⟨fun _ _ => trivial⟩).from_pure 0
    ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.fromPure_pure_and` idx 10: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_50 : ¬ drop0% Iris.ProofMode.fromPure_pure_and 10 := fun h =>
  ((@h SiProp .in false false True True _ iprop(True) iprop(False) ⟨fun _ _ => trivial⟩).from_pure 0
    ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.fromPure_pure_or` idx 9: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_51 : ¬ drop0% Iris.ProofMode.fromPure_pure_or 9 := fun h =>
  ((@h SiProp .in false false True False _ iprop(False) iprop(False) ⟨fun _ h => h⟩).from_pure 0
    (Or.inl trivial)).elim id id

-- `Iris.ProofMode.fromPure_pure_or` idx 10: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_52 : ¬ drop0% Iris.ProofMode.fromPure_pure_or 10 := fun h =>
  ((@h SiProp .in false false False True _ iprop(False) iprop(False) ⟨fun _ h => h⟩).from_pure 0
    (Or.inr trivial)).elim id id

-- `Iris.ProofMode.fromPure_pure_imp` idx 8: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_53 : ¬ drop0% Iris.ProofMode.fromPure_pure_imp 8 := fun h =>
  (@h SiProp .in false False False _ iprop(True) iprop(False) ⟨fun _ h => h⟩).from_pure 0
    (fun h => h) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromPure_pure_imp` idx 9: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_54 : ¬ drop0% Iris.ProofMode.fromPure_pure_imp 9 := fun h =>
  (@h SiProp .in false True True _ iprop(True) iprop(False) ⟨fun _ _ => trivial⟩).from_pure 0
    (fun _ => trivial) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromPure_exists` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_55 : ¬ drop0% Iris.ProofMode.fromPure_exists 7 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp True .in false _ (fun _ => iprop(False)) (fun _ => True)).from_pure 0
    ⟨trivial, trivial⟩) with
  | ⟨_, hx⟩ => hx

-- `Iris.ProofMode.fromPure_forall` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_56 : ¬ drop0% Iris.ProofMode.fromPure_forall 7 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp True .in false _ (fun _ => iprop(False)) (fun _ => True)).from_pure 0
    (fun _ => trivial)) trivial

-- `Iris.ProofMode.fromPure_pure_sep_true` idx 9: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_57 : ¬ drop0% Iris.ProofMode.fromPure_pure_sep_true 9 := fun h =>
  ((@h SiProp .in false false True True _ iprop(False) iprop(True) ⟨fun _ _ => trivial⟩).from_pure 0
    ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.fromPure_pure_sep_true` idx 10: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_58 : ¬ drop0% Iris.ProofMode.fromPure_pure_sep_true 10 := fun h =>
  ((@h SiProp .in false false True True _ iprop(True) iprop(False) ⟨fun _ _ => trivial⟩).from_pure 0
    ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.fromPure_persistently` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_59 : ¬ drop0% Iris.ProofMode.fromPure_persistently 6 := fun h =>
  (@h SiProp .in _ iprop(False) false True).from_pure 0 trivial

-- `Iris.ProofMode.fromPure_affinely_true` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_60 : ¬ drop0% Iris.ProofMode.fromPure_affinely_true 6 := fun h =>
  ((@h SiProp .in false _ iprop(False) True).from_pure 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.fromPure_intuitionistically_true` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_61 : ¬ drop0% Iris.ProofMode.fromPure_intuitionistically_true 6 := fun h =>
  ((@h SiProp .in false _ iprop(False) True).from_pure 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.fromPure_absorbingly` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_62 : ¬ drop0% Iris.ProofMode.fromPure_absorbingly 6 := fun h =>
  ((@h SiProp .in false _ iprop(False) True).from_pure 0 trivial).2

-- `Iris.ProofMode.fromPure_tforall` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_63 : ¬ drop0% Iris.ProofMode.fromPure_tforall 7 := fun h =>
  (@h SiProp .in .nil false _ (fun _ => iprop(False)) (fun _ => True)).from_pure 0 trivial

-- `Iris.ProofMode.fromPure_texist` idx 7: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_64 : ¬ drop0% Iris.ProofMode.fromPure_texist 7 := fun h =>
  (@h SiProp .in .nil false _ (fun _ => iprop(False)) (fun _ => True)).from_pure 0 trivial

-- `Iris.ProofMode.fromModal_intuitionistically_affine_bi` idx 2: necessary (GB (non-affine): <pers>True ⊬ □True at world true)
theorem w8c0_65 : ¬ drop0% Iris.ProofMode.fromModal_intuitionistically_affine_bi 2 := fun h =>
  Bool.noConfusion (((@h GB _ iprop(True) .in).from_modal trivial true trivial).1 : true = false)

-- `Iris.ProofMode.elimModal_wand` idx 11: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_66 : ¬ drop0% Iris.ProofMode.elimModal_wand 11 := fun h =>
  (@h SiProp _ True false false .in iprop(True) iprop(True) iprop(False) iprop(True) iprop(True)).elim_modal
    trivial 0 ⟨trivial, fun _ _ _ _ _ _ => trivial⟩ 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.elimModal_wandM` idx 11: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_67 : ¬ drop0% Iris.ProofMode.elimModal_wandM 11 := fun h =>
  (@h SiProp _ True false false .in iprop(True) iprop(True) iprop(False) iprop(True) none).elim_modal
    trivial 0 ⟨trivial, fun _ _ _ => trivial⟩

-- `Iris.ProofMode.elimModal_forall` idx 11: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_68 : ¬ drop0% Iris.ProofMode.elimModal_forall 11 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp True _ True false false .in iprop(True) iprop(True) (fun _ => iprop(False))
    (fun _ => iprop(True))).elim_modal trivial 0 ⟨trivial, fun _ _ _ => SiProp.forall_holds.2 fun _ => trivial⟩)
    trivial

-- `Iris.ProofMode.elimModal_absorbingly_here` idx 6: necessary (GB (non-affine): P = Q = emp (not absorbing); <absorb>emp ∗ (emp -∗ emp) holds at world true, emp does not)
theorem w8c0_69 : ¬ drop0% Iris.ProofMode.elimModal_absorbingly_here 6 := fun h =>
  Bool.noConfusion ((@h GB _ false .in iprop(emp) iprop(emp)).elim_modal trivial true
    ⟨true, false, rfl, ⟨true, false, rfl, trivial, rfl⟩, fun y hy => by cases (hy : y = false); rfl⟩ : true = false)

-- `Iris.ProofMode.elimModal_tforall` idx 11: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_70 : ¬ drop0% Iris.ProofMode.elimModal_tforall 11 := fun h =>
  (@h SiProp .nil _ True false false .in iprop(True) iprop(True) (fun _ => iprop(False))
    (fun _ => iprop(True))).elim_modal trivial 0 ⟨trivial, fun _ _ _ => trivial⟩

-- `Iris.ProofMode.addModal_wand_mp` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_71 : ¬ drop0% Iris.ProofMode.addModal_wand_mp 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) iprop(True)) 0 ⟨trivial, fun _ _ hf => hf.elim⟩ 0
    (Nat.le_refl 0) trivial

-- `Iris.ProofMode.addModal_wand` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_72 : ¬ drop0% Iris.ProofMode.addModal_wand 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) iprop(True)).add_modal 0 ⟨trivial, fun _ _ hf => hf.elim⟩ 0
    (Nat.le_refl 0) trivial

-- `Iris.ProofMode.addModal_wandM` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_73 : ¬ drop0% Iris.ProofMode.addModal_wandM 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) none).add_modal 0 ⟨trivial, fun _ _ hf => hf.elim⟩

-- `Iris.ProofMode.addModal_forall` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_74 : ¬ drop0% Iris.ProofMode.addModal_forall 6 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp Unit _ iprop(True) iprop(False) (fun _ => iprop(False))).add_modal 0
    ⟨trivial, fun _ _ hf => hf.elim⟩) ()

-- `Iris.ProofMode.addModal_tforall` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_75 : ¬ drop0% Iris.ProofMode.addModal_tforall 6 := fun h =>
  (@h SiProp .nil _ iprop(True) iprop(False) (fun _ => iprop(False))).add_modal 0
    ⟨trivial, fun _ _ hf => hf.elim⟩

-- `Iris.ProofMode.combineSepAs_affinely` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_76 : ¬ drop0% Iris.ProofMode.combineSepAs_affinely 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_as 0
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩).2

-- `Iris.ProofMode.combineSepAs_intuitionistically` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_77 : ¬ drop0% Iris.ProofMode.combineSepAs_intuitionistically 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_as 0
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩).2

-- `Iris.ProofMode.combineSepAs_absorbingly` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_78 : ¬ drop0% Iris.ProofMode.combineSepAs_absorbingly 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_as 0
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩).2

-- `Iris.ProofMode.combineSepAs_persistently` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_79 : ¬ drop0% Iris.ProofMode.combineSepAs_persistently 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_as 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.combineSepGives_affinely` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_80 : ¬ drop0% Iris.ProofMode.combineSepGives_affinely 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_gives 0
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

-- `Iris.ProofMode.combineSepGives_intuitionistically` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_81 : ¬ drop0% Iris.ProofMode.combineSepGives_intuitionistically 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_gives 0
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

-- `Iris.ProofMode.combineSepGives_absorbingly` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_82 : ¬ drop0% Iris.ProofMode.combineSepGives_absorbingly 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_gives 0
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

-- `Iris.ProofMode.combineSepGives_persistently` idx 5: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_83 : ¬ drop0% Iris.ProofMode.combineSepGives_persistently 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False)).combine_sep_gives 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoIH_forall` idx 6: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_84 : ¬ drop0% Iris.ProofMode.intoIH_forall 6 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp True _ (fun _ => True) iprop(True) (fun _ => iprop(False))).into_ih
    (fun _ => trivial) 0 ⟨trivial, trivial⟩) trivial

-- `Iris.ProofMode.intoIH_imp` idx 8: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_85 : ¬ drop0% Iris.ProofMode.intoIH_imp 8 := fun h =>
  (@h SiProp _ True True iprop(True) iprop(<affine> ⌜True⌝) iprop(False) ⟨.rfl⟩).into_ih (fun _ => trivial) 0
    ⟨trivial, trivial⟩ 0 (Nat.le_refl 0) ⟨trivial, trivial⟩

-- `Iris.ProofMode.asEmpValid_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_86 : ¬ drop0% Iris.ProofMode.asEmpValid_embed 8 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) .into True iprop(False)).as_emp_valid.1 rfl trivial 0 trivial

-- `Iris.ProofMode.fromModal_id_embed` idx 11: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_87 : ¬ drop0% Iris.ProofMode.fromModal_id_embed 11 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) Unit True .in () iprop(False) iprop(True)).from_modal trivial 0 trivial

-- `Iris.ProofMode.fromModal_affinely_embed` idx 11: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_88 : ¬ drop0% Iris.ProofMode.fromModal_affinely_embed 11 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) Unit True .in () iprop(False) iprop(True)).from_modal trivial 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromModal_persistently_embed` idx 11: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_89 : ¬ drop0% Iris.ProofMode.fromModal_persistently_embed 11 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) Unit True .in () iprop(False) iprop(True)).from_modal trivial 0 trivial

-- `Iris.ProofMode.fromModal_intuitionistically_embed` idx 11: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_90 : ¬ drop0% Iris.ProofMode.fromModal_intuitionistically_embed 11 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) Unit True .in () iprop(False) iprop(True)).from_modal trivial 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoEmbed_affinely` idx 10: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_91 : ¬ drop0% Iris.ProofMode.intoEmbed_affinely 10 := fun h =>
  ((@h SiProp SiProp _ _ (idEmb SiProp) idBupd idBupd (idBU idBupd) iprop(True) iprop(False)).into_embed 0
    ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoPure_embed` idx 7: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_92 : ¬ drop0% Iris.ProofMode.intoPure_embed 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) iprop(True) False).into_pure 0 trivial

-- `Iris.ProofMode.fromPure_embed` idx 9: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_93 : ¬ drop0% Iris.ProofMode.fromPure_embed 9 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) false iprop(False) .in True).from_pure 0 trivial

-- `Iris.ProofMode.intoPersistently_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_94 : ¬ drop0% Iris.ProofMode.intoPersistently_embed 8 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) false iprop(True) iprop(False)).into_persistently 0 trivial

-- `Iris.ProofMode.intoWand_embed` idx 11: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_95 : ¬ drop0% Iris.ProofMode.intoWand_embed 11 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) false false (.matching .argument) iprop(True) iprop(True) iprop(False)).into_wand
    0 trivial 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_affine_embed_true` idx 10: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_96 : ¬ drop0% Iris.ProofMode.intoWand_affine_embed_true 10 := fun h =>
  ((@h SiProp SiProp _ _ (idEmb SiProp) .argument false iprop(True) iprop(False) iprop(True)).into_wand
    0 ⟨trivial, trivial⟩ 0 (Nat.le_refl 0) ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.fromWand_embed` idx 9: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_97 : ¬ drop0% Iris.ProofMode.fromWand_embed 9 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) .in iprop(False) iprop(False) iprop(True)).from_wand 0
    (fun _ _ _ => trivial)

-- `Iris.ProofMode.fromImp_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_98 : ¬ drop0% Iris.ProofMode.fromImp_embed 8 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) iprop(False) iprop(False) iprop(True)).from_imp 0
    (fun _ _ _ => trivial)

-- `Iris.ProofMode.fromAnd_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_99 : ¬ drop0% Iris.ProofMode.fromAnd_embed 8 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) iprop(False) iprop(True) iprop(True)).from_and 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromSep_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_100 : ¬ drop0% Iris.ProofMode.fromSep_embed 8 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) iprop(False) iprop(True) iprop(True)).from_sep 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.combineSepGives_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_101 : ¬ drop0% Iris.ProofMode.combineSepGives_embed 8 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) iprop(True) iprop(True) iprop(False)).combine_sep_gives 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoAnd_embed` idx 9: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_102 : ¬ drop0% Iris.ProofMode.intoAnd_embed 9 := fun h =>
  ((@h SiProp SiProp _ _ (idEmb SiProp) false iprop(True) iprop(False) iprop(True)).into_and 0 trivial).1

-- `Iris.ProofMode.intoSep_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_103 : ¬ drop0% Iris.ProofMode.intoSep_embed 8 := fun h =>
  ((@h SiProp SiProp _ _ (idEmb SiProp) iprop(True) iprop(False) iprop(True)).into_sep 0 trivial).1

-- `Iris.ProofMode.fromOr_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_104 : ¬ drop0% Iris.ProofMode.fromOr_embed 8 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) iprop(False) iprop(True) iprop(True)).from_or 0 (Or.inl trivial)

-- `Iris.ProofMode.intoOr_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_105 : ¬ drop0% Iris.ProofMode.intoOr_embed 8 := fun h =>
  ((@h SiProp SiProp _ _ (idEmb SiProp) iprop(True) iprop(False) iprop(False)).into_or 0 trivial).elim id id

-- `Iris.ProofMode.fromExists_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_106 : ¬ drop0% Iris.ProofMode.fromExists_embed 8 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) True iprop(False) (fun _ => iprop(True))).from_exists 0
    (SiProp.exists_holds.2 ⟨trivial, trivial⟩)

-- `Iris.ProofMode.intoExists_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_107 : ¬ drop0% Iris.ProofMode.intoExists_embed 8 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp SiProp _ _ (idEmb SiProp) True iprop(True)
    (fun _ => iprop(False))).into_exists 0 trivial) with
  | ⟨_, hx⟩ => hx

-- `Iris.ProofMode.intoForall_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_108 : ¬ drop0% Iris.ProofMode.intoForall_embed 8 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp SiProp _ _ (idEmb SiProp) True iprop(True)
    (fun _ => iprop(False))).into_forall 0 trivial) trivial

-- `Iris.ProofMode.fromForall_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_109 : ¬ drop0% Iris.ProofMode.fromForall_embed 8 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) True iprop(False) (fun _ => iprop(True))).from_forall 0
    (SiProp.forall_holds.2 fun _ => trivial)

-- `Iris.ProofMode.isExcept0_embed` idx 7: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_110 : ¬ drop0% Iris.ProofMode.isExcept0_embed 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) (idLat SiProp) iprop(False)).is_except0 0 (Or.inl trivial)

-- `Iris.ProofMode.isExcept0_embed` idx 5: necessary (AU (affine BI on Unit → Prop, later = id) embedded into SiProp as pure props: P = False is except-0 in AU but ◇⎡False⎤ holds at step 0)
theorem w8c0_111 : ¬ drop0% Iris.ProofMode.isExcept0_embed 5 := fun h =>
  (@h AU SiProp _ _ auE iprop(False) ⟨fun _ h => h.elim id id⟩).is_except0 0 (Or.inl trivial)

-- `Iris.ProofMode.fromModal_later_embed` idx 5: necessary (AU embedded into SiProp as pure props: FromModal (▷) False False holds in AU (later = id), but ▷⎡False⎤ holds at step 0)
theorem w8c0_112 : ¬ drop0% Iris.ProofMode.fromModal_later_embed 5 := fun h =>
  (@h AU SiProp _ _ auE Unit True .in () 1 iprop(False) iprop(False) ⟨fun _ _ h => h⟩).from_modal trivial 0
    trivial

-- `Iris.ProofMode.intoExcept0_embed` idx 5: necessary (delay embedding dl of SiProp: P = ▷False, Q = False; dl(▷False) holds at step 1, ◇ dl False does not)
theorem w8c0_113 : ¬ drop0% Iris.ProofMode.intoExcept0_embed 5 := fun h =>
  ((@h SiProp SiProp _ _ delayE iprop(▷ False) iprop(False) ⟨fun _ h => Or.inl h⟩).into_except0 1
    trivial).elim id id

-- `Iris.ProofMode.intoExcept0_embed` idx 8: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_114 : ¬ drop0% Iris.ProofMode.intoExcept0_embed 8 := fun h =>
  ((@h SiProp SiProp _ _ (idEmb SiProp) (idLat SiProp) iprop(True) iprop(False)).into_except0 1
    trivial).elim id id

-- `Iris.ProofMode.intoLater_embed` idx 5: necessary (delay embedding dl of SiProp: n = 1, P = ▷False, Q = False; dl(▷False) holds at step 1, ▷ dl False does not)
theorem w8c0_115 : ¬ drop0% Iris.ProofMode.intoLater_embed 5 := fun h =>
  (@h SiProp SiProp _ _ delayE 1 iprop(▷ False) iprop(False) false ⟨fun _ h => h⟩).into_laterN 1 trivial

-- `Iris.ProofMode.intoLater_embed` idx 10: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_116 : ¬ drop0% Iris.ProofMode.intoLater_embed 10 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) (idLat SiProp) 0 iprop(True) iprop(False) false).into_laterN 0 trivial

-- `Iris.ProofMode.fromModal_plainly_embed` idx 12: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_117 : ¬ drop0% Iris.ProofMode.fromModal_plainly_embed 12 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) (idSbi SiProp) Unit True .in () iprop(False) iprop(True)).from_modal
    trivial 0 ((show (iprop(True) : SiProp) ⊢ iprop(■ True) from plainly_pure.2) 0 trivial)

-- `Iris.ProofMode.intoInternalEq_embed` idx 5: necessary (delay embedding dl of SiProp: P = (s0 ≡ True); dl P holds at step 1 but s0 ≢{1} True)
theorem w8c0_118 : ¬ drop0% Iris.ProofMode.intoInternalEq_embed 5 := fun h => by
  have H : s0 ≡{1}≡ sT := (@h SiProp SiProp _ _ delayE SiProp _ s0 sT iprop(s0 ≡ sT) ⟨.rfl⟩).into_internal_eq 1
    (show s0 ≡{0}≡ sT from fun {m} hm => ⟨fun _ => trivial, fun _ => by show m = 0; omega⟩)
  exact Nat.one_ne_zero ((H (m := 1) (Nat.le_refl 1)).2 trivial)

-- `Iris.ProofMode.intoInternalEq_embed` idx 11: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_119 : ¬ drop0% Iris.ProofMode.intoInternalEq_embed 11 := fun h => by
  have H : s0 ≡{1}≡ sT := (@h SiProp SiProp _ _ (idEmb SiProp) (idSbi SiProp) SiProp _ s0 sT iprop(True)).into_internal_eq 1 trivial
  exact Nat.one_ne_zero ((H (m := 1) (Nat.le_refl 1)).2 trivial)

-- `Iris.ProofMode.elimModal_embed_bupd_goal` idx 7: necessary (identity embedding SiProp → SiProp with bupd = id on PROP1, constant True on PROP2: premise trivial, conclusion True ∗ (True -∗ True) ⊢ False)
theorem w8c0_120 : ¬ drop0% Iris.ProofMode.elimModal_embed_bupd_goal 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) idBupd topBupd True false .in false iprop(True) iprop(True) iprop(False)
    iprop(True) ⟨fun _ _ _ => trivial⟩).elim_modal trivial 0 ⟨trivial, fun _ _ _ => trivial⟩

-- `Iris.ProofMode.elimModal_embed_bupd_goal` idx 16: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_121 : ¬ drop0% Iris.ProofMode.elimModal_embed_bupd_goal 16 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) idBupd idBupd (idBU idBupd) True false .in false iprop(True) iprop(True)
    iprop(False) iprop(True)).elim_modal trivial 0 ⟨trivial, fun _ _ _ => trivial⟩

-- `Iris.ProofMode.elimModal_embed_bupd_hyp` idx 7: necessary (identity embedding with bupd constant True on PROP1, id on PROP2: premise has P = False, conclusion True ∗ (True -∗ True) ⊢ False)
theorem w8c0_122 : ¬ drop0% Iris.ProofMode.elimModal_embed_bupd_hyp 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) topBupd idBupd True false .in false iprop(False) iprop(True) iprop(False)
    iprop(True) ⟨fun _ _ h => h.1⟩).elim_modal trivial 0 ⟨trivial, fun _ _ _ => trivial⟩

-- `Iris.ProofMode.elimModal_embed_bupd_hyp` idx 16: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_123 : ¬ drop0% Iris.ProofMode.elimModal_embed_bupd_hyp 16 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) idBupd idBupd (idBU idBupd) True false .in false iprop(True) iprop(True)
    iprop(False) iprop(True)).elim_modal trivial 0 ⟨trivial, fun _ _ _ => trivial⟩

-- `Iris.ProofMode.addModal_embed_bupd_goal` idx 7: necessary (identity embedding with bupd = id on PROP1, constant True on PROP2: P = True, P' = Q = False)
theorem w8c0_124 : ¬ drop0% Iris.ProofMode.addModal_embed_bupd_goal 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) idBupd topBupd iprop(True) iprop(False) iprop(False)
    ⟨fun _ _ => trivial⟩).add_modal 0 ⟨trivial, fun _ _ hf => hf.elim⟩

-- `Iris.ProofMode.addModal_embed_bupd_goal` idx 11: necessary (identity embedding of SiProp into itself; conclusion reduces to the dropped class at values making it True ⊢ False)
theorem w8c0_125 : ¬ drop0% Iris.ProofMode.addModal_embed_bupd_goal 11 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) idBupd idBupd (idBU idBupd) iprop(True) iprop(False)
    iprop(False)).add_modal 0 ⟨trivial, fun _ _ hf => hf.elim⟩

-- `Iris.ProofMode.intoPure_internalCmraValid` idx 4: necessary (UV (one-point ORA valid only at step 0, not discrete): ✓ a holds at step 0 in SiProp, ⌜✓ a⌝ is False)
theorem w8c0_126 : ¬ drop0% Iris.ProofMode.intoPure_internalCmraValid 4 := fun h =>
  (@h SiProp _ UV _ ⟨⟩).into_pure 0 (rfl : (0 : Nat) = 0)

-- `Iris.ProofMode.intoPure_internalCmraOrder` idx 4: necessary (UZ (one-point ORA, order only at step 0): a ≼ₒ a holds at step 0 in SiProp, ⌜a ≼ₒ a⌝ is False)
theorem w8c0_127 : ¬ drop0% Iris.ProofMode.intoPure_internalCmraOrder 4 := fun h =>
  (@h SiProp _ UZ _ ⟨⟩ ⟨⟩).into_pure 0 (rfl : (0 : Nat) = 0)

-- `Iris.ProofMode.intoPure_internalCmraIncluded` idx 4: necessary (NU (Bool, op and, all elements agree at step 0): false ≼{0} true but not false ≼ true)
theorem w8c0_128 : ¬ drop0% Iris.ProofMode.intoPure_internalCmraIncluded 4 := fun h => by
  obtain ⟨c, hc⟩ := (@h SiProp _ NU _ ⟨false⟩ ⟨true⟩).into_pure 0 (incH' ⟨⟨true⟩, .inl rfl⟩)
  cases c with | mk b => exact absurd (congrArg NU.b hc) (by cases b <;> decide)

-- `Iris.ProofMode.elimModal_embed_fupd_hyp` idx 18: necessary (identity embedding of SiProp with constant-True fupd on both sides: conclusion True ∗ (True -∗ True) ⊢ False)
theorem w8c0_129 : ¬ drop0% Iris.ProofMode.elimModal_embed_fupd_hyp 18 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) topFupd topFupd topFU True false .in false ⊤ ⊤ iprop(False) iprop(True)
    iprop(False) iprop(True)).elim_modal trivial 0 ⟨trivial, fun _ _ _ => trivial⟩

-- `Iris.ProofMode.intoIH_listForall₂` idx 9: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_130 : ¬ drop0% Iris.ProofMode.intoIH_listForall₂ 9 := fun h =>
  ((@h SiProp Unit Unit _ (fun _ _ => True) [()] [()] iprop(True) (fun _ _ => iprop(False))).into_ih
    (List.Forall₂.cons trivial .nil) 0 ⟨trivial, trivial⟩).1.2

-- `Iris.ProofMode.intoPure_bigSepL` idx 6: necessary (SiProp, list [()], Φ and φ chosen opposite (True/False))
theorem w8c0_131 : ¬ drop0% Iris.ProofMode.intoPure_bigSepL 6 := fun h =>
  (@h SiProp _ Unit (fun _ _ => iprop(True)) (fun _ _ => False) [()]).into_pure 0 ⟨trivial, trivial⟩ 0 () rfl

-- `Iris.ProofMode.fromPure_bigSepL` idx 8: necessary (SiProp, list [()], Φ and φ chosen opposite (True/False))
theorem w8c0_132 : ¬ drop0% Iris.ProofMode.fromPure_bigSepL 8 := fun h =>
  ((@h SiProp true _ Unit (fun _ _ => iprop(False)) .in (fun _ _ => True) [()]
    (@Iris.Std.TCOr.l _ _ Iris.Std.TCEq.refl)).from_pure 0 ⟨trivial, fun _ _ _ => trivial⟩).1

-- `Iris.ProofMode.intoPure_bigSepM` idx 9: necessary (SiProp, one-key ExtTreeMap, Φ and φ chosen opposite (True/False))
theorem w8c0_133 : ¬ drop0% Iris.ProofMode.intoPure_bigSepM 9 := fun h => by
  have H := (@h SiProp _ Nat Unit TM _ (fun _ _ => iprop(True)) (fun _ _ => False) (sg ())).into_pure 0
    (by rw [sgE]; trivial)
  exact H 0 () (sg_get ())

-- `Iris.ProofMode.fromPure_bigSepM` idx 11: necessary (SiProp, one-key ExtTreeMap, Φ and φ chosen opposite (True/False))
theorem w8c0_134 : ¬ drop0% Iris.ProofMode.fromPure_bigSepM 11 := fun h => by
  have H := (@h SiProp true _ Nat Unit TM _ (fun _ _ => iprop(False)) (fun _ _ => True) (sg ()) .in
    (@Iris.Std.TCOr.l _ _ Iris.Std.TCEq.refl)).from_pure 0 ⟨trivial, fun _ _ _ => trivial⟩
  rw [sgE] at H; exact H

-- `Iris.ProofMode.intoPure_bigSepS` idx 8: necessary (SiProp, ExtTreeSet {0}, Φ and φ chosen opposite (True/False))
theorem w8c0_135 : ¬ drop0% Iris.ProofMode.intoPure_bigSepS 8 := fun h =>
  (@h SiProp _ TS Nat _ (fun _ => iprop(True)) (fun _ => False) {0}).into_pure 0 ((ssE (PROP := SiProp) (fun _ => iprop(True))).2 0 trivial) 0
    (by rw [Iris.Std.LawfulSet.mem_singleton])

-- `Iris.ProofMode.fromPure_bigSepS` idx 10: necessary (SiProp, ExtTreeSet {0}, Φ and φ chosen opposite (True/False))
theorem w8c0_136 : ¬ drop0% Iris.ProofMode.fromPure_bigSepS 10 := fun h =>
  (ssE (PROP := SiProp) (fun _ => iprop(False))).1 0 ((@h SiProp true _ TS Nat _ (fun _ => iprop(False)) (fun _ => True) {0} .in
    (@Iris.Std.TCOr.l _ _ Iris.Std.TCEq.refl)).from_pure 0 ⟨trivial, fun _ _ => trivial⟩)

-- `Iris.ProofMode.intoPure_bigSepMS` idx 8: necessary (SiProp, ListPerm multiset {0}, Φ and φ chosen opposite (True/False))
theorem w8c0_137 : ¬ drop0% Iris.ProofMode.intoPure_bigSepMS 8 := fun h =>
  (@h SiProp _ MSN Nat _ (fun _ => iprop(True)) (fun _ => False) {0}).into_pure 0 ((msSing (PROP := SiProp) (fun _ => iprop(True))).2 0 trivial) 0
    ((Iris.Std.LawfulFiniteMultiSet.mem_toList (MS := MSN)).1
      (by rw [Iris.Std.LawfulFiniteMultiSet.toList_singleton]; exact List.mem_singleton.2 rfl))

-- `Iris.ProofMode.fromPure_bigSepMS` idx 10: necessary (SiProp, ListPerm multiset {0}, Φ and φ chosen opposite (True/False))
theorem w8c0_138 : ¬ drop0% Iris.ProofMode.fromPure_bigSepMS 10 := fun h =>
  (msSing (PROP := SiProp) (fun _ => iprop(False))).1 0 ((@h SiProp true _ MSN Nat _ (fun _ => iprop(False)) (fun _ => True) {0} .in
    (@Iris.Std.TCOr.l _ _ Iris.Std.TCEq.refl)).from_pure 0 ⟨trivial, fun _ _ => trivial⟩)

-- `Iris.ProofMode.elimInv_acc_without_close` idx 14: necessary (SiProp, M1 = const False makes the kept accessor elimination instance hold vacuously; Q = False, everything else True)
theorem w8c0_139 : ¬ drop0% Iris.ProofMode.elimInv_acc_without_close 14 := fun h =>
  (@h SiProp _ Unit True True iprop(True) iprop(True) (fun _ => iprop(False)) id (fun _ => iprop(True))
    (fun _ => iprop(True)) (fun _ => none) iprop(False) (fun _ => iprop(True))
    ⟨fun _ => fun _ _ _ _ _ _ _ hf => (hf : False).elim⟩).elim_inv ⟨trivial, trivial⟩ 0
    ⟨trivial, trivial, SiProp.forall_holds.2 fun _ _ _ _ => trivial⟩

-- `Iris.ProofMode.elimInv_acc_without_close` idx 15: necessary (SiProp, M1 = const True makes the kept IntoAcc instance hold; Q = False, everything else True)
theorem w8c0_140 : ¬ drop0% Iris.ProofMode.elimInv_acc_without_close 15 := fun h =>
  (@h SiProp _ Unit True True iprop(True) iprop(True) (fun _ => iprop(True)) id (fun _ => iprop(True))
    (fun _ => iprop(True)) (fun _ => none) iprop(False) (fun _ => iprop(True))
    ⟨fun _ => fun _ _ _ _ _ _ _ _ => trivial⟩).elim_inv ⟨trivial, trivial⟩ 0
    ⟨trivial, trivial, SiProp.forall_holds.2 fun _ _ _ _ => trivial⟩

-- `Iris.ProofMode.elimInv_acc_with_close` idx 14: necessary (SiProp, M1 = const False makes the kept accessor elimination instance hold vacuously; Q = False, everything else True)
theorem w8c0_141 : ¬ drop0% Iris.ProofMode.elimInv_acc_with_close 14 := fun h =>
  (@h SiProp _ Unit True True iprop(True) iprop(True) (fun _ => iprop(False)) id (fun _ => iprop(True))
    (fun _ => iprop(True)) (fun _ => none) iprop(False) iprop(True)
    (fun _ => ⟨fun _ _ h => h.1.elim⟩)).elim_inv ⟨trivial, trivial⟩ 0
    ⟨trivial, trivial, SiProp.forall_holds.2 fun _ _ _ _ => trivial⟩

-- `Iris.ProofMode.elimInv_acc_with_close` idx 15: necessary (SiProp, M1 = const True makes the kept IntoAcc instance hold; Q = False, everything else True)
theorem w8c0_142 : ¬ drop0% Iris.ProofMode.elimInv_acc_with_close 15 := fun h =>
  (@h SiProp _ Unit True True iprop(True) iprop(True) (fun _ => iprop(True)) id (fun _ => iprop(True))
    (fun _ => iprop(True)) (fun _ => none) iprop(False) iprop(True)
    ⟨fun _ => fun _ _ _ _ _ _ _ _ => trivial⟩).elim_inv ⟨trivial, trivial⟩ 0
    ⟨trivial, trivial, SiProp.forall_holds.2 fun _ _ _ _ => trivial⟩

-- `Iris.ProofMode.elimModal_embed_fupd_goal` idx 7: necessary (MK (mask BI, W6c1) with mkFupd on PROP1 and constant-True fupd on PROP2, identity embedding, masks ∅: premise trivial, |={∅,∅}=> False fails at ∅)
theorem w8c0_143 : ¬ drop0% Iris.ProofMode.elimModal_embed_fupd_goal 7 := fun h =>
  mk_false ((@h MK MK _ _ (idEmb MK) mkFupd (topF MK) True false .in false ∅ ∅ ∅ iprop(True) iprop(True)
    iprop(False) iprop(True) ⟨fun _ _ _ => trivial⟩).elim_modal trivial ∅
    ⟨∅, ∅, dj0, union_empty_left.symm, trivial, fun y _ _ _ =>
      ⟨y, dj0, union_empty_right.trans union_empty_left.symm, trivial⟩⟩)

-- `Iris.ProofMode.elimModal_embed_fupd_goal` idx 19: necessary (MK with mkFupd on both sides (BiEmbedFUpd holds for the identity embedding), masks ∅: Q = False, Q' = True)
theorem w8c0_144 : ¬ drop0% Iris.ProofMode.elimModal_embed_fupd_goal 19 := fun h =>
  mk_false ((@h MK MK _ _ (idEmb MK) mkFupd mkFupd mkFU True false .in false ∅ ∅ ∅ iprop(True) iprop(True)
    iprop(False) iprop(True)).elim_modal trivial ∅
    ⟨∅, ∅, dj0, union_empty_left.symm, trivial, fun y _ _ _ =>
      ⟨y, dj0, union_empty_right.trans union_empty_left.symm, trivial⟩⟩)

-- `Iris.ProofMode.elimModal_embed_fupd_hyp` idx 7: necessary (MK: fupd constant True on PROP1, mkFupd on PROP2, masks ∅: |={∅,∅}=> False is unsatisfiable so the premise holds; conclusion True ∗ (True -∗ True) ⊢ False)
theorem w8c0_145 : ¬ drop0% Iris.ProofMode.elimModal_embed_fupd_hyp 7 := fun h =>
  (@h MK MK _ _ (idEmb MK) (topF MK) mkFupd True false .in false ∅ ∅ iprop(False) iprop(True) iprop(False)
    iprop(True) ⟨fun _ _ ⟨a, _, _, _, ha, _⟩ => let ⟨_, _, _, f⟩ := ha (djs dj0); f⟩).elim_modal trivial ∅
    mk_lhs

-- `Iris.ProofMode.addModal_embed_fupd_goal` idx 7: necessary (MK with mkFupd on PROP1 and constant-True fupd on PROP2, masks ∅: P = True, P' = Q = False)
theorem w8c0_146 : ¬ drop0% Iris.ProofMode.addModal_embed_fupd_goal 7 := fun h =>
  mk_false ((@h MK MK _ _ (idEmb MK) mkFupd (topF MK) ∅ ∅ iprop(True) iprop(False) iprop(False)
    ⟨fun _ _ => trivial⟩).add_modal ∅ ⟨∅, ∅, dj0, union_empty_left.symm, trivial, fun _ _ hf => hf.elim⟩)

-- `Iris.ProofMode.addModal_embed_fupd_goal` idx 13: necessary (MK with mkFupd on both sides, masks ∅: P = True, P' = Q = False)
theorem w8c0_147 : ¬ drop0% Iris.ProofMode.addModal_embed_fupd_goal 13 := fun h =>
  mk_false ((@h MK MK _ _ (idEmb MK) mkFupd mkFupd mkFU ∅ ∅ iprop(True) iprop(False) iprop(False)).add_modal ∅
    ⟨∅, ∅, dj0, union_empty_left.symm, trivial, fun _ _ hf => hf.elim⟩)

-- `Iris.ProofMode.fromPure_pure_wand` idx 8: necessary (SiProp: without the dropped instance the other arguments are free; True/False choices make the conclusion entailment fail at step 0)
theorem w8c0_148 : ¬ drop0% Iris.ProofMode.fromPure_pure_wand 8 := fun h =>
  (@h SiProp false .in False False _ iprop(True) iprop(False) ⟨fun _ h => h⟩
    (@Iris.Std.TCOr.l _ _ Iris.Std.TCEq.refl)).from_pure 0 (fun h => h) 0 (Nat.le_refl 0) trivial
