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

namespace W8c1
open Iris Iris.BI Iris.ProofMode

-- GB copied from W4c4

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

/-- identity basic update on GB (lawful) -/
instance gbBupd : BIUpdate GB where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h

/-- framing against the goal False always succeeds, in any BI -/
theorem frF {PROP : Type _} [BI PROP] (p : Bool) (R P : PROP) : Frame p R P iprop(False) :=
  ⟨sep_comm.1.trans (wand_elim false_elim)⟩

-- identity embedding of any BI into itself (copied from W5c0)
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
theorem idSbi (PROP : Type _) [Sbi PROP] : @BiEmbedSbi PROP PROP _ _ (idEmb PROP) _ _ :=
  @BiEmbedSbi.mk PROP PROP _ _ (idEmb PROP) _ _ (fun _ => .rfl) (fun _ => .rfl)

/-- Discrete Bool OFE (copied from W5c1). -/
structure DB where b : Bool
instance : OFE DB := OFE.ofDiscrete DB
instance : OFE.Discrete DB := ⟨id⟩
def dT : DB := ⟨true⟩
def dF : DB := ⟨false⟩
theorem dTF : dT ≠ dF := by simp [dT, dF]

end W8c1

namespace W8c1
open Iris Iris.BI Iris.Std Iris.Std.LawfulSet

-- MK copied from W6c1
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
end W8c1

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.LawfulSet W8c1

-- `Iris.ProofMode.frame_here_absorbing` idx 4: necessary (GB, p = false, R = emp: emp ∗ True ⊬ emp at point true)
theorem w8c1_1 : ¬ drop0% Iris.ProofMode.frame_here_absorbing 4 := fun h =>
  Bool.noConfusion ((@h GB gbBI false iprop(emp)).frame true ⟨false, true, rfl, rfl, trivial⟩ : true = false)

-- `Iris.ProofMode.frame_affinely_here_absorbing` idx 4: necessary (GB, p = false, R = emp: <affine> emp ∗ True ⊬ emp at point true)
theorem w8c1_2 : ¬ drop0% Iris.ProofMode.frame_affinely_here_absorbing 4 := fun h =>
  Bool.noConfusion ((@h GB gbBI false iprop(emp)).frame true ⟨false, true, rfl, ⟨rfl, rfl⟩, trivial⟩ : true = false)

-- `Iris.ProofMode.frame_here_pure_persistent` idx 5: necessary (GB, φ = True, Q = False: □⌜True⌝ ∗ emp holds at false)
theorem w8c1_3 : ¬ drop0% Iris.ProofMode.frame_here_pure_persistent 5 := fun h =>
  (@h GB gbBI false True iprop(False)).frame false ⟨false, false, rfl, ⟨rfl, trivial⟩, rfl⟩

-- `Iris.ProofMode.frame_here_pure` idx 5: necessary (GB, a = false, φ = True, Q = False)
theorem w8c1_4 : ¬ drop0% Iris.ProofMode.frame_here_pure 5 := fun h =>
  (@h GB gbBI false True iprop(False) inferInstance).frame false ⟨false, false, rfl, trivial, rfl⟩

-- `Iris.ProofMode.frame_wand` idx 7: necessary (GB, R = P1 = emp, P2 = False, Q2 = True)
theorem w8c1_5 : ¬ drop0% Iris.ProofMode.frame_wand 7 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(emp) iprop(False) iprop(True)).frame false
    ⟨false, false, rfl, rfl, fun _ _ => trivial⟩ false rfl

-- `Iris.ProofMode.frame_affinely` idx 8: necessary (GB, p = true, R = emp, P = False, Q = True, Q' = <affine> True)
theorem w8c1_6 : ¬ drop0% Iris.ProofMode.frame_affinely 8 := fun h =>
  ((@h GB gbBI true iprop(emp) iprop(False) iprop(True) iprop(<affine> True) inferInstance ⟨.rfl⟩).frame false
    ⟨false, false, rfl, ⟨rfl, rfl⟩, ⟨rfl, trivial⟩⟩).2

-- `Iris.ProofMode.frame_affinely` idx 9: necessary (GB, p = true, R = emp, P = Q = False, Q' = True)
theorem w8c1_7 : ¬ drop0% Iris.ProofMode.frame_affinely 9 := fun h =>
  ((@h GB gbBI true iprop(emp) iprop(False) iprop(False) iprop(True) inferInstance (frF _ _ _)).frame false
    ⟨false, false, rfl, ⟨rfl, rfl⟩, trivial⟩).2

-- `Iris.ProofMode.frame_intuitionistically` idx 6: necessary (GB, R = emp, P = False, Q = True, Q' = □ True)
theorem w8c1_8 : ¬ drop0% Iris.ProofMode.frame_intuitionistically 6 := fun h =>
  ((@h GB gbBI iprop(emp) iprop(False) iprop(True) iprop(□ True) ⟨.rfl⟩).frame false
    ⟨false, false, rfl, ⟨rfl, rfl⟩, ⟨rfl, trivial⟩⟩).2

-- `Iris.ProofMode.frame_intuitionistically` idx 7: necessary (GB, R = emp, P = Q = False, Q' = True)
theorem w8c1_9 : ¬ drop0% Iris.ProofMode.frame_intuitionistically 7 := fun h =>
  ((@h GB gbBI iprop(emp) iprop(False) iprop(False) iprop(True) (frF _ _ _)).frame false
    ⟨false, false, rfl, ⟨rfl, rfl⟩, trivial⟩).2

-- `Iris.ProofMode.frame_absorbingly` idx 7: necessary (GB, R = emp, P = False, Q = True, Q' = <absorb> True)
theorem w8c1_10 : ¬ drop0% Iris.ProofMode.frame_absorbingly 7 := fun h => by
  obtain ⟨_, _, _, _, h⟩ := (@h GB gbBI false iprop(emp) iprop(False) iprop(True) iprop(<absorb> True) ⟨.rfl⟩).frame
    false ⟨false, false, rfl, rfl, false, false, rfl, trivial, trivial⟩
  exact h

-- `Iris.ProofMode.frame_absorbingly` idx 8: necessary (GB, R = emp, P = Q = False, Q' = True)
theorem w8c1_11 : ¬ drop0% Iris.ProofMode.frame_absorbingly 8 := fun h => by
  obtain ⟨_, _, _, _, h⟩ := (@h GB gbBI false iprop(emp) iprop(False) iprop(False) iprop(True) (frF _ _ _)).frame
    false ⟨false, false, rfl, rfl, trivial⟩
  exact h

-- `Iris.ProofMode.frame_persistently` idx 6: necessary (GB, R = emp, P = False, Q = True, Q' = <pers> True)
theorem w8c1_12 : ¬ drop0% Iris.ProofMode.frame_persistently 6 := fun h =>
  (@h GB gbBI iprop(emp) iprop(False) iprop(True) iprop(<pers> True) ⟨.rfl⟩).frame false
    ⟨false, false, rfl, ⟨rfl, rfl⟩, trivial⟩

-- `Iris.ProofMode.frame_persistently` idx 7: necessary (GB, R = emp, P = Q = False, Q' = True)
theorem w8c1_13 : ¬ drop0% Iris.ProofMode.frame_persistently 7 := fun h =>
  (@h GB gbBI iprop(emp) iprop(False) iprop(False) iprop(True) (frF _ _ _)).frame false
    ⟨false, false, rfl, ⟨rfl, rfl⟩, trivial⟩

-- `Iris.ProofMode.frame_forall` idx 7: necessary (GB, α = True, R = emp, Φ = False, Ψ = True)
theorem w8c1_14 : ¬ drop0% Iris.ProofMode.frame_forall 7 := fun h =>
  (@h GB True gbBI false iprop(emp) (fun _ => iprop(False)) (fun _ => iprop(True))).frame false
    ⟨false, false, rfl, rfl, fun _ ⟨_, e⟩ => e ▸ trivial⟩ _ ⟨trivial, rfl⟩

-- `Iris.ProofMode.frame_impl_persistent` idx 6: necessary (GB, R = emp, P1 = True, P2 = False, Q2 = True)
theorem w8c1_15 : ¬ drop0% Iris.ProofMode.frame_impl_persistent 6 := fun h =>
  (@h GB gbBI iprop(emp) iprop(True) iprop(False) iprop(True)).frame false
    ⟨false, false, rfl, ⟨rfl, rfl⟩, fun _ => trivial⟩ trivial

-- `Iris.ProofMode.frame_impl` idx 7: necessary (GB, R = True, P1 = emp (persistent, not absorbing), P2 = Q2 = False; point false)
theorem w8c1_16 : ¬ drop0% Iris.ProofMode.frame_impl 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(emp) iprop(False) iprop(False) ⟨fun _ _ => rfl⟩ ⟨frF _ _ _⟩).frame false
    ⟨true, true, rfl, trivial, fun e => Bool.noConfusion e⟩ rfl

-- `Iris.ProofMode.frame_impl` idx 8: necessary (GB, R = emp, P1 = True, P2 = False, Q2 = True)
theorem w8c1_17 : ¬ drop0% Iris.ProofMode.frame_impl 8 := fun h =>
  (@h GB gbBI iprop(emp) iprop(True) iprop(False) iprop(True) ⟨fun _ _ => trivial⟩ ⟨⟨fun _ _ => trivial⟩⟩).frame false
    ⟨false, false, rfl, rfl, fun _ => trivial⟩ trivial

-- `Iris.ProofMode.frame_later` idx 8: necessary (GB (later = id), R = P = Q = emp, Q' = ▷ emp, R' = True; point true)
theorem w8c1_18 : ¬ drop0% Iris.ProofMode.frame_later 8 := fun h =>
  Bool.noConfusion ((@h GB gbBI false iprop(emp) iprop(True) iprop(emp) iprop(emp) iprop(▷ emp)
    (frame_here false _) ⟨.rfl⟩).frame true ⟨true, false, rfl, trivial, rfl⟩ : true = false)

-- `Iris.ProofMode.frame_later` idx 9: necessary (GB, R = emp, R' = ▷ emp, P = False, Q = True, Q' = ▷ True)
theorem w8c1_19 : ¬ drop0% Iris.ProofMode.frame_later 9 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(▷ emp) iprop(False) iprop(True) iprop(▷ True) ⟨.rfl⟩ ⟨.rfl⟩).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_later` idx 10: necessary (GB, R = emp, R' = ▷ emp, P = Q = False, Q' = True)
theorem w8c1_20 : ¬ drop0% Iris.ProofMode.frame_later 10 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(▷ emp) iprop(False) iprop(False) iprop(True) ⟨.rfl⟩ (frF _ _ _)).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_laterN` idx 9: necessary (GB, n = 1, R = P = Q = emp, Q' = ▷ emp, R' = True; point true)
theorem w8c1_21 : ¬ drop0% Iris.ProofMode.frame_laterN 9 := fun h =>
  Bool.noConfusion ((@h GB gbBI false 1 iprop(emp) iprop(True) iprop(emp) iprop(emp) iprop(▷ emp)
    (frame_here false _) ⟨.rfl⟩).frame true ⟨true, false, rfl, trivial, rfl⟩ : true = false)

-- `Iris.ProofMode.frame_laterN` idx 10: necessary (GB, n = 1, R = emp, R' = ▷ emp, P = False, Q = True, Q' = ▷ True)
theorem w8c1_22 : ¬ drop0% Iris.ProofMode.frame_laterN 10 := fun h =>
  (@h GB gbBI false 1 iprop(emp) iprop(▷ emp) iprop(False) iprop(True) iprop(▷ True) ⟨.rfl⟩ ⟨.rfl⟩).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_laterN` idx 11: necessary (GB, n = 1, R = emp, R' = ▷ emp, P = Q = False, Q' = True)
theorem w8c1_23 : ¬ drop0% Iris.ProofMode.frame_laterN 11 := fun h =>
  (@h GB gbBI false 1 iprop(emp) iprop(▷ emp) iprop(False) iprop(False) iprop(True) ⟨.rfl⟩ (frF _ _ _)).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_bupd` idx 8: necessary (GB with identity bupd, R = emp, P = False, Q = True, Q' = |==> True)
theorem w8c1_24 : ¬ drop0% Iris.ProofMode.frame_bupd 8 := fun h =>
  (@h GB gbBI gbBupd false iprop(emp) iprop(False) iprop(True) iprop(|==> True) ⟨.rfl⟩).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_bupd` idx 9: necessary (GB with identity bupd, R = emp, P = Q = False, Q' = True)
theorem w8c1_25 : ¬ drop0% Iris.ProofMode.frame_bupd 9 := fun h =>
  (@h GB gbBI gbBupd false iprop(emp) iprop(False) iprop(False) iprop(True) (frF _ _ _)).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_fupd` idx 10: necessary (MK with mask-ownership fupd, E1 = E2 = ∅, R = emp, P = False, Q = True, Q' = |={∅,∅}=> True; point ∅)
theorem w8c1_26 : ¬ drop0% Iris.ProofMode.frame_fupd 10 := fun h => by
  obtain ⟨_, _, _, h⟩ := (@h MK mkBI mkFupd false ∅ ∅ iprop(emp) iprop(False) iprop(True)
    iprop(|={∅,∅}=> True) ⟨.rfl⟩).frame ∅
    ⟨∅, ∅, dj0, union_empty_left.symm, rfl, fun _ => ⟨∅, dj0, rfl, trivial⟩⟩ dj0
  exact h

-- `Iris.ProofMode.frame_fupd` idx 11: necessary (MK with mask-ownership fupd, E1 = E2 = ∅, R = emp, P = Q = False, Q' = True; point ∅)
theorem w8c1_27 : ¬ drop0% Iris.ProofMode.frame_fupd 11 := fun h => by
  obtain ⟨_, _, _, h⟩ := (@h MK mkBI mkFupd false ∅ ∅ iprop(emp) iprop(False) iprop(False) iprop(True)
    (frF _ _ _)).frame ∅ ⟨∅, ∅, dj0, union_empty_left.symm, rfl, trivial⟩ dj0
  exact h

-- `Iris.ProofMode.frame_except_0` idx 7: necessary (GB, R = emp, P = False, Q = True, Q' = ◇ True)
theorem w8c1_28 : ¬ drop0% Iris.ProofMode.frame_except_0 7 := fun h => by
  rcases (@h GB gbBI false iprop(emp) iprop(False) iprop(True) iprop(◇ True) ⟨.rfl⟩).frame false
    ⟨false, false, rfl, rfl, .inr trivial⟩ with h | h <;> exact h

-- `Iris.ProofMode.frame_except_0` idx 8: necessary (GB, R = emp, P = Q = False, Q' = True)
theorem w8c1_29 : ¬ drop0% Iris.ProofMode.frame_except_0 8 := fun h => by
  rcases (@h GB gbBI false iprop(emp) iprop(False) iprop(False) iprop(True) (frF _ _ _)).frame false
    ⟨false, false, rfl, rfl, trivial⟩ with h | h <;> exact h

-- `Iris.ProofMode.frame_embed_core` idx 11: necessary (identity embedding of GB, R = emp, P = Q = False, Q' = True)
theorem w8c1_30 : ¬ drop0% Iris.ProofMode.frame_embed_core 11 := fun h =>
  @h GB GB gbBI gbBI (idEmb GB) false iprop(emp) iprop(False) iprop(False) iprop(True) (frF _ _ _) false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_embed` idx 10: necessary (identity embedding of GB, R = emp, P = False, Q = True, Q' = True)
theorem w8c1_31 : ¬ drop0% Iris.ProofMode.frame_embed 10 := fun h => by
  letI := idEmb GB
  exact (@h GB GB gbBI gbBI (idEmb GB) false iprop(emp) iprop(False) iprop(True) iprop(True) ⟨.rfl⟩).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_embed` idx 11: necessary (identity embedding of GB, R = emp, P = Q = False, Q' = True)
theorem w8c1_32 : ¬ drop0% Iris.ProofMode.frame_embed 11 := fun h =>
  (@h GB GB gbBI gbBI (idEmb GB) false iprop(emp) iprop(False) iprop(False) iprop(True) (frF _ _ _)).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_pure_embed` idx 10: necessary (identity embedding of GB, φ = True, P = False, Q = True, Q' = True)
theorem w8c1_33 : ¬ drop0% Iris.ProofMode.frame_pure_embed 10 := fun h => by
  letI := idEmb GB
  exact (@h GB GB gbBI gbBI (idEmb GB) false True iprop(False) iprop(True) iprop(True) ⟨.rfl⟩).frame false
    ⟨false, false, rfl, trivial, trivial⟩

-- `Iris.ProofMode.frame_pure_embed` idx 11: necessary (identity embedding of GB, φ = True, P = Q = False, Q' = True)
theorem w8c1_34 : ¬ drop0% Iris.ProofMode.frame_pure_embed 11 := fun h =>
  (@h GB GB gbBI gbBI (idEmb GB) false True iprop(False) iprop(False) iprop(True) (frF _ _ _)).frame false
    ⟨false, false, rfl, trivial, trivial⟩

-- `Iris.ProofMode.frame_eq_embed` idx 15: necessary (SiProp with identity embedding, a = b, P = Q = False, Q' = True; step 0)
theorem w8c1_36 : ¬ drop0% Iris.ProofMode.frame_eq_embed 15 := fun h =>
  (@h SiProp SiProp _ _ (idEmb SiProp) (idSbi SiProp) false DB _ dT dT iprop(False) iprop(False) iprop(True)
    (frF _ _ _)).frame 0 ⟨(internalEq.refl (PROP := SiProp) (P := iprop(True)) (a := dT)) 0 trivial, trivial⟩

-- `Iris.ProofMode.frame_texist` idx 7: necessary (GB, empty telescope, R = emp, Φ = False, Ψ = True)
theorem w8c1_37 : ¬ drop0% Iris.ProofMode.frame_texist 7 := fun h =>
  (@h GB .nil gbBI false iprop(emp) (fun _ => iprop(False)) (fun _ => iprop(True))).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_tforall` idx 7: necessary (GB, empty telescope, R = emp, Φ = False, Ψ = True)
theorem w8c1_38 : ¬ drop0% Iris.ProofMode.frame_tforall 7 := fun h =>
  (@h GB .nil gbBI false iprop(emp) (fun _ => iprop(False)) (fun _ => iprop(True))).frame false
    ⟨false, false, rfl, rfl, trivial⟩

/-- GB: emp ∗ True ⊢ True ∗ emp ∗ … (used for big-sep framing premises) -/
theorem gb_et (X : GB) (hX : X false) : (iprop(emp ∗ True) : GB) ⊢ iprop(True ∗ X) :=
  fun x _ => ⟨x, false, by cases x <;> rfl, trivial, hX⟩

-- `Iris.ProofMode.frame_bigSepL_cons` idx 10: necessary (GB, l = [] (not a cons), x = (), l' = [], Φ = True, R = emp, Q = True; point true)
theorem w8c1_39 : ¬ drop0% Iris.ProofMode.frame_bigSepL_cons 10 := fun h =>
  Bool.noConfusion ((@h GB gbBI Unit false (fun _ _ => iprop(True)) iprop(emp) iprop(True) [] () []
    ⟨gb_et _ rfl⟩).frame true ⟨false, true, rfl, rfl, trivial⟩ : true = false)

-- `Iris.ProofMode.frame_bigSepL_cons` idx 11: necessary (GB, l = [()], Φ = False, R = emp, Q = True)
theorem w8c1_40 : ¬ drop0% Iris.ProofMode.frame_bigSepL_cons 11 := fun h => by
  obtain ⟨_, _, _, h, _⟩ := (@h GB gbBI Unit false (fun _ _ => iprop(False)) iprop(emp) iprop(True) [()] () []
    inferInstance).frame false ⟨false, false, rfl, rfl, trivial⟩
  exact h

-- `Iris.ProofMode.frame_bigSepL_app` idx 10: necessary (GB, l = [], l1 = [()], l2 = [], Φ = True, R = emp, Q = True; point true)
theorem w8c1_41 : ¬ drop0% Iris.ProofMode.frame_bigSepL_app 10 := fun h =>
  Bool.noConfusion ((@h GB gbBI Unit false (fun _ _ => iprop(True)) iprop(emp) iprop(True) [] [()] []
    ⟨fun x _ => ⟨x, false, by cases x <;> rfl, ⟨x, false, by cases x <;> rfl, trivial, rfl⟩, rfl⟩⟩).frame true ⟨false, true, rfl, rfl, trivial⟩ : true = false)

-- `Iris.ProofMode.frame_bigSepL_app` idx 11: necessary (GB, l = l1 = l2 = [], R = emp, Q = True; point true)
theorem w8c1_42 : ¬ drop0% Iris.ProofMode.frame_bigSepL_app 11 := fun h =>
  Bool.noConfusion ((@h GB gbBI Unit false (fun _ _ => iprop(True)) iprop(emp) iprop(True) [] [] []
    ⟨rfl⟩).frame true ⟨false, true, rfl, rfl, trivial⟩ : true = false)

-- `Iris.ProofMode.frame_bigSepL2_cons` idx 14: necessary (GB, l1 = [] (not a cons), l2 = [()], Φ = True, R = emp, Q = True: the goal is False)
theorem w8c1_43 : ¬ drop0% Iris.ProofMode.frame_bigSepL2_cons 14 := fun h =>
  (@h GB gbBI Unit Unit false (fun _ _ _ => iprop(True)) iprop(emp) iprop(True) [] () [] [()] () []
    inferInstance ⟨gb_et _ rfl⟩).frame false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_bigSepL2_cons` idx 15: necessary (GB, l1 = [()], l2 = [] (not a cons), Φ = True, R = emp, Q = True)
theorem w8c1_44 : ¬ drop0% Iris.ProofMode.frame_bigSepL2_cons 15 := fun h =>
  (@h GB gbBI Unit Unit false (fun _ _ _ => iprop(True)) iprop(emp) iprop(True) [()] () [] [] () []
    inferInstance ⟨gb_et _ rfl⟩).frame false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_bigSepL2_cons` idx 16: necessary (GB, l1 = l2 = [()], Φ = False, R = emp, Q = True)
theorem w8c1_45 : ¬ drop0% Iris.ProofMode.frame_bigSepL2_cons 16 := fun h => by
  obtain ⟨_, _, _, h, _⟩ := (@h GB gbBI Unit Unit false (fun _ _ _ => iprop(False)) iprop(emp) iprop(True)
    [()] () [] [()] () [] inferInstance inferInstance).frame false ⟨false, false, rfl, rfl, trivial⟩
  exact h

-- `Iris.ProofMode.frame_bigSepL2_app` idx 14: necessary (GB, l1 = [] but l1' = [()], l2 = l2' = [()], Φ = True, R = emp, Q = True: the goal is False)
theorem w8c1_46 : ¬ drop0% Iris.ProofMode.frame_bigSepL2_app 14 := fun h =>
  (@h GB gbBI Unit Unit false (fun _ _ _ => iprop(True)) iprop(emp) iprop(True) [] [()] [] [()] [()] []
    ⟨rfl⟩ ⟨fun x _ => ⟨x, false, by cases x <;> rfl, ⟨x, false, by cases x <;> rfl, trivial, rfl⟩, rfl⟩⟩).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_bigSepL2_app` idx 15: necessary (GB, l2 = [] but l2' = [()], l1 = l1' = [()], Φ = True, R = emp, Q = True)
theorem w8c1_47 : ¬ drop0% Iris.ProofMode.frame_bigSepL2_app 15 := fun h =>
  (@h GB gbBI Unit Unit false (fun _ _ _ => iprop(True)) iprop(emp) iprop(True) [()] [()] [] [] [()] []
    ⟨rfl⟩ ⟨fun x _ => ⟨x, false, by cases x <;> rfl, ⟨x, false, by cases x <;> rfl, trivial, rfl⟩, rfl⟩⟩).frame false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.frame_bigSepL2_app` idx 16: necessary (GB, all lists [], R = emp, Q = True; point true)
theorem w8c1_48 : ¬ drop0% Iris.ProofMode.frame_bigSepL2_app 16 := fun h =>
  Bool.noConfusion ((@h GB gbBI Unit Unit false (fun _ _ _ => iprop(True)) iprop(emp) iprop(True) [] [] [] [] [] []
    ⟨rfl⟩ ⟨rfl⟩).frame true ⟨false, true, rfl, rfl, trivial⟩ : true = false)

-- `Iris.ProofMode.frame_bigSepMS_disjUnion` idx 12: necessary (GB, multisets ListPerm Nat, X = ∅, X1 = {0}, X2 = ∅, Φ = True, R = emp, Q = True; point true)
theorem w8c1_49 : ¬ drop0% Iris.ProofMode.frame_bigSepMS_disjUnion 12 := fun h =>
  Bool.noConfusion ((BigSepMS.bigSepMS_empty (PROP := GB) (MS := ListPerm Nat)).1 true
    ((@h GB gbBI (ListPerm Nat) Nat _ false (fun _ => iprop(True)) iprop(emp) iprop(True) ∅ {0} ∅
      ⟨(gb_et iprop(emp) rfl).trans (sep_mono (BigSepMS.bigSepMS_singleton (MS := ListPerm Nat) (Φ := fun _ => iprop(True)) (x := 0)).2
        (BigSepMS.bigSepMS_empty (MS := ListPerm Nat)).2)⟩).frame true ⟨false, true, rfl, rfl, trivial⟩) :
    true = false)

-- `Iris.ProofMode.frame_bigSepMS_disjUnion` idx 13: necessary (GB, X = ∅ ⊎ ∅, X1 = X2 = ∅, R = emp, Q = True; point true)
theorem w8c1_50 : ¬ drop0% Iris.ProofMode.frame_bigSepMS_disjUnion 13 := fun h => by
  have H := (@h GB gbBI (ListPerm Nat) Nat _ false (fun _ => iprop(True)) iprop(emp) iprop(True)
      ((∅ : ListPerm Nat) ⊎ ∅) ∅ ∅ ⟨rfl⟩).frame
  have H2 := H.trans ((BigSepMS.bigSepMS_disjUnion (MS := ListPerm Nat)).1.trans
    (sep_mono (BigSepMS.bigSepMS_empty (MS := ListPerm Nat)).1 (BigSepMS.bigSepMS_empty (MS := ListPerm Nat)).1))
  obtain ⟨a, b, e, ha, hb⟩ := H2 true ⟨false, true, rfl, rfl, trivial⟩
  have ha : a = false := ha
  have hb : b = false := hb
  subst ha hb
  exact Bool.noConfusion e

-- `Iris.ProofMode.frame_sep_both` idx 8: necessary (GB, R = emp, P1 = False, Q1 = True, P2 = Q2 = emp, Q' = True ∗ emp)
theorem w8c1_51 : ¬ drop0% Iris.ProofMode.frame_sep_both 8 := fun h => by
  obtain ⟨_, _, _, h, _⟩ := (@h GB gbBI iprop(emp) iprop(False) iprop(emp) iprop(True) iprop(emp) iprop(True ∗ emp)
    (frame_here true _) ⟨.rfl⟩).frame false ⟨false, false, rfl, ⟨rfl, rfl⟩, false, false, rfl, trivial, rfl⟩
  exact h

-- `Iris.ProofMode.frame_sep_both` idx 9: necessary (GB, R = emp, P1 = Q1 = emp, P2 = False, Q2 = True, Q' = emp ∗ True)
theorem w8c1_52 : ¬ drop0% Iris.ProofMode.frame_sep_both 9 := fun h => by
  obtain ⟨_, _, _, _, h⟩ := (@h GB gbBI iprop(emp) iprop(emp) iprop(False) iprop(emp) iprop(True) iprop(emp ∗ True)
    (frame_here true _) ⟨.rfl⟩).frame false ⟨false, false, rfl, ⟨rfl, rfl⟩, false, false, rfl, rfl, trivial⟩
  exact h

-- `Iris.ProofMode.frame_sep_both` idx 10: necessary (GB, R = emp, P1 = P2 = Q1 = Q2 = False, Q' = True)
theorem w8c1_53 : ¬ drop0% Iris.ProofMode.frame_sep_both 10 := fun h => by
  obtain ⟨_, _, _, h, _⟩ := (@h GB gbBI iprop(emp) iprop(False) iprop(False) iprop(False) iprop(False) iprop(True)
    (frF _ _ _) (frF _ _ _)).frame false ⟨false, false, rfl, ⟨rfl, rfl⟩, trivial⟩
  exact h

-- `Iris.ProofMode.frame_sep_left` idx 8: necessary (GB, R = emp, P1 = False, P2 = emp, Q = True, Q' = True ∗ emp)
theorem w8c1_54 : ¬ drop0% Iris.ProofMode.frame_sep_left 8 := fun h => by
  obtain ⟨_, _, _, h, _⟩ := (@h GB gbBI false iprop(emp) iprop(False) iprop(emp) iprop(True) iprop(True ∗ emp)
    ⟨.rfl⟩).frame false ⟨false, false, rfl, rfl, false, false, rfl, trivial, rfl⟩
  exact h

-- `Iris.ProofMode.frame_sep_left` idx 9: necessary (GB, R = emp, P1 = Q = False, P2 = emp, Q' = True)
theorem w8c1_55 : ¬ drop0% Iris.ProofMode.frame_sep_left 9 := fun h => by
  obtain ⟨_, _, _, h, _⟩ := (@h GB gbBI false iprop(emp) iprop(False) iprop(emp) iprop(False) iprop(True)
    (frF _ _ _)).frame false ⟨false, false, rfl, rfl, trivial⟩
  exact h

-- `Iris.ProofMode.frame_sep_right` idx 8: necessary (GB, R = emp, P1 = emp, P2 = False, Q = True, Q' = emp ∗ True)
theorem w8c1_56 : ¬ drop0% Iris.ProofMode.frame_sep_right 8 := fun h => by
  obtain ⟨_, _, _, _, h⟩ := (@h GB gbBI false iprop(emp) iprop(emp) iprop(False) iprop(True) iprop(emp ∗ True)
    ⟨.rfl⟩).frame false ⟨false, false, rfl, rfl, false, false, rfl, rfl, trivial⟩
  exact h

-- `Iris.ProofMode.frame_sep_right` idx 9: necessary (GB, R = emp, P1 = emp, P2 = Q = False, Q' = True)
theorem w8c1_57 : ¬ drop0% Iris.ProofMode.frame_sep_right 9 := fun h => by
  obtain ⟨_, _, _, _, h⟩ := (@h GB gbBI false iprop(emp) iprop(emp) iprop(False) iprop(False) iprop(True)
    (frF _ _ _)).frame false ⟨false, false, rfl, rfl, trivial⟩
  exact h

-- `Iris.ProofMode.frame_and` idx 9: necessary (GB, R = emp, P1 = False, Q1 = True, P2 = Q2 = emp, Q' = True ∧ emp)
theorem w8c1_58 : ¬ drop0% Iris.ProofMode.frame_and 9 := fun h =>
  ((@h GB gbBI false iprop(emp) iprop(False) iprop(emp) iprop(True) iprop(emp) iprop(True ∧ emp)
    (frame_here false _) ⟨.rfl⟩).frame false ⟨false, false, rfl, rfl, trivial, rfl⟩).1

-- `Iris.ProofMode.frame_and` idx 10: necessary (GB, R = emp, P1 = Q1 = emp, P2 = False, Q2 = True, Q' = emp ∧ True)
theorem w8c1_59 : ¬ drop0% Iris.ProofMode.frame_and 10 := fun h =>
  ((@h GB gbBI false iprop(emp) iprop(emp) iprop(False) iprop(emp) iprop(True) iprop(emp ∧ True)
    (frame_here false _) ⟨.rfl⟩).frame false ⟨false, false, rfl, rfl, rfl, trivial⟩).2

-- `Iris.ProofMode.frame_and` idx 11: necessary (GB, R = emp, P1 = P2 = Q1 = Q2 = False, Q' = True)
theorem w8c1_60 : ¬ drop0% Iris.ProofMode.frame_and 11 := fun h =>
  ((@h GB gbBI false iprop(emp) iprop(False) iprop(False) iprop(False) iprop(False) iprop(True)
    (frF _ _ _) (frF _ _ _)).frame false ⟨false, false, rfl, rfl, trivial⟩).1

-- `Iris.ProofMode.frame_or` idx 9: necessary (GB, R = emp, P1 = P2 = Q2 = False, Q1 = True, Q' = True ∨ False)
theorem w8c1_61 : ¬ drop0% Iris.ProofMode.frame_or 9 := fun h => by
  rcases (@h GB gbBI false iprop(emp) iprop(False) iprop(False) iprop(True) iprop(False) iprop(True ∨ False)
    (frF _ _ _) ⟨.rfl⟩).frame false ⟨false, false, rfl, rfl, .inl trivial⟩ with h | h <;> exact h

-- `Iris.ProofMode.frame_or` idx 10: necessary (GB, R = emp, P1 = P2 = Q1 = False, Q2 = True, Q' = False ∨ True)
theorem w8c1_62 : ¬ drop0% Iris.ProofMode.frame_or 10 := fun h => by
  rcases (@h GB gbBI false iprop(emp) iprop(False) iprop(False) iprop(False) iprop(True) iprop(False ∨ True)
    (frF _ _ _) ⟨.rfl⟩).frame false ⟨false, false, rfl, rfl, .inr trivial⟩ with h | h <;> exact h

-- `Iris.ProofMode.frame_or` idx 11: necessary (GB, R = emp, P1 = P2 = Q1 = Q2 = False, Q' = True)
theorem w8c1_63 : ¬ drop0% Iris.ProofMode.frame_or 11 := fun h => by
  rcases (@h GB gbBI false iprop(emp) iprop(False) iprop(False) iprop(False) iprop(False) iprop(True)
    (frF _ _ _) (frF _ _ _)).frame false ⟨false, false, rfl, rfl, trivial⟩ with h | h <;> exact h

-- `Iris.ProofMode.frame_exist` idx 8: necessary (GB, α = True, R = emp, Φ = False, Q = True)
theorem w8c1_64 : ¬ drop0% Iris.ProofMode.frame_exist 8 := fun h => by
  obtain ⟨_, ⟨_, e⟩, hp⟩ := (@h GB gbBI True false iprop(emp) (fun _ => iprop(False)) trivial iprop(True)).frame false
    ⟨false, false, rfl, rfl, trivial⟩
  subst e; exact hp

-- `Iris.ProofMode.frame_exist_no_instantiate` idx 7: necessary (GB, α = True, R = emp, Φ = False, Ψ = True)
theorem w8c1_65 : ¬ drop0% Iris.ProofMode.frame_exist_no_instantiate 7 := fun h => by
  obtain ⟨_, ⟨_, e⟩, hp⟩ := (@h GB gbBI True false iprop(emp) (fun _ => iprop(False)) (fun _ => iprop(True))).frame
    false ⟨false, false, rfl, rfl, _, ⟨trivial, rfl⟩, trivial⟩
  subst e; exact hp

-- `Iris.ProofMode.frameInstantiateExistsDisabled_of` idx 6: necessary (GB, R = emp, P = False, Q = True)
theorem w8c1_66 : ¬ drop0% Iris.ProofMode.frameInstantiateExistsDisabled_of 6 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(False) iprop(True)).1.1 false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.intoLaterN_internalEq_next` idx 11: necessary (SiProp, discrete Bool, n = 0: Next true ≡ Next false holds at step 0, true ≡ false does not)
theorem w8c1_67 : ¬ drop0% Iris.ProofMode.intoLaterN_internalEq_next 11 := fun h =>
  dTF ((@h SiProp DB _ _ dT dF false false false 0 0).1 0 (fun _ h => absurd h (Nat.not_lt_zero _)))

-- `Iris.ProofMode.intoInternalEq_affinely` idx 7: necessary (SiProp, discrete Bool true, false, P = True)
theorem w8c1_68 : ¬ drop0% Iris.ProofMode.intoInternalEq_affinely 7 := fun h =>
  dTF ((@h SiProp DB _ _ dT dF iprop(True)).1 0 ⟨trivial, trivial⟩)

-- `Iris.ProofMode.intoInternalEq_intuitionistically` idx 7: necessary (SiProp, discrete Bool true, false, P = True)
theorem w8c1_69 : ¬ drop0% Iris.ProofMode.intoInternalEq_intuitionistically 7 := fun h =>
  dTF ((@h SiProp DB _ _ dT dF iprop(True)).1 0 ⟨trivial, trivial⟩)

-- `Iris.ProofMode.intoInternalEq_absorbingly` idx 7: necessary (SiProp, discrete Bool true, false, P = True)
theorem w8c1_70 : ¬ drop0% Iris.ProofMode.intoInternalEq_absorbingly 7 := fun h =>
  dTF ((@h SiProp DB _ _ dT dF iprop(True)).1 0 ⟨trivial, trivial⟩)

-- `Iris.ProofMode.intoInternalEq_plainly` idx 7: necessary (SiProp, discrete Bool true, false, P = True)
theorem w8c1_71 : ¬ drop0% Iris.ProofMode.intoInternalEq_plainly 7 := fun h =>
  dTF ((@h SiProp DB _ _ dT dF iprop(True)).1 0 ((show (iprop(True) : SiProp) ⊢ iprop(■ True) from plainly_pure.2) 0 trivial))

-- `Iris.ProofMode.intoInternalEq_persistently` idx 7: necessary (SiProp, discrete Bool true, false, P = True)
theorem w8c1_72 : ¬ drop0% Iris.ProofMode.intoInternalEq_persistently 7 := fun h =>
  dTF ((@h SiProp DB _ _ dT dF iprop(True)).1 0 trivial)

-- `Iris.ProofMode.frame_eq_embed` idx 5: removable (a ≡ b ⊢ ⎡a ≡ b⎤ holds for every embedding: rewrite with z ↦ ⎡a ≡ z⎤ and ⎡a ≡ a⎤ ⊣ ⎡True⎤ = True)
theorem w8c1_35 : drop% Iris.ProofMode.frame_eq_embed 5 := by
  intro P1 P2 _ _ _ p A _ a b P Q Q' h1 h2
  letI : OFE.NonExpansive (fun z : A => (embed (iprop(a ≡ z) : P1) : P2)) :=
    ⟨fun {_} _ _ h => embed_ne.ne ((internalEq.ne_r (PROP := P1) a).ne h)⟩
  have key : (iprop(a ≡ b) : P2) ⊢ embed (iprop(a ≡ b) : P1) :=
    internalEq.rewrite' (fun z : A => (embed (iprop(a ≡ z) : P1) : P2)) .rfl
      (true_intro.trans ((embed_pure True).2.trans (embed_mono internalEq.refl)))
  exact ⟨(sep_mono_left (intuitionisticallyIf_mono key)).trans (frame_embed_core h1 h2)⟩
