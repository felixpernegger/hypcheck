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

namespace W6c1
open Iris Iris.BI Iris.Std

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


def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩

theorem nt {Q : SiProp} (h : iprop(▷ Q) ⊢ iprop(◇ Q)) (h0 : Q.holds 0) (h1 : ¬ Q.holds 1) : False := by
  rcases h 1 h0 with h' | h'
  · exact h'
  · exact h1 h'

@[reducible] def idBupd : BIUpdate SiProp where
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

@[reducible] def gbBupd : BIUpdate GB where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h

theorem tfn {PROP : Type} [BI PROP] (Ψ : Tele.nil.{0}.Arg → PROP) : tforall Ψ = Ψ .nil := rfl
theorem ten {PROP : Type} [BI PROP] (Ψ : Tele.nil.{0}.Arg → PROP) : texist Ψ = Ψ .nil := rfl

end W6c1

open Iris Iris.BI Iris.Std W6c1

-- `Iris.BI.tforall_ne` idx 6: necessary (GB, TT = nil, Phi = True, Psi = False: Dist is equality in the discrete GB)
theorem w6c1_1 : ¬ drop0% Iris.BI.tforall_ne 6 := fun h =>
  (cast (congrFun (show (iprop(True) : GB) = iprop(False) from @h GB _ Tele.nil 0 (fun _ => iprop(True)) (fun _ => iprop(False))) false) trivial : (iprop(False) : GB) false)
-- `Iris.BI.tforall_congr` idx 5: necessary (GB, TT = nil, Phi = True, Psi = False)
theorem w6c1_2 : ¬ drop0% Iris.BI.tforall_congr 5 := fun h =>
  (@h GB _ Tele.nil (fun _ => iprop(True)) (fun _ => iprop(False))).1 false trivial
-- `Iris.BI.texist_ne` idx 6: necessary (GB, TT = nil, Phi = True, Psi = False)
theorem w6c1_3 : ¬ drop0% Iris.BI.texist_ne 6 := fun h =>
  (cast (congrFun (show (iprop(True) : GB) = iprop(False) from @h GB _ Tele.nil 0 (fun _ => iprop(True)) (fun _ => iprop(False))) false) trivial : (iprop(False) : GB) false)
-- `Iris.BI.texist_congr` idx 5: necessary (GB, TT = nil, Phi = True, Psi = False)
theorem w6c1_4 : ¬ drop0% Iris.BI.texist_congr 5 := fun h =>
  (@h GB _ Tele.nil (fun _ => iprop(True)) (fun _ => iprop(False))).1 false trivial
-- `Iris.BI.tforall_absorbing` idx 4: necessary (GB, TT = nil, Psi = emp (not absorbing))
theorem w6c1_5 : ¬ drop0% Iris.BI.tforall_absorbing 4 := fun h =>
  gb_emp_not_absorbing (@h GB _ Tele.nil (fun _ => iprop(emp)))
-- `Iris.BI.tforall_persistent` idx 5: necessary (GB, TT = nil, Psi = own1 (not persistent))
theorem w6c1_6 : ¬ drop0% Iris.BI.tforall_persistent 5 := fun h =>
  gb_own1_not_pers (@h GB _ Tele.nil inferInstance (fun _ => own1))
-- `Iris.BI.texist_affine` idx 4: necessary (GB, TT = nil, Psi = True (not affine))
theorem w6c1_7 : ¬ drop0% Iris.BI.texist_affine 4 := fun h =>
  gb_true_not_affine (@h GB _ Tele.nil (fun _ => iprop(True)))
-- `Iris.BI.texist_absorbing` idx 4: necessary (GB, TT = nil, Psi = emp)
theorem w6c1_8 : ¬ drop0% Iris.BI.texist_absorbing 4 := fun h =>
  gb_emp_not_absorbing (@h GB _ Tele.nil (fun _ => iprop(emp)))
-- `Iris.BI.texist_persistent` idx 4: necessary (GB, TT = nil, Psi = own1)
theorem w6c1_9 : ¬ drop0% Iris.BI.texist_persistent 4 := fun h =>
  gb_own1_not_pers (@h GB _ Tele.nil (fun _ => own1))
-- `Iris.BI.tforall_timeless` idx 4: necessary (SiProp, TT = nil, Psi = s0 (true only at step 0))
theorem w6c1_10 : ¬ drop0% Iris.BI.tforall_timeless 4 := fun h =>
  nt (@h SiProp _ Tele.nil (fun _ => s0)).timeless rfl (by intro h; cases h)
-- `Iris.BI.texist_timeless` idx 4: necessary (SiProp, TT = nil, Psi = s0)
theorem w6c1_11 : ¬ drop0% Iris.BI.texist_timeless 4 := fun h =>
  nt (@h SiProp _ Tele.nil (fun _ => s0)).timeless rfl (by intro h; cases h)
-- `Iris.BI.tforall_persistent` idx 3: necessary (PF (no BIPersistentlyForall), TT = one Nat binder, Psi k = evens or at least k: each persistent, the conjunction (evens) is not)
theorem w6c1_12 : ¬ drop0% Iris.BI.tforall_persistent 3 := fun h => by
  have H := (@h PF _ (Tele.cons (fun _ : Nat => Tele.nil)) (fun x => evk x.1)
    (fun x => ⟨fun n hn => ⟨evk_cof _, hn⟩⟩)).persistent
  rw [(tforall_forall _).to_eq] at H
  have H2 := H 0 (fun p ⟨x, hp⟩ => hp ▸ (Or.inl rfl : evk x.1 0))
  apply evk_all_not_cof
  obtain ⟨N, hN⟩ := H2.1
  exact ⟨N, fun m hm k => hN m hm _ ⟨⟨k, .nil⟩, rfl⟩⟩
-- `Iris.BIUpdate.mono` idx 5: necessary (SiProp with identity bupd, P = True, Q = False)
theorem w6c1_13 : ¬ drop0% Iris.BIUpdate.mono 5 := fun h =>
  @h SiProp _ idBupd iprop(True) iprop(False) 0 trivial
-- `Iris.bupd_mono` idx 5: necessary (SiProp with identity bupd, P = True, Q = False)
theorem w6c1_14 : ¬ drop0% Iris.bupd_mono 5 := fun h =>
  @h SiProp _ idBupd iprop(True) iprop(False) 0 trivial
-- `Iris.instAbsorbingBupd` idx 4: necessary (GB with identity bupd, P = emp)
theorem w6c1_15 : ¬ drop0% Iris.instAbsorbingBupd 4 := fun h =>
  gb_emp_not_absorbing (@h GB _ gbBupd iprop(emp))
-- `Iris.bupd_elim` idx 3: necessary (SiProp with constant-True bupd (not BIBUpdateSbi), P = False)
theorem w6c1_16 : ¬ drop0% Iris.bupd_elim 3 := fun h =>
  @h SiProp _ topBupd iprop(False) inferInstance inferInstance 0 trivial
-- `Iris.Examples.MyR_always_invalid` idx 2: necessary (S1 = S2 = "a": toAgree a op toAgree a is valid)
theorem w6c1_17 : ¬ drop0% Iris.Examples.MyR_always_invalid 2 := fun h =>
  h "a" "a" 0 (by
    simp only [ORA.ValidN, ORA.op, Iris.Examples.MyAg, optionValidN, optionOp]
    exact Agree.toAgree_op_validN_iff_dist.mpr OFE.Dist.rfl)
-- `Iris.Examples.proof_example_1` idx 3: removable (holds in every BI: the boxed wand is used by intuitionistically_elim, the existential is destructed in the spatial context)
theorem w6c1_18 : drop% Iris.Examples.proof_example_1 3 := by
  intro PROP α _ P Q R Φ
  iintro ⟨HP, HQ, #HR⟩ HRΦ
  ihave HΦ := (intuitionistically_elim : iprop(□ (R -∗ ∃ x, Φ x)) ⊢ _) $$ HRΦ
  ihave HΦ := HΦ $$ HR
  icases HΦ with ⟨%x, HΦ⟩
  iexists x
  isplitr [HP HQ]
  · iexact HΦ
  isplitl [HP]
  · iexact HP
  · iexact HQ

namespace W6c1
open Iris Iris.BI Iris.Std Iris.OFE

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF

theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩

/-- fupd soundness with arbitrary masks: ⊢ |={E1,E2}=> False is impossible in IProp. -/
theorem fupd_false (E1 E2 : CoPset) (H : ∀ [InvGS_gen .hasNoLC CGF], ⊢ (iprop(|={E1,E2}=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := E1) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))

/-- ⊢ |={∅}[∅]▷=> False is impossible in IProp (step_fupdN soundness). -/
theorem step_false (H : ∀ [InvGS_gen .hasNoLC CGF], ⊢ (iprop(|={∅}[∅]▷=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (step_fupdN_soundness (hlc := .hasNoLC) 1 0 (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (H.trans (fupd_mask_intro_discard LawfulSet.empty_subset))))

theorem fupd_loeb_false (H : ∀ [InvGS_gen .hasNoLC CGF],
    (iprop(▷ |={⊤}=> ⌜False⌝) : IProp CGF) ⊢ iprop(|={⊤}=> ⌜False⌝)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (true_intro.trans (loeb_weak H))))

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

/-- A step update with equal masks proving True. -/
theorem stepT [InvGS_gen .hasNoLC CGF] (E : CoPset) : ⊢ (iprop(|={E}[E]▷=> True) : IProp CGF) :=
  (true_intro : (emp : IProp CGF) ⊢ iprop(True)).trans ((fupd_intro.trans later_intro).trans fupd_intro)

/-- Constant-True basic update on IProp (lawful in any BI). -/
@[reducible] noncomputable def topBupdI : BIUpdate (IProp CGF) where
  bupd _ := iprop(True)
  bupd_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  intro := true_intro
  mono _ := .rfl
  trans := .rfl
  frame_right := true_intro

end W6c1

open Iris Iris.BI Iris.Std W6c1

-- `Iris.BIFUpdate.mono` idx 7: necessary (IProp (closed-proofs GF), P = True, Q = False, masks top: fupd soundness)
theorem w6c1_19 : ¬ drop0% Iris.BIFUpdate.mono 7 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => (true_intro.trans fupd_intro).trans (@h (IProp CGF) _ _ ⊤ ⊤ iprop(True) iprop(⌜False⌝))
-- `Iris.fupd_mono` idx 7: necessary (IProp, P = True, Q = False, masks top: fupd soundness)
theorem w6c1_20 : ¬ drop0% Iris.fupd_mono 7 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => (true_intro.trans fupd_intro).trans (@h (IProp CGF) _ _ ⊤ ⊤ iprop(True) iprop(⌜False⌝))
-- `Iris.BIFUpdate.mask_frame_right_strong` idx 7: necessary (IProp, E1 = E2 = Ef = top, P = False: premise holds since top, top not disjoint; fupd soundness)
theorem w6c1_21 : ¬ drop0% Iris.BIFUpdate.mask_frame_right_strong 7 := fun h =>
  fupd_false (⊤ ∪ ⊤) (⊤ ∪ ⊤) fun {_} => ((true_intro.trans fupd_intro).trans
    (BIFUpdate.mono (Q := iprop(⌜(⊤ : CoPset) ## ⊤⌝ → ⌜False⌝)) (by iintro _ %hd; exact absurd hd full_not_disj))).trans
    (@h (IProp CGF) _ _ ⊤ ⊤ ⊤ iprop(⌜False⌝))
-- `Iris.fupd_mask_frame_right_strong` idx 7: necessary (IProp, E1 = E2 = Ef = top, P = False; fupd soundness)
theorem w6c1_22 : ¬ drop0% Iris.fupd_mask_frame_right_strong 7 := fun h =>
  fupd_false (⊤ ∪ ⊤) (⊤ ∪ ⊤) fun {_} => ((true_intro.trans fupd_intro).trans
    (BIFUpdate.mono (Q := iprop(⌜(⊤ : CoPset) ## ⊤⌝ → ⌜False⌝)) (by iintro _ %hd; exact absurd hd full_not_disj))).trans
    (@h (IProp CGF) _ _ ⊤ ⊤ ⊤ iprop(⌜False⌝))
-- `Iris.fupd_elim` idx 8: necessary (IProp, Q = True, P = False, masks top; fupd soundness)
theorem w6c1_23 : ¬ drop0% Iris.fupd_elim 8 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => (true_intro.trans fupd_intro).trans (@h (IProp CGF) _ _ ⊤ ⊤ ⊤ iprop(⌜False⌝) iprop(True))
-- `Iris.fupd_mask_weaken` idx 7: necessary (IProp, E1 = empty, E2 = E3 = top, P = True: gives |={empty,top}=> _ (open_top_false))
theorem w6c1_24 : ¬ drop0% Iris.fupd_mask_weaken 7 := fun h =>
  open_top_false fun {_} => ⟨_, (wand_intro (true_intro.trans fupd_intro)).trans (@h (IProp CGF) _ _ ∅ ⊤ ⊤ iprop(True))⟩
-- `Iris.fupd_mask_subseteq_emptyset_difference` idx 5: necessary (IProp, E1 = empty, E2 = top: |={empty,top}=> _ (open_top_false))
theorem w6c1_25 : ¬ drop0% Iris.fupd_mask_subseteq_emptyset_difference 5 := fun h =>
  open_top_false fun {_} => ⟨_, @h (IProp CGF) _ _ ∅ ⊤⟩
-- `Iris.fupd_mask_frame` idx 8: necessary (IProp, E = empty, E1 = E2 = E' = top, P = True: |={empty,top}=> _)
theorem w6c1_26 : ¬ drop0% Iris.fupd_mask_frame 8 := fun h =>
  open_top_false fun {_} => ⟨_, ((true_intro.trans (fupd_mask_intro_discard (fun x hx => mem_union.2 (.inl hx)))).trans fupd_intro).trans
    (@h (IProp CGF) _ _ ∅ ⊤ ⊤ ⊤ iprop(True))⟩
-- `Iris.fupd_mask_frame_acc` idx 9: necessary (IProp, E = empty, E' = E1 = E2 = top, Q = |={top\top,top}=> emp, P = True: |={empty,top}=> _)
theorem w6c1_27 : ¬ drop0% Iris.fupd_mask_frame_acc 9 := fun h =>
  open_top_false fun {_} => ⟨_, by
    have A := (fupd_mask_subseteq (PROP := IProp CGF) (E1 := ⊤) (E2 := ⊤ \ ⊤) (fun _ _ => CoPset.mem_full)).trans
      (@h (IProp CGF) _ _ ∅ ⊤ ⊤ ⊤ iprop(True) iprop(|={⊤ \ ⊤,⊤}=> emp))
    have B : ⊢ (iprop((|={⊤ \ ⊤,⊤}=> emp) -∗ |={∅ \ ⊤,⊤}=> ((∀ R, (|={⊤ \ ⊤,⊤}=> R) -∗ |={∅ \ ⊤,∅}=> R) -∗ True)) : IProp CGF) :=
      wand_intro (emp_sep.1.trans (BIFUpdate.mono (wand_intro true_intro)))
    exact emp_sep.2.trans ((sep_mono A B).trans wand_elim_left)⟩
-- `Iris.step_fupd_mask_mono` idx 9: necessary (IProp, Eo1 = Ei1 = Ei2 = top, Eo2 = empty: RHS starts |={empty,top}=>)
theorem w6c1_28 : ¬ drop0% Iris.step_fupd_mask_mono 9 := fun h =>
  open_top_false fun {_} => ⟨_, (stepT ⊤).trans (@h (IProp CGF) _ _ ⊤ ∅ ⊤ ⊤ iprop(True) LawfulSet.subset_refl)⟩
-- `Iris.step_fupd_intro` idx 6: necessary (IProp, Ei = top, Eo = empty, P = True: |={empty,top}=>)
theorem w6c1_29 : ¬ drop0% Iris.step_fupd_intro 6 := fun h =>
  open_top_false fun {_} => ⟨_, (true_intro.trans later_intro).trans (@h (IProp CGF) _ _ ⊤ ∅ iprop(True))⟩
-- `Iris.step_fupdN_intro` idx 7: necessary (IProp, n = 1, Ei = top, Eo = empty, P = True)
theorem w6c1_30 : ¬ drop0% Iris.step_fupdN_intro 7 := fun h =>
  open_top_false fun {_} => ⟨_, (true_intro.trans later_intro).trans (@h (IProp CGF) _ _ 1 ⊤ ∅ iprop(True))⟩
-- `Iris.step_fupdN_le` idx 9: necessary (IProp, n = 0, m = 1, Eo = empty, Ei = top, P = True)
theorem w6c1_31 : ¬ drop0% Iris.step_fupdN_le 9 := fun h =>
  open_top_false fun {_} => ⟨_, true_intro.trans (@h (IProp CGF) _ _ 0 1 ∅ ⊤ iprop(True) (Nat.zero_le 1))⟩
-- `Iris.step_fupdN_le` idx 8: necessary (IProp, n = 1, m = 0, masks top, P = |={top}=> False: with step_fupd_intro gives later P |- P, Loeb + fupd soundness)
theorem w6c1_32 : ¬ drop0% Iris.step_fupdN_le 8 := fun h =>
  fupd_loeb_false fun {_} => (step_fupd_intro LawfulSet.subset_refl).trans
    (@h (IProp CGF) _ _ 1 0 ⊤ ⊤ iprop(|={⊤}=> ⌜False⌝) LawfulSet.subset_refl)
-- `Iris.step_fupd_mono` idx 7: necessary (IProp, Eo = Ei = empty, Q = True, P = False: step_fupdN_soundness)
theorem w6c1_33 : ¬ drop0% Iris.step_fupd_mono 7 := fun h =>
  step_false fun {_} => (stepT ∅).trans (@h (IProp CGF) _ _ ∅ ∅ iprop(⌜False⌝) iprop(True))
-- `Iris.step_fupdN_mono` idx 8: necessary (IProp, n = 1, Eo = Ei = empty, P = True, Q = False: step_fupdN_soundness)
theorem w6c1_34 : ¬ drop0% Iris.step_fupdN_mono 8 := fun h =>
  step_false fun {_} => (stepT ∅).trans (@h (IProp CGF) _ _ 1 ∅ ∅ iprop(True) iprop(⌜False⌝))
-- `Iris.BIUpdateFUpdate.fupd_of_bupd` idx 4: necessary (IProp with constant-True bupd and the real fupd, P = False: fupd soundness)
theorem w6c1_35 : ¬ drop0% Iris.BIUpdateFUpdate.fupd_of_bupd 4 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => true_intro.trans (@h (IProp CGF) _ topBupdI inferInstance iprop(⌜False⌝) ⊤)

namespace W6c1
open Iris Iris.Std Iris.HeapLang

def l0 : Loc := ⟨0⟩
def iV (k : Int) : Val := .lit (.int k)
def σ0 (v : Val) : HeapLang.State := { heap := PartialMap.singleton (M := HeapF) l0 (some v), usedProphId := ∅ }
theorem hget (v : Val) : get? (M := HeapF) (σ0 v).heap l0 = some (some v) :=
  LawfulPartialMap.get?_singleton_eq rfl
theorem hgetS (v : Val) : (σ0 v).get? l0 = some (some v) := hget v

end W6c1

open Iris Iris.Std Iris.HeapLang W6c1

-- `Iris.HeapLang.storeS_det` idx 7: necessary (no step given: efs = [stuck] is not [])
theorem w6c1_36 : ¬ drop0% Iris.HeapLang.storeS_det 7 := fun h =>
  List.cons_ne_nil _ _ (@h l0 (iV 0) (default : HeapLang.State) [] Exp.stuck (default : HeapLang.State) [Exp.stuck]).2.2.2
-- `Iris.HeapLang.freeS_det` idx 6: necessary (no step given: efs = [stuck] is not [])
theorem w6c1_37 : ¬ drop0% Iris.HeapLang.freeS_det 6 := fun h =>
  List.cons_ne_nil _ _ (@h l0 (default : HeapLang.State) [] Exp.stuck (default : HeapLang.State) [Exp.stuck]).2.2.2
-- `Iris.HeapLang.loadS_det` idx 8: necessary (heap l0 -> 0, no step given: efs = [stuck] is not [])
theorem w6c1_38 : ¬ drop0% Iris.HeapLang.loadS_det 8 := fun h =>
  List.cons_ne_nil _ _ (@h l0 (iV 0) (σ0 (iV 0)) [] Exp.stuck (default : HeapLang.State) [Exp.stuck] (hget _)).2.2.2
-- `Iris.HeapLang.xchgS_det` idx 9: necessary (heap l0 -> 0, no step given: efs = [stuck])
theorem w6c1_39 : ¬ drop0% Iris.HeapLang.xchgS_det 9 := fun h =>
  List.cons_ne_nil _ _ (@h l0 (iV 0) (iV 0) (σ0 (iV 0)) [] Exp.stuck (default : HeapLang.State) [Exp.stuck] (hget _)).2.2.2
-- `Iris.HeapLang.faaS_det` idx 9: necessary (heap l0 -> 0, no step given: efs = [stuck])
theorem w6c1_40 : ¬ drop0% Iris.HeapLang.faaS_det 9 := fun h =>
  List.cons_ne_nil _ _ (@h l0 0 0 (σ0 (iV 0)) [] Exp.stuck (default : HeapLang.State) [Exp.stuck] (hget _)).2.2.2
-- `Iris.HeapLang.cmpXchgS_det_true` idx 11: necessary (heap l0 -> 0, vl = v1, no step given: efs = [stuck])
theorem w6c1_41 : ¬ drop0% Iris.HeapLang.cmpXchgS_det_true 11 := fun h =>
  List.cons_ne_nil _ _ (@h l0 (iV 0) (iV 0) (iV 0) (σ0 (iV 0)) [] Exp.stuck (default : HeapLang.State) [Exp.stuck] (hget _) (by decide)).2.2.2
-- `Iris.HeapLang.cmpXchgS_det_false` idx 11: necessary (heap l0 -> 0, vl = 0, v1 = 1, no step given: efs = [stuck])
theorem w6c1_42 : ¬ drop0% Iris.HeapLang.cmpXchgS_det_false 11 := fun h =>
  List.cons_ne_nil _ _ (@h l0 (iV 1) (iV 0) (iV 0) (σ0 (iV 0)) [] Exp.stuck (default : HeapLang.State) [Exp.stuck] (hget _) (by decide)).2.2.2
-- `Iris.HeapLang.loadS_det` idx 7: necessary (heap l0 -> 0, real load step, claimed value v = 1)
theorem w6c1_43 : ¬ drop0% Iris.HeapLang.loadS_det 7 := fun h =>
  absurd (@h l0 (iV 1) (σ0 (iV 0)) _ _ _ _ (BaseStep.loadS l0 (iV 0) (σ0 (iV 0)) (hgetS _))).2.1 (by decide)
-- `Iris.HeapLang.xchgS_det` idx 8: necessary (heap l0 -> 0, real xchg step, claimed old value v1 = 1)
theorem w6c1_44 : ¬ drop0% Iris.HeapLang.xchgS_det 8 := fun h =>
  absurd (@h l0 (iV 1) (iV 2) (σ0 (iV 0)) _ _ _ _ (BaseStep.xchgS l0 (iV 0) (iV 2) (σ0 (iV 0)) (hgetS _))).2.1 (by decide)
-- `Iris.HeapLang.faaS_det` idx 8: necessary (heap l0 -> 0, real faa step, claimed old value i1 = 1)
theorem w6c1_45 : ¬ drop0% Iris.HeapLang.faaS_det 8 := fun h =>
  absurd (@h l0 1 2 (σ0 (iV 0)) _ _ _ _ (BaseStep.faaS l0 0 2 (σ0 (iV 0)) (hgetS _))).2.1 (by decide)
-- `Iris.HeapLang.cmpXchgS_det_true` idx 9: necessary (heap l0 -> 1, vl = v1 = 0: the real step compares 1 with 0 and returns false)
theorem w6c1_46 : ¬ drop0% Iris.HeapLang.cmpXchgS_det_true 9 := fun h =>
  absurd (@h l0 (iV 0) (iV 2) (iV 0) (σ0 (iV 1)) _ _ _ _ (by decide)
    (BaseStep.cmpXchgS l0 (iV 0) (iV 2) (iV 1) (σ0 (iV 1)) false (hgetS _) rfl (by decide))).2.1 (by decide)
-- `Iris.HeapLang.cmpXchgS_det_true` idx 10: necessary (heap l0 -> 0 = vl, v1 = 1: the real step fails and returns false)
theorem w6c1_47 : ¬ drop0% Iris.HeapLang.cmpXchgS_det_true 10 := fun h =>
  absurd (@h l0 (iV 1) (iV 2) (iV 0) (σ0 (iV 0)) _ _ _ _ (hget _)
    (BaseStep.cmpXchgS l0 (iV 1) (iV 2) (iV 0) (σ0 (iV 0)) false (hgetS _) rfl (by decide))).2.1 (by decide)
-- `Iris.HeapLang.cmpXchgS_det_false` idx 9: necessary (heap l0 -> 1 = v1, vl = 0: the real step succeeds)
theorem w6c1_48 : ¬ drop0% Iris.HeapLang.cmpXchgS_det_false 9 := fun h =>
  absurd (@h l0 (iV 1) (iV 2) (iV 0) (σ0 (iV 1)) _ _ _ _ (by decide)
    (BaseStep.cmpXchgS l0 (iV 1) (iV 2) (iV 1) (σ0 (iV 1)) true (hgetS _) rfl (by decide))).2.1 (by decide)
-- `Iris.HeapLang.cmpXchgS_det_false` idx 10: necessary (heap l0 -> 0 = vl = v1: the real step succeeds)
theorem w6c1_49 : ¬ drop0% Iris.HeapLang.cmpXchgS_det_false 10 := fun h =>
  absurd (@h l0 (iV 0) (iV 2) (iV 0) (σ0 (iV 0)) _ _ _ _ (hget _)
    (BaseStep.cmpXchgS l0 (iV 0) (iV 2) (iV 0) (σ0 (iV 0)) true (hgetS _) rfl (by decide))).2.1 (by decide)

namespace W6c1
open Iris Iris.BI Iris.Std Iris.OFE

/-- Opening the whole mask hands out the token ownE ⊤. -/
theorem own_open [InvGS_gen .hasNoLC CGF] : ⊢ (iprop(|={⊤,∅}=> ownE ⊤) : IProp CGF) := by
  refine .trans ?_ (fupd_unfold_no_lc ⊤ ∅ _).2
  iintro - ⟨Hw, HE⟩
  imod ownE_empty with H0
  imodintro
  iapply except0_intro
  isplitl [Hw]
  · iexact Hw
  isplitl [H0]
  · iexact H0
  · iexact HE

/-- Holding ownE ⊤ while the mask ⊤ is enabled is contradictory. -/
theorem own_conf [InvGS_gen .hasNoLC CGF] (E : CoPset) : (ownE ⊤ : IProp CGF) ⊢ iprop(|={⊤,E}=> ⌜False⌝) := by
  refine .trans ?_ (fupd_unfold_no_lc ⊤ E _).2
  iintro H ⟨Hw, HE⟩
  ihave %hd : ⌜(⊤ : CoPset) ## ⊤⌝ $$ [H HE]
  · iapply ownE_disjoint
    isplitl [H] <;> iassumption
  exact absurd hd full_not_disj

open Iris.Instances in
theorem cr_upd : (iprop(True) : UPred Credit) ⊢ iprop(|==> UPred.ownM (1 : Credit)) :=
  (UPred.ownM_unit' (M := Credit)).2.trans (UPred.bupd_ownM_update (fun _ _ _ => trivial))

theorem cr_bad (h : (iprop(True) : UPred Credit) ⊢ UPred.ownM (1 : Credit)) : False := by
  have := h 0 ⟨0, trivial⟩ trivial
  simp [UPred.ownM] at this
  obtain ⟨z, hz⟩ := this
  have hz' : (0 : Nat) = 1 + z := hz
  omega

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

theorem na_pl_emp : (iprop(True) : UPred NA) ⊢ iprop(|==> ■ emp) :=
  (show (iprop(True) : UPred NA) ⊢ iprop(■ emp) from fun _ _ _ => rfl).trans BIUpdate.intro

end W6c1

open Iris Iris.BI Iris.Std W6c1

-- `Iris.fupd_mask_mono` idx 6: necessary (IProp, E1 = top, E2 = empty, P = False: open the full mask to get ownE top, which contradicts |={top}=>; fupd soundness)
theorem w6c1_50 : ¬ drop0% Iris.fupd_mask_mono 6 := fun h =>
  fupd_false ⊤ ∅ fun {_} => own_open.trans ((fupd_mono ((own_conf ⊤).trans
    (@h (IProp CGF) _ _ ⊤ ∅ iprop(⌜False⌝)))).trans fupd_trans)
-- `Iris.fupd_mask_frame_right` idx 7: necessary (IProp, E1 = Ef = top, E2 = empty, P = ownE top: gives ownE top twice; fupd soundness)
theorem w6c1_51 : ¬ drop0% Iris.fupd_mask_frame_right 7 := fun h =>
  fupd_false (⊤ ∪ ⊤) (∅ ∪ ⊤) fun {_} => (own_open.trans (@h (IProp CGF) _ _ ⊤ ∅ ⊤ (ownE ⊤))).trans
    ((fupd_mono (own_conf (∅ ∪ ⊤))).trans fupd_trans)
-- `Iris.bupd_elim` idx 5: necessary (UPred Credit, P = ownM 1 (absorbing, not plain): 0 can be updated to 1)
theorem w6c1_52 : ¬ drop0% Iris.bupd_elim 5 := fun h =>
  cr_bad (cr_upd.trans (@h (UPred Credit) _ _ _ (UPred.ownM (1 : Credit)) inferInstance))
-- `Iris.bupd_plainly_elim` idx 5: necessary (UPred NA (non-affine), P = emp: plainly emp holds everywhere, True does not entail emp)
theorem w6c1_53 : ¬ drop0% Iris.bupd_plainly_elim 5 := fun h =>
  na_true_not_emp (na_pl_emp.trans (@h (UPred NA) _ _ _ iprop(emp)))
-- `Iris.step_fupd_mask_frame_right` idx 8: removable (frame with Ef minus Ei (disjoint from Eo and Ei) by the library lemma, then step_fupd_mask_mono (inner mask shrinks from Ei u Ef to Ei u (Ef minus Ei), outer grows))
theorem w6c1_54 : drop% Iris.step_fupd_mask_frame_right 8 := by
  intro PROP _ _ Eo Ei Ef P hEo
  refine (step_fupd_mask_frame_right (Ef := Ef \ Ei)
    (fun x ⟨h1, h2⟩ => hEo x ⟨h1, (mem_diff.1 h2).1⟩) (fun x ⟨h1, h2⟩ => (mem_diff.1 h2).2 h1)).trans
    (step_fupd_mask_mono ?_ ?_)
  · intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact mem_union.2 (.inl hx)
    · by_cases hi : x ∈ Ei
      · exact mem_union.2 (.inl hi)
      · exact mem_union.2 (.inr (mem_diff.2 ⟨hx, hi⟩))
  · intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact mem_union.2 (.inl hx)
    · exact mem_union.2 (.inr (mem_diff.1 hx).1)

namespace W6c1
open Iris Iris.BI Iris.Std Iris.OFE

def naA : UPred NA := iprop(UPred.ownM NA.a ∗ True)

/-- Basic update P ∨ (ownM a ∗ True) on UPred NA: lawful, but not BIBUpdateSbi. -/
@[reducible] def naBupd : BIUpdate (UPred NA) where
  bupd P := iprop(P ∨ naA)
  bupd_ne := ⟨fun _ _ _ h => or_ne.ne h OFE.Dist.rfl⟩
  intro := or_intro_l
  mono h := or_mono h .rfl
  trans := or_elim .rfl or_intro_r
  frame_right := sep_or_right.1.trans (or_mono .rfl (sep_assoc.1.trans (sep_mono_right true_intro)))

theorem na_a_holds : naA 0 ⟨.a, trivial⟩ := ⟨.a, .e, rfl, rfl, trivial⟩
theorem na_a_unit : ¬ naA 0 ⟨.e, trivial⟩ := fun ⟨x1, x2, H, h1, _⟩ => by cases h1; cases H

instance naPlainEmp : Plain (iprop(emp) : UPred NA) := ⟨fun _ _ _ => rfl⟩

theorem na_upd_emp : (iprop(True) : UPred NA) ⊢ iprop(|==> emp) :=
  fun _ _ _ _ _ _ _ => ⟨.e, trivial, rfl⟩

end W6c1

open Iris Iris.BI Iris.Std W6c1

-- `Iris.bupd_plain` idx 3: necessary (UPred NA with bupd P := P or (ownM a * True) (lawful, not BIBUpdateSbi), P = False)
theorem w6c1_55 : ¬ drop0% Iris.bupd_plain 3 := fun h =>
  ((@h (UPred NA) _ naBupd iprop(False) inferInstance).plain 0 ⟨.a, trivial⟩ (Or.inr na_a_holds)).elim
    (fun f => f) na_a_unit
-- `Iris.bupd_elim` idx 6: necessary (UPred NA (non-affine), P = emp (plain, not absorbing): |==> emp holds at a)
theorem w6c1_56 : ¬ drop0% Iris.bupd_elim 6 := fun h =>
  na_true_not_emp (na_upd_emp.trans (@h (UPred NA) _ _ _ iprop(emp) naPlainEmp))

namespace W6c1
open Iris Iris.BI Iris.Std Iris.Std.LawfulSet

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

theorem top_ne_empty : (⊤ : CoPset) ≠ ∅ := fun h => CoPset.mem_empty (p := .xH) (by rw [← h]; exact CoPset.mem_full)

end W6c1

open Iris Iris.BI Iris.Std Iris.Std.LawfulSet W6c1

-- `Iris.instAbsorbingFupd` idx 6: necessary (MK (non-affine mask-ownership BI with lawful fupd), E1 = E2 = empty, P = emp: |={empty}=> emp is not absorbing)
theorem w6c1_57 : ¬ drop0% Iris.instAbsorbingFupd 6 := fun h => by
  have H : mfupd ∅ ∅ iprop(emp) ⊤ := (@h MK _ _ ∅ ∅ iprop(emp)).absorbing ⊤
    ⟨⊤, ∅, djs dj0, union_empty_right.symm, trivial,
      show mfupd ∅ ∅ iprop(emp) ∅ from fun _ => ⟨∅, dj0, rfl, rfl⟩⟩
  obtain ⟨B, _, e, hB⟩ := H (djs dj0)
  have hB' : B = ∅ := hB
  rw [hB', union_empty_right, union_empty_right] at e
  exact top_ne_empty e
-- `Iris.fupd_mask_intro_discard` idx 6: necessary (MK, E1 = top, E2 = empty, P = emp: the opened tokens cannot be discarded)
theorem w6c1_58 : ¬ drop0% Iris.fupd_mask_intro_discard 6 := fun h => by
  have H : mfupd ⊤ ∅ iprop(emp) ∅ := @h MK _ _ ⊤ ∅ iprop(emp) (fun _ _ => CoPset.mem_full) ∅ rfl
  obtain ⟨B, _, e, hB⟩ := H dj0
  have hB' : B = ∅ := hB
  rw [hB', union_empty_left, union_empty_right] at e
  exact top_ne_empty e
-- `Iris.step_fupdN_contractive` idx 6: necessary (MK (discrete, later = id), masks empty, n = 0: True and False are 0-later-close but the step updates differ)
theorem w6c1_59 : ¬ drop0% Iris.step_fupdN_contractive 6 := fun h => by
  have H : _ = _ := (@h MK _ _ ∅ ∅ 0).distLater_dist (n := 0) (x := iprop(True)) (y := iprop(False))
    (fun _ hm => absurd hm (Nat.not_lt_zero _))
  have H2 := congrFun H ∅
  have hT : mfupd ∅ ∅ (mfupd ∅ ∅ iprop(True)) ∅ := fun _ => ⟨∅, dj0, rfl, fun _ => ⟨∅, dj0, rfl, trivial⟩⟩
  have hF : mfupd ∅ ∅ (mfupd ∅ ∅ iprop(False)) ∅ := cast H2 hT
  obtain ⟨B, _, _, hB⟩ := hF dj0
  obtain ⟨_, _, _, f⟩ := hB (djs dj0)
  exact f

namespace W6c1
open Iris Iris.BI

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

/-- In UPred AX, |==> ownM a holds at a but not at the unit (frame a makes a • a invalid). -/
theorem ax_upd_a : (iprop(|==> oX) : UPred AX) 0 ⟨.a, by show AX.a ≠ AX.b; decide⟩ :=
  fun _ _ _ hv => ⟨.a, hv, (Or.inr (Or.inl rfl) : AX.a = .e ∨ AX.a = AX.a ∨ AX.a = .b)⟩
theorem ax_upd_e : ¬ (iprop(|==> oX) : UPred AX) 0 ⟨.e, by show AX.e ≠ AX.b; decide⟩ := fun h => by
  obtain ⟨x', hv, ho⟩ := h 0 .a (Nat.le_refl 0) (show AX.op AX.e AX.a ≠ AX.b by decide)
  have hv' : AX.op x' AX.a ≠ AX.b := hv
  have ho' : AX.a = .e ∨ AX.a = x' ∨ x' = .b := ho
  cases x' <;> simp_all [AX.op]

end W6c1

open Iris Iris.BI W6c1

-- `Iris.bupd_plain` idx 5: necessary (UPred AX (a • a invalid), P = ownM a: |==> ownM a holds at a but not at the unit (frame a), so it is not plain)
theorem w6c1_60 : ¬ drop0% Iris.bupd_plain 5 := fun h =>
  ax_upd_e ((@h (UPred AX) _ _ _ oX).plain 0 _ ax_upd_a)
