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

namespace W4c4
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

end W4c4

open Iris Iris.BI W4c4


-- `Iris.BI.pure_elim_right` idx 5: necessary (GB, phi = True, Q = True, R = False)
theorem c4_1 : ¬ drop0% Iris.BI.pure_elim_right 5 := fun h =>
  @h GB _ True iprop(True) iprop(False) false ⟨trivial, trivial⟩
-- `Iris.BI.pure_true` idx 3: necessary (GB, phi = False)
theorem c4_2 : ¬ drop0% Iris.BI.pure_true 3 := fun h => (@h GB _ False).2 false trivial
-- `Iris.BI.pure_false` idx 3: necessary (GB, phi = True)
theorem c4_3 : ¬ drop0% Iris.BI.pure_false 3 := fun h => (@h GB _ True).1 false trivial
-- `Iris.BI.pure_iff` idx 4: necessary (GB, True vs False)
theorem c4_4 : ¬ drop0% Iris.BI.pure_iff 4 := fun h => (@h GB _ True False).1 false trivial
-- `Iris.BI.pure_imp_elim` idx 4: necessary (GB, phi = False, R = False)
theorem c4_5 : ¬ drop0% Iris.BI.pure_imp_elim 4 := fun h =>
  @h GB _ False iprop(False) false (fun h => h)
-- `Iris.BI.pure_wand_forall` idx 4: necessary (GB non-affine, phi = True, P = emp)
theorem c4_6 : ¬ drop0% Iris.BI.pure_wand_forall 4 := fun h =>
  Bool.noConfusion ((@h GB _ True iprop(emp)).2 false (fun p ⟨_, e⟩ => e ▸ rfl) true trivial : true = false)
-- `Iris.BI.affinely_congr` idx 4: necessary (GB, True vs False)
theorem c4_7 : ¬ drop0% Iris.BI.affinely_congr 4 := fun h =>
  ((@h GB _ iprop(True) iprop(False)).1 false ⟨rfl, trivial⟩).2
-- `Iris.BI.affinely_intro_affinely` idx 4: necessary (GB, True, False)
theorem c4_8 : ¬ drop0% Iris.BI.affinely_intro_affinely 4 := fun h =>
  (@h GB _ iprop(True) iprop(False) false ⟨rfl, trivial⟩).2
-- `Iris.BI.affinely_sep_right` idx 2: necessary (GB is not positive, P = Q = own1)
theorem c4_9 : ¬ drop0% Iris.BI.affinely_sep_right 2 := fun h => by
  obtain ⟨a, b, e, ha, hb1, hb2⟩ := @h GB _ own1 own1 false ⟨rfl, true, true, rfl, rfl, rfl⟩
  have hb1 : b = false := hb1
  have hb2 : b = true := hb2
  subst hb1; exact Bool.noConfusion hb2
-- `Iris.BI.affinely_sep` idx 2: necessary (GB is not positive, P = Q = own1)
theorem c4_10 : ¬ drop0% Iris.BI.affinely_sep 2 := fun h => by
  obtain ⟨a, b, e, ⟨ha1, ha2⟩, hb⟩ := (@h GB _ own1 own1).1 false ⟨rfl, true, true, rfl, rfl, rfl⟩
  have ha1 : a = false := ha1
  have ha2 : a = true := ha2
  subst ha1; exact Bool.noConfusion ha2
-- `Iris.BI.affine_mono` idx 5: necessary (GB, P = Q = True)
theorem c4_11 : ¬ drop0% Iris.BI.affine_mono 5 := fun h =>
  gb_true_not_affine (@h GB _ iprop(True) iprop(True) (fun _ h => h))
-- `Iris.BI.and_affine_left` idx 4: necessary (GB, P = Q = True)
theorem c4_12 : ¬ drop0% Iris.BI.and_affine_left 4 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) iprop(True)).1 true ⟨trivial, trivial⟩ : true = false)
-- `Iris.BI.and_affine_right` idx 4: necessary (GB, P = Q = True)
theorem c4_13 : ¬ drop0% Iris.BI.and_affine_right 4 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) iprop(True)).1 true ⟨trivial, trivial⟩ : true = false)
-- `Iris.BI.or_affine` idx 4: necessary (GB, P = True, Q = emp)
theorem c4_14 : ¬ drop0% Iris.BI.or_affine 4 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) iprop(emp) _).1 true (.inl trivial) : true = false)
-- `Iris.BI.or_affine` idx 5: necessary (GB, P = emp, Q = True)
theorem c4_15 : ¬ drop0% Iris.BI.or_affine 5 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp) iprop(True) _).1 true (.inr trivial) : true = false)
-- `Iris.BI.forall_affine` idx 5: necessary (GB, alpha = True, Phi = True)
theorem c4_16 : ¬ drop0% Iris.BI.forall_affine 5 := fun h =>
  Bool.noConfusion ((@h True GB ⟨trivial⟩ _ (fun _ => iprop(True))).1 true
    (fun p ⟨_, e⟩ => e ▸ trivial) : true = false)
-- `Iris.BI.exists_affine` idx 4: necessary (GB, alpha = True, Phi = True)
theorem c4_17 : ¬ drop0% Iris.BI.exists_affine 4 := fun h =>
  Bool.noConfusion ((@h GB True _ (fun _ => iprop(True))).1 true
    ⟨_, ⟨trivial, rfl⟩, trivial⟩ : true = false)
-- `Iris.BI.sep_affine` idx 4: necessary (GB, P = True, Q = emp)
theorem c4_18 : ¬ drop0% Iris.BI.sep_affine 4 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) iprop(emp) _).1 true ⟨true, false, rfl, trivial, rfl⟩ : true = false)
-- `Iris.BI.absorbingly_congr` idx 4: necessary (GB, True vs False)
theorem c4_19 : ¬ drop0% Iris.BI.absorbingly_congr 4 := fun h => by
  obtain ⟨a, b, e, _, hb⟩ := (@h GB _ iprop(True) iprop(False)).1 false ⟨false, false, rfl, trivial, trivial⟩
  exact hb
-- `Iris.BI.absorbingly_mono` idx 4: necessary (GB, True, False)
theorem c4_20 : ¬ drop0% Iris.BI.absorbingly_mono 4 := fun h => by
  obtain ⟨a, b, e, _, hb⟩ := @h GB _ iprop(True) iprop(False) false ⟨false, false, rfl, trivial, trivial⟩
  exact hb
-- `Iris.BI.affinely_absorbingly` idx 2: necessary (GB is not positive, P = own1)
theorem c4_21 : ¬ drop0% Iris.BI.affinely_absorbingly 2 := fun h =>
  Bool.noConfusion ((@h GB _ own1).1 false ⟨rfl, true, true, rfl, trivial, rfl⟩).2
-- `Iris.BI.affinely_absorbingly_elim` idx 3: necessary (GB is not positive, P = own1)
theorem c4_22 : ¬ drop0% Iris.BI.affinely_absorbingly_elim 3 := fun h =>
  Bool.noConfusion ((@h GB _ own1).1 false ⟨rfl, true, true, rfl, trivial, rfl⟩).2
-- `Iris.BI.and_absorbing` idx 4: necessary (GB, P = emp, Q = True)
theorem c4_23 : ¬ drop0% Iris.BI.and_absorbing 4 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp) iprop(True) _).1 true
    ⟨true, false, rfl, trivial, rfl, trivial⟩).1
-- `Iris.BI.and_absorbing` idx 5: necessary (GB, P = True, Q = emp)
theorem c4_24 : ¬ drop0% Iris.BI.and_absorbing 5 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) iprop(emp) _).1 true
    ⟨true, false, rfl, trivial, trivial, rfl⟩).2
-- `Iris.BI.or_absorbing` idx 4: necessary (GB, P = emp, Q = False)
theorem c4_25 : ¬ drop0% Iris.BI.or_absorbing 4 := fun h => by
  rcases (@h GB _ iprop(emp) iprop(False) _).1 true ⟨true, false, rfl, trivial, .inl rfl⟩ with h | h
  · exact Bool.noConfusion (h : true = false)
  · exact h
-- `Iris.BI.forall_absorbing` idx 4: necessary (GB, alpha = True, Phi = emp)
theorem c4_26 : ¬ drop0% Iris.BI.forall_absorbing 4 := fun h =>
  Bool.noConfusion ((@h GB True _ (fun _ => iprop(emp))).1 true
    ⟨true, false, rfl, trivial, fun p ⟨_, e⟩ => e ▸ rfl⟩ _ ⟨trivial, rfl⟩ : true = false)
-- `Iris.BI.exists_absorbing` idx 4: necessary (GB, alpha = True, Phi = emp)
theorem c4_27 : ¬ drop0% Iris.BI.exists_absorbing 4 := fun h => by
  obtain ⟨p, ⟨_, e⟩, hp⟩ := (@h GB True _ (fun _ => iprop(emp))).1 true
    ⟨true, false, rfl, trivial, _, ⟨trivial, rfl⟩, rfl⟩
  subst e; exact Bool.noConfusion (hp : true = false)
-- `Iris.BI.sep_absorbing_left` idx 4: necessary (GB, P = Q = emp)
theorem c4_28 : ¬ drop0% Iris.BI.sep_absorbing_left 4 := fun h => by
  obtain ⟨a, b, e, ha, hb⟩ := (@h GB _ iprop(emp) iprop(emp)).1 true
    ⟨true, false, rfl, trivial, false, false, rfl, rfl, rfl⟩
  have ha : a = false := ha
  have hb : b = false := hb
  subst ha hb; exact Bool.noConfusion e
-- `Iris.BI.sep_absorbing_right` idx 4: necessary (GB, P = Q = emp)
theorem c4_29 : ¬ drop0% Iris.BI.sep_absorbing_right 4 := fun h => by
  obtain ⟨a, b, e, ha, hb⟩ := (@h GB _ iprop(emp) iprop(emp)).1 true
    ⟨true, false, rfl, trivial, false, false, rfl, rfl, rfl⟩
  have ha : a = false := ha
  have hb : b = false := hb
  subst ha hb; exact Bool.noConfusion e
-- `Iris.BI.bi_affine_absorbing` idx 2: necessary (GB, emp not absorbing)
theorem c4_30 : ¬ drop0% Iris.BI.bi_affine_absorbing 2 := fun h =>
  gb_emp_not_absorbing (@h GB _ iprop(emp))
-- `Iris.BI.biaffine_of_true_affine` idx 2: necessary (GB is not affine)
theorem c4_31 : ¬ drop0% Iris.BI.biaffine_of_true_affine 2 := fun h => gb_not_biaffine (@h GB _)
-- `Iris.BI.absorbing_absorbingly` idx 3: necessary (GB, P = emp)
theorem c4_32 : ¬ drop0% Iris.BI.absorbing_absorbingly 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp)).1 true ⟨true, false, rfl, trivial, rfl⟩ : true = false)
-- `Iris.BI.absorbing_of_emp_absorbing` idx 2: necessary (GB, emp not absorbing)
theorem c4_33 : ¬ drop0% Iris.BI.absorbing_of_emp_absorbing 2 := fun h =>
  gb_emp_not_absorbing (@h GB _ iprop(emp))
-- `Iris.BI.wand_absorbing_left` idx 4: necessary (GB, P = Q = emp)
theorem c4_34 : ¬ drop0% Iris.BI.wand_absorbing_left 4 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp) iprop(emp)).1 true
    ⟨true, false, rfl, trivial, fun y (hy : y = false) => by subst hy; rfl⟩ false rfl : true = false)
-- `Iris.BI.wand_absorbing_right` idx 4: necessary (GB, P = Q = emp)
theorem c4_35 : ¬ drop0% Iris.BI.wand_absorbing_right 4 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp) iprop(emp)).1 true
    ⟨true, false, rfl, trivial, fun y (hy : y = false) => by subst hy; rfl⟩ false rfl : true = false)
-- `Iris.BI.affinely_intro` idx 4: necessary (GB, P = Q = True)
theorem c4_36 : ¬ drop0% Iris.BI.affinely_intro 4 := fun h =>
  Bool.noConfusion (@h GB _ iprop(True) iprop(True) (fun _ h => h) true trivial).1
-- `Iris.BI.affinely_intro` idx 5: necessary (GB, P = emp, Q = False)
theorem c4_37 : ¬ drop0% Iris.BI.affinely_intro 5 := fun h =>
  (@h GB _ iprop(emp) iprop(False) _ false rfl).2
-- `Iris.BI.emp_and` idx 3: necessary (GB, P = True)
theorem c4_38 : ¬ drop0% Iris.BI.emp_and 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True)).2 true trivial).1
-- `Iris.BI.emp_and_biaffine` idx 2: necessary (GB, x = True)
theorem c4_39 : ¬ drop0% Iris.BI.emp_and_biaffine 2 := fun h =>
  Bool.noConfusion (((@h GB _).left_id (x := iprop(True))).2 true trivial).1
-- `Iris.BI.and_emp` idx 3: necessary (GB, P = True)
theorem c4_40 : ¬ drop0% Iris.BI.and_emp 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True)).2 true trivial).2
-- `Iris.BI.and_emp_biaffine` idx 2: necessary (GB, x = True)
theorem c4_41 : ¬ drop0% Iris.BI.and_emp_biaffine 2 := fun h =>
  Bool.noConfusion (((@h GB _).right_id (x := iprop(True))).2 true trivial).2
-- `Iris.BI.emp_or` idx 3: necessary (GB, P = True)
theorem c4_42 : ¬ drop0% Iris.BI.emp_or 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True)).1 true (.inr trivial) : true = false)
-- `Iris.BI.or_emp` idx 3: necessary (GB, P = True)
theorem c4_43 : ¬ drop0% Iris.BI.or_emp 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True)).1 true (.inl trivial) : true = false)
-- `Iris.BI.True_affine_all_affine` idx 2: necessary (GB, P = True)
theorem c4_44 : ¬ drop0% Iris.BI.True_affine_all_affine 2 := fun h =>
  gb_true_not_affine (@h GB _ iprop(True))
-- `Iris.BI.instAbsorbingOfBIAffine` idx 2: necessary (GB, emp not absorbing)
theorem c4_45 : ¬ drop0% Iris.BI.instAbsorbingOfBIAffine 2 := fun h =>
  gb_emp_not_absorbing (@h GB _ iprop(emp))
-- `Iris.BI.true_sep` idx 3: necessary (GB, P = emp)
theorem c4_46 : ¬ drop0% Iris.BI.true_sep 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp)).1 true ⟨true, false, rfl, trivial, rfl⟩ : true = false)
-- `Iris.BI.instLeftIdBiEntailsPureTrueSepOfBIAffine` idx 2: necessary (GB, x = emp)
theorem c4_47 : ¬ drop0% Iris.BI.instLeftIdBiEntailsPureTrueSepOfBIAffine 2 := fun h =>
  Bool.noConfusion (((@h GB _).left_id (x := iprop(emp))).1 true
    ⟨true, false, rfl, trivial, rfl⟩ : true = false)
-- `Iris.BI.true_sep_flip` idx 3: necessary (GB, P = emp)
theorem c4_48 : ¬ drop0% Iris.BI.true_sep_flip 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp)).2 true ⟨true, false, rfl, trivial, rfl⟩ : true = false)
-- `Iris.BI.sep_true` idx 3: necessary (GB, P = emp)
theorem c4_49 : ¬ drop0% Iris.BI.sep_true 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp)).1 true ⟨false, true, rfl, rfl, trivial⟩ : true = false)
-- `Iris.BI.instRightIdBiEntailsPureTrueSepOfBIAffine` idx 2: necessary (GB, x = emp)
theorem c4_50 : ¬ drop0% Iris.BI.instRightIdBiEntailsPureTrueSepOfBIAffine 2 := fun h =>
  Bool.noConfusion (((@h GB _).right_id (x := iprop(emp))).1 true
    ⟨false, true, rfl, rfl, trivial⟩ : true = false)
-- `Iris.BI.sep_true_flip` idx 3: necessary (GB, P = emp)
theorem c4_51 : ¬ drop0% Iris.BI.sep_true_flip 3 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp)).2 true ⟨false, true, rfl, rfl, trivial⟩ : true = false)
-- `Iris.BI.bi_affine_positive` idx 2: necessary (GB is not positive)
theorem c4_52 : ¬ drop0% Iris.BI.bi_affine_positive 2 := fun h => gb_not_positive (@h GB _)
-- `Iris.BI.imp_wand_1` idx 2: necessary (GB, P = Q = emp)
theorem c4_53 : ¬ drop0% Iris.BI.imp_wand_1 2 := fun h =>
  Bool.noConfusion (@h GB _ iprop(emp) iprop(emp) true (fun h => h) false rfl : true = false)
-- `Iris.BI.decide_emp` idx 2: necessary (GB, phi = False, P = False)
theorem c4_54 : ¬ drop0% Iris.BI.decide_emp 2 := fun h =>
  Bool.noConfusion ((@h GB _ False _ iprop(False)).2 true (fun h => h) : true = false)
-- `Iris.BI.persistently_congr` idx 4: necessary (GB, True vs False)
theorem c4_55 : ¬ drop0% Iris.BI.persistently_congr 4 := fun h =>
  (@h GB _ iprop(True) iprop(False)).1 false trivial
-- `Iris.BI.persistently_forall` idx 3: necessary (at alpha : Type) in PF, Psi = evk
theorem c4_56 : ¬ ∀ {PROP : Type} {α : Type} [inst : Iris.BI PROP] {Ψ : α → PROP},
    (<pers> ∀ a, Ψ a) ⊣⊢ ∀ a, <pers> Ψ a := fun h => by
  have := (@h PF Nat _ evk).2 0 (fun p ⟨k, e⟩ => e ▸ ⟨evk_cof k, .inl rfl⟩)
  obtain ⟨⟨N, hN⟩, _⟩ := this
  exact evk_all_not_cof ⟨N, fun m hm k => hN m hm _ ⟨k, rfl⟩⟩
-- `Iris.BI.persistently_exists` idx 3: necessary (at alpha : Type) in PF, Psi true = ev, Psi false = od
theorem c4_57 : ¬ ∀ {PROP : Type} {α : Type} [inst : Iris.BI PROP] {Ψ : α → PROP},
    (<pers> ∃ a, Ψ a) ⊣⊢ ∃ a, <pers> Ψ a := fun h => by
  have := (@h PF Bool _ (fun b => if b then ev else od)).1 0
    ⟨⟨0, fun m _ => by
      by_cases hm : m % 2 = 0
      · exact ⟨_, ⟨true, rfl⟩, hm⟩
      · exact ⟨_, ⟨false, rfl⟩, show m % 2 = 1 by omega⟩⟩,
     _, ⟨true, rfl⟩, rfl⟩
  obtain ⟨p, ⟨b, e⟩, hp⟩ := this
  subst e
  obtain ⟨hc, _⟩ := hp
  cases b
  · exact od_not_cof hc
  · exact ev_not_cof hc
-- `Iris.BI.persistently_or` idx 2: necessary (PF, P = ev, Q = od)
theorem c4_58 : ¬ drop0% Iris.BI.persistently_or 2 := fun h => by
  rcases (@h PF _ ev od).1 0 ⟨evod_cof, .inl rfl⟩ with ⟨hc, _⟩ | ⟨hc, _⟩
  · exact ev_not_cof hc
  · exact od_not_cof hc
-- `Iris.BI.persistently_elim` idx 3: necessary (GB, P = emp)
theorem c4_59 : ¬ drop0% Iris.BI.persistently_elim 3 := fun h =>
  Bool.noConfusion (@h GB _ iprop(emp) true rfl : true = false)
-- `Iris.BI.persistently_intro_persistently` idx 4: necessary (GB, True, False)
theorem c4_60 : ¬ drop0% Iris.BI.persistently_intro_persistently 4 := fun h =>
  @h GB _ iprop(True) iprop(False) false trivial
-- `Iris.BI.persistently_sep` idx 2: necessary (GB is not positive, P = Q = own1)
theorem c4_61 : ¬ drop0% Iris.BI.persistently_sep 2 := fun h => by
  obtain ⟨a, b, e, ha, hb⟩ := (@h GB _ own1 own1).1 false ⟨true, true, rfl, rfl, rfl⟩
  exact Bool.noConfusion (ha : false = true)
-- `Iris.BI.persistently_entails_left` idx 4: necessary (GB, P = True, Q = False)
theorem c4_62 : ¬ drop0% Iris.BI.persistently_entails_left 4 := fun h => by
  obtain ⟨a, b, e, ha, hb⟩ := @h GB _ iprop(True) iprop(False) false trivial
  exact ha
-- `Iris.BI.persistently_entails_right` idx 4: necessary (GB, P = True, Q = False)
theorem c4_63 : ¬ drop0% Iris.BI.persistently_entails_right 4 := fun h => by
  obtain ⟨a, b, e, ha, hb⟩ := @h GB _ iprop(True) iprop(False) false trivial
  exact hb
-- `Iris.BI.persistently_emp_affine` idx 2: necessary (GB is not affine)
theorem c4_64 : ¬ drop0% Iris.BI.persistently_emp_affine 2 := fun h =>
  Bool.noConfusion ((@h GB _).1 true rfl : true = false)
-- `Iris.BI.persistently_and_iff_sep` idx 2: necessary (GB, P = True, Q = emp)
theorem c4_65 : ¬ drop0% Iris.BI.persistently_and_iff_sep 2 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) iprop(emp)).2 true ⟨true, false, rfl, trivial, rfl⟩).2
-- `Iris.BI.and_persistently_iff_sep` idx 2: necessary (GB, P = emp, Q = True)
theorem c4_66 : ¬ drop0% Iris.BI.and_persistently_iff_sep 2 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp) iprop(True)).2 true ⟨false, true, rfl, rfl, trivial⟩).1
-- `Iris.BI.imp_wand_persistently` idx 2: necessary (GB, P = True, Q = emp)
theorem c4_67 : ¬ drop0% Iris.BI.imp_wand_persistently 2 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) iprop(emp)).1 false (fun _ => rfl) true trivial : true = false)
-- `Iris.BI.wand_iff_exists_persistently` idx 2: necessary (GB, P = Q = emp, R = True)
theorem c4_68 : ¬ drop0% Iris.BI.wand_iff_exists_persistently 2 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(emp) iprop(emp)).2 true
    ⟨_, ⟨iprop(True), rfl⟩, true, false, rfl, trivial, fun _ => rfl⟩ false rfl : true = false)
-- `Iris.BI.and_persistent` idx 4: necessary (GB, P = own1, Q = True)
theorem c4_69 : ¬ drop0% Iris.BI.and_persistent 4 := fun h =>
  Bool.noConfusion ((@h GB _ own1 iprop(True) _).1 true ⟨rfl, trivial⟩).1
-- `Iris.BI.and_persistent` idx 5: necessary (GB, P = True, Q = own1)
theorem c4_70 : ¬ drop0% Iris.BI.and_persistent 5 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) own1 _).1 true ⟨trivial, rfl⟩).2
-- `Iris.BI.or_persistent` idx 4: necessary (GB, P = own1, Q = False)
theorem c4_71 : ¬ drop0% Iris.BI.or_persistent 4 := fun h => by
  rcases (@h GB _ own1 iprop(False) _).1 true (.inl rfl) with h | h
  · exact Bool.noConfusion (h : false = true)
  · exact h
-- `Iris.BI.or_persistent` idx 5: necessary (GB, P = False, Q = own1)
theorem c4_72 : ¬ drop0% Iris.BI.or_persistent 5 := fun h => by
  rcases (@h GB _ iprop(False) own1 _).1 true (.inr rfl) with h | h
  · exact h
  · exact Bool.noConfusion (h : false = true)
-- `Iris.BI.sForall_persistent` idx 2: necessary (PF, Psi = range of evk: each persistent, meet = evens not)
theorem c4_73 : ¬ drop0% Iris.BI.sForall_persistent 2 := fun h => by
  obtain ⟨hp⟩ := @h PF _ (fun p => ∃ k, p = evk k)
    (fun p ⟨k, e⟩ => e ▸ ⟨fun n hn => ⟨evk_cof k, hn⟩⟩)
  obtain ⟨⟨N, hN⟩, _⟩ := hp 0 (fun p ⟨k, e⟩ => e ▸ .inl rfl)
  exact evk_all_not_cof ⟨N, fun m hm k => hN m hm _ ⟨k, rfl⟩⟩
-- `Iris.BI.sForall_persistent` idx 4: necessary (GB, Psi = equal to own1)
theorem c4_74 : ¬ drop0% Iris.BI.sForall_persistent 4 := fun h => by
  obtain ⟨hp⟩ := @h GB _ _ (· = own1)
  exact Bool.noConfusion (hp true (fun p e => e ▸ rfl) own1 rfl : false = true)
-- `Iris.BI.forall_persistent` idx 3: necessary (at alpha : Type) in PF, Psi = evk
theorem c4_75 : ¬ ∀ {PROP : Type} {α : Type} [inst : Iris.BI PROP] (Ψ : α → PROP)
    [h : ∀ (x : α), Iris.BI.Persistent (Ψ x)], Iris.BI.Persistent iprop(∀ x, Ψ x) := fun h => by
  obtain ⟨hp⟩ := @h PF Nat _ evk (fun k => ⟨fun n hn => ⟨evk_cof k, hn⟩⟩)
  obtain ⟨⟨N, hN⟩, _⟩ := hp 0 (fun p ⟨k, e⟩ => e ▸ .inl rfl)
  exact evk_all_not_cof ⟨N, fun m hm k => hN m hm _ ⟨k, rfl⟩⟩
-- `Iris.BI.forall_persistent` idx 5: necessary (GB, alpha = True, Psi = own1)
theorem c4_76 : ¬ drop0% Iris.BI.forall_persistent 5 := fun h => by
  obtain ⟨hp⟩ := @h GB True _ _ (fun _ => own1)
  exact Bool.noConfusion (hp true (fun p ⟨_, e⟩ => e ▸ rfl) own1 ⟨trivial, rfl⟩ : false = true)
-- `Iris.BI.sExists_persistent` idx 3: necessary (GB, Psi = equal to own1)
theorem c4_77 : ¬ drop0% Iris.BI.sExists_persistent 3 := fun h => by
  obtain ⟨hp⟩ := @h GB _ (· = own1)
  obtain ⟨p, e, hp'⟩ := hp true ⟨own1, rfl, rfl⟩
  subst e; exact Bool.noConfusion (hp' : false = true)
-- `Iris.BI.exists_persistent` idx 4: necessary (GB, alpha = True, Psi = own1)
theorem c4_78 : ¬ drop0% Iris.BI.exists_persistent 4 := fun h => by
  obtain ⟨hp⟩ := @h GB True _ (fun _ => own1)
  obtain ⟨p, ⟨_, e⟩, hp'⟩ := hp true ⟨own1, ⟨trivial, rfl⟩, rfl⟩
  subst e; exact Bool.noConfusion (hp' : false = true)
-- `Iris.BI.sep_persistent` idx 4: necessary (GB, P = own1, Q = emp)
theorem c4_79 : ¬ drop0% Iris.BI.sep_persistent 4 := fun h => by
  obtain ⟨hp⟩ := @h GB _ own1 iprop(emp) _
  obtain ⟨a, b, e, ha, hb⟩ := hp true ⟨true, false, rfl, rfl, rfl⟩
  have ha : a = true := ha
  have hb : b = false := hb
  subst ha hb; exact Bool.noConfusion e
-- `Iris.BI.sep_persistent` idx 5: necessary (GB, P = emp, Q = own1)
theorem c4_80 : ¬ drop0% Iris.BI.sep_persistent 5 := fun h => by
  obtain ⟨hp⟩ := @h GB _ iprop(emp) own1 _
  obtain ⟨a, b, e, ha, hb⟩ := hp true ⟨false, true, rfl, rfl, rfl⟩
  have ha : a = false := ha
  have hb : b = true := hb
  subst ha hb; exact Bool.noConfusion e
-- `Iris.BI.affinely_persistent` idx 3: necessary (PF, P = ev)
theorem c4_81 : ¬ drop0% Iris.BI.affinely_persistent 3 := fun h => by
  obtain ⟨hp⟩ := @h PF _ ev
  obtain ⟨⟨N, hN⟩, _⟩ := hp 0 ⟨trivial, rfl⟩
  exact ev_not_cof ⟨N, fun m hm => (hN m hm).2⟩
-- `Iris.BI.intuitionistically_congr` idx 4: necessary (GB, True vs False)
theorem c4_82 : ¬ drop0% Iris.BI.intuitionistically_congr 4 := fun h =>
  ((@h GB _ iprop(True) iprop(False)).1 false ⟨rfl, trivial⟩).2
-- `Iris.BI.intuitionistically_mono` idx 4: necessary (GB, True, False)
theorem c4_83 : ¬ drop0% Iris.BI.intuitionistically_mono 4 := fun h =>
  (@h GB _ iprop(True) iprop(False) false ⟨rfl, trivial⟩).2
-- `Iris.BI.intuitionistically_or` idx 2: necessary (PF, P = ev, Q = od)
theorem c4_84 : ¬ drop0% Iris.BI.intuitionistically_or 2 := fun h => by
  rcases (@h PF _ ev od).1 0 ⟨trivial, evod_cof, .inl rfl⟩ with ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact ev_not_cof hc
  · exact od_not_cof hc
-- `Iris.BI.intuitionistically_exists` idx 3: necessary (at alpha : Type) in PF, Phi true = ev, Phi false = od
theorem c4_85 : ¬ ∀ {PROP : Type} {α : Type} [inst : Iris.BI PROP] {Φ : α → PROP},
    (□ ∃ x, Φ x) ⊣⊢ ∃ x, □ Φ x := fun h => by
  have := (@h PF Bool _ (fun b => if b then ev else od)).1 0
    ⟨trivial, ⟨0, fun m _ => by
      by_cases hm : m % 2 = 0
      · exact ⟨_, ⟨true, rfl⟩, hm⟩
      · exact ⟨_, ⟨false, rfl⟩, show m % 2 = 1 by omega⟩⟩,
     _, ⟨true, rfl⟩, rfl⟩
  obtain ⟨p, ⟨b, e⟩, hp⟩ := this
  subst e
  obtain ⟨_, hc, _⟩ := hp
  cases b
  · exact od_not_cof hc
  · exact ev_not_cof hc
