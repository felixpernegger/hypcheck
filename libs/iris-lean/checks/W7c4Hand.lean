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

namespace W7c4
open Iris Iris.BI

/-! GB (copied from W4c4): predicates on Bool with sep over xor, emp = {false}, persistently P := const (P false): non-affine, non-positive. -/
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

instance pfAffine : BIAffine PF := ⟨fun _ => ⟨fun _ _ => trivial⟩⟩

/-- evens for true, odds for false. -/
def eo : Bool → PF
  | true => ev
  | false => od

/-- own1 ∗ own1 does not hold at true in GB. -/
theorem gb_o1o1_true : ¬ (iprop(own1 ∗ own1) : GB) true := fun ⟨a, b, e, ha, hb⟩ => by
  have ha : a = true := ha
  have hb : b = true := hb
  subst ha; subst hb; exact Bool.noConfusion e

/-- own1 ∗ (own1 ∗ emp) does not hold at true in GB. -/
theorem gb_o1o1e_true : ¬ (iprop(own1 ∗ (own1 ∗ emp)) : GB) true := fun ⟨a, b, e, ha, c, d, e2, hc, hd⟩ => by
  have ha : a = true := ha
  have hc : c = true := hc
  have hd : d = false := hd
  subst ha; subst hc; subst hd; subst e2; exact Bool.noConfusion e

/-- own1 ∗ emp holds at true in GB. -/
theorem gb_o1e_true : (iprop(own1 ∗ emp) : GB) true := ⟨true, false, rfl, rfl, rfl⟩

end W7c4

section
open Iris Iris.BI Iris.ProofMode

-- `Iris.ProofMode.asEmpValid_forall` idx 7: necessary (SiProp: d=into, Phi=True, P=False, alpha=True)
theorem w7c4_1 : ¬ drop0% Iris.ProofMode.asEmpValid_forall 7 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp True SiProp.instBI (fun _ => True) (fun _ => iprop(False)) .into .in).as_emp_valid.1
    rfl (fun _ => trivial) 0 trivial) trivial

-- `Iris.ProofMode.asEmpValid_tforall` idx 7: necessary (SiProp: TT=nil, d=into, phi=True, P=False)
theorem w7c4_2 : ¬ drop0% Iris.ProofMode.asEmpValid_tforall 7 := fun h =>
  (@h SiProp .nil SiProp.instBI (fun _ => True) (fun _ => iprop(False)) .into .in).as_emp_valid.1
    rfl trivial 0 trivial

-- `Iris.ProofMode.intoWand_impl_false_true` idx 7: necessary (SiProp: P=True, Q=P'=False)
theorem w7c4_4 : ¬ drop0% Iris.ProofMode.intoWand_impl_false_true 7 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) (.matching .argument) inferInstance).into_wand 0
    (fun _ _ hf => hf) 0 (Nat.le_refl 0) ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoWand_impl_true_false` idx 7: necessary (SiProp: P=Q=False, P'=P''=True)
theorem w7c4_5 : ¬ drop0% Iris.ProofMode.intoWand_impl_true_false 7 := fun h =>
  (@h SiProp _ iprop(False) iprop(False) iprop(True) iprop(True) (.matching .argument)
    ⟨fun _ _ => trivial⟩).into_wand 0 ⟨trivial, fun _ _ hf => hf⟩ 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_impl_true_false` idx 8: necessary (SiProp: P=Q=P'=False, P''=True)
theorem w7c4_6 : ¬ drop0% Iris.ProofMode.intoWand_impl_true_false 8 := fun h =>
  (@h SiProp _ iprop(False) iprop(False) iprop(False) iprop(True) (.matching .argument)
    ⟨⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩⟩).into_wand 0 ⟨trivial, fun _ _ hf => hf⟩ 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_impl_true_true` idx 6: necessary (SiProp: P=True, Q=P'=False)
theorem w7c4_7 : ¬ drop0% Iris.ProofMode.intoWand_impl_true_true 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) (.matching .argument)).into_wand 0
    ⟨trivial, fun _ _ hf => hf⟩ 0 (Nat.le_refl 0) ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoWand_impl_false_false` idx 9: necessary (SiProp: P=Q=False, P'=P''=True)
theorem w7c4_9 : ¬ drop0% Iris.ProofMode.intoWand_impl_false_false 9 := fun h =>
  (@h SiProp _ iprop(False) iprop(False) iprop(True) iprop(True) (.matching .argument) inferInstance
    (Iris.Std.TCOr.l (t := SiProp.instBIAffine)) ⟨fun _ _ => trivial⟩).into_wand 0
    (fun _ _ hf => hf) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_impl_false_false` idx 10: necessary (SiProp: P=Q=P'=False, P''=True)
theorem w7c4_10 : ¬ drop0% Iris.ProofMode.intoWand_impl_false_false 10 := fun h =>
  (@h SiProp _ iprop(False) iprop(False) iprop(False) iprop(True) (.matching .argument) inferInstance
    (Iris.Std.TCOr.l (t := SiProp.instBIAffine)) ⟨⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩⟩).into_wand 0
    (fun _ _ hf => hf) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_and_left` idx 9: necessary (SiProp: R1=R2=P'=True, Q'=False)
theorem w7c4_11 : ¬ drop0% Iris.ProofMode.intoWand_and_left 9 := fun h =>
  (@h SiProp (.matching .argument) false false _ iprop(True) iprop(True) iprop(True) iprop(False)).into_wand 0
    ⟨trivial, trivial⟩ 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_and_right` idx 9: necessary (SiProp: R1=R2=P'=True, Q'=False)
theorem w7c4_12 : ¬ drop0% Iris.ProofMode.intoWand_and_right 9 := fun h =>
  (@h SiProp (.matching .argument) false false _ iprop(True) iprop(True) iprop(True) iprop(False)).into_wand 0
    ⟨trivial, trivial⟩ 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_wandIff` idx 9: necessary (SiProp: R1=R2=P'=True, Q'=False)
theorem w7c4_13 : ¬ drop0% Iris.ProofMode.intoWand_wandIff 9 := fun h =>
  (@h SiProp (.matching .argument) false false _ iprop(True) iprop(True) iprop(True) iprop(False)).into_wand 0
    ⟨fun _ _ h => h, fun _ _ h => h⟩ 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_wandM` idx 8: necessary (SiProp: mP'=some False, P=True, Q=False)
theorem w7c4_14 : ¬ drop0% Iris.ProofMode.intoWand_wandM 8 := fun h =>
  (@h SiProp (.matching .argument) false false _ (some iprop(False)) iprop(True) iprop(False)).into_wand 0
    (fun _ _ hf => hf) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_forall_prop_false` idx 8: necessary (SiProp: phi=False, Pphi=P'=True, P=False)
theorem w7c4_15 : ¬ drop0% Iris.ProofMode.intoWand_forall_prop_false 8 := fun h =>
  (@h SiProp false _ (.matching .argument) False iprop(True) iprop(True) iprop(False) ⟨fun _ _ => trivial⟩).into_wand 0
    (SiProp.forall_holds.2 fun x => x.elim) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_forall_prop_false` idx 9: necessary (SiProp: phi=False, Pphi=pure False, P'=True, P=False)
theorem w7c4_16 : ¬ drop0% Iris.ProofMode.intoWand_forall_prop_false 9 := fun h =>
  (@h SiProp false _ (.matching .argument) False iprop(⌜False⌝) iprop(True) iprop(False)
    ⟨⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩⟩).into_wand 0
    (SiProp.forall_holds.2 fun x => x.elim) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_forall` idx 10: necessary (SiProp: Phi=True, P=True, Q=False)
theorem w7c4_17 : ¬ drop0% Iris.ProofMode.intoWand_forall 10 := fun h =>
  (@h SiProp True (.matching .argument) false false _ (fun _ => iprop(True)) iprop(True) iprop(False) trivial).into_wand 0
    (SiProp.forall_holds.2 fun _ => trivial) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_affinely` idx 8: necessary (SiProp: R=P=True, Q=False)
theorem w7c4_18 : ¬ drop0% Iris.ProofMode.intoWand_affinely 8 := fun h =>
  ((@h SiProp (.matching .argument) false false _ iprop(True) iprop(True) iprop(False)).into_wand 0
    ⟨trivial, trivial⟩ 0 (Nat.le_refl 0) ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoWand_affinely_args` idx 7: necessary (SiProp: R=P=True, Q=False)
theorem w7c4_19 : ¬ drop0% Iris.ProofMode.intoWand_affinely_args 7 := fun h =>
  ((@h SiProp false _ .argument iprop(True) iprop(True) iprop(False)).into_wand 0
    ⟨trivial, trivial⟩ 0 (Nat.le_refl 0) ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoWand_intuitionistically` idx 8: necessary (SiProp: R=P=True, Q=False)
theorem w7c4_20 : ¬ drop0% Iris.ProofMode.intoWand_intuitionistically 8 := fun h =>
  (@h SiProp (.matching .argument) false false _ iprop(True) iprop(True) iprop(False)).into_wand 0
    ⟨trivial, trivial⟩ 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_persistently_true` idx 7: necessary (SiProp: R=P=True, Q=False)
theorem w7c4_21 : ¬ drop0% Iris.ProofMode.intoWand_persistently_true 7 := fun h =>
  (@h SiProp (.matching .argument) false _ iprop(True) iprop(True) iprop(False)).into_wand 0
    ⟨trivial, trivial⟩ 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_persistently_false` idx 8: necessary (SiProp: R=P=True, Q=False)
theorem w7c4_23 : ¬ drop0% Iris.ProofMode.intoWand_persistently_false 8 := fun h =>
  (@h SiProp (.matching .argument) false _ iprop(True) iprop(True) iprop(False) inferInstance).into_wand 0
    trivial 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.intoWand_tforall` idx 10: necessary (SiProp: TT=nil, Phi=True, P=True, Q=False)
theorem w7c4_24 : ¬ drop0% Iris.ProofMode.intoWand_tforall 10 := fun h =>
  (@h SiProp (.matching .argument) .nil false false _ (fun _ => iprop(True)) iprop(True) iprop(False) ⟨⟩).into_wand 0
    trivial 0 (Nat.le_refl 0) trivial
end

section
open Iris Iris.BI Iris.ProofMode

-- `Iris.ProofMode.fromForall_imp_pure` idx 5: necessary (SiProp: phi=False, P=True, Q=False)
theorem w7c4_25 : ¬ drop0% Iris.ProofMode.fromForall_imp_pure 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) False).from_forall 0 (SiProp.forall_holds.2 fun x => x.elim)
    0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromForall_wand_pure` idx 5: necessary (SiProp: phi=False, P=True, Q=False)
theorem w7c4_26 : ¬ drop0% Iris.ProofMode.fromForall_wand_pure 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) False (Iris.Std.TCOr.l (t := inferInstance))).from_forall 0
    (SiProp.forall_holds.2 fun x => x.elim) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromForall_persistently` idx 6: necessary (SiProp: A=True, Phi=True, P=False)
theorem w7c4_30 : ¬ drop0% Iris.ProofMode.fromForall_persistently 6 := fun h =>
  (@h SiProp _ _ True iprop(False) (fun _ => iprop(True))).from_forall 0 (SiProp.forall_holds.2 fun _ => trivial)

-- `Iris.ProofMode.intoForall_affinely` idx 5: necessary (SiProp: P=True, Phi=False)
theorem w7c4_31 : ¬ drop0% Iris.ProofMode.intoForall_affinely 5 := fun h =>
  (SiProp.forall_holds.1 ((@h SiProp True _ iprop(True) (fun _ => iprop(False))).into_forall 0
    ⟨trivial, trivial⟩) trivial).2

-- `Iris.ProofMode.intoForall_intuitionistically` idx 5: necessary (SiProp: P=True, Phi=False)
theorem w7c4_32 : ¬ drop0% Iris.ProofMode.intoForall_intuitionistically 5 := fun h =>
  (SiProp.forall_holds.1 ((@h SiProp True _ iprop(True) (fun _ => iprop(False))).into_forall 0
    ⟨trivial, trivial⟩) trivial).2

-- `Iris.ProofMode.intoForall_persistently` idx 6: necessary (SiProp: P=True, Phi=False)
theorem w7c4_33 : ¬ drop0% Iris.ProofMode.intoForall_persistently 6 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp True _ _ iprop(True) (fun _ => iprop(False))).into_forall 0
    trivial) trivial

-- `Iris.ProofMode.intoForall_wand_pure` idx 6: necessary (SiProp: a=false, P=Q=False, Phi=True)
theorem w7c4_34 : ¬ drop0% Iris.ProofMode.intoForall_wand_pure 6 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp false _ iprop(False) iprop(False) True).into_forall 0
    (fun _ _ hf => hf)) trivial

-- `Iris.ProofMode.intoForall_imp_pure` idx 6: necessary (SiProp: a=false, phi=True, P=Q=False)
theorem w7c4_35 : ¬ drop0% Iris.ProofMode.intoForall_imp_pure 6 := fun h =>
  SiProp.forall_holds.1 ((@h SiProp _ false True iprop(False) iprop(False)
    (Iris.Std.TCOr.l (t := Iris.Std.TCEq.refl))).into_forall 0 (fun _ _ hf => hf)) trivial

-- `Iris.ProofMode.fromExists_affinely` idx 5: necessary (SiProp: P=False, Phi=True)
theorem w7c4_37 : ¬ drop0% Iris.ProofMode.fromExists_affinely 5 := fun h =>
  ((@h SiProp True _ iprop(False) (fun _ => iprop(True))).from_exists 0
    (SiProp.exists_holds.2 ⟨trivial, trivial, trivial⟩)).2

-- `Iris.ProofMode.fromExists_intuitionistically` idx 5: necessary (SiProp: P=False, Phi=True)
theorem w7c4_38 : ¬ drop0% Iris.ProofMode.fromExists_intuitionistically 5 := fun h =>
  ((@h SiProp True _ iprop(False) (fun _ => iprop(True))).from_exists 0
    (SiProp.exists_holds.2 ⟨trivial, trivial, trivial⟩)).2

-- `Iris.ProofMode.fromExists_absorbingly` idx 5: necessary (SiProp: P=False, Phi=True)
theorem w7c4_39 : ¬ drop0% Iris.ProofMode.fromExists_absorbingly 5 := fun h =>
  ((@h SiProp True _ iprop(False) (fun _ => iprop(True))).from_exists 0
    (SiProp.exists_holds.2 ⟨trivial, trivial, trivial⟩)).2

-- `Iris.ProofMode.fromExists_persistently` idx 5: necessary (SiProp: P=False, Phi=True)
theorem w7c4_40 : ¬ drop0% Iris.ProofMode.fromExists_persistently 5 := fun h =>
  (@h SiProp True _ iprop(False) (fun _ => iprop(True))).from_exists 0
    (SiProp.exists_holds.2 ⟨trivial, trivial⟩)

-- `Iris.ProofMode.intoExists_affinely` idx 5: necessary (SiProp: P=True, Phi=False)
theorem w7c4_41 : ¬ drop0% Iris.ProofMode.intoExists_affinely 5 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp True _ iprop(True) (fun _ => iprop(False))).into_exists 0
    ⟨trivial, trivial⟩) with
  | ⟨_, hx⟩ => hx.2

-- `Iris.ProofMode.intoExists_intuitionistically` idx 6: necessary (SiProp: P=True, Phi=False)
theorem w7c4_43 : ¬ drop0% Iris.ProofMode.intoExists_intuitionistically 6 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp True _ _ iprop(True) (fun _ => iprop(False))).into_exists 0
    ⟨trivial, trivial⟩) with
  | ⟨_, hx⟩ => hx.2

-- `Iris.ProofMode.intoExist_and_pure` idx 6: necessary (SiProp: PQ=Q=True, P=False, Phi=False)
theorem w7c4_44 : ¬ drop0% Iris.ProofMode.intoExist_and_pure 6 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp _ iprop(True) iprop(False) iprop(True) False
    ⟨fun _ hf => hf⟩).into_exists 0 trivial) with
  | ⟨x, _⟩ => x

-- `Iris.ProofMode.intoExist_sep_pure` idx 5: necessary (SiProp: P=Q=True, Phi=False)
theorem w7c4_45 : ¬ drop0% Iris.ProofMode.intoExist_sep_pure 5 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp _ iprop(True) iprop(True) False
    (Iris.Std.TCOr.l (t := inferInstance))).into_exists 0 ⟨trivial, trivial⟩) with
  | ⟨x, _⟩ => x

-- `Iris.ProofMode.intoExists_absorbingly` idx 5: necessary (SiProp: P=True, Phi=False)
theorem w7c4_46 : ¬ drop0% Iris.ProofMode.intoExists_absorbingly 5 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp True _ iprop(True) (fun _ => iprop(False))).into_exists 0
    ⟨trivial, trivial⟩) with
  | ⟨_, hx⟩ => hx.2

-- `Iris.ProofMode.intoExists_persistently` idx 6: necessary (SiProp: P=True, Phi=False)
theorem w7c4_48 : ¬ drop0% Iris.ProofMode.intoExists_persistently 6 := fun h =>
  match SiProp.exists_holds.1 ((@h SiProp True _ _ iprop(True) (fun _ => iprop(False))).into_exists 0
    trivial) with
  | ⟨_, hx⟩ => hx

-- `Iris.ProofMode.fromAnd_wandIff` idx 6: necessary (SiProp: P1=P1'=P2'=True, P2=False)
theorem w7c4_49 : ¬ drop0% Iris.ProofMode.fromAnd_wandIff 6 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True) iprop(True)).from_and 0 ⟨trivial, trivial⟩).1
    0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromAnd_iff` idx 6: necessary (SiProp: P1=P1'=P2'=True, P2=False)
theorem w7c4_50 : ¬ drop0% Iris.ProofMode.fromAnd_iff 6 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True) iprop(True)).from_and 0 ⟨trivial, trivial⟩).1
    0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.fromAnd_sep_persistent_left` idx 6: necessary (SiProp: P1=False, P1'=P2=True)
theorem w7c4_52 : ¬ drop0% Iris.ProofMode.fromAnd_sep_persistent_left 6 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True) inferInstance).from_and 0 ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.fromAnd_sep_persistent_right` idx 6: necessary (SiProp: P2=False, P1=P2'=True)
theorem w7c4_54 : ¬ drop0% Iris.ProofMode.fromAnd_sep_persistent_right 6 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True) inferInstance).from_and 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.fromAnd_persistently` idx 5: necessary (SiProp: P=False, Q1=Q2=True)
theorem w7c4_55 : ¬ drop0% Iris.ProofMode.fromAnd_persistently 5 := fun h =>
  (@h SiProp _ iprop(False) iprop(True) iprop(True)).from_and 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAnd_persistently_sep` idx 5: necessary (SiProp: P=False, Q1=Q2=True)
theorem w7c4_56 : ¬ drop0% Iris.ProofMode.fromAnd_persistently_sep 5 := fun h =>
  (@h SiProp _ iprop(False) iprop(True) iprop(True)).from_and 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAnd_bigSepL_cons_persistent` idx 7: necessary (SiProp: Phi k y = (y = true), l=[false], x=true, l'=[])
theorem w7c4_57 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL_cons_persistent 7 := fun h =>
  Bool.noConfusion ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [false] true [] inferInstance).from_and 0
    ⟨rfl, trivial⟩).1

-- `Iris.ProofMode.fromAnd_bigSepL_app_persistent` idx 7: necessary (SiProp: Phi k y = (y = true), l=[false], l1=l2=[])
theorem w7c4_59 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL_app_persistent 7 := fun h =>
  Bool.noConfusion ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [false] [] [] (fun _ _ => inferInstance)).from_and 0
    ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.fromAnd_bigSepL2_cons_persistent` idx 11: necessary (SiProp: Phi=True, l1=[], l2=[()]: lengths differ)
theorem w7c4_61 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL2_cons_persistent 11 := fun h =>
  (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [] () [] [()] () [] ⟨rfl⟩ inferInstance).from_and 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAnd_bigSepL2_cons_persistent` idx 12: necessary (SiProp: Phi=True, l1=[()], l2=[]: lengths differ)
theorem w7c4_62 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL2_cons_persistent 12 := fun h =>
  (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] () [] [] () [] ⟨rfl⟩ inferInstance).from_and 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAnd_bigSepL2_app_persistent` idx 11: necessary (SiProp: Phi=True, l1=[()], all other lists empty)
theorem w7c4_64 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL2_app_persistent 11 := fun h =>
  (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] [] [] [] [] [] ⟨rfl⟩ (fun _ _ _ => inferInstance)).from_and 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromAnd_bigSepL2_app_persistent` idx 12: necessary (SiProp: Phi=True, l2=[()], all other lists empty)
theorem w7c4_65 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL2_app_persistent 12 := fun h =>
  (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [] [] [] [()] [] [] ⟨rfl⟩ (fun _ _ _ => inferInstance)).from_and 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoAnd_wandIff` idx 7: necessary (SiProp: p=false, P1=P2=P2'=True, P1'=False)
theorem w7c4_68 : ¬ drop0% Iris.ProofMode.intoAnd_wandIff 7 := fun h =>
  ((@h SiProp _ false iprop(True) iprop(True) iprop(False) iprop(True)).into_and 0
    ⟨fun _ _ h => h, fun _ _ h => h⟩).1

-- `Iris.ProofMode.intoAnd_iff` idx 7: necessary (SiProp: p=false, P1=P2=P2'=True, P1'=False)
theorem w7c4_69 : ¬ drop0% Iris.ProofMode.intoAnd_iff 7 := fun h =>
  ((@h SiProp _ false iprop(True) iprop(True) iprop(False) iprop(True)).into_and 0
    ⟨fun _ _ h => h, fun _ _ h => h⟩).1

-- `Iris.ProofMode.intoAnd_and_affine_left` idx 6: necessary (SiProp: P=Q=True, Q'=False)
theorem w7c4_71 : ¬ drop0% Iris.ProofMode.intoAnd_and_affine_left 6 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False) inferInstance).into_and 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoAnd_and_affine_right` idx 6: necessary (SiProp: P=Q=True, P'=False)
theorem w7c4_72 : ¬ drop0% Iris.ProofMode.intoAnd_and_affine_right 6 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True) inferInstance).into_and 0 ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.intoAnd_affinely` idx 6: necessary (SiProp: p=false, P=Q2=True, Q1=False)
theorem w7c4_74 : ¬ drop0% Iris.ProofMode.intoAnd_affinely 6 := fun h =>
  ((@h SiProp false _ iprop(True) iprop(False) iprop(True)).into_and 0 ⟨trivial, trivial⟩).1.2

-- `Iris.ProofMode.intoAnd_intuitionistically` idx 6: necessary (SiProp: p=false, P=Q2=True, Q1=False)
theorem w7c4_75 : ¬ drop0% Iris.ProofMode.intoAnd_intuitionistically 6 := fun h =>
  ((@h SiProp false _ iprop(True) iprop(False) iprop(True)).into_and 0 ⟨trivial, trivial⟩).1.2

-- `Iris.ProofMode.intoAnd_persistently` idx 6: necessary (SiProp: p=false, P=Q2=True, Q1=False)
theorem w7c4_76 : ¬ drop0% Iris.ProofMode.intoAnd_persistently 6 := fun h =>
  ((@h SiProp false _ iprop(True) iprop(False) iprop(True)).into_and 0 trivial).1

-- `Iris.ProofMode.fromSep_affinely` idx 5: necessary (SiProp: P=False, Q1=Q2=True)
theorem w7c4_77 : ¬ drop0% Iris.ProofMode.fromSep_affinely 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_sep 0 ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩).2

-- `Iris.ProofMode.fromSep_intuitionistically` idx 5: necessary (SiProp: P=False, Q1=Q2=True)
theorem w7c4_78 : ¬ drop0% Iris.ProofMode.fromSep_intuitionistically 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_sep 0 ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩).2

-- `Iris.ProofMode.fromSep_absorbingly` idx 5: necessary (SiProp: P=False, Q1=Q2=True)
theorem w7c4_79 : ¬ drop0% Iris.ProofMode.fromSep_absorbingly 5 := fun h =>
  ((@h SiProp _ iprop(False) iprop(True) iprop(True)).from_sep 0 ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩).2

-- `Iris.ProofMode.fromSep_persistently` idx 5: necessary (SiProp: P=False, Q1=Q2=True)
theorem w7c4_80 : ¬ drop0% Iris.ProofMode.fromSep_persistently 5 := fun h =>
  (@h SiProp _ iprop(False) iprop(True) iprop(True)).from_sep 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromSep_bigSepL_cons` idx 7: necessary (SiProp: Phi k y = (y = true), l=[false], x=true, l'=[])
theorem w7c4_81 : ¬ drop0% Iris.ProofMode.fromSep_bigSepL_cons 7 := fun h =>
  Bool.noConfusion ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [false] true []).from_sep 0
    ⟨rfl, trivial⟩).1

-- `Iris.ProofMode.fromSep_bigSepL_app` idx 7: necessary (SiProp: Phi k y = (y = true), l=[false], l1=l2=[])
theorem w7c4_82 : ¬ drop0% Iris.ProofMode.fromSep_bigSepL_app 7 := fun h =>
  Bool.noConfusion ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [false] [] []).from_sep 0
    ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.fromSep_bigSepL2_cons` idx 11: necessary (SiProp: Phi=True, l1=[], l2=[()]: lengths differ)
theorem w7c4_83 : ¬ drop0% Iris.ProofMode.fromSep_bigSepL2_cons 11 := fun h =>
  (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [] () [] [()] () [] ⟨rfl⟩).from_sep 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromSep_bigSepL2_cons` idx 12: necessary (SiProp: Phi=True, l1=[()], l2=[]: lengths differ)
theorem w7c4_84 : ¬ drop0% Iris.ProofMode.fromSep_bigSepL2_cons 12 := fun h =>
  (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] () [] [] () [] ⟨rfl⟩).from_sep 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromSep_bigSepL2_app` idx 11: necessary (SiProp: Phi=True, l1=[()], all other lists empty)
theorem w7c4_85 : ¬ drop0% Iris.ProofMode.fromSep_bigSepL2_app 11 := fun h =>
  (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [()] [] [] [] [] [] ⟨rfl⟩).from_sep 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.fromSep_bigSepL2_app` idx 12: necessary (SiProp: Phi=True, l2=[()], all other lists empty)
theorem w7c4_86 : ¬ drop0% Iris.ProofMode.fromSep_bigSepL2_app 12 := fun h =>
  (@h SiProp _ Unit Unit (fun _ _ _ => iprop(True)) [] [] [] [()] [] [] ⟨rfl⟩).from_sep 0
    ⟨trivial, trivial⟩

-- `Iris.ProofMode.intoSep_and_persistent_left` idx 7: necessary (SiProp: P=Q=Q'=True, P'=False)
theorem w7c4_88 : ¬ drop0% Iris.ProofMode.intoSep_and_persistent_left 7 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True) inferInstance).into_sep 0 ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.intoSep_and_persistent_right` idx 7: necessary (SiProp: P=Q=Q'=True, P'=False)
theorem w7c4_90 : ¬ drop0% Iris.ProofMode.intoSep_and_persistent_right 7 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True) inferInstance).into_sep 0 ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.intoSep_affinely` idx 6: necessary (SiProp: P=Q2=True, Q1=False)
theorem w7c4_92 : ¬ drop0% Iris.ProofMode.intoSep_affinely 6 := fun h =>
  ((@h SiProp _ inferInstance iprop(True) iprop(False) iprop(True)).into_sep 0 ⟨trivial, trivial⟩).1.2

-- `Iris.ProofMode.intoSep_intuitionistically` idx 6: necessary (SiProp: P=Q2=True, Q1=False)
theorem w7c4_94 : ¬ drop0% Iris.ProofMode.intoSep_intuitionistically 6 := fun h =>
  ((@h SiProp _ inferInstance iprop(True) iprop(False) iprop(True)).into_sep 0 ⟨trivial, trivial⟩).1.2

-- `Iris.ProofMode.intoSep_affinely_trim` idx 5: necessary (SiProp: P=Q2=True, Q1=False)
theorem w7c4_95 : ¬ drop0% Iris.ProofMode.intoSep_affinely_trim 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True)).into_sep 0 ⟨trivial, trivial⟩).1

-- `Iris.ProofMode.intoSep_persistently_affine` idx 5: necessary (SiProp: P=Q2=True, Q1=False)
theorem w7c4_97 : ¬ drop0% Iris.ProofMode.intoSep_persistently_affine 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True) (Iris.Std.TCOr.l (t := inferInstance))
    (Iris.Std.TCOr.l (t := inferInstance))).into_sep 0 trivial).1

-- `Iris.ProofMode.intoSep_intuitionistically_affine` idx 5: necessary (SiProp: P=Q2=True, Q1=False)
theorem w7c4_98 : ¬ drop0% Iris.ProofMode.intoSep_intuitionistically_affine 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False) iprop(True) (Iris.Std.TCOr.l (t := inferInstance))
    (Iris.Std.TCOr.l (t := inferInstance))).into_sep 0 ⟨trivial, trivial⟩).1.2

-- `Iris.ProofMode.intoSep_bigSepL_cons` idx 7: necessary (SiProp: Phi k y = (y = true), l=[], x=false, l'=[])
theorem w7c4_99 : ¬ drop0% Iris.ProofMode.intoSep_bigSepL_cons 7 := fun h =>
  Bool.noConfusion ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [] false []).into_sep 0 trivial).1

-- `Iris.ProofMode.intoSep_bigSepL_app` idx 7: necessary (SiProp: Phi k y = (y = true), l=[], l1=[false], l2=[])
theorem w7c4_100 : ¬ drop0% Iris.ProofMode.intoSep_bigSepL_app 7 := fun h =>
  Bool.noConfusion ((@h SiProp _ Bool (fun _ y => iprop(⌜y = true⌝)) [] [false] []).into_sep 0 trivial).1.1
end

section
open Iris Iris.BI Iris.ProofMode W7c4

-- `Iris.ProofMode.intoWand_impl_false_true` idx 6: necessary (GB: P=P'=emp (not absorbing), Q=False, at true)
theorem w7c4_3 : ¬ drop0% Iris.ProofMode.intoWand_impl_false_true 6 := fun h =>
  (@h GB _ iprop(emp) iprop(False) iprop(emp) (.matching .argument) ⟨fun _ hx => hx.1⟩).into_wand true
    (fun e => Bool.noConfusion e) false ⟨rfl, rfl⟩

-- `Iris.ProofMode.intoWand_impl_false_false` idx 7: necessary (GB: P=P'=P''=emp (persistent, not absorbing), Q=False, at true)
theorem w7c4_8 : ¬ drop0% Iris.ProofMode.intoWand_impl_false_false 7 := fun h =>
  (@h GB _ iprop(emp) iprop(False) iprop(emp) iprop(emp) (.matching .argument)
    (Iris.Std.TCOr.r (u := inferInstance)) ⟨⟨fun _ h => h.2, fun _ h => ⟨h, h⟩⟩⟩ ⟨fun _ h => h⟩).into_wand true
    (fun e => Bool.noConfusion e) false rfl

-- `Iris.ProofMode.intoWand_persistently_false` idx 7: necessary (GB: R=P=Q=emp, q=false, at true)
theorem w7c4_22 : ¬ drop0% Iris.ProofMode.intoWand_persistently_false 7 := fun h => by
  have hw : IntoWand false false (iprop(emp) : GB) (.matching .argument) iprop(emp) iprop(emp) :=
    ⟨fun x hx y hy => by
      have hx : x = false := hx
      have hy : y = false := hy
      subst hx; subst hy; rfl⟩
  have := (@h GB (.matching .argument) false _ iprop(emp) iprop(emp) iprop(emp) hw).into_wand true
    (rfl : false = false) false rfl
  exact Bool.noConfusion this

-- `Iris.ProofMode.fromForall_intuitionistically` idx 2: necessary (GB: A=False (empty), P=True, at true)
theorem w7c4_27 : ¬ drop0% Iris.ProofMode.fromForall_intuitionistically 2 := fun h =>
  Bool.noConfusion ((@h GB _ inferInstance False iprop(True) (fun a => a.elim) ⟨fun _ _ => trivial⟩).from_forall
    true (fun _ ⟨a, _⟩ => a.elim)).1

-- `Iris.ProofMode.fromForall_intuitionistically` idx 3: necessary (at A : Type) in PF, Phi = evk, P = their intersection (not cofinite)
theorem w7c4_28 : ¬ ∀ {PROP : Type} [inst : Iris.BI PROP] [Iris.BI.BIAffine PROP] {A : Type} (P : PROP)
    (Φ : A → PROP) [Iris.ProofMode.FromForall P Φ],
    Iris.ProofMode.FromForall iprop(□ P) fun (a : A) => iprop(□ Φ a) := fun h => by
  have := (@h PF _ _ Nat (fun n => ∀ k, evk k n) evk ⟨fun _ hx k => hx _ ⟨k, rfl⟩⟩).from_forall 0
    (fun p ⟨k, e⟩ => e ▸ ⟨trivial, evk_cof k, .inl rfl⟩)
  exact evk_all_not_cof this.2.1

-- `Iris.ProofMode.fromForall_persistently` idx 2: necessary (at A : Type) in PF, Phi = evk, P = their intersection (not cofinite)
theorem w7c4_29 : ¬ ∀ {PROP : Type} [inst : Iris.BI PROP] {A : Type} (P : PROP)
    (Φ : A → PROP) [Iris.ProofMode.FromForall P Φ],
    Iris.ProofMode.FromForall iprop(<pers> P) fun (a : A) => iprop(<pers> Φ a) := fun h => by
  have := (@h PF _ Nat (fun n => ∀ k, evk k n) evk ⟨fun _ hx k => hx _ ⟨k, rfl⟩⟩).from_forall 0
    (fun p ⟨k, e⟩ => e ▸ ⟨evk_cof k, .inl rfl⟩)
  exact evk_all_not_cof this.1

-- `Iris.ProofMode.intoForall_imp` idx 2: necessary (GB: P=emp, Q=False, at true)
theorem w7c4_36 : ¬ drop0% Iris.ProofMode.intoForall_imp 2 := fun h =>
  (@h GB _ iprop(emp) iprop(False)).into_forall true (fun e => Bool.noConfusion e) _
    ⟨(fun _ h => h : (iprop(emp) : GB) ⊢ iprop(emp)), rfl⟩

-- `Iris.ProofMode.intoExists_intuitionistically` idx 3: necessary (at alpha : Type) in PF, Phi true = evens, Phi false = odds, P = their union
theorem w7c4_42 : ¬ ∀ {PROP : Type} {α : Type} [inst : Iris.BI PROP] (P : PROP) (Φ : α → PROP)
    [h : Iris.ProofMode.IntoExists P Φ],
    Iris.ProofMode.IntoExists iprop(□ P) fun (a : α) => iprop(□ Φ a) := fun h => by
  have := (@h PF Bool _ (fun n => ev n ∨ od n) eo
    ⟨fun _ hx => hx.elim (fun he => ⟨ev, ⟨true, rfl⟩, he⟩) (fun ho => ⟨od, ⟨false, rfl⟩, ho⟩)⟩).into_exists 0
    ⟨trivial, evod_cof, .inl rfl⟩
  obtain ⟨p, ⟨b, e⟩, hp⟩ := this
  subst e
  cases b
  · exact od_not_cof hp.2.1
  · exact ev_not_cof hp.2.1

-- `Iris.ProofMode.intoExists_persistently` idx 3: necessary (at alpha : Type) in PF, Phi true = evens, Phi false = odds, P = their union
theorem w7c4_47 : ¬ ∀ {PROP : Type} {α : Type} [inst : Iris.BI PROP] {P : PROP} (Φ : α → PROP)
    [h : Iris.ProofMode.IntoExists P Φ],
    Iris.ProofMode.IntoExists iprop(<pers> P) fun (a : α) => iprop(<pers> Φ a) := fun h => by
  have := (@h PF Bool _ (fun n => ev n ∨ od n) eo
    ⟨fun _ hx => hx.elim (fun he => ⟨ev, ⟨true, rfl⟩, he⟩) (fun ho => ⟨od, ⟨false, rfl⟩, ho⟩)⟩).into_exists 0
    ⟨evod_cof, .inl rfl⟩
  obtain ⟨p, ⟨b, e⟩, hp⟩ := this
  subst e
  cases b
  · exact od_not_cof hp.1
  · exact ev_not_cof hp.1

-- `Iris.ProofMode.fromAnd_sep_persistent_left` idx 5: necessary (GB: P1=own1 (not persistent), P1'=True, P2=emp, at false)
theorem w7c4_51 : ¬ drop0% Iris.ProofMode.fromAnd_sep_persistent_left 5 := fun h => by
  have := (@h GB _ own1 iprop(True) iprop(emp)
    ⟨fun x _ => ⟨xor x true, true, by cases x <;> rfl, trivial, rfl⟩⟩).from_and false ⟨trivial, rfl⟩
  obtain ⟨a, b, e, ha, hb⟩ := this
  have ha : a = true := ha
  have hb : b = false := hb
  subst ha; subst hb; exact Bool.noConfusion e

-- `Iris.ProofMode.fromAnd_sep_persistent_right` idx 5: necessary (GB: P2=own1 (not persistent), P2'=True, P1=emp, at false)
theorem w7c4_53 : ¬ drop0% Iris.ProofMode.fromAnd_sep_persistent_right 5 := fun h => by
  have := (@h GB _ iprop(emp) own1 iprop(True)
    ⟨fun x _ => ⟨xor x true, true, by cases x <;> rfl, trivial, rfl⟩⟩).from_and false ⟨rfl, trivial⟩
  obtain ⟨a, b, e, ha, hb⟩ := this
  have ha : a = false := ha
  have hb : b = true := hb
  subst ha; subst hb; exact Bool.noConfusion e

-- `Iris.ProofMode.fromAnd_bigSepL_cons_persistent` idx 8: necessary (GB: Phi = own1, l = [(),()], at true)
theorem w7c4_58 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL_cons_persistent 8 := fun h =>
  gb_o1o1e_true ((@h GB _ Unit (fun _ _ => own1) [(), ()] () [()] ⟨rfl⟩).from_and true ⟨rfl, gb_o1e_true⟩)

-- `Iris.ProofMode.fromAnd_bigSepL_app_persistent` idx 8: necessary (GB: Phi = own1, l = [(),()], l1 = l2 = [()], at true)
theorem w7c4_60 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL_app_persistent 8 := fun h =>
  gb_o1o1e_true ((@h GB _ Unit (fun _ _ => own1) [(), ()] [()] [()] ⟨rfl⟩).from_and true
    ⟨gb_o1e_true, gb_o1e_true⟩)

-- `Iris.ProofMode.fromAnd_bigSepL2_cons_persistent` idx 13: necessary (GB: Phi = own1, l1 = l2 = [(),()], at true)
theorem w7c4_63 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL2_cons_persistent 13 := fun h =>
  gb_o1o1e_true ((@h GB _ Unit Unit (fun _ _ _ => own1) [(), ()] () [()] [(), ()] () [()] ⟨rfl⟩ ⟨rfl⟩).from_and
    true ⟨rfl, gb_o1e_true⟩)

-- `Iris.ProofMode.fromAnd_bigSepL2_app_persistent` idx 13: necessary (GB: Phi = own1, l1 = l2 = [(),()] split as [()] ++ [()], at true)
theorem w7c4_66 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepL2_app_persistent 13 := fun h =>
  gb_o1o1e_true ((@h GB _ Unit Unit (fun _ _ _ => own1) [(), ()] [()] [()] [(), ()] [()] [()] ⟨rfl⟩ ⟨rfl⟩).from_and
    true ⟨gb_o1e_true, gb_o1e_true⟩)

-- `Iris.ProofMode.fromAnd_bigSepMS_disjUnion_persistent` idx 8: necessary (GB, ListPerm Nat: Phi = own1, X1 = X2 = {0}, at true)
theorem w7c4_67 : ¬ drop0% Iris.ProofMode.fromAnd_bigSepMS_disjUnion_persistent 8 := fun h => by
  have s1 := (BigSepMS.bigSepMS_singleton (PROP := GB) (MS := Iris.Std.ListPerm Nat)
    (Φ := fun _ => own1) (x := 0)).2 true rfl
  have r := (@h GB _ (Iris.Std.ListPerm Nat) Nat _ (fun _ => own1) {0} {0}).from_and true ⟨s1, s1⟩
  have r2 := (BigSepMS.bigSepMS_disjUnion (PROP := GB) (MS := Iris.Std.ListPerm Nat)
    (Φ := fun _ => own1) (X := {0}) (Y := {0})).1 true r
  have hs := (BigSepMS.bigSepMS_singleton (PROP := GB) (MS := Iris.Std.ListPerm Nat)
    (Φ := fun _ => own1) (x := 0)).1
  exact gb_o1o1_true (sep_mono hs hs true r2)

-- `Iris.ProofMode.intoAnd_and_affine_left` idx 5: necessary (GB: P=Q=True (not affine), Q'=emp, at true)
theorem w7c4_70 : ¬ drop0% Iris.ProofMode.intoAnd_and_affine_left 5 := fun h =>
  Bool.noConfusion ((@h GB _ iprop(True) iprop(True) iprop(emp) ⟨fun _ h => h.1⟩).into_and true
    ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.intoAnd_sep` idx 2: necessary (GB: P=Q=own1, at false)
theorem w7c4_73 : ¬ drop0% Iris.ProofMode.intoAnd_sep 2 := fun h =>
  Bool.noConfusion ((@h GB _ own1 own1).into_and false ⟨rfl, true, true, rfl, rfl, rfl⟩).2.1

-- `Iris.ProofMode.intoSep_and_persistent_left` idx 6: necessary (GB: P=own1 (not persistent), P'=affinely own1, Q=Q'=True, at true)
theorem w7c4_87 : ¬ drop0% Iris.ProofMode.intoSep_and_persistent_left 6 := fun h => by
  have := (@h GB _ own1 iprop(True) iprop(<affine> own1) iprop(True) (.affinely _ _)).into_sep true ⟨rfl, trivial⟩
  obtain ⟨a, b, e, ⟨ha1, ha2⟩, _⟩ := this
  have ha1 : a = false := ha1
  have ha2 : a = true := ha2
  exact Bool.noConfusion (ha1.symm.trans ha2)

-- `Iris.ProofMode.intoSep_and_persistent_right` idx 6: necessary (GB: Q=own1 (not persistent), Q'=affinely own1, P=P'=True, at true)
theorem w7c4_89 : ¬ drop0% Iris.ProofMode.intoSep_and_persistent_right 6 := fun h => by
  have := (@h GB _ iprop(True) own1 iprop(True) iprop(<affine> own1) (.affinely _ _)).into_sep true ⟨trivial, rfl⟩
  obtain ⟨a, b, e, _, ⟨hb1, hb2⟩⟩ := this
  have hb1 : b = false := hb1
  have hb2 : b = true := hb2
  exact Bool.noConfusion (hb1.symm.trans hb2)

-- `Iris.ProofMode.intoSep_affinely` idx 2: necessary (GB: P = own1 ∗ own1, Q1=Q2=own1, at false)
theorem w7c4_91 : ¬ drop0% Iris.ProofMode.intoSep_affinely 2 := fun h => by
  have := (@h GB _ iprop(own1 ∗ own1) own1 own1 ⟨fun _ h => h⟩).into_sep false ⟨rfl, true, true, rfl, rfl, rfl⟩
  obtain ⟨a, b, e, ⟨ha1, ha2⟩, _⟩ := this
  have ha1 : a = false := ha1
  have ha2 : a = true := ha2
  exact Bool.noConfusion (ha1.symm.trans ha2)

-- `Iris.ProofMode.intoSep_intuitionistically` idx 2: necessary (GB: P = own1 ∗ own1, Q1=Q2=own1, at false)
theorem w7c4_93 : ¬ drop0% Iris.ProofMode.intoSep_intuitionistically 2 := fun h => by
  have := (@h GB _ iprop(own1 ∗ own1) own1 own1 ⟨fun _ h => h⟩).into_sep false ⟨rfl, true, true, rfl, rfl, rfl⟩
  obtain ⟨a, b, e, ⟨_, ha⟩, _⟩ := this
  exact Bool.noConfusion (ha : false = true)

-- `Iris.ProofMode.intoSep_persistently` idx 2: necessary (GB: P = own1 ∗ own1, Q1=Q2=own1, at false)
theorem w7c4_96 : ¬ drop0% Iris.ProofMode.intoSep_persistently 2 := fun h => by
  have := (@h GB _ iprop(own1 ∗ own1) own1 own1 ⟨fun _ h => h⟩).into_sep false ⟨true, true, rfl, rfl, rfl⟩
  obtain ⟨a, b, e, ha, _⟩ := this
  exact Bool.noConfusion (ha : false = true)
end
