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
namespace W9c1
open Iris Iris.BI Iris.OFE

/-- Truncation OFE on naturals (copied from Probe1): 1 and 2 agree at step 0. -/
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

/-- Discrete Bool OFE (copied from W5c1). -/
structure DB where b : Bool
instance : OFE DB := OFE.ofDiscrete DB
def dT : DB := ⟨true⟩
def dF : DB := ⟨false⟩
theorem dTF : dT ≠ dF := by simp [dT, dF]
theorem db_ne {B : Type} [OFE B] (f : DB → B) : NonExpansive f := ⟨fun _ _ _ h => (h : _ = _) ▸ OFE.Dist.rfl⟩

/-! GB (copied from W4c4): predicates on Bool with sep over xor; non-affine, own1 not persistent. -/
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

end W9c1

section
open Iris Iris.BI Iris.OFE Iris.ProofMode W9c1

-- `Iris.ProofMode.wand_revert` idx 6: necessary (SiProp: Δ = P = True, Δ' = Q = False)
theorem w9c1_1 : ¬ drop0% Iris.ProofMode.wand_revert 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(True) iprop(False) (fun _ hf => hf.elim)) 0 trivial

-- `Iris.ProofMode.wand_revert` idx 7: necessary (SiProp: Δ = Δ' = P = True, Q = False)
theorem w9c1_2 : ¬ drop0% Iris.ProofMode.wand_revert 7 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False)
    ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩) 0 trivial

-- `Iris.ProofMode.forall_revert` idx 5: necessary (SiProp: α = True, Δ = True, Ψ = const False)
theorem w9c1_3 : ¬ drop0% Iris.ProofMode.forall_revert 5 := fun h =>
  (@h SiProp True _ iprop(True) (fun _ => iprop(False)) trivial) 0 trivial

-- `Iris.ProofMode.pure_revert` idx 6: necessary (SiProp: Δ = True, P = Q = False, φ = True)
theorem w9c1_4 : ¬ drop0% Iris.ProofMode.pure_revert 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) True (fun _ _ _ _ hf => hf) trivial) 0 trivial

-- `Iris.ProofMode.pure_revert` idx 7: necessary (SiProp: Δ = True, P = <affine> ⌜True⌝, Q = False)
theorem w9c1_5 : ¬ drop0% Iris.ProofMode.pure_revert 7 := fun h =>
  (@h SiProp _ iprop(True) iprop(<affine> ⌜True⌝) iprop(False) True
    ⟨⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩⟩ trivial) 0 trivial

-- `Iris.ProofMode.pure_revert` idx 8: necessary (SiProp: φ = False, P = <affine> ⌜False⌝, Δ = True, Q = False)
theorem w9c1_6 : ¬ drop0% Iris.ProofMode.pure_revert 8 := fun h =>
  (@h SiProp _ iprop(True) iprop(<affine> ⌜False⌝) iprop(False) False
    ⟨⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩⟩ (fun _ _ _ _ hp => hp.2.elim)) 0 trivial

-- `Iris.ProofMode.rewrite_tac` idx 11: necessary (SiProp, A = TN, a = 1, b = 2 agree at step 0, Ψ x = ⌜x = 1⌝ not non-expansive)
theorem w9c1_7 : ¬ drop0% Iris.ProofMode.rewrite_tac 11 := fun h => by
  have H := (@h SiProp _ iprop(internalEq (⟨1⟩ : TN) ⟨2⟩) iprop(emp) iprop(internalEq (⟨1⟩ : TN) ⟨2⟩) TN _
    ⟨1⟩ ⟨2⟩ false (fun x => iprop(⌜x = ⟨1⟩⌝)) _ emp_sep.mpr) 0 tn12
  have H2 : (⟨2⟩ : TN) = ⟨1⟩ := H.1 0 (Nat.le_refl 0) rfl
  simp at H2

-- `Iris.ProofMode.rewrite_tac` idx 12: necessary (SiProp, discrete Bool, a = true, b = false, Ψ x = ⌜x = true⌝, P = P' = Q = True)
theorem w9c1_8 : ¬ drop0% Iris.ProofMode.rewrite_tac 12 := fun h => by
  have H := (@h SiProp _ iprop(True) iprop(True) iprop(True) DB _ dT dF false (fun x => iprop(⌜x = dT⌝))
    (db_ne _) (fun _ _ => ⟨trivial, trivial⟩)) 0 trivial
  exact dTF (H.1 0 (Nat.le_refl 0) rfl).symm

-- `Iris.ProofMode.rewrite_tac` idx 13: necessary (SiProp, discrete Bool, Q = (true ≡ false), Ψ x = ⌜x = true⌝, P = True)
theorem w9c1_9 : ¬ drop0% Iris.ProofMode.rewrite_tac 13 := fun h => by
  have H := (@h SiProp _ iprop(True) iprop(True) iprop(internalEq dT dF) DB _ dT dF false (fun x => iprop(⌜x = dT⌝))
    (db_ne _) _) 0 trivial
  exact dTF (H.1 0 (Nat.le_refl 0) rfl).symm

-- `Iris.ProofMode.rewrite_tac_symm` idx 11: necessary (SiProp, A = TN, a = 1, b = 2, Ψ x = ⌜x = 1⌝ not non-expansive)
theorem w9c1_10 : ¬ drop0% Iris.ProofMode.rewrite_tac_symm 11 := fun h => by
  have H := (@h SiProp _ iprop(internalEq (⟨1⟩ : TN) ⟨2⟩) iprop(emp) iprop(internalEq (⟨1⟩ : TN) ⟨2⟩) TN _
    ⟨1⟩ ⟨2⟩ false (fun x => iprop(⌜x = ⟨1⟩⌝)) _ emp_sep.mpr) 0 tn12
  have H2 : (⟨2⟩ : TN) = ⟨1⟩ := H.2 0 (Nat.le_refl 0) rfl
  simp at H2

-- `Iris.ProofMode.rewrite_tac_symm` idx 12: necessary (SiProp, discrete Bool, a = true, b = false, P = P' = Q = True)
theorem w9c1_11 : ¬ drop0% Iris.ProofMode.rewrite_tac_symm 12 := fun h => by
  have H := (@h SiProp _ iprop(True) iprop(True) iprop(True) DB _ dT dF false (fun x => iprop(⌜x = dT⌝))
    (db_ne _) (fun _ _ => ⟨trivial, trivial⟩)) 0 trivial
  exact dTF (H.2 0 (Nat.le_refl 0) rfl).symm

-- `Iris.ProofMode.rewrite_tac_symm` idx 13: necessary (SiProp, discrete Bool, Q = (true ≡ false), P = True)
theorem w9c1_12 : ¬ drop0% Iris.ProofMode.rewrite_tac_symm 13 := fun h => by
  have H := (@h SiProp _ iprop(True) iprop(True) iprop(internalEq dT dF) DB _ dT dF false (fun x => iprop(⌜x = dT⌝))
    (db_ne _) _) 0 trivial
  exact dTF (H.2 0 (Nat.le_refl 0) rfl).symm

-- `Iris.ProofMode.rewrite_tac_goal` idx 5: necessary (SiProp: P = Q' = True, Q = False)
theorem w9c1_13 : ¬ drop0% Iris.ProofMode.rewrite_tac_goal 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(True) (fun _ _ => trivial)) 0 trivial

-- `Iris.ProofMode.rewrite_tac_goal` idx 6: necessary (SiProp: P = True, Q = Q' = False)
theorem w9c1_14 : ¬ drop0% Iris.ProofMode.rewrite_tac_goal 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) (fun _ _ => ⟨fun _ _ hf => hf, fun _ _ hf => hf⟩)) 0 trivial

-- `Iris.ProofMode.rewrite_tac_hyp` idx 5: necessary (SiProp: P = Q = True, Q' = False)
theorem w9c1_15 : ¬ drop0% Iris.ProofMode.rewrite_tac_hyp 5 := fun h =>
  ((@h SiProp _ iprop(True) iprop(True) iprop(False)) 0 trivial) 0 (Nat.le_refl 0) trivial

-- `Iris.ProofMode.specialize_wand` idx 8: necessary (SiProp: p = q = false, A = Q = P1 = True, P2 = False)
theorem w9c1_16 : ¬ drop0% Iris.ProofMode.specialize_wand 8 := fun h =>
  ((@h SiProp _ false false iprop(True) iprop(True) iprop(True) iprop(False)) 0 ⟨⟨trivial, trivial⟩, trivial⟩).2

-- `Iris.ProofMode.specialize_wand_nest` idx 13: necessary (SiProp: all True except goal = out2 = False; h2 vacuous)
theorem w9c1_17 : ¬ drop0% Iris.ProofMode.specialize_wand_nest 13 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) iprop(True) iprop(True) iprop(True) iprop(False)
    false false false ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩
    (fun hx => ((hx 0 ⟨trivial, trivial⟩) 0 (Nat.le_refl 0) trivial).elim)
    (fun _ hf => hf.2)) 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.specialize_wand_nest` idx 14: necessary (SiProp: e = out = Q = out1' = out2 = True, e' = e'' = goal = False)
theorem w9c1_18 : ¬ drop0% Iris.ProofMode.specialize_wand_nest 14 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) iprop(False) iprop(True) iprop(True) iprop(True) iprop(True)
    false false false ⟨fun _ _ _ _ _ => trivial⟩
    (fun _ _ hf => hf.1.elim)
    (fun _ hf => hf.1)) 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.specialize_wand_nest` idx 15: necessary (SiProp: e = e' = out = out1' = Q = out2 = True, e'' = goal = False)
theorem w9c1_19 : ¬ drop0% Iris.ProofMode.specialize_wand_nest 15 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(False) iprop(True) iprop(True) iprop(True) iprop(True)
    false false false ⟨fun _ _ _ _ _ => trivial⟩ ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩
    (fun _ hf => hf.1)) 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.specialize_wand_nest` idx 16: necessary (SiProp: all True except goal = False; h2 vacuous)
theorem w9c1_20 : ¬ drop0% Iris.ProofMode.specialize_wand_nest 16 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) iprop(True) iprop(True) iprop(True) iprop(True)
    false false false ⟨fun _ _ _ _ _ => trivial⟩ ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩
    (fun hx => ((hx 0 ⟨trivial, trivial⟩) 0 (Nat.le_refl 0) trivial).elim)) 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.specialize_wand_modal` idx 10: necessary (SiProp: e = R = P1 = P2 = True, e' = goal = P1' = False)
theorem w9c1_21 : ¬ drop0% Iris.ProofMode.specialize_wand_modal 10 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) iprop(True) iprop(True) iprop(False) iprop(True) false
    (fun _ hf => hf.1) ⟨fun _ _ _ _ _ => trivial⟩ ⟨fun _ hf => hf.1⟩) 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.specialize_wand_modal` idx 11: necessary (SiProp: all True except goal = False)
theorem w9c1_22 : ¬ drop0% Iris.ProofMode.specialize_wand_modal 11 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True) iprop(True) iprop(True) iprop(True) false
    (fun _ _ => ⟨trivial, trivial⟩) ⟨fun _ _ _ _ _ => trivial⟩
    ⟨fun n hf => hf.2 n (Nat.le_refl n) trivial⟩) 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.specialize_wand_modal` idx 12: necessary (SiProp: e = e' = R = P1 = P1' = True, P2 = goal = False)
theorem w9c1_23 : ¬ drop0% Iris.ProofMode.specialize_wand_modal 12 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True) iprop(True) iprop(True) iprop(False) false
    (fun _ _ => ⟨trivial, trivial⟩) (fun _ hf => hf.2)
    ⟨fun n hf => hf.2 n (Nat.le_refl n) trivial⟩) 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.specialize_wand_modal` idx 13: necessary (SiProp: e = e' = R = P1' = True, P1 = P2 = goal = False)
theorem w9c1_24 : ¬ drop0% Iris.ProofMode.specialize_wand_modal 13 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True) iprop(False) iprop(True) iprop(False) false
    (fun _ _ => ⟨trivial, trivial⟩) (fun _ hf => hf.2) ⟨fun _ _ _ _ hf => hf⟩) 0 ⟨trivial, trivial⟩

-- `Iris.ProofMode.specialize_wand_intuitionistic` idx 9: necessary (SiProp: q = false, all True except P2 = False)
theorem w9c1_25 : ¬ drop0% Iris.ProofMode.specialize_wand_intuitionistic 9 := fun h =>
  ((@h SiProp _ false iprop(True) iprop(True) iprop(True) iprop(True) iprop(True) iprop(False)
    ⟨fun _ h => h⟩ ⟨fun _ _ => ⟨trivial, trivial⟩⟩ (fun _ _ => ⟨trivial, trivial⟩)) 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.specialize_wand_intuitionistic` idx 10: necessary (GB: P1 = P1' = own1 not persistent, □ own1 is False, A2 = A3 = Q = True, P2 = False)
theorem w9c1_26 : ¬ drop0% Iris.ProofMode.specialize_wand_intuitionistic 10 := fun h => by
  have H := (@h GB _ false iprop(True) iprop(True) iprop(True) own1 own1 iprop(False)
    ⟨fun _ _ _ hy => absurd (hy.2 : false = true) (by decide)⟩
    ⟨fun x hx => ⟨false, x, by cases x <;> rfl, trivial, hx⟩⟩
    (fun x _ => ⟨xor x true, true, by cases x <;> rfl, trivial, rfl⟩)) false ⟨false, false, rfl, trivial, trivial⟩
  obtain ⟨_, _, _, _, hf⟩ := H
  exact hf

-- `Iris.ProofMode.specialize_wand_intuitionistic` idx 11: necessary (SiProp: P1 = P2 = False, P1' = A2 = A3 = Q = True)
theorem w9c1_27 : ¬ drop0% Iris.ProofMode.specialize_wand_intuitionistic 11 := fun h =>
  ((@h SiProp _ false iprop(True) iprop(True) iprop(True) iprop(True) iprop(False) iprop(False)
    ⟨fun _ _ _ _ hf => hf.2⟩ ⟨fun _ h => h⟩ (fun _ _ => ⟨trivial, trivial⟩)) 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.specialize_wand_intuitionistic` idx 12: necessary (SiProp: P1 = P1' = P2 = False, A2 = A3 = Q = True)
theorem w9c1_28 : ¬ drop0% Iris.ProofMode.specialize_wand_intuitionistic 12 := fun h =>
  ((@h SiProp _ false iprop(True) iprop(True) iprop(True) iprop(False) iprop(False) iprop(False)
    ⟨fun _ _ _ _ hf => hf.2⟩ ⟨fun _ h => h⟩ ⟨fun _ hf => hf.elim⟩) 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.specialize_forall` idx 7: necessary (SiProp: A2 = P = True, Φ = const False, α = True)
theorem w9c1_29 : ¬ drop0% Iris.ProofMode.specialize_forall 7 := fun h =>
  ((@h SiProp _ false iprop(True) iprop(True) True (fun _ => iprop(False)) trivial) 0 ⟨trivial, trivial⟩).2

-- `Iris.ProofMode.specialize_dup_context` idx 9: necessary (SiProp: pa = true, pb = false, P = A = P' = B = True, B' = False)
theorem w9c1_30 : ¬ drop0% Iris.ProofMode.specialize_dup_context 9 := fun h =>
  ((@h SiProp _ iprop(True) true iprop(True) iprop(True) false iprop(True) iprop(False)
    (fun _ _ => ⟨trivial, trivial⟩) (Or.inl rfl)) 0 ⟨trivial, trivial, trivial⟩).2.2

-- `Iris.ProofMode.specialize_dup_context` idx 10: necessary (SiProp: pa = true, pb = false, P = A = P' = True, B = B' = False)
theorem w9c1_31 : ¬ drop0% Iris.ProofMode.specialize_dup_context 10 := fun h =>
  ((@h SiProp _ iprop(True) true iprop(True) iprop(True) false iprop(False) iprop(False)
    ⟨fun _ h => h⟩ (Or.inl rfl)) 0 ⟨trivial, trivial, trivial⟩).2.2

-- `Iris.ProofMode.from_and_intro` idx 6: necessary (SiProp: P = A1 = A2 = True, Q = False)
theorem w9c1_32 : ¬ drop0% Iris.ProofMode.from_and_intro 6 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(True) iprop(True) (fun _ _ => trivial) (fun _ _ => trivial)) 0 trivial

-- `Iris.ProofMode.from_and_intro` idx 7: necessary (SiProp: P = A2 = True, Q = A1 = False)
theorem w9c1_33 : ¬ drop0% Iris.ProofMode.from_and_intro 7 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) iprop(True) ⟨fun _ h => h.1⟩ (fun _ _ => trivial)) 0 trivial

-- `Iris.ProofMode.from_and_intro` idx 8: necessary (SiProp: P = A1 = True, Q = A2 = False)
theorem w9c1_34 : ¬ drop0% Iris.ProofMode.from_and_intro 8 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(True) iprop(False) ⟨fun _ h => h.2⟩ (fun _ _ => trivial)) 0 trivial

-- `Iris.ProofMode.sep_split` idx 8: necessary (SiProp: all True except Q = False)
theorem w9c1_35 : ¬ drop0% Iris.ProofMode.sep_split 8 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) iprop(True) iprop(True)
    ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩ (fun _ _ => trivial) (fun _ _ => trivial)) 0 trivial

-- `Iris.ProofMode.sep_split` idx 9: necessary (SiProp: P = True, P1 = P2 = Q = Q1 = Q2 = False)
theorem w9c1_36 : ¬ drop0% Iris.ProofMode.sep_split 9 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) iprop(False) iprop(False) iprop(False) iprop(False)
    ⟨fun _ h => h.1⟩ (fun _ h => h) (fun _ h => h)) 0 trivial

-- `Iris.ProofMode.sep_split` idx 10: necessary (SiProp: P = P1 = P2 = Q2 = True, Q = Q1 = False)
theorem w9c1_37 : ¬ drop0% Iris.ProofMode.sep_split 10 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) iprop(False) iprop(True)
    ⟨fun _ h => h.1⟩ ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩ (fun _ _ => trivial)) 0 trivial

-- `Iris.ProofMode.sep_split` idx 11: necessary (SiProp: P = P1 = P2 = Q1 = True, Q = Q2 = False)
theorem w9c1_38 : ¬ drop0% Iris.ProofMode.sep_split 11 := fun h =>
  (@h SiProp _ iprop(True) iprop(True) iprop(True) iprop(False) iprop(True) iprop(False)
    ⟨fun _ h => h.2⟩ ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩ (fun _ _ => trivial)) 0 trivial

end
namespace W9c1
open Iris Iris.Std

/-- Lawful big-op structure on Prop: And with unit True, equivalence Iff. -/
instance andBO : Iris.Std.LawfulBigOp (PROP := Prop) And True Iff where
  refl := Iff.rfl
  symm := Iff.symm
  trans := Iff.trans
  comm := And.comm
  assoc := and_assoc
  left_id := ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  congr_l h := ⟨fun ⟨x, y⟩ => ⟨h.1 x, y⟩, fun ⟨x, y⟩ => ⟨h.2 x, y⟩⟩

/-- A non-well-formed raw CoPset tree (full set written as a node). -/
abbrev badT : CoPsetRaw := .node true (.leaf true) (.leaf true)

theorem badT_all (p : Pos) : CoPsetRaw.ElemOf p badT = CoPsetRaw.ElemOf p (.leaf true) := by cases p <;> simp

/-- Multisets over Bool as counts (number of false, number of true); toList lists false first. -/
structure BM where
  nf : Nat
  nt : Nat
  deriving DecidableEq

def bmc (x : Bool) (X : BM) : Nat := if x then X.nt else X.nf

instance : Iris.Std.MultiSet BM Bool where
  singleton a := if a then ⟨0, 1⟩ else ⟨1, 0⟩
  emptyCollection := ⟨0, 0⟩
  union X Y := ⟨max X.nf Y.nf, max X.nt Y.nt⟩
  inter X Y := ⟨min X.nf Y.nf, min X.nt Y.nt⟩
  sdiff X Y := ⟨X.nf - Y.nf, X.nt - Y.nt⟩
  multiplicity := bmc
  disjUnion X Y := ⟨X.nf + Y.nf, X.nt + Y.nt⟩

instance bmL : Iris.Std.LawfulFiniteMultiSet BM Bool where
  ext {X Y} h := by
    have h1 : X.nf = Y.nf := h false
    have h2 : X.nt = Y.nt := h true
    cases X; cases Y; simp_all
  multiplicity_empty := by intro x; cases x <;> rfl
  multiplicity_singleton_eq := by intro x; cases x <;> rfl
  multiplicity_singleton_ne := by intro x y h; cases x <;> cases y <;> first | rfl | exact absurd rfl h
  multiplicity_disjUnion := by intro X Y x; cases x <;> rfl
  multiplicity_union := by intro X Y x; cases x <;> rfl
  multiplicity_intersection := by intro X Y x; cases x <;> rfl
  multiplicity_difference := by intro X Y x; cases x <;> rfl
  toList X := List.replicate X.nf false ++ List.replicate X.nt true
  mem_toList := by
    intro a m
    show _ ↔ 0 < bmc a m
    cases a <;> simp [bmc, List.mem_replicate] <;> omega
  toList_empty := rfl
  toList_singleton := by intro a; cases a <;> rfl
  toList_disjUnion := by
    intro X Y
    exact List.perm_iff_count.mpr fun x => by
      show List.count x (List.replicate (X.nf + Y.nf) false ++ List.replicate (X.nt + Y.nt) true) = _
      cases x <;> simp [List.count_append, List.count_replicate] <;> omega

/-- Finite sets of Bool as characteristic functions (copied from Probe4); toList lists false first. -/
def BS := Bool → Bool

instance : Iris.Std.Set BS Bool where
  mem X x := X x = true
  singleton y := fun x => x == y
  union X Y := fun x => or (X x) (Y x)
  inter X Y := fun x => and (X x) (Y x)
  sdiff X Y := fun x => and (X x) (not (Y x))
  emptyCollection := fun _ => false

def bsList (X : BS) : List Bool := (if X false then [false] else []) ++ (if X true then [true] else [])

instance bsLFS : LawfulFiniteSet BS Bool where
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

/-- Computable membership test for BS (the library's generic instance is stuck for `decide`). -/
instance (priority := high) bsMemDec (x : Bool) (X : BS) : Decidable (x ∈ X) :=
  inferInstanceAs (Decidable (X x = true))

abbrev bT : BS := {true}
abbrev bF : BS := {false}
abbrev bE : BS := ∅

theorem mT : true ∈ bT := LawfulSet.mem_singleton.mpr rfl
theorem bs_ne {X Y : BS} (h : X true ≠ Y true) : X ≠ Y := fun e => h (congrArg (fun Z : BS => Z true) e)
theorem bE_sub (X : BS) : bE ⊆ X := fun _ hx => (LawfulSet.mem_empty hx).elim

/-- In CoPset, a set that is not `isFinite` is not `setFinite`, and an `isFinite` set is not `setInfinite`. -/
theorem cinf {X : CoPset} (hX : ¬ CoPset.isFinite X = true) : ¬ LawfulSet.setFinite X :=
  fun hf => hX (isFinite_setFinite.mpr hf)
theorem cnotinf {X : CoPset} (hX : CoPset.isFinite X = true) : ¬ LawfulSet.setInfinite X :=
  fun hi => (not_isFinite_setInfinite.mpr hi) hX
theorem cfin {X : CoPset} (hX : CoPset.isFinite X = true) : LawfulSet.setFinite X :=
  isFinite_setFinite.mp hX

abbrev TS := Std.ExtTreeSet Nat compare

/-- CoPsets with equal trees are equal. -/
theorem ceq {X Y : CoPset} (h : X.tree = Y.tree) : X = Y := by
  cases X; cases Y; cases h; rfl

theorem tg_src : ∀ {x y : Bool}, Relation.TransGen (fun x (_ : Bool) => x = true) x y → x = true := by
  intro x y h
  induction h with
  | single hr => exact hr
  | tail _ _ ih => exact ih

end W9c1

section
open Iris Iris.Std W9c1

-- `Iris.Std.LawfulBigOp.symm` idx 7: necessary (at PROP : Type; Prop, And, unit True, eq = Iff; a = True, b = False)
theorem w9c1_39 : ¬ ∀ {PROP : Type} (f : PROP → PROP → PROP) {unit : PROP} {eq : PROP → PROP → Prop}
    [Iris.Std.LawfulBigOp f unit eq] {a b : PROP}, eq b a := fun h =>
  (@h Prop And True Iff andBO True False).mpr trivial

-- `Iris.Std.LawfulBigOp.trans` idx 8: necessary (at PROP : Type; Prop, And/True/Iff; a = True, b = c = False)
theorem w9c1_40 : ¬ ∀ {PROP : Type} (f : PROP → PROP → PROP) {unit : PROP} {eq : PROP → PROP → Prop}
    [Iris.Std.LawfulBigOp f unit eq] {a b c : PROP}, eq b c → eq a c := fun h =>
  (@h Prop And True Iff andBO True False False Iff.rfl).mp trivial

-- `Iris.Std.LawfulBigOp.trans` idx 9: necessary (at PROP : Type; Prop, And/True/Iff; a = b = True, c = False)
theorem w9c1_41 : ¬ ∀ {PROP : Type} (f : PROP → PROP → PROP) {unit : PROP} {eq : PROP → PROP → Prop}
    [Iris.Std.LawfulBigOp f unit eq] {a b c : PROP}, eq a b → eq a c := fun h =>
  (@h Prop And True Iff andBO True True False Iff.rfl).mp trivial

-- `Iris.Std.LawfulBigOp.congr_l` idx 8: necessary (at PROP : Type; Prop, And/True/Iff; a = b = True, a' = False)
theorem w9c1_42 : ¬ ∀ {PROP : Type} {f : PROP → PROP → PROP} {unit : PROP} {eq : PROP → PROP → Prop}
    [Iris.Std.LawfulBigOp f unit eq] {a a' b : PROP}, eq (f a b) (f a' b) := fun h =>
  ((@h Prop And True Iff andBO True False True).mp ⟨trivial, trivial⟩).1

-- `Iris.Std.LawfulBigOp.congr_r` idx 8: necessary (at PROP : Type; Prop, And/True/Iff; a = b = True, b' = False)
theorem w9c1_43 : ¬ ∀ {PROP : Type} {f : PROP → PROP → PROP} {unit : PROP} {eq : PROP → PROP → Prop}
    {b b' a : PROP} [Iris.Std.LawfulBigOp f unit eq], eq (f a b) (f a b') := fun h =>
  ((@h Prop And True Iff True False True andBO).mp ⟨trivial, trivial⟩).2

-- `node_wf_l` idx 3: necessary (l = node true (leaf true) (leaf true) is not well-formed)
theorem w9c1_44 : ¬ drop0% node_wf_l 3 := fun h =>
  absurd (@h false badT (.leaf false)) (by decide)

-- `node_wf_r` idx 3: necessary (r = node true (leaf true) (leaf true) is not well-formed)
theorem w9c1_45 : ¬ drop0% node_wf_r 3 := fun h =>
  absurd (@h false (.leaf false) badT) (by decide)

-- `node'_wf` idx 3: necessary (b = false, l not well-formed, r = leaf false)
theorem w9c1_46 : ¬ drop0% node'_wf 3 := fun h =>
  absurd (@h false badT (.leaf false) rfl) (by decide)

-- `node'_wf` idx 4: necessary (b = false, l = leaf false, r not well-formed)
theorem w9c1_47 : ¬ drop0% node'_wf 4 := fun h =>
  absurd (@h false (.leaf false) badT rfl) (by decide)

-- `coPsetUnion_wf` idx 2: necessary (t1 not well-formed, t2 = leaf false)
theorem w9c1_48 : ¬ drop0% coPsetUnion_wf 2 := fun h =>
  absurd (h badT (.leaf false) rfl) (by decide)

-- `coPsetUnion_wf` idx 3: necessary (t1 = leaf false, t2 not well-formed)
theorem w9c1_49 : ¬ drop0% coPsetUnion_wf 3 := fun h =>
  absurd (h (.leaf false) badT rfl) (by decide)

-- `coPsetIntersection_wf` idx 2: necessary (t1 not well-formed, t2 = leaf true)
theorem w9c1_50 : ¬ drop0% coPsetIntersection_wf 2 := fun h =>
  absurd (h badT (.leaf true) rfl) (by decide)

-- `coPsetIntersection_wf` idx 3: necessary (t1 = leaf true, t2 not well-formed)
theorem w9c1_51 : ¬ drop0% coPsetIntersection_wf 3 := fun h =>
  absurd (h (.leaf true) badT rfl) (by decide)

-- `CoPset.coPsetLeaf_wf` idx 2: necessary (t = node true (leaf true) (leaf true), b = true)
theorem w9c1_52 : ¬ drop0% CoPset.coPsetLeaf_wf 2 := fun h =>
  absurd (@h badT true fun p => (badT_all p).trans (by cases p <;> rfl)) (by decide)

-- `CoPset.coPsetLeaf_wf` idx 3: necessary (t = leaf false, b = true)
theorem w9c1_53 : ¬ drop0% CoPset.coPsetLeaf_wf 3 := fun h =>
  absurd (@h (.leaf false) true rfl) (by decide)

-- `CoPset.coPsetRaw_eq` idx 2: necessary (t1 = leaf true, t2 = leaf false)
theorem w9c1_54 : ¬ drop0% CoPset.coPsetRaw_eq 2 := fun h =>
  absurd (@h (.leaf true) (.leaf false) rfl rfl) (by decide)

-- `CoPset.coPsetRaw_eq` idx 3: necessary (t1 = node true (leaf true) (leaf true), t2 = leaf true)
theorem w9c1_55 : ¬ drop0% CoPset.coPsetRaw_eq 3 := fun h =>
  absurd (@h badT (.leaf true) badT_all rfl) (by decide)

-- `CoPset.coPsetRaw_eq` idx 4: necessary (t1 = leaf true, t2 = node true (leaf true) (leaf true))
theorem w9c1_56 : ¬ drop0% CoPset.coPsetRaw_eq 4 := fun h =>
  absurd (@h (.leaf true) badT (fun p => (badT_all p).symm) rfl) (by decide)

-- `CoPset.ext` idx 2: necessary (X = ⊤, Y = ∅)
theorem w9c1_57 : ¬ drop0% CoPset.ext 2 := fun h => CoPset.top_ne_empty (h)

-- `CoPset.subseteq_trans` idx 3: necessary (X = ⊤, Y = Z = ∅)
theorem w9c1_58 : ¬ drop0% CoPset.subseteq_trans 3 := fun h =>
  CoPset.mem_empty (@h ⊤ ∅ ∅ CoPset.subseteq_refl Pos.P1 CoPset.mem_full)

-- `CoPset.subseteq_trans` idx 4: necessary (X = Y = ⊤, Z = ∅)
theorem w9c1_59 : ¬ drop0% CoPset.subseteq_trans 4 := fun h =>
  CoPset.mem_empty (@h ⊤ ⊤ ∅ CoPset.subseteq_refl Pos.P1 CoPset.mem_full)

-- `CoPset.CoPsetRaw.pickRaw_elem_of` idx 2: necessary (t = leaf false)
theorem w9c1_60 : ¬ drop0% CoPset.CoPsetRaw.pickRaw_elem_of 2 := fun h =>
  absurd (h (.leaf false) Pos.P1) (by decide)

-- `CoPset.CoPsetRaw.pickRaw_none` idx 2: necessary (t = leaf true)
theorem w9c1_61 : ¬ drop0% CoPset.CoPsetRaw.pickRaw_none 2 := fun h =>
  h (.leaf true) Pos.P1 rfl

-- `CoPset.mem_pick` idx 1: necessary (X = ∅)
theorem w9c1_62 : ¬ drop0% CoPset.mem_pick 1 := fun h => CoPset.mem_empty (h ∅)

-- `CoPset.elemOf_rightRaw_imp` idx 2: necessary (t = leaf false)
theorem w9c1_63 : ¬ drop0% CoPset.elemOf_rightRaw_imp 2 := fun h =>
  absurd (h (.leaf false) Pos.P1) (by decide)

-- `CoPset.elemOf_leftRaw_or_rightRaw` idx 2: necessary (t = leaf false)
theorem w9c1_64 : ¬ drop0% CoPset.elemOf_leftRaw_or_rightRaw 2 := fun h => by
  rcases h (.leaf false) Pos.P1 with h1 | h1 <;> exact absurd h1 (by decide)

-- `splitLeft_infinite` idx 1: necessary (X = ∅)
theorem w9c1_65 : ¬ drop0% splitLeft_infinite 1 := fun h => cnotinf (by decide) (@h ∅)

-- `splitRight_infinite` idx 1: necessary (X = ∅)
theorem w9c1_66 : ¬ drop0% splitRight_infinite 1 := fun h => cnotinf (by decide) (@h ∅)

-- `split_infinite` idx 1: necessary (X = ∅: an infinite part of ∅ is impossible)
theorem w9c1_67 : ¬ drop0% split_infinite 1 := fun h => by
  obtain ⟨E1, E2, hu, -, hi, -⟩ := h ∅
  obtain ⟨x, hx, -⟩ := hi []
  have : x ∈ E1 ∪ E2 := CoPset.in_union.mpr (.inl hx)
  rw [hu] at this
  exact CoPset.mem_empty this

-- `FromMathlib.Relation.ReflTransGen.head_induction_on` idx 5: necessary (at α : Type; Bool, r = False, a = false, b = true, motive = True)
theorem w9c1_68 : ¬ ∀ {α : Type} {r : α → α → Prop} {b : α}
    {motive : (a : α) → FromMathlib.Relation.ReflTransGen r a b → Prop} {a : α},
    motive b FromMathlib.Relation.ReflTransGen.refl →
    (∀ {a c : α} (h' : r a c) (h : FromMathlib.Relation.ReflTransGen r c b),
      motive c h → motive a (FromMathlib.Relation.ReflTransGen.head h' h)) →
    FromMathlib.Relation.ReflTransGen r a b := fun h => by
  have H := @h Bool (fun _ _ => False) true (fun _ _ => True) false trivial (fun h' _ _ => h'.elim)
  cases H with
  | tail _ hr => exact hr

-- `FromMathlib.Relation.ReflTransGen.head_induction_on` idx 6: necessary (α = True, r = False, motive = False, h = refl)
theorem w9c1_69 : ¬ drop0% FromMathlib.Relation.ReflTransGen.head_induction_on 6 := fun h =>
  @h True (fun _ _ => False) trivial (fun _ _ => False) trivial .refl (fun h' _ _ => h'.elim)

-- `FromMathlib.Relation.ReflTransGen.head_induction_on` idx 7: necessary (at α : Type; Bool, r x y = (x = false ∧ y = true), motive x _ = (x = true), a = false, b = true)
theorem w9c1_70 : ¬ ∀ {α : Type} {r : α → α → Prop} {b : α}
    {motive : (a : α) → FromMathlib.Relation.ReflTransGen r a b → Prop} {a : α}
    (h : FromMathlib.Relation.ReflTransGen r a b),
    motive b FromMathlib.Relation.ReflTransGen.refl → motive a h := fun h => by
  have H := @h Bool (fun x y => x = false ∧ y = true) true (fun x _ => x = true) false
    (FromMathlib.Relation.ReflTransGen.head ⟨rfl, rfl⟩ .refl) rfl
  exact absurd H (by decide)

-- `FromMathlib.Relation.TransGen.head` idx 5: necessary (at α : Type; Bool, r x y = (x = true), a = false, b = c = true)
theorem w9c1_71 : ¬ ∀ {α : Type} {r : α → α → Prop} {a b c : α},
    Relation.TransGen r b c → Relation.TransGen r a c := fun h => by
  have H := @h Bool (fun x _ => x = true) false true true (.single rfl)
  exact absurd (tg_src H) (by decide)

-- `Iris.Std.LawfulMultiSet.ext` idx 5: necessary (counting multisets over Bool, ∅ ≠ {true})
theorem w9c1_72 : ¬ drop0% Iris.Std.LawfulMultiSet.ext 5 := fun h =>
  absurd (@h BM Bool _ ∅ {true}) (by decide)

-- `Iris.Std.LawfulMultiSet.multiplicity_singleton_ne` idx 5: necessary (counting multisets over Bool, x = y = true)
theorem w9c1_73 : ¬ drop0% Iris.Std.LawfulMultiSet.multiplicity_singleton_ne 5 := fun h =>
  absurd (@h BM Bool _ true true) (by decide)

-- `Iris.Std.disjUnion_left_inj` idx 6: necessary (counting multisets over Bool, X = ∅, Y = ∅, Z = {true})
theorem w9c1_74 : ¬ drop0% Iris.Std.disjUnion_left_inj 6 := fun h =>
  absurd (@h BM Bool _ ∅ ∅ {true}) (by decide)

-- `Iris.Std.eq_empty_of_toList_nil` idx 4: necessary (counting multisets over Bool, X = {true})
theorem w9c1_75 : ¬ drop0% Iris.Std.eq_empty_of_toList_nil 4 := fun h =>
  absurd (@h BM Bool _ {true}) (by decide)

-- `Iris.Std.multiset_ind` idx 4: necessary (motive = const False)
theorem w9c1_76 : ¬ drop0% Iris.Std.multiset_ind 4 := fun h =>
  @h BM Bool _ (fun _ => False) (fun _ _ hf => hf) ∅

-- `Iris.Std.multiset_ind` idx 5: necessary (motive X = (X = ∅), X = {true})
theorem w9c1_77 : ¬ drop0% Iris.Std.multiset_ind 5 := fun h =>
  absurd (@h BM Bool _ (fun X => X = ∅) rfl {true}) (by decide)

-- `Iris.Std.FiniteMultiSet.size_difference` idx 5: necessary (counting multisets over Bool, X = {false}, Y = {true})
theorem w9c1_78 : ¬ drop0% Iris.Std.FiniteMultiSet.size_difference 5 := fun h =>
  absurd (@h BM Bool _ {false} {true}) (by decide)

-- `Iris.Std.FiniteMultiSet.fold_disjUnion` idx 6: necessary (counting multisets over Bool, f = cons, X = {true}, Y = {false})
theorem w9c1_79 : ¬ drop0% Iris.Std.FiniteMultiSet.fold_disjUnion 6 := fun h =>
  absurd (@h BM Bool _ (List Bool) List.cons [] {true} {false}) (by decide)

-- `Iris.Std.FiniteMultiSet.fold_comm_acc` idx 7: necessary (counting multisets over Bool, X = {true}, f x y = 0, g = succ)
theorem w9c1_80 : ¬ drop0% Iris.Std.FiniteMultiSet.fold_comm_acc 7 := fun h =>
  absurd (@h BM Bool _ Nat (fun _ _ => 0) 0 Nat.succ {true}) (by decide)

-- `Iris.Std.ListPerm.ind` idx 2: necessary (motive = const False)
theorem w9c1_81 : ¬ drop0% Iris.Std.ListPerm.ind 2 := fun h =>
  @h Nat (fun _ => False) ∅

-- `Iris.Std.ListPerm.ind₂` idx 2: necessary (motive = const False)
theorem w9c1_82 : ¬ drop0% Iris.Std.ListPerm.ind₂ 2 := fun h =>
  @h Nat (fun _ _ => False) ∅ ∅

end
section
open Iris Iris.Std W9c1

-- `Iris.Std.LawfulSet.ext` idx 5: necessary (Bool sets: ∅ ≠ {true})
theorem w9c1_83 : ¬ drop0% Iris.Std.LawfulSet.ext 5 := fun h =>
  bs_ne (by decide) (@h BS Bool _ bE bT)

-- `Iris.Std.LawfulSet.eq_subset` idx 5: necessary (Bool sets: X = {true}, Y = ∅)
theorem w9c1_84 : ¬ drop0% Iris.Std.LawfulSet.eq_subset 5 := fun h =>
  bs_ne (by decide) (@h BS Bool _ bT bE (bE_sub _))

-- `Iris.Std.LawfulSet.eq_subset` idx 6: necessary (Bool sets: X = ∅, Y = {true})
theorem w9c1_85 : ¬ drop0% Iris.Std.LawfulSet.eq_subset 6 := fun h =>
  bs_ne (by decide) (@h BS Bool _ bE bT (bE_sub _))

-- `Iris.Std.LawfulSet.mem_insert_ne` idx 6: necessary (Bool sets: s = ∅, x = y = true)
theorem w9c1_86 : ¬ drop0% Iris.Std.LawfulSet.mem_insert_ne 6 := fun h =>
  LawfulSet.mem_empty ((@h BS Bool _ bE true true).mp (LawfulSet.mem_insert.mpr (.inl rfl)))

-- `Iris.Std.LawfulSet.insert_idem` idx 5: necessary (Bool sets: s = ∅, x = true)
theorem w9c1_87 : ¬ drop0% Iris.Std.LawfulSet.insert_idem 5 := fun h =>
  bs_ne (by decide) (@h BS Bool _ bE true)

-- `Iris.Std.LawfulSet.mem_insert_of_mem` idx 6: necessary (Bool sets: s = ∅, x = true, y = false)
theorem w9c1_88 : ¬ drop0% Iris.Std.LawfulSet.mem_insert_of_mem 6 := fun h =>
  absurd (@h BS Bool _ bE true false) (by decide)

-- `Iris.Std.LawfulSet.mem_diff_singleton_eq` idx 6: necessary (Bool sets: s = {true}, x = true, y = false)
theorem w9c1_89 : ¬ drop0% Iris.Std.LawfulSet.mem_diff_singleton_eq 6 := fun h =>
  @h BS Bool _ bT true false (by decide)

-- `Iris.Std.LawfulSet.mem_diff_singleton_ne` idx 6: necessary (Bool sets: s = {true}, x = y = true)
theorem w9c1_90 : ¬ drop0% Iris.Std.LawfulSet.mem_diff_singleton_ne 6 := fun h =>
  absurd ((@h BS Bool _ bT true true).mp mT) (by decide)

-- `Iris.Std.LawfulSet.delete_notin` idx 5: necessary (Bool sets: s = {true}, x = true)
theorem w9c1_91 : ¬ drop0% Iris.Std.LawfulSet.delete_notin 5 := fun h =>
  bs_ne (by decide) (@h BS Bool _ bT true)

-- `Iris.Std.LawfulSet.delete_subset_delete` idx 6: necessary (Bool sets: s₁ = {true}, s₂ = ∅, x = false)
theorem w9c1_92 : ¬ drop0% Iris.Std.LawfulSet.delete_subset_delete 6 := fun h =>
  absurd ((@h BS Bool _ bT bE false) true (by decide)) (by decide)

-- `Iris.Std.LawfulSet.insert_subset_subset` idx 6: necessary (Bool sets: s₁ = {true}, s₂ = ∅, x = false)
theorem w9c1_93 : ¬ drop0% Iris.Std.LawfulSet.insert_subset_subset 6 := fun h =>
  absurd ((@h BS Bool _ bT bE false) true (by decide)) (by decide)

-- `Iris.Std.LawfulSet.subset_trans` idx 6: necessary (Bool sets: s₁ = {true}, s₂ = s₃ = ∅)
theorem w9c1_94 : ¬ drop0% Iris.Std.LawfulSet.subset_trans 6 := fun h =>
  absurd ((@h BS Bool _ bT bE bE (bE_sub _)) true mT) (by decide)

-- `Iris.Std.LawfulSet.subset_trans` idx 7: necessary (Bool sets: s₁ = s₂ = {true}, s₃ = ∅)
theorem w9c1_95 : ¬ drop0% Iris.Std.LawfulSet.subset_trans 7 := fun h =>
  absurd ((@h BS Bool _ bT bT bE (fun _ hx => hx)) true mT) (by decide)

-- `Iris.Std.LawfulSet.disjoint_symm` idx 5: necessary (Bool sets: s₁ = s₂ = {true})
theorem w9c1_96 : ¬ drop0% Iris.Std.LawfulSet.disjoint_symm 5 := fun h =>
  (@h BS Bool _ bT bT) true ⟨mT, mT⟩

-- `Iris.Std.LawfulSet.disjoint_subset_left` idx 6: necessary (Bool sets: s₁ = t = {true}, s₂ = ∅)
theorem w9c1_97 : ¬ drop0% Iris.Std.LawfulSet.disjoint_subset_left 6 := fun h =>
  (@h BS Bool _ bT bE bT (fun _ hx => LawfulSet.mem_empty hx.1)) true ⟨mT, mT⟩

-- `Iris.Std.LawfulSet.disjoint_subset_left` idx 7: necessary (Bool sets: s₁ = s₂ = t = {true})
theorem w9c1_98 : ¬ drop0% Iris.Std.LawfulSet.disjoint_subset_left 7 := fun h =>
  (@h BS Bool _ bT bT bT (fun _ hx => hx)) true ⟨mT, mT⟩

-- `Iris.Std.LawfulSet.disjoint_subset_right` idx 6: necessary (Bool sets: s₁ = t = {true}, s₂ = ∅)
theorem w9c1_99 : ¬ drop0% Iris.Std.LawfulSet.disjoint_subset_right 6 := fun h =>
  (@h BS Bool _ bT bE bT (fun _ hx => LawfulSet.mem_empty hx.2)) true ⟨mT, mT⟩

-- `Iris.Std.LawfulSet.disjoint_subset_right` idx 7: necessary (Bool sets: s₁ = s₂ = t = {true})
theorem w9c1_100 : ¬ drop0% Iris.Std.LawfulSet.disjoint_subset_right 7 := fun h =>
  (@h BS Bool _ bT bT bT (fun _ hx => hx)) true ⟨mT, mT⟩

-- `Iris.Std.LawfulSet.diff_subset_diff_right` idx 6: necessary (Bool sets: s = t₁ = {true}, t₂ = ∅)
theorem w9c1_101 : ¬ drop0% Iris.Std.LawfulSet.diff_subset_diff_right 6 := fun h =>
  absurd ((@h BS Bool _ bT bT bE) true (by decide)) (by decide)

-- `Iris.Std.LawfulSet.diff_self_diff_of_subset` idx 5: necessary (Bool sets: s = {true}, u = ∅)
theorem w9c1_102 : ¬ drop0% Iris.Std.LawfulSet.diff_self_diff_of_subset 5 := fun h =>
  bs_ne (by decide) (@h BS Bool _ bT bE)

-- `Iris.Std.LawfulSet.diff_subset_disj` idx 5: necessary (Bool sets: s₁ = s₂ = {true})
theorem w9c1_103 : ¬ drop0% Iris.Std.LawfulSet.diff_subset_disj 5 := fun h =>
  bs_ne (by decide) (@h BS Bool _ bT bT)

-- `Iris.Std.LawfulSet.mem_of_subset` idx 6: necessary (Bool sets: s₁ = {true}, s₂ = ∅, x = true)
theorem w9c1_104 : ¬ drop0% Iris.Std.LawfulSet.mem_of_subset 6 := fun h =>
  LawfulSet.mem_empty (@h BS Bool _ bT bE true mT)

-- `Iris.Std.LawfulSet.mem_of_subset` idx 7: necessary (Bool sets: s₁ = s₂ = ∅, x = true)
theorem w9c1_105 : ¬ drop0% Iris.Std.LawfulSet.mem_of_subset 7 := fun h =>
  LawfulSet.mem_empty (@h BS Bool _ bE bE true (bE_sub _))

-- `Iris.Std.LawfulSet.not_mem_of_not_mem_subset` idx 6: necessary (Bool sets: s₁ = {true}, s₂ = ∅, x = true)
theorem w9c1_106 : ¬ drop0% Iris.Std.LawfulSet.not_mem_of_not_mem_subset 6 := fun h =>
  @h BS Bool _ bT bE true LawfulSet.mem_empty mT

-- `Iris.Std.LawfulSet.not_mem_of_not_mem_subset` idx 7: necessary (Bool sets: s₁ = s₂ = {true}, x = true)
theorem w9c1_107 : ¬ drop0% Iris.Std.LawfulSet.not_mem_of_not_mem_subset 7 := fun h =>
  @h BS Bool _ bT bT true (fun _ hx => hx) mT

-- `Iris.Std.LawfulSet.union_subset_absorption` idx 5: necessary (Bool sets: s₁ = {true}, s₂ = ∅)
theorem w9c1_108 : ¬ drop0% Iris.Std.LawfulSet.union_subset_absorption 5 := fun h =>
  bs_ne (by decide) (@h BS Bool _ bT bE)

-- `_private.Iris.Std.GenSets.0.Iris.Std.LawfulSet.ofListExtend_subset_subset` idx 6: necessary (Bool sets: xs = [], s₁ = {true}, s₂ = ∅)
theorem w9c1_109 : ¬ drop0% _private.Iris.Std.GenSets.«0».Iris.Std.LawfulSet.ofListExtend_subset_subset 6 := fun h =>
  absurd ((h (S := BS) (A := Bool) (s₁ := bT) (s₂ := bE) (xs := [])) true mT) (by decide)

-- `Iris.Std.LawfulSet.intersection_finite_l` idx 5: necessary (CoPset: X = Y = ⊤)
theorem w9c1_110 : ¬ drop0% Iris.Std.LawfulSet.intersection_finite_l 5 := fun h =>
  cinf (by decide) (@h CoPset Pos _ ⊤ ⊤)

-- `Iris.Std.LawfulSet.intersection_finite_r` idx 5: necessary (CoPset: X = Y = ⊤)
theorem w9c1_111 : ¬ drop0% Iris.Std.LawfulSet.intersection_finite_r 5 := fun h =>
  cinf (by decide) (@h CoPset Pos _ ⊤ ⊤)

-- `Iris.Std.LawfulSet.union_finite` idx 5: necessary (CoPset: X = ⊤, Y = ∅)
theorem w9c1_112 : ¬ drop0% Iris.Std.LawfulSet.union_finite 5 := fun h =>
  cinf (by decide) (@h CoPset Pos _ ⊤ ∅ LawfulSet.empty_finite)

-- `Iris.Std.LawfulSet.union_finite` idx 6: necessary (CoPset: X = ∅, Y = ⊤)
theorem w9c1_113 : ¬ drop0% Iris.Std.LawfulSet.union_finite 6 := fun h =>
  cinf (by decide) (@h CoPset Pos _ ∅ ⊤ LawfulSet.empty_finite)

-- `Iris.Std.LawfulSet.difference_finite` idx 5: necessary (CoPset: X = ⊤, Y = ∅)
theorem w9c1_114 : ¬ drop0% Iris.Std.LawfulSet.difference_finite 5 := fun h =>
  cinf (by decide) (@h CoPset Pos _ ⊤ ∅)

-- `Iris.Std.LawfulSet.difference_finite_inv` idx 5: necessary (CoPset: X = Y = ⊤)
theorem w9c1_115 : ¬ drop0% Iris.Std.LawfulSet.difference_finite_inv 5 := fun h =>
  cinf (by decide) (@h CoPset Pos _ ⊤ ⊤ (cfin (by decide)))

-- `Iris.Std.LawfulSet.difference_finite_inv` idx 6: necessary (CoPset: X = ⊤, Y = ∅)
theorem w9c1_116 : ¬ drop0% Iris.Std.LawfulSet.difference_finite_inv 6 := fun h =>
  cinf (by decide) (@h CoPset Pos _ ⊤ ∅ LawfulSet.empty_finite)

-- `Iris.Std.LawfulSet.difference_infinite` idx 5: necessary (CoPset: X = Y = ∅)
theorem w9c1_117 : ¬ drop0% Iris.Std.LawfulSet.difference_infinite 5 := fun h =>
  cnotinf (by decide) (@h CoPset Pos _ ∅ ∅ LawfulSet.empty_finite)

-- `Iris.Std.LawfulSet.difference_infinite` idx 6: necessary (CoPset: X = Y = ⊤)
theorem w9c1_118 : ¬ drop0% Iris.Std.LawfulSet.difference_infinite 6 := fun h =>
  cnotinf (by decide) (@h CoPset Pos _ ⊤ ⊤ top_infinite)

-- `Iris.Std.LawfulSet.setInfinite_mono` idx 5: necessary (CoPset: X = ⊤, Y = ∅)
theorem w9c1_119 : ¬ drop0% Iris.Std.LawfulSet.setInfinite_mono 5 := fun h =>
  cnotinf (by decide) (@h CoPset Pos _ ⊤ ∅ top_infinite)

-- `Iris.Std.LawfulSet.setInfinite_mono` idx 6: necessary (CoPset: X = Y = ∅)
theorem w9c1_120 : ¬ drop0% Iris.Std.LawfulSet.setInfinite_mono 6 := fun h =>
  cnotinf (by decide) (@h CoPset Pos _ ∅ ∅ (fun _ hx => hx))

-- `Iris.Std.LawfulSet.diff_not_finite_finite_ne_empty` idx 5: necessary (CoPset: X = Y = ∅)
theorem w9c1_121 : ¬ drop0% Iris.Std.LawfulSet.diff_not_finite_finite_ne_empty 5 := fun h =>
  @h CoPset Pos _ ∅ ∅ LawfulSet.empty_finite (ceq (by decide))

-- `Iris.Std.LawfulSet.diff_not_finite_finite_ne_empty` idx 6: necessary (CoPset: X = Y = ⊤)
theorem w9c1_122 : ¬ drop0% Iris.Std.LawfulSet.diff_not_finite_finite_ne_empty 6 := fun h =>
  @h CoPset Pos _ ⊤ ⊤ top_infinite (ceq (by decide))

-- `Iris.Std.LawfulSet.disjoint_singleton_setSeq` idx 5: necessary (ExtTreeSet Nat: start = 0, len = 1, x = 0)
theorem w9c1_123 : ¬ drop0% Iris.Std.LawfulSet.disjoint_singleton_setSeq 5 := fun h =>
  (@h TS _ 0 1 0) 0 ⟨LawfulSet.mem_singleton.mpr rfl, LawfulSet.mem_setSeq.mpr (by omega)⟩

-- `Iris.Std.FiniteSet.map_subset` idx 9: necessary (Bool sets, f = id, s₁ = {true}, s₂ = ∅)
theorem w9c1_124 : ¬ drop0% Iris.Std.FiniteSet.map_subset 9 := fun h =>
  absurd ((@h BS Bool _ BS Bool _ id bT bE) true (by decide)) (by decide)

-- `Iris.Std.FiniteSet.ofList_congr` idx 5: necessary (Bool sets: l = [true], l' = [])
theorem w9c1_125 : ¬ drop0% Iris.Std.FiniteSet.ofList_congr 5 := fun h =>
  bs_ne (by decide) (@h BS Bool _ [true] [])

-- `Iris.Std.FiniteSet.set_choose` idx 4: necessary (Bool sets: X = ∅)
theorem w9c1_126 : ¬ drop0% Iris.Std.FiniteSet.set_choose 4 := fun h =>
  let ⟨_, hx⟩ := @h BS Bool _ bE
  LawfulSet.mem_empty hx

-- `Iris.Std.FiniteSet.size_union` idx 5: necessary (Bool sets: X = Y = {true})
theorem w9c1_127 : ¬ drop0% Iris.Std.FiniteSet.size_union 5 := fun h =>
  absurd (@h BS Bool _ bT bT) (by decide)

-- `Iris.Std.FiniteSet.size_ssubset` idx 5: necessary (Bool sets: X = Y = ∅)
theorem w9c1_128 : ¬ drop0% Iris.Std.FiniteSet.size_ssubset 5 := fun h =>
  absurd (@h BS Bool _ bE bE) (by decide)

-- `Iris.Std.FiniteSet.size_insert_not_mem` idx 5: necessary (Bool sets: s = {true}, x = true)
theorem w9c1_129 : ¬ drop0% Iris.Std.FiniteSet.size_insert_not_mem 5 := fun h =>
  absurd (@h BS Bool _ bT true) (by decide)

-- `Iris.Std.FiniteSet.size_insert_mem` idx 5: necessary (Bool sets: s = ∅, x = true)
theorem w9c1_130 : ¬ drop0% Iris.Std.FiniteSet.size_insert_mem 5 := fun h =>
  absurd (@h BS Bool _ bE true) (by decide)

-- `Iris.Std.FiniteSet.size_pos` idx 4: necessary (Bool sets: s = ∅)
theorem w9c1_131 : ¬ drop0% Iris.Std.FiniteSet.size_pos 4 := fun h =>
  absurd (@h BS Bool _ bE) (by decide)

-- `Iris.Std.FiniteSet.size_subset` idx 5: necessary (Bool sets: s₁ = {true}, s₂ = ∅)
theorem w9c1_132 : ¬ drop0% Iris.Std.FiniteSet.size_subset 5 := fun h =>
  absurd (@h BS Bool _ bT bE) (by decide)

-- `Iris.Std.FiniteSet.set_ind` idx 4: necessary (P = const False)
theorem w9c1_133 : ¬ drop0% Iris.Std.FiniteSet.set_ind 4 := fun h =>
  @h BS Bool _ (fun _ => False) (fun _ _ _ hf => hf) bE

-- `Iris.Std.FiniteSet.set_ind` idx 5: necessary (Bool sets: P X = (X true = false), X = {true})
theorem w9c1_134 : ¬ drop0% Iris.Std.FiniteSet.set_ind 5 := fun h =>
  absurd (@h BS Bool _ (fun X => X true = false) rfl bT) (by decide)

-- `_private.Iris.Std.GenSets.0.Iris.Std.FiniteSet.foldl_perm` idx 3: necessary (f = flipped cons, [0, 1] ~ [1, 0], init = [])
theorem w9c1_135 : ¬ drop0% _private.Iris.Std.GenSets.«0».Iris.Std.FiniteSet.foldl_perm 3 := fun h =>
  absurd (h (A := Nat) (β := List Nat) (f := fun b x => x :: b) (l₁ := [0, 1]) (l₂ := [1, 0])
    (List.Perm.swap 1 0 []) []) (by decide)

-- `Iris.Std.FiniteSet.toList_union_perm` idx 5: necessary (Bool sets: s = t = {true})
theorem w9c1_136 : ¬ drop0% Iris.Std.FiniteSet.toList_union_perm 5 := fun h =>
  absurd (@h BS Bool _ bT bT).length_eq (by decide)

-- `Iris.Std.FiniteSet.fold_insert` idx 9: necessary (Bool sets: s = {true}, a = true, f b _ = b + 1, init = 0)
theorem w9c1_137 : ¬ drop0% Iris.Std.FiniteSet.fold_insert 9 := fun h =>
  absurd (@h BS Bool _ Nat (fun b _ => b + 1) (fun _ _ _ => rfl) 0 true bT) (by decide)

-- `Iris.Std.FiniteSet.fold_union` idx 5: necessary (Bool sets, toList lists false first: s = {true}, t = {false}, f = flipped cons)
theorem w9c1_138 : ¬ drop0% Iris.Std.FiniteSet.fold_union 5 := fun h =>
  absurd (@h BS Bool _ (List Bool) (fun b x => x :: b) [] bT bF
    (fun x hx => by cases x <;> exact absurd hx (by decide))) (by decide)

-- `Iris.Std.FiniteSet.fold_union` idx 9: necessary (Bool sets: s = t = {true}, f b _ = b + 1, init = 0)
theorem w9c1_139 : ¬ drop0% Iris.Std.FiniteSet.fold_union 9 := fun h =>
  absurd (@h BS Bool _ Nat (fun b _ => b + 1) (fun _ _ _ => rfl) 0 bT bT) (by decide)

end
