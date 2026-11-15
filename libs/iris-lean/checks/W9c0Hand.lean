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

namespace W9c0
open Iris Iris.BI Iris.ProofMode

/-! GB copied from W4c4 (via W8c1): predicates on Bool with sep over xor, emp = {false},
persistently P := constant P false, later = id. Non-affine, non-positive. -/
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

/-- copied from W5c2 -/
instance gbPE : BIPersistentlyExist GB := ⟨fun _ _ ⟨p, hp, h⟩ => ⟨_, ⟨p, rfl⟩, hp, h⟩⟩

/-- emp ⊣⊢ emp ∗ emp in GB -/
theorem gEE : (iprop(emp) : GB) ⊣⊢ iprop(emp ∗ emp) := ⟨sep_emp.2, sep_emp.1⟩
/-- emp ⊢ emp ∗ □ True in GB -/
theorem gEB : (iprop(emp) : GB) ⊢ iprop(emp ∗ □ True) := fun x hx =>
  ⟨false, false, by subst hx; rfl, rfl, rfl, trivial⟩
/-- emp ⊣⊢ emp ∗ □ True in GB -/
theorem gEBe : (iprop(emp) : GB) ⊣⊢ iprop(emp ∗ □ True) :=
  ⟨gEB, fun x ⟨a, b, e, ha, hb⟩ => by
    have ha : a = false := ha
    have hb : b = false := hb.1
    subst ha hb e; rfl⟩
/-- emp ∗ (True -∗ emp) fails at false -/
theorem gEW : ¬ (iprop(emp ∗ (True -∗ emp)) : GB) false := fun ⟨a, b, e, ha, hb⟩ => by
  have ha : a = false := ha
  have h1 : xor b true = false := hb true trivial
  subst ha; cases b
  · exact absurd h1 (by decide)
  · exact absurd e (by decide)

end W9c0

open Iris Iris.BI Iris.ProofMode Iris.Std W9c0

-- `Iris.ProofMode.apply` idx 7: necessary (GB, P = Q = True, Q1 = R = False)
theorem w9c0_1 : ¬ drop0% Iris.ProofMode.apply 7 := fun h =>
  (@h GB gbBI false iprop(True) iprop(True) iprop(False) iprop(False) ⟨fun _ _ _ hy => hy⟩) false
    ⟨false, false, rfl, trivial, trivial⟩

-- `Iris.ProofMode.apply` idx 8: necessary (GB, P = Q = Q1 = True, R = False)
theorem w9c0_2 : ¬ drop0% Iris.ProofMode.apply 8 := fun h =>
  (@h GB gbBI false iprop(True) iprop(True) iprop(True) iprop(False) .rfl) false
    ⟨false, false, rfl, trivial, trivial⟩

-- `Iris.ProofMode.apply_assumption` idx 6: necessary (GB, P = emp, A = True, Q = False)
theorem w9c0_3 : ¬ drop0% Iris.ProofMode.apply_assumption 6 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(True) iprop(False) (TCOr.l (t := inferInstance))) false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.assumption` idx 7: necessary (GB, P = P' = A = emp, Q = False)
theorem w9c0_4 : ¬ drop0% Iris.ProofMode.assumption 7 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(emp) iprop(emp) iprop(False) (TCOr.l (t := inferInstance)) gEE)
    false rfl

-- `Iris.ProofMode.assumption` idx 9: necessary (GB, P = True, P' = emp, A = Q = False)
theorem w9c0_5 : ¬ drop0% Iris.ProofMode.assumption 9 := fun h =>
  (@h GB gbBI false iprop(True) iprop(emp) iprop(False) iprop(False) ⟨fun _ h => h⟩
    (TCOr.l (t := inferInstance))) false trivial

-- `Iris.ProofMode.exists_elim'` idx 9: necessary (GB, alpha = True, Phi = False, A = True, Q = False)
theorem w9c0_7 : ¬ drop0% Iris.ProofMode.exists_elim' 9 := fun h =>
  (@h GB True gbBI gbPE false iprop(emp) iprop(True) iprop(False) (fun _ => iprop(False))
    (fun _ _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.exists_elim'` idx 10: necessary (GB, alpha = True, Phi = True, A = True, Q = False)
theorem w9c0_8 : ¬ drop0% Iris.ProofMode.exists_elim' 10 := fun h =>
  (@h GB True gbBI gbPE false iprop(emp) iprop(True) iprop(False) (fun _ => iprop(True))
    ⟨fun _ _ => ⟨_, ⟨trivial, rfl⟩, trivial⟩⟩) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.exists_elim_spatial'` idx 8: necessary (GB, alpha = True, Phi = False, A = True, Q = False)
theorem w9c0_9 : ¬ drop0% Iris.ProofMode.exists_elim_spatial' 8 := fun h =>
  (@h GB True gbBI false iprop(emp) iprop(True) iprop(False) (fun _ => iprop(False))
    (fun _ _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.exists_elim_spatial'` idx 9: necessary (GB, alpha = True, Phi = True, A = True, Q = False)
theorem w9c0_10 : ¬ drop0% Iris.ProofMode.exists_elim_spatial' 9 := fun h =>
  (@h GB True gbBI false iprop(emp) iprop(True) iprop(False) (fun _ => iprop(True))
    ⟨fun _ _ => ⟨_, ⟨trivial, rfl⟩, trivial⟩⟩) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.sep_and_elim_left` idx 8: necessary (GB, P = emp, A = True, A1 = Q = False)
theorem w9c0_11 : ¬ drop0% Iris.ProofMode.sep_and_elim_left 8 := fun h =>
  (@h GB false gbBI iprop(emp) iprop(True) iprop(False) iprop(False) iprop(True)
    (fun _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.sep_and_elim_left` idx 9: necessary (GB, P = emp, A = A1 = A2 = True, Q = False)
theorem w9c0_12 : ¬ drop0% Iris.ProofMode.sep_and_elim_left 9 := fun h =>
  (@h GB false gbBI iprop(emp) iprop(True) iprop(False) iprop(True) iprop(True)
    ⟨fun _ _ => ⟨trivial, trivial⟩⟩) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.sep_and_elim_right` idx 8: necessary (GB, P = emp, A = True, A2 = Q = False)
theorem w9c0_13 : ¬ drop0% Iris.ProofMode.sep_and_elim_right 8 := fun h =>
  (@h GB false gbBI iprop(emp) iprop(True) iprop(False) iprop(True) iprop(False)
    (fun _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.sep_and_elim_right` idx 9: necessary (GB, P = emp, A = A1 = A2 = True, Q = False)
theorem w9c0_14 : ¬ drop0% Iris.ProofMode.sep_and_elim_right 9 := fun h =>
  (@h GB false gbBI iprop(emp) iprop(True) iprop(False) iprop(True) iprop(True)
    ⟨fun _ _ => ⟨trivial, trivial⟩⟩) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.sep_elim_spatial` idx 7: necessary (GB, P = emp, A = True, A1 = Q = False)
theorem w9c0_15 : ¬ drop0% Iris.ProofMode.sep_elim_spatial 7 := fun h =>
  (@h GB gbBI iprop(emp) iprop(True) iprop(False) iprop(False) iprop(True)
    (fun _ ⟨_, _, _, _, hb⟩ => hb.elim)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.sep_elim_spatial` idx 8: necessary (GB, P = A = A1 = A2 = emp, Q = False)
theorem w9c0_16 : ¬ drop0% Iris.ProofMode.sep_elim_spatial 8 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(False) iprop(emp) iprop(emp) ⟨sep_emp.2⟩) false
    ⟨false, false, rfl, rfl, rfl⟩

-- `Iris.ProofMode.and_elim_intuitionistic` idx 7: necessary (GB, P = emp, A = True, A1 = Q = False)
theorem w9c0_17 : ¬ drop0% Iris.ProofMode.and_elim_intuitionistic 7 := fun h =>
  (@h GB gbBI iprop(emp) iprop(True) iprop(False) iprop(False) iprop(True)
    (fun _ ⟨_, _, _, _, hb⟩ => hb.2.elim)) false ⟨false, false, rfl, rfl, rfl, trivial⟩

-- `Iris.ProofMode.and_elim_intuitionistic` idx 8: necessary (GB, P = emp, A = A1 = A2 = True, Q = False)
theorem w9c0_18 : ¬ drop0% Iris.ProofMode.and_elim_intuitionistic 8 := fun h =>
  (@h GB gbBI iprop(emp) iprop(True) iprop(False) iprop(True) iprop(True)
    ⟨fun _ h => ⟨h.1, trivial, trivial⟩⟩) false ⟨false, false, rfl, rfl, rfl, trivial⟩

-- `Iris.ProofMode.or_elim'` idx 9: necessary (GB, P = emp, A = True, A1 = A2 = Q = False)
theorem w9c0_20 : ¬ drop0% Iris.ProofMode.or_elim' 9 := fun h =>
  (@h GB gbBI gbPE false iprop(emp) iprop(True) iprop(False) iprop(False) iprop(False)
    (fun _ ⟨_, _, _, _, hb⟩ => hb) (fun _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.or_elim'` idx 10: necessary (GB, P = emp, A = A1 = True, A2 = Q = False)
theorem w9c0_21 : ¬ drop0% Iris.ProofMode.or_elim' 10 := fun h =>
  (@h GB gbBI gbPE false iprop(emp) iprop(True) iprop(False) iprop(True) iprop(False)
    ⟨fun _ _ => .inl trivial⟩ (fun _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.or_elim'` idx 11: necessary (GB, P = emp, A = A2 = True, A1 = Q = False)
theorem w9c0_22 : ¬ drop0% Iris.ProofMode.or_elim' 11 := fun h =>
  (@h GB gbBI gbPE false iprop(emp) iprop(True) iprop(False) iprop(False) iprop(True)
    ⟨fun _ _ => .inr trivial⟩ (fun _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.or_elim_spatial'` idx 8: necessary (GB, P = emp, A = True, A1 = A2 = Q = False)
theorem w9c0_23 : ¬ drop0% Iris.ProofMode.or_elim_spatial' 8 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(True) iprop(False) iprop(False) iprop(False)
    (fun _ ⟨_, _, _, _, hb⟩ => hb) (fun _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.or_elim_spatial'` idx 9: necessary (GB, P = emp, A = A1 = True, A2 = Q = False)
theorem w9c0_24 : ¬ drop0% Iris.ProofMode.or_elim_spatial' 9 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(True) iprop(False) iprop(True) iprop(False)
    ⟨fun _ _ => .inl trivial⟩ (fun _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.or_elim_spatial'` idx 10: necessary (GB, P = emp, A = A2 = True, A1 = Q = False)
theorem w9c0_25 : ¬ drop0% Iris.ProofMode.or_elim_spatial' 10 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(True) iprop(False) iprop(False) iprop(True)
    ⟨fun _ _ => .inr trivial⟩ (fun _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.intuitionistic_elim_spatial` idx 6: necessary (GB, A = P = emp, A' = Q = False)
theorem w9c0_26 : ¬ drop0% Iris.ProofMode.intuitionistic_elim_spatial 6 := fun h =>
  (@h GB gbBI iprop(emp) iprop(False) iprop(emp) iprop(False) (TCOr.l (t := inferInstance))
    (fun _ ⟨_, _, _, _, hb⟩ => hb.2)) false ⟨false, false, rfl, rfl, rfl⟩

-- `Iris.ProofMode.intuitionistic_elim_spatial` idx 8: necessary (GB, A = A' = P = emp, Q = False)
theorem w9c0_27 : ¬ drop0% Iris.ProofMode.intuitionistic_elim_spatial 8 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(emp) iprop(False) ⟨fun _ _ => rfl⟩
    (TCOr.l (t := inferInstance))) false ⟨false, false, rfl, rfl, rfl⟩

-- `Iris.ProofMode.intuitionistic_elim_intuitionistic` idx 6: necessary (GB, P = emp, A = True, A' = Q = False)
theorem w9c0_28 : ¬ drop0% Iris.ProofMode.intuitionistic_elim_intuitionistic 6 := fun h =>
  (@h GB iprop(emp) gbBI iprop(True) iprop(False) iprop(False)
    (fun _ ⟨_, _, _, _, hb⟩ => hb.2)) false ⟨false, false, rfl, rfl, rfl, trivial⟩

-- `Iris.ProofMode.intuitionistic_elim_intuitionistic` idx 7: necessary (GB, P = emp, A = A' = True, Q = False)
theorem w9c0_29 : ¬ drop0% Iris.ProofMode.intuitionistic_elim_intuitionistic 7 := fun h =>
  (@h GB iprop(emp) gbBI iprop(True) iprop(True) iprop(False) ⟨fun _ h => h⟩) false
    ⟨false, false, rfl, rfl, rfl, trivial⟩

-- `Iris.ProofMode.spatial_elim` idx 7: necessary (GB, P = emp, A = True, A' = Q = False)
theorem w9c0_30 : ¬ drop0% Iris.ProofMode.spatial_elim 7 := fun h =>
  (@h GB iprop(emp) gbBI false iprop(True) iprop(False) iprop(False)
    (fun _ ⟨_, _, _, _, hb⟩ => hb)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.spatial_elim` idx 8: necessary (GB, P = emp, A = A' = True, Q = False)
theorem w9c0_31 : ¬ drop0% Iris.ProofMode.spatial_elim 8 := fun h =>
  (@h GB iprop(emp) gbBI false iprop(True) iprop(True) iprop(False) ⟨fun _ h => h⟩) false
    ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.of_emp_sep` idx 4: necessary (GB, A = True, Q = False)
theorem w9c0_32 : ¬ drop0% Iris.ProofMode.of_emp_sep 4 := fun h =>
  (@h GB gbBI iprop(True) iprop(False)) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.clear_spatial` idx 7: necessary (GB, P = True, P' = Q = False, A = emp)
theorem w9c0_33 : ¬ drop0% Iris.ProofMode.clear_spatial 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(emp) iprop(False) (TCOr.l (t := inferInstance)) .rfl)
    false trivial

-- `Iris.ProofMode.clear_spatial` idx 8: necessary (GB, P = P' = A = emp, Q = False)
theorem w9c0_34 : ¬ drop0% Iris.ProofMode.clear_spatial 8 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(emp) iprop(False) (TCOr.l (t := inferInstance)) gEE)
    false rfl

-- `Iris.ProofMode.clear_intuitionistic` idx 6: necessary (GB, P = True, P' = Q = False)
theorem w9c0_35 : ¬ drop0% Iris.ProofMode.clear_intuitionistic 6 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(emp) iprop(False) .rfl) false trivial

-- `Iris.ProofMode.clear_intuitionistic` idx 7: necessary (GB, P = P' = emp, A = True, Q = False)
theorem w9c0_36 : ¬ drop0% Iris.ProofMode.clear_intuitionistic 7 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(True) iprop(False) gEBe) false rfl

-- `Iris.ProofMode.combine_as_step` idx 10: necessary (GB, all emp, p1 = p2 = false, out = False)
theorem w9c0_37 : ¬ drop0% Iris.ProofMode.combine_as_step 10 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(emp) iprop(emp) iprop(emp) iprop(emp)
    iprop(False) sep_emp.2 sep_emp.2) false rfl
  hb

-- `Iris.ProofMode.combine_as_step` idx 11: necessary (GB, e = True, e1 = out1 = out2 = out = False)
theorem w9c0_38 : ¬ drop0% Iris.ProofMode.combine_as_step 11 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(True) iprop(False) iprop(emp) iprop(False)
    iprop(False) iprop(False) ⟨fun _ ⟨_, _, _, ha, _⟩ => ha⟩ false_elim) false trivial
  hb

-- `Iris.ProofMode.combine_as_step` idx 12: necessary (GB, e = e1 = e2 = out1 = emp, out2 = out = False)
theorem w9c0_39 : ¬ drop0% Iris.ProofMode.combine_as_step 12 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(emp) iprop(emp) iprop(emp)
    iprop(False) iprop(False) ⟨fun _ ⟨_, _, _, ha, _⟩ => ha⟩ sep_emp.2) false rfl
  hb

-- `Iris.ProofMode.combine_gives_step` idx 10: necessary (GB, all emp, out = False)
theorem w9c0_40 : ¬ drop0% Iris.ProofMode.combine_gives_step 10 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(emp) iprop(emp) iprop(emp) iprop(emp)
    iprop(False) gEE gEE) false rfl
  hb.2

-- `Iris.ProofMode.combine_gives_step` idx 11: necessary (GB, e = e2 = out1 = emp, e1 = out2 = out = False)
theorem w9c0_41 : ¬ drop0% Iris.ProofMode.combine_gives_step 11 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(False) iprop(emp) iprop(emp)
    iprop(False) iprop(False) ⟨fun _ ⟨_, _, _, ha, _⟩ => ha⟩
    ⟨false_elim, fun _ ⟨_, _, _, _, hb⟩ => hb⟩) false rfl
  hb.2

-- `Iris.ProofMode.combine_gives_step` idx 12: necessary (GB, e = e1 = out1 = emp, out2 = out = False)
theorem w9c0_42 : ¬ drop0% Iris.ProofMode.combine_gives_step 12 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(emp) iprop(emp) iprop(emp)
    iprop(False) iprop(False) ⟨fun _ ⟨_, _, _, ha, _⟩ => ha⟩ gEE) false rfl
  hb.2

-- `Iris.ProofMode.combine_gives_step_conj` idx 12: necessary (GB, e's and outs emp, outGives = True, newOutGives = combined = False)
theorem w9c0_43 : ¬ drop0% Iris.ProofMode.combine_gives_step_conj 12 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(emp) iprop(emp) iprop(True)
    iprop(False) iprop(False) iprop(emp) iprop(emp) ⟨fun _ h => h.2, fun _ h => h.elim⟩
    gEB sep_emp.2 gEE) false rfl
  hb.2

-- `Iris.ProofMode.combine_gives_step_conj` idx 13: necessary (GB, outGives = newOutGives = True, combined = False)
theorem w9c0_44 : ¬ drop0% Iris.ProofMode.combine_gives_step_conj 13 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(emp) iprop(emp) iprop(True)
    iprop(True) iprop(False) iprop(emp) iprop(emp) ⟨fun _ _ => trivial⟩
    gEB sep_emp.2 gEE) false rfl
  hb.2

-- `Iris.ProofMode.combine_gives_step_conj` idx 14: necessary (GB, outGives = combined = False, newOutGives = True)
theorem w9c0_45 : ¬ drop0% Iris.ProofMode.combine_gives_step_conj 14 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(emp) iprop(emp) iprop(False)
    iprop(True) iprop(False) iprop(emp) iprop(emp) ⟨fun _ _ => trivial⟩
    ⟨fun _ h => h.1, fun _ h => h.elim⟩ sep_emp.2 gEE) false rfl
  hb.2

-- `Iris.ProofMode.combine_gives_step_conj` idx 15: necessary (GB, out1 = False, outGives = True, newOutGives = combined = False)
theorem w9c0_46 : ¬ drop0% Iris.ProofMode.combine_gives_step_conj 15 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(emp) iprop(emp) iprop(True)
    iprop(False) iprop(False) iprop(False) iprop(emp) ⟨fun _ ⟨_, _, _, _, hb⟩ => hb⟩
    ⟨fun _ h => h.2, fun _ h => h.elim⟩ gEB gEE) false rfl
  hb.2

-- `Iris.ProofMode.combine_gives_step_conj` idx 16: necessary (GB, out2 = False, outGives = True, newOutGives = combined = False)
theorem w9c0_47 : ¬ drop0% Iris.ProofMode.combine_gives_step_conj 16 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false false iprop(emp) iprop(emp) iprop(emp) iprop(True)
    iprop(False) iprop(False) iprop(emp) iprop(False) ⟨fun _ ⟨_, _, _, ha, _⟩ => ha⟩
    ⟨fun _ h => h.2, fun _ h => h.elim⟩ gEB sep_emp.2) false rfl
  hb.2

-- `Iris.ProofMode.combine_as_gives` idx 8: necessary (GB, e = outAs = emp, outGives = True, newE = goal = False)
theorem w9c0_48 : ¬ drop0% Iris.ProofMode.combine_as_gives 8 := fun h =>
  (@h GB gbBI false iprop(False) iprop(emp) iprop(emp) iprop(True) iprop(False) gEB
    (fun _ ⟨_, _, _, ha, _⟩ => ha)) false rfl

-- `Iris.ProofMode.combine_as_gives` idx 9: necessary (GB, e = newE = outAs = emp, outGives = goal = False)
theorem w9c0_49 : ¬ drop0% Iris.ProofMode.combine_as_gives 9 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(emp) iprop(emp) iprop(False) iprop(False) sep_emp.2
    (fun _ ⟨_, _, _, _, _, _, _, _, hc⟩ => hc.2)) false rfl

-- `Iris.ProofMode.combine_as_gives` idx 10: necessary (GB, e = newE = outAs = emp, outGives = True, goal = False)
theorem w9c0_50 : ¬ drop0% Iris.ProofMode.combine_as_gives 10 := fun h =>
  (@h GB gbBI false iprop(emp) iprop(emp) iprop(emp) iprop(True) iprop(False) sep_emp.2 gEB) false rfl

-- `Iris.ProofMode.hyps_replace_ieval` idx 5: necessary (GB, P = R = True, Q = False)
theorem w9c0_51 : ¬ drop0% Iris.ProofMode.hyps_replace_ieval 5 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(True)) false trivial false trivial

-- `Iris.ProofMode.exfalso` idx 4: necessary (GB, P = True, Q = False)
theorem w9c0_52 : ¬ drop0% Iris.ProofMode.exfalso 4 := fun h =>
  (@h GB gbBI iprop(True) iprop(False)) false trivial

-- `Iris.ProofMode.from_exists_intro` idx 6: necessary (GB, alpha = True, Phi = True, P = Q = False)
theorem w9c0_53 : ¬ drop0% Iris.ProofMode.from_exists_intro 6 := fun h =>
  (@h GB True gbBI (fun _ => iprop(True)) iprop(False) iprop(False) trivial .rfl) false trivial

-- `Iris.ProofMode.from_exists_intro` idx 8: necessary (GB, alpha = True, Phi = P = True, Q = False)
theorem w9c0_54 : ¬ drop0% Iris.ProofMode.from_exists_intro 8 := fun h =>
  (@h GB True gbBI (fun _ => iprop(True)) iprop(True) iprop(False) ⟨fun _ _ => trivial⟩ trivial)
    false trivial

-- `Iris.ProofMode.frame_hyp` idx 10: necessary (GB, origE = True, origGoal = False, rest emp)
theorem w9c0_55 : ¬ drop0% Iris.ProofMode.frame_hyp 10 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI false iprop(emp) iprop(emp) iprop(True) iprop(emp) iprop(emp)
    iprop(False) iprop(emp) ⟨sep_emp.1⟩ gEE) false trivial
  hb false rfl

-- `Iris.ProofMode.frame_hyp` idx 11: necessary (GB, all emp, goal' = True: emp ∗ (True -∗ emp) fails)
theorem w9c0_56 : ¬ drop0% Iris.ProofMode.frame_hyp 11 := fun h =>
  gEW ((@h GB gbBI false iprop(emp) iprop(emp) iprop(emp) iprop(emp) iprop(True) iprop(emp)
    iprop(emp) frame_init gEE) false rfl)

-- `Iris.ProofMode.frame_hyp` idx 12: necessary (GB, origE = e = goal = goal' = origGoal = R = emp, e' = False)
theorem w9c0_57 : ¬ drop0% Iris.ProofMode.frame_hyp 12 := fun h =>
  let ⟨_, _, _, ha, _⟩ := (@h GB gbBI false iprop(emp) iprop(False) iprop(emp) iprop(emp) iprop(emp)
    iprop(emp) iprop(emp) frame_init ⟨sep_emp.1⟩) false rfl
  ha

-- `Iris.ProofMode.frame_pure` idx 8: necessary (GB, origE = True, e = False, phi = True)
theorem w9c0_58 : ¬ drop0% Iris.ProofMode.frame_pure 8 := fun h =>
  let ⟨_, _, _, ha, _⟩ := (@h GB gbBI iprop(True) iprop(False) iprop(True) iprop(True) iprop(False)
    True ⟨fun _ _ => trivial⟩ trivial) false trivial
  ha

-- `Iris.ProofMode.frame_pure` idx 9: necessary (GB, all emp, goal' = True, phi = True)
theorem w9c0_59 : ¬ drop0% Iris.ProofMode.frame_pure 9 := fun h =>
  gEW ((@h GB gbBI iprop(emp) iprop(emp) iprop(emp) iprop(True) iprop(emp) True frame_init trivial)
    false rfl)

-- `Iris.ProofMode.frame_finish` idx 6: necessary (GB, e = goal = emp, origE = True, origGoal = False)
theorem w9c0_60 : ¬ drop0% Iris.ProofMode.frame_finish 6 := fun h =>
  (@h GB gbBI iprop(emp) iprop(True) iprop(emp) iprop(False) .rfl) false trivial

-- `Iris.ProofMode.frame_finish` idx 7: necessary (GB, origE = e = True, goal = origGoal = False)
theorem w9c0_61 : ¬ drop0% Iris.ProofMode.frame_finish 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(True) iprop(False) iprop(False) frame_init) false trivial

-- `Iris.ProofMode.frame_finish_close_true` idx 5: necessary (GB, e = origE = True, origGoal = False)
theorem w9c0_62 : ¬ drop0% Iris.ProofMode.frame_finish_close_true 5 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI iprop(True) iprop(True) iprop(False)) false trivial
  hb

-- `Iris.ProofMode.ihave_assert` idx 5: necessary (GB, A = B = True, C = False)
theorem w9c0_63 : ¬ drop0% Iris.ProofMode.ihave_assert 5 := fun h =>
  (@h GB gbBI iprop(True) iprop(True) iprop(False)) false trivial

-- `Iris.ProofMode.have_asEmpValid` idx 5: necessary (GB, phi = True, P = False, Q = emp)
theorem w9c0_64 : ¬ drop0% Iris.ProofMode.have_asEmpValid 5 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI True iprop(False) iprop(emp) trivial) false rfl
  hb.2

-- `Iris.ProofMode.revert_IH` idx 6: necessary (GB, phi = False, P = emp, Q = True, R = False)
theorem w9c0_65 : ¬ drop0% Iris.ProofMode.revert_IH 6 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI iprop(emp) iprop(True) iprop(False) False
    (fun _ hx => ⟨hx, rfl⟩) (fun _ _ => trivial) ⟨fun h => h.elim⟩) false rfl
  hb.2

-- `Iris.ProofMode.revert_IH` idx 7: necessary (GB, phi = True, P = own1, Q = True, R = False)
theorem w9c0_66 : ¬ drop0% Iris.ProofMode.revert_IH 7 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI own1 iprop(True) iprop(False) True trivial
    (fun _ _ => trivial) ⟨fun _ _ hx => Bool.noConfusion (hx.2 : false = true)⟩) true rfl
  hb.2

-- `Iris.ProofMode.revert_IH` idx 8: necessary (GB, phi = True, P = R = emp, Q = False)
theorem w9c0_67 : ¬ drop0% Iris.ProofMode.revert_IH 8 := fun h =>
  let ⟨_, _, _, ha, _⟩ := (@h GB gbBI iprop(emp) iprop(False) iprop(emp) True trivial
    (fun _ hx => ⟨hx, rfl⟩) ⟨fun _ _ hx => hx.1⟩) false rfl
  ha

-- `Iris.ProofMode.revert_IH` idx 9: necessary (GB, phi = True, P = emp, Q = True, R = False)
theorem w9c0_68 : ¬ drop0% Iris.ProofMode.revert_IH 9 := fun h =>
  let ⟨_, _, _, _, hb⟩ := (@h GB gbBI iprop(emp) iprop(True) iprop(False) True trivial
    (fun _ hx => ⟨hx, rfl⟩) (fun _ _ => trivial)) false rfl
  hb.2

-- `Iris.ProofMode.imp_intro_drop` idx 6: necessary (GB, P = A1 = A2 = True, Q = False)
theorem w9c0_69 : ¬ drop0% Iris.ProofMode.imp_intro_drop 6 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(True) iprop(True) .rfl) false trivial

-- `Iris.ProofMode.imp_intro_drop` idx 7: necessary (GB, P = A1 = True, A2 = Q = False)
theorem w9c0_70 : ¬ drop0% Iris.ProofMode.imp_intro_drop 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(True) iprop(False) ⟨fun _ h => h trivial⟩) false trivial

-- `Iris.ProofMode.from_forall_intro` idx 6: necessary (GB, alpha = True, P = Phi = True, Q = False)
theorem w9c0_71 : ¬ drop0% Iris.ProofMode.from_forall_intro 6 := fun h =>
  (@h GB True gbBI iprop(True) iprop(False) (fun _ => iprop(True)) (fun _ => .rfl)) false trivial

-- `Iris.ProofMode.from_forall_intro` idx 7: necessary (GB, alpha = True, P = True, Phi = Q = False)
theorem w9c0_72 : ¬ drop0% Iris.ProofMode.from_forall_intro 7 := fun h =>
  (@h GB True gbBI iprop(True) iprop(False) (fun _ => iprop(False))
    ⟨fun _ h => h _ ⟨trivial, rfl⟩⟩) false trivial

-- `Iris.ProofMode.imp_intro_intuitionistic` idx 7: necessary (GB, P = A2 = True, A1 = B = emp, Q = False)
theorem w9c0_73 : ¬ drop0% Iris.ProofMode.imp_intro_intuitionistic 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(emp) iprop(True) iprop(emp) ⟨fun _ _ => rfl⟩
    (fun _ _ => trivial)) false trivial

-- `Iris.ProofMode.imp_intro_intuitionistic` idx 8: necessary (GB, P = A1 = True, A2 = B = Q = False)
theorem w9c0_74 : ¬ drop0% Iris.ProofMode.imp_intro_intuitionistic 8 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(True) iprop(False) iprop(False) ⟨fun _ h => h trivial⟩
    (fun _ ⟨_, _, _, _, hb⟩ => hb.2)) false trivial

-- `Iris.ProofMode.imp_intro_intuitionistic` idx 9: necessary (GB, P = A1 = B = True, A2 = False, Q = (A1 → A2))
theorem w9c0_75 : ¬ drop0% Iris.ProofMode.imp_intro_intuitionistic 9 := fun h =>
  (@h GB gbBI iprop(True) iprop(True → False) iprop(True) iprop(False) iprop(True) ⟨.rfl⟩
    ⟨fun _ _ => trivial⟩) false trivial trivial

-- `Iris.ProofMode.wand_intro_intuitionistic` idx 7: necessary (GB, P = A2 = True, A1 = B = emp, Q = False)
theorem w9c0_76 : ¬ drop0% Iris.ProofMode.wand_intro_intuitionistic 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(emp) iprop(True) iprop(emp) ⟨fun _ _ => rfl⟩
    (TCOr.l (t := inferInstance)) (fun _ _ => trivial)) false trivial

-- `Iris.ProofMode.wand_intro_intuitionistic` idx 8: necessary (GB, P = A1 = True, A2 = B = False, Q = (A1 -∗ A2))
theorem w9c0_77 : ¬ drop0% Iris.ProofMode.wand_intro_intuitionistic 8 := fun h =>
  (@h GB gbBI iprop(True) iprop(True -∗ False) iprop(True) iprop(False) iprop(False) ⟨.rfl⟩
    (TCOr.r (u := inferInstance)) (fun _ ⟨_, _, _, _, hb⟩ => hb.2)) false trivial false trivial

-- `Iris.ProofMode.wand_intro_intuitionistic` idx 10: necessary (GB, P = A1 = B = True, A2 = False, Q = (A1 -∗ A2))
theorem w9c0_78 : ¬ drop0% Iris.ProofMode.wand_intro_intuitionistic 10 := fun h =>
  (@h GB gbBI iprop(True) iprop(True -∗ False) iprop(True) iprop(False) iprop(True) ⟨.rfl⟩
    ⟨fun _ _ => trivial⟩ (TCOr.r (u := inferInstance))) false trivial false trivial

-- `Iris.ProofMode.imp_intro_spatial` idx 7: necessary (GB, P = A1 = A2 = B = True, Q = False)
theorem w9c0_79 : ¬ drop0% Iris.ProofMode.imp_intro_spatial 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(True) iprop(True) iprop(True) ⟨fun _ h => h.2⟩
    (TCOr.l (t := inferInstance)) (fun _ _ => trivial)) false trivial

-- `Iris.ProofMode.imp_intro_spatial` idx 8: necessary (GB, P = A1 = True, A2 = B = False, Q = (A1 → A2))
theorem w9c0_80 : ¬ drop0% Iris.ProofMode.imp_intro_spatial 8 := fun h =>
  (@h GB gbBI iprop(True) iprop(True → False) iprop(True) iprop(False) iprop(False) ⟨.rfl⟩
    (TCOr.l (t := inferInstance)) (fun _ ⟨_, _, _, _, hb⟩ => hb)) false trivial trivial

-- `Iris.ProofMode.wand_intro_spatial` idx 6: necessary (GB, P = A1 = A2 = True, Q = False)
theorem w9c0_81 : ¬ drop0% Iris.ProofMode.wand_intro_spatial 6 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(True) iprop(True) (fun _ _ => trivial)) false trivial

-- `Iris.ProofMode.wand_intro_spatial` idx 7: necessary (GB, P = A1 = True, A2 = False, Q = (A1 -∗ A2))
theorem w9c0_82 : ¬ drop0% Iris.ProofMode.wand_intro_spatial 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(True -∗ False) iprop(True) iprop(False) ⟨.rfl⟩) false trivial
    false trivial

-- `Iris.ProofMode.tac_inv_elim` idx 15: necessary (dependent; GB, e = e' = False, Pinv = Pin = Pout = emp, Q' = True, goal = False)
theorem w9c0_83 : ¬ indep0% Iris.ProofMode.tac_inv_elim 15 := fun h =>
  (@h GB gbBI iprop(False) iprop(False) iprop(emp) iprop(False) True Unit false false iprop(emp)
    iprop(emp) none (fun _ => iprop(emp)) (fun _ => iprop(True)) trivial
    ⟨false_elim, fun _ ⟨_, _, _, ha, _⟩ => ha⟩ (fun _ ⟨_, _, _, ha, _⟩ => ha.elim)).elim_inv trivial
    false ⟨false, false, rfl, rfl, false, false, rfl, rfl, fun _ ⟨_, hx⟩ => hx ▸ fun _ _ => trivial⟩

-- `Iris.ProofMode.tac_inv_elim` idx 16: necessary (GB, phi = False, all emp, goal = False)
theorem w9c0_84 : ¬ drop0% Iris.ProofMode.tac_inv_elim 16 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(emp) iprop(False) False Unit false false iprop(emp)
    iprop(emp) none (fun _ => iprop(emp)) (fun _ => iprop(emp)) ⟨fun h => h.elim⟩
    (fun _ => sep_emp.1) gEE (wand_elim_right.trans sep_emp.2)) false rfl

-- `Iris.ProofMode.tac_inv_elim` idx 17: necessary (GB, phi = True, all emp, Q' = goal = False)
theorem w9c0_85 : ¬ drop0% Iris.ProofMode.tac_inv_elim 17 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(emp) iprop(False) True Unit false false iprop(emp)
    iprop(emp) none (fun _ => iprop(emp)) (fun _ => iprop(False))
    ⟨fun _ _ ⟨_, _, _, _, _, _, _, _, hd⟩ => hd _ ⟨(), rfl⟩ false ⟨false, false, rfl, rfl, rfl⟩⟩
    trivial gEE (wand_elim_right.trans sep_emp.2)) false rfl

-- `Iris.ProofMode.tac_inv_elim` idx 18: necessary (GB, e = True, e' = e'' = Q' = goal = False)
theorem w9c0_86 : ¬ drop0% Iris.ProofMode.tac_inv_elim 18 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(False) iprop(False) True Unit false false iprop(emp)
    iprop(emp) none (fun _ => iprop(emp)) (fun _ => iprop(False))
    ⟨fun _ _ ⟨_, _, _, _, _, _, _, _, hd⟩ => hd _ ⟨(), rfl⟩ false ⟨false, false, rfl, rfl, rfl⟩⟩
    trivial (fun _ _ ⟨_, _, _, ha, _⟩ => ha) (fun _ ⟨_, _, _, ha, _⟩ => ha.elim)) false trivial

-- `Iris.ProofMode.tac_inv_elim` idx 19: necessary (GB, e = e' = Pinv = Pin = emp, e'' = Q' = goal = False)
theorem w9c0_87 : ¬ drop0% Iris.ProofMode.tac_inv_elim 19 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(False) iprop(False) True Unit false false iprop(emp)
    iprop(emp) none (fun _ => iprop(emp)) (fun _ => iprop(False))
    ⟨fun _ _ ⟨_, _, _, _, _, _, _, _, hd⟩ => hd _ ⟨(), rfl⟩ false ⟨false, false, rfl, rfl, rfl⟩⟩
    trivial (fun _ _ ⟨_, _, _, ha, _⟩ => ha) gEE) false rfl

-- `Iris.ProofMode.from_or_left` idx 6: necessary (GB, P = A1 = A2 = True, Q = False)
theorem w9c0_88 : ¬ drop0% Iris.ProofMode.from_or_left 6 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(True) iprop(True) .rfl) false trivial

-- `Iris.ProofMode.from_or_left` idx 7: necessary (GB, P = True, A1 = A2 = Q = False)
theorem w9c0_89 : ¬ drop0% Iris.ProofMode.from_or_left 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(False) iprop(False) ⟨fun _ h => h.elim id id⟩) false trivial

-- `Iris.ProofMode.from_or_right` idx 6: necessary (GB, P = A1 = A2 = True, Q = False)
theorem w9c0_90 : ¬ drop0% Iris.ProofMode.from_or_right 6 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(True) iprop(True) .rfl) false trivial

-- `Iris.ProofMode.from_or_right` idx 7: necessary (GB, P = True, A1 = A2 = Q = False)
theorem w9c0_91 : ¬ drop0% Iris.ProofMode.from_or_right 7 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(False) iprop(False) ⟨fun _ h => h.elim id id⟩) false trivial

-- `Iris.ProofMode.mod` idx 10: necessary (GB, e = emp, A = True, A' = Q = Q' = False)
theorem w9c0_92 : ¬ drop0% Iris.ProofMode.mod 10 := fun h =>
  (@h GB gbBI iprop(emp) True false false iprop(True) iprop(False) iprop(False) iprop(False)
    (fun _ ⟨_, _, _, _, hb⟩ => hb) trivial) false ⟨false, false, rfl, rfl, trivial⟩

-- `Iris.ProofMode.mod` idx 11: necessary (GB, e = A' = True, A = emp, Q = Q' = False)
theorem w9c0_93 : ¬ drop0% Iris.ProofMode.mod 11 := fun h =>
  (@h GB gbBI iprop(True) True false false iprop(emp) iprop(True) iprop(False) iprop(False)
    ⟨fun _ _ ⟨_, _, _, _, hb⟩ => hb false trivial⟩ trivial) false ⟨false, false, rfl, trivial, rfl⟩

-- `Iris.ProofMode.mod` idx 12: necessary (GB, Phi = False, e = A = Q' = True, Q = False)
theorem w9c0_94 : ¬ drop0% Iris.ProofMode.mod 12 := fun h =>
  (@h GB gbBI iprop(True) False false false iprop(True) iprop(True) iprop(False) iprop(True)
    ⟨fun h => h.elim⟩ (fun _ _ => trivial)) false ⟨false, false, rfl, trivial, trivial⟩

namespace W9c0
open Iris Iris.BI Iris.ProofMode

/-- Modality on GB that sends everything to emp, with a chosen action (spec must hold). -/
def mEmp (a : Bool → ModalityAction GB GB) (hs : ∀ p, (a p).action_spec p (fun _ => (iprop(emp) : GB))) :
    Modality GB GB where
  M _ := iprop(emp)
  action := a
  spec := hs
  emp := .rfl
  mono _ := .rfl
  sep := sep_emp.1

/-! PF copied from W4c4: predicates on Nat with sep = and, emp = True (affine, discrete),
persistently P n := (P holds cofinitely) and P n. Not BIPersistentlyExist (evens or odds). -/
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

theorem ev_not_cof : ¬ cof ev := fun ⟨N, h⟩ => by
  have := h (2 * N + 1) (by omega); simp only [ev] at this; omega
theorem od_not_cof : ¬ cof od := fun ⟨N, h⟩ => by
  have := h (2 * N) (by omega); simp only [od] at this; omega
theorem evod_cof : cof (fun n => ev n ∨ od n) := ⟨0, fun m _ => by simp only [ev, od]; omega⟩

end W9c0

open Iris Iris.BI Iris.ProofMode Iris.Std W9c0

-- `Iris.ProofMode.exists_elim'` idx 3: necessary (at alpha : Type) in PF, p = true, P = emp, Phi true = ev, Phi false = od, Q = ∃ b, □ Phi b
theorem w9c0_6 : ¬ ∀ {PROP : Type} {α : Type} [inst : BI PROP] {p : Bool} {P A Q : PROP}
    {Φ : α → PROP} [inst_1 : IntoExists A Φ], (∀ (a : α), P ∗ □?p Φ a ⊢ Q) → P ∗ □?p A ⊢ Q :=
  fun h => by
  have := (@h PF Bool pfBI true iprop(emp) iprop(∃ b, (fun b : Bool => if b then ev else od) b)
    iprop(∃ b, □ (fun b : Bool => if b then ev else od) b) (fun b => if b then ev else od) ⟨.rfl⟩
    (fun a => emp_sep.1.trans (exists_intro (Ψ := fun b : Bool => iprop(□ (if b then ev else od))) a)))
    0 ⟨trivial, trivial, ⟨0, fun m _ => by
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

-- `Iris.ProofMode.or_elim'` idx 2: necessary (PF, p = true, P = emp, A1 = ev, A2 = od, A = A1 ∨ A2, Q = □A1 ∨ □A2)
theorem w9c0_19 : ¬ drop0% Iris.ProofMode.or_elim' 2 := fun h => by
  rcases (@h PF pfBI true iprop(emp) iprop(ev ∨ od) iprop(□ ev ∨ □ od) ev od ⟨.rfl⟩
    (emp_sep.1.trans or_intro_l) (emp_sep.1.trans or_intro_r)) 0
    ⟨trivial, trivial, evod_cof, .inl rfl⟩ with ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact ev_not_cof hc
  · exact od_not_cof hc

-- `Iris.ProofMode.modaction_forall` idx 6: necessary (GB, M = const emp with empty action, P = True)
theorem w9c0_95 : ¬ drop0% Iris.ProofMode.modaction_forall 6 := fun h =>
  Bool.noConfusion ((@h GB gbBI false iprop(True) (mEmp (fun _ => .isEmpty) (fun _ => trivial))
    (fun _ => True) trivial) true trivial : true = false)

-- `Iris.ProofMode.modaction_forall` idx 7: necessary (GB, M = const emp with action forall False, P = True)
theorem w9c0_96 : ¬ drop0% Iris.ProofMode.modaction_forall 7 := fun h =>
  Bool.noConfusion ((@h GB gbBI false iprop(True)
    (mEmp (fun _ => .forall (fun _ => False)) (fun _ _ h => h.elim)) (fun _ => False) rfl)
    true trivial : true = false)

-- `Iris.ProofMode.modaction_transform` idx 9: necessary (GB, M = const emp with empty action, P = True)
theorem w9c0_97 : ¬ drop0% Iris.ProofMode.modaction_transform 9 := fun h =>
  Bool.noConfusion ((@h GB GB gbBI gbBI false iprop(True) iprop(True)
    (mEmp (fun _ => .isEmpty) (fun _ => trivial)) (fun _ _ => True) trivial) true trivial : true = false)

-- `Iris.ProofMode.modaction_transform` idx 10: necessary (GB, M = const emp with action transform False, P = True)
theorem w9c0_98 : ¬ drop0% Iris.ProofMode.modaction_transform 10 := fun h =>
  Bool.noConfusion ((@h GB GB gbBI gbBI false iprop(True) iprop(True)
    (mEmp (fun _ => .transform (fun _ _ => False)) (fun _ _ _ h => h.elim)) (fun _ _ => False) rfl)
    true trivial : true = false)

-- `Iris.ProofMode.modaction_clear` idx 7: necessary (GB, M = const emp with empty action, P = True)
theorem w9c0_99 : ¬ drop0% Iris.ProofMode.modaction_clear 7 := fun h =>
  Bool.noConfusion ((@h GB GB gbBI gbBI false iprop(True)
    (mEmp (fun _ => .isEmpty) (fun _ => trivial))) true trivial : true = false)

-- `Iris.ProofMode.modaction_id` idx 5: necessary (GB, M = const emp with empty action, P = True)
theorem w9c0_100 : ¬ drop0% Iris.ProofMode.modaction_id 5 := fun h =>
  Bool.noConfusion ((@h GB gbBI false iprop(True)
    (mEmp (fun _ => .isEmpty) (fun _ => trivial))) true trivial : true = false)

-- `Iris.ProofMode.modaction_sep_emp_left` idx 8: necessary (GB, M = id, elhs = True, erhs = erhs' = emp)
theorem w9c0_101 : ¬ drop0% Iris.ProofMode.modaction_sep_emp_left 8 := fun h =>
  Bool.noConfusion ((@h GB GB gbBI gbBI iprop(True) iprop(emp) iprop(emp) modality_id .rfl)
    true ⟨true, false, rfl, trivial, rfl⟩ : true = false)

-- `Iris.ProofMode.modaction_sep_emp_left` idx 9: necessary (GB, M = id, elhs = erhs' = emp, erhs = True)
theorem w9c0_102 : ¬ drop0% Iris.ProofMode.modaction_sep_emp_left 9 := fun h =>
  Bool.noConfusion ((@h GB GB gbBI gbBI iprop(emp) iprop(True) iprop(emp) modality_id .rfl)
    true ⟨false, true, rfl, rfl, trivial⟩ : true = false)

-- `Iris.ProofMode.modaction_sep_emp_right` idx 8: necessary (GB, M = id, elhs = True, elhs' = erhs = emp)
theorem w9c0_103 : ¬ drop0% Iris.ProofMode.modaction_sep_emp_right 8 := fun h =>
  Bool.noConfusion ((@h GB GB gbBI gbBI iprop(True) iprop(emp) iprop(emp) modality_id .rfl)
    true ⟨true, false, rfl, trivial, rfl⟩ : true = false)

-- `Iris.ProofMode.modaction_sep_emp_right` idx 9: necessary (GB, M = id, elhs = elhs' = emp, erhs = True)
theorem w9c0_104 : ¬ drop0% Iris.ProofMode.modaction_sep_emp_right 9 := fun h =>
  Bool.noConfusion ((@h GB GB gbBI gbBI iprop(emp) iprop(emp) iprop(True) modality_id .rfl)
    true ⟨false, true, rfl, rfl, trivial⟩ : true = false)

-- `Iris.ProofMode.modaction_sep` idx 9: necessary (GB, M = id, elhs = True, elhs' = erhs = erhs' = emp)
theorem w9c0_105 : ¬ drop0% Iris.ProofMode.modaction_sep 9 := fun h =>
  let ⟨a, b, e, ha, hb⟩ := (@h GB GB gbBI gbBI iprop(True) iprop(emp) iprop(emp) iprop(emp) modality_id
    .rfl) true ⟨true, false, rfl, trivial, rfl⟩
  by
    have ha : a = false := ha
    have hb : b = false := hb
    subst ha hb; exact absurd e (by decide)

-- `Iris.ProofMode.modaction_sep` idx 10: necessary (GB, M = id, erhs = True, elhs = elhs' = erhs' = emp)
theorem w9c0_106 : ¬ drop0% Iris.ProofMode.modaction_sep 10 := fun h =>
  let ⟨a, b, e, ha, hb⟩ := (@h GB GB gbBI gbBI iprop(emp) iprop(True) iprop(emp) iprop(emp) modality_id
    .rfl) true ⟨false, true, rfl, rfl, trivial⟩
  by
    have ha : a = false := ha
    have hb : b = false := hb
    subst ha hb; exact absurd e (by decide)

-- `Iris.ProofMode.modintro` idx 12: necessary (GB, M = id, e = e' = Q = True, P = False)
theorem w9c0_107 : ¬ drop0% Iris.ProofMode.modintro 12 := fun h =>
  (@h GB GB gbBI gbBI iprop(True) iprop(True) Unit True modality_id () iprop(False) iprop(True)
    .rfl .rfl trivial) false trivial

-- `Iris.ProofMode.modintro` idx 13: necessary (GB, M = id, e = True, e' = P = Q = emp)
theorem w9c0_108 : ¬ drop0% Iris.ProofMode.modintro 13 := fun h =>
  Bool.noConfusion ((@h GB GB gbBI gbBI iprop(True) iprop(emp) Unit True modality_id () iprop(emp)
    iprop(emp) ⟨fun _ => .rfl⟩ .rfl trivial) true trivial : true = false)

-- `Iris.ProofMode.modintro` idx 14: necessary (GB, M = id, e = e' = True, P = Q = emp)
theorem w9c0_109 : ¬ drop0% Iris.ProofMode.modintro 14 := fun h =>
  Bool.noConfusion ((@h GB GB gbBI gbBI iprop(True) iprop(True) Unit True modality_id () iprop(emp)
    iprop(emp) ⟨fun _ => .rfl⟩ .rfl trivial) true trivial : true = false)

-- `Iris.ProofMode.modintro` idx 15: necessary (GB, Phi = False, M = id, e = e' = Q = True, P = False)
theorem w9c0_110 : ¬ drop0% Iris.ProofMode.modintro 15 := fun h =>
  (@h GB GB gbBI gbBI iprop(True) iprop(True) Unit False modality_id () iprop(False) iprop(True)
    ⟨fun h => h.elim⟩ .rfl .rfl) false trivial

-- `Iris.ProofMode.pure_elim_spatial` idx 7: necessary (GB, phi = False, P = P' = A = emp, Q = False)
theorem w9c0_111 : ¬ drop0% Iris.ProofMode.pure_elim_spatial 7 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(emp) iprop(False) False (TCOr.l (t := inferInstance)) gEE
    (fun h => h.elim)) false rfl

-- `Iris.ProofMode.pure_elim_spatial` idx 9: necessary (GB, phi = True, P = True, A = emp, P' = Q = False)
theorem w9c0_112 : ¬ drop0% Iris.ProofMode.pure_elim_spatial 9 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(emp) iprop(False) True ⟨fun _ _ => trivial⟩
    (TCOr.l (t := inferInstance)) (fun _ => .rfl)) false trivial

-- `Iris.ProofMode.pure_elim_spatial` idx 10: necessary (GB, phi = True, P = P' = A = emp, Q = False)
theorem w9c0_113 : ¬ drop0% Iris.ProofMode.pure_elim_spatial 10 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(emp) iprop(False) True ⟨fun _ _ => trivial⟩
    (TCOr.l (t := inferInstance)) gEE) false rfl

-- `Iris.ProofMode.pure_elim_intuitionistic` idx 7: necessary (GB, phi = False, P = P' = emp, A = True, Q = False)
theorem w9c0_114 : ¬ drop0% Iris.ProofMode.pure_elim_intuitionistic 7 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(True) iprop(False) False gEBe (fun h => h.elim)) false rfl

-- `Iris.ProofMode.pure_elim_intuitionistic` idx 8: necessary (GB, phi = True, P = A = True, P' = Q = False)
theorem w9c0_115 : ¬ drop0% Iris.ProofMode.pure_elim_intuitionistic 8 := fun h =>
  (@h GB gbBI iprop(True) iprop(False) iprop(True) iprop(False) True ⟨fun _ _ => trivial⟩
    (fun _ => .rfl)) false trivial

-- `Iris.ProofMode.pure_elim_intuitionistic` idx 9: necessary (GB, phi = True, P = P' = emp, A = True, Q = False)
theorem w9c0_116 : ¬ drop0% Iris.ProofMode.pure_elim_intuitionistic 9 := fun h =>
  (@h GB gbBI iprop(emp) iprop(emp) iprop(True) iprop(False) True ⟨fun _ _ => trivial⟩ gEBe)
    false rfl

-- `Iris.ProofMode.pure_intro_affine` idx 5: necessary (GB, P = emp, Q = False, phi = True)
theorem w9c0_117 : ¬ drop0% Iris.ProofMode.pure_intro_affine 5 := fun h =>
  (@h GB iprop(emp) gbBI iprop(False) True inferInstance trivial) false rfl

-- `Iris.ProofMode.pure_intro_affine` idx 7: necessary (GB, P = emp, Q = False, phi = False)
theorem w9c0_118 : ¬ drop0% Iris.ProofMode.pure_intro_affine 7 := fun h =>
  (@h GB iprop(emp) gbBI iprop(False) False ⟨fun _ h => h.2⟩ inferInstance) false rfl

-- `Iris.ProofMode.pure_intro_spatial` idx 5: necessary (GB, P = True, Q = False, phi = True)
theorem w9c0_119 : ¬ drop0% Iris.ProofMode.pure_intro_spatial 5 := fun h =>
  (@h GB iprop(True) gbBI iprop(False) True trivial) false trivial
