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

namespace W7c3
open Iris Iris.BI Iris.ProofMode
theorem sF (H : (iprop(True) : SiProp) ⊢ iprop(False)) : False := H 0 trivial
theorem sE (H : (iprop(emp) : SiProp) ⊢ iprop(False)) : False := H 0 trivial
@[reducible] def natOFE : OFE Nat := OFE.ofDiscrete Nat
theorem ent {P Q : SiProp} (H : P ⊢ Q) : ∀ n, P.holds n → Q.holds n := H
end W7c3
open Iris Iris.BI Iris.ProofMode W7c3

-- `Iris.ProofMode.AsEmpValid.as_emp_valid` idx 6: necessary
theorem w7c3_62 : ¬ drop0% Iris.ProofMode.AsEmpValid.as_emp_valid 6 := fun h =>
  sE ((@h .into True .in SiProp SiProp.instBI iprop(False)).1 rfl trivial)
-- `Iris.ProofMode.asEmpValid_1` idx 5: necessary
theorem w7c3_63 : ¬ drop0% Iris.ProofMode.asEmpValid_1 5 := fun h =>
  sE (@h SiProp _ True iprop(False) .in trivial)
-- `Iris.ProofMode.asEmpValid_2` idx 5: necessary
theorem w7c3_64 : ¬ drop0% Iris.ProofMode.asEmpValid_2 5 := fun h =>
  @h SiProp _ iprop(True) False .in (fun _ _ => trivial)
-- `Iris.ProofMode.asEmpValid_2` idx 6: necessary
theorem w7c3_65 : ¬ drop0% Iris.ProofMode.asEmpValid_2 6 := fun h =>
  @h SiProp _ iprop(False) False .in ⟨⟨fun e => AsEmpValid.Direction.noConfusion e, fun _ hP => sE hP⟩⟩
-- `Iris.ProofMode.AsEmpValid0.as_emp_valid_0` idx 7: necessary
theorem w7c3_66 : ¬ drop0% Iris.ProofMode.AsEmpValid0.as_emp_valid_0 7 := fun h =>
  (@h .from False .in SiProp SiProp.instBI .in iprop(True)).as_emp_valid.2 rfl (fun _ _ => trivial)
-- `Iris.ProofMode.asEmpValid_of_asEmpValid0` idx 6: necessary
theorem w7c3_67 : ¬ drop0% Iris.ProofMode.asEmpValid_of_asEmpValid0 6 := fun h =>
  (h .from False .in SiProp SiProp.instBI iprop(True)).as_emp_valid.2 rfl (fun _ _ => trivial)
-- `Iris.ProofMode.FromImp.from_imp` idx 5: necessary
theorem w7c3_68 : ¬ drop0% Iris.ProofMode.FromImp.from_imp 5 := fun h =>
  sF ((BI.imp_intro true_intro).trans (@h SiProp _ iprop(False) iprop(False) iprop(True)))
-- `Iris.ProofMode.FromWand.from_wand` idx 6: necessary
theorem w7c3_69 : ¬ drop0% Iris.ProofMode.FromWand.from_wand 6 := fun h =>
  sF ((wand_intro true_intro).trans (@h SiProp _ iprop(False) .in iprop(False) iprop(True)))
-- `Iris.ProofMode.IntoForall.into_forall` idx 5: necessary
theorem w7c3_70 : ¬ drop0% Iris.ProofMode.IntoForall.into_forall 5 := fun h =>
  sF ((@h SiProp _ iprop(True) True (fun _ => iprop(False))).trans (forall_elim trivial))
-- `Iris.ProofMode.FromAnd.from_and` idx 5: necessary
theorem w7c3_71 : ¬ drop0% Iris.ProofMode.FromAnd.from_and 5 := fun h =>
  sF ((and_intro .rfl .rfl).trans (@h SiProp _ iprop(False) iprop(True) iprop(True)))
-- `Iris.ProofMode.IntoAnd.into_and` idx 6: necessary
theorem w7c3_72 : ¬ drop0% Iris.ProofMode.IntoAnd.into_and 6 := fun h =>
  sF ((@h SiProp _ false iprop(True) iprop(False) iprop(True)).trans and_elim_l)
-- `Iris.ProofMode.FromSep.from_sep` idx 5: necessary
theorem w7c3_73 : ¬ drop0% Iris.ProofMode.FromSep.from_sep 5 := fun h =>
  sE (emp_sep.2.trans (@h SiProp _ iprop(False) iprop(emp) iprop(emp)))
-- `Iris.ProofMode.FromOr.from_or` idx 5: necessary
theorem w7c3_74 : ¬ drop0% Iris.ProofMode.FromOr.from_or 5 := fun h =>
  sF (or_intro_l.trans (@h SiProp _ iprop(False) iprop(True) iprop(True)))
-- `Iris.ProofMode.IntoOr.into_or` idx 5: necessary
theorem w7c3_75 : ¬ drop0% Iris.ProofMode.IntoOr.into_or 5 := fun h =>
  sF ((@h SiProp _ iprop(True) iprop(False) iprop(False)).trans (or_elim .rfl .rfl))
-- `Iris.ProofMode.IntoInternalEq.into_internal_eq` idx 8: necessary
theorem w7c3_76 : ¬ drop0% Iris.ProofMode.IntoInternalEq.into_internal_eq 8 := fun h =>
  absurd (internalEq_soundness (PROP := SiProp) (0 : Nat) 1
    (true_intro.trans (@h SiProp _ _ Nat natOFE iprop(True) 0 1))) (by decide)
-- `Iris.ProofMode.IntoPersistently.into_persistently` idx 5: necessary
theorem w7c3_77 : ¬ drop0% Iris.ProofMode.IntoPersistently.into_persistently 5 := fun h =>
  ent (@h SiProp _ false iprop(True) iprop(False)) 0 trivial
-- `Iris.ProofMode.FromAffinely.from_affinely` idx 5: necessary
theorem w7c3_78 : ¬ drop0% Iris.ProofMode.FromAffinely.from_affinely 5 := fun h =>
  ent (@h SiProp _ iprop(False) iprop(True) false) 0 trivial
-- `Iris.ProofMode.IntoAbsorbingly.into_absorbingly` idx 4: necessary
theorem w7c3_79 : ¬ drop0% Iris.ProofMode.IntoAbsorbingly.into_absorbingly 4 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(False)) 0 trivial).2
-- `Iris.ProofMode.IntoExcept0.into_except0` idx 4: necessary
theorem w7c3_80 : ¬ drop0% Iris.ProofMode.IntoExcept0.into_except0 4 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(False)) 1 trivial).elim (fun h => h) (fun h => h)
-- `Iris.ProofMode.IsDisjUnion.is_disj_union` idx 6: necessary
theorem w7c3_83 : ¬ drop0% Iris.ProofMode.IsDisjUnion.is_disj_union 6 := fun h => by
  have e := congrArg (Iris.Std.MultiSet.multiplicity (0 : Nat)) (@h (Iris.Std.ListPerm Nat) Nat inferInstance {0} ∅ ∅)
  rw [Iris.Std.LawfulMultiSet.multiplicity_disjUnion, Iris.Std.LawfulMultiSet.multiplicity_empty,
    Iris.Std.LawfulMultiSet.multiplicity_singleton_eq] at e
  exact absurd e (by decide)
-- `Iris.ProofMode.FrameInstantiateExistDisabled.frame_instantiatiate_exist_disabled` idx 6: necessary
theorem w7c3_84 : ¬ drop0% Iris.ProofMode.FrameInstantiateExistDisabled.frame_instantiatiate_exist_disabled 6 := fun h =>
  ent (@h SiProp _ false iprop(True) iprop(False) iprop(True)).frame 0 ⟨trivial, trivial⟩

namespace W7c3
open Iris Iris.BI Iris.Std
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
abbrev UIdx : Iris.BI.BiIndex := { car := Nat, rel := inferInstance }
instance idBupd : BIUpdate SiProp where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h
end W7c3
open Iris Iris.BI Iris.ProofMode W7c3

-- `Iris.ProofMode.FromModal.from_modal` idx 12: necessary
theorem w7c3_81 : ¬ drop0% Iris.ProofMode.FromModal.from_modal 12 := fun h =>
  sF (@h .in SiProp SiProp Unit SiProp.instBI SiProp.instBI modality_id False () iprop(False) iprop(True)
    ⟨fun hf => hf.elim⟩)
-- `Iris.ProofMode.ElimModal.elim_modal` idx 11: necessary
theorem w7c3_82 : ¬ drop0% Iris.ProofMode.ElimModal.elim_modal 11 := fun h =>
  ent (@h SiProp _ False false .in false iprop(True) iprop(True) iprop(False) iprop(True) ⟨fun hf => hf.elim⟩) 0
    ⟨trivial, fun _ _ _ => trivial⟩
-- `Iris.ProofMode.ElimAcc.elim_acc` idx 11: necessary
theorem w7c3_85 : ¬ drop0% Iris.ProofMode.ElimAcc.elim_acc 11 := fun h =>
  ent (@h SiProp _ Unit True id id (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => none) iprop(False)
    (fun _ => iprop(True)) trivial) 0 trivial 0 (Nat.le_refl 0) (SiProp.forall_holds.2 fun _ _ _ _ => trivial)
    0 (Nat.le_refl 0) (SiProp.exists_holds.2 ⟨(), trivial, fun _ _ _ => trivial⟩)
-- `Iris.ProofMode.ElimAcc.elim_acc` idx 12: necessary
theorem w7c3_86 : ¬ drop0% Iris.ProofMode.ElimAcc.elim_acc 12 := fun h =>
  ent (@h SiProp _ Unit False id id (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => none) iprop(False)
    (fun _ => iprop(True)) ⟨fun hf => hf.elim⟩) 0 trivial 0 (Nat.le_refl 0) (SiProp.forall_holds.2 fun _ _ _ _ => trivial)
    0 (Nat.le_refl 0) (SiProp.exists_holds.2 ⟨(), trivial, fun _ _ _ => trivial⟩)
-- `Iris.ProofMode.IntoAcc.into_acc` idx 11: necessary
theorem w7c3_87 : ¬ drop0% Iris.ProofMode.IntoAcc.into_acc 11 := fun h =>
  ent (@h SiProp _ Unit iprop(True) True iprop(True) (fun _ => iprop(False)) id (fun _ => iprop(True))
    (fun _ => iprop(True)) (fun _ => none) trivial) 0 trivial 0 (Nat.le_refl 0) trivial 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.IntoAcc.into_acc` idx 12: necessary
theorem w7c3_88 : ¬ drop0% Iris.ProofMode.IntoAcc.into_acc 12 := fun h =>
  ent (@h SiProp _ Unit iprop(True) False iprop(True) (fun _ => iprop(False)) id (fun _ => iprop(True))
    (fun _ => iprop(True)) (fun _ => none) ⟨fun hf => hf.elim⟩) 0 trivial 0 (Nat.le_refl 0) trivial 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.ElimInv.elim_inv` idx 11: necessary
theorem w7c3_89 : ¬ drop0% Iris.ProofMode.ElimInv.elim_inv 11 := fun h =>
  ent (@h SiProp _ True Unit iprop(True) iprop(True) (fun _ => iprop(True)) false none iprop(False)
    (fun _ => iprop(True)) trivial) 0 ⟨trivial, trivial, SiProp.forall_holds.2 fun _ _ _ _ => trivial⟩
-- `Iris.ProofMode.ElimInv.elim_inv` idx 12: necessary
theorem w7c3_90 : ¬ drop0% Iris.ProofMode.ElimInv.elim_inv 12 := fun h =>
  ent (@h SiProp _ False Unit iprop(True) iprop(True) (fun _ => iprop(True)) false none iprop(False)
    (fun _ => iprop(True)) ⟨fun hf => hf.elim⟩) 0 ⟨trivial, trivial, SiProp.forall_holds.2 fun _ _ _ _ => trivial⟩
-- `Iris.ProofMode.IntoIH.into_ih` idx 5: necessary
theorem w7c3_91 : ¬ drop0% Iris.ProofMode.IntoIH.into_ih 5 := fun h =>
  ent (@h SiProp _ True iprop(True) iprop(False) trivial) 0 ⟨trivial, trivial⟩
-- `Iris.ProofMode.IntoIH.into_ih` idx 6: necessary
theorem w7c3_92 : ¬ drop0% Iris.ProofMode.IntoIH.into_ih 6 := fun h =>
  ent (@h SiProp _ False iprop(True) iprop(False) ⟨fun hf => hf.elim⟩) 0 ⟨trivial, trivial⟩
-- `Iris.ProofMode.IntoEmbed.into_embed` idx 7: necessary
theorem w7c3_93 : ¬ drop0% Iris.ProofMode.IntoEmbed.into_embed 7 := fun h =>
  (show MonPred.Entails _ _ from @h SiProp (MonPred UIdx SiProp) _ _ _ iprop(True) iprop(False)) (0 : Nat) 0 trivial
-- `Iris.ProofMode.QuickAbsorbing.quick_absorbing` idx 3: necessary
theorem w7c3_94 : ¬ drop0% Iris.ProofMode.QuickAbsorbing.quick_absorbing 3 := fun h =>
  gb_emp_not_absorbing (@h GB _ iprop(emp))
-- `Iris.ProofMode.MakeSep.make_sep` idx 5: necessary
theorem w7c3_95 : ¬ drop0% Iris.ProofMode.MakeSep.make_sep 5 := fun h =>
  ent (@h SiProp _ iprop(True) iprop(True) iprop(False)).mp 0 ⟨trivial, trivial⟩
-- `Iris.ProofMode.MakeAnd.make_and` idx 5: necessary
theorem w7c3_96 : ¬ drop0% Iris.ProofMode.MakeAnd.make_and 5 := fun h =>
  ent (@h SiProp _ iprop(True) iprop(True) iprop(False)).mp 0 ⟨trivial, trivial⟩
-- `Iris.ProofMode.MakeOr.make_or` idx 5: necessary
theorem w7c3_97 : ¬ drop0% Iris.ProofMode.MakeOr.make_or 5 := fun h =>
  ent (@h SiProp _ iprop(True) iprop(True) iprop(False)).mp 0 (.inl trivial)
-- `Iris.ProofMode.MakeIntuitionistically.make_intuitionistically` idx 4: necessary
theorem w7c3_98 : ¬ drop0% Iris.ProofMode.MakeIntuitionistically.make_intuitionistically 4 := fun h =>
  ent (@h SiProp _ iprop(True) iprop(False)).mp 0 ⟨trivial, trivial⟩
-- `Iris.ProofMode.MakeAbsorbingly.make_absorbingly` idx 4: necessary
theorem w7c3_99 : ¬ drop0% Iris.ProofMode.MakeAbsorbingly.make_absorbingly 4 := fun h =>
  ent (@h SiProp _ iprop(True) iprop(False)).mp 0 ⟨trivial, trivial⟩
-- `Iris.ProofMode.MakePersistently.make_persistently` idx 4: necessary
theorem w7c3_100 : ¬ drop0% Iris.ProofMode.MakePersistently.make_persistently 4 := fun h =>
  ent (@h SiProp _ iprop(True) iprop(False)).mp 0 trivial
-- `Iris.ProofMode.MakeLaterN.make_laterN` idx 5: necessary
theorem w7c3_101 : ¬ drop0% Iris.ProofMode.MakeLaterN.make_laterN 5 := fun h =>
  ent (@h SiProp _ 0 iprop(True) iprop(False)).mp 0 trivial
-- `Iris.ProofMode.MakeExcept0.make_except0` idx 4: necessary
theorem w7c3_102 : ¬ drop0% Iris.ProofMode.MakeExcept0.make_except0 4 := fun h =>
  ent (@h SiProp _ iprop(True) iprop(False)).mp 0 (.inr trivial)
-- `Iris.ProofMode.MakeBUpd.make_bupd` idx 5: necessary
theorem w7c3_103 : ¬ drop0% Iris.ProofMode.MakeBUpd.make_bupd 5 := fun h =>
  ent (@h SiProp _ idBupd iprop(True) iprop(False)).mp 0 trivial
-- `Iris.ProofMode.MakeEmbed.make_embed` idx 7: necessary
theorem w7c3_105 : ¬ drop0% Iris.ProofMode.MakeEmbed.make_embed 7 := fun h =>
  (@h SiProp (MonPred UIdx SiProp) _ _ _ iprop(True) iprop(False)).mp (0 : Nat) 0 trivial
-- `Iris.ProofMode.split_es` idx 5: necessary
theorem w7c3_106 : ¬ drop0% Iris.ProofMode.split_es 5 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(False) iprop(True)).mp 0 ⟨trivial, trivial⟩).1
-- `Iris.ProofMode.split_rs` idx 6: necessary
theorem w7c3_107 : ¬ drop0% Iris.ProofMode.split_rs 6 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True)).mp 0 ⟨trivial, trivial⟩).1
-- `Iris.ProofMode.split_se` idx 5: necessary
theorem w7c3_108 : ¬ drop0% Iris.ProofMode.split_se 5 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(False) iprop(True)).mp 0 ⟨trivial, trivial⟩).1
-- `Iris.ProofMode.split_sl` idx 6: necessary
theorem w7c3_109 : ¬ drop0% Iris.ProofMode.split_sl 6 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True)).mp 0 ⟨trivial, trivial⟩).1.1
-- `Iris.ProofMode.split_ss` idx 8: necessary
theorem w7c3_110 : ¬ drop0% Iris.ProofMode.split_ss 8 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(True) iprop(False) iprop(True) iprop(True) iprop(True)
    ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩).mp 0 ⟨trivial, trivial⟩).1.1
-- `Iris.ProofMode.split_ss` idx 9: necessary
theorem w7c3_111 : ¬ drop0% Iris.ProofMode.split_ss 9 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(True) iprop(True) iprop(True) iprop(False) iprop(True)
    ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩).mp 0 ⟨trivial, trivial⟩).1.2
-- `Iris.ProofMode.remove_left` idx 6: necessary
theorem w7c3_112 : ¬ drop0% Iris.ProofMode.remove_left 6 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(False) iprop(True) iprop(True)).mp 0 ⟨trivial, trivial⟩).1.1
-- `Iris.ProofMode.Replaces.apply` idx 5: necessary
theorem w7c3_113 : ¬ drop0% Iris.ProofMode.Replaces.apply 5 := fun h =>
  sF (@h SiProp _ iprop(True) iprop(False) iprop(False) BIBase.Entails.rfl)
-- `Iris.ProofMode.Replaces.apply` idx 6: necessary
theorem w7c3_114 : ¬ drop0% Iris.ProofMode.Replaces.apply 6 := fun h =>
  sF (@h SiProp _ iprop(True) iprop(True) iprop(False) (BIBase.Entails.rfl : (iprop(True -∗ False) : SiProp) ⊢ _))
-- `Iris.ProofMode.replaces_right` idx 6: necessary
theorem w7c3_115 : ¬ drop0% Iris.ProofMode.replaces_right 6 := fun h =>
  ent (@h SiProp _ iprop(False) iprop(True) iprop(True) iprop(False)) 0 (fun _ _ hpq => hpq.2) 0 (Nat.le_refl 0)
    ⟨trivial, trivial⟩
-- `Iris.ProofMode.replaces_left` idx 6: necessary
theorem w7c3_116 : ¬ drop0% Iris.ProofMode.replaces_left 6 := fun h =>
  ent (@h SiProp _ iprop(False) iprop(True) iprop(False) iprop(True)) 0 (fun _ _ hpq => hpq.1) 0 (Nat.le_refl 0)
    ⟨trivial, trivial⟩
-- `Iris.ProofMode.to_persistent_spatial` idx 5: necessary
theorem w7c3_117 : ¬ drop0% Iris.ProofMode.to_persistent_spatial 5 := fun h =>
  ent (@h SiProp _ iprop(True) iprop(False) iprop(False) _) 0 (fun _ _ hp => hp.2) 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.to_persistent_intuitionistic` idx 5: necessary
theorem w7c3_118 : ¬ drop0% Iris.ProofMode.to_persistent_intuitionistic 5 := fun h =>
  ent (@h SiProp _ iprop(True) iprop(False) iprop(False)) 0 (fun _ _ hp => hp.2) 0 (Nat.le_refl 0) ⟨trivial, trivial⟩
-- `Iris.ProofMode.from_affine` idx 6: necessary
theorem w7c3_119 : ¬ drop0% Iris.ProofMode.from_affine 6 := fun h =>
  ent (@h SiProp _ false iprop(True) iprop(False) iprop(False)) 0 (fun _ _ hp => hp) 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.replace_hyp` idx 6: necessary
theorem w7c3_120 : ¬ drop0% Iris.ProofMode.replace_hyp 6 := fun h =>
  (ent (@h SiProp _ false iprop(True) iprop(False) iprop(True) iprop(True)) 0 ⟨⟨trivial, trivial⟩, trivial⟩).1
-- `Iris.ProofMode.replace_hyp_sep_left` idx 6: necessary
theorem w7c3_121 : ¬ drop0% Iris.ProofMode.replace_hyp_sep_left 6 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(False) iprop(True) iprop(True) iprop(True)) 0
    ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩).1.1
-- `Iris.ProofMode.replace_hyp_sep_right` idx 6: necessary
theorem w7c3_122 : ¬ drop0% Iris.ProofMode.replace_hyp_sep_right 6 := fun h =>
  (ent (@h SiProp _ iprop(True) iprop(False) iprop(True) iprop(True) iprop(True)) 0
    ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩).1.2
-- `Iris.ProofMode.replace_finish` idx 4: necessary
theorem w7c3_123 : ¬ drop0% Iris.ProofMode.replace_finish 4 := fun h =>
  sF (@h SiProp _ iprop(True) iprop(False))

namespace W7c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF

/-- fupd soundness with arbitrary masks: ⊢ |={E1,E2}=> False is impossible in IProp (from W6c1). -/
theorem fupd_false (E1 E2 : CoPset) (H : ∀ [InvGS_gen .hasNoLC CGF], ⊢ (iprop(|={E1,E2}=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := E1) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))

/-- Toy language: expressions Nat, values Bool (0 = false, 1 = true), 2 steps to 0, 4 steps to 4, 3 is stuck. -/
instance vToVal : ToVal Nat Bool where
  toVal n := if n = 0 then some false else if n = 1 then some true else none
  ofVal b := if b then 1 else 0
  coe_of_toVal_eq_some {e v} h := by
    match e, v with
    | 0, false => rfl
    | 1, true => rfl
    | 0, true => simp at h
    | 1, false => simp at h
    | n + 2, _ => simp at h
  toVal_coe b := by cases b <;> rfl

instance vLang : Language Nat Unit Unit Bool where
  primStep c _ c' := (c.1 = 2 ∧ c'.1 = 0 ∨ c.1 = 4 ∧ c'.1 = 4) ∧ c'.2.2 = []
  val_stuck {e} := by
    intro _ _ _ _ _ ⟨h, _⟩
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> (simp only at h; subst h; rfl)

/-- IrisGS over the toy language with a constant state interpretation. -/
@[reducible] noncomputable def mkI [x : InvGS_gen .hasNoLC CGF] (si : IProp CGF) : IrisGS_gen .hasNoLC Nat CGF :=
  { invGS := x, stateInterp := fun _ _ _ _ => si, numLatersPerStep := fun _ => 0,
    forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }

abbrev vF : Nat := ToVal.ofVal false
abbrev vT : Nat := ToVal.ofVal true
end W7c3
open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic W7c3
-- `Iris.ProofMode.MakeFUpd.make_fupd` idx 7: necessary
theorem w7c3_104 : ¬ drop0% Iris.ProofMode.MakeFUpd.make_fupd 7 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => (true_intro.trans fupd_intro).trans ((@h (IProp CGF) _ _ ⊤ ⊤ iprop(True) iprop(⌜False⌝)).mp.trans fupd_intro)
-- `Iris.twp.mono` idx 13: necessary
theorem w7c3_27 : ¬ drop0% Iris.twp.mono 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact ((true_intro.trans (twp.value' (Φ := fun _ => iprop(True)) (v := false))).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF (fun _ => iprop(True)) (fun _ => iprop(⌜False⌝)))).trans
      twp.value_fupd'.mp
-- `Iris.wp_mono` idx 13: necessary
theorem w7c3_44 : ¬ drop0% Iris.wp_mono 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact ((true_intro.trans (wp_value' (Φ := fun _ => iprop(True)) (v := false))).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF (fun _ => iprop(True)) (fun _ => iprop(⌜False⌝)))).trans
      wp_value_fupd'.mp
-- `Iris.twp.value` idx 13: necessary
theorem w7c3_30 : ¬ drop0% Iris.twp.value 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact ((pure_intro rfl).trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF true
      (fun b => iprop(⌜b = true⌝)))).trans (twp.value_fupd'.mp.trans (BIFUpdate.mono (pure_mono (φ2 := False) Bool.noConfusion)))
-- `Iris.wp_value` idx 13: necessary
theorem w7c3_48 : ¬ drop0% Iris.wp_value 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact ((pure_intro rfl).trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF true
      (fun b => iprop(⌜b = true⌝)))).trans (wp_value_fupd'.mp.trans (BIFUpdate.mono (pure_mono (φ2 := False) Bool.noConfusion)))
-- `Iris.twp.value_fupd` idx 13: necessary
theorem w7c3_19 : ¬ drop0% Iris.twp.value_fupd 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact ((pure_intro rfl).trans (twp.value' (Φ := fun b => iprop(⌜b = true⌝)) (v := true))).trans
      ((@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vT false (fun b => iprop(⌜b = true⌝))).mp.trans
        (BIFUpdate.mono (pure_mono (φ2 := False) Bool.noConfusion)))
-- `Iris.wp_value_fupd` idx 13: necessary
theorem w7c3_47 : ¬ drop0% Iris.wp_value_fupd 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact ((pure_intro rfl).trans (wp_value' (Φ := fun b => iprop(⌜b = true⌝)) (v := true))).trans
      ((@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vT false (fun b => iprop(⌜b = true⌝))).mp.trans
        (BIFUpdate.mono (pure_mono (φ2 := False) Bool.noConfusion)))
-- `Iris.ProgramLogic.twp.pure_step` idx 16: necessary
theorem w7c3_16 : ¬ drop0% Iris.ProgramLogic.twp.pure_step 16 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact (((pure_intro rfl).trans (twp.value' (Φ := fun b => iprop(⌜b = true⌝)) (v := true))).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF vT (fun b => iprop(⌜b = true⌝)) True 0 inferInstance trivial)).trans
        (twp.value_fupd'.mp.trans (BIFUpdate.mono (pure_mono (φ2 := False) Bool.noConfusion)))
-- `Iris.ProgramLogic.twp.pure_step` idx 17: necessary
theorem w7c3_17 : ¬ drop0% Iris.ProgramLogic.twp.pure_step 17 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact (((pure_intro rfl).trans (twp.value' (Φ := fun b => iprop(⌜b = true⌝)) (v := true))).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF vT (fun b => iprop(⌜b = true⌝)) False 0 inferInstance
        ⟨fun hf => hf.elim⟩)).trans
        (twp.value_fupd'.mp.trans (BIFUpdate.mono (pure_mono (φ2 := False) Bool.noConfusion)))
-- `Iris.twp.frameTwp` idx 15: necessary
theorem w7c3_32 : ¬ drop0% Iris.twp.frameTwp 15 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact ((true_intro.trans (twp.value' (Φ := fun _ => iprop(True)) (v := false))).trans
      (emp_sep.2.trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF (fun _ => iprop(⌜False⌝))
        (fun _ => iprop(True)) iprop(emp) false).frame)).trans twp.value_fupd'.mp
-- `Iris.frameWp` idx 15: necessary
theorem w7c3_61 : ¬ drop0% Iris.frameWp 15 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact ((true_intro.trans (wp_value' (Φ := fun _ => iprop(True)) (v := false))).trans
      (emp_sep.2.trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF (fun _ => iprop(⌜False⌝))
        (fun _ => iprop(True)) iprop(emp) false).frame)).trans wp_value_fupd'.mp
namespace W7c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic
theorem vF_nostep {σ : Unit} {κ : List Unit} {c' : Nat × Unit × List Nat} :
    ¬ vLang.toPrimStep.primStep (vF, σ) κ c' := by
  rintro ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩ <;> change (0 : Nat) = _ at h <;> cases h
theorem acc_loop {α : Type} {r : α → α → Prop} {x : α} (hx : r x x) : ¬ Relation.StronglyNormalizing r x := by
  intro hacc
  have : ∀ y, Acc (flip r) y → y ≠ x := fun y hy => by
    induction hy with
    | intro y _ ih => intro hyx; subst hyx; exact ih y hx rfl
  exact this x hacc rfl
@[instance_reducible] def nLang : Language Bool Unit Unit Unit where
  primStep := fun _ _ _ => False
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by intro e σ obs e' σ' eₜ h; exact h.elim
theorem nLang_nostep {ρ κ ρ'} : ¬ Language.Step (Λ := nLang) ρ κ ρ' := fun s => by
  cases s with | atomic H => exact H
end W7c3
open W7c3

-- `Iris.ProgramLogic.twp.lift_pure_step_no_fork` idx 13: necessary
theorem w7c3_12 : ¬ drop0% Iris.ProgramLogic.twp.lift_pure_step_no_fork 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact ((forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      BI.imp_intro (pure_elim_right fun hs => absurd hs vF_nostep)).trans fupd_intro).trans
      ((@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF (fun _ => iprop(⌜False⌝)) inferInstance
        (fun _ _ _ _ _ hs => absurd hs vF_nostep)).trans twp.value_fupd'.mp)
-- `Iris.ProgramLogic.twp.lift_step` idx 12: necessary
theorem w7c3_10 : ¬ drop0% Iris.ProgramLogic.twp.lift_step 12 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(False)
    exact (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      wand_intro (sep_elim_right.trans false_elim)).trans
      ((@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF (fun _ => iprop(⌜False⌝))).trans twp.value_fupd'.mp)
-- `Iris.ProgramLogic.twp.lift_atomic_step` idx 12: necessary
theorem w7c3_11 : ¬ drop0% Iris.ProgramLogic.twp.lift_atomic_step 12 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(False)
    exact (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      wand_intro (sep_elim_right.trans false_elim)).trans
      ((@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF (fun _ => iprop(⌜False⌝))).trans twp.value_fupd'.mp)
-- `Iris.wp_credit_access` idx 13: necessary
theorem w7c3_37 : ¬ drop0% Iris.wp_credit_access 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(False)
    have A : (iprop(emp) : IProp CGF) ⊢ _ := (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      wand_intro (sep_elim_right.trans false_elim)).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ vF (fun _ => iprop(⌜False⌝)) iprop(⌜False⌝)
        (fun _ _ => Nat.le_refl 0))
    have B : (iprop(emp) : IProp CGF) ⊢ _ := (wand_intro (sep_elim_right.trans false_elim)).trans
      (wp_value' (hlc := .hasNoLC) (Expr := Nat) (GF := CGF) (s := .NotStuck) (E := ⊤) (v := false) (Φ := fun _ => iprop(⌜False⌝ ={⊤}=∗ ⌜False⌝)))
    exact (emp_sep.2.trans ((sep_mono A B).trans wand_elim_left)).trans wp_value_fupd'.mp
-- `_private.Iris.ProgramLogic.TotalAdequacy.0.Iris.ProgramLogic.twptp.step_append_inv` idx 11: necessary
theorem w7c3_0 : ¬ drop0% _private.Iris.ProgramLogic.TotalAdequacy.«0».Iris.ProgramLogic.twptp.step_append_inv 11 :=
  fun h => match @h Bool Unit Unit Unit nLang [] [] [] () () [] with
  | .inl ⟨_, s, _⟩ => nLang_nostep s
  | .inr ⟨_, s, _⟩ => nLang_nostep s
-- `Iris.ProgramLogic.twp_total` idx 14: necessary
theorem w7c3_2 : ¬ drop0% Iris.ProgramLogic.twp_total 14 := fun h =>
  acc_loop (r := Language.ErasedStep (Λ := vLang)) (x := ([4], ())) ⟨[], Language.Step.atomic (e := 4) (e' := 4)
    (eₜ := []) (And.intro (Or.inr ⟨rfl, rfl⟩) rfl) [] []⟩
    (@h Nat Unit Unit Bool .hasNoLC CGF inferInstance vLang .NotStuck 4 () (fun _ => iprop(True)) 0 0)

namespace W7c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic

theorem nLang_nsteps {n ρ₁ κ ρ₂} (hs : Language.NSteps (Λ := nLang) n ρ₁ κ ρ₂) (hn : n ≠ 0) : False := by
  cases hs with
  | refl => exact hn rfl
  | cons s _ => cases s with | atomic H => exact H

-- `Iris.ProgramLogic.nSteps_one` idx 8: necessary (Bool language with no steps: NSteps 1 impossible)
theorem p4_42 : ¬ drop0% Iris.ProgramLogic.nSteps_one 8 := fun h =>
  nLang_nsteps (@h Bool Unit Unit Unit nLang ([], ()) ([], ()) []) (by decide)

def fillN (k : Bool) (e : Nat) : Nat := if k then (if e = 1 then 1 else 2 * e) else 2 * e + 1
def toValN (e : Nat) : Option Unit := if e = 0 then some () else none

theorem fillN_inj (k : Bool) : Function.Injective (fillN k) := by
  intro a b h; cases k
  · simp [fillN] at h; omega
  · by_cases ha : a = 1 <;> by_cases hb : b = 1 <;> simp [fillN, ha, hb] at h <;> omega

theorem fillN_val (e : Nat) (k : Bool) : (toValN (fillN k e)).isSome → (toValN e).isSome := by
  intro h
  by_cases he : e = 0
  · simp [toValN, he]
  · exfalso; cases k
    · simp [toValN, fillN] at h
    · by_cases h1 : e = 1 <;> simp [toValN, fillN, h1] at h <;> omega

theorem fillN_nvi (e₁ e₂ : Nat) (k₁ k₂ : Bool) (h1 : toValN e₁ = none) (h2 : toValN e₂ = none)
    (h : fillN k₁ e₁ = fillN k₂ e₂) : k₁ = k₂ := by
  simp [toValN] at h1 h2
  cases k₁ <;> cases k₂ <;> simp only [fillN] at h <;> simp at h ⊢
  · by_cases hb : e₂ = 1 <;> simp [hb] at h <;> omega
  · by_cases ha : e₁ = 1 <;> simp [ha] at h <;> omega

@[instance_reducible] def iLang : EctxItemLanguage Nat Bool Unit Unit Unit where
  toVal := toValN
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases he : e = 0 <;> simp_all [toValN]
  toVal_coe := fun _ => rfl
  baseStep := fun _ _ _ => False
  fillItem := fillN
  fillItem_inj := fun {Ki} => fillN_inj Ki
  fillItem_val := fillN_val
  fillItem_no_val_inj := fun k₁ k₂ h1 h2 h => fillN_nvi _ _ k₁ k₂ h1 h2 h
  val_stuck := by intro e σ obs e' σ' eₜ h; exact h.elim
  base_ctx_step_val := by intro Ki e σ obs e' σ' eₜ h; exact h.elim
abbrev iΛE := @EctxItemLanguage.instEctxLanguage Nat Unit Unit Unit Bool iLang
abbrev iΛ := @EctxLanguage.instLanguage Nat Unit Unit Unit _ iΛE

/-- IrisGS over any language with a constant state interpretation. -/
@[reducible] noncomputable def mkG {Expr State Obs Val : Type} [Language Expr State Obs Val]
    [x : InvGS_gen .hasNoLC CGF] (si : IProp CGF) : IrisGS_gen .hasNoLC Expr CGF :=
  { invGS := x, stateInterp := fun _ _ _ _ => si, numLatersPerStep := fun _ => 0,
    forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }

theorem v3_irred : ¬ PrimStep.ReducibleNoObs (Expr := Nat) (State := Unit) (Obs := Unit) ((3 : Nat), ()) := by
  rintro ⟨_, _, _, ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩⟩ <;> change (3 : Nat) = _ at h <;> exact absurd h (by decide)

/-- With state interpretation True, the total WP of the stuck expression 3 (not stuck-allowed) gives |={E,∅}=> False. -/
theorem twp3 [InvGS_gen .hasNoLC CGF] {E : CoPset} {Φ : Bool → IProp CGF} :
    letI := mkI iprop(True); (WP (3 : Nat) @ Stuckness.NotStuck ; E [{ Φ }] : IProp CGF) ⊢ |={E,∅}=> ⌜False⌝ := by
  letI := mkI iprop(True)
  refine twp.unfold.mp.trans ?_
  refine (forall_elim ()).trans ((forall_elim 0).trans ((forall_elim []).trans ((forall_elim 0).trans ?_)))
  refine (sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans ?_)
  exact BIFUpdate.mono (sep_elim_left.trans (pure_mono v3_irred))
end W7c3
open W7c3
-- `Iris.twp.bind_inv` idx 9: necessary
theorem w7c3_24 : ¬ drop0% Iris.twp.bind_inv 9 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI iprop(True)
    exact ((true_intro.trans (twp.value' (Φ := fun _ => iprop(True)) (v := true))).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ (fun _ => vT) .NotStuck ⊤ 3 (fun _ => iprop(True)))).trans twp3

namespace W7c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic

theorem v3_nostep {σ : Unit} {κ : List Unit} {c' : Nat × Unit × List Nat} :
    ¬ vLang.toPrimStep.primStep ((3 : Nat), σ) κ c' := by
  rintro ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩ <;> change (3 : Nat) = _ at h <;> exact absurd h (by decide)

theorem v3_irr : ¬ PrimStep.Reducible (Expr := Nat) (State := Unit) (Obs := List Unit) ((3 : Nat), ()) := by
  rintro ⟨_, _, _, _, hs⟩; exact v3_nostep hs

theorem v2_step : vLang.toPrimStep.primStep ((2 : Nat), ()) [()] (vF, (), []) := And.intro (Or.inl ⟨rfl, rfl⟩) rfl

/-- With state interpretation True, WP of the stuck expression 3 (not stuck-allowed) gives |={E,∅}=> False. -/
theorem wp3 [InvGS_gen .hasNoLC CGF] {E : CoPset} {Φ : Bool → IProp CGF} :
    letI := mkI iprop(True); (WP (3 : Nat) @ Stuckness.NotStuck ; E {{ Φ }} : IProp CGF) ⊢ |={E,∅}=> ⌜False⌝ := by
  letI := mkI iprop(True)
  refine wp_unfold.mp.trans ?_
  refine (forall_elim ()).trans ((forall_elim 0).trans ((forall_elim []).trans ((forall_elim []).trans
    ((forall_elim 0).trans ?_))))
  refine (sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans ?_)
  exact BIFUpdate.mono (sep_elim_left.trans (pure_mono v3_irr))

/-- Total WP of 2 (which has a step with an observation) is refutable. -/
theorem twp2 [InvGS_gen .hasNoLC CGF] {E : CoPset} {Φ : Bool → IProp CGF} :
    letI := mkI iprop(True); (WP (2 : Nat) @ Stuckness.NotStuck ; E [{ Φ }] : IProp CGF) ⊢ |={E}=> ⌜False⌝ := by
  letI := mkI iprop(True)
  refine twp.unfold.mp.trans ?_
  refine (forall_elim ()).trans ((forall_elim 0).trans ((forall_elim []).trans ((forall_elim 0).trans ?_)))
  refine (sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans ?_)
  refine (BIFUpdate.mono (sep_elim_right.trans ((forall_elim [()]).trans ((forall_elim vF).trans
    ((forall_elim ()).trans ((forall_elim []).trans ?_)))))).trans fupd_trans
  exact (sep_emp.2.trans (sep_mono .rfl (pure_intro v2_step))).trans (wand_elim_left.trans
    (BIFUpdate.mono (sep_elim_left.trans (pure_mono (fun e => List.cons_ne_nil _ _ e)))))

/-- With MaybeStuck, the total WP of the stuck expression 3 holds. -/
theorem twp3m [InvGS_gen .hasNoLC CGF] {E : CoPset} {Φ : Bool → IProp CGF} :
    letI := mkI iprop(True); ⊢ (WP (3 : Nat) @ Stuckness.MaybeStuck ; E [{ Φ }] : IProp CGF) := by
  letI := mkI iprop(True)
  refine Entails.trans ?_ twp.unfold.mpr
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
    wand_intro (sep_elim_left.trans ((emp_sep.2.trans (sep_mono (pure_intro trivial)
      (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
        wand_intro (sep_elim_right.trans (pure_elim' fun hs => absurd hs v3_nostep))))).trans
      (fupd_mask_intro_discard LawfulSet.empty_subset)))

/-- With MaybeStuck, WP of the stuck expression 3 holds. -/
theorem wp3m [InvGS_gen .hasNoLC CGF] {E : CoPset} {Φ : Bool → IProp CGF} :
    letI := mkI iprop(True); ⊢ (WP (3 : Nat) @ Stuckness.MaybeStuck ; E {{ Φ }} : IProp CGF) := by
  letI := mkI iprop(True)
  refine Entails.trans ?_ wp_unfold.mpr
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
    wand_intro (sep_elim_left.trans ((emp_sep.2.trans (sep_mono (pure_intro trivial)
      (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
        wand_intro (sep_elim_right.trans (pure_elim' fun hs => absurd hs v3_nostep))))).trans
      (fupd_mask_intro_discard LawfulSet.empty_subset)))
end W7c3
open W7c3
-- `Iris.wp_bind_inv` idx 9: necessary
theorem w7c3_43 : ¬ drop0% Iris.wp_bind_inv 9 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI iprop(True)
    exact ((true_intro.trans (wp_value' (Φ := fun _ => iprop(True)) (v := true))).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ (fun _ => vT) .NotStuck ⊤ 3 (fun _ => iprop(True)))).trans wp3
-- `Iris.wp_bind_iff` idx 9: necessary
theorem w7c3_41 : ¬ drop0% Iris.wp_bind_iff 9 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI iprop(True)
    exact ((true_intro.trans (wp_value' (Φ := fun _ => iprop(True)) (v := true))).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ (fun _ => vT) .NotStuck ⊤ 3 (fun _ => iprop(True))).mpr).trans wp3
-- `Iris.ProgramLogic.twp.lift_pure_det_step_no_fork` idx 14: necessary
theorem w7c3_14 : ¬ drop0% Iris.ProgramLogic.twp.lift_pure_det_step_no_fork 14 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI iprop(True)
    exact (((true_intro.trans (twp.value' (Φ := fun _ => iprop(True)) (v := true))).trans fupd_intro).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ 3 vT (fun _ => iprop(True)) inferInstance
        (fun _ _ _ _ _ hs => absurd hs v3_nostep))).trans twp3
-- `Iris.ProgramLogic.twp.lift_pure_det_step_no_fork` idx 15: necessary
theorem w7c3_15 : ¬ drop0% Iris.ProgramLogic.twp.lift_pure_det_step_no_fork 15 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact (((true_intro.trans (twp.value' (Φ := fun _ => iprop(True)) (v := true))).trans fupd_intro).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ 2 vT (fun _ => iprop(True)) inferInstance
        (fun _ => ⟨vF, (), [], And.intro (Or.inl ⟨rfl, rfl⟩) rfl⟩))).trans twp2
-- `Iris.ProgramLogic.twp.lift_pure_step_no_fork` idx 14: necessary
theorem w7c3_13 : ¬ drop0% Iris.ProgramLogic.twp.lift_pure_step_no_fork 14 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    refine (((forall_intro fun _ => forall_intro fun e₂ => forall_intro fun _ => forall_intro fun _ =>
      BI.imp_intro (pure_elim_right fun hs => ?_)).trans fupd_intro).trans
      (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ 2 (fun _ => iprop(True)) inferInstance
        (fun _ => ⟨vF, (), [], And.intro (Or.inl ⟨rfl, rfl⟩) rfl⟩))).trans twp2
    rcases hs with ⟨⟨_, he⟩ | ⟨he, _⟩, _⟩
    · change e₂ = 0 at he
      subst he
      exact true_intro.trans (twp.value' (Φ := fun _ => iprop(True)) (v := false))
    · change (2 : Nat) = 4 at he
      exact absurd he (by decide)
-- `Iris.twp.stuck_mono` idx 13: necessary
theorem w7c3_28 : ¬ drop0% Iris.twp.stuck_mono 13 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI iprop(True)
    exact (twp3m.trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .MaybeStuck .NotStuck ⊤ 3
      (fun _ => iprop(True)))).trans twp3
-- `Iris.wp_stuck_mono` idx 13: necessary
theorem w7c3_45 : ¬ drop0% Iris.wp_stuck_mono 13 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI iprop(True)
    exact (wp3m.trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .MaybeStuck .NotStuck ⊤ 3
      (fun _ => iprop(True)))).trans wp3

namespace W7c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic
theorem app {PROP : Type} [BI PROP] {P Q : PROP} (H : ⊢ P -∗ Q) (HP : ⊢ P) : ⊢ Q :=
  (emp_sep.2.trans (sep_mono H HP)).trans wand_elim_left
end W7c3
open W7c3
-- `Iris.twp.strong_mono` idx 15: necessary
theorem w7c3_20 : ¬ drop0% Iris.twp.strong_mono 15 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI iprop(True)
    exact (app (app (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .MaybeStuck .NotStuck ⊤ ⊤ 3
      (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ h => h)) twp3m)
      (forall_intro fun _ => wand_intro (sep_elim_right.trans fupd_intro))).trans twp3
-- `Iris.wp_strong_mono` idx 15: necessary
theorem w7c3_34 : ¬ drop0% Iris.wp_strong_mono 15 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI iprop(True)
    exact (app (app (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .MaybeStuck .NotStuck ⊤ ⊤ 3
      (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ h => h)) wp3m)
      (forall_intro fun _ => wand_intro (sep_elim_right.trans fupd_intro))).trans wp3
-- `Iris.ProgramLogic.twp.lift_base_step` idx 13: necessary
theorem w7c3_3 : ¬ drop0% Iris.ProgramLogic.twp.lift_base_step 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := @mkG Nat Unit Unit Unit iΛ _ iprop(False)
    exact (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      wand_intro (sep_elim_right.trans false_elim)).trans
      ((@h .hasNoLC Nat _ Unit Unit Unit iΛE CGF _ .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))).trans
        (twp.value_fupd' (Λ := iΛ) (v := ())).mp)
-- `Iris.ProgramLogic.twp.lift_atomic_base_step` idx 13: necessary
theorem w7c3_6 : ¬ drop0% Iris.ProgramLogic.twp.lift_atomic_base_step 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := @mkG Nat Unit Unit Unit iΛ _ iprop(False)
    exact (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      wand_intro (sep_elim_right.trans false_elim)).trans
      ((@h .hasNoLC Nat _ Unit Unit Unit iΛE CGF _ .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))).trans
        (twp.value_fupd' (Λ := iΛ) (v := ())).mp)
-- `Iris.ProgramLogic.twp.lift_atomic_base_step_no_fork` idx 13: necessary
theorem w7c3_7 : ¬ drop0% Iris.ProgramLogic.twp.lift_atomic_base_step_no_fork 13 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := @mkG Nat Unit Unit Unit iΛ _ iprop(False)
    exact (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      wand_intro (sep_elim_right.trans false_elim)).trans
      ((@h .hasNoLC Nat _ Unit Unit Unit iΛE CGF _ .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝))).trans
        (twp.value_fupd' (Λ := iΛ) (v := ())).mp)
-- `Iris.ProgramLogic.twp.lift_pure_base_step_no_fork` idx 14: necessary
theorem w7c3_4 : ¬ drop0% Iris.ProgramLogic.twp.lift_pure_base_step_no_fork 14 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := @mkG Nat Unit Unit Unit iΛ _ iprop(True)
    exact ((forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      BI.imp_intro (pure_elim_right fun hs => (hs : False).elim)).trans fupd_intro).trans
      ((@h .hasNoLC Nat _ Unit Unit Unit iΛE CGF _ .NotStuck ⊤ 0 (fun _ => iprop(⌜False⌝)) inferInstance
        (fun _ _ _ _ _ hs => (hs : False).elim)).trans (twp.value_fupd' (Λ := iΛ) (v := ())).mp)

namespace W7c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic
theorem nil_nostep {σ : Unit} {κ : List Unit} {ρ : List Nat × Unit} : ¬ Language.Step (Λ := vLang) ([], σ) κ ρ := by
  intro hs
  generalize hb : (([] : List Nat), σ) = b at hs
  cases hs with
  | atomic H t₁ t₂ => have := congrArg Prod.fst hb; simp at this

theorem tp_nil [InvGS_gen .hasNoLC CGF] :
    letI := mkI iprop(True); ⊢ (twptp.get (Λ := vLang) [] : IProp CGF) := by
  letI := mkI iprop(True)
  refine Entails.trans ?_ (twptp.unfold []).mpr
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
    forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      wand_intro (sep_elim_right.trans (pure_elim' fun hs => absurd hs nil_nostep))

theorem tp_two [InvGS_gen .hasNoLC CGF] :
    letI := mkI iprop(True); (twptp.get (Λ := vLang) [2] : IProp CGF) ⊢ |={⊤}=> ⌜False⌝ := by
  letI := mkI iprop(True)
  refine (twptp.unfold [2]).mp.trans ?_
  refine (forall_elim [vF]).trans ((forall_elim ()).trans ((forall_elim 0).trans ((forall_elim [()]).trans
    ((forall_elim []).trans ((forall_elim ()).trans ((forall_elim 0).trans ?_))))))
  refine (sep_emp.2.trans (sep_mono .rfl (pure_intro (Language.Step.atomic v2_step [] [])))).trans
    (wand_elim_left.trans ?_)
  refine (sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans ?_)
  exact BIFUpdate.mono (exists_elim fun _ => sep_elim_left.trans (pure_mono (fun e => List.cons_ne_nil _ _ e)))
end W7c3
open W7c3

-- `Iris.ProgramLogic.twptp.permutation` idx 10: necessary
theorem w7c3_1 : ¬ drop0% Iris.ProgramLogic.twptp.permutation 10 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact (tp_nil.trans (@h Nat Unit Unit Bool vLang .hasNoLC CGF _ [] [2])).trans tp_two
-- `Iris.twp.bind` idx 9: necessary
theorem w7c3_23 : ¬ drop0% Iris.twp.bind 9 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact (twp3m.trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ (fun x => if x = 3 then vF else x) .MaybeStuck ⊤ 3
      (fun _ => iprop(⌜False⌝)))).trans twp.value_fupd'.mp
-- `Iris.wp_bind` idx 9: necessary
theorem w7c3_42 : ¬ drop0% Iris.wp_bind 9 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := mkI iprop(True)
    exact (wp3m.trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ (fun x => if x = 3 then vF else x) .MaybeStuck ⊤ 3
      (fun _ => iprop(⌜False⌝)))).trans wp_value_fupd'.mp
-- `Iris.ProgramLogic.twp.lift_pure_det_base_step_no_fork` idx 16: necessary
theorem w7c3_8 : ¬ drop0% Iris.ProgramLogic.twp.lift_pure_det_base_step_no_fork 16 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := @mkG Nat Unit Unit Unit iΛ _ iprop(True)
    refine ((true_intro.trans (twp.value' (Λ := iΛ) (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(True)) (v := ()))).trans
      (@h .hasNoLC Nat _ Unit Unit Unit iΛE CGF _ .NotStuck ⊤ 1 0 (fun _ => iprop(True)) inferInstance rfl
        (fun _ _ _ _ _ hs => (hs : False).elim))).trans ((twp.unfold (Λ := iΛ)).mp.trans ?_)
    refine (forall_elim ()).trans ((forall_elim 0).trans ((forall_elim []).trans ((forall_elim 0).trans ?_)))
    refine (sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans ?_)
    exact BIFUpdate.mono (sep_elim_left.trans (pure_mono fun ⟨_, _, _, hs⟩ => by revert hs; generalize (1 : Nat) = x; intro hs; cases hs <;> assumption))

namespace W7c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic
/-- Like iLang, but 2 base-steps to the value 0 with any observation. -/
@[instance_reducible] def jLang : EctxItemLanguage Nat Bool Unit Unit Unit where
  toVal := toValN
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases he : e = 0 <;> simp_all [toValN]
  toVal_coe := fun _ => rfl
  baseStep := fun c _ c' => c.1 = 2 ∧ c'.1 = 0 ∧ c'.2.2 = []
  fillItem := fillN
  fillItem_inj := fun {Ki} => fillN_inj Ki
  fillItem_val := fillN_val
  fillItem_no_val_inj := fun k₁ k₂ h1 h2 h => fillN_nvi _ _ k₁ k₂ h1 h2 h
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    have h1 : e = 2 := h.1
    subst h1; rfl
  base_ctx_step_val := by
    intro Ki e σ obs e' σ' eₜ h
    have h1 : fillN Ki e = 2 := h.1
    exfalso
    cases Ki
    · simp [fillN] at h1; omega
    · by_cases he : e = 1 <;> simp [fillN, he] at h1 <;> omega
abbrev jΛE := @EctxItemLanguage.instEctxLanguage Nat Unit Unit Unit Bool jLang
abbrev jΛ := @EctxLanguage.instLanguage Nat Unit Unit Unit _ jΛE

theorem j2_step : jΛ.toPrimStep.primStep ((2 : Nat), ()) [()] ((0 : Nat), (), []) :=
  @Iris.ProgramLogic.EctxLanguage.primStep_of_baseStep _ _ _ _ _ jΛE 2 () [()] 0 () []
    (And.intro rfl (And.intro rfl rfl))
end W7c3
open W7c3

-- `Iris.ProgramLogic.twp.lift_pure_det_base_step_no_fork` idx 17: necessary
theorem w7c3_9 : ¬ drop0% Iris.ProgramLogic.twp.lift_pure_det_base_step_no_fork 17 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := @mkG Nat Unit Unit Unit jΛ _ iprop(True)
    refine ((true_intro.trans (twp.value' (Λ := jΛ) (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(True)) (v := ()))).trans
      (@h .hasNoLC Nat _ Unit Unit Unit jΛE CGF _ .NotStuck ⊤ 2 0 (fun _ => iprop(True)) inferInstance rfl
        (fun _ => ⟨0, (), [], And.intro rfl (And.intro rfl rfl)⟩))).trans ((twp.unfold (Λ := jΛ)).mp.trans ?_)
    refine (forall_elim ()).trans ((forall_elim 0).trans ((forall_elim []).trans ((forall_elim 0).trans ?_)))
    refine (sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans ?_)
    refine (BIFUpdate.mono (sep_elim_right.trans ((forall_elim [()]).trans ((forall_elim (0 : Nat)).trans
      ((forall_elim ()).trans ((forall_elim []).trans ?_)))))).trans fupd_trans
    exact (sep_emp.2.trans (sep_mono .rfl (pure_intro j2_step))).trans (wand_elim_left.trans
      (BIFUpdate.mono (sep_elim_left.trans (pure_mono (fun e => List.cons_ne_nil _ _ e)))))
-- `Iris.ProgramLogic.twp.lift_pure_base_step_no_fork` idx 15: necessary
theorem w7c3_5 : ¬ drop0% Iris.ProgramLogic.twp.lift_pure_base_step_no_fork 15 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => by
    letI := @mkG Nat Unit Unit Unit jΛ _ iprop(True)
    refine (((forall_intro fun _ => forall_intro fun e₂ => forall_intro fun _ => forall_intro fun _ =>
      BI.imp_intro (pure_elim_right fun hs => ?_)).trans fupd_intro).trans
      (@h .hasNoLC Nat _ Unit Unit Unit jΛE CGF _ .NotStuck ⊤ 2 (fun _ => iprop(True)) inferInstance
        (fun _ => ⟨0, (), [], And.intro rfl (And.intro rfl rfl)⟩))).trans ((twp.unfold (Λ := jΛ)).mp.trans ?_)
    · have he : e₂ = 0 := hs.2.1
      subst he
      exact true_intro.trans (twp.value' (Λ := jΛ) (Φ := fun _ => iprop(True)) (v := ()))
    refine (forall_elim ()).trans ((forall_elim 0).trans ((forall_elim []).trans ((forall_elim 0).trans ?_)))
    refine (sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans ?_)
    refine (BIFUpdate.mono (sep_elim_right.trans ((forall_elim [()]).trans ((forall_elim (0 : Nat)).trans
      ((forall_elim ()).trans ((forall_elim []).trans ?_)))))).trans fupd_trans
    exact (sep_emp.2.trans (sep_mono .rfl (pure_intro j2_step))).trans (wand_elim_left.trans
      (BIFUpdate.mono (sep_elim_left.trans (pure_mono (fun e => List.cons_ne_nil _ _ e)))))

namespace W7c3
open Iris Iris.BI Iris.Std Iris.OFE Iris.ProgramLogic
theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩
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

/-- State interpretation ownE ⊤: at mask ⊤ every non-value total WP holds (the tokens clash). -/
theorem twp3top [InvGS_gen .hasNoLC CGF] {Φ : Bool → IProp CGF} :
    letI := mkI (ownE ⊤); ⊢ (WP (3 : Nat) @ Stuckness.NotStuck ; ⊤ [{ Φ }] : IProp CGF) := by
  letI := mkI (ownE ⊤)
  refine Entails.trans ?_ twp.unfold.mpr
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
    wand_intro (sep_elim_right.trans ((own_conf ∅).trans (BIFUpdate.mono false_elim)))

theorem wp3top [InvGS_gen .hasNoLC CGF] {Φ : Bool → IProp CGF} :
    letI := mkI (ownE ⊤); ⊢ (WP (3 : Nat) @ Stuckness.NotStuck ; ⊤ {{ Φ }} : IProp CGF) := by
  letI := mkI (ownE ⊤)
  refine Entails.trans ?_ wp_unfold.mpr
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
    wand_intro (sep_elim_right.trans ((own_conf ∅).trans (BIFUpdate.mono false_elim)))

/-- ... while at mask ∅ the total WP of the stuck 3 is refutable (open the whole mask first). -/
theorem twp3_empty [InvGS_gen .hasNoLC CGF] {Φ : Bool → IProp CGF} :
    letI := mkI (ownE ⊤); (⊢ (WP (3 : Nat) @ Stuckness.NotStuck ; ∅ [{ Φ }] : IProp CGF)) →
      ⊢ (iprop(|={⊤,∅}=> ⌜False⌝) : IProp CGF) := fun H => by
  letI := mkI (ownE ⊤)
  have H' := (H.trans twp.unfold.mp).trans ((forall_elim ()).trans ((forall_elim 0).trans
    ((forall_elim []).trans (forall_elim 0))))
  exact own_open.trans ((BIFUpdate.mono ((emp_sep.2.trans (sep_mono H' .rfl)).trans (wand_elim_left.trans
    (BIFUpdate.mono (sep_elim_left.trans (pure_mono v3_irred)))))).trans fupd_trans)

theorem wp3_empty [InvGS_gen .hasNoLC CGF] {Φ : Bool → IProp CGF} :
    letI := mkI (ownE ⊤); (⊢ (WP (3 : Nat) @ Stuckness.NotStuck ; ∅ {{ Φ }} : IProp CGF)) →
      ⊢ (iprop(|={⊤,∅}=> ⌜False⌝) : IProp CGF) := fun H => by
  letI := mkI (ownE ⊤)
  have H' := (H.trans wp_unfold.mp).trans ((forall_elim ()).trans ((forall_elim 0).trans
    ((forall_elim []).trans ((forall_elim []).trans (forall_elim 0)))))
  exact own_open.trans ((BIFUpdate.mono ((emp_sep.2.trans (sep_mono H' .rfl)).trans (wand_elim_left.trans
    (BIFUpdate.mono (sep_elim_left.trans (pure_mono v3_irr)))))).trans fupd_trans)
end W7c3
open W7c3
-- `Iris.twp.mask_mono` idx 13: necessary
theorem w7c3_29 : ¬ drop0% Iris.twp.mask_mono 13 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI (ownE ⊤)
    exact twp3_empty (twp3top.trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ ∅ 3 (fun _ => iprop(True))))
-- `Iris.wp_mask_mono` idx 13: necessary
theorem w7c3_46 : ¬ drop0% Iris.wp_mask_mono 13 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI (ownE ⊤)
    exact wp3_empty (wp3top.trans (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck ⊤ ∅ 3 (fun _ => iprop(True))))
-- `Iris.twp.strong_mono` idx 16: necessary
theorem w7c3_21 : ¬ drop0% Iris.twp.strong_mono 16 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI (ownE ⊤)
    exact twp3_empty (app (app (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck .NotStuck ⊤ ∅ 3
      (fun _ => iprop(True)) (fun _ => iprop(True)) (fun ⟨e, _⟩ => Stuckness.noConfusion e)) twp3top)
      (forall_intro fun _ => wand_intro (sep_elim_right.trans fupd_intro)))
-- `Iris.wp_strong_mono` idx 16: necessary
theorem w7c3_35 : ¬ drop0% Iris.wp_strong_mono 16 := fun h =>
  fupd_false ⊤ ∅ fun {_} => by
    letI := mkI (ownE ⊤)
    exact wp3_empty (app (app (@h .hasNoLC Nat Unit Unit Bool vLang CGF _ .NotStuck .NotStuck ⊤ ∅ 3
      (fun _ => iprop(True)) (fun _ => iprop(True)) (fun ⟨e, _⟩ => Stuckness.noConfusion e)) wp3top)
      (forall_intro fun _ => wand_intro (sep_elim_right.trans fupd_intro)))
