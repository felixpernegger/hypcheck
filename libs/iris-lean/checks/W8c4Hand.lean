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

namespace W8c4
open Iris Iris.BI Iris.Std Iris.ProofMode Iris.OFE

abbrev UIdx : Iris.BI.BiIndex := { car := Nat, rel := inferInstance }
abbrev MP := MonPred UIdx SiProp
abbrev sT : SiProp := iprop(True)
abbrev sF : SiProp := iprop(False)
abbrev eT : MP := MonPred.embed sT
abbrev eF : MP := MonPred.embed sF
/-- Monotone non-objective predicate 1 <= k over the Nat index. -/
def mp1 : MP := ⟨fun k => iprop(⌜(1 : Nat) ≤ k⌝), fun hij _ h => Nat.le_trans h hij⟩
/-- MakeMonPredAt for any monPred at its own value. -/
theorem mk {d} {i} (P : MP) : MakeMonPredAt d i P (P.monPred_at i) := ⟨⟨fun _ h => h, fun _ h => h⟩⟩
/-- MakeEmbed at the embedding itself. -/
theorem mkE {X : SiProp} : MakeEmbed X (MonPred.embed X : MP) := ⟨⟨fun _ _ h => h, fun _ _ h => h⟩⟩
/-- Identity basic update on SiProp (lawful). -/
@[reducible] def idBupd : BIUpdate SiProp where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h
/-- Wand eT -* eT (or eF -* eF) holds at every index and step. -/
theorem wTT (i : Nat) (n : Nat) : (iprop(eT -∗ eT) : MP).monPred_at i |>.holds n :=
  SiProp.forall_holds.2 fun _ _ _ _ _ _ h => h
theorem wFF (i : Nat) (n : Nat) : (iprop(eF -∗ eF) : MP).monPred_at i |>.holds n :=
  SiProp.forall_holds.2 fun _ _ _ _ _ _ h => h
theorem iTT (i : Nat) (n : Nat) : (iprop(eT → eT) : MP).monPred_at i |>.holds n :=
  SiProp.forall_holds.2 fun _ _ _ _ _ _ h => h
/-- Wand eT -* eF fails at index i, step n. -/
theorem wTF (i n : Nat) (w : (iprop(eT -∗ eF) : MP).monPred_at i |>.holds n) : False :=
  SiProp.forall_holds.1 w i n (Nat.le_refl n) (Nat.le_refl i) n (Nat.le_refl n) trivial
theorem iTF (i n : Nat) (w : (iprop(eT → eF) : MP).monPred_at i |>.holds n) : False :=
  SiProp.forall_holds.1 w i n (Nat.le_refl n) (Nat.le_refl i) n (Nat.le_refl n) trivial

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF
abbrev MI := MonPred UIdx (IProp CGF)

/-- fupd soundness with arbitrary masks (copied from W6c1). -/
theorem fupd_false (E1 E2 : CoPset) (H : ∀ [InvGS_gen .hasNoLC CGF], ⊢ (iprop(|={E1,E2}=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := E1) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))

theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩

/-- No mask-opening update from the empty mask to top is provable (copied from W6c1). -/
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

/-- emp entails a top-mask update of True. -/
theorem fT [InvGS_gen .hasNoLC CGF] (E : CoPset) : (emp : IProp CGF) ⊢ iprop(|={E}=> True) :=
  true_intro.trans fupd_intro

/-- MakeMonPredAt over IProp at the predicate's own value. -/
theorem mkI {d} {i} (P : MI) : MakeMonPredAt d i P (P.monPred_at i) := ⟨⟨.rfl, .rfl⟩⟩

/-- emp entails True * (False -* X) in IProp. -/
theorem tfw [InvGS_gen .hasNoLC CGF] (X : IProp CGF) : (emp : IProp CGF) ⊢ iprop(True ∗ (⌜False⌝ -∗ X)) :=
  emp_sep.2.trans (sep_mono true_intro (wand_intro (sep_elim_right.trans (pure_elim' False.elim))))

/-- From emp |- A -* B -* Q and emp |- A, emp |- B get emp |- Q. -/
theorem app2 {PROP : Type _} [BI PROP] {A B Q : PROP} (W : (emp : PROP) ⊢ A -∗ B -∗ Q)
    (hA : (emp : PROP) ⊢ A) (hB : (emp : PROP) ⊢ B) : (emp : PROP) ⊢ Q :=
  (emp_sep.2.trans (sep_mono ((emp_sep.2.trans (sep_mono W hA)).trans wand_elim_left) hB)).trans wand_elim_left

/-- MakeEmbed over IProp at the embedding itself. -/
theorem mkEI {X : IProp CGF} : MakeEmbed X (MonPred.embed X : MI) := ⟨⟨fun _ => .rfl, fun _ => .rfl⟩⟩

theorem wT [InvGS_gen .hasNoLC CGF] : (emp : IProp CGF) ⊢ iprop(∀ _x : Unit, True -∗ True) :=
  forall_intro fun _ => wand_intro true_intro

/-- (True -* R) entails R in any BI. -/
theorem wtrue {PROP : Type _} [BI PROP] {R : PROP} : iprop(True -∗ R) ⊢ R :=
  (sep_emp.2.trans (sep_mono .rfl true_intro)).trans wand_elim_left

theorem accN [InvGS_gen .hasNoLC CGF] (E : CoPset) : (emp : IProp CGF) ⊢
    accessor (fupd E E) (fupd E E) (fun _ : Unit => iprop(True)) (fun _ => iprop(True)) (fun _ => none) :=
  (((emp_sep.2.trans (sep_mono true_intro (wand_intro (sep_elim_left.trans fupd_intro)))).trans
    (exists_intro (Ψ := fun _ : Unit => iprop(True ∗ (True -∗ |={E}=> emp))) ())).trans fupd_intro)
theorem accS [InvGS_gen .hasNoLC CGF] (E : CoPset) : (emp : IProp CGF) ⊢
    accessor (fupd E E) (fupd E E) (fun _ : Unit => iprop(True)) (fun _ => iprop(True)) (fun _ => some iprop(True)) :=
  (((emp_sep.2.trans (sep_mono true_intro (wand_intro (true_intro.trans fupd_intro)))).trans
    (exists_intro (Ψ := fun _ : Unit => iprop(True ∗ (True -∗ |={E}=> True))) ())).trans fupd_intro)
theorem accF [InvGS_gen .hasNoLC CGF] (g : Option (IProp CGF)) : (emp : IProp CGF) ⊢
    accessor (fupd ∅ ∅) (fupd ∅ ⊤) (fun _ : Unit => iprop(True)) (fun _ => iprop(⌜False⌝)) (fun _ => g) :=
  ((emp_sep.2.trans (sep_mono true_intro (wand_intro (sep_elim_right.trans false_elim)))).trans
    (exists_intro (Ψ := fun _ : Unit => iprop(True ∗ (⌜False⌝ -∗ |={∅,⊤}=> (g.getD emp)))) ())).trans fupd_intro
noncomputable abbrev eTI : MI := MonPred.embed iprop(True)
noncomputable abbrev eFI : MI := MonPred.embed iprop(⌜False⌝)
theorem accV [InvGS_gen .hasNoLC CGF] (g : Unit → Option MI) :
    accessor (fupd ⊤ ⊤) (fupd ⊤ ⊤) (fun _ : Unit => eFI) (fun _ => eTI) g ⊢
      (MonPred.embed iprop(|={⊤}=> ⌜False⌝) : MI) := by
  unfold accessor
  have A : iprop(∃ x : Unit, eFI ∗ (eTI -∗ |={⊤}=> ((g x).getD emp))) ⊢ eFI :=
    exists_elim fun _ => sep_elim_left
  exact (BIFUpdate.mono A).trans (fun _ => .rfl)
/-- ElimAcc in MonPred with alpha' = embed False: holds since the accessor yields False. -/
theorem hvAcc [InvGS_gen .hasNoLC CGF] (g : Unit → Option MI) :
    ElimAcc True (fupd ⊤ ⊤) (fupd ⊤ ⊤) (fun _ : Unit => eFI) (fun _ => eTI) g
      (MonPred.embed iprop(|={⊤}=> ⌜False⌝) : MI) (fun _ => eTI) :=
  ⟨fun _ => wand_intro (wand_intro (sep_elim_right.trans (accV g)))⟩
/-- With beta' = embed True and masks (empty, empty), (empty, top), the accessor gives |={empty,top}=> R. -/
theorem accB [InvGS_gen .hasNoLC CGF] (g : MI) :
    accessor (fupd ∅ ∅) (fupd ∅ ⊤) (fun _ : Unit => eTI) (fun _ => eTI) (fun _ => some g) ⊢
      iprop(|={∅,⊤}=> g) := by
  unfold accessor
  have A : iprop(∃ x : Unit, eTI ∗ (eTI -∗ |={∅,⊤}=> g)) ⊢ iprop(|={∅,⊤}=> g) :=
    exists_elim fun _ => sep_elim_right.trans ((sep_emp.2.trans (sep_mono .rfl true_intro)).trans wand_elim_left)
  exact (BIFUpdate.mono A).trans BIFUpdate.trans
theorem accBn [InvGS_gen .hasNoLC CGF] :
    accessor (fupd ∅ ∅) (fupd ∅ ⊤) (fun _ : Unit => eTI) (fun _ => eTI) (fun _ => none) ⊢
      iprop(|={∅,⊤}=> emp) := by
  unfold accessor
  have A : iprop(∃ x : Unit, eTI ∗ (eTI -∗ |={∅,⊤}=> emp)) ⊢ iprop(|={∅,⊤}=> emp) :=
    exists_elim fun _ => sep_elim_right.trans ((sep_emp.2.trans (sep_mono .rfl true_intro)).trans wand_elim_left)
  exact (BIFUpdate.mono A).trans BIFUpdate.trans
/-- gamma' = embed False at top masks: the accessor gives |={top}=> False. -/
theorem accG [InvGS_gen .hasNoLC CGF] :
    accessor (fupd ⊤ ⊤) (fupd ⊤ ⊤) (fun _ : Unit => eTI) (fun _ => eTI) (fun _ => some eFI) ⊢
      (MonPred.embed iprop(|={⊤}=> ⌜False⌝) : MI) := by
  unfold accessor
  have A : iprop(∃ x : Unit, eTI ∗ (eTI -∗ |={⊤}=> eFI)) ⊢ iprop(|={⊤}=> eFI) :=
    exists_elim fun _ => sep_elim_right.trans ((sep_emp.2.trans (sep_mono .rfl true_intro)).trans wand_elim_left)
  exact ((BIFUpdate.mono A).trans BIFUpdate.trans).trans (fun _ => .rfl)

macro "fin " H:ident : tactic => `(tactic| first
  | exact $H 0 trivial
  | exact $H 0 ⟨trivial, trivial⟩
  | exact $H 0 (Or.inl trivial)
  | exact $H 0 (Or.inr trivial)
  | exact ($H 0 trivial).1
  | exact ($H 0 trivial).2
  | exact ($H 0 trivial).elim id id
  | exact ($H 0 ⟨trivial, trivial⟩).1
  | exact ($H 0 ⟨trivial, trivial⟩).2
  | exact ($H 0 ⟨trivial, trivial⟩).elim id id
  | exact ($H 0 (Or.inl trivial)).elim id id
  | exact $H 0 trivial 0 (Nat.le_refl 0) trivial
  | exact $H 0 ⟨trivial, fun _ _ h => h⟩
  | exact $H 1 trivial
  | exact $H 1 ⟨trivial, trivial⟩
  | exact $H 1 (Or.inr trivial)
  | exact ($H 1 trivial).elim id id
  | exact ($H 1 (Or.inr trivial)).elim id id
  | exact $H 0 (SiProp.exists_holds.2 ⟨(), trivial⟩)
  | exact $H 0 (SiProp.exists_holds.2 ⟨trivial, trivial⟩)
  | exact SiProp.forall_holds.1 ($H 0 trivial) trivial
  | exact $H 0 (SiProp.exists_holds.2 ⟨(0 : Nat), trivial⟩)
  | exact $H 0 (SiProp.forall_holds.2 fun _ => trivial)
  | exact $H 0 ⟨trivial, SiProp.forall_holds.2 fun _ => trivial⟩
  | exact SiProp.forall_holds.1 ($H 0 trivial) ()
  | exact SiProp.forall_holds.1 ($H 0 trivial) (0 : Nat)
  | exact SiProp.forall_holds.1 ($H 0 ⟨trivial, trivial⟩) (0 : Nat)
  | exact SiProp.forall_holds.1 ($H 0 (SiProp.forall_holds.2 fun _ => trivial)) (0 : Nat)
  | exact (SiProp.exists_holds.1 ($H 0 trivial)).elim fun _ h => h
  | exact (SiProp.exists_holds.1 ($H 0 ⟨trivial, trivial⟩)).elim fun _ h => h
  | exact (SiProp.exists_holds.1 ($H 0 (SiProp.exists_holds.2 ⟨(0 : Nat), trivial⟩))).elim fun _ h => h
  | exact wTF 0 0 ($H 0 trivial)
  | exact wTF 0 0 ($H 0 ⟨trivial, wTT 0 0⟩)
  | exact iTF 0 0 ($H 0 ⟨trivial, iTT 0 0⟩)
  | (have H0 := $H 0; simp at H0; done)
  | (have H1 := $H 1; simp at H1; done))

-- `Iris.ProofMode.IsBiIndexRel.is_bi_index_rel` idx 3: necessary (Nat index: 1 <= 0 fails)
theorem w8c4_0 : ¬ drop0% Iris.ProofMode.IsBiIndexRel.is_bi_index_rel 3 := fun h => by
  exact Nat.not_succ_le_zero 0 (@h UIdx (1 : Nat) (0 : Nat))
-- `Iris.ProofMode.FrameMonPredAt.frame_monPred_at` idx 8: necessary (MonPred over SiProp: R=Q=True, P=embed False)
theorem w8c4_1 : ¬ drop0% Iris.ProofMode.FrameMonPredAt.frame_monPred_at 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT eF sT); fin H
-- `Iris.ProofMode.asEmpValid_monPred_at` idx 7: necessary (P=embed False, Phi=False, phi=True: gives |- forall i, False)
theorem w8c4_2 : ¬ drop0% Iris.ProofMode.asEmpValid_monPred_at 7 := fun h => by
  have H := (@h UIdx SiProp _ .into True eF (fun _ => sF) (fun _ => mk eF)).as_emp_valid.1 rfl trivial; exact SiProp.forall_holds.1 (H 0 trivial) (0 : Nat)
-- `Iris.ProofMode.asEmpValid_monPred_at` idx 8: necessary (P=embed True (valid), Phi=False unconstrained)
theorem w8c4_3 : ¬ drop0% Iris.ProofMode.asEmpValid_monPred_at 8 := fun h => by
  have H := (@h UIdx SiProp _ .into True eT (fun _ => sF) ⟨⟨⟨fun _ _ => fun _ _ _ => trivial, fun h => nomatch h⟩⟩⟩).as_emp_valid.1 rfl trivial; exact SiProp.forall_holds.1 (H 0 trivial) (0 : Nat)
-- `Iris.ProofMode.asEmpValid_monPred_at_wand` idx 9: necessary (P=embed True, Q=embed False: |- forall i, True -* False)
theorem w8c4_4 : ¬ drop0% Iris.ProofMode.asEmpValid_monPred_at_wand 9 := fun h => by
  have H := (@h UIdx SiProp _ .into True eT eF (fun _ => sT) (fun _ => sF) (fun _ => mk eT) (fun _ => mk eF)).as_emp_valid.1 rfl trivial; exact SiProp.forall_holds.1 (H 0 trivial) (0 : Nat) 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.asEmpValid_monPred_at_wand` idx 10: necessary (P=Q=embed False (wand valid), Phi=True unconstrained, Psi=False)
theorem w8c4_5 : ¬ drop0% Iris.ProofMode.asEmpValid_monPred_at_wand 10 := fun h => by
  have H := (@h UIdx SiProp _ .into True eF eF (fun _ => sT) (fun _ => sF) ⟨⟨⟨fun _ _ => (fun i n _ => wFF i n), fun h => nomatch h⟩⟩⟩ (fun _ => mk eF)).as_emp_valid.1 rfl trivial; exact SiProp.forall_holds.1 (H 0 trivial) (0 : Nat) 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.asEmpValid_monPred_at_wand` idx 11: necessary (P=Q=embed True, Psi=False unconstrained)
theorem w8c4_6 : ¬ drop0% Iris.ProofMode.asEmpValid_monPred_at_wand 11 := fun h => by
  have H := (@h UIdx SiProp _ .into True eT eT (fun _ => sT) (fun _ => sF) ⟨⟨⟨fun _ _ => (fun i n _ => wTT i n), fun h => nomatch h⟩⟩⟩ (fun _ => mk eT)).as_emp_valid.1 rfl trivial; exact SiProp.forall_holds.1 (H 0 trivial) (0 : Nat) 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.asEmpValid_monPred_at_equiv` idx 9: necessary (P=embed True, Q=embed False)
theorem w8c4_7 : ¬ drop0% Iris.ProofMode.asEmpValid_monPred_at_equiv 9 := fun h => by
  have H := (@h UIdx SiProp _ .into True eT eF (fun _ => sT) (fun _ => sF) (fun _ => mk eT) (fun _ => mk eF)).as_emp_valid.1 rfl trivial; exact (SiProp.forall_holds.1 (H 0 trivial) (0 : Nat)).1 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.asEmpValid_monPred_at_equiv` idx 10: necessary (P=Q=embed False, Phi=True unconstrained)
theorem w8c4_8 : ¬ drop0% Iris.ProofMode.asEmpValid_monPred_at_equiv 10 := fun h => by
  have H := (@h UIdx SiProp _ .into True eF eF (fun _ => sT) (fun _ => sF) ⟨⟨⟨fun _ _ => wandIff_refl, fun h => nomatch h⟩⟩⟩ (fun _ => mk eF)).as_emp_valid.1 rfl trivial; exact (SiProp.forall_holds.1 (H 0 trivial) (0 : Nat)).1 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.asEmpValid_monPred_at_equiv` idx 11: necessary (P=Q=embed True, Psi=False unconstrained)
theorem w8c4_9 : ¬ drop0% Iris.ProofMode.asEmpValid_monPred_at_equiv 11 := fun h => by
  have H := (@h UIdx SiProp _ .into True eT eT (fun _ => sT) (fun _ => sF) ⟨⟨⟨fun _ _ => wandIff_refl, fun h => nomatch h⟩⟩⟩ (fun _ => mk eT)).as_emp_valid.1 rfl trivial; exact (SiProp.forall_holds.1 (H 0 trivial) (0 : Nat)).1 0 (Nat.le_refl 0) trivial
-- `Iris.ProofMode.fromAssumption_make_monPred_at_l` idx 8: necessary (P=embed True, assumption False)
theorem w8c4_10 : ¬ drop0% Iris.ProofMode.fromAssumption_make_monPred_at_l 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 0 eT sF ⟨Nat.le_refl 0⟩).1; fin H
-- `Iris.ProofMode.fromAssumption_make_monPred_at_l` idx 9: necessary (P = (1 <= k), i=0, j=1)
theorem w8c4_11 : ¬ drop0% Iris.ProofMode.fromAssumption_make_monPred_at_l 9 := fun h => by
  have H := (@h UIdx SiProp _ false (0 : Nat) (1 : Nat) mp1 (mp1.monPred_at 0) (mk mp1)).1; exact Nat.not_succ_le_zero 0 (H 0 (Nat.le_refl 1))
-- `Iris.ProofMode.fromAssumption_make_monPred_at_r` idx 9: necessary (P=embed False, assumption True)
theorem w8c4_12 : ¬ drop0% Iris.ProofMode.fromAssumption_make_monPred_at_r 9 := fun h => by
  have H := (@h UIdx SiProp _ false .in 0 0 eF sT ⟨Nat.le_refl 0⟩).1; fin H
-- `Iris.ProofMode.fromAssumption_make_monPred_at_r` idx 10: necessary (P = (1 <= k), i=1, j=0)
theorem w8c4_13 : ¬ drop0% Iris.ProofMode.fromAssumption_make_monPred_at_r 10 := fun h => by
  have H := (@h UIdx SiProp _ false .in (1 : Nat) (0 : Nat) mp1 (mp1.monPred_at 1) (mk mp1)).1; exact Nat.not_succ_le_zero 0 (H 0 (Nat.le_refl 1))
-- `Iris.ProofMode.fromAssumption_monPred_objectively` idx 6: necessary (P=embed True, Q=embed False)
theorem w8c4_14 : ¬ drop0% Iris.ProofMode.fromAssumption_monPred_objectively 6 := fun h => by
  have H := (@h UIdx SiProp _ false eT eF).1 0; fin H
-- `Iris.ProofMode.fromAssumption_monPred_subjectively` idx 7: necessary (P=embed True, Q=embed False)
theorem w8c4_15 : ¬ drop0% Iris.ProofMode.fromAssumption_monPred_subjectively 7 := fun h => by
  have H := (@h UIdx SiProp _ false .in eT eF).1 0; fin H
-- `Iris.ProofMode.fromModal_affinely_monPred_at` idx 11: necessary (P=embed False, Q=embed True, phi=True)
theorem w8c4_16 : ¬ drop0% Iris.ProofMode.fromModal_affinely_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () eF eT sT 0 (mk eT)).1 trivial; fin H
-- `Iris.ProofMode.fromModal_affinely_monPred_at` idx 12: necessary (P=Q=embed False, Q-at unconstrained := True)
theorem w8c4_17 : ¬ drop0% Iris.ProofMode.fromModal_affinely_monPred_at 12 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () eF eF sT 0 ⟨fun _ => fun _ _ h => h.2⟩).1 trivial; fin H
-- `Iris.ProofMode.fromModal_persistently_monPred_at` idx 11: necessary (P=embed False, Q=embed True, phi=True)
theorem w8c4_18 : ¬ drop0% Iris.ProofMode.fromModal_persistently_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () eF eT sT 0 (mk eT)).1 trivial; fin H
-- `Iris.ProofMode.fromModal_persistently_monPred_at` idx 12: necessary (P=Q=embed False, Q-at unconstrained := True)
theorem w8c4_19 : ¬ drop0% Iris.ProofMode.fromModal_persistently_monPred_at 12 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () eF eF sT 0 ⟨fun _ => fun _ _ h => h⟩).1 trivial; fin H
-- `Iris.ProofMode.fromModal_intuitionistically_monPred_at` idx 11: necessary (P=embed False, Q=embed True, phi=True)
theorem w8c4_20 : ¬ drop0% Iris.ProofMode.fromModal_intuitionistically_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () eF eT sT 0 (mk eT)).1 trivial; fin H
-- `Iris.ProofMode.fromModal_intuitionistically_monPred_at` idx 12: necessary (P=Q=embed False, Q-at unconstrained := True)
theorem w8c4_21 : ¬ drop0% Iris.ProofMode.fromModal_intuitionistically_monPred_at 12 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () eF eF sT 0 ⟨fun _ => fun _ _ h => h.2⟩).1 trivial; fin H
-- `Iris.ProofMode.fromModal_id_monPred_at` idx 11: necessary (P=embed False, Q=embed True, phi=True)
theorem w8c4_22 : ¬ drop0% Iris.ProofMode.fromModal_id_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () eF eT sT 0 (mk eT)).1 trivial; fin H
-- `Iris.ProofMode.fromModal_id_monPred_at` idx 12: necessary (P=Q=embed False, Q-at unconstrained := True)
theorem w8c4_23 : ¬ drop0% Iris.ProofMode.fromModal_id_monPred_at 12 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () eF eF sT 0 ⟨fun _ => fun _ _ h => h⟩).1 trivial; fin H
-- `Iris.ProofMode.fromLater_monPred_at` idx 12: necessary (n=0, P=embed False, Q=embed True)
theorem w8c4_24 : ¬ drop0% Iris.ProofMode.fromLater_monPred_at 12 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () 0 eF eT sT 0 (mk eT)).1 trivial; fin H
-- `Iris.ProofMode.fromLater_monPred_at` idx 13: necessary (n=0, P=Q=embed False, Q-at := True)
theorem w8c4_25 : ¬ drop0% Iris.ProofMode.fromLater_monPred_at 13 := fun h => by
  have H := (@h UIdx SiProp _ Unit True .in () 0 eF eF sT 0 ⟨fun _ => fun _ _ h => h⟩).1 trivial; fin H
-- `Iris.ProofMode.intoPure_monPred_at` idx 6: necessary (P=embed True, phi=False)
theorem w8c4_26 : ¬ drop0% Iris.ProofMode.intoPure_monPred_at 6 := fun h => by
  have H := (@h UIdx SiProp _ eT False 0).1; fin H
-- `Iris.ProofMode.intoPersistently_monPred_at` idx 8: necessary (P=embed True, Q=embed False)
theorem w8c4_27 : ¬ drop0% Iris.ProofMode.intoPersistently_monPred_at 8 := fun h => by
  have H := (@h UIdx SiProp _ false eT eF sF 0 (mk eF)).1; fin H
-- `Iris.ProofMode.intoPersistently_monPred_at` idx 9: necessary (P=Q=embed True, Q-at := False)
theorem w8c4_28 : ¬ drop0% Iris.ProofMode.intoPersistently_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ false eT eT sF 0 ⟨fun _ _ h => h⟩).1; fin H
-- `Iris.ProofMode.fromAnd_monPred_at` idx 9: necessary (P=embed False, Q1=Q2=embed True)
theorem w8c4_29 : ¬ drop0% Iris.ProofMode.fromAnd_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ eF eT eT sT sT 0 (mk eT) (mk eT)).1; fin H
-- `Iris.ProofMode.fromAnd_monPred_at` idx 10: necessary (P=Q1=embed False, Q2=True, Q1-at := True)
theorem w8c4_30 : ¬ drop0% Iris.ProofMode.fromAnd_monPred_at 10 := fun h => by
  have H := (@h UIdx SiProp _ eF eF eT sT sT 0 ⟨fun _ _ h => h.1⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.fromAnd_monPred_at` idx 11: necessary (P=Q2=embed False, Q1=True, Q2-at := True)
theorem w8c4_31 : ¬ drop0% Iris.ProofMode.fromAnd_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ eF eT eF sT sT 0 ⟨fun _ _ h => h.2⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.fromSep_monPred_at` idx 9: necessary (P=embed False, Q1=Q2=embed True)
theorem w8c4_32 : ¬ drop0% Iris.ProofMode.fromSep_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ eF eT eT sT sT 0 (mk eT) (mk eT)).1; fin H
-- `Iris.ProofMode.fromSep_monPred_at` idx 10: necessary (P=Q1=embed False, Q2=True, Q1-at := True)
theorem w8c4_33 : ¬ drop0% Iris.ProofMode.fromSep_monPred_at 10 := fun h => by
  have H := (@h UIdx SiProp _ eF eF eT sT sT 0 ⟨fun _ _ h => h.1⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.fromSep_monPred_at` idx 11: necessary (P=Q2=embed False, Q1=True, Q2-at := True)
theorem w8c4_34 : ¬ drop0% Iris.ProofMode.fromSep_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ eF eT eF sT sT 0 ⟨fun _ _ h => h.2⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.intoAnd_monPred_at` idx 10: necessary (P=embed True, Q1=Q2=embed False)
theorem w8c4_35 : ¬ drop0% Iris.ProofMode.intoAnd_monPred_at 10 := fun h => by
  have H := (@h UIdx SiProp _ false eT eF eF sF sF 0 (mk eF) (mk eF)).1; fin H
-- `Iris.ProofMode.intoAnd_monPred_at` idx 11: necessary (P=Q1=Q2=embed True, Q1-at := False)
theorem w8c4_36 : ¬ drop0% Iris.ProofMode.intoAnd_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ false eT eT eT sF sT 0 ⟨fun _ _ h => ⟨h, h⟩⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.intoAnd_monPred_at` idx 12: necessary (P=Q1=Q2=embed True, Q2-at := False)
theorem w8c4_37 : ¬ drop0% Iris.ProofMode.intoAnd_monPred_at 12 := fun h => by
  have H := (@h UIdx SiProp _ false eT eT eT sT sF 0 ⟨fun _ _ h => ⟨h, h⟩⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.intoSep_monPred_at` idx 9: necessary (P=embed True, Q1=Q2=embed False)
theorem w8c4_38 : ¬ drop0% Iris.ProofMode.intoSep_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ eT eF eF sF sF 0 (mk eF) (mk eF)).1; fin H
-- `Iris.ProofMode.intoSep_monPred_at` idx 10: necessary (P=Q1=Q2=embed True, Q1-at := False)
theorem w8c4_39 : ¬ drop0% Iris.ProofMode.intoSep_monPred_at 10 := fun h => by
  have H := (@h UIdx SiProp _ eT eT eT sF sT 0 ⟨fun _ _ h => ⟨h, h⟩⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.intoSep_monPred_at` idx 11: necessary (P=Q1=Q2=embed True, Q2-at := False)
theorem w8c4_40 : ¬ drop0% Iris.ProofMode.intoSep_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ eT eT eT sT sF 0 ⟨fun _ _ h => ⟨h, h⟩⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.fromOr_monPred_at` idx 9: necessary (P=embed False, Q1=Q2=embed True)
theorem w8c4_41 : ¬ drop0% Iris.ProofMode.fromOr_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ eF eT eT sT sT 0 (mk eT) (mk eT)).1; fin H
-- `Iris.ProofMode.fromOr_monPred_at` idx 10: necessary (P=Q1=Q2=embed False, Q1-at := True)
theorem w8c4_42 : ¬ drop0% Iris.ProofMode.fromOr_monPred_at 10 := fun h => by
  have H := (@h UIdx SiProp _ eF eF eF sT sF 0 ⟨fun _ _ h => h.elim id id⟩ (mk eF)).1; fin H
-- `Iris.ProofMode.fromOr_monPred_at` idx 11: necessary (P=Q1=Q2=embed False, Q2-at := True)
theorem w8c4_43 : ¬ drop0% Iris.ProofMode.fromOr_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ eF eF eF sF sT 0 ⟨fun _ _ h => h.elim id id⟩ (mk eF)).1; fin H
-- `Iris.ProofMode.intoOr_monPred_at` idx 9: necessary (P=embed True, Q1=Q2=embed False)
theorem w8c4_44 : ¬ drop0% Iris.ProofMode.intoOr_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ eT eF eF sF sF 0 (mk eF) (mk eF)).1; fin H
-- `Iris.ProofMode.intoOr_monPred_at` idx 10: necessary (P=Q1=embed True, Q2=False, Q1-at := False)
theorem w8c4_45 : ¬ drop0% Iris.ProofMode.intoOr_monPred_at 10 := fun h => by
  have H := (@h UIdx SiProp _ eT eT eF sF sF 0 ⟨fun _ _ h => Or.inl h⟩ (mk eF)).1; fin H
-- `Iris.ProofMode.intoOr_monPred_at` idx 11: necessary (P=Q2=embed True, Q1=False, Q2-at := False)
theorem w8c4_46 : ¬ drop0% Iris.ProofMode.intoOr_monPred_at 11 := fun h => by
  have H := (@h UIdx SiProp _ eT eF eT sF sF 0 ⟨fun _ _ h => Or.inr h⟩ (mk eF)).1; fin H
-- `Iris.ProofMode.intoLaterN_monPred_at` idx 9: necessary (n=0, P=embed True, Q=embed False)
theorem w8c4_47 : ¬ drop0% Iris.ProofMode.intoLaterN_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ false 0 eT eF sF 0 (mk eF)).1; fin H
-- `Iris.ProofMode.intoLaterN_monPred_at` idx 10: necessary (n=0, P=Q=embed True, Q-at := False)
theorem w8c4_48 : ¬ drop0% Iris.ProofMode.intoLaterN_monPred_at 10 := fun h => by
  have H := (@h UIdx SiProp _ false 0 eT eT sF 0 ⟨fun _ _ h => h⟩).1; fin H
-- `Iris.ProofMode.intoEmbed_objective` idx 4: necessary (P = (1 <= k) not objective: holds at 1, not at 0)
theorem w8c4_49 : ¬ drop0% Iris.ProofMode.intoEmbed_objective 4 := fun h => by
  have H := (@h UIdx SiProp _ mp1).1; exact Nat.not_succ_le_zero 0 (SiProp.forall_holds.1 (H 1 0 (Nat.le_refl 1)) (0 : Nat))
-- `Iris.ProofMode.fromExists_monPred_at` idx 8: necessary (alpha=True, P=embed False, Phi=embed True)
theorem w8c4_50 : ¬ drop0% Iris.ProofMode.fromExists_monPred_at 8 := fun h => by
  have H := (@h UIdx SiProp _ True eF (fun _ => eT) (fun _ => sT) 0 (fun _ => mk eT)).1; fin H
-- `Iris.ProofMode.fromExists_monPred_at` idx 9: necessary (P=Phi=embed False, Psi := True)
theorem w8c4_51 : ¬ drop0% Iris.ProofMode.fromExists_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ True eF (fun _ => eF) (fun _ => sT) 0 ⟨exists_elim fun _ => .rfl⟩).1; fin H
-- `Iris.ProofMode.fromExists_monPred_at_ex` idx 6: necessary (P=embed False, Phi=True)
theorem w8c4_52 : ¬ drop0% Iris.ProofMode.fromExists_monPred_at_ex 6 := fun h => by
  have H := (@h UIdx SiProp _ eF (fun _ => sT) 0).1; fin H
-- `Iris.ProofMode.intoExists_monPred_at` idx 8: necessary (P=embed True, Phi=embed False)
theorem w8c4_53 : ¬ drop0% Iris.ProofMode.intoExists_monPred_at 8 := fun h => by
  have H := (@h UIdx SiProp _ True eT (fun _ => eF) (fun _ => sF) 0 (fun _ => mk eF)).1; fin H
-- `Iris.ProofMode.intoExists_monPred_at` idx 9: necessary (P=Phi=embed True, Psi := False)
theorem w8c4_54 : ¬ drop0% Iris.ProofMode.intoExists_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ True eT (fun _ => eT) (fun _ => sF) 0 ⟨exists_intro (Ψ := fun _ : True => eT) trivial⟩).1; fin H
-- `Iris.ProofMode.intoExists_monPred_at_ex` idx 6: necessary (P=embed True, Phi=False)
theorem w8c4_55 : ¬ drop0% Iris.ProofMode.intoExists_monPred_at_ex 6 := fun h => by
  have H := (@h UIdx SiProp _ eT (fun _ => sF) 0).1; fin H
-- `Iris.ProofMode.fromForall_monPred_at_wand` idx 8: necessary (P=embed True, Q=embed False, Phi := False)
theorem w8c4_56 : ¬ drop0% Iris.ProofMode.fromForall_monPred_at_wand 8 := fun h => by
  have H := (@h UIdx SiProp _ eT eF (fun _ => sF) (fun _ => sF) 0 (fun _ => mk eF)).1; exact wTF 0 0 (H 0 (SiProp.forall_holds.2 fun _ _ _ _ _ _ h => h))
-- `Iris.ProofMode.fromForall_monPred_at_wand` idx 9: necessary (P=embed True, Q=embed False, Psi := True)
theorem w8c4_57 : ¬ drop0% Iris.ProofMode.fromForall_monPred_at_wand 9 := fun h => by
  have H := (@h UIdx SiProp _ eT eF (fun _ => sT) (fun _ => sT) 0 (fun _ => mk eT)).1; exact wTF 0 0 (H 0 (SiProp.forall_holds.2 fun _ _ _ _ _ _ h => h))
-- `Iris.ProofMode.fromForall_monPred_at_imp` idx 8: necessary (P=embed True, Q=embed False, Phi := False)
theorem w8c4_58 : ¬ drop0% Iris.ProofMode.fromForall_monPred_at_imp 8 := fun h => by
  have H := (@h UIdx SiProp _ eT eF (fun _ => sF) (fun _ => sF) 0 (fun _ => mk eF)).1; exact iTF 0 0 (H 0 (SiProp.forall_holds.2 fun _ _ _ _ _ _ h => h))
-- `Iris.ProofMode.fromForall_monPred_at_imp` idx 9: necessary (P=embed True, Q=embed False, Psi := True)
theorem w8c4_59 : ¬ drop0% Iris.ProofMode.fromForall_monPred_at_imp 9 := fun h => by
  have H := (@h UIdx SiProp _ eT eF (fun _ => sT) (fun _ => sT) 0 (fun _ => mk eT)).1; exact iTF 0 0 (H 0 (SiProp.forall_holds.2 fun _ _ _ _ _ _ h => h))
-- `Iris.ProofMode.fromForall_monPred_at` idx 8: necessary (alpha=True, P=embed False, Phi=embed True)
theorem w8c4_60 : ¬ drop0% Iris.ProofMode.fromForall_monPred_at 8 := fun h => by
  have H := (@h UIdx SiProp _ True eF (fun _ => eT) (fun _ => sT) 0 (fun _ => mk eT)).1; fin H
-- `Iris.ProofMode.fromForall_monPred_at` idx 9: necessary (P=Phi=embed False, Psi := True)
theorem w8c4_61 : ¬ drop0% Iris.ProofMode.fromForall_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ True eF (fun _ => eF) (fun _ => sT) 0 ⟨forall_elim trivial⟩).1; fin H
-- `Iris.ProofMode.fromForall_monPred_at_objectively` idx 6: necessary (P=embed False, Phi=True)
theorem w8c4_62 : ¬ drop0% Iris.ProofMode.fromForall_monPred_at_objectively 6 := fun h => by
  have H := (@h UIdx SiProp _ eF (fun _ => sT) 0).1; fin H
-- `Iris.ProofMode.intoForall_monPred_at` idx 8: necessary (P=embed True, Phi=embed False)
theorem w8c4_63 : ¬ drop0% Iris.ProofMode.intoForall_monPred_at 8 := fun h => by
  have H := (@h UIdx SiProp _ True eT (fun _ => eF) (fun _ => sF) 0 (fun _ => mk eF)).1; fin H
-- `Iris.ProofMode.intoForall_monPred_at` idx 9: necessary (P=Phi=embed True, Psi := False)
theorem w8c4_64 : ¬ drop0% Iris.ProofMode.intoForall_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ True eT (fun _ => eT) (fun _ => sF) 0 ⟨forall_intro fun _ => .rfl⟩).1; fin H
-- `Iris.ProofMode.intoForall_monPred_at_objectively` idx 6: necessary (P=embed True, Phi=False)
theorem w8c4_65 : ¬ drop0% Iris.ProofMode.intoForall_monPred_at_objectively 6 := fun h => by
  have H := (@h UIdx SiProp _ eT (fun _ => sF) 0).1; fin H
-- `Iris.ProofMode.isExcept0_monPred_at` idx 5: necessary (P=embed False (step 0: except0 False holds))
theorem w8c4_66 : ¬ drop0% Iris.ProofMode.isExcept0_monPred_at 5 := fun h => by
  have H := (@h UIdx SiProp _ eF 0).1; fin H
-- `Iris.ProofMode.intoExcept0_monPred_at_fwd` idx 7: necessary (P=embed True, Q=embed False, step 1)
theorem w8c4_67 : ¬ drop0% Iris.ProofMode.intoExcept0_monPred_at_fwd 7 := fun h => by
  have H := (@h UIdx SiProp _ eT eF sF 0 (mk eF)).1; fin H
-- `Iris.ProofMode.intoExcept0_monPred_at_fwd` idx 8: necessary (P=Q=embed True, Q-at := False, step 1)
theorem w8c4_68 : ¬ drop0% Iris.ProofMode.intoExcept0_monPred_at_fwd 8 := fun h => by
  have H := (@h UIdx SiProp _ eT eT sF 0 ⟨fun _ _ h => Or.inr h⟩).1; fin H
-- `_private.Iris.ProofMode.MonPred.0.Iris.ProofMode.intoWand_monPred_at_core` idx 13: necessary (R=P=embed True, Q=embed False, i=j=0)
theorem w8c4_69 : ¬ drop0% _private.Iris.ProofMode.MonPred.«0».Iris.ProofMode.intoWand_monPred_at_core 13 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eT eF sT sF 0 0 (Nat.le_refl 0) (fun _ h => h) (fun _ h => h)); fin H
-- `_private.Iris.ProofMode.MonPred.0.Iris.ProofMode.intoWand_monPred_at_core` idx 14: necessary (R=embed True, P=Q=embed False, P-at := True)
theorem w8c4_70 : ¬ drop0% _private.Iris.ProofMode.MonPred.«0».Iris.ProofMode.intoWand_monPred_at_core 14 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eF eF sT sF 0 0 (Nat.le_refl 0) (wand_intro sep_elim_right) (fun _ h => h)); fin H
-- `_private.Iris.ProofMode.MonPred.0.Iris.ProofMode.intoWand_monPred_at_core` idx 15: necessary (R=P=Q=embed True, Q-at := False)
theorem w8c4_71 : ¬ drop0% _private.Iris.ProofMode.MonPred.«0».Iris.ProofMode.intoWand_monPred_at_core 15 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eT eT sT sF 0 0 (Nat.le_refl 0) (wand_intro sep_elim_right) (fun _ h => h)); fin H
-- `Iris.ProofMode.intoWand_monPred_at_unknown_unknown` idx 11: necessary (R=P=embed True, Q=embed False)
theorem w8c4_72 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_unknown_unknown 11 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eT eF sT sF 0 (mk eT) (mk eF)).1; fin H
-- `Iris.ProofMode.intoWand_monPred_at_unknown_unknown` idx 12: necessary (R=True, P=Q=False, P-at := True)
theorem w8c4_73 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_unknown_unknown 12 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eF eF sT sF 0 ⟨(wand_intro sep_elim_right)⟩ (mk eF)).1; fin H
-- `Iris.ProofMode.intoWand_monPred_at_unknown_unknown` idx 13: necessary (R=P=Q=True, Q-at := False)
theorem w8c4_74 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_unknown_unknown 13 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eT eT sT sF 0 ⟨(wand_intro sep_elim_right)⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.intoWand_monPred_at_unknown_known` idx 11: necessary (R=Q=(1 <= k), P=True, i=1, j=0)
theorem w8c4_75 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_unknown_known 11 := fun h => by
  have H := (@h UIdx SiProp _ false false mp1 eT mp1 sT (1 : Nat) (0 : Nat) ⟨wand_intro sep_elim_left⟩ (mk eT)).1; exact Nat.not_succ_le_zero 0 (H 0 (Nat.le_refl 1) 0 (Nat.le_refl 0) trivial)
-- `Iris.ProofMode.intoWand_monPred_at_unknown_known` idx 12: necessary (R=P=embed True, Q=embed False)
theorem w8c4_76 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_unknown_known 12 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eT eF sT 0 0 ⟨Nat.le_refl 0⟩ (mk eT)).1; fin H
-- `Iris.ProofMode.intoWand_monPred_at_unknown_known` idx 13: necessary (R=True, P=Q=False, P-at := True)
theorem w8c4_77 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_unknown_known 13 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eF eF sT 0 0 ⟨Nat.le_refl 0⟩ ⟨(wand_intro sep_elim_right)⟩).1; fin H
-- `Iris.ProofMode.intoWand_monPred_at_known_unknown_le` idx 11: necessary (R=Q=(1 <= k), P=True, i=1, j=0)
theorem w8c4_78 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_known_unknown_le 11 := fun h => by
  have H := (@h UIdx SiProp _ false false mp1 eT mp1 (mp1.monPred_at 0) (1 : Nat) (0 : Nat) ⟨wand_intro sep_elim_left⟩ (mk mp1)).1; exact Nat.not_succ_le_zero 0 (H 0 (Nat.le_refl 1) 0 (Nat.le_refl 0) trivial)
-- `Iris.ProofMode.intoWand_monPred_at_known_unknown_le` idx 12: necessary (R=P=embed True, Q=embed False)
theorem w8c4_79 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_known_unknown_le 12 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eT eF sF 0 0 ⟨Nat.le_refl 0⟩ (mk eF)).1; fin H
-- `Iris.ProofMode.intoWand_monPred_at_known_unknown_le` idx 13: necessary (R=P=Q=True, Q-at := False)
theorem w8c4_80 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_known_unknown_le 13 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eT eT sF 0 0 ⟨Nat.le_refl 0⟩ ⟨(wand_intro sep_elim_right)⟩).1; fin H
-- `Iris.ProofMode.intoWand_monPred_at_known_unknown_ge` idx 11: necessary (R=True, P=Q=(1 <= k), i=1, j=0)
theorem w8c4_81 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_known_unknown_ge 11 := fun h => by
  have H := (@h UIdx SiProp _ false false eT mp1 mp1 (mp1.monPred_at 0) (1 : Nat) (0 : Nat) ⟨(wand_intro sep_elim_right)⟩ (mk mp1)).1; exact Nat.not_succ_le_zero 0 (H 0 trivial 0 (Nat.le_refl 0) (Nat.le_refl 1))
-- `Iris.ProofMode.intoWand_monPred_at_known_unknown_ge` idx 13: necessary (R=P=Q=True, Q-at := False)
theorem w8c4_82 : ¬ drop0% Iris.ProofMode.intoWand_monPred_at_known_unknown_ge 13 := fun h => by
  have H := (@h UIdx SiProp _ false false eT eT eT sF 0 0 ⟨Nat.le_refl 0⟩ ⟨(wand_intro sep_elim_right)⟩).1; fin H
-- `Iris.ProofMode.elimModal_at` idx 12: necessary (P=embed False, P'=embed True, phi=True)
theorem w8c4_83 : ¬ drop0% Iris.ProofMode.elimModal_at 12 := fun h => by
  have H := (@h UIdx SiProp _ True false .in false sT sT eF eT 0).1 trivial; fin H
-- `Iris.ProofMode.elimModal_at_bupd_goal` idx 13: necessary (identity bupd, Q=embed False, Q'=embed True)
theorem w8c4_84 : ¬ drop0% Iris.ProofMode.elimModal_at_bupd_goal 13 := fun h => by
  have H := (@h UIdx SiProp _ idBupd True false .in false sT sT eF eT 0).1 trivial; fin H
-- `Iris.ProofMode.elimModal_at_bupd_hyp` idx 14: necessary (identity bupd, P=embed True, P-at := False (premise vacuous), goal False)
theorem w8c4_85 : ¬ drop0% Iris.ProofMode.elimModal_at_bupd_hyp 14 := fun h => by
  have H := (@h UIdx SiProp _ idBupd True false .in false eT sF sT sF sT 0 ⟨fun _ _ h => h.1⟩).1 trivial; fin H
-- `Iris.ProofMode.addModal_at_bupd_goal` idx 8: necessary (identity bupd, P=True, P'=False, Q=embed False)
theorem w8c4_86 : ¬ drop0% Iris.ProofMode.addModal_at_bupd_goal 8 := fun h => by
  have H := (@h UIdx SiProp _ idBupd sT sF eF 0).1; fin H
-- `Iris.ProofMode.makeMonPredAt_sep` idx 8: necessary (P=Q=embed True, P-at := False)
theorem w8c4_87 : ¬ drop0% Iris.ProofMode.makeMonPredAt_sep 8 := fun h => by
  have H := (@h UIdx SiProp _ 0 eT eT sF sT (mk eT)).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_sep` idx 9: necessary (P=Q=embed True, Q-at := False)
theorem w8c4_88 : ¬ drop0% Iris.ProofMode.makeMonPredAt_sep 9 := fun h => by
  have H := (@h UIdx SiProp _ 0 eT eT sT sF (mk eT)).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_and` idx 8: necessary (P=Q=embed True, P-at := False)
theorem w8c4_89 : ¬ drop0% Iris.ProofMode.makeMonPredAt_and 8 := fun h => by
  have H := (@h UIdx SiProp _ 0 eT eT sF sT (mk eT)).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_or` idx 8: necessary (P=True, Q=False, P-at := False)
theorem w8c4_90 : ¬ drop0% Iris.ProofMode.makeMonPredAt_or 8 := fun h => by
  have H := (@h UIdx SiProp _ 0 eT eF sF sF (mk eF)).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_or` idx 9: necessary (P=False, Q=True, Q-at := False)
theorem w8c4_91 : ¬ drop0% Iris.ProofMode.makeMonPredAt_or 9 := fun h => by
  have H := (@h UIdx SiProp _ 0 eF eT sF sF (mk eF)).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_forall` idx 8: necessary (alpha=True, Phi=embed False, Psi := True)
theorem w8c4_92 : ¬ drop0% Iris.ProofMode.makeMonPredAt_forall 8 := fun h => by
  have H := (@h UIdx SiProp _ True .indexToProp 0 (fun _ => eF) (fun _ => sT)).1.mpr; exact (H 0 (SiProp.forall_holds.2 fun _ => trivial)) sF ⟨eF, ⟨trivial, rfl⟩, rfl⟩
-- `Iris.ProofMode.makeMonPredAt_exists` idx 8: necessary (alpha=True, Phi=embed True, Psi := False)
theorem w8c4_93 : ¬ drop0% Iris.ProofMode.makeMonPredAt_exists 8 := fun h => by
  have H := (@h UIdx SiProp _ True .indexToProp 0 (fun _ => eT) (fun _ => sF)).1.mp; exact (SiProp.exists_holds.1 (H 0 ⟨sT, ⟨eT, ⟨trivial, rfl⟩, rfl⟩, trivial⟩)).elim fun _ h => h
-- `Iris.ProofMode.makeMonPredAt_persistently` idx 7: necessary (P=embed True, P-at := False)
theorem w8c4_94 : ¬ drop0% Iris.ProofMode.makeMonPredAt_persistently 7 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_affinely` idx 7: necessary (P=embed True, P-at := False)
theorem w8c4_95 : ¬ drop0% Iris.ProofMode.makeMonPredAt_affinely 7 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_intuitionistically` idx 7: necessary (P=embed True, P-at := False)
theorem w8c4_96 : ¬ drop0% Iris.ProofMode.makeMonPredAt_intuitionistically 7 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_absorbingly` idx 7: necessary (P=embed True, P-at := False)
theorem w8c4_97 : ¬ drop0% Iris.ProofMode.makeMonPredAt_absorbingly 7 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_except0` idx 7: necessary (P=embed True, P-at := False (step 1))
theorem w8c4_98 : ¬ drop0% Iris.ProofMode.makeMonPredAt_except0 7 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_later` idx 7: necessary (P=embed True, P-at := False (step 1))
theorem w8c4_99 : ¬ drop0% Iris.ProofMode.makeMonPredAt_later 7 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_persistentlyIf` idx 8: necessary (p=true, P=embed True, P-at := False)
theorem w8c4_100 : ¬ drop0% Iris.ProofMode.makeMonPredAt_persistentlyIf 8 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp true 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_affinelyIf` idx 8: necessary (p=true, P=embed True, P-at := False)
theorem w8c4_101 : ¬ drop0% Iris.ProofMode.makeMonPredAt_affinelyIf 8 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp true 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_absorbinglyIf` idx 8: necessary (p=true, P=embed True, P-at := False)
theorem w8c4_102 : ¬ drop0% Iris.ProofMode.makeMonPredAt_absorbinglyIf 8 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp true 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_intuitionisticallyIf` idx 8: necessary (p=true, P=embed True, P-at := False)
theorem w8c4_103 : ¬ drop0% Iris.ProofMode.makeMonPredAt_intuitionisticallyIf 8 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp true 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_bupd` idx 8: necessary (identity bupd, P=embed True, P-at := False)
theorem w8c4_104 : ¬ drop0% Iris.ProofMode.makeMonPredAt_bupd 8 := fun h => by
  have H := (@h UIdx SiProp _ idBupd .indexToProp 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.makeMonPredAt_laterN` idx 8: necessary (n=0, P=embed True, P-at := False)
theorem w8c4_105 : ¬ drop0% Iris.ProofMode.makeMonPredAt_laterN 8 := fun h => by
  have H := (@h UIdx SiProp _ .indexToProp 0 0 eT sF).1.mp; fin H
-- `Iris.ProofMode.frameMonPredAt_enter` idx 8: necessary (R=Q=True, P=embed False)
theorem w8c4_106 : ¬ drop0% Iris.ProofMode.frameMonPredAt_enter 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_here` idx 7: necessary (P=(1 <= k), i=1, j=0)
theorem w8c4_107 : ¬ drop0% Iris.ProofMode.frameMonPredAt_here 7 := fun h => by
  have H := (@h UIdx SiProp _ false (1 : Nat) (0 : Nat) mp1).1; exact Nat.not_succ_le_zero 0 (H 0 ⟨Nat.le_refl 1, trivial⟩)
-- `Iris.ProofMode.frameMonPredAt_embed` idx 8: necessary (R=Q=True, framed False)
theorem w8c4_108 : ¬ drop0% Iris.ProofMode.frameMonPredAt_embed 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sF sT).1; fin H
-- `Iris.ProofMode.frameMonPredAt_sep` idx 9: necessary (R=Q=True, P=Q=embed False)
theorem w8c4_109 : ¬ drop0% Iris.ProofMode.frameMonPredAt_sep 9 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_and` idx 9: necessary (R=Q=True, P=Q=embed False)
theorem w8c4_110 : ¬ drop0% Iris.ProofMode.frameMonPredAt_and 9 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_or` idx 9: necessary (R=Q=True, P=Q=embed False)
theorem w8c4_111 : ¬ drop0% Iris.ProofMode.frameMonPredAt_or 9 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_forall` idx 9: necessary (X=True, Psi=embed False)
theorem w8c4_112 : ¬ drop0% Iris.ProofMode.frameMonPredAt_forall 9 := fun h => by
  have H := (@h UIdx SiProp _ True false 0 sT sT (fun _ => eF)).1; exact (H 0 ⟨trivial, trivial⟩) sF ⟨eF, ⟨trivial, rfl⟩, rfl⟩
-- `Iris.ProofMode.frameMonPredAt_exists` idx 9: necessary (X=True, Psi=embed False)
theorem w8c4_113 : ¬ drop0% Iris.ProofMode.frameMonPredAt_exists 9 := fun h => by
  have H := (@h UIdx SiProp _ True false 0 sT sT (fun _ => eF)).1; obtain ⟨_, ⟨_, ⟨_, rfl⟩, rfl⟩, hP⟩ := H 0 ⟨trivial, trivial⟩; exact hP
-- `Iris.ProofMode.frameMonPredAt_absorbingly` idx 8: necessary (R=Q=True, P=embed False)
theorem w8c4_114 : ¬ drop0% Iris.ProofMode.frameMonPredAt_absorbingly 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_affinely` idx 8: necessary (R=Q=True, P=embed False)
theorem w8c4_115 : ¬ drop0% Iris.ProofMode.frameMonPredAt_affinely 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_persistently` idx 8: necessary (R=Q=True, P=embed False)
theorem w8c4_116 : ¬ drop0% Iris.ProofMode.frameMonPredAt_persistently 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_intuitionistically` idx 8: necessary (R=Q=True, P=embed False)
theorem w8c4_117 : ¬ drop0% Iris.ProofMode.frameMonPredAt_intuitionistically 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_objectively` idx 8: necessary (R=Q=True, P=embed False)
theorem w8c4_118 : ¬ drop0% Iris.ProofMode.frameMonPredAt_objectively 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_subjectively` idx 8: necessary (R=Q=True, P=embed False)
theorem w8c4_119 : ¬ drop0% Iris.ProofMode.frameMonPredAt_subjectively 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_later` idx 8: necessary (R=Q=True, P=embed False (step 1))
theorem w8c4_120 : ¬ drop0% Iris.ProofMode.frameMonPredAt_later 8 := fun h => by
  have H := (@h UIdx SiProp _ false 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_bupd` idx 9: necessary (identity bupd, R=Q=True, P=embed False)
theorem w8c4_121 : ¬ drop0% Iris.ProofMode.frameMonPredAt_bupd 9 := fun h => by
  have H := (@h UIdx SiProp _ idBupd false 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_laterN` idx 9: necessary (n=0, R=Q=True, P=embed False)
theorem w8c4_122 : ¬ drop0% Iris.ProofMode.frameMonPredAt_laterN 9 := fun h => by
  have H := (@h UIdx SiProp _ false 0 0 sT sT eF).1; fin H
-- `Iris.ProofMode.frameMonPredAt_wand` idx 10: necessary (R=Q1=(1 <= k), P=Q2=True, i=1, j=0)
theorem w8c4_123 : ¬ drop0% Iris.ProofMode.frameMonPredAt_wand 10 := fun h => by
  have H := (@h UIdx SiProp _ false (1 : Nat) (0 : Nat) eT mp1 mp1 eT ⟨fun _ _ h => h.1⟩).1; exact Nat.not_succ_le_zero 0 (SiProp.forall_holds.1 (H 0 ⟨Nat.le_refl 1, wTT 1 0⟩) (0 : Nat) 0 (Nat.le_refl 0) (Nat.le_refl 0) 0 (Nat.le_refl 0) trivial)
-- `Iris.ProofMode.frameMonPredAt_wand` idx 11: necessary (R=P=Q2=True, Q1=embed False)
theorem w8c4_124 : ¬ drop0% Iris.ProofMode.frameMonPredAt_wand 11 := fun h => by
  have H := (@h UIdx SiProp _ false 0 0 eT eT eF eT ⟨Nat.le_refl 0⟩).1; exact wTF 0 0 (H 0 ⟨trivial, wTT 0 0⟩)
-- `Iris.ProofMode.frameMonPredAt_impl` idx 9: necessary (R=Q1=(1 <= k), P=Q2=True, i=1, j=0)
theorem w8c4_125 : ¬ drop0% Iris.ProofMode.frameMonPredAt_impl 9 := fun h => by
  have H := (@h UIdx SiProp _ (1 : Nat) (0 : Nat) eT mp1 mp1 eT ⟨fun _ _ h => h.1.2⟩).1; exact Nat.not_succ_le_zero 0 (SiProp.forall_holds.1 (H 0 ⟨⟨trivial, Nat.le_refl 1⟩, iTT 1 0⟩) (0 : Nat) 0 (Nat.le_refl 0) (Nat.le_refl 0) 0 (Nat.le_refl 0) trivial)
-- `Iris.ProofMode.frameMonPredAt_impl` idx 10: necessary (R=P=Q2=True, Q1=embed False)
theorem w8c4_126 : ¬ drop0% Iris.ProofMode.frameMonPredAt_impl 10 := fun h => by
  have H := (@h UIdx SiProp _ 0 0 eT eT eF eT ⟨Nat.le_refl 0⟩).1; exact iTF 0 0 (H 0 ⟨⟨trivial, trivial⟩, iTT 0 0⟩)
-- `Iris.ProofMode.intoInternalEq_monPred_at` idx 9: necessary (A=SiProp, x=True, y=False, P=embed True)
theorem w8c4_127 : ¬ drop0% Iris.ProofMode.intoInternalEq_monPred_at 9 := fun h => by
  have H := (@h UIdx SiProp _ SiProp _ sT sF eT 0).1; exact ((H 0 trivial) (Nat.le_refl 0)).mp trivial
-- `Iris.ProofMode.fromForall_monPred_at_plainly` idx 6: necessary (P=embed False, Phi=True)
theorem w8c4_128 : ¬ drop0% Iris.ProofMode.fromForall_monPred_at_plainly 6 := fun h => by
  have H := (@h UIdx SiProp _ eF (fun _ => sT) 0).1; fin H
-- `Iris.ProofMode.intoForall_monPred_at_plainly` idx 6: necessary (P=embed True, Phi=False)
theorem w8c4_129 : ¬ drop0% Iris.ProofMode.intoForall_monPred_at_plainly 6 := fun h => by
  have H := (@h UIdx SiProp _ eT (fun _ => sF) 0).1; fin H
-- `Iris.ProofMode.elimModal_at_fupd_goal` idx 16: necessary (IProp: P=True, P'=False, Q=embed False, masks top; fupd soundness)
theorem w8c4_130 : ¬ drop0% Iris.ProofMode.elimModal_at_fupd_goal 16 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (tfw _).trans ((@h UIdx (IProp CGF) _ _ True false .in false ⊤ ⊤ ⊤ iprop(True) iprop(⌜False⌝) (MonPred.embed iprop(⌜False⌝) : MI) (MonPred.embed iprop(True) : MI) 0).1 trivial)
-- `Iris.ProofMode.elimModal_at_fupd_hyp` idx 17: necessary (IProp: P=embed True, goal |={top}=> False; fupd soundness)
theorem w8c4_131 : ¬ drop0% Iris.ProofMode.elimModal_at_fupd_hyp 17 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (emp_sep.2.trans (sep_mono (fT ⊤) (wand_intro true_intro))).trans ((@h UIdx (IProp CGF) _ _ True false .in false ⊤ ⊤ (MonPred.embed iprop(True) : MI) iprop(True) iprop(True) iprop(|={⊤}=> ⌜False⌝) iprop(True) 0 (mkI _)).1 trivial)
-- `Iris.ProofMode.elimModal_at_fupd_hyp` idx 16: necessary (IProp: P=embed True, P-at := False (premise holds by sep_elim_left), goal |={top}=> False; fupd soundness)
theorem w8c4_132 : ¬ drop0% Iris.ProofMode.elimModal_at_fupd_hyp 16 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (emp_sep.2.trans (sep_mono (fT ⊤) (wand_intro (sep_elim_right.trans (pure_elim' False.elim))))).trans ((@h UIdx (IProp CGF) _ _ True false .in false ⊤ ⊤ (MonPred.embed iprop(True) : MI) iprop(⌜False⌝) iprop(⌜False⌝) iprop(|={⊤}=> ⌜False⌝) iprop(|={⊤}=> ⌜False⌝) 0 ⟨fun _ => sep_elim_left⟩).1 trivial)
-- `Iris.ProofMode.addModal_at_fupd_goal` idx 10: necessary (IProp: P=True, P'=False, Q=embed False; fupd soundness)
theorem w8c4_133 : ¬ drop0% Iris.ProofMode.addModal_at_fupd_goal 10 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (tfw _).trans (@h UIdx (IProp CGF) _ _ ⊤ ⊤ iprop(True) iprop(⌜False⌝) (MonPred.embed iprop(⌜False⌝) : MI) 0).1
-- `Iris.ProofMode.makeMonPredAt_fupd` idx 10: necessary (IProp: P=embed True, P-at := False; fupd soundness)
theorem w8c4_134 : ¬ drop0% Iris.ProofMode.makeMonPredAt_fupd 10 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (fT ⊤).trans (@h UIdx (IProp CGF) _ _ .indexToProp 0 ⊤ ⊤ (MonPred.embed iprop(True) : MI) iprop(⌜False⌝)).1.mp
-- `Iris.ProofMode.frameMonPredAt_fupd` idx 11: necessary (IProp: R=Q=True, P=embed False; fupd soundness)
theorem w8c4_135 : ¬ drop0% Iris.ProofMode.frameMonPredAt_fupd 11 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => (emp_sep.2.trans (sep_mono true_intro true_intro)).trans (@h UIdx (IProp CGF) _ _ false 0 ⊤ ⊤ iprop(True) iprop(True) (MonPred.embed iprop(⌜False⌝) : MI)).1
-- `Iris.ProofMode.elimInv_embed_with_close` idx 14: necessary (all True, Q=embed False)
theorem w8c4_136 : ¬ drop0% Iris.ProofMode.elimInv_embed_with_close 14 := fun h => by
  have H := (@h UIdx SiProp _ Unit True sT sT (fun _ => sT) (fun _ => sT) eT (fun _ => eT) (fun _ => eT) eF eT mkE (fun _ => mkE) (fun _ => mkE)).1 trivial; exact (BIBase.Entails.trans (show (emp : MP) ⊢ _ from (emp_sep.2.trans (sep_mono true_intro (emp_sep.2.trans (sep_mono true_intro (forall_intro fun _ => wand_intro true_intro)))))) H) 0 0 trivial
-- `Iris.ProofMode.elimInv_embed_with_close` idx 15: necessary (Pin-embedded := False (premise vacuous), Pin=embed True, Q=embed False)
theorem w8c4_137 : ¬ drop0% Iris.ProofMode.elimInv_embed_with_close 15 := fun h => by
  have H := (@h UIdx SiProp _ Unit True sT sF (fun _ => sT) (fun _ => sT) eT (fun _ => eT) (fun _ => eT) eF eT (fun _ => ⟨fun _ _ h => h.2.1.elim⟩) (fun _ => mkE) (fun _ => mkE)).1 trivial; exact (BIBase.Entails.trans (show (emp : MP) ⊢ _ from (emp_sep.2.trans (sep_mono true_intro (emp_sep.2.trans (sep_mono true_intro (forall_intro fun _ => wand_intro true_intro)))))) H) 0 0 trivial
-- `Iris.ProofMode.elimInv_embed_with_close` idx 16: necessary (Pout=embed False unconstrained, Q=Q'=False (premise LHS false))
theorem w8c4_138 : ¬ drop0% Iris.ProofMode.elimInv_embed_with_close 16 := fun h => by
  have H := (@h UIdx SiProp _ Unit True sT sT (fun _ => sT) (fun _ => sT) eT (fun _ => eF) (fun _ => eT) eF eF (fun _ => ⟨fun _ n h => SiProp.forall_holds.1 h.2.2 () n (Nat.le_refl n) ⟨trivial, trivial⟩⟩) mkE (fun _ => mkE)).1 trivial; exact (BIBase.Entails.trans (show (emp : MP) ⊢ _ from (emp_sep.2.trans (sep_mono true_intro (emp_sep.2.trans (sep_mono true_intro (forall_intro fun _ => wand_intro (sep_elim_right.trans sep_elim_left))))))) H) 0 0 trivial
-- `Iris.ProofMode.elimInv_embed_with_close` idx 17: necessary (Pclose=embed False unconstrained, Q=Q'=False (premise LHS false))
theorem w8c4_139 : ¬ drop0% Iris.ProofMode.elimInv_embed_with_close 17 := fun h => by
  have H := (@h UIdx SiProp _ Unit True sT sT (fun _ => sT) (fun _ => sT) eT (fun _ => eT) (fun _ => eF) eF eF (fun _ => ⟨fun _ n h => SiProp.forall_holds.1 h.2.2 () n (Nat.le_refl n) ⟨trivial, trivial⟩⟩) mkE (fun _ => mkE)).1 trivial; exact (BIBase.Entails.trans (show (emp : MP) ⊢ _ from (emp_sep.2.trans (sep_mono true_intro (emp_sep.2.trans (sep_mono true_intro (forall_intro fun _ => wand_intro (sep_elim_right.trans sep_elim_right))))))) H) 0 0 trivial
-- `Iris.ProofMode.elimInv_embed_without_close` idx 12: necessary (all True, Q=embed False)
theorem w8c4_140 : ¬ drop0% Iris.ProofMode.elimInv_embed_without_close 12 := fun h => by
  have H := (@h UIdx SiProp _ Unit True sT sT (fun _ => sT) eT (fun _ => eT) eF (fun _ => eT) mkE (fun _ => mkE)).1 trivial; exact (BIBase.Entails.trans (show (emp : MP) ⊢ _ from (emp_sep.2.trans (sep_mono true_intro (emp_sep.2.trans (sep_mono true_intro (forall_intro fun _ => wand_intro true_intro)))))) H) 0 0 trivial
-- `Iris.ProofMode.elimInv_embed_without_close` idx 13: necessary (Pin-embedded := False (premise vacuous), Pin=embed True, Q=embed False)
theorem w8c4_141 : ¬ drop0% Iris.ProofMode.elimInv_embed_without_close 13 := fun h => by
  have H := (@h UIdx SiProp _ Unit True sT sF (fun _ => sT) eT (fun _ => eT) eF (fun _ => eT) (fun _ => ⟨fun _ _ h => h.2.1.elim⟩) (fun _ => mkE)).1 trivial; exact (BIBase.Entails.trans (show (emp : MP) ⊢ _ from (emp_sep.2.trans (sep_mono true_intro (emp_sep.2.trans (sep_mono true_intro (forall_intro fun _ => wand_intro true_intro)))))) H) 0 0 trivial
-- `Iris.ProofMode.elimInv_embed_without_close` idx 14: necessary (Pout=embed False unconstrained, Q=Q'=False (premise LHS false))
theorem w8c4_142 : ¬ drop0% Iris.ProofMode.elimInv_embed_without_close 14 := fun h => by
  have H := (@h UIdx SiProp _ Unit True sT sT (fun _ => sT) eT (fun _ => eF) eF (fun _ => eF) (fun _ => ⟨fun _ n h => SiProp.forall_holds.1 h.2.2 () n (Nat.le_refl n) ⟨trivial, trivial⟩⟩) mkE).1 trivial; exact (BIBase.Entails.trans (show (emp : MP) ⊢ _ from (emp_sep.2.trans (sep_mono true_intro (emp_sep.2.trans (sep_mono true_intro (forall_intro fun _ => wand_intro (sep_elim_right.trans sep_elim_left))))))) H) 0 0 trivial
-- `Iris.ProofMode.elimAcc_at_none` idx 19: necessary (IProp, masks top, all alpha/beta True, P=embed (|={top}=> False); fupd soundness)
theorem w8c4_143 : ¬ drop0% Iris.ProofMode.elimAcc_at_none 19 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => app2 ((@h UIdx (IProp CGF) _ _ Unit True ⊤ ⊤ ⊤ ⊤ (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => (MonPred.embed iprop(True) : MI)) (fun _ => (MonPred.embed iprop(True) : MI)) (MonPred.embed iprop(|={⊤}=> ⌜False⌝) : MI) (fun _ => (MonPred.embed iprop(True) : MI)) 0 (fun _ => mkEI) (fun _ => mkEI)).1 trivial) wT (accN ⊤)
-- `Iris.ProofMode.elimAcc_at_none` idx 17: necessary (IProp: alpha=True, alpha'=embed False (premise holds: accessor gives False), P=embed (|={top}=> False); fupd soundness)
theorem w8c4_144 : ¬ drop0% Iris.ProofMode.elimAcc_at_none 17 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => app2 ((@h UIdx (IProp CGF) _ _ Unit True ⊤ ⊤ ⊤ ⊤ (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => eFI) (fun _ => (MonPred.embed iprop(True) : MI)) (MonPred.embed iprop(|={⊤}=> ⌜False⌝) : MI) (fun _ => (MonPred.embed iprop(True) : MI)) 0 (fun _ => mkEI) (hvAcc _)).1 trivial) wT (accN ⊤)
-- `Iris.ProofMode.elimAcc_at_none` idx 18: necessary (IProp, masks (empty,empty) and (empty,top): beta=False, beta'=embed True, P=embed (|={empty,top}=> emp); open_top_false)
theorem w8c4_145 : ¬ drop0% Iris.ProofMode.elimAcc_at_none 18 := fun h => by
  exact open_top_false fun {_} => ⟨_, app2 ((@h UIdx (IProp CGF) _ _ Unit True ∅ ∅ ∅ ⊤ (fun _ => iprop(True)) (fun _ => iprop(⌜False⌝)) (fun _ => (MonPred.embed iprop(True) : MI)) (fun _ => (MonPred.embed iprop(True) : MI)) (MonPred.embed iprop(|={∅,⊤}=> emp) : MI) (fun _ => (MonPred.embed iprop(True) : MI)) 0 (fun _ => mkEI) ⟨fun _ => wand_intro (wand_intro (sep_elim_right.trans (accBn.trans (fun _ => .rfl))))⟩).1 trivial) wT (accF none)⟩
-- `Iris.ProofMode.elimAcc_at_some` idx 22: necessary (IProp, masks top, all True, P=embed (|={top}=> False); fupd soundness)
theorem w8c4_146 : ¬ drop0% Iris.ProofMode.elimAcc_at_some 22 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => app2 ((@h UIdx (IProp CGF) _ _ Unit True ⊤ ⊤ ⊤ ⊤ (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => (MonPred.embed iprop(True) : MI)) (fun _ => (MonPred.embed iprop(True) : MI)) (fun _ => (MonPred.embed iprop(True) : MI)) (MonPred.embed iprop(|={⊤}=> ⌜False⌝) : MI) (fun _ => (MonPred.embed iprop(True) : MI)) 0 (fun _ => mkEI) (fun _ => mkEI) (fun _ => mkEI)).1 trivial) wT (accS ⊤)
-- `Iris.ProofMode.elimAcc_at_some` idx 19: necessary (IProp: alpha=True, alpha'=embed False (premise holds: accessor gives False), P=embed (|={top}=> False); fupd soundness)
theorem w8c4_147 : ¬ drop0% Iris.ProofMode.elimAcc_at_some 19 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => app2 ((@h UIdx (IProp CGF) _ _ Unit True ⊤ ⊤ ⊤ ⊤ (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => eFI) (fun _ => (MonPred.embed iprop(True) : MI)) (fun _ => (MonPred.embed iprop(True) : MI)) (MonPred.embed iprop(|={⊤}=> ⌜False⌝) : MI) (fun _ => (MonPred.embed iprop(True) : MI)) 0 (fun _ => mkEI) (fun _ => mkEI) (hvAcc _)).1 trivial) wT (accS ⊤)
-- `Iris.ProofMode.elimAcc_at_some` idx 20: necessary (IProp, masks (empty,empty) and (empty,top): beta=False, beta'=embed True, P=embed (|={empty,top}=> True); open_top_false)
theorem w8c4_148 : ¬ drop0% Iris.ProofMode.elimAcc_at_some 20 := fun h => by
  exact open_top_false fun {_} => ⟨_, app2 ((@h UIdx (IProp CGF) _ _ Unit True ∅ ∅ ∅ ⊤ (fun _ => iprop(True)) (fun _ => iprop(⌜False⌝)) (fun _ => iprop(True)) (fun _ => (MonPred.embed iprop(True) : MI)) (fun _ => (MonPred.embed iprop(True) : MI)) (fun _ => (MonPred.embed iprop(True) : MI)) (MonPred.embed iprop(|={∅,⊤}=> True) : MI) (fun _ => (MonPred.embed iprop(True) : MI)) 0 (fun _ => mkEI) (fun _ => mkEI) ⟨fun _ => wand_intro (wand_intro (sep_elim_right.trans ((accB eTI).trans (fun _ => .rfl))))⟩).1 trivial) wT (accF (some iprop(True)))⟩
-- `Iris.ProofMode.elimAcc_at_some` idx 21: necessary (IProp, masks top: gamma=True, gamma'=embed False, P=embed (|={top}=> False); fupd soundness)
theorem w8c4_149 : ¬ drop0% Iris.ProofMode.elimAcc_at_some 21 := fun h => by
  exact fupd_false ⊤ ⊤ fun {_} => app2 ((@h UIdx (IProp CGF) _ _ Unit True ⊤ ⊤ ⊤ ⊤ (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => iprop(True)) (fun _ => (MonPred.embed iprop(True) : MI)) (fun _ => (MonPred.embed iprop(True) : MI)) (fun _ => eFI) (MonPred.embed iprop(|={⊤}=> ⌜False⌝) : MI) (fun _ => (MonPred.embed iprop(True) : MI)) 0 (fun _ => mkEI) (fun _ => mkEI) ⟨fun _ => wand_intro (wand_intro (sep_elim_right.trans accG))⟩).1 trivial) wT (accS ⊤)
end W8c4
