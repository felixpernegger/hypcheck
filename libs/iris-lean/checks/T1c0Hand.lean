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

namespace T1c0
open Iris Iris.BI Iris.Std

/-- A lawful closure modality on a BI (intro, join, frame, absorbs except0). -/
structure LM (PROP : Type _) [BI PROP] where
  M : PROP → PROP
  ne : OFE.NonExpansive M
  mono : ∀ {P Q : PROP}, (P ⊢ Q) → M P ⊢ M Q
  intro : ∀ {P : PROP}, P ⊢ M P
  join : ∀ {P : PROP}, M (M P) ⊢ M P
  frame : ∀ {P R : PROP}, iprop(M P ∗ R) ⊢ M iprop(P ∗ R)
  ex0 : ∀ {P : PROP}, iprop(◇ M P) ⊢ M P

theorem e_sub {E1 E2 : CoPset} (h : E2 ⊆ E1) (e : E1 = ∅) : E2 = ∅ :=
  CoPset.ext fun p => ⟨fun hp => e ▸ h p hp, fun hp => (CoPset.mem_empty hp).elim⟩
theorem e_unl {E1 E2 : CoPset} (e : E1 ∪ E2 = ∅) : E1 = ∅ :=
  e_sub (fun _ hp => LawfulSet.mem_union.2 (.inl hp)) e
theorem e_unr {E1 E2 : CoPset} (e : E1 ∪ E2 = ∅) : E2 = ∅ :=
  e_sub (fun _ hp => LawfulSet.mem_union.2 (.inr hp)) e
theorem e_dj {E1 E2 : CoPset} (e : E1 = ∅) : E1 ## E2 :=
  fun _ ⟨h1, _⟩ => CoPset.mem_empty (e ▸ h1)
theorem e_un {E1 E2 : CoPset} (e1 : E1 = ∅) (e2 : E2 = ∅) : E1 ∪ E2 = ∅ := by
  subst e1; subst e2; exact LawfulSet.union_empty_left

variable {PROP : Type _} [BI PROP]

/-- The fancy update: nothing to show unless the source mask is empty, then M and an empty target. -/
def zf (L : LM PROP) (E1 E2 : CoPset) (P : PROP) : PROP :=
  iprop(⌜E1 = ∅⌝ → L.M iprop(⌜E2 = ∅⌝ ∧ P))

def zFupd (L : LM PROP) : BIFUpdate PROP where
  fupd := zf L
  ne := ⟨fun _ _ _ h => imp_ne.ne .rfl (L.ne.ne (and_ne.ne .rfl h))⟩
  subset {E1 E2} h := imp_intro <| pure_elim_right fun e1 =>
    have e2 := e_sub h e1
    L.intro.trans <| L.mono <| and_intro (pure_intro e2) <| imp_intro <| pure_elim_right fun _ =>
      L.intro.trans <| L.mono <| and_intro (pure_intro e1) .rfl
  except0 := imp_intro <| pure_elim_right fun e1 =>
    (except0_mono (pure_imp_elim e1)).trans L.ex0
  mono h := imp_mono_right (L.mono (and_mono .rfl h))
  trans := imp_intro <| pure_elim_right fun e1 =>
    (pure_imp_elim e1).trans <| (L.mono (pure_elim_left fun e2 => pure_imp_elim e2)).trans L.join
  mask_frame_right_strong {E1 E2 Ef P} _ := imp_intro <| pure_elim_right fun e =>
    (pure_imp_elim (e_unl e)).trans <| L.mono <| pure_elim_left fun e2 =>
      and_intro (pure_intro (e_un e2 (e_unr e))) (pure_imp_elim (e_dj e2))
  frame_right := imp_intro <| pure_elim_right fun e1 =>
    (sep_mono_left (pure_imp_elim e1)).trans <| L.frame.trans <| L.mono <| by
      iintro ⟨⟨%e, HP⟩, HR⟩
      isplit
      · ipureintro; exact e
      · isplitl [HP]
        · iexact HP
        · iexact HR

/-- except0 as the closure modality. -/
def exL : LM PROP where
  M P := iprop(◇ P)
  ne := ⟨fun _ _ _ h => or_ne.ne .rfl h⟩
  mono := except0_mono
  intro := except0_intro
  join := except0_idem.1
  frame := except0_frame_right
  ex0 := except0_idem.1

end T1c0

namespace T1c0
open Iris Iris.BI Iris.Std
variable {PROP : Type _} [Sbi PROP]

theorem zk_keep (E E' : CoPset) (Pi : SiProp) (R : PROP) :
    iprop(zf (exL (PROP := PROP)) E E' iprop(<si_pure> Pi) ∧ (<si_pure> Pi -∗ zf (exL (PROP := PROP)) E E R)) ⊢ zf (exL (PROP := PROP)) E E R :=
  imp_intro <| pure_elim_right fun e =>
    (and_mono ((pure_imp_elim e).trans (except0_mono and_elim_r)) (and_intro .rfl (except0_intro (P := iprop(<si_pure> Pi -∗ zf (exL (PROP := PROP)) E E R))))).trans <|
    (and_mono .rfl and_elim_r).trans <| except0_and.2.trans <| (except0_mono <|
      persistent_and_affinely_sep_left_mp.trans <| (sep_mono_left affinely_elim).trans <| (sep_mono_right .rfl).trans <| wand_elim_right.trans (pure_imp_elim e)).trans except0_idem.1

theorem zk_later (E : CoPset) (Pi : SiProp) :
    iprop(▷ zf (exL (PROP := PROP)) E E iprop(<si_pure> Pi)) ⊢ zf (exL (PROP := PROP)) E E iprop(▷ ◇ <si_pure> Pi) :=
  imp_intro <| pure_elim_right fun e =>
    (later_mono ((pure_imp_elim e).trans (except0_mono and_elim_r))).trans <|
      except0_intro.trans (except0_mono (and_intro (pure_intro e) .rfl))

theorem zk_one (E : CoPset) (e : E = ∅) (Ψ : SiProp → Prop) (q : SiProp) :
    iprop(⌜Ψ q⌝ → zf (exL (PROP := PROP)) E E iprop(<si_pure> q)) ⊢ iprop(◇ (⌜Ψ q⌝ → <si_pure> q)) := by
  by_cases hq : Ψ q
  · exact (pure_imp_elim hq).trans <| (pure_imp_elim e).trans <|
      except0_mono (imp_intro (and_elim_l.trans and_elim_r))
  · exact true_intro.trans <| except0_intro.trans <| except0_mono <|
      imp_intro (pure_elim_right fun h => (hq h).elim)

theorem zk_all (E : CoPset) (Ψ : SiProp → Prop) :
    iprop(∀ q, ⌜Ψ q⌝ → zf (exL (PROP := PROP)) E E iprop(<si_pure> q)) ⊢ zf (exL (PROP := PROP)) E E iprop(<si_pure> (sForall Ψ)) :=
  imp_intro <| pure_elim_right fun e =>
    (forall_mono (zk_one E e Ψ)).trans <|
    except0_forall.2.trans <| except0_mono <| and_intro (pure_intro e) Sbi.siPure_sForall_mpr

theorem zFS : @BIFUpdateSbi PROP _ (zFupd exL) _ :=
  @BIFUpdateSbi.mk PROP _ (zFupd exL) _ (fun E' Pi R => zk_keep _ E' Pi R) (fun E Pi => zk_later E Pi)
    (fun E Ψ => zk_all E Ψ)

end T1c0

namespace T1c0
open Iris Iris.BI Iris.Std

theorem zM {PROP : Type _} [BI PROP] {L : LM PROP} {Y X : PROP} (h : Y ⊢ L.M X) : Y ⊢ zf L ∅ ∅ X :=
  imp_intro ((and_elim_l.trans h).trans (L.mono (and_intro (pure_intro rfl) .rfl)))
theorem zO {PROP : Type _} [BI PROP] {L : LM PROP} {X : PROP} : zf L ∅ ∅ X ⊢ L.M X :=
  (pure_imp_elim rfl).trans (L.mono and_elim_r)

/-! Model (a): `UPred NA` (non-affine, NA = two-element monoid with the equality order) with
the fupd `zf exL` (= except0 at empty masks): lawful, `BIFUpdateSbi`, not affine. -/

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

theorem na_pl : (iprop(True) : UPred NA) ⊢ iprop(■ emp) := fun _ _ _ => rfl

theorem na_ex (n : Nat) {Q : UPred NA} (hQ : ¬ Q.holds (n + 1) ⟨.a, trivial⟩)
    (h : (iprop(True) : UPred NA) ⊢ iprop(◇ Q)) : False := by
  rcases h (n + 1) ⟨.a, trivial⟩ trivial with h0 | h1
  · exact h0
  · exact hQ h1

theorem na_emp1 : ¬ (iprop(emp) : UPred NA).holds 1 ⟨.a, trivial⟩ := fun h => by cases h
theorem na_xemp1 : ¬ (iprop(◇ emp) : UPred NA).holds 1 ⟨.a, trivial⟩ := fun h =>
  h.elim (fun f => f) (fun h => by cases h)
theorem na_lxemp2 : ¬ (iprop(▷ ◇ emp) : UPred NA).holds 2 ⟨.a, trivial⟩ := fun h =>
  h.elim (fun f => f) (fun h => by cases h)

/-! Model (b): `SiProp` with the fupd `zf cL`, `cL X := ◇ X ∨ ▷ ▷ False`: lawful, affine,
but `▷ |={∅}=> False ⊬ |={∅}=> ▷ ◇ False` (fails at step 2), so not `BIFUpdateSbi`. -/

abbrev sC : SiProp := iprop(▷ ▷ False)

theorem sx0g {PROP : Type _} [BI PROP] {C X : PROP} : iprop(◇ (◇ X ∨ C)) ⊢ iprop(◇ X ∨ C) :=
  except0_or.1.trans <| or_elim (except0_idem.1.trans or_intro_l) <|
    (show iprop(▷ False ∨ C) ⊢ iprop(◇ X ∨ C) from or_elim (or_intro_l.trans or_intro_l) or_intro_r)

/-- The closure modality `X ↦ ◇ X ∨ C` (C a fixed proposition) on an affine BI. -/
def cLg {PROP : Type _} [BI PROP] [BIAffine PROP] (C : PROP) : LM PROP where
  M X := iprop(◇ X ∨ C)
  ne := ⟨fun _ _ _ h => or_ne.ne (or_ne.ne .rfl h) .rfl⟩
  mono h := or_mono (except0_mono h) .rfl
  intro := except0_intro.trans or_intro_l
  join := or_elim sx0g or_intro_r
  frame := sep_or_right.1.trans (or_mono except0_frame_right sep_elim_left)
  ex0 := sx0g

abbrev cL : LM SiProp := cLg sC

theorem s_bad (h : (iprop(▷ ▷ ▷ False) : SiProp) ⊢ iprop(◇ ▷ ◇ False ∨ sC)) : False := by
  rcases h 2 trivial with ((h | h | h) | h) <;> exact h

theorem s_lhs {X : SiProp} : (iprop(▷ ▷ ▷ False) : SiProp) ⊢ iprop(▷ zf cL ∅ ∅ X) :=
  later_mono (zM (L := cL) (show sC ⊢ iprop(◇ X ∨ sC) from or_intro_r))

end T1c0

open Iris Iris.BI Iris.Std T1c0

-- `Iris.fupd_plainly_mask` idx 4: necessary (UPred NA (non-affine) with fupd zf exL (except0 at empty masks; lawful, BIFUpdateSbi), E = E' = empty, P = emp: plainly emp holds, emp fails at the non-unit a, step 1)
theorem t1c0_1 : ¬ drop0% Iris.fupd_plainly_mask 4 := fun h =>
  na_ex 0 na_emp1 <| ((zM (L := exL) (na_pl.trans exL.intro)).trans
    (@h (UPred NA) _ (zFupd exL) zFS ∅ ∅ iprop(emp))).trans zO
-- `Iris.fupd_plainly_later` idx 4: necessary (UPred NA with zf exL, E = empty, P = emp: RHS is except0 later except0 emp, false at a, step 2)
theorem t1c0_2 : ¬ drop0% Iris.fupd_plainly_later 4 := fun h =>
  na_ex 1 na_lxemp2 <| ((later_intro.trans (later_mono (zM (L := exL) (na_pl.trans exL.intro)))).trans
    (@h (UPred NA) _ (zFupd exL) zFS ∅ iprop(emp))).trans zO
-- `Iris.fupd_plainly_laterN` idx 4: necessary (UPred NA with zf exL, n = 0, E = empty, P = emp: RHS except0 except0 emp, false at a, step 1)
theorem t1c0_3 : ¬ drop0% Iris.fupd_plainly_laterN 4 := fun h =>
  na_ex 0 na_xemp1 <| ((zM (L := exL) (na_pl.trans exL.intro)).trans
    (@h (UPred NA) _ (zFupd exL) zFS ∅ 0 iprop(emp))).trans zO
-- `Iris.fupd_plainly_forall_2` idx 5: necessary (UPred NA with zf exL, alpha = True, E = empty, Phi = emp)
theorem t1c0_4 : ¬ drop0% Iris.fupd_plainly_forall_2 5 := fun h =>
  na_ex 0 na_emp1 <| ((forall_intro fun _ => zM (L := exL) (na_pl.trans exL.intro)).trans
    (@h (UPred NA) _ (zFupd exL) zFS True ∅ (fun _ => iprop(emp)))).trans (zO.trans (except0_mono (forall_elim trivial)))
-- `Iris.fupd_plainly_later` idx 3: necessary (SiProp with fupd zf cL (except0 or later later False; lawful, not BIFUpdateSbi), E = empty, P = False, step 2)
theorem t1c0_5 : ¬ drop0% Iris.fupd_plainly_later 3 := fun h =>
  s_bad <| s_lhs.trans <| (@h SiProp _ (zFupd cL) _ ∅ iprop(False)).trans (zO (L := cL))
-- `Iris.fupd_plain_later` idx 3: necessary (SiProp with zf cL, E = empty, P = False, step 2)
theorem t1c0_6 : ¬ drop0% Iris.fupd_plain_later 3 := fun h =>
  s_bad <| s_lhs.trans <| (@h SiProp _ (zFupd cL) _ ∅ iprop(False) _).trans (zO (L := cL))
-- `Iris.fupd_plainly_laterN` idx 3: necessary (SiProp with zf cL, n = 1, E = empty, P = False, step 2)
theorem t1c0_7 : ¬ drop0% Iris.fupd_plainly_laterN 3 := fun h =>
  s_bad <| s_lhs.trans <| (@h SiProp _ (zFupd cL) _ ∅ 1 iprop(False)).trans (zO (L := cL))
-- `Iris.fupd_plain_laterN` idx 3: necessary (SiProp with zf cL, n = 1, E = empty, P = False, step 2)
theorem t1c0_8 : ¬ drop0% Iris.fupd_plain_laterN 3 := fun h =>
  s_bad <| s_lhs.trans <| (@h SiProp _ (zFupd cL) _ ∅ 1 iprop(False) _).trans (zO (L := cL))
-- `Iris.step_fupd_plain` idx 3: necessary (SiProp with zf cL, E1 = E2 = empty, P = False, step 2)
theorem t1c0_9 : ¬ drop0% Iris.step_fupd_plain 3 := fun h =>
  s_bad <| (s_lhs.trans (zM (L := cL) cL.intro)).trans <| (@h SiProp _ (zFupd cL) _ ∅ ∅ iprop(False) _).trans (zO (L := cL))
-- `Iris.step_fupdN_plain` idx 3: necessary (SiProp with zf cL, n = 1, E1 = E2 = empty, P = False, step 2)
theorem t1c0_10 : ¬ drop0% Iris.step_fupdN_plain 3 := fun h =>
  s_bad <| (s_lhs.trans (zM (L := cL) cL.intro)).trans <| (@h SiProp _ (zFupd cL) _ ∅ ∅ 1 iprop(False) _).trans (zO (L := cL))
-- `Iris.BIFUpdateSbi.fupd_siPure_later` idx 4: necessary (SiProp with zf cL, E = empty, Pi = False, step 2)
theorem t1c0_11 : ¬ drop0% Iris.BIFUpdateSbi.fupd_siPure_later 4 := fun h =>
  s_bad <| s_lhs.trans <| (@h SiProp _ (zFupd cL) _ ∅ iprop(False)).trans (zO (L := cL))

namespace T1c0
open Iris Iris.BI Iris.Std Iris.OFE

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF

theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩

theorem fupd_false (E1 E2 : CoPset) (H : ∀ [InvGS_gen .hasNoLC CGF], ⊢ (iprop(|={E1,E2}=> ⌜False⌝) : IProp CGF)) : False :=
  pure_soundness (PROP := IProp CGF)
    (fupd_soundness .hasNoLC 0 (E1 := E1) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))

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

theorem emp_mp {PROP : Type _} [BI PROP] {X Y : PROP} (h : ⊢ iprop(X -∗ Y)) (a : ⊢ X) : ⊢ Y :=
  (emp_sep.2.trans (sep_mono h a)).trans wand_elim_left

end T1c0

open Iris Iris.BI Iris.Std T1c0

-- `Iris.fupd_plain_mask` idx 8: necessary (IProp with its BIFUpdateSbi instance, E = top, E' = empty, P = ownE top (not plain): opening gives ownE top, which clashes at mask top; fupd soundness)
theorem t1c0_12 : ¬ drop0% Iris.fupd_plain_mask 8 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => (own_open.trans (@h (IProp CGF) _ _ _ _ ⊤ ∅ (ownE ⊤))).trans
    ((fupd_mono (own_conf ⊤)).trans fupd_trans)
-- `Iris.fupd_keep_plain` idx 10: necessary (IProp, E1 = E2 = top, E2' = empty, P = ownE top, R = False)
theorem t1c0_13 : ¬ drop0% Iris.fupd_keep_plain 10 := fun h =>
  fupd_false ⊤ ⊤ fun {_} => (and_intro own_open (wand_intro (emp_sep.1.trans (own_conf ⊤)))).trans
    (@h (IProp CGF) _ _ _ _ ⊤ ⊤ ∅ (ownE ⊤) iprop(⌜False⌝))
-- `Iris.fupd_keep_plain_sep` idx 9: necessary (IProp, E = top, E' = empty, P = ownE top, R = emp)
theorem t1c0_14 : ¬ drop0% Iris.fupd_keep_plain_sep 9 := fun h =>
  fupd_false ⊤ ⊤ fun {_} =>
    (emp_mp (emp_mp (@h (IProp CGF) _ _ _ _ ⊤ ∅ (ownE ⊤) iprop(emp)) (wand_intro (emp_sep.1.trans own_open)))
      (.rfl : (iprop(emp) : IProp CGF) ⊢ iprop(emp))).trans
    ((fupd_mono (sep_elim_left.trans (own_conf ⊤))).trans fupd_trans)
-- `Iris.fupd_plain_forall` idx 10: necessary (IProp, alpha = False, E1 = empty, E2 = top: the right side is True, the left side opens the full mask from empty)
theorem t1c0_15 : ¬ drop0% Iris.fupd_plain_forall 10 := fun h =>
  open_top_false fun {_} => ⟨_, (forall_intro fun a => a.elim).trans
    (@h (IProp CGF) _ _ _ False _ ∅ ⊤ (fun a => a.elim) (fun a => a.elim)).2⟩
-- `Iris.step_fupd_plain_forall` idx 10: necessary (IProp, alpha = False, Eo = empty, Ei = top: the left side starts with |={empty,top}=>)
theorem t1c0_16 : ¬ drop0% Iris.step_fupd_plain_forall 10 := fun h =>
  open_top_false fun {_} => ⟨_, (forall_intro fun a => a.elim).trans
    (@h (IProp CGF) _ _ _ False _ ∅ ⊤ (fun a => a.elim) (fun a => a.elim)).2⟩

namespace T1c0
open Iris Iris.BI Iris.Std

theorem minN (p : Nat → Prop) : ∀ n, p n → ∃ m, p m ∧ ∀ k, k < m → ¬ p k
  | n, h => by
    by_cases hc : ∃ k, k < n ∧ p k
    · obtain ⟨k, hk, pk⟩ := hc
      exact minN p k pk
    · exact ⟨n, h, fun k hk pk => hc ⟨k, hk, pk⟩⟩
termination_by n => n

/-- SiProp is a well-ordered chain: every nonempty family has a least member. -/
theorem simin {A : Sort _} (Φ : A → SiProp) (hA : Nonempty A) : ∃ a0, ∀ a, Φ a0 ⊢ Φ a := by
  by_cases hex : ∃ n, ∃ a, ¬ (Φ a).holds n
  · obtain ⟨n, hn⟩ := hex
    obtain ⟨m, ⟨a0, ha0⟩, hmin⟩ := minN (fun n => ∃ a, ¬ (Φ a).holds n) n hn
    refine ⟨a0, fun a k hk => ?_⟩
    have hkm : k < m := Nat.lt_of_not_le fun hc => ha0 ((Φ a0).closed hk hc)
    exact Classical.byContradiction fun hc => hmin k hkm ⟨a, hc⟩
  · obtain ⟨a0⟩ := hA
    exact ⟨a0, fun a n _ => Classical.byContradiction fun hc => hex ⟨n, a, hc⟩⟩

/-- `fupd_siPure_forall_2` without `BIFUpdateSbi`: pick the least member of the family. -/
theorem fsf2 {PROP : Type _} [Sbi PROP] [BIFUpdate PROP] {E : CoPset} {A : Sort _} {Φi : A → SiProp} :
    (iprop(∀ x, |={E}=> <si_pure> Φi x) : PROP) ⊢ iprop(|={E}=> ∀ x, <si_pure> Φi x) := by
  by_cases hA : Nonempty A
  · obtain ⟨a0, h0⟩ := simin Φi hA
    exact (forall_elim a0).trans (BIFUpdate.mono (forall_intro fun a => siPure_mono (h0 a)))
  · exact true_intro.trans ((forall_intro fun x => (hA ⟨x⟩).elim).trans fupd_intro)

/-- For a nonempty family of plain propositions in an affine Sbi, one member entails all. -/
theorem pmin {PROP : Type _} [Sbi PROP] [BIAffine PROP] {α : Sort _} {Φ : α → PROP} [∀ a, Plain (Φ a)]
    (hA : Nonempty α) : ∃ a0, Φ a0 ⊢ iprop(∀ a, Φ a) := by
  obtain ⟨a0, h0⟩ := simin (fun a => iprop(<si_emp_valid> Φ a)) hA
  exact ⟨a0, forall_intro fun a => Plain.plain.trans ((siPure_mono (h0 a)).trans siPure_siEmpValid_elim)⟩

end T1c0

open Iris Iris.BI Iris.Std T1c0

-- `Iris.fupd_siPure_forall_2` idx 3: removable (SiProp is a well-ordered chain: the least member Φi a0 of the family entails all, so the update for a0 suffices; empty family: fupd_intro)
theorem t1c0_25 : drop% Iris.fupd_siPure_forall_2 3 := by
  intro PROP _ _ E A Φi
  exact fsf2
-- `Iris.fupd_plainly_forall_2` idx 3: removable (fupd_siPure_forall_2 without BIFUpdateSbi (least member of a SiProp family), then plainly elimination by BIAffine)
theorem t1c0_26 : drop% Iris.fupd_plainly_forall_2 3 := by
  intro PROP _ _ α _ E Φ
  exact fsf2.trans (BIFUpdate.mono (forall_mono fun _ => siPure_siEmpValid_elim))
-- `Iris.fupd_plain_forall_2` idx 3: removable (Plain to plainly, then as for fupd_plainly_forall_2 via the least member of a SiProp family)
theorem t1c0_27 : drop% Iris.fupd_plain_forall_2 3 := by
  intro PROP _ _ α _ E Φ _
  exact (forall_mono fun _ => BIFUpdate.mono Plain.plain).trans
    (fsf2.trans (BIFUpdate.mono (forall_mono fun _ => siPure_siEmpValid_elim)))
-- `Iris.fupd_plain_forall` idx 3: removable (nonempty alpha: some Phi a0 entails all Phi a (least emp-validity, Plain, BIAffine); empty alpha: fupd_mask_intro_discard with E2 below E1)
theorem t1c0_28 : drop% Iris.fupd_plain_forall 3 := by
  intro PROP _ _ α _ E1 E2 Φ _ h
  refine ⟨fupd_forall, ?_⟩
  by_cases hA : Nonempty α
  · obtain ⟨a0, h0⟩ := pmin (Φ := Φ) hA
    exact (forall_elim a0).trans (BIFUpdate.mono h0)
  · exact true_intro.trans ((forall_intro fun x => (hA ⟨x⟩).elim).trans (fupd_mask_intro_discard h))
-- `Iris.fupd_plain_forall'` idx 3: removable (as fupd_plain_forall idx 3 with E1 = E2)
theorem t1c0_29 : drop% Iris.fupd_plain_forall' 3 := by
  intro PROP _ _ α _ E Φ _
  refine ⟨fupd_forall, ?_⟩
  by_cases hA : Nonempty α
  · obtain ⟨a0, h0⟩ := pmin (Φ := Φ) hA
    exact (forall_elim a0).trans (BIFUpdate.mono h0)
  · exact true_intro.trans ((forall_intro fun x => (hA ⟨x⟩).elim).trans fupd_intro)
-- `Iris.step_fupd_plain_forall` idx 3: removable (nonempty alpha: some Phi a0 entails all Phi a, then step_fupd_mono; empty alpha: step_fupd_intro with Ei below Eo)
theorem t1c0_30 : drop% Iris.step_fupd_plain_forall 3 := by
  intro PROP _ _ α _ Eo Ei Φ _ h
  refine ⟨forall_intro fun a => step_fupd_mono (forall_elim a), ?_⟩
  by_cases hA : Nonempty α
  · obtain ⟨a0, h0⟩ := pmin (Φ := Φ) hA
    exact (forall_elim a0).trans (step_fupd_mono h0)
  · exact true_intro.trans ((forall_intro fun x => (hA ⟨x⟩).elim).trans (later_intro.trans (step_fupd_intro h)))

namespace T1c0
open Iris Iris.BI Iris.Std

/-- For a nonempty family of plain absorbing propositions in an Sbi, one member entails all. -/
theorem pminA {PROP : Type _} [Sbi PROP] {α : Sort _} {Φ : α → PROP} [∀ a, Plain (Φ a)] [∀ a, Absorbing (Φ a)]
    (hA : Nonempty α) : ∃ a0, Φ a0 ⊢ iprop(∀ a, Φ a) := by
  obtain ⟨a0, h0⟩ := simin (fun a => iprop(<si_emp_valid> Φ a)) hA
  exact ⟨a0, forall_intro fun a => Plain.plain.trans ((siPure_mono (h0 a)).trans siPure_siEmpValid_elim)⟩

end T1c0

open Iris Iris.BI Iris.Std T1c0

-- `Iris.bupd_plain_forall` idx 3: removable (plain absorbing Phi x is equivalent to the SiProp proposition emp-valid Phi x; SiProp is a well-ordered chain, so for nonempty A some Phi a0 entails all Phi x; empty A: BIUpdate.intro)
theorem t1c0_31 : drop% Iris.bupd_plain_forall 3 := by
  intro PROP _ _ A Φ _ _
  refine ⟨forall_intro fun x => BIUpdate.mono (forall_elim x), ?_⟩
  by_cases hA : Nonempty A
  · obtain ⟨a0, h0⟩ := pminA (Φ := Φ) hA
    exact (forall_elim a0).trans (BIUpdate.mono h0)
  · exact true_intro.trans ((forall_intro fun x => (hA ⟨x⟩).elim).trans BIUpdate.intro)

namespace T1c0
open Iris Iris.BI Iris.Std

/-! ND: unit e, a start token s and two exclusive outcomes c0, c1 (any product of non-units is
invalid), equality order. In `UPred ND` the basic update from s may choose c0 or c1, but no
resource is above both, so |==> does not commute with ∀ over non-plain propositions. -/
inductive ND | e | s | c0 | c1 | bot deriving DecidableEq

def ND.op : ND → ND → ND
  | .e, y => y
  | x, .e => x
  | _, _ => .bot

instance : OFE ND := OFE.ofDiscrete ND
instance : OFE.Discrete ND := ⟨id⟩

instance ndORA : ORA ND := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := ND.op
  Valid := fun x => x ≠ .bot
  Order := Eq
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y h; cases x <;> cases y <;> first | exact h | exact fun h' => nomatch h' | simp_all [ND.op]
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := by intro x y h hv; cases h; exact hv
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> rfl
  increasing_closed := by intro x y _ h; cases h; assumption }

instance : OrderRefl ND := ⟨fun x => show x = x from rfl⟩

instance ndUORA : UORA ND where
  unit := .e
  unit_valid := fun h => nomatch h
  unit_left_id := rfl
  pcore_unit := rfl

def ndc (b : Bool) : ND := if b then .c1 else .c0

/-- The outcome propositions: own c_b, made absorbing. -/
abbrev ndΦ (b : Bool) : UPred ND := iprop(<absorb> UPred.ownM (ndc b))

end T1c0

open Iris Iris.BI Iris.Std T1c0

-- `Iris.bupd_plain_forall` idx 6: necessary (at Type: UPred ND (start token s updates to either of two exclusive outcomes c0, c1), A = Bool, Phi b = absorbingly own c_b: each update succeeds from s, no resource owns both)
theorem t1c0_32 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIUpdate PROP] [Iris.BIBUpdateSbi PROP] {A : Type}
    (Φ : A → PROP) [∀ (x : A), Iris.BI.Absorbing (Φ x)], (|==> ∀ x, Φ x) ⊣⊢ ∀ x, |==> Φ x) := fun h => by
  have H := (@h (UPred ND) _ _ _ Bool ndΦ (fun _ => inferInstance)).2 0 ⟨.s, fun h => nomatch h⟩ (by
    intro p ⟨b, hp⟩
    subst hp
    intro k yf _ hv
    cases yf
    · exact ⟨ndc b, by cases b <;> (intro h; cases h), ⟨.e, ndc b, by cases b <;> rfl, trivial, rfl⟩⟩
    all_goals exact absurd rfl hv)
  obtain ⟨x', hv, hx⟩ := H 0 .e (Nat.le_refl 0) (fun h => nomatch h)
  have h0 := hx _ ⟨false, rfl⟩
  have h1 := hx _ ⟨true, rfl⟩
  obtain ⟨y1, y2, e0, -, o0⟩ := h0
  obtain ⟨z1, z2, e1, -, o1⟩ := h1
  have e0' : ND.op y1 y2 = x' := e0
  have e1' : ND.op z1 z2 = x' := e1
  have o0' : ndc false = y2 := o0
  have o1' : ndc true = z2 := o1
  have hv' : ND.op x' ND.e ≠ ND.bot := hv
  subst o0' o1'
  cases y1 <;> simp only [ND.op, ndc] at e0' <;> subst e0' <;>
    first | exact hv' rfl | (cases z1 <;> simp only [ND.op, ndc] at e1' <;> exact absurd e1' (by decide))

namespace T1c0
open Iris Iris.BI Iris.Std
variable {PROP : Type _} [Sbi PROP] [BIUpdate PROP]

/-- The closure modality `|==> ◇` (from a lawful basic update). -/
def bL : LM PROP where
  M X := iprop(|==> ◇ X)
  ne := ⟨fun _ _ _ h => BIUpdate.bupd_ne.ne (or_ne.ne .rfl h)⟩
  mono h := BIUpdate.mono (except0_mono h)
  intro := except0_intro.trans BIUpdate.intro
  join := (BIUpdate.mono except0_bupd).trans (BIUpdate.trans.trans (BIUpdate.mono except0_idem.1))
  frame := BIUpdate.frame_right.trans (BIUpdate.mono except0_frame_right)
  ex0 := except0_bupd.trans (BIUpdate.mono except0_idem.1)

variable [BIBUpdateSbi PROP]

theorem bsp {Pi : SiProp} : (bL (PROP := PROP)).M iprop(<si_pure> Pi) ⊢ iprop(◇ <si_pure> Pi) :=
  (BIUpdate.mono siPure_except0.2).trans ((BIBUpdateSbi.bupd_siPure _).trans siPure_except0.1)

theorem zb_keep (E E' : CoPset) (Pi : SiProp) (R : PROP) :
    iprop(zf (bL (PROP := PROP)) E E' iprop(<si_pure> Pi) ∧ (<si_pure> Pi -∗ zf (bL (PROP := PROP)) E E R)) ⊢ zf (bL (PROP := PROP)) E E R :=
  imp_intro <| pure_elim_right fun e =>
    (and_mono ((pure_imp_elim e).trans ((bL.mono and_elim_r).trans bsp)) (and_intro .rfl (except0_intro (P := iprop(<si_pure> Pi -∗ zf (bL (PROP := PROP)) E E R))))).trans <|
    (and_mono .rfl and_elim_r).trans <| except0_and.2.trans <| (except0_mono <|
      persistent_and_affinely_sep_left_mp.trans <| (sep_mono_left affinely_elim).trans <| wand_elim_right.trans (pure_imp_elim e)).trans bL.ex0

theorem zb_later (E : CoPset) (Pi : SiProp) :
    iprop(▷ zf (bL (PROP := PROP)) E E iprop(<si_pure> Pi)) ⊢ zf (bL (PROP := PROP)) E E iprop(▷ ◇ <si_pure> Pi) :=
  imp_intro <| pure_elim_right fun e =>
    (later_mono ((pure_imp_elim e).trans ((bL.mono and_elim_r).trans bsp))).trans <|
      bL.intro.trans (bL.mono (and_intro (pure_intro e) .rfl))

theorem zb_one (E : CoPset) (e : E = ∅) (Ψ : SiProp → Prop) (q : SiProp) :
    iprop(⌜Ψ q⌝ → zf (bL (PROP := PROP)) E E iprop(<si_pure> q)) ⊢ iprop(◇ (⌜Ψ q⌝ → <si_pure> q)) := by
  by_cases hq : Ψ q
  · exact (pure_imp_elim hq).trans <| (pure_imp_elim e).trans <| ((bL.mono and_elim_r).trans bsp).trans <|
      except0_mono (imp_intro and_elim_l)
  · exact true_intro.trans <| except0_intro.trans <| except0_mono <|
      imp_intro (pure_elim_right fun h => (hq h).elim)

theorem zb_all (E : CoPset) (Ψ : SiProp → Prop) :
    iprop(∀ q, ⌜Ψ q⌝ → zf (bL (PROP := PROP)) E E iprop(<si_pure> q)) ⊢ zf (bL (PROP := PROP)) E E iprop(<si_pure> (sForall Ψ)) :=
  imp_intro <| pure_elim_right fun e =>
    (forall_mono (zb_one E e Ψ)).trans <|
    except0_forall.2.trans <| (except0_mono (and_intro (pure_intro e) Sbi.siPure_sForall_mpr)).trans BIUpdate.intro

theorem zbFS : @BIFUpdateSbi PROP _ (zFupd bL) _ :=
  @BIFUpdateSbi.mk PROP _ (zFupd bL) _ (fun E' Pi R => zb_keep _ E' Pi R) (fun E Pi => zb_later E Pi)
    (fun E Ψ => zb_all E Ψ)

end T1c0

namespace T1c0
open Iris Iris.BI Iris.Std

/-! NDA: as ND but with the extension order (affine `UPred NDA`): unit e, start token s, two
exclusive outcomes c0, c1; s updates to either outcome, no valid resource is above both. -/
inductive NDA | e | s | c0 | c1 | bot deriving DecidableEq

def NDA.op : NDA → NDA → NDA
  | .e, y => y
  | x, .e => x
  | _, _ => .bot

instance : OFE NDA := OFE.ofDiscrete NDA
instance : OFE.Discrete NDA := ⟨id⟩

instance ndaORA : ORA NDA := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := NDA.op
  Valid := fun x => x ≠ .bot
  Order := fun x y => x = .e ∨ x = y ∨ y = .bot
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y h; cases x <;> cases y <;> first | exact h | exact fun h' => nomatch h' | simp_all [NDA.op]
  ord_trans := by intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all
  op_mono_left := by intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [NDA.op]
  valid_of_ord := by intro x y h hv; cases x <;> cases y <;> simp_all
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; exact .inl rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; exact .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact .inr (.inl rfl)
  increasing_closed := by intro x y hx h z; cases x <;> cases y <;> cases z <;> simp_all [NDA.op] }

instance : OrderRefl NDA := ⟨fun _ => .inr (.inl rfl)⟩

instance ndaUORA : UORA NDA where
  unit := .e
  unit_valid := fun h => nomatch h
  unit_left_id := rfl
  pcore_unit := rfl

instance : IncOrd NDA := ⟨by
  intro x y ⟨z, hz⟩
  show x = .e ∨ x = y ∨ y = .bot
  cases x <;> cases z <;> simp_all [Op.op, NDA.op]⟩

def ndac (b : Bool) : NDA := if b then .c1 else .c0

theorem nda_upd (b : Bool) : NDA.s ~~> ndac b := by
  intro n mz h
  cases mz with
  | none => cases b <;> exact fun h' => nomatch h'
  | some z => cases z <;> cases b <;> first | exact absurd rfl h | exact fun h' => nomatch h'

theorem nda_ups (b : Bool) : (UPred.ownM NDA.s : UPred NDA) ⊢ bL.M (UPred.ownM (ndac b)) :=
  (UPred.bupd_ownM_update (nda_upd b)).trans (BIUpdate.mono except0_intro)

/-- From own s, no update reaches both outcomes (step 1). -/
theorem nda_bad (H : (UPred.ownM NDA.s : UPred NDA) ⊢ bL.M iprop(UPred.ownM (ndac false) ∧ UPred.ownM (ndac true))) : False := by
  obtain ⟨x', hv, hx⟩ := H 1 ⟨.s, fun h => nomatch h⟩ (.inr (.inl rfl)) 1 .e (Nat.le_refl 1) (fun h => nomatch h)
  rcases hx with hf | ⟨h0, h1⟩
  · exact hf
  · have h0' : NDA.c0 = .e ∨ NDA.c0 = x' ∨ x' = .bot := h0
    have h1' : NDA.c1 = .e ∨ NDA.c1 = x' ∨ x' = .bot := h1
    have hv' : NDA.op x' NDA.e ≠ NDA.bot := hv
    cases x' <;> simp_all [NDA.op]

theorem nda_bad2 (H : (UPred.ownM NDA.s : UPred NDA) ⊢
    bL.M iprop(▷ bL.M iprop(UPred.ownM (ndac false) ∧ UPred.ownM (ndac true)))) : False := by
  obtain ⟨x', hv, hx⟩ := H 2 ⟨.s, fun h => nomatch h⟩ (.inr (.inl rfl)) 2 .e (Nat.le_refl 2) (fun h => nomatch h)
  rcases hx with hf | hl
  · exact hf
  · obtain ⟨x'', hv2, hx2⟩ := hl 1 .e (Nat.le_refl 1) hv
    rcases hx2 with hf | ⟨h0, h1⟩
    · exact hf
    · have h0' : NDA.c0 = .e ∨ NDA.c0 = x'' ∨ x'' = .bot := h0
      have h1' : NDA.c1 = .e ∨ NDA.c1 = x'' ∨ x'' = .bot := h1
      have hv' : NDA.op x'' NDA.e ≠ NDA.bot := hv2
      cases x'' <;> simp_all [NDA.op]

end T1c0

open Iris Iris.BI Iris.Std T1c0

-- `Iris.fupd_plain_forall_2` idx 8: necessary (at Type: affine UPred NDA with fupd zf bL (bupd then except0 at empty masks; lawful, BIFUpdateSbi), alpha = Bool, E = empty, Phi b = own c_b (not plain): from own s each outcome is reachable, both together are not)
theorem t1c0_33 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP] {α : Type}
    [Iris.BI.BIAffine PROP] {E : CoPset} {Φ : α → PROP}, (∀ a, |={E}=> Φ a) ⊢ |={E}=> ∀ a, Φ a) := fun h =>
  nda_bad <| ((forall_intro fun b => zM (L := bL) (nda_ups b)).trans
    (@h (UPred NDA) _ (zFupd bL) zbFS Bool _ ∅ (fun b => UPred.ownM (ndac b)))).trans
    ((zO (L := bL)).trans (bL.mono (and_intro (forall_elim false) (forall_elim true))))
-- `Iris.fupd_plain_forall` idx 9: necessary (at Type: affine UPred NDA with zf bL, alpha = Bool, E1 = E2 = empty, Phi b = own c_b)
theorem t1c0_34 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP] {α : Type}
    [Iris.BI.BIAffine PROP] {E1 E2 : CoPset} {Φ : α → PROP},
    E2 ⊆ E1 → (|={E1,E2}=> ∀ a, Φ a) ⊣⊢ ∀ a, |={E1,E2}=> Φ a) := fun h =>
  nda_bad <| ((forall_intro fun b => zM (L := bL) (nda_ups b)).trans
    (@h (UPred NDA) _ (zFupd bL) zbFS Bool _ ∅ ∅ (fun b => UPred.ownM (ndac b)) LawfulSet.subset_refl).2).trans
    ((zO (L := bL)).trans (bL.mono (and_intro (forall_elim false) (forall_elim true))))
-- `Iris.fupd_plain_forall'` idx 8: necessary (at Type: affine UPred NDA with zf bL, alpha = Bool, E = empty, Phi b = own c_b)
theorem t1c0_35 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP] {α : Type}
    [Iris.BI.BIAffine PROP] {E : CoPset} {Φ : α → PROP}, (|={E}=> ∀ a, Φ a) ⊣⊢ ∀ a, |={E}=> Φ a) := fun h =>
  nda_bad <| ((forall_intro fun b => zM (L := bL) (nda_ups b)).trans
    (@h (UPred NDA) _ (zFupd bL) zbFS Bool _ ∅ (fun b => UPred.ownM (ndac b))).2).trans
    ((zO (L := bL)).trans (bL.mono (and_intro (forall_elim false) (forall_elim true))))
-- `Iris.step_fupd_plain_forall` idx 9: necessary (at Type: affine UPred NDA with zf bL, alpha = Bool, Eo = Ei = empty, Phi b = own c_b: each step update reaches one outcome, none reaches both; step 2)
theorem t1c0_36 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP] {α : Type}
    [Iris.BI.BIAffine PROP] {Eo Ei : CoPset} {Φ : α → PROP},
    Ei ⊆ Eo → (|={Eo}[Ei]▷=> ∀ a, Φ a) ⊣⊢ ∀ a, |={Eo}[Ei]▷=> Φ a) := fun h =>
  nda_bad2 <| ((forall_intro fun b => zM (L := bL) ((zM (L := bL) (nda_ups b)).trans (later_intro.trans bL.intro))).trans
    (@h (UPred NDA) _ (zFupd bL) zbFS Bool _ ∅ ∅ (fun b => UPred.ownM (ndac b)) LawfulSet.subset_refl).2).trans
    ((zO (L := bL)).trans (bL.mono (later_mono ((zO (L := bL)).trans (bL.mono (and_intro (forall_elim false) (forall_elim true)))))))

namespace T1c0
open Iris Iris.BI Iris.Std

/-! Atomic accessors over nil telescopes in `SiProp` with the fupd `sF := zf exL` (except0 at
empty masks; lawful): accessors are except0 of simple propositions, so they are not 1-close. -/

@[reducible] def sF : BIFUpdate SiProp := zFupd exL
attribute [local instance] sF

abbrev UIdx : Iris.BI.BiIndex := { car := Nat, rel := inferInstance }

theorem sdist {A B : SiProp} (hA : iprop(True) ⊢ A) (hB : B ⊢ iprop(◇ ◇ False)) (h : A ≡{1}≡ B) : False := by
  have := (h (Nat.le_refl 1)).1 (hA 1 trivial)
  rcases hB 1 this with h | h | h <;> exact h

theorem zT {Y : SiProp} : Y ⊢ zf exL ∅ ∅ iprop(True) := zM (true_intro.trans except0_intro)
theorem sepT {Y Z : SiProp} (h : Y ⊢ Z) : Y ⊢ iprop(True ∗ Z) := (h.trans emp_sep.2).trans (sep_mono_left true_intro)

theorem acc_true {Φ : Tele.nil.Arg → Tele.nil.Arg → SiProp} : iprop(True) ⊢
    atomic_acc (TA := .nil) (TB := .nil) ∅ ∅ (fun _ => iprop(True)) iprop(True) (fun _ _ => iprop(False)) Φ :=
  zM (L := exL) <| (sepT (and_intro (wand_intro zT) (wand_intro (sep_elim_right.trans false_elim)))).trans except0_intro

theorem acc_true2 : (iprop(True) : SiProp) ⊢
    atomic_acc (TA := .nil) (TB := .nil) ∅ ∅ (fun _ => iprop(True)) iprop(True) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) :=
  zM (L := exL) <| (sepT (and_intro (wand_intro zT) (wand_intro zT))).trans except0_intro

theorem acc_a {P : SiProp} {β Φ : Tele.nil.Arg → Tele.nil.Arg → SiProp} :
    atomic_acc (TA := .nil) (TB := .nil) ∅ ∅ (fun _ => iprop(False)) P β Φ ⊢ iprop(◇ ◇ False) :=
  (zO (L := exL)).trans (except0_mono (sep_elim_left.trans except0_intro))

theorem acc_p {β Φ : Tele.nil.Arg → Tele.nil.Arg → SiProp} :
    atomic_acc (TA := .nil) (TB := .nil) ∅ ∅ (fun _ => iprop(True)) iprop(False) β Φ ⊢ iprop(◇ ◇ False) :=
  (zO (L := exL)).trans (except0_mono ((sep_mono_right and_elim_l).trans (wand_elim_right.trans (zO (L := exL)))))

theorem acc_f {P : SiProp} :
    atomic_acc (TA := .nil) (TB := .nil) ∅ ∅ (fun _ => iprop(True)) P (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) ⊢ iprop(◇ ◇ False) :=
  (zO (L := exL)).trans (except0_mono ((sep_mono_right and_elim_r).trans (wand_elim_right.trans (zO (L := exL)))))

theorem au_true {Φ : Tele.nil.Arg → Tele.nil.Arg → SiProp} : iprop(True) ⊢
    atomic_update (TA := .nil) (TB := .nil) ∅ ∅ (fun _ => iprop(True)) (fun _ _ => iprop(False)) Φ :=
  (and_intro .rfl .rfl).trans (aupd_intro (P := iprop(True)) (Q := iprop(True)) (and_elim_l.trans acc_true))

theorem au_true2 : (iprop(True) : SiProp) ⊢
    atomic_update (TA := .nil) (TB := .nil) ∅ ∅ (fun _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) :=
  (and_intro .rfl .rfl).trans (aupd_intro (P := iprop(True)) (Q := iprop(True)) (and_elim_l.trans acc_true2))

end T1c0

open Iris Iris.BI Iris.Std T1c0
attribute [local instance] sF

-- `Iris.atomic_acc_ne` idx 16: necessary (SiProp with fupd zf exL (except0 at empty masks), nil telescopes, masks empty, n = 1, alpha1 = True, alpha2 = False, P = True, beta = Phi = False)
theorem t1c0_17 : ¬ drop0% Iris.atomic_acc_ne 16 := fun h =>
  sdist acc_true acc_a (@h SiProp _ sF .nil .nil ∅ ∅ 1 (fun _ => iprop(True)) (fun _ => iprop(False)) iprop(True) iprop(True)
    (fun _ _ => iprop(False)) (fun _ _ => iprop(False)) (fun _ _ => iprop(False)) (fun _ _ => iprop(False))
    (@OFE.Dist.rfl _ _ _ _) (fun _ _ => @OFE.Dist.rfl _ _ _ _) (fun _ _ => @OFE.Dist.rfl _ _ _ _))
-- `Iris.atomic_acc_ne` idx 17: necessary (SiProp with zf exL, nil telescopes, n = 1, alpha = True, P1 = True, P2 = False, beta = Phi = False)
theorem t1c0_18 : ¬ drop0% Iris.atomic_acc_ne 17 := fun h =>
  sdist acc_true acc_p (@h SiProp _ sF .nil .nil ∅ ∅ 1 (fun _ => iprop(True)) (fun _ => iprop(True)) iprop(True) iprop(False)
    (fun _ _ => iprop(False)) (fun _ _ => iprop(False)) (fun _ _ => iprop(False)) (fun _ _ => iprop(False))
    (fun _ => @OFE.Dist.rfl _ _ _ _) (fun _ _ => @OFE.Dist.rfl _ _ _ _) (fun _ _ => @OFE.Dist.rfl _ _ _ _))
-- `Iris.atomic_acc_ne` idx 18: necessary (SiProp with zf exL, nil telescopes, n = 1, alpha = P = True, beta1 = False, beta2 = True, Phi = False)
theorem t1c0_19 : ¬ drop0% Iris.atomic_acc_ne 18 := fun h =>
  sdist acc_true acc_f (@h SiProp _ sF .nil .nil ∅ ∅ 1 (fun _ => iprop(True)) (fun _ => iprop(True)) iprop(True) iprop(True)
    (fun _ _ => iprop(False)) (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) (fun _ _ => iprop(False))
    (fun _ => @OFE.Dist.rfl _ _ _ _) (@OFE.Dist.rfl _ _ _ _) (fun _ _ => @OFE.Dist.rfl _ _ _ _))
-- `Iris.atomic_acc_ne` idx 19: necessary (SiProp with zf exL, nil telescopes, n = 1, alpha = P = beta = True, Phi1 = True, Phi2 = False)
theorem t1c0_20 : ¬ drop0% Iris.atomic_acc_ne 19 := fun h =>
  sdist acc_true2 acc_f (@h SiProp _ sF .nil .nil ∅ ∅ 1 (fun _ => iprop(True)) (fun _ => iprop(True)) iprop(True) iprop(True)
    (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(False))
    (fun _ => @OFE.Dist.rfl _ _ _ _) (@OFE.Dist.rfl _ _ _ _) (fun _ _ => @OFE.Dist.rfl _ _ _ _))
-- `Iris.atomic_update_ne` idx 14: necessary (SiProp with zf exL, nil telescopes, n = 1, alpha1 = True, alpha2 = False, beta = Phi = False)
theorem t1c0_21 : ¬ drop0% Iris.atomic_update_ne 14 := fun h =>
  sdist au_true (aupd_aacc.trans acc_a) (@h SiProp _ sF .nil .nil ∅ ∅ 1 (fun _ => iprop(True)) (fun _ => iprop(False))
    (fun _ _ => iprop(False)) (fun _ _ => iprop(False)) (fun _ _ => iprop(False)) (fun _ _ => iprop(False))
    (fun _ _ => @OFE.Dist.rfl _ _ _ _) (fun _ _ => @OFE.Dist.rfl _ _ _ _))
-- `Iris.atomic_update_ne` idx 15: necessary (SiProp with zf exL, nil telescopes, n = 1, alpha = True, beta1 = False, beta2 = True, Phi = False)
theorem t1c0_22 : ¬ drop0% Iris.atomic_update_ne 15 := fun h =>
  sdist au_true (aupd_aacc.trans acc_f) (@h SiProp _ sF .nil .nil ∅ ∅ 1 (fun _ => iprop(True)) (fun _ => iprop(True))
    (fun _ _ => iprop(False)) (fun _ _ => iprop(True)) (fun _ _ => iprop(False)) (fun _ _ => iprop(False))
    (fun _ => @OFE.Dist.rfl _ _ _ _) (fun _ _ => @OFE.Dist.rfl _ _ _ _))
-- `Iris.atomic_update_ne` idx 16: necessary (SiProp with zf exL, nil telescopes, n = 1, alpha = beta = True, Phi1 = True, Phi2 = False)
theorem t1c0_23 : ¬ drop0% Iris.atomic_update_ne 16 := fun h =>
  sdist au_true2 (aupd_aacc.trans acc_f) (@h SiProp _ sF .nil .nil ∅ ∅ 1 (fun _ => iprop(True)) (fun _ => iprop(True))
    (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ _ => iprop(False))
    (fun _ => @OFE.Dist.rfl _ _ _ _) (fun _ _ => @OFE.Dist.rfl _ _ _ _))
-- `Iris.BI.MonPred.monPred_bi_fupd_sbi` idx 4: necessary (MonPred over Nat indices on SiProp with fupd zf cL (lawful, not BIFUpdateSbi): the MonPred fupd_siPure_later law at index 0 is the SiProp one, false at step 2)
theorem t1c0_24 : ¬ drop0% Iris.BI.MonPred.monPred_bi_fupd_sbi 4 := fun h =>
  s_bad <| s_lhs.trans <| (show (iprop(▷ zf cL ∅ ∅ iprop(<si_pure> False)) : SiProp) ⊢ zf cL ∅ ∅ iprop(▷ ◇ <si_pure> False) from
    Iris.BI.entails_at.mp (@BIFUpdateSbi.fupd_siPure_later _ _ _ _ (@h UIdx SiProp _ (zFupd cL)) ∅ iprop(False)) (0 : Nat)).trans
    (zO (L := cL))
