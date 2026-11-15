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
namespace T2c1
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

theorem zk_keep {PROP : Type _} [Sbi PROP] (E E' : CoPset) (Pi : SiProp) (R : PROP) :
    iprop(zf (exL (PROP := PROP)) E E' iprop(<si_pure> Pi) ∧ (<si_pure> Pi -∗ zf (exL (PROP := PROP)) E E R)) ⊢ zf (exL (PROP := PROP)) E E R :=
  imp_intro <| pure_elim_right fun e =>
    (and_mono ((pure_imp_elim e).trans (except0_mono and_elim_r)) (and_intro .rfl (except0_intro (P := iprop(<si_pure> Pi -∗ zf (exL (PROP := PROP)) E E R))))).trans <|
    (and_mono .rfl and_elim_r).trans <| except0_and.2.trans <| (except0_mono <|
      persistent_and_affinely_sep_left_mp.trans <| (sep_mono_left affinely_elim).trans <| (sep_mono_right .rfl).trans <| wand_elim_right.trans (pure_imp_elim e)).trans except0_idem.1

theorem zO {PROP : Type _} [BI PROP] {L : LM PROP} {X : PROP} : zf L ∅ ∅ X ⊢ L.M X :=
  (pure_imp_elim rfl).trans (L.mono and_elim_r)

theorem w2 {PROP : Type _} [BI PROP] {A B C : PROP} (h : ⊢ A -∗ B -∗ C) : iprop(A ∗ B) ⊢ C :=
  (sep_mono_left ((emp_sep.2).trans ((sep_mono_left h).trans wand_elim_left))).trans wand_elim_left

/-- NP: Nat under addition as a discrete UORA (unit 0, core 0, all valid, order ≤); UPred NP is affine and ownM 1 is not duplicable. -/
structure NP where v : Nat

instance : OFE NP := OFE.ofDiscrete NP
instance : OFE.Discrete NP := ⟨id⟩

instance npORA : ORA NP := ORA.ofDiscreteORAData {
  pcore := fun _ => some ⟨0⟩
  op := fun a b => ⟨a.v + b.v⟩
  Valid := fun _ => True
  Order := fun a b => a.v ≤ b.v
  assoc := by intro x y z; cases x; cases y; cases z; simp only [NP.mk.injEq]; omega
  comm := by intro x y; cases x; cases y; simp only [NP.mk.injEq]; omega
  pcore_op_left := by intro x cx h; cases h; cases x; simp
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ h1 h2 => Nat.le_trans h1 h2
  op_mono_left := by intro x y z h; show _ ≤ _; dsimp only; have : x.v ≤ y.v := h; omega
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨⟨0⟩, rfl, Nat.le_refl 0⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨⟨0⟩, rfl, Nat.le_refl 0⟩
  pcore_increasing := by intro x cx h y; cases h; show _ ≤ _; dsimp only; omega
  increasing_closed := by intro x y _ _ z; show _ ≤ _; dsimp only; omega }

instance : OrderRefl NP := ⟨fun x => Nat.le_refl x.v⟩

instance npUORA : UORA NP where
  unit := ⟨0⟩
  unit_valid := trivial
  unit_left_id := by intro x; cases x; simp [Op.op]
  pcore_unit := rfl

instance : IncOrd NP := ⟨by
  intro x y ⟨z, hz⟩
  have : y = ⟨x.v + z.v⟩ := hz
  subst this; exact Nat.le_add_right _ _⟩


/-- Credit modality on UPred NP: spend k of the owned credits to drop to step n - k
(or reach step 0). A lawful closure modality, not BIFUpdateSbi. -/
def crL (X : UPred NP) : UPred NP where
  holds n x := ∃ k, k ≤ x.val.v ∧ (n ≤ k ∨ X.holds (n - k) ⟨⟨x.val.v - k⟩, trivial⟩)
  mono := by
    rintro n1 n2 x1 x2 ⟨k, hk, h⟩ hle hn
    have hle' : x1.val.v ≤ x2.val.v := hle
    refine ⟨k, by omega, h.imp (fun h => by omega) (fun h => X.mono h ?_ (by omega))⟩
    show x1.val.v - k ≤ x2.val.v - k
    omega

def crLM : LM (UPred NP) where
  M := crL
  ne := ⟨fun {n P Q} h n' x hn' p => by
    constructor
    · rintro ⟨k, hk, h1⟩
      exact ⟨k, hk, h1.imp id (fun h2 => (h (n' - k) _ (by omega) trivial).1 h2)⟩
    · rintro ⟨k, hk, h1⟩
      exact ⟨k, hk, h1.imp id (fun h2 => (h (n' - k) _ (by omega) trivial).2 h2)⟩⟩
  mono h := fun n x ⟨k, hk, h1⟩ => ⟨k, hk, h1.imp id (h _ _)⟩
  intro {P} := fun n x hp => ⟨0, Nat.zero_le _, .inr (P.mono hp (show x.val.v ≤ x.val.v - 0 by omega) (by omega))⟩
  join {P} := fun n x ⟨k1, hk1, h1⟩ => by
    rcases h1 with h1 | ⟨k2, hk2, h2⟩
    · exact ⟨k1, hk1, .inl h1⟩
    · have hk2' : k2 ≤ x.val.v - k1 := hk2
      refine ⟨k1 + k2, by omega, h2.imp (fun h => by omega) (fun h => P.mono h ?_ (by omega))⟩
      show x.val.v - k1 - k2 ≤ x.val.v - (k1 + k2)
      omega
  frame {P R} := fun n x ⟨x1, x2, H, ⟨k, hk, h1⟩, hR⟩ => by
    have H' : x1.v + x2.v ≤ x.val.v := H
    have hk' : k ≤ x1.v := hk
    refine ⟨k, by omega, h1.imp id (fun hP => ⟨⟨x1.v - k⟩, x2, ?_, hP, R.mono hR (show x2.v ≤ x2.v from Nat.le_refl _) (by omega)⟩)⟩
    show x1.v - k + x2.v ≤ x.val.v - k
    omega
  ex0 {P} := fun n x h => by
    rcases h with hl | hr
    · cases n with
      | zero => exact ⟨0, Nat.zero_le _, .inl (Nat.le_refl 0)⟩
      | succ m => exact hl.elim
    · exact hr

theorem cr_key (P : UPred NP) : iprop(UPred.ownM (⟨1⟩ : NP) ∗ ▷ P) ⊢ crL P :=
  fun n x ⟨x1, x2, H, hl, hp⟩ => by
    have H' : x1.v + x2.v ≤ x.val.v := H
    have hl' : 1 ≤ x1.v := hl
    cases n with
    | zero => exact ⟨1, by omega, .inl (Nat.zero_le _)⟩
    | succ m => exact ⟨1, by omega, .inr (P.mono hp (show x2.v ≤ x.val.v - 1 by omega) (by omega))⟩

theorem cr_elim (E : CoPset) (P : UPred NP) :
    iprop(UPred.ownM (⟨1⟩ : NP) ∗ ▷ P) ⊢ zf crLM E E P :=
  imp_intro <| pure_elim_right fun e => (cr_key P).trans (crLM.mono (and_intro (pure_intro e) .rfl))

theorem lnF {PROP : Type _} [Sbi PROP] : (iprop(True) : PROP) ⊢ iprop(∃ n, ▷^[n] (False : PROP)) :=
  loeb_weak (later_exists_false.trans (or_elim (exists_intro (Ψ := fun n => iprop(▷^[n] (False : PROP))) 1)
    (exists_elim fun n => exists_intro (Ψ := fun n => iprop(▷^[n] (False : PROP))) (n + 1))))

theorem lcF {PROP : Type _} [Sbi PROP] [BIFUpdate PROP] {lc : PROP}
    (helim : ∀ (E : CoPset) (P : PROP), lc ∗ ▷ P ⊢ |={E}=> P)
    (hkeep : ∀ {E : CoPset} (E' : CoPset) (Pi : Iris.SiProp) (R : PROP),
        (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R) (E : CoPset) :
    ∀ n, iprop(lc ∗ ▷^[n] (False : PROP)) ⊢ |={E}=> (False : PROP)
  | 0 => (sep_mono_right (false_elim (P := iprop(lc -∗ |={E}=> (False : PROP))))).trans wand_elim_right
  | n + 1 => by
    have k : iprop(lc ∗ ▷ ▷^[n] (False : PROP)) ⊢ |={E}=> iprop(lc ∗ ▷^[n] (False : PROP)) := by
      iintro ⟨Hlc, HX⟩
      iapply (Iris.LaterCreditsPlain.lc_fupd_elim_later_keep helim hkeep (E := E) (P := iprop(▷^[n] (False : PROP)))) $$ Hlc HX
    exact k.trans ((BIFUpdate.mono (lcF helim hkeep E n)).trans BIFUpdate.trans)

theorem lcF' {PROP : Type _} [Sbi PROP] [BIFUpdate PROP] {lc : PROP}
    (helim : ∀ (E : CoPset) (P : PROP), lc ∗ ▷ P ⊢ |={E}=> P)
    (hkeep : ∀ {E : CoPset} (E' : CoPset) (Pi : Iris.SiProp) (R : PROP),
        (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R) (E : CoPset) :
    lc ⊢ |={E}=> (False : PROP) :=
  (sep_emp.2.trans (sep_mono_right (true_intro.trans lnF))).trans
    (sep_exists_left.1.trans (exists_elim fun n => lcF helim hkeep E n))

theorem keepG {PROP : Type _} [Sbi PROP] [BIFUpdate PROP] {lc : PROP}
    (helim : ∀ (E : CoPset) (P : PROP), lc ∗ ▷ P ⊢ |={E}=> P)
    (hkeep : ∀ {E : CoPset} (E' : CoPset) (Pi : Iris.SiProp) (R : PROP),
        (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R) {E : CoPset} {P : PROP} :
    ⊢ lc -∗ ▷ P ={E}=∗ lc ∗ P := by
  exact wand_intro (emp_sep.1.trans (wand_intro ((sep_mono_left (lcF' helim hkeep E)).trans
    (BIFUpdate.frame_right.trans (BIFUpdate.mono
      ((sep_mono_left (false_elim (P := iprop(▷ P -∗ lc ∗ P)))).trans wand_elim_left))))))
inductive T2 where | e | o | bot
  deriving DecidableEq

def T2.op : T2 → T2 → T2
  | .e, x => x
  | x, .e => x
  | _, _ => .bot

theorem T2.op_assoc (a b c : T2) : a.op (b.op c) = (a.op b).op c := by
  cases a <;> cases b <;> cases c <;> rfl
theorem T2.op_comm (a b : T2) : a.op b = b.op a := by cases a <;> cases b <;> rfl
theorem T2.op_bot (a b : T2) (h : a.op b ≠ .bot) : a ≠ .bot := by
  cases a <;> cases b <;> simp_all [T2.op]
theorem T2.e_op (a : T2) : T2.e.op a = a := rfl
theorem T2.op_e (a : T2) : a.op .e = a := by cases a <;> rfl

/-- MC: mask tokens (Pos → T2, o = owned) and later credits (Nat). -/
structure MC where
  g : Pos → T2
  c : Nat

def MC.op (x y : MC) : MC := ⟨fun p => (x.g p).op (y.g p), x.c + y.c⟩
def MC.Valid (x : MC) : Prop := ∀ p, x.g p ≠ .bot
def MC.Le (x y : MC) : Prop := (∃ zg : Pos → T2, ∀ p, y.g p = (x.g p).op (zg p)) ∧ x.c ≤ y.c
def mcUnit : MC := ⟨fun _ => .e, 0⟩

instance : OFE MC := OFE.ofDiscrete MC
instance : OFE.Discrete MC := ⟨id⟩

theorem MC.op_assoc (x y z : MC) : x.op (y.op z) = (x.op y).op z := by
  simp only [MC.op, T2.op_assoc, Nat.add_assoc]
theorem MC.op_comm (x y : MC) : x.op y = y.op x := by
  simp only [MC.op]; congr 1
  · funext p; exact T2.op_comm _ _
  · exact Nat.add_comm _ _
theorem MC.le_refl (x : MC) : x.Le x := ⟨⟨fun _ => T2.e, fun p => (T2.op_e _).symm⟩, Nat.le_refl _⟩
theorem MC.le_op (x z : MC) : z.Le (x.op z) :=
  ⟨⟨x.g, fun p => T2.op_comm _ _⟩, by simp only [MC.op]; omega⟩
theorem MC.unit_op (x : MC) : mcUnit.op x = x := by cases x; simp only [MC.op, mcUnit, T2.e_op, Nat.zero_add]

instance mcORA : ORA MC := ORA.ofDiscreteORAData {
  pcore := fun _ => some mcUnit
  op := MC.op
  Valid := MC.Valid
  Order := MC.Le
  assoc := MC.op_assoc
  comm := MC.op_comm
  pcore_op_left := by intro x cx h; cases h; exact MC.unit_op x
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun x y h p => T2.op_bot _ _ (h p)
  ord_trans := by
    rintro x y z ⟨⟨a, ha⟩, h1⟩ ⟨⟨b, hb⟩, h2⟩
    exact ⟨⟨fun p => (a p).op (b p), fun p => by rw [hb, ha, T2.op_assoc]⟩, Nat.le_trans h1 h2⟩
  op_mono_left := by
    rintro x y z ⟨⟨a, ha⟩, h1⟩
    refine ⟨⟨a, fun p => ?_⟩, ?_⟩
    · show ((y.g p).op (z.g p)) = ((x.g p).op (z.g p)).op (a p)
      rw [ha, ← T2.op_assoc, T2.op_comm (a p), T2.op_assoc]
    · show x.c + z.c ≤ y.c + z.c
      omega
  valid_of_ord := by
    rintro x y ⟨⟨a, ha⟩, _⟩ hv p
    exact T2.op_bot _ _ (by rw [← ha]; exact hv p)
  pcore_mono := by intro x y cx _ h; cases h; exact ⟨_, rfl, MC.le_refl _⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨_, rfl, MC.le_refl _⟩
  pcore_increasing := by intro x cx h y; cases h; exact MC.le_op _ _
  increasing_closed := by intro x y _ _ z; exact MC.le_op _ _ }

instance : OrderRefl MC := ⟨MC.le_refl⟩

instance mcUORA : UORA MC where
  unit := mcUnit
  unit_valid := fun _ h => T2.noConfusion h
  unit_left_id := MC.unit_op _
  pcore_unit := rfl

instance : IncOrd MC := ⟨by rintro x y ⟨z, hz⟩; have hz' : y = x.op z := hz; subst hz'; exact ⟨⟨z.g, fun _ => rfl⟩, Nat.le_add_right _ _⟩⟩


open Classical in
noncomputable def tokE (E : CoPset) : MC := ⟨fun p => if p ∈ E then .o else .e, 0⟩
def cr (k : Nat) : MC := ⟨fun _ => .e, k⟩
noncomputable abbrev ownE (E : CoPset) : UPred MC := UPred.ownM (tokE E)

theorem tokE_union {E1 E2 : CoPset} (h : E1 ## E2) : tokE (E1 ∪ E2) = (tokE E1).op (tokE E2) := by
  simp only [tokE, MC.op]; congr 1; funext p
  have hu := (LawfulSet.mem_union (X := E1) (Y := E2) (x := p))
  have hd := h p
  by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [T2.op]

theorem tokE_diff {E1 E2 : CoPset} (h : E2 ⊆ E1) : tokE E1 = (tokE E2).op (tokE (E1 \ E2)) := by
  simp only [tokE, MC.op]; congr 1; funext p
  have hu := (LawfulSet.mem_diff (X := E1) (Y := E2) (x := p))
  have hs := h p
  by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [T2.op]

theorem ownM_disj (E1 E2 : CoPset) : UPred.ownM ((tokE E1).op (tokE E2)) ⊢ iprop(⌜E1 ## E2⌝) :=
  fun n x h p ⟨h1, h2⟩ => by
    have hv : MC.Valid ((tokE E1).op (tokE E2)) := ORA.validN_of_ordN h x.property
    have := hv p
    simp [MC.op, tokE, h1, h2, T2.op] at this

theorem ownE_join (E1 E2 : CoPset) : iprop(ownE E1 ∗ ownE E2) ⊢ iprop(⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2)) :=
  (UPred.ownM_op _ _).2.trans <| (and_intro (ownM_disj E1 E2) .rfl).trans <| pure_elim_left fun hd =>
    and_intro (pure_intro hd) (by show _ ⊢ UPred.ownM (tokE (E1 ∪ E2)); rw [tokE_union hd])

theorem ownE_split {E1 E2 : CoPset} (hd : E1 ## E2) : ownE (E1 ∪ E2) ⊢ iprop(ownE E1 ∗ ownE E2) := by
  show UPred.ownM (tokE (E1 ∪ E2)) ⊢ _; rw [tokE_union hd]; exact (UPred.ownM_op _ _).1

theorem ownE_sub {E1 E2 : CoPset} (h : E2 ⊆ E1) : ownE E1 ⊣⊢ iprop(ownE E2 ∗ ownE (E1 \ E2)) := by
  show UPred.ownM (tokE E1) ⊣⊢ _; rw [tokE_diff h]; exact UPred.ownM_op _ _


/-- Fancy update from mask ownership: own E1, get L (own E2 ∗ P). -/
noncomputable def wf (L : LM (UPred MC)) (E1 E2 : CoPset) (P : UPred MC) : UPred MC :=
  iprop(ownE E1 -∗ L.M iprop(ownE E2 ∗ P))

theorem pa {φ : Prop} {X Y Z : UPred MC} (h : φ → iprop(X ∗ Y) ⊢ Z) : iprop((⌜φ⌝ ∧ X) ∗ Y) ⊢ Z :=
  (sep_mono_left (pure_elim_left fun hφ => wand_intro (h hφ))).trans wand_elim_left

theorem rcomm {A B C : UPred MC} : iprop((A ∗ B) ∗ C) ⊢ iprop((A ∗ C) ∗ B) :=
  sep_assoc.1.trans ((sep_mono_right sep_comm.1).trans sep_assoc.2)

noncomputable def wFupd (L : LM (UPred MC)) : BIFUpdate (UPred MC) where
  fupd := wf L
  ne := ⟨fun _ _ _ h => wand_ne.ne .rfl (L.ne.ne (sep_ne.ne .rfl h))⟩
  subset {E1 E2} h := wand_intro <| emp_sep.1.trans <| (ownE_sub h).1.trans <|
    (sep_mono_right (wand_intro ((sep_comm.1.trans (ownE_sub h).2).trans (sep_emp.2.trans L.intro)))).trans L.intro
  except0 := wand_intro <| (sep_mono_right except0_intro).trans
    (except0_sep.2.trans ((except0_mono wand_elim_left).trans L.ex0))
  mono h := wand_intro (wand_elim_left.trans (L.mono (sep_mono_right h)))
  trans := wand_intro (wand_elim_left.trans ((L.mono wand_elim_right).trans L.join))
  mask_frame_right_strong {E1 E2 Ef P} hd := wand_intro <| (sep_mono_right (ownE_split hd)).trans <|
    sep_assoc.2.trans <| (sep_mono_left wand_elim_left).trans <| L.frame.trans <| L.mono <|
      rcomm.trans ((sep_mono_left (ownE_join E2 Ef)).trans (pa fun hd2 => sep_mono_right (pure_imp_elim hd2)))
  frame_right := wand_intro <| rcomm.trans <| (sep_mono_left wand_elim_left).trans <|
    L.frame.trans (L.mono sep_assoc.1)

theorem wk_keep (E E' : CoPset) (Pi : SiProp) (R : UPred MC) :
    iprop(wf exL E E' iprop(<si_pure> Pi) ∧ (<si_pure> Pi -∗ wf exL E E R)) ⊢ wf exL E E R :=
  wand_intro <| (and_intro (sep_mono_left and_elim_l) (sep_mono_left and_elim_r)).trans <|
    (and_mono (wand_elim_left.trans (except0_mono sep_elim_right)) except0_intro).trans <|
    except0_and.2.trans <| (except0_mono <| persistent_and_affinely_sep_left_mp.trans <|
      (sep_mono_left affinely_elim).trans <| sep_assoc.2.trans <|
      (sep_mono_left wand_elim_right).trans wand_elim_left).trans except0_idem.1

open Classical in
theorem tokE_valid (E : CoPset) : MC.Valid ((UORA.unit : MC).op (tokE E)) := fun p => by
  show T2.e.op (if p ∈ E then T2.o else T2.e) ≠ T2.bot
  split <;> exact fun h => T2.noConfusion h

theorem unit_le (x : MC) : MC.Le (UORA.unit : MC) x := ⟨⟨x.g, fun _ => rfl⟩, Nat.zero_le _⟩

theorem wsound (E : CoPset) (P : UPred MC) [Plain P] (h : (iprop(emp) : UPred MC) ⊢ wf exL E E P) :
    (iprop(emp) : UPred MC) ⊢ P := fun n x _ => by
  have h1 := h (n + 1) ⟨UORA.unit, fun _ h => T2.noConfusion h⟩ (MC.le_refl _)
  have h2 := h1 (n + 1) (tokE E) (Nat.le_refl _) (tokE_valid E) (MC.le_refl _)
  rcases h2 with h2 | ⟨y1, y2, _, _, hp⟩
  · exact h2.elim
  · have hp' := (Plain.plain (P := P)) (n + 1) _ hp
    exact P.mono hp' (unit_le x.val) (Nat.le_succ n)


/-- Credit modality on UPred MC: spend k credits to drop k steps (masks untouched). -/
def crM (X : UPred MC) : UPred MC where
  holds n x := ∃ k, k ≤ x.val.c ∧ (n ≤ k ∨ X.holds (n - k) ⟨⟨x.val.g, x.val.c - k⟩, x.property⟩)
  mono := by
    rintro n1 n2 x1 x2 ⟨k, hk, h⟩ hle hn
    obtain ⟨hg, hc⟩ := (hle : MC.Le x1.val x2.val)
    refine ⟨k, by omega, ?_⟩
    rcases h with h | h
    · exact .inl (by omega)
    · refine .inr (X.mono h ?_ (by omega))
      exact ⟨hg, show x1.val.c - k ≤ x2.val.c - k by omega⟩


def crMLM : LM (UPred MC) where
  M := crM
  ne := ⟨fun {n P Q} h n' x hn' p => by
    constructor
    · rintro ⟨k, hk, h1⟩
      exact ⟨k, hk, h1.imp id (fun h2 => (h (n' - k) _ (by omega) _).1 h2)⟩
    · rintro ⟨k, hk, h1⟩
      exact ⟨k, hk, h1.imp id (fun h2 => (h (n' - k) _ (by omega) _).2 h2)⟩⟩
  mono h := fun n x ⟨k, hk, h1⟩ => ⟨k, hk, h1.imp id (h _ _)⟩
  intro {P} := fun n x hp => by
    refine ⟨0, Nat.zero_le _, .inr (P.mono hp ?_ (by omega))⟩
    exact ⟨⟨fun _ => T2.e, fun p => (T2.op_e _).symm⟩, show x.val.c ≤ x.val.c - 0 by omega⟩
  join {P} := fun n x ⟨k1, hk1, h1⟩ => by
    rcases h1 with h1 | ⟨k2, hk2, h2⟩
    · exact ⟨k1, hk1, .inl h1⟩
    · have hk2' : k2 ≤ x.val.c - k1 := hk2
      refine ⟨k1 + k2, by omega, ?_⟩
      rcases h2 with h | h
      · exact .inl (by omega)
      · refine .inr (P.mono h ?_ (by omega))
        exact ⟨⟨fun _ => T2.e, fun p => (T2.op_e _).symm⟩, show x.val.c - k1 - k2 ≤ x.val.c - (k1 + k2) by omega⟩
  frame {P R} := fun n x ⟨x1, x2, ⟨hg, hc⟩, ⟨k, hk, h1⟩, hR⟩ => by
    have hc' : x1.c + x2.c ≤ x.val.c := hc
    have hk' : k ≤ x1.c := hk
    refine ⟨k, by omega, h1.imp id (fun hP => ⟨⟨x1.g, x1.c - k⟩, x2, ⟨hg, ?_⟩, hP,
      R.mono hR (MC.le_refl x2) (by omega)⟩)⟩
    show x1.c - k + x2.c ≤ x.val.c - k
    omega
  ex0 {P} := fun n x h => by
    rcases h with hl | hr
    · cases n with
      | zero => exact ⟨0, Nat.zero_le _, .inl (Nat.le_refl 0)⟩
      | succ m => exact hl.elim
    · exact hr

theorem cm_key (P : UPred MC) : iprop(UPred.ownM (cr 1) ∗ ▷ P) ⊢ crM P :=
  fun n x ⟨x1, x2, ⟨⟨zg, hg⟩, hc⟩, ⟨_, hl⟩, hp⟩ => by
    have hc' : x1.c + x2.c ≤ x.val.c := hc
    have hl' : 1 ≤ x1.c := hl
    cases n with
    | zero => exact ⟨1, by omega, .inl (Nat.zero_le _)⟩
    | succ m =>
      refine ⟨1, by omega, .inr (P.mono hp ⟨⟨fun p => (x1.g p).op (zg p), fun p => ?_⟩, ?_⟩ (by omega))⟩
      · show x.val.g p = (x2.g p).op ((x1.g p).op (zg p))
        rw [hg p]; show ((x1.g p).op (x2.g p)).op (zg p) = _
        rw [T2.op_comm (x1.g p), ← T2.op_assoc]
      · show x2.c ≤ x.val.c - 1
        omega

theorem cm_elim (E : CoPset) (P : UPred MC) : iprop(UPred.ownM (cr 1) ∗ ▷ P) ⊢ wf crMLM E E P :=
  wand_intro <| sep_assoc.1.trans <| (sep_mono_right ((sep_mono_right later_intro).trans later_sep.2)).trans <|
    (cm_key _).trans (crMLM.mono sep_comm.1)

open Classical in
theorem crE_valid (E : CoPset) : MC.Valid ((cr 1).op (tokE E)) := fun p => by
  show T2.e.op (if p ∈ E then T2.o else T2.e) ≠ T2.bot
  split <;> exact fun h => T2.noConfusion h

theorem csound (E : CoPset) (P : UPred MC) [Plain P] (h : UPred.ownM (cr 1) ⊢ wf crMLM E E P) :
    (iprop(emp) : UPred MC) ⊢ P := fun n x _ => by
  have h1 := h (n + 2) ⟨cr 1, fun _ h => T2.noConfusion h⟩ (MC.le_refl _)
  obtain ⟨k, hk, h3⟩ := h1 (n + 2) (tokE E) (Nat.le_refl _) (crE_valid E) (MC.le_refl _)
  have hk' : k ≤ 1 + 0 := hk
  rcases h3 with h3 | ⟨y1, y2, _, _, hp⟩
  · omega
  · have hp' := (Plain.plain (P := P)) _ _ hp
    exact P.mono hp' (unit_le x.val) (by omega)

theorem np_pers1 : iprop(<pers> UPred.ownM (⟨1⟩ : NP)) ⊢ iprop(False) := fun _ _ h =>
  (Nat.not_succ_le_zero 0 (h : (1 : Nat) ≤ 0)).elim

/-- Mask-independent fupd adding ownership of one credit. -/
def tF (_ : Iris.Inv.Mask) (X : UPred NP) : UPred NP := iprop(X ∨ UPred.ownM (⟨1⟩ : NP))

theorem tF_pers (E : Iris.Inv.Mask) : iprop(□ tF E iprop(False)) ⊢ iprop(False) :=
  affinely_elim.trans <| (persistently_mono (or_elim false_elim .rfl)).trans np_pers1

end T2c1


open Iris Iris.BI

-- `Iris.LaterCreditsPlain.lc_fupd_elim_later_keep` idx 8: removable (lc_fupd_elim_later and fupd_keep_si_pure' give lc ⊢ fupd False via Löb (Sbi is later-contractive) and the library lemma for the plain P = later^n False, so the conclusion holds for every P)
theorem t2c1_1 : drop% Iris.LaterCreditsPlain.lc_fupd_elim_later_keep 8 := by
  intro PROP _ _ lc helim hkeep E P _
  exact T2c1.keepG helim hkeep

-- `Iris.LaterCreditsPlain.lc_fupd_elim_later_keep` idx 9: removable (same derivation: lc ⊢ fupd False from the two hypotheses, then frame)
theorem t2c1_2 : drop% Iris.LaterCreditsPlain.lc_fupd_elim_later_keep 9 := by
  intro PROP _ _ lc helim hkeep E P _
  exact T2c1.keepG helim hkeep

-- `Iris.LaterCreditsPlain.lc_fupd_elim_later_keep` idx 4: necessary (SiProp with fupd zf exL (except0 at empty masks, keeps si_pure), lc = True, E = empty, P = later False: later later False does not give except0 later False at step 1)
theorem t2c1_3 : ¬ drop0% Iris.LaterCreditsPlain.lc_fupd_elim_later_keep 4 := fun h => by
  have k := T2c1.w2 (@h SiProp _ (T2c1.zFupd T2c1.exL) iprop(True)
    (fun E' Pi R => T2c1.zk_keep _ E' Pi R) ∅ iprop(▷ False) _ _)
  have k2 := ((emp_sep.2.trans (sep_mono_left true_intro)).trans k).trans T2c1.zO
  rcases k2 1 trivial with h | ⟨_, h⟩ <;> exact h

-- `Iris.LaterCreditsPlain.lc_fupd_elim_later_keep` idx 5: necessary (UPred NP (credits = Nat under +) with fupd zf crL (spending k credits drops k steps), lc = ownM 1, E = empty, P = later later False: fails at step 2 with one credit)
theorem t2c1_4 : ¬ drop0% Iris.LaterCreditsPlain.lc_fupd_elim_later_keep 5 := fun h => by
  have k := (T2c1.w2 (@h (UPred T2c1.NP) _ (T2c1.zFupd T2c1.crLM) (UPred.ownM (⟨1⟩ : T2c1.NP))
    T2c1.cr_elim ∅ iprop(▷ ▷ False) _ _)).trans T2c1.zO
  obtain ⟨k0, hk, h1⟩ := k 2 ⟨⟨1⟩, trivial⟩ ⟨⟨1⟩, ⟨0⟩, (show 1 + 0 ≤ 1 by omega), (show 1 ≤ 1 by omega), trivial⟩
  have hk' : k0 ≤ 1 := hk
  rcases h1 with h1 | ⟨y1, y2, H, hl, hp⟩
  · omega
  · have H' : y1.v + y2.v ≤ 1 - k0 := H
    have hl' : 1 ≤ y1.v := hl
    have : k0 = 0 := by omega
    subst this
    exact hp

-- `Iris.LaterCreditsPlain.contradiction` idx 5: necessary (UPred MC (mask tokens Pos → {e,o,bot} plus credits) with fupd E1 E2 P := ownE E1 -∗ ◇ (ownE E2 ∗ P) (lawful, keeps si_pure), lc = emp: lc_soundness by instantiating the wand with the token for E; consistent, so the conclusion False fails)
theorem t2c1_5 : ¬ drop0% Iris.LaterCreditsPlain.contradiction 5 := fun h =>
  @h (UPred T2c1.MC) _ _ (T2c1.wFupd T2c1.exL) iprop(emp) (fun P _ E hP => T2c1.wsound E P hP)
    (fun E' Pi R => T2c1.wk_keep _ E' Pi R) _

-- `Iris.LaterCreditsPlain.contradiction` idx 7: necessary (UPred MC with fupd E1 E2 P := ownE E1 -∗ crM (ownE E2 ∗ P), crM spends k credits to drop k steps; lc = ownM (one credit) strips a later; lc_soundness by evaluating at step n+2 with one credit and the token for E)
theorem t2c1_6 : ¬ drop0% Iris.LaterCreditsPlain.contradiction 7 := fun h =>
  @h (UPred T2c1.MC) _ _ (T2c1.wFupd T2c1.crMLM) (UPred.ownM (T2c1.cr 1)) (fun E P => T2c1.cm_elim E P)
    (fun P _ E hP => T2c1.csound E P hP) _

-- `Iris.Inv.finished_contradiction` idx 6: necessary (UPred NP, non-persistent invariants inv i P = ownM 1 (one credit), fupd E X = X ∨ ownM 1, start = False, finished = True: B = □(False ∨ ownM 1) fails at the credit since its core is 0)
theorem t2c1_7 : ¬ drop0% Iris.Inv.finished_contradiction 6 := fun h => by
  have k := @h (UPred T2c1.NP) _ _ T2c1.tF Unit (fun _ _ => UPred.ownM (⟨1⟩ : T2c1.NP))
    (fun {_ _} => or_intro_l) (fun {_ _} => or_elim .rfl or_intro_r)
    (fun _ _ _ _ => sep_elim_left.trans or_intro_r) Unit (fun _ => iprop(False)) (fun _ => iprop(True)) _
    (fun _ => sep_elim_left) () ()
  have k2 := ((emp_sep.2.trans (sep_mono_left true_intro)).trans k).trans (T2c1.tF_pers .M1)
  exact k2 0 ⟨⟨1⟩, trivial⟩ (show (1 : Nat) ≤ 1 from Nat.le_refl 1)

-- `Iris.Inv.contradiction'` idx 2: removable (the paradox goes through without affinity: use B = <pers> (fupd M1 False) instead of □, absorb leftovers into it, and <pers> X ⊢ X ∗ <pers> X)
theorem t2c1_8 : drop% Iris.Inv.contradiction' 2 := by
  intro PROP _ fupd name inv _ hi hm hff hfr hmm ha hinv hc gname start fin _ hs hsf hns
  let F : PROP := fupd .M1 iprop(False)
  have fr : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, iprop(fupd E P ∗ Q) ⊢ fupd E iprop(P ∗ Q) :=
    sep_comm.1.trans (hfr.trans (hm sep_comm.1))
  have fsep : ∀ {X : PROP}, iprop(False ∗ X) ⊢ (iprop(False) : PROP) :=
    (sep_mono_left false_elim).trans wand_elim_left
  have BF : iprop(<pers> F) ⊢ F :=
    ((and_intro .rfl .rfl).trans persistently_and_l).trans (fr.trans (hm fsep))
  have BB : iprop(<pers> F) ⊢ iprop(<pers> F ∗ <pers> F) := persistent_sep_dup_mp
  have L1 : ∀ γ i, iprop(fin γ ∗ inv i iprop(start γ ∨ <pers> F)) ⊢ F := fun γ i =>
    sep_comm.1.trans ((hinv (i := i) _ (fin γ) iprop(<pers> F) (sep_or_right.1.trans (or_elim
      ((hns γ).trans false_elim)
      ((persistently_absorb_l.trans (BB.trans (sep_mono_left or_intro_r))).trans hi)))).trans
      ((hm BF).trans hff))
  have L2 : ∀ γ i, iprop(fin γ ∗ inv i iprop(start γ ∨ <pers> F)) ⊢ iprop(<pers> F) := fun γ i =>
    persistently_intro.trans (persistently_mono (L1 γ i))
  have L3 : ∀ γ i, inv i iprop(start γ ∨ <pers> F) ⊢ fupd .M1 iprop(<pers> F) := fun γ i =>
    persistent_sep_dup_mp.trans (hinv _ _ iprop(<pers> F) (sep_or_right.1.trans (or_elim
      ((sep_mono_left (hsf γ)).trans (fr.trans (hm ((L2 γ i).trans (BB.trans (sep_mono_left or_intro_r))))))
      ((persistently_absorb_l.trans (BB.trans (sep_mono_left or_intro_r))).trans hi))))
  have G : ∀ γ, start γ ⊢ F := fun γ =>
    or_intro_l.trans ((ha _).trans ((hm (exists_elim fun i => L3 γ i)).trans (hff.trans ((hm BF).trans hff))))
  exact hc (hs.trans (hmm.trans ((hm (exists_elim G)).trans hff)))

-- `Iris.Inv.contradiction` idx 2: removable (non-affine derivation: saved props with body start ∨ finished ∗ <pers> P and A = ∃ P, <pers> (P -∗ fupd M1 False) ∗ saved P; leftovers (a finished token, persistent copies) are carried and finally absorbed by False)
theorem t2c1_9 : drop% Iris.Inv.contradiction 2 := by
  intro PROP _ fupd name inv _ hi hm hff hfr hmm ha hinv hc gname start fin hs hsf hns hdup
  let F : PROP := fupd .M1 iprop(False)
  let body : gname → PROP → PROP := fun γ P => iprop(start γ ∨ fin γ ∗ <pers> P)
  let sv : gname → PROP → PROP := fun γ P => iprop(∃ i, inv i (body γ P))
  let A : gname → PROP := fun γ => iprop(∃ P, <pers> (P -∗ F) ∗ sv γ P)
  have fr : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, iprop(fupd E P ∗ Q) ⊢ fupd E iprop(P ∗ Q) :=
    sep_comm.1.trans (hfr.trans (hm sep_comm.1))
  have fsep : ∀ {X : PROP}, iprop(False ∗ X) ⊢ (iprop(False) : PROP) :=
    (sep_mono_left false_elim).trans wand_elim_left
  have FJ : ∀ {X : PROP}, fupd .M1 iprop(F ∗ X) ⊢ F := (hm fr).trans (hff.trans (hm fsep))
  have psplit : ∀ {X : PROP}, iprop(<pers> X) ⊢ iprop(X ∗ <pers> X) :=
    (and_intro .rfl .rfl).trans persistently_and_l
  -- opening the Q-invariant while holding fin
  have inner : ∀ γ Q j, iprop(inv j (body γ Q) ∗ fin γ) ⊢ fupd .M1 iprop(<pers> Q ∗ fin γ) := fun γ Q j =>
    hinv _ _ _ (sep_or_right.1.trans (or_elim ((hns γ).trans false_elim) (by
      refine Entails.trans ?_ hi
      iintro ⟨⟨Hf, HQ⟩, Hf2⟩
      icases (persistent_sep_dup_mp (P := iprop(<pers> Q))) $$ HQ with ⟨HQ, HQ'⟩
      isplitl [Hf HQ]
      · iright; isplitl [Hf]
        · iexact Hf
        · iexact HQ
      · isplitl [HQ']
        · iexact HQ'
        · iexact Hf2)))
  have W : ∀ γ P, iprop(body γ P ∗ <pers> P) ⊢ fupd .M0 iprop(fin γ ∗ <pers> P) := fun γ P =>
    sep_or_right.1.trans (or_elim ((sep_mono_left (hsf γ)).trans fr)
      ((sep_assoc.1.trans (sep_mono_right persistently_absorb_l)).trans hi))
  have outer : ∀ γ P Q i, iprop(inv i (body γ P) ∗ (sv γ Q ∗ <pers> P)) ⊢ fupd .M1 iprop(<pers> Q ∗ fin γ) :=
    fun γ P Q i => (hinv _ _ (fupd .M1 iprop(<pers> Q ∗ fin γ)) (by
      refine ((sep_mono_right sep_comm.1).trans sep_assoc.2).trans ?_
      refine (sep_mono_left (W γ P)).trans (fr.trans (hm ?_))
      refine (sep_mono_left (sep_mono_left (hdup γ))).trans ?_
      refine Entails.trans ?_ (sep_mono (or_intro_r (P := start γ)) (sep_exists_right.1.trans (exists_elim fun j => inner γ Q j)))
      iintro ⟨⟨⟨H1, H2⟩, H3⟩, H4⟩
      isplitl [H1 H3]
      · isplitl [H1]
        · iexact H1
        · iexact H3
      · isplitl [H4]
        · iexact H4
        · iexact H2)).trans hff
  have cast : ∀ γ P Q, iprop(sv γ P ∗ (sv γ Q ∗ <pers> P)) ⊢ fupd .M1 iprop(<pers> Q ∗ fin γ) := fun γ P Q =>
    sep_exists_right.1.trans (exists_elim fun i => outer γ P Q i)
  have pA : ∀ γ, A γ ⊢ iprop(<pers> A γ ∗ A γ) := fun γ =>
    persistent_sep_dup_mp.trans (sep_mono_left persistently_intro)
  have NA : ∀ γ, iprop(sv γ (A γ) ∗ A γ) ⊢ F := fun γ => by
    refine (sep_mono_right ((pA γ).trans sep_exists_left.1)).trans (sep_exists_left.1.trans (exists_elim fun P' => ?_))
    refine Entails.trans ?_ (FJ (X := iprop((<pers> P' ∗ fin γ) ∗ <pers> (P' -∗ F))))
    refine Entails.trans ?_ (hm (P := iprop((<pers> P' ∗ fin γ) ∗ <pers> (P' -∗ F)))
      (Q := iprop(F ∗ ((<pers> P' ∗ fin γ) ∗ <pers> (P' -∗ F)))) ?_)
    · refine Entails.trans ?_ fr
      refine Entails.trans ?_ (sep_mono_left (cast γ (A γ) P'))
      iintro ⟨Hs, HA, HN, HsP⟩
      isplitl [Hs HsP HA]
      · isplitl [Hs]
        · iexact Hs
        · isplitl [HsP]
          · iexact HsP
          · iexact HA
      · iexact HN
    · refine (sep_mono (sep_mono_left psplit) psplit).trans ?_
      iintro ⟨⟨⟨HP, HpP⟩, Hf⟩, ⟨HW, HN⟩⟩
      isplitl [HP HW]
      · iapply HW; iexact HP
      · isplitl [HpP Hf]
        · isplitl [HpP]
          · iexact HpP
          · iexact Hf
        · iexact HN
  have SA : ∀ γ, sv γ (A γ) ⊢ A γ := fun γ =>
    (persistent_sep_dup_mp.trans (sep_mono_left (persistently_intro.trans (persistently_mono (wand_intro (NA γ)))))).trans
      (exists_intro (Ψ := fun P => iprop(<pers> (P -∗ F) ∗ sv γ P)) (A γ))
  have G : ∀ γ, sv γ (A γ) ⊢ F := fun γ =>
    persistent_sep_dup_mp.trans ((sep_mono_right (SA γ)).trans (NA γ))
  have alloc : ∀ γ, start γ ⊢ fupd .M1 F := fun γ =>
    or_intro_l.trans ((ha (body γ (A γ))).trans (hm (G γ)))
  exact hc (hs.trans (hmm.trans ((hm (exists_elim fun γ => (alloc γ).trans hff)).trans hff)))
