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
namespace T2c2
open Iris Iris.BI Iris.Std

/-! Copy of T1c0's closure-modality fupd (`LM`, `zf`, `zFupd`, `bL`, `zbFS`). -/
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

section
variable {PROP : Type _} [BI PROP]

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

theorem zM {L : LM PROP} {Y X : PROP} (h : Y ⊢ L.M X) : Y ⊢ zf L ∅ ∅ X :=
  imp_intro ((and_elim_l.trans h).trans (L.mono (and_intro (pure_intro rfl) .rfl)))
theorem zO {L : LM PROP} {X : PROP} : zf L ∅ ∅ X ⊢ L.M X :=
  (pure_imp_elim rfl).trans (L.mono and_elim_r)
end

section
variable {PROP : Type _} [Sbi PROP] [BIUpdate PROP]

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
end

/-! RN: discrete UORA e (unit), x, y1, y2, bot; all non-unit products bot; equality order
(UPred RN is non-affine). A nondeterministic update relation x → y1, x → y2 that never
reaches the unit gives a lawful basic update `rB`; plain props hold at the unit. -/
inductive RN | e | x | y1 | y2 | bot deriving DecidableEq

def RN.op : RN → RN → RN
  | .e, y => y
  | u, .e => u
  | _, _ => .bot

instance : OFE RN := OFE.ofDiscrete RN
instance : OFE.Discrete RN := ⟨id⟩

instance rnORA : ORA RN := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := RN.op
  Valid := fun x => x ≠ .bot
  Order := Eq
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y h; cases x <;> cases y <;> first | exact h | exact fun h' => nomatch h' | simp_all [RN.op]
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := by intro x y h hv; cases h; exact hv
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> rfl
  increasing_closed := by intro x y _ h; cases h; assumption }

instance : OrderRefl RN := ⟨fun x => show x = x from rfl⟩

instance rnUORA : UORA RN where
  unit := .e
  unit_valid := fun h => nomatch h
  unit_left_id := rfl
  pcore_unit := rfl

def rrel : RN → RN → Bool
  | .x, .y1 => true
  | .x, .y2 => true
  | a, b => decide (a = b)

theorem rrel_refl (a : RN) : rrel a a = true := by cases a <;> rfl
theorem rrel_trans (a b c : RN) : rrel a b = true → rrel b c = true → rrel a c = true := by
  cases a <;> cases b <;> cases c <;> decide
theorem rrel_frame (a b c : RN) : RN.op a b ≠ .bot → rrel a c = true →
    rrel (RN.op a b) (RN.op c b) = true ∧ RN.op c b ≠ .bot := by
  cases a <;> cases b <;> cases c <;> decide

theorem rn_valid {n : Nat} {a : RN} : ✓{n} a ↔ a ≠ .bot := Iff.rfl
theorem rn_ord {n : Nat} {a b : RN} : a ≼ₒ{n} b ↔ a = b := Iff.rfl
theorem rn_op {a b : RN} : a • b = RN.op a b := rfl


/-- The relational update on `UPred RN`. -/
def rbu (P : UPred RN) : UPred RN where
  holds n v := ∃ y : RN, ∃ hy : ✓{n} y, rrel v.val y = true ∧ P n ⟨y, hy⟩
  mono := by
    intro n1 n2 v1 v2 ⟨y, hy, hr, hp⟩ hle hn
    have e : v1.val = v2.val := hle
    exact ⟨y, hy, e ▸ hr, P.mono hp (ORA.ordN_refl y) hn⟩

def rB : BIUpdate (UPred RN) where
  bupd := rbu
  bupd_ne := ⟨fun n P Q h n' v hn hv =>
    ⟨fun ⟨y, hy, hr, hp⟩ => ⟨y, hy, hr, (h n' y hn hy).1 hp⟩,
     fun ⟨y, hy, hr, hp⟩ => ⟨y, hy, hr, (h n' y hn hy).2 hp⟩⟩⟩
  intro := fun n v hp => ⟨v.val, v.property, rrel_refl _, hp⟩
  mono h := fun n v ⟨y, hy, hr, hp⟩ => ⟨y, hy, hr, h n ⟨y, hy⟩ hp⟩
  trans := fun n v ⟨y, hy, hr, z, hz, hr2, hp⟩ => ⟨z, hz, rrel_trans _ _ _ hr hr2, hp⟩
  frame_right := by
    intro P R n v ⟨x1, x2, hx, ⟨y, hy, hr, hp⟩, hq⟩
    have e : RN.op x1 x2 = v.val := hx
    have hv : RN.op x1 x2 ≠ .bot := e ▸ v.property
    obtain ⟨h1, h2⟩ := rrel_frame x1 x2 y hv hr
    exact ⟨RN.op y x2, h2, e ▸ h1, y, x2, ORA.ordN_refl _, hp, hq⟩

theorem rBS : @BIBUpdateSbi (UPred RN) _ rB _ :=
  @BIBUpdateSbi.mk (UPred RN) _ rB _ (fun _ _ _ ⟨_, _, _, h⟩ => h)


/-- Plain props holding at the unit and at one outcome. -/
def ph (b : Bool) : UPred RN where
  holds _ v := v.val = .e ∨ v.val = (if b then .y1 else .y2)
  mono := by
    intro n1 n2 v1 v2 h hle _
    have e : v1.val = v2.val := hle
    exact e ▸ h

instance ph_plain (b : Bool) : Plain (ph b) := ⟨fun _ _ _ => Or.inl rfl⟩

abbrev rL : LM (UPred RN) := @bL (UPred RN) _ rB

theorem ph_reach (a : Bool) : (UPred.ownM RN.x : UPred RN) ⊢ rL.M (ph a) := by
  intro n v hv
  have e : RN.x = v.val := hv
  cases a
  · exact ⟨.y2, (fun h => nomatch h), e ▸ rfl, Or.inr (Or.inr rfl)⟩
  · exact ⟨.y1, (fun h => nomatch h), e ▸ rfl, Or.inr (Or.inr rfl)⟩

theorem ownx1 : (UPred.ownM RN.x : UPred RN).holds 2 ⟨.x, fun h => nomatch h⟩ := ORA.ordN_refl _

theorem ph_both {y : RN} (hr : rrel .x y = true) (h0 : y = .e ∨ y = .y1) (h1 : y = .e ∨ y = .y2) : False := by
  cases y <;> simp_all [rrel]

theorem bad1 (H : (UPred.ownM RN.x : UPred RN) ⊢ rL.M iprop(ph true ∧ ph false)) : False := by
  obtain ⟨y, hy, hr, hp⟩ := H 1 ⟨.x, fun h => nomatch h⟩ (ORA.ordN_refl _)
  rcases hp with hf | ⟨h0, h1⟩
  · exact hf
  · exact ph_both hr h0 h1

theorem bad2 (H : (UPred.ownM RN.x : UPred RN) ⊢ rL.M iprop(▷ rL.M iprop(ph true ∧ ph false))) : False := by
  obtain ⟨y, hy, hr, hp⟩ := H 2 ⟨.x, fun h => nomatch h⟩ (ORA.ordN_refl _)
  rcases hp with hf | hl
  · exact hf
  · obtain ⟨z, hz, hr2, hp2⟩ := hl
    rcases hp2 with hf | ⟨h0, h1⟩
    · exact hf
    · exact ph_both (rrel_trans _ _ _ hr hr2) h0 h1

end T2c2

open Iris Iris.BI Iris.Std T2c2 in
-- `Iris.ProofMode.fromForall_fupd` idx 4: necessary
theorem t2c2_1 : ¬ drop0% Iris.ProofMode.fromForall_fupd 4 := fun h => by
  have K := (@h (UPred RN) _ (zFupd rL) (@zbFS _ _ rB rBS) ∅ ∅ iprop(∀ b, ph b) Bool ph
    ⟨fun _ h => h⟩ ⟨.rfl⟩ ph_plain).from_forall
  exact bad1 <| (forall_intro fun a => zM (ph_reach a)).trans <| K.trans <| zO.trans <|
    rL.mono (and_intro (forall_elim true) (forall_elim false))

open Iris Iris.BI Iris.Std T2c2 in
-- `Iris.ProofMode.fromForall_stepFupd` idx 4: necessary (stated by hand at α : Type)
theorem t2c2_2 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP]
    {α : Type} (E1 E2 : CoPset) (P : PROP) (Φ : α → PROP) [inst_4 : Iris.ProofMode.TCSideCondition (E2 ⊆ E1)]
    [h : Iris.ProofMode.FromForall P Φ] [∀ (a : α), Iris.BI.Plain (Φ a)],
    Iris.ProofMode.FromForall iprop(|={E1}[E2]▷=> P) fun a => iprop(|={E1}[E2]▷=> Φ a)) := fun h => by
  have K := (@h (UPred RN) _ (zFupd rL) (@zbFS _ _ rB rBS) Bool ∅ ∅ iprop(∀ b, ph b) ph
    ⟨fun _ h => h⟩ ⟨.rfl⟩ ph_plain).from_forall
  exact bad2 <| (forall_intro fun a => zM ((ph_reach a).trans (rL.mono (later_intro.trans (later_mono (zM rL.intro)))))).trans <|
    K.trans <| zO.trans <| rL.mono <| later_mono <| zO.trans <|
    rL.mono (and_intro (forall_elim true) (forall_elim false))

namespace T2c2
open Iris Iris.BI Iris.Std

/-! TN: step-indexed Kripke BI over (Nat, +) where the "emp-resources" shrink with the step:
every resource at step 0, every resource except 1 later (`EE n x`). Props are downward closed in
the step and closed under adding emp-resources. `emp` is not timeless; a resource 2 = 1 + 1 is an
emp-resource at step 1 but its only split into Q-parts uses 1, which is not. -/
def EE (n x : Nat) : Prop := n = 0 ∨ x ≠ 1

theorem EE_mono {n n' x : Nat} (h : EE n x) (hle : n' ≤ n) : EE n' x := by
  unfold EE at *; omega
theorem EE_add {n x y : Nat} (h1 : EE n x) (h2 : EE n y) : EE n (x + y) := by
  unfold EE at *; omega
theorem EE_zero (n : Nat) : EE n 0 := .inr (by omega)

structure TN where
  holds : Nat → Nat → Prop
  mono {n n' : Nat} {m : Nat} : holds n m → n' ≤ n → holds n' m
  tr {n m x : Nat} : holds n m → EE n x → holds n (m + x)

theorem TN.ext' : {P Q : TN} → (∀ n m, P.holds n m ↔ Q.holds n m) → P = Q
  | ⟨p, _, _⟩, ⟨q, _, _⟩, h => by
    have : p = q := funext fun n => funext fun m => propext (h n m)
    subst this; rfl

def TN.emp : TN where
  holds n m := EE n m
  mono h hle := EE_mono h hle
  tr h hx := EE_add h hx
def TN.pure (φ : Prop) : TN where
  holds _ _ := φ
  mono h _ := h
  tr h _ := h
def TN.and (P Q : TN) : TN where
  holds n m := P.holds n m ∧ Q.holds n m
  mono h hle := ⟨P.mono h.1 hle, Q.mono h.2 hle⟩
  tr h hx := ⟨P.tr h.1 hx, Q.tr h.2 hx⟩
def TN.or (P Q : TN) : TN where
  holds n m := P.holds n m ∨ Q.holds n m
  mono h hle := h.elim (fun h => .inl (P.mono h hle)) (fun h => .inr (Q.mono h hle))
  tr h hx := h.elim (fun h => .inl (P.tr h hx)) (fun h => .inr (Q.tr h hx))
def TN.imp (P Q : TN) : TN where
  holds n m := ∀ n', n' ≤ n → ∀ x, EE n' x → P.holds n' (m + x) → Q.holds n' (m + x)
  mono h hle n'' h'' x hx hp := h n'' (Nat.le_trans h'' hle) x hx hp
  tr {n m y} h hy n' hle x hx hp := by
    have e : m + y + x = m + (y + x) := Nat.add_assoc m y x
    rw [e] at hp ⊢
    exact h n' hle (y + x) (EE_add (EE_mono hy hle) hx) hp
def TN.sForall (Ψ : TN → Prop) : TN where
  holds n m := ∀ p, Ψ p → p.holds n m
  mono h hle p hp := p.mono (h p hp) hle
  tr h hx p hp := p.tr (h p hp) hx
def TN.sExists (Ψ : TN → Prop) : TN where
  holds n m := ∃ p, Ψ p ∧ p.holds n m
  mono h hle := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.mono h hle⟩
  tr h hx := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.tr h hx⟩
def TN.sep (P Q : TN) : TN where
  holds n m := ∃ a b, m = a + b ∧ P.holds n a ∧ Q.holds n b
  mono h hle := let ⟨a, b, e, hp, hq⟩ := h; ⟨a, b, e, P.mono hp hle, Q.mono hq hle⟩
  tr {n m x} h hx := let ⟨a, b, e, hp, hq⟩ := h; ⟨a, b + x, by omega, hp, Q.tr hq hx⟩
def TN.wand (P Q : TN) : TN where
  holds n m := ∀ n', n' ≤ n → ∀ b, P.holds n' b → Q.holds n' (m + b)
  mono h hle n'' h'' b hp := h n'' (Nat.le_trans h'' hle) b hp
  tr {n m y} h hy n' hle b hp := by
    have e : m + y + b = m + b + y := by omega
    rw [e]; exact Q.tr (h n' hle b hp) (EE_mono hy hle)
def TN.pers (P : TN) : TN where
  holds n _ := P.holds n 0
  mono h hle := P.mono h hle
  tr h _ := h
def TN.later (P : TN) : TN where
  holds n m := match n with | 0 => True | k+1 => P.holds k m
  mono {n n' m} h hle := by
    cases n' with
    | zero => trivial
    | succ k' => cases n with
      | zero => omega
      | succ k => exact P.mono h (by omega)
  tr {n m x} h hx := by
    cases n with
    | zero => trivial
    | succ k => exact P.tr h (EE_mono hx (Nat.le_succ k))

instance : BIBase TN where
  Entails P Q := ∀ n m, P.holds n m → Q.holds n m
  emp := TN.emp
  pure := TN.pure
  and := TN.and
  or := TN.or
  imp := TN.imp
  sForall := TN.sForall
  sExists := TN.sExists
  sep := TN.sep
  wand := TN.wand
  persistently := TN.pers
  later := TN.later

instance : COFE TN := COFE.ofDiscrete _

instance tnBI : BI TN where
  entails_refl _ _ h := h
  entails_trans h1 h2 n m h := h2 n m (h1 n m h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ _ h => h, fun _ _ h => h⟩,
    fun ⟨h1, h2⟩ => TN.ext' fun n m => ⟨h1 n m, h2 n m⟩⟩
  and_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  pure_intro h _ _ _ := h
  pure_elim' h n m hφ := h hφ n m trivial
  and_elim_l _ _ h := h.1
  and_elim_r _ _ h := h.2
  and_intro h1 h2 n m h := ⟨h1 n m h, h2 n m h⟩
  or_intro_l _ _ h := .inl h
  or_intro_r _ _ h := .inr h
  or_elim h1 h2 n m h := h.elim (h1 n m) (h2 n m)
  imp_intro {P _ _} h n m hp n' hle x hx hq := h n' (m + x) ⟨P.tr (P.mono hp hle) hx, hq⟩
  imp_elim h n m hpq := h n m hpq.1 n (Nat.le_refl n) 0 (EE_zero n) hpq.2
  sForall_intro h n m hp p hΨ := h p hΨ n m hp
  sForall_elim hΨ n m h := h _ hΨ
  sExists_intro hΨ n m h := ⟨_, hΨ, h⟩
  sExists_elim h n m := fun ⟨p, hp, hh⟩ => h p hp n m hh
  sep_mono h1 h2 n m := fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, h1 n a hp, h2 n b hq⟩
  emp_sep {P} := ⟨fun n m ⟨a, b, e, he, hp⟩ => by
      have e' : m = b + a := by omega
      rw [e']; exact P.tr hp he,
    fun n m hp => ⟨0, m, (Nat.zero_add m).symm, EE_zero n, hp⟩⟩
  sep_symm n m := fun ⟨a, b, e, hp, hq⟩ => ⟨b, a, by omega, hq, hp⟩
  sep_assoc_l n m := fun ⟨_, c, e, ⟨a, b, e', hp, hq⟩, hr⟩ =>
    ⟨a, b + c, by omega, hp, b, c, rfl, hq, hr⟩
  wand_intro {P _ _} h n m hp n' hle b hq := h n' (m + b) ⟨m, b, rfl, P.mono hp hle, hq⟩
  wand_elim h n m := fun ⟨a, b, e, hp, hq⟩ => e ▸ h n a hp n (Nat.le_refl n) b hq
  persistently_mono h n _ hp := h n 0 hp
  persistently_idem_2 _ _ h := h
  persistently_emp_2 n _ _ := EE_zero n
  persistently_and_2 _ _ h := h
  persistently_absorb_l n m := fun ⟨_, _, _, hp, _⟩ => hp
  persistently_and_l n m := fun ⟨hp, hq⟩ => ⟨0, m, (Nat.zero_add m).symm, hp, hq⟩
  later_mono h n m hp := by
    cases n with
    | zero => trivial
    | succ k => exact h k m hp
  later_intro {P} n m hp := by
    cases n with
    | zero => trivial
    | succ k => exact P.mono hp (Nat.le_succ k)
  later_sForall_2 n m h := by
    cases n with
    | zero => trivial
    | succ k => exact fun p hp => h _ ⟨p, rfl⟩ (k+1) (Nat.le_refl _) 0 (EE_zero _) hp
  later_sExists_false n m h := by
    cases n with
    | zero => exact .inl trivial
    | succ k =>
      obtain ⟨p, hp, hh⟩ := h
      exact .inr ⟨_, ⟨p, rfl⟩, hp, hh⟩
  later_sep := ⟨fun n m h => by
      cases n with
      | zero => exact ⟨m, 0, rfl, trivial, trivial⟩
      | succ k => exact h,
    fun n m h => by
      cases n with
      | zero => trivial
      | succ k => exact h⟩
  later_persistently := ⟨fun n m h => by cases n <;> exact h, fun n m h => by cases n <;> exact h⟩
  later_false_em {P} n m h := by
    cases n with
    | zero => exact .inl trivial
    | succ k =>
      refine .inr fun n' hle x hx hf => ?_
      cases n' with
      | zero => exact P.tr (P.mono h (Nat.zero_le _)) (.inl rfl)
      | succ j => exact hf.elim

/-- Holds only at step 0, at every nonzero resource. -/
def tnQ : TN where
  holds n m := n = 0 ∧ 1 ≤ m
  mono h hle := ⟨by omega, h.2⟩
  tr h _ := ⟨h.1, by omega⟩

instance tnQ_aff : Affine tnQ := ⟨fun n m h => .inl h.1⟩

end T2c2

open Iris Iris.BI Iris.Std T2c2 in
-- `Iris.ProofMode.intoSep_affinely_later` idx 2: necessary
theorem t2c2_3 : ¬ drop0% Iris.ProofMode.intoSep_affinely_later 2 := fun h => by
  have K := (@h TN _ iprop(tnQ ∗ tnQ) tnQ tnQ ⟨.rfl⟩ tnQ_aff tnQ_aff).into_sep
  obtain ⟨a, b, e, ⟨ha, _, ha2⟩, ⟨hb, _, hb2⟩⟩ := K 1 2 ⟨.inr (by omega), 1, 1, rfl, ⟨rfl, Nat.le_refl 1⟩, ⟨rfl, Nat.le_refl 1⟩⟩
  have ha' : EE 1 a := ha
  have hb' : EE 1 b := hb
  have ha2' : 1 ≤ a := ha2
  have hb2' : 1 ≤ b := hb2
  unfold EE at ha' hb'
  omega
