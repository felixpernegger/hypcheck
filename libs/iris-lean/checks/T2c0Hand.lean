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
namespace T2c0
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

/-- One-way steps: stay, or move from the start token s to an outcome c0 or c1 (never to e). -/
def ndR (x y : ND) : Prop := x = y ∨ (x = .s ∧ (y = .c0 ∨ y = .c1))

theorem ndR_trans {x y z : ND} (h1 : ndR x y) (h2 : ndR y z) : ndR x z := by
  rcases h1 with h | ⟨hx, hy⟩
  · subst h; exact h2
  · rcases h2 with h | ⟨hy', _⟩
    · subst h; exact .inr ⟨hx, hy⟩
    · subst hy'; rcases hy with h | h <;> cases h

theorem ndR_frame {x1 x2 y1 : ND} (h : ndR x1 y1) (hv : ND.op x1 x2 ≠ .bot) : ndR (ND.op x1 x2) (ND.op y1 x2) := by
  rcases h with h | ⟨hx, hy⟩
  · subst h; exact .inl rfl
  · subst hx; cases x2
    · exact .inr ⟨rfl, by rcases hy with h | h <;> subst h <;> simp [ND.op]⟩
    all_goals exact absurd rfl hv

/-- The update modality of the steps ndR (no frame quantification: it cannot drop resources). -/
def ndU (Q : UPred ND) : UPred ND where
  holds n x := ∃ y, ndR x.val y ∧ ∃ H : ✓{n} y, Q n ⟨y, H⟩
  mono := fun ⟨y, hr, hv, hq⟩ hle hn => ⟨y, (show _ = _ from hle) ▸ hr, hv, Q.mono hq (ORA.ordN_refl y) hn⟩


def ndBU : @BIUpdate (UPred ND) _ where
  toBUpd := ⟨ndU⟩
  bupd_ne := ⟨fun n P Q H n' x hn hx => ⟨fun ⟨y, hr, hv, hq⟩ => ⟨y, hr, hv, (H n' y hn hv).1 hq⟩,
    fun ⟨y, hr, hv, hq⟩ => ⟨y, hr, hv, (H n' y hn hv).2 hq⟩⟩⟩
  intro {P} n x hp := ⟨x.val, .inl rfl, x.property, hp⟩
  mono h n x := fun ⟨y, hr, hv, hq⟩ => ⟨y, hr, hv, h n ⟨y, hv⟩ hq⟩
  trans n x := fun ⟨y, hr, hv, z, hr2, hv2, hq⟩ => ⟨z, ndR_trans hr hr2, hv2, hq⟩
  frame_right {P R} n x := fun ⟨x1, x2, hx, ⟨y1, hr, hv, hp⟩, hR⟩ => by
    have hx' : ND.op x1 x2 = x.val := hx
    have hxv : ND.op x1 x2 ≠ .bot := hx' ▸ x.property
    refine ⟨ND.op y1 x2, hx' ▸ ndR_frame hr hxv, ?_, y1, x2, rfl, hp, hR⟩
    rcases hr with h | ⟨h1, h2⟩
    · subst h; exact hxv
    · subst h1; cases x2
      · rcases h2 with h | h <;> subst h <;> exact hv
      all_goals exact absurd rfl hxv

theorem ndBS : @BIBUpdateSbi (UPred ND) _ ndBU _ :=
  @BIBUpdateSbi.mk (UPred ND) _ ndBU _ (fun _ n x => fun ⟨_, _, _, hq⟩ => hq)


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

theorem zM {L : LM PROP} {Y X : PROP} (h : Y ⊢ L.M X) : Y ⊢ zf L ∅ ∅ X :=
  imp_intro ((and_elim_l.trans h).trans (L.mono (and_intro (pure_intro rfl) .rfl)))
theorem zO {L : LM PROP} {X : PROP} : zf L ∅ ∅ X ⊢ L.M X :=
  (pure_imp_elim rfl).trans (L.mono and_elim_r)
end

section
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
end

/-! ND model with the step update ndU: lawful BIFUpdateSbi fupd zf (|==> ◇) on the non-affine `UPred ND`. -/
abbrev ndL : LM (UPred ND) := @bL (UPred ND) _ ndBU
abbrev ndF : BIFUpdate (UPred ND) := zFupd ndL
theorem ndFS : @BIFUpdateSbi (UPred ND) _ ndF _ := @zbFS (UPred ND) _ ndBU ndBS

def ndc (b : Bool) : ND := if b then .c1 else .c0

/-- Plain, not absorbing: holds at the unit and at the outcome c_b. -/
def ndP (b : Bool) : UPred ND where
  holds _ x := x.val = .e ∨ x.val = ndc b
  mono h hle _ := (show _ = _ from hle) ▸ h

instance ndP_plain (b : Bool) : Plain (ndP b) := ⟨fun _ _ _ => .inl rfl⟩

theorem nd_own_s (b : Bool) : UPred.ownM ND.s ⊢ ndL.M (ndP b) := fun _ x hs => by
  have e : ND.s = x.val := hs
  refine ⟨ndc b, e ▸ .inr ⟨rfl, by cases b <;> simp [ndc]⟩, by cases b <;> (intro h; cases h), .inr (.inr rfl)⟩

theorem nd_fin {y : ND} (hr : ndR .s y) (h0 : y = .e ∨ y = ndc false) (h1 : y = .e ∨ y = ndc true) : False := by
  rcases hr with h | ⟨-, h⟩
  · subst h; rcases h0 with h | h <;> cases h
  · rcases h with h | h <;> subst h <;> simp [ndc] at h0 h1

theorem nd_bad1 (h : UPred.ownM ND.s ⊢ ndL.M iprop(∀ b, ndP b)) : False := by
  obtain ⟨y, hr, _, h⟩ := h 1 ⟨.s, fun h => nomatch h⟩ (ORA.ordN_refl _)
  rcases h with h | h
  · exact h
  · exact nd_fin hr (h _ ⟨false, rfl⟩) (h _ ⟨true, rfl⟩)

theorem nd_bad2 (h : UPred.ownM ND.s ⊢ ndL.M iprop(▷ ndL.M iprop(∀ b, ndP b))) : False := by
  obtain ⟨y, hr, _, h⟩ := h 2 ⟨.s, fun h => nomatch h⟩ (ORA.ordN_refl _)
  rcases h with h | h
  · exact h
  · obtain ⟨z, hr2, _, h⟩ := h
    rcases h with h | h
    · exact h
    · exact nd_fin (ndR_trans hr hr2) (h _ ⟨false, rfl⟩) (h _ ⟨true, rfl⟩)

theorem nd_lhs1 : UPred.ownM ND.s ⊢ iprop(∀ b, zf ndL ∅ ∅ (ndP b)) :=
  forall_intro fun b => zM (nd_own_s b)

theorem nd_lhs2 : UPred.ownM ND.s ⊢ iprop(∀ b, zf ndL ∅ ∅ iprop(▷ zf ndL ∅ ∅ (ndP b))) :=
  forall_intro fun b => zM ((later_intro.trans (later_mono (zM (nd_own_s b)))).trans ndL.intro)


theorem nd_bu (b : Bool) : UPred.ownM ND.s ⊢ ndU (ndP b) := fun _ x hs => by
  have e : ND.s = x.val := hs
  exact ⟨ndc b, e ▸ .inr ⟨rfl, by cases b <;> simp [ndc]⟩, by cases b <;> (intro h; cases h), .inr rfl⟩

theorem nd_bu_bad (h : UPred.ownM ND.s ⊢ ndU iprop(∀ b, ndP b)) : False := by
  obtain ⟨y, hr, _, h⟩ := h 1 ⟨.s, fun h => nomatch h⟩ (ORA.ordN_refl _)
  exact nd_fin hr (h _ ⟨false, rfl⟩) (h _ ⟨true, rfl⟩)


/-! ND with a step-dependent one-way update: s may move to c0 or c1 only at steps ≤ 1. -/
def ndS (n : Nat) (x y : ND) : Prop := x = y ∨ (n ≤ 1 ∧ x = .s ∧ (y = .c0 ∨ y = .c1))

theorem ndS_trans {n : Nat} {x y z : ND} (h1 : ndS n x y) (h2 : ndS n y z) : ndS n x z := by
  rcases h1 with h | ⟨hn, hx, hy⟩
  · subst h; exact h2
  · rcases h2 with h | ⟨_, hy', _⟩
    · subst h; exact .inr ⟨hn, hx, hy⟩
    · subst hy'; rcases hy with h | h <;> cases h

theorem ndS_le {n m : Nat} {x y : ND} (h : ndS n x y) (hm : m ≤ n) : ndS m x y :=
  h.elim .inl fun ⟨hn, hx, hy⟩ => .inr ⟨Nat.le_trans hm hn, hx, hy⟩

def ndV (Q : UPred ND) : UPred ND where
  holds n x := ∃ y, ndS n x.val y ∧ ∃ H : ✓{n} y, Q n ⟨y, H⟩
  mono := fun ⟨y, hr, hv, hq⟩ hle hn => ⟨y, ndS_le ((show _ = _ from hle) ▸ hr) hn, hv, Q.mono hq (ORA.ordN_refl y) hn⟩

def ndBV : @BIUpdate (UPred ND) _ where
  toBUpd := ⟨ndV⟩
  bupd_ne := ⟨fun n P Q H n' x hn hx => ⟨fun ⟨y, hr, hv, hq⟩ => ⟨y, hr, hv, (H n' y hn hv).1 hq⟩,
    fun ⟨y, hr, hv, hq⟩ => ⟨y, hr, hv, (H n' y hn hv).2 hq⟩⟩⟩
  intro {P} n x hp := ⟨x.val, .inl rfl, x.property, hp⟩
  mono h n x := fun ⟨y, hr, hv, hq⟩ => ⟨y, hr, hv, h n ⟨y, hv⟩ hq⟩
  trans n x := fun ⟨y, hr, hv, z, hr2, hv2, hq⟩ => ⟨z, ndS_trans hr hr2, hv2, hq⟩
  frame_right {P R} n x := fun ⟨x1, x2, hx, ⟨y1, hr, hv, hp⟩, hR⟩ => by
    have hx' : ND.op x1 x2 = x.val := hx
    have hxv : ND.op x1 x2 ≠ .bot := hx' ▸ x.property
    rcases hr with h | ⟨hn, h1, h2⟩
    · subst h; exact ⟨ND.op x1 x2, hx' ▸ .inl rfl, hxv, x1, x2, rfl, hp, hR⟩
    · subst h1; cases x2
      · refine ⟨y1, hx' ▸ .inr ⟨hn, rfl, h2⟩, hv, y1, ND.e, ?_, hp, hR⟩
        rcases h2 with h | h <;> subst h <;> rfl
      all_goals exact absurd rfl hxv

theorem ndBVS : @BIBUpdateSbi (UPred ND) _ ndBV _ :=
  @BIBUpdateSbi.mk (UPred ND) _ ndBV _ (fun _ n x => fun ⟨_, _, _, hq⟩ => hq)

abbrev ndL2 : LM (UPred ND) := @bL (UPred ND) _ ndBV
abbrev ndF2 : BIFUpdate (UPred ND) := zFupd ndL2
theorem ndFS2 : @BIFUpdateSbi (UPred ND) _ ndF2 _ := @zbFS (UPred ND) _ ndBV ndBVS

/-- From s at steps ≤ 1 the update reaches c0, where ndP false holds. -/
theorem nd2_reach : iprop(UPred.ownM ND.s ∧ ▷ ▷ False) ⊢ ndL2.M (ndP false) := fun n x ⟨hs, hl⟩ => by
  have e : ND.s = x.val := hs
  have hn : n ≤ 1 := by
    rcases n with _ | _ | n
    · exact Nat.zero_le _
    · exact Nat.le_refl _
    · exact hl.elim
  exact ⟨ND.c0, e ▸ Or.inr ⟨hn, rfl, Or.inl rfl⟩, (fun h => nomatch h), Or.inr (Or.inr rfl)⟩

theorem nd2_lhs : iprop(UPred.ownM ND.s ∧ ▷ ▷ ▷ False) ⊢ iprop(▷ zf ndL2 ∅ ∅ (ndP false)) :=
  (and_mono later_intro .rfl).trans <| later_and.2.trans <| later_mono (zM nd2_reach)

/-- At step 2 the update cannot leave s, and ndP false fails at s one step later. -/
theorem nd2_bad (h : iprop(UPred.ownM ND.s ∧ ▷ ▷ ▷ False) ⊢ ndL2.M iprop(▷ ◇ ndP false)) : False := by
  obtain ⟨y, hr, _, h⟩ := h 2 ⟨.s, fun h => nomatch h⟩ ⟨ORA.ordN_refl _, trivial⟩
  rcases hr with hr | ⟨hn, -⟩
  · subst hr
    rcases h with h | h
    · exact h
    · rcases h with h | h
      · exact h
      · rcases h with h | h <;> cases h
  · exact absurd hn (by decide)


/-! NDA: as ND with the extension order (affine `UPred NDA`), and the step-dependent one-way update. -/
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

def ndaS (n : Nat) (x y : NDA) : Prop := x = y ∨ (n ≤ 1 ∧ x = .s ∧ (y = .c0 ∨ y = .c1))

theorem ndaS_trans {n : Nat} {x y z : NDA} (h1 : ndaS n x y) (h2 : ndaS n y z) : ndaS n x z := by
  rcases h1 with h | ⟨hn, hx, hy⟩
  · subst h; exact h2
  · rcases h2 with h | ⟨_, hy', _⟩
    · subst h; exact .inr ⟨hn, hx, hy⟩
    · subst hy'; rcases hy with h | h <;> cases h

theorem ndaS_le {n m : Nat} {x y : NDA} (h : ndaS n x y) (hm : m ≤ n) : ndaS m x y :=
  h.elim .inl fun ⟨hn, hx, hy⟩ => .inr ⟨Nat.le_trans hm hn, hx, hy⟩

def ndaV (Q : UPred NDA) : UPred NDA where
  holds n x := ∃ y, ndaS n x.val y ∧ ∃ H : ✓{n} y, Q n ⟨y, H⟩
  mono {n1 n2 x1 x2} := fun ⟨y, hr, hv, hq⟩ hle hn => by
    have hle' : x1.val = .e ∨ x1.val = x2.val ∨ x2.val = .bot := hle
    have hx2 : x2.val ≠ .bot := x2.property
    rcases hle' with h | h | h
    · rcases hr with hr | ⟨-, hs, -⟩
      · refine ⟨x2.val, .inl rfl, x2.property, Q.mono hq ?_ hn⟩
        show y = .e ∨ y = x2.val ∨ x2.val = .bot
        exact .inl (hr ▸ h)
      · rw [h] at hs; cases hs
    · exact ⟨y, ndaS_le (h ▸ hr) hn, hv, Q.mono hq (ORA.ordN_refl y) hn⟩
    · exact absurd h hx2

def ndaBV : @BIUpdate (UPred NDA) _ where
  toBUpd := ⟨ndaV⟩
  bupd_ne := ⟨fun n P Q H n' x hn hx => ⟨fun ⟨y, hr, hv, hq⟩ => ⟨y, hr, hv, (H n' y hn hv).1 hq⟩,
    fun ⟨y, hr, hv, hq⟩ => ⟨y, hr, hv, (H n' y hn hv).2 hq⟩⟩⟩
  intro {P} n x hp := ⟨x.val, .inl rfl, x.property, hp⟩
  mono h n x := fun ⟨y, hr, hv, hq⟩ => ⟨y, hr, hv, h n ⟨y, hv⟩ hq⟩
  trans n x := fun ⟨y, hr, hv, z, hr2, hv2, hq⟩ => ⟨z, ndaS_trans hr hr2, hv2, hq⟩
  frame_right {P R} n x := fun ⟨x1, x2, hx, ⟨y1, hr, hv, hp⟩, hR⟩ => by
    have hxv : x.val ≠ .bot := x.property
    rcases hr with h | ⟨hn, h1, h2⟩
    · subst h; exact ⟨x.val, .inl rfl, x.property, x1, x2, hx, hp, hR⟩
    · subst h1
      have H' : NDA.op .s x2 = .e ∨ NDA.op .s x2 = x.val ∨ x.val = .bot := hx
      cases x2
      · have hs : x.val = .s := by
          rcases H' with h | h | h
          · cases h
          · exact h.symm
          · exact absurd h hxv
        refine ⟨y1, hs ▸ .inr ⟨hn, rfl, h2⟩, hv, y1, .e, ?_, hp, hR⟩
        rcases h2 with h | h <;> subst h <;> exact .inr (.inl rfl)
      all_goals (exfalso; rcases H' with h | h | h; · cases h
                 · exact hxv h.symm
                 · exact hxv h)

theorem ndaBVS : @BIBUpdateSbi (UPred NDA) _ ndaBV _ :=
  @BIBUpdateSbi.mk (UPred NDA) _ ndaBV _ (fun _ n x => fun ⟨_, _, _, hq⟩ => hq)

abbrev ndaL : LM (UPred NDA) := @bL (UPred NDA) _ ndaBV
abbrev ndaF : BIFUpdate (UPred NDA) := zFupd ndaL
theorem ndaFS : @BIFUpdateSbi (UPred NDA) _ ndaF _ := @zbFS (UPred NDA) _ ndaBV ndaBVS

theorem nda_reach : iprop(UPred.ownM NDA.s ∧ ▷ ▷ False) ⊢ ndaL.M (UPred.ownM NDA.c0) := fun n x ⟨hs, hl⟩ => by
  have e : NDA.s = .e ∨ NDA.s = x.val ∨ x.val = .bot := hs
  have hxv : x.val ≠ .bot := x.property
  have e' : NDA.s = x.val := by
    rcases e with h | h | h
    · cases h
    · exact h
    · exact absurd h hxv
  have hn : n ≤ 1 := by
    rcases n with _ | _ | n
    · exact Nat.zero_le _
    · exact Nat.le_refl _
    · exact hl.elim
  exact ⟨NDA.c0, e' ▸ Or.inr ⟨hn, rfl, Or.inl rfl⟩, (fun h => nomatch h), Or.inr (Or.inr (Or.inl rfl))⟩

theorem nda_lhs : iprop(UPred.ownM NDA.s ∧ ▷ ▷ ▷ False) ⊢ iprop(▷ zf ndaL ∅ ∅ (UPred.ownM NDA.c0)) :=
  (and_mono later_intro .rfl).trans <| later_and.2.trans <| later_mono (zM nda_reach)

theorem nda_bad (h : iprop(UPred.ownM NDA.s ∧ ▷ ▷ ▷ False) ⊢ ndaL.M iprop(▷ ◇ UPred.ownM NDA.c0)) : False := by
  obtain ⟨y, hr, _, h⟩ := h 2 ⟨.s, fun h => nomatch h⟩ ⟨.inr (.inl rfl), trivial⟩
  rcases hr with hr | ⟨hn, -⟩
  · subst hr
    rcases h with h | h
    · exact h
    · rcases h with h | h
      · exact h
      · have h' : NDA.c0 = .e ∨ NDA.c0 = .s ∨ NDA.s = .bot := h
        rcases h' with h | h | h <;> cases h
  · exact absurd hn (by decide)


/-- except0 as the closure modality. -/
def exL {PROP : Type _} [BI PROP] : LM PROP where
  M P := iprop(◇ P)
  ne := ⟨fun _ _ _ h => or_ne.ne .rfl h⟩
  mono := except0_mono
  intro := except0_intro
  join := except0_idem.1
  frame := except0_frame_right
  ex0 := except0_idem.1

/-! A second lawful BI on the carrier `SiProp`: the reversed chain (entailment reversed, a
complete Heyting algebra; sep = and, persistently = later = id), discrete COFE. -/
def rImp (P Q : SiProp) : SiProp := ⟨fun n => ¬ (∀ k, Q.holds k → P.holds k) ∧ Q.holds n,
  fun h hle => ⟨h.1, Q.closed h.2 hle⟩⟩
def rAnd (P Q : SiProp) : SiProp := ⟨fun n => P.holds n ∨ Q.holds n,
  fun h hle => h.elim (fun h => .inl (P.closed h hle)) (fun h => .inr (Q.closed h hle))⟩

theorem si_ext {P Q : SiProp} (h : ∀ n, P.holds n ↔ Q.holds n) : P = Q := by
  cases P; cases Q; congr; funext n; exact propext (h n)

theorem rImp_intro {P Q R : SiProp} (h : ∀ n, Q.holds n → R.holds n ∨ P.holds n) :
    ∀ n, (rImp P Q).holds n → R.holds n := fun n ⟨hn, hq⟩ => by
  rcases h n hq with hr | hp
  · exact hr
  · obtain ⟨m, hm⟩ := Classical.not_forall.1 hn
    have ⟨hqm, hpm⟩ := Classical.not_imp.1 hm
    rcases h m hqm with hr | hp'
    · rcases Nat.lt_or_ge n m with hl | hl
      · exact R.closed hr (Nat.le_of_lt hl)
      · exact absurd (P.closed hp hl) hpm
    · exact absurd hp' hpm

theorem rImp_elim {P Q R : SiProp} (h : ∀ n, (rImp P Q).holds n → R.holds n) :
    ∀ n, Q.holds n → R.holds n ∨ P.holds n := fun n hq => by
  by_cases hp : P.holds n
  · exact .inr hp
  · exact .inl (h n ⟨fun hall => hp (hall n hq), hq⟩)

/-- The carrier SiProp under a new name, so that instance search does not see SiProp's own BI. -/
def RSi : Type := SiProp

instance : COFE RSi := COFE.ofDiscrete _

instance revBase : BIBase RSi where
  Entails P Q := ∀ n, SiProp.holds Q n → SiProp.holds P n
  emp := ⟨fun _ => False, fun h _ => h⟩
  pure φ := ⟨fun _ => ¬ φ, fun h _ => h⟩
  and := rAnd
  or P Q := (⟨fun n => SiProp.holds P n ∧ SiProp.holds Q n, fun h hle => ⟨SiProp.closed P h.1 hle, SiProp.closed Q h.2 hle⟩⟩ : SiProp)
  imp := rImp
  sForall Ψ := (⟨fun n => ∃ p : SiProp, Ψ p ∧ p.holds n, fun ⟨p, hp, h⟩ hle => ⟨p, hp, p.closed h hle⟩⟩ : SiProp)
  sExists Ψ := (⟨fun n => ∀ p : SiProp, Ψ p → p.holds n, fun h hle p hp => p.closed (h p hp) hle⟩ : SiProp)
  sep := rAnd
  wand := rImp
  persistently P := P
  later P := P

instance revBI : BI RSi where
  entails_refl := fun _ h => h
  entails_trans := fun h1 h2 n h => h1 n (h2 n h)
  equiv_iff := ⟨fun h => h ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h₁, h₂⟩ => si_ext fun n => ⟨h₂ n, h₁ n⟩⟩
  and_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne := fun {_ P Q} h => (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne := fun {_ P Q} h => (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  pure_intro := fun hφ _ h => absurd hφ h
  pure_elim' := fun h _ hp hφ => h hφ _ hp trivial
  and_elim_l := fun _ h => .inl h
  and_elim_r := fun _ h => .inr h
  and_intro := fun h1 h2 n h => h.elim (h1 n) (h2 n)
  or_intro_l := fun _ h => h.1
  or_intro_r := fun _ h => h.2
  or_elim := fun h1 h2 n h => ⟨h1 n h, h2 n h⟩
  imp_intro := fun h => rImp_intro h
  imp_elim := fun h => rImp_elim h
  sForall_intro := fun h n ⟨p, hp, hn⟩ => h p hp n hn
  sForall_elim := fun hp _ h => ⟨_, hp, h⟩
  sExists_intro := fun hp _ h => h _ hp
  sExists_elim := fun h n hq p hp => h p hp n hq
  sep_mono := fun h1 h2 n h => h.elim (fun h => .inl (h1 n h)) (fun h => .inr (h2 n h))
  emp_sep := ⟨fun _ h => .inr h, fun _ h => h.elim (fun h => h.elim) id⟩
  sep_symm := fun _ h => h.symm
  sep_assoc_l := fun _ h => h.elim (fun h => .inl (.inl h)) (fun h => h.elim (fun h => .inl (.inr h)) .inr)
  wand_intro := fun h => rImp_intro h
  wand_elim := fun h => rImp_elim h
  persistently_mono := fun h => h
  persistently_idem_2 := fun _ h => h
  persistently_emp_2 := fun _ h => h
  persistently_and_2 := fun _ h => h
  persistently_absorb_l := fun _ h => .inl h
  persistently_and_l := fun _ h => h
  later_mono := fun h => h
  later_intro := fun _ h => h
  later_sForall_2 := fun {Φ} n ⟨p, hΦ, hp⟩ => ⟨_, ⟨p, rfl⟩, fun h => h n hp hΦ, hp⟩
  later_sExists_false := fun {Φ} n h p hΦ => (h.2 _ ⟨p, rfl⟩).elim (fun h => absurd hΦ h) id
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em := fun _ h => h.2.2

/-- SiProp's own Sbi, seen on the renamed carrier (its BI is the standard one, not revBI). -/
def rSbi : Sbi RSi := instSbiSiProp
abbrev rF : BIFUpdate RSi := zFupd exL

end T2c0

namespace T2c0
open Iris Iris.BI Iris.Std Iris.Std.LawfulSet

/-- A family of exact mask-token propositions: disjoint masks split and join. -/
structure TW (PROP : Type _) [BI PROP] where
  W : CoPset → PROP
  split : ∀ {A B : CoPset}, A ## B → W (A ∪ B) ⊢ iprop(W A ∗ W B)
  join : ∀ {A B : CoPset}, iprop(W A ∗ W B) ⊢ iprop(⌜A ## B⌝ ∧ W (A ∪ B))

theorem sub_eq {E1 E2 : CoPset} (h : E2 ⊆ E1) : E1 = E2 ∪ (E1 \ E2) :=
  CoPset.ext fun p => ⟨fun hp => by
      by_cases h2 : p ∈ E2
      · exact mem_union.2 (.inl h2)
      · exact mem_union.2 (.inr (mem_diff.2 ⟨hp, h2⟩)),
    fun hp => (mem_union.1 hp).elim (h p) (fun h' => (mem_diff.1 h').1)⟩

section
variable {PROP : Type _} [BI PROP]

theorem wq (T : TW PROP) {A B : CoPset} (h : A = B) : T.W A ⊢ T.W B := h ▸ .rfl

/-- Token fancy update: trade the enabled-mask tokens W E1 for W E2 and P (under except0). -/
def tf (T : TW PROP) (E1 E2 : CoPset) (P : PROP) : PROP := iprop(T.W E1 -∗ ◇ (T.W E2 ∗ P))

def tFupd (T : TW PROP) : BIFUpdate PROP where
  fupd := tf T
  ne := ⟨fun _ _ _ h => wand_ne.ne .rfl (or_ne.ne .rfl (sep_ne.ne .rfl h))⟩
  subset {E1 E2} h := wand_intro <| emp_sep.1.trans <| (wq T (sub_eq h)).trans <|
    (T.split (fun p ⟨h1, h2⟩ => (mem_diff.1 h2).2 h1)).trans <| (sep_mono_right (wand_intro <|
      T.join.trans <| and_elim_r.trans <| (wq T (by rw [union_comm]; exact (sub_eq h).symm)).trans <|
        sep_emp.2.trans except0_intro)).trans except0_intro
  except0 := wand_intro <| (sep_mono_right except0_intro).trans <| except0_sep.2.trans <|
    (except0_mono wand_elim_left).trans except0_idem.1
  mono h := wand_mono_right (except0_mono (sep_mono_right h))
  trans := wand_intro <| wand_elim_left.trans <| (except0_mono (sep_symm.trans wand_elim_left)).trans except0_idem.1
  mask_frame_right_strong {E1 E2 Ef P} hd := wand_intro <| (sep_mono_right (T.split hd)).trans <|
    sep_assoc.2.trans <| (sep_mono_left wand_elim_left).trans <| except0_frame_right.trans <| except0_mono <|
      sep_right_comm.1.trans <| (sep_mono_left T.join).trans <| by
        iintro ⟨⟨%d, HW⟩, HG⟩
        isplitl [HW]
        · iexact HW
        · iapply (pure_imp_elim (PROP := PROP) d)
          iexact HG
  frame_right := wand_intro <| sep_right_comm.1.trans <| (sep_mono_left wand_elim_left).trans <|
    except0_frame_right.trans (except0_mono sep_assoc.1)

theorem ztrick {X Y Z : PROP} [Persistent Z] [Absorbing Z] (h : iprop(X ∗ Y) ⊢ Z) :
    iprop(X ∗ Y) ⊢ iprop(◇ (Y ∗ Z)) :=
  (and_intro h .rfl).trans <| persistent_and_affinely_sep_left_mp.trans <| (sep_mono_left affinely_elim).trans <|
    sep_assoc.2.trans <| (sep_mono_left sep_elim_left).trans <| sep_symm.trans except0_intro
end

section
variable {PROP : Type _} [Sbi PROP]

theorem tk_keep (T : TW PROP) (E E' : CoPset) (Pi : SiProp) (R : PROP) :
    iprop(tf T E E' iprop(<si_pure> Pi) ∧ (<si_pure> Pi -∗ tf T E E R)) ⊢ tf T E E R :=
  wand_intro <| (and_intro ((sep_mono_left and_elim_l).trans (wand_elim_left.trans (except0_mono sep_elim_right)))
    (sep_mono_left and_elim_r)).trans <| (and_mono .rfl except0_intro).trans <| except0_and.2.trans <|
    (except0_mono <| persistent_and_affinely_sep_left_mp.trans <| (sep_mono_left affinely_elim).trans <|
      sep_assoc.2.trans <| (sep_mono_left wand_elim_right).trans wand_elim_left).trans except0_idem.1

theorem tk_later (T : TW PROP) (E : CoPset) (Pi : SiProp) :
    iprop(▷ tf T E E iprop(<si_pure> Pi)) ⊢ tf T E E iprop(▷ ◇ <si_pure> Pi) :=
  wand_intro <| ztrick <| (sep_mono_right later_intro).trans <| later_sep.2.trans <|
    later_mono (wand_elim_left.trans (except0_mono sep_elim_right))

theorem tk_all1 (T : TW PROP) (E : CoPset) (Ψ : SiProp → Prop) :
    iprop((∀ q, ⌜Ψ q⌝ → tf T E E iprop(<si_pure> q)) ∗ T.W E) ⊢ iprop(∀ q, ◇ (⌜Ψ q⌝ → <si_pure> q)) :=
  forall_intro fun q => by
    by_cases hq : Ψ q
    · have h1 : iprop(∀ q, ⌜Ψ q⌝ → tf T E E iprop(<si_pure> q)) ⊢ tf T E E iprop(<si_pure> q) :=
        (forall_elim (Ψ := fun q => iprop(⌜Ψ q⌝ → tf T E E iprop(<si_pure> q))) q).trans (pure_imp_elim hq)
      have h2 : iprop(tf T E E iprop(<si_pure> q) ∗ T.W E) ⊢ iprop(◇ (⌜Ψ q⌝ → <si_pure> q)) :=
        wand_elim_left.trans (except0_mono (sep_elim_right.trans (imp_intro and_elim_l)))
      exact (sep_mono_left h1).trans h2
    · exact true_intro.trans <| except0_intro.trans <| except0_mono <|
        imp_intro (pure_elim_right fun h => (hq h).elim)

theorem tk_all (T : TW PROP) (E : CoPset) (Ψ : SiProp → Prop) :
    iprop(∀ q, ⌜Ψ q⌝ → tf T E E iprop(<si_pure> q)) ⊢ tf T E E iprop(<si_pure> (sForall Ψ)) :=
  wand_intro <| (ztrick (Z := iprop(◇ <si_pure> (sForall Ψ))) <| (tk_all1 T E Ψ).trans <|
    except0_forall.2.trans (except0_mono Sbi.siPure_sForall_mpr)).trans <|
    (except0_mono ((sep_mono_left except0_intro).trans except0_sep.2)).trans except0_idem.1

theorem tFS (T : TW PROP) : @BIFUpdateSbi PROP _ (tFupd T) _ :=
  @BIFUpdateSbi.mk PROP _ (tFupd T) _ (fun E' Pi R => tk_keep T _ E' Pi R) (fun E Pi => tk_later T E Pi)
    (fun E Ψ => tk_all T E Ψ)
end


/-! TK: exact ownership of mask tokens: a set S with a validity flag, op = union, valid only if
disjoint; unit (empty, True); equality order, so `UPred TK` is not affine. -/
structure TK where
  S : CoPset
  ok : Prop

def TK.op (x y : TK) : TK := ⟨x.S ∪ y.S, x.ok ∧ y.ok ∧ x.S ## y.S⟩
abbrev tku : TK := ⟨∅, True⟩

theorem dj0 {A : CoPset} : (∅ : CoPset) ## A := fun _ ⟨h, _⟩ => CoPset.mem_empty h

theorem tk_unit_op (x : TK) : TK.op tku x = x := by
  cases x with
  | mk S ok =>
    simp only [TK.op]
    rw [union_empty_left]
    congr 1
    exact propext ⟨fun h => h.2.1, fun h => ⟨trivial, h, dj0⟩⟩

theorem tk_assoc (x y z : TK) : TK.op x (TK.op y z) = TK.op (TK.op x y) z := by
  cases x; cases y; cases z
  simp only [TK.op]
  rw [union_assoc]
  congr 1
  apply propext
  constructor
  · rintro ⟨ha, ⟨hb, hc, hbc⟩, habc⟩
    exact ⟨⟨ha, hb, fun p ⟨h1, h2⟩ => habc p ⟨h1, mem_union.2 (.inl h2)⟩⟩, hc,
      fun p ⟨h1, h2⟩ => (mem_union.1 h1).elim (fun h => habc p ⟨h, mem_union.2 (.inr h2)⟩) (fun h => hbc p ⟨h, h2⟩)⟩
  · rintro ⟨⟨ha, hb, hab⟩, hc, habc⟩
    exact ⟨ha, ⟨hb, hc, fun p ⟨h1, h2⟩ => habc p ⟨mem_union.2 (.inr h1), h2⟩⟩,
      fun p ⟨h1, h2⟩ => (mem_union.1 h2).elim (fun h => hab p ⟨h1, h⟩) (fun h => habc p ⟨mem_union.2 (.inl h1), h⟩)⟩

theorem tk_comm (x y : TK) : TK.op x y = TK.op y x := by
  cases x; cases y
  simp only [TK.op]
  rw [union_comm]
  congr 1
  exact propext ⟨fun ⟨a, b, d⟩ => ⟨b, a, fun p ⟨h1, h2⟩ => d p ⟨h2, h1⟩⟩,
    fun ⟨a, b, d⟩ => ⟨b, a, fun p ⟨h1, h2⟩ => d p ⟨h2, h1⟩⟩⟩

instance : OFE TK := OFE.ofDiscrete TK
instance : OFE.Discrete TK := ⟨id⟩

instance tkORA : ORA TK := ORA.ofDiscreteORAData {
  pcore := fun _ => some tku
  op := TK.op
  Valid := fun x => x.ok
  Order := Eq
  assoc := by intro x y z; exact tk_assoc x y z
  comm := by intro x y; exact tk_comm x y
  pcore_op_left := by intro x cx h; cases h; exact tk_unit_op x
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y h; exact h.1
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := by intro x y h hv; cases h; exact hv
  pcore_mono := by intro x y cx h1 h2; exact ⟨tku, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨tku, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact (tk_unit_op y).symm
  increasing_closed := by intro x y _ h; cases h; assumption }

instance : OrderRefl TK := ⟨fun x => show x = x from rfl⟩

instance tkUORA : UORA TK where
  unit := tku
  unit_valid := trivial
  unit_left_id := tk_unit_op _
  pcore_unit := rfl

/-- Token family in `UPred TK`: own exactly the mask E. -/
def tkW : TW (UPred TK) where
  W E := UPred.ownM (⟨E, True⟩ : TK)
  split {A B} d := fun _ x h => ⟨⟨A, True⟩, ⟨B, True⟩, (show TK.op _ _ = _ from
      ((congrArg (TK.mk (A ∪ B)) (propext ⟨fun _ => trivial, fun _ => ⟨trivial, trivial, d⟩⟩)).trans h)),
    ORA.ordN_refl _, ORA.ordN_refl _⟩
  join {A B} := fun _ x ⟨x1, x2, hx, h1, h2⟩ => by
    have e1 : (⟨A, True⟩ : TK) = x1 := h1
    have e2 : (⟨B, True⟩ : TK) = x2 := h2
    have ex : TK.op x1 x2 = x.val := hx
    subst e1 e2
    have hv : x.val.ok := x.property
    rw [← ex] at hv
    refine ⟨hv.2.2, ?_⟩
    show (⟨A ∪ B, True⟩ : TK) = x.val
    rw [← ex]
    exact congrArg (TK.mk (A ∪ B)) (propext ⟨fun _ => ⟨trivial, trivial, hv.2.2⟩, fun _ => trivial⟩)

abbrev tkF : BIFUpdate (UPred TK) := tFupd tkW
theorem tkFS : @BIFUpdateSbi (UPred TK) _ tkF _ := tFS tkW

theorem top_ne_empty (h : (⊤ : CoPset) = ∅) : False := by
  have h1 : Pos.xH ∈ (⊤ : CoPset) := rfl
  rw [h] at h1
  exact CoPset.mem_empty h1

/-- Owning all tokens does not let one end with none (at step 1). -/
theorem tk_bad (h : tkW.W ⊤ ⊢ iprop(◇ tkW.W ∅)) : False := by
  rcases h 1 ⟨⟨⊤, True⟩, trivial⟩ (ORA.ordN_refl _) with h | h
  · exact h
  · exact top_ne_empty (congrArg TK.S (show (⟨∅, True⟩ : TK) = ⟨⊤, True⟩ from h)).symm

theorem tk_open : tkW.W ⊤ ⊢ tf tkW ∅ ⊤ iprop(emp) :=
  wand_intro <| tkW.join.trans <| and_elim_r.trans <| (wq tkW union_empty_right).trans <| sep_emp.2.trans except0_intro

theorem tk_close (h : tkW.W ⊤ ⊢ tf tkW ∅ ∅ iprop(emp)) : False :=
  tk_bad <| ((wq tkW union_empty_right.symm).trans (tkW.split (fun _ ⟨_, h2⟩ => CoPset.mem_empty h2))).trans <|
    (sep_mono_left h).trans <| wand_elim_left.trans (except0_mono sep_emp.1)

end T2c0

namespace T2c0
open Iris Iris.BI Iris.Std Iris.OFE

/-! TP: step-indexed predicates on the one-point compactification Option Nat (none = the point at
infinity; a set containing none is open iff it contains a tail of the some m), pointwise SiProp
connectives, persistently = interior. An affine Sbi in which persistently does not commute with ∀. -/
def TP : Type := Option Nat → SiProp

instance : COFE TP := inferInstanceAs (COFE (Option Nat → SiProp))

def isOpen (U : Option Nat → Prop) : Prop := U none → ∃ N, ∀ m, N ≤ m → U (some m)

theorem open_inter {U V : Option Nat → Prop} (hU : isOpen U) (hV : isOpen V) : isOpen (fun y => U y ∧ V y) :=
  fun ⟨h1, h2⟩ => by
    obtain ⟨N1, h1⟩ := hU h1
    obtain ⟨N2, h2⟩ := hV h2
    exact ⟨N1 + N2, fun m hm => ⟨h1 m (by omega), h2 m (by omega)⟩⟩

theorem open_univ : isOpen (fun _ => True) := fun _ => ⟨0, fun _ _ => trivial⟩

def tint (P : TP) : TP := fun x => ⟨fun n => ∃ U, isOpen U ∧ U x ∧ ∀ y, U y → (P y).holds n,
  fun ⟨U, ho, hx, h⟩ hle => ⟨U, ho, hx, fun y hy => (P y).closed (h y hy) hle⟩⟩

instance tpBase : BIBase TP where
  Entails P Q := ∀ x, P x ⊢ Q x
  emp := fun _ => iprop(emp)
  pure φ := fun _ => iprop(⌜φ⌝)
  and P Q := fun x => iprop(P x ∧ Q x)
  or P Q := fun x => iprop(P x ∨ Q x)
  imp P Q := fun x => iprop(P x → Q x)
  sForall Ψ := fun x => sForall (fun p : SiProp => ∃ P : TP, Ψ P ∧ p = P x)
  sExists Ψ := fun x => sExists (fun p : SiProp => ∃ P : TP, Ψ P ∧ p = P x)
  sep P Q := fun x => iprop(P x ∗ Q x)
  wand P Q := fun x => iprop(P x -∗ Q x)
  persistently := tint
  later P := fun x => iprop(▷ P x)

instance tpBI : BI TP where
  entails_refl := fun _ => .rfl
  entails_trans h1 h2 := fun x => (h1 x).trans (h2 x)
  equiv_iff := ⟨fun h => h ▸ ⟨fun _ => .rfl, fun _ => .rfl⟩,
    fun ⟨h1, h2⟩ => funext fun x => BI.equiv_iff.2 ⟨h1 x, h2 x⟩⟩
  and_ne := ⟨fun _ _ _ hP _ _ hQ x => (BI.and_ne (PROP := SiProp)).ne (hP x) (hQ x)⟩
  or_ne := ⟨fun _ _ _ hP _ _ hQ x => (BI.or_ne (PROP := SiProp)).ne (hP x) (hQ x)⟩
  imp_ne := ⟨fun _ _ _ hP _ _ hQ x => (BI.imp_ne (PROP := SiProp)).ne (hP x) (hQ x)⟩
  sep_ne := ⟨fun _ _ _ hP _ _ hQ x => (BI.sep_ne (PROP := SiProp)).ne (hP x) (hQ x)⟩
  wand_ne := ⟨fun _ _ _ hP _ _ hQ x => (BI.wand_ne (PROP := SiProp)).ne (hP x) (hQ x)⟩
  persistently_ne := ⟨fun _ P Q h x _ hm => ⟨fun ⟨U, ho, hx, hU⟩ => ⟨U, ho, hx, fun y hy => ((h y) hm).mp (hU y hy)⟩,
    fun ⟨U, ho, hx, hU⟩ => ⟨U, ho, hx, fun y hy => ((h y) hm).mpr (hU y hy)⟩⟩⟩
  later_ne := ⟨fun _ _ _ h x => (BI.later_ne (PROP := SiProp)).ne (h x)⟩
  sForall_ne {_ P₁ P₂} H x := BI.sForall_ne (PROP := SiProp)
    ⟨fun _ ⟨P, hP, e⟩ => let ⟨Q, hQ, hPQ⟩ := H.1 P hP; ⟨Q x, ⟨Q, hQ, rfl⟩, e ▸ hPQ x⟩,
     fun _ ⟨Q, hQ, e⟩ => let ⟨P, hP, hPQ⟩ := H.2 Q hQ; ⟨P x, ⟨P, hP, rfl⟩, e ▸ hPQ x⟩⟩
  sExists_ne {_ P₁ P₂} H x := BI.sExists_ne (PROP := SiProp)
    ⟨fun _ ⟨P, hP, e⟩ => let ⟨Q, hQ, hPQ⟩ := H.1 P hP; ⟨Q x, ⟨Q, hQ, rfl⟩, e ▸ hPQ x⟩,
     fun _ ⟨Q, hQ, e⟩ => let ⟨P, hP, hPQ⟩ := H.2 Q hQ; ⟨P x, ⟨P, hP, rfl⟩, e ▸ hPQ x⟩⟩
  pure_intro h := fun _ => pure_intro h
  pure_elim' h := fun x => pure_elim' fun hφ => h hφ x
  and_elim_l := fun _ => and_elim_l
  and_elim_r := fun _ => and_elim_r
  and_intro h1 h2 := fun x => and_intro (h1 x) (h2 x)
  or_intro_l := fun _ => or_intro_l
  or_intro_r := fun _ => or_intro_r
  or_elim h1 h2 := fun x => or_elim (h1 x) (h2 x)
  imp_intro h := fun x => imp_intro (h x)
  imp_elim h := fun x => imp_elim (h x)
  sForall_intro h := fun x => sForall_intro fun _ ⟨P, hP, e⟩ => e ▸ h P hP x
  sForall_elim hp := fun _ => sForall_elim ⟨_, hp, rfl⟩
  sExists_intro hp := fun _ => sExists_intro ⟨_, hp, rfl⟩
  sExists_elim h := fun x => sExists_elim fun _ ⟨P, hP, e⟩ => e ▸ h P hP x
  sep_mono h1 h2 := fun x => sep_mono (h1 x) (h2 x)
  emp_sep := ⟨fun _ => emp_sep.1, fun _ => emp_sep.2⟩
  sep_symm := fun _ => sep_symm
  sep_assoc_l := fun _ => BI.sep_assoc_l
  wand_intro h := fun x => wand_intro (h x)
  wand_elim h := fun x => wand_elim (h x)
  persistently_mono h := fun x n ⟨U, ho, hx, hU⟩ => ⟨U, ho, hx, fun y hy => h y n (hU y hy)⟩
  persistently_idem_2 := fun x n ⟨U, ho, hx, hU⟩ => ⟨U, ho, hx, fun y hy => ⟨U, ho, hy, hU⟩⟩
  persistently_emp_2 := fun x n h => ⟨fun _ => True, open_univ, trivial, fun _ _ => h⟩
  persistently_and_2 := fun x n ⟨⟨U, ho, hx, hU⟩, ⟨V, ho', hx', hV⟩⟩ =>
    ⟨fun y => U y ∧ V y, open_inter ho ho', ⟨hx, hx'⟩, fun y hy => ⟨hU y hy.1, hV y hy.2⟩⟩
  persistently_absorb_l := fun _ _ h => h.1
  persistently_and_l := fun x _ ⟨⟨_, _, hx, hU⟩, hq⟩ => ⟨hU x hx, hq⟩
  later_mono h := fun x => later_mono (h x)
  later_intro := fun _ => later_intro
  later_sForall_2 {Φ} := fun x => by
    refine (?_ : _ ⊢ iprop(∀ q : SiProp, ⌜∃ P : TP, Φ P ∧ q = P x⌝ → ▷ q)).trans BI.later_sForall_2
    refine forall_intro fun q => imp_intro (pure_elim_right fun ⟨P, hP, e⟩ => ?_)
    subst e
    exact (sForall_elim ⟨_, ⟨P, rfl⟩, rfl⟩).trans (pure_imp_elim hP)
  later_sExists_false {Φ} := fun x => by
    refine (BI.later_sExists_false (PROP := SiProp)).trans (or_mono .rfl ?_)
    refine exists_elim fun q => pure_elim_left fun ⟨P, hP, e⟩ => ?_
    subst e
    exact (and_intro (pure_intro hP) .rfl).trans (sExists_intro ⟨_, ⟨P, rfl⟩, rfl⟩)
  later_sep := ⟨fun _ => later_sep.1, fun _ => later_sep.2⟩
  later_persistently := ⟨fun x n h => by
      cases n with
      | zero => exact ⟨fun _ => True, open_univ, trivial, fun _ _ => trivial⟩
      | succ n => exact h,
    fun x n h => by
      cases n with
      | zero => trivial
      | succ n => exact h⟩
  later_false_em := fun _ => later_false_em


theorem exMax (p : Nat → Prop) : ∀ n, (∃ k, k ≤ n ∧ p k) → ∃ m, m ≤ n ∧ p m ∧ ∀ k, k ≤ n → p k → k ≤ m
  | 0, ⟨k, hk, hp⟩ => ⟨0, Nat.le_refl _, (Nat.le_zero.1 hk) ▸ hp, fun _ hk _ => hk⟩
  | n + 1, ⟨k, hk, hpk⟩ => by
    by_cases hn : p (n + 1)
    · exact ⟨n + 1, Nat.le_refl _, hn, fun _ hk _ => hk⟩
    · have hk' : k ≤ n := by
        rcases Nat.lt_or_ge k (n + 1) with h | h
        · omega
        · exact absurd (show k = n + 1 by omega ▸ hpk) hn
      obtain ⟨m, hm, hpm, hmax⟩ := exMax p n ⟨k, hk', hpk⟩
      refine ⟨m, by omega, hpm, fun k' hk' hp' => ?_⟩
      rcases Nat.lt_or_ge k' (n + 1) with h | h
      · exact hmax k' (by omega) hp'
      · exact absurd (show k' = n + 1 by omega ▸ hp') hn

instance : SiPure TP := ⟨fun Pi _ => Pi⟩
instance : SiEmpValid TP := ⟨fun P => ⟨fun n => ∀ x, (P x).holds n, fun h hle x => (P x).closed (h x) hle⟩⟩

instance tpSbi : Sbi TP where
  siPure_ne := ⟨fun _ _ _ h _ => h⟩
  siEmpValid_ne := ⟨fun _ _ _ h _ hm => ⟨fun hp x => ((h x) hm).mp (hp x), fun hq x => ((h x) hm).mpr (hq x)⟩⟩
  siPure_mono H := fun _ => H
  siEmpValid_mono H := fun n hp x => H x n (hp x)
  siEmpValid_siPure := ⟨fun _ h => h none, fun _ h _ => h⟩
  siPure_siEmpValid := fun _ _ h => ⟨fun _ => True, open_univ, trivial, fun y _ => h y⟩
  siPure_imp_mpr := fun _ => .rfl
  siPure_sForall_mpr {Ψ} := fun x => sForall_intro fun q hq =>
    (sForall_elim ⟨_, ⟨q, rfl⟩, rfl⟩).trans (pure_imp_elim hq)
  persistently_imp_siPure {Pi Q} := fun x n h => by
    by_cases hp : ∃ k, k ≤ n ∧ Pi.holds k
    · obtain ⟨m, hm, hpm, hmax⟩ := exMax _ n hp
      obtain ⟨U, ho, hx, hU⟩ := h m hm hpm
      exact ⟨U, ho, hx, fun y hy k hk hPk => (Q y).closed (hU y hy) (hmax k (Nat.le_trans hk (Nat.le_refl _)) hPk)⟩
    · exact ⟨fun _ => True, open_univ, trivial, fun y _ k hk hPk => absurd ⟨k, hk, hPk⟩ hp⟩
  siPure_later := ⟨fun _ => .rfl, fun _ => .rfl⟩
  siPure_absorbing _ := ⟨fun _ _ h => h.2⟩
  siEmpValid_later_mp := fun n h => by
    cases n with
    | zero => trivial
    | succ n => exact fun x => h x
  siEmpValid_affinely_mpr := fun _ h x => ⟨trivial, h x⟩
  prop_ext_siEmpValid := fun _ h x _ hm => ⟨fun hp => (h x).1 _ hm hp, fun hq => (h x).2 _ hm hq⟩

/-- Holds exactly at the point at infinity. -/
def cP : TP := fun x => iprop(⌜x = none⌝)
def cQ (m : Nat) : TP := fun y => iprop(⌜y ≠ some m⌝)

instance : Affine cP := ⟨fun _ _ _ => trivial⟩

theorem cQ_open (m : Nat) : isOpen (fun z => z ≠ some m) :=
  fun _ => ⟨m + 1, fun k hk h => by injection h; omega⟩

theorem cp_none : (coreP cP none).holds 0 := by
  have H : cP ⊢ coreP cP := wand_entails (coreP_intro (PROP := TP) (P := cP))
  exact H none 0 rfl

/-- coreP cP is the intersection of the open sets around none: it fails at every some m. -/
theorem cp_some (m : Nat) : ¬ (coreP cP (some m)).holds 0 := fun h => by
  have h1 := h _ ⟨_, ⟨cQ m, rfl⟩, rfl⟩
  have h2 := h1 0 (Nat.le_refl _) ⟨trivial, fun y n' _ hq => ⟨fun z => z ≠ some m, cQ_open m, hq, fun _ hz => hz⟩⟩
  exact h2 0 (Nat.le_refl _) ⟨trivial, fun y n' _ (hy : y = none) => hy ▸ (fun h => nomatch h)⟩ rfl

theorem cp_bad (H : (tint (coreP cP) none).holds 0) : False := by
  obtain ⟨U, ho, hU, hall⟩ := H
  obtain ⟨N, hN⟩ := ho hU
  exact cp_some N (hall _ (hN N (Nat.le_refl _)))

end T2c0

open Iris Iris.BI Iris.Std T2c0

-- `Iris.fupd_plain_forall_2` idx 5: necessary (at Type: non-affine UPred ND with the one-way step update s to c0 or c1 (cannot drop to the unit), fupd zf (bupd except0), alpha = Bool, Phi b holds at e and c_b (plain, not absorbing), E = empty)
theorem t2c0_1 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP] {α : Type}
    {E : CoPset} {Φ : α → PROP} [∀ (a : α), Iris.BI.Plain (Φ a)],
    iprop(∀ a, |={E}=> Φ a) ⊢ iprop(|={E}=> ∀ a, Φ a)) := fun h =>
  nd_bad1 <| nd_lhs1.trans <| (@h (UPred ND) _ ndF ndFS Bool ∅ ndP _).trans zO
-- `Iris.fupd_plain_forall` idx 5: necessary (at Type: UPred ND with the one-way step update, fupd zf (bupd except0), alpha = Bool, Phi b holds at e and c_b, E1 = E2 = empty)
theorem t2c0_2 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP] {α : Type}
    {E1 E2 : CoPset} {Φ : α → PROP} [inst_4 : ∀ (a : α), Iris.BI.Plain (Φ a)], E2 ⊆ E1 →
    (iprop(|={E1,E2}=> ∀ a, Φ a) ⊣⊢ iprop(∀ a, |={E1,E2}=> Φ a))) := fun h =>
  nd_bad1 <| nd_lhs1.trans <| (@h (UPred ND) _ ndF ndFS Bool ∅ ∅ ndP _ LawfulSet.subset_refl).2.trans zO
-- `Iris.fupd_plain_forall'` idx 5: necessary (at Type: UPred ND with the one-way step update, alpha = Bool, Phi b holds at e and c_b, E = empty)
theorem t2c0_3 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP] {α : Type}
    {E : CoPset} {Φ : α → PROP} [∀ (a : α), Iris.BI.Plain (Φ a)],
    (iprop(|={E}=> ∀ a, Φ a) ⊣⊢ iprop(∀ a, |={E}=> Φ a))) := fun h =>
  nd_bad1 <| nd_lhs1.trans <| (@h (UPred ND) _ ndF ndFS Bool ∅ ndP _).2.trans zO
-- `Iris.step_fupd_plain_forall` idx 5: necessary (at Type: UPred ND with the one-way step update, alpha = Bool, Phi b holds at e and c_b, Eo = Ei = empty, step 2)
theorem t2c0_4 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIFUpdate PROP] [Iris.BIFUpdateSbi PROP] {α : Type}
    {Eo Ei : CoPset} {Φ : α → PROP} [∀ (a : α), Iris.BI.Plain (Φ a)], Ei ⊆ Eo →
    (iprop(|={Eo}[Ei]▷=> ∀ a, Φ a) ⊣⊢ iprop(∀ a, |={Eo}[Ei]▷=> Φ a))) := fun h =>
  nd_bad2 <| nd_lhs2.trans <| (@h (UPred ND) _ ndF ndFS Bool ∅ ∅ ndP _ LawfulSet.subset_refl).2.trans
    (zO.trans (ndL.mono (later_mono zO)))
-- `Iris.fupd_plain_mask` idx 4: necessary (non-affine UPred TK, TK = exact mask tokens (set, disjointness validity, equality order), fupd E1 E2 P := W E1 -∗ ◇ (W E2 ∗ P) (lawful, BIFUpdateSbi), E = empty, E' = top, P = emp: W top gives |={empty,top}=> emp but not |={empty}=> emp)
theorem t2c0_5 : ¬ drop0% Iris.fupd_plain_mask 4 := fun h =>
  tk_close <| tk_open.trans (@h (UPred TK) _ tkF tkFS ∅ ⊤ iprop(emp) _)
-- `Iris.fupd_keep_plain_sep` idx 4: necessary (UPred TK with the token fupd, E = empty, E' = top, P = R = emp, the wand held by W top)
theorem t2c0_6 : ¬ drop0% Iris.fupd_keep_plain_sep 4 := fun h =>
  tk_close <| ((emp_sep.2.trans (sep_mono (@h (UPred TK) _ tkF tkFS ∅ ⊤ iprop(emp) iprop(emp) _)
    (wand_intro (sep_emp.1.trans tk_open)))).trans wand_elim_left).trans <|
    sep_emp.2.trans (wand_elim_left.trans (BIFUpdate.mono (PROP := UPred TK) (self := tkF) sep_emp.1 |>.trans .rfl))
-- `Iris.fupd_plain_later` idx 4: necessary (non-affine UPred ND with a step-dependent one-way update (s to c0 or c1 only at steps up to 1), fupd zf (bupd except0), E = empty, P holds at e and c0 (plain, not absorbing), at s, step 2)
theorem t2c0_7 : ¬ drop0% Iris.fupd_plain_later 4 := fun h =>
  nd2_bad <| nd2_lhs.trans <| (@h (UPred ND) _ ndF2 ndFS2 ∅ (ndP false) _).trans zO
-- `Iris.fupd_plain_laterN` idx 4: necessary (UPred ND with the step-dependent one-way update, n = 1, E = empty, P holds at e and c0, at s, step 2)
theorem t2c0_8 : ¬ drop0% Iris.fupd_plain_laterN 4 := fun h =>
  nd2_bad <| nd2_lhs.trans <| (@h (UPred ND) _ ndF2 ndFS2 ∅ 1 (ndP false) _).trans zO
-- `Iris.step_fupd_plain` idx 4: necessary (UPred ND with the step-dependent one-way update, E1 = E2 = empty, P holds at e and c0, at s, step 2)
theorem t2c0_9 : ¬ drop0% Iris.step_fupd_plain 4 := fun h =>
  nd2_bad <| (zM (nd2_lhs.trans ndL2.intro)).trans <| (@h (UPred ND) _ ndF2 ndFS2 ∅ ∅ (ndP false) _).trans zO
-- `Iris.step_fupdN_plain` idx 4: necessary (UPred ND with the step-dependent one-way update, n = 1, E1 = E2 = empty, P holds at e and c0, at s, step 2)
theorem t2c0_10 : ¬ drop0% Iris.step_fupdN_plain 4 := fun h =>
  nd2_bad <| (zM (nd2_lhs.trans ndL2.intro)).trans <| (@h (UPred ND) _ ndF2 ndFS2 ∅ ∅ 1 (ndP false) _).trans zO
-- `Iris.fupd_plain_later` idx 7: necessary (affine UPred NDA with a step-dependent one-way update (s to c0 or c1 only at steps up to 1), fupd zf (bupd except0), E = empty, P = own c0 (not plain), at s, step 2)
theorem t2c0_11 : ¬ drop0% Iris.fupd_plain_later 7 := fun h =>
  nda_bad <| nda_lhs.trans <| (@h (UPred NDA) _ ndaF ndaFS _ ∅ (UPred.ownM NDA.c0)).trans zO
-- `Iris.fupd_plain_laterN` idx 8: necessary (affine UPred NDA with the step-dependent one-way update, n = 1, E = empty, P = own c0, at s, step 2)
theorem t2c0_12 : ¬ drop0% Iris.fupd_plain_laterN 8 := fun h =>
  nda_bad <| nda_lhs.trans <| (@h (UPred NDA) _ ndaF ndaFS _ ∅ 1 (UPred.ownM NDA.c0)).trans zO
-- `Iris.step_fupd_plain` idx 8: necessary (affine UPred NDA with the step-dependent one-way update, E1 = E2 = empty, P = own c0, at s, step 2)
theorem t2c0_13 : ¬ drop0% Iris.step_fupd_plain 8 := fun h =>
  nda_bad <| (zM (nda_lhs.trans ndaL.intro)).trans <| (@h (UPred NDA) _ ndaF ndaFS _ ∅ ∅ (UPred.ownM NDA.c0)).trans zO
-- `Iris.step_fupdN_plain` idx 9: necessary (affine UPred NDA with the step-dependent one-way update, n = 1, E1 = E2 = empty, P = own c0, at s, step 2)
theorem t2c0_14 : ¬ drop0% Iris.step_fupdN_plain 9 := fun h =>
  nda_bad <| (zM (nda_lhs.trans ndaL.intro)).trans <| (@h (UPred NDA) _ ndaF ndaFS _ ∅ ∅ 1 (UPred.ownM NDA.c0)).trans zO
-- `Iris.bupd_plain_forall` idx 7: necessary (at Type: non-affine UPred ND with the one-way step update ndU (lawful, BIBUpdateSbi; s moves to c0 or c1, never to the unit), A = Bool, Phi b holds at e and c_b (plain, not absorbing), at s)
theorem t2c0_15 : ¬ (∀ {PROP : Type} [inst : Iris.Sbi PROP] [inst_1 : Iris.BIUpdate PROP] [Iris.BIBUpdateSbi PROP] {A : Type}
    (Φ : A → PROP) [∀ (x : A), Iris.BI.Plain (Φ x)], (iprop(|==> ∀ x, Φ x) ⊣⊢ iprop(∀ x, |==> Φ x))) := fun h =>
  nd_bu_bad <| (forall_intro fun b => nd_bu b).trans (@h (UPred ND) _ ndBU ndBS Bool ndP _).2
-- `Iris.BIFUpdateSbi.fupd_siPure_sForall_2` idx 4: necessary (class field: the BI instance is independent of the Sbi; carrier SiProp (renamed RSi) with the reversed-chain BI revBI (lawful), fupd zf except0 over it, Sbi = SiProp's own; Psi empty: the left side is the top of revBI, the right side is si_pure True = the bottom of revBI)
theorem t2c0_16 : ¬ drop0% Iris.BIFUpdateSbi.fupd_siPure_sForall_2 4 := fun h => by
  have H := @h RSi revBI rF rSbi ∅ (fun _ => False)
  obtain ⟨p, ⟨q0, hq⟩, hp⟩ := H 0 ⟨fun hall => hall 0 ⟨id, .inr (fun _ h => h.elim)⟩ rfl, ⟨id, .inr (fun _ h => h.elim)⟩⟩
  subst hq
  exact hp.1 (fun _ _ h => h)
-- `Iris.coreP_persistent` idx 2: necessary (Sbi TP of step-indexed predicates on the one-point compactification of Nat, persistently = interior, no BIPersistentlyForall; P holds only at the point at infinity: coreP P holds there but fails at every finite point (open cofinite sets avoid it), so it is not persistent)
theorem t2c0_17 : ¬ drop0% Iris.coreP_persistent 2 := fun h =>
  cp_bad ((@h TP tpSbi cP).persistent none 0 cp_none)
-- `Iris.coreP_entails` idx 2: necessary (Sbi TP, P holds only at infinity, Q = coreP P: the left side holds by affinely_elim, P does not entail persistently coreP P)
theorem t2c0_18 : ¬ drop0% Iris.coreP_entails 2 := fun h =>
  cp_bad (((@h TP tpSbi cP (coreP cP)).1 affinely_elim) none 0 rfl)
-- `Iris.coreP_entails'` idx 2: necessary (Sbi TP, P holds only at infinity (affine), Q = coreP P: the left side is reflexivity, P does not entail the intuitionistic coreP P)
theorem t2c0_19 : ¬ drop0% Iris.coreP_entails' 2 := fun h =>
  cp_bad (((@h TP tpSbi cP (coreP cP) _).1 .rfl) none 0 rfl).2
