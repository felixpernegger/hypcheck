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

namespace T1c4
open Iris Iris.BI Iris.Std Iris.ProgramLogic COFE Auth

/-- Language on Bool with no steps; `true` is the only value (from W7c3). -/
@[instance_reducible] def nLang : Language Bool Unit Unit Unit where
  primStep := fun _ _ _ => False
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by intro e σ obs e' σ' eₜ h; exact h.elim
attribute [instance] nLang

abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare
noncomputable abbrev GMF : OFunctorPre := constOF (HeapView Nat (Agree (DiscreteO Bool)) TM)

/-- Closed-proofs GF (slots 0–3) with a ghost map Nat → Bool in slot 4 and cancelable invariants above. -/
noncomputable def GY : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF⟩
  | 1  => ⟨constOF CoPsetDisjL⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3  => ⟨AuthURF (constOF Credit)⟩
  | 4  => ⟨GMF⟩
  | _  => ⟨CInvF⟩

instance gyWsat : WsatGpreS GY where
  inv := { τ := 0, transp := by unfold GY; rfl }
  enabled := { τ := 1, transp := by unfold GY; rfl }
  disabled := { τ := 2, transp := by unfold GY; rfl }
instance gyLc : LcGpreS GY where
  lc_elem := { τ := 3, transp := by unfold GY; rfl }
instance gyInv : InvGpreS GY where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance
instance gyGM : GhostMapG GY Nat Bool TM := ⟨{ τ := 4, transp := by unfold GY; rfl }⟩
instance gyCInv : CInvG GY := ⟨{ τ := 5, transp := by unfold GY; rfl }⟩
@[reducible] def tiY (γ : GName) : TpinvGS GY Bool TM := { toGhostMapG := inferInstance, tp_name := γ }

/-- IrisGS over `nLang` with stateInterp True. -/
@[reducible] noncomputable instance igY {L : Language Bool Unit Unit Unit} [x : InvGS_gen .hasNoLC GY] : IrisGS_gen .hasNoLC Bool GY :=
  { invGS := x, stateInterp := fun _ _ _ _ => iprop(True), numLatersPerStep := fun _ => 0,
    forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }

theorem fupd_falseY (E1 E2 : CoPset) (H : ∀ [InvGS_gen .hasNoLC GY], ⊢ (iprop(|={E1,E2}=> ⌜False⌝) : IProp GY)) : False :=
  pure_soundness (PROP := IProp GY)
    (fupd_soundness .hasNoLC 0 (E1 := E1) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))

/-- The trivially true abstract wp. -/
noncomputable abbrev wpT : AbstractWP Bool Unit GY := fun _ _ _ => iprop(True)
theorem lwpT_false (h : ∀ [InvGS_gen .hasNoLC GY], @LawfulAbstractWP Bool Unit Unit Unit nLang GY .hasNoLC igY wpT) : False :=
  fupd_falseY ⊤ ⊤ fun {_} => true_intro.trans (h.wp_value (v := ()) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝))).mp
theorem iaoT [InvGS_gen .hasNoLC GY] : @InvOpenAbstractWP Bool Unit Unit Unit nLang GY .hasNoLC igY wpT :=
  @InvOpenAbstractWP.mk Bool Unit Unit Unit nLang GY .hasNoLC igY wpT (fun _ _ _ _ _ => true_intro)


/-- `[true]` is adequate in `nLang`. -/
theorem n_step {ρ o ρ'} (hs : @Language.Step Bool Unit Unit Unit nLang ρ o ρ') : False := by
  cases hs with
  | atomic H => exact H
theorem n_rtg {C C'} (h : FromMathlib.Relation.ReflTransGen (@Language.ErasedStep Bool Unit Unit Unit nLang) C C') :
    C = C' := by
  induction h with
  | refl => rfl
  | tail _ hs ih => obtain ⟨_, hs⟩ := hs; exact (n_step hs).elim
theorem n_adeq (φ : Unit → Unit → Prop) (hφ : φ () ()) : @adequate Bool Unit Unit Unit nLang .NotStuck true () φ :=
  ⟨fun t2 σ2 v2 hr => by
      have := n_rtg hr; simp at this; obtain ⟨_, rfl⟩ := this; cases v2; exact hφ,
   fun t2 σ2 e2 _ hr hm => by
      have := n_rtg hr; simp at this; obtain ⟨rfl, rfl⟩ := this
      simp at hm; subst hm; exact .inl rfl⟩

/-- Completeness data for the library WP over `nLang`: no expression is reducible. -/
@[reducible] noncomputable def acgY [InvGS_gen .hasNoLC GY] (γ : GName) :
    @AbstractLangCompletenessGen Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY γ)
      (Wp.wp (PROP := IProp GY) Stuckness.NotStuck) WP_lawful_abstract :=
  letI := tiY γ
  { heap_inv := fun _ _ => iprop(True), heap_inv_timeless := fun _ _ => inferInstance,
    lang_completeness := fun {n C e₁ σ E} => by
      iintro %hr
      obtain ⟨_, _, _, _, h⟩ := hr
      exact (h : False).elim }


theorem n_adeqNF (φ : Unit → Unit → Prop) (hφ : φ () ()) : @AdequateNoFork Bool Unit Unit Unit nLang .NotStuck true () φ :=
  ⟨fun hr => by have := n_rtg hr; simp at this; obtain ⟨rfl, rfl⟩ := this; rfl,
   fun {t2 σ2 v2} hr => by
      have := n_rtg hr; simp at this; obtain ⟨_, rfl⟩ := this; cases v2; exact hφ,
   fun {t2 σ2 e2} _ hr hm => by
      have := n_rtg hr; simp at this; obtain ⟨rfl, rfl⟩ := this
      simp at hm; subst hm; exact .inl rfl⟩

/-- Ectx language on Bool with a trivial context and no base steps; `true` is the only value. -/
@[instance_reducible] def nEL : EctxLanguage Bool Unit Unit Unit Unit where
  baseStep := fun _ _ _ => False
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  empty := ()
  comp := fun _ _ => ()
  fill := fun _ e => e
  fill_empty := fun _ => rfl
  fill_comp := fun _ _ _ => rfl
  fill_inj := fun h => h
  fill_val := fun _ _ h => h
  step_by_val := fun _ _ h => h.elim
  val_stuck := fun h => h.elim
  base_ctx_step_val := fun h => h.elim

theorem bwpT_false (h : ∀ [InvGS_gen .hasNoLC GY], @BindAbstractWP Bool Unit Unit Unit (@EctxLanguage.instLanguage _ _ _ _ _ nEL) GY .hasNoLC (@igY (@EctxLanguage.instLanguage _ _ _ _ _ nEL) _) wpT) : False :=
  fupd_falseY ⊤ ⊤ fun {_} => true_intro.trans (h.wp_value (v := ()) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝))).mp

/-- In IProp, `▷▷False ⊢ |==> ▷False` fails at step index 1. -/
theorem nn_bupd_false {GF : BundledGFunctors}
    (E : (iprop(▷ ▷ ⌜False⌝) : IProp GF) ⊢ iprop(|==> ▷ ⌜False⌝)) : False := by
  obtain ⟨_, _, h⟩ := E 1 ⟨UORA.unit, ORA.unit_validN⟩ trivial 1 UORA.unit (Nat.le_refl _)
    (by rw [UORA.unit_left_id]; exact ORA.unit_validN)
  exact h

theorem nn_le {GF : BundledGFunctors} {n} {x} (h : (iprop(▷ ▷ ⌜False⌝) : IProp GF) n x) : n ≤ 1 := by
  rcases n with _ | _ | k
  · exact Nat.zero_le _
  · exact Nat.le_refl _
  · exact h.elim

/-- Stripping one later through a fancy update is unsound: `▷▷False ⊢ |={⊤}=> ▷False` under every InvGS gives False. -/
theorem strip_false {GF : BundledGFunctors} [InvGpreS GF]
    (H : ∀ [InvGS_gen .hasNoLC GF], (iprop(▷ ▷ ⌜False⌝) : IProp GF) ⊢ iprop(|={⊤}=> ▷ ⌜False⌝)) : False :=
  nn_bupd_false (GF := GF) (by
    iintro HP
    imod (fupd_soundness_no_lc_unfold (GF := GF) 0 ⊤) with ⟨%I, %ω, _, Hω, #Hupd⟩
    ihave Hf := (@H I) $$ HP
    imod Hupd $$ Hf Hω with Hr
    imodintro
    iapply (except0_mono sep_elim_right).trans except0_later
    iexact Hr)


noncomputable abbrev F : IProp GY := iprop(▷ ⌜False⌝)
theorem app2 {X A B C : IProp GY} (h : ⊢ A -∗ B -∗ C) (ha : X ⊢ A) (hb : ⊢ B) : X ⊢ C :=
  (ha.trans (wand_entails h)).trans (sep_emp.2.trans ((sep_mono_right hb).trans wand_elim_left))
theorem dropX {X Q : IProp GY} (hq : ⊢ Q) : X ⊢ Q := sep_emp.2.trans ((sep_mono_right hq).trans sep_elim_right)
/-- `▷ P` gives the one-step update at a single mask. -/
theorem sfi [InvGS_gen .hasNoLC GY] {E : CoPset} {P : IProp GY} : iprop(▷ P) ⊢ iprop(|={E}[E]▷=> P) :=
  (later_mono fupd_intro).trans fupd_intro
theorem post_id [InvGS_gen .hasNoLC GY] : ⊢ iprop(F ={⊤}=∗ F) := wand_intro (emp_sep.1.trans fupd_intro)
theorem wvf [InvGS_gen .hasNoLC GY] {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GY} :
    iprop(WP true @ s ; E {{ Φ }}) ⊢ iprop(|={E}=> Φ ()) := (wp_value_fupd' (v := ())).mp
theorem wvi [InvGS_gen .hasNoLC GY] {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GY} :
    Φ () ⊢ iprop(WP true @ s ; E {{ Φ }}) := wp_value' (v := ())
theorem twi [InvGS_gen .hasNoLC GY] {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GY} :
    Φ () ⊢ iprop(WP true @ s ; E [{ Φ }]) := twp.value' (v := ())

theorem n_irr : ¬ PrimStep.Reducible (Expr := Bool) (State := Unit) (Obs := List Unit) (false, ()) := by
  rintro ⟨_, _, _, _, hs⟩; exact hs
/-- With state interpretation True, WP of the stuck `false` gives `|={E,∅}=> False`. -/
theorem wpF [InvGS_gen .hasNoLC GY] {E : CoPset} {Φ : Unit → IProp GY} :
    iprop(WP false @ Stuckness.NotStuck ; E {{ Φ }}) ⊢ iprop(|={E,∅}=> ⌜False⌝) := by
  refine wp_unfold.mp.trans ?_
  refine (forall_elim ()).trans ((forall_elim 0).trans ((forall_elim []).trans ((forall_elim []).trans
    ((forall_elim 0).trans ?_))))
  refine (sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans ?_)
  exact BIFUpdate.mono (sep_elim_left.trans (pure_mono n_irr))
/-- One step update to a later-closed `|={∅,⊤}=> … WP false …` collapses to False. -/
theorem stepF [InvGS_gen .hasNoLC GY] {A B : IProp GY} {Φ : Unit → IProp GY} :
    iprop(|={∅}▷=>^[1] |={∅,⊤}=> A ∗ WP false @ Stuckness.NotStuck ; ⊤ {{ Φ }} ∗ B) ⊢ iprop(|={∅}▷=>^[1] ⌜False⌝) :=
  BIFUpdate.mono (later_mono ((BIFUpdate.mono ((BIFUpdate.mono (sep_elim_right.trans (sep_elim_left.trans wpF))).trans fupd_trans)).trans fupd_trans))
theorem stepsF (H : ∀ [InvGS_gen .hasNoLC GY], ⊢ (iprop(£ 1 -∗ |={⊤,∅}=> |={∅}▷=>^[1] ⌜False⌝) : IProp GY)) : False :=
  pure_soundness (PROP := IProp GY) (step_fupdN_soundness (hlc := .hasNoLC) 1 1 (P := iprop(⌜False⌝)) fun _ => H)

theorem stepG [InvGS_gen .hasNoLC GY] {Y : IProp GY} (g : Y ⊢ iprop(|={⊤,∅}=> ⌜False⌝)) :
    iprop(|={∅}▷=>^[1] |={∅,⊤}=> Y) ⊢ iprop(|={∅}▷=>^[1] ⌜False⌝) :=
  BIFUpdate.mono (later_mono ((BIFUpdate.mono ((BIFUpdate.mono g).trans fupd_trans)).trans fupd_trans))
theorem wptpF [InvGS_gen .hasNoLC GY] {l : List Bool} {Φs : List (Unit → IProp GY)} :
    wptp (GF := GY) (hlc := .hasNoLC) Stuckness.NotStuck (false :: l) Φs ⊢ iprop(|={⊤,∅}=> ⌜False⌝) :=
  BigSepL2.bigSepL2_cons_inv_left.mp.trans (exists_elim fun _ => exists_elim fun _ =>
    and_elim_r.trans (sep_elim_left.trans wpF))
theorem wptpT [InvGS_gen .hasNoLC GY] : ⊢ wptp (GF := GY) (hlc := .hasNoLC) Stuckness.NotStuck [true] [fun (_ : Unit) => iprop(True)] :=
  true_intro.trans ((wvi (Φ := fun _ => iprop(True)) (s := Stuckness.NotStuck) (E := ⊤)).trans
    (BigSepL2.bigSepL2_singleton (Φ := fun _ (e : Bool) (Ψ : Unit → IProp GY) => iprop(WP e @ Stuckness.NotStuck ; ⊤ {{ Ψ }}))).mpr)

end T1c4
open Iris Iris.BI Iris.Std Iris.ProgramLogic T1c4

-- `Iris.wp_step_fupd` idx 14: necessary
theorem t1c4_20 : ¬ drop0% Iris.wp_step_fupd 14 := fun h =>
  strip_false fun {_} => (app2 (@h .hasNoLC Bool Unit Unit Unit nLang GY igY .NotStuck ⊤ ⊤ true F (fun _ => F) (fun _ h => h))
    (sfi (P := F)) (post_id.trans (wvi (Φ := fun _ => iprop(F ={⊤}=∗ F))))).trans wvf
namespace T1c4
theorem dsub : (⊤ \ ⊤ : CoPset) ⊆ ∅ := fun _ hx => ((Std.LawfulSet.mem_diff.1 hx).2 CoPset.mem_full).elim
theorem esub (E : CoPset) : (∅ : CoPset) ⊆ E := fun _ h => (CoPset.mem_empty h).elim
theorem app1 {X A C : IProp GY} (h : ⊢ A -∗ C) (ha : X ⊢ A) : X ⊢ C := ha.trans (wand_entails h)
end T1c4
-- `Iris.wp_step_fupdN` idx 15: necessary
theorem t1c4_21 : ¬ drop0% Iris.wp_step_fupdN 15 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck ⊤ ⊤ true F (fun _ => F) 1 (fun _ h => h)
    refine (app1 h1 (and_intro ?_ (sep_emp.2.trans (sep_mono ?_ ?_)))).trans wvf
    · exact dropX (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
        wand_intro ((pure_intro (Nat.le_refl 1)).trans (fupd_mask_intro_discard (esub _))))
    · exact (later_mono (fupd_mask_intro_discard dsub)).trans sfi |>.trans (fupd_mask_intro_discard (esub _))
    · exact dropX (post_id.trans (wvi (Φ := fun _ => iprop(F ={⊤}=∗ F))))
-- `Iris.wp_step_fupdN_strong` idx 15: necessary
theorem t1c4_22 : ¬ drop0% Iris.wp_step_fupdN_strong 15 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck ⊤ ⊤ true F (fun _ => F) 1 (fun _ h => h)
    refine ((and_intro ?_ (sep_emp.2.trans (sep_mono ?_ ?_))).trans h1).trans wvf
    · exact dropX (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
        wand_intro ((pure_intro (Nat.le_refl 1)).trans (fupd_mask_intro_discard (esub _))))
    · exact (later_mono fupd_intro).trans sfi |>.trans fupd_intro
    · exact dropX (post_id.trans (wvi (Φ := fun _ => iprop(F ={⊤}=∗ F))))
-- `Iris.wp_frame_step_l` idx 14: necessary
theorem t1c4_23 : ¬ drop0% Iris.wp_frame_step_l 14 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck ⊤ ⊤ true (fun _ => iprop(True)) F (fun _ h => h)
    exact ((sep_emp.2.trans (sep_mono sfi (dropX (true_intro.trans (wvi (Φ := fun _ => iprop(True))))))).trans h1).trans
      (wvf.trans (BIFUpdate.mono sep_elim_left))
-- `Iris.wp_frame_step_r` idx 14: necessary
theorem t1c4_24 : ¬ drop0% Iris.wp_frame_step_r 14 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck ⊤ ⊤ true (fun _ => iprop(True)) F (fun _ h => h)
    exact ((emp_sep.2.trans (sep_mono (true_intro.trans (wvi (Φ := fun _ => iprop(True)))) sfi)).trans h1).trans
      (wvf.trans (BIFUpdate.mono sep_elim_right))
-- `Iris.wp_frame_step_l'` idx 14: necessary
theorem t1c4_25 : ¬ drop0% Iris.wp_frame_step_l' 14 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck ⊤ ⊤ true (fun _ => iprop(True)) F (fun _ h => h)
    exact ((sep_emp.2.trans (sep_mono .rfl (dropX (true_intro.trans (wvi (Φ := fun _ => iprop(True))))))).trans h1).trans
      (wvf.trans (BIFUpdate.mono sep_elim_left))
-- `Iris.wp_frame_step_r'` idx 14: necessary
theorem t1c4_26 : ¬ drop0% Iris.wp_frame_step_r' 14 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck ⊤ ⊤ true (fun _ => iprop(True)) F (fun _ h => h)
    exact ((emp_sep.2.trans (sep_mono (true_intro.trans (wvi (Φ := fun _ => iprop(True)))) .rfl)).trans h1).trans
      (wvf.trans (BIFUpdate.mono sep_elim_right))
-- `Iris.twp.to_wp_fupdN_strong` idx 15: necessary
theorem t1c4_27 : ¬ drop0% Iris.twp.to_wp_fupdN_strong 15 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck ⊤ ⊤ true F (fun _ => F) 1 (fun _ h => h)
    refine ((and_intro ?_ (sep_emp.2.trans (sep_mono ?_ ?_))).trans h1).trans wvf
    · exact dropX (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
        wand_intro ((pure_intro (Nat.le_refl 1)).trans (fupd_mask_intro_discard (esub _))))
    · exact (wand_intro (sep_elim_left.trans ((later_mono fupd_intro).trans sfi))).trans fupd_intro
    · exact dropX (post_id.trans (twi (Φ := fun _ => iprop(F ={⊤}=∗ F))))
-- `Iris.twp.wp_step` idx 13: necessary
theorem t1c4_28 : ¬ drop0% Iris.twp.wp_step 13 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck ⊤ true F (fun _ => F)
    exact (app2 h1 .rfl (post_id.trans (twi (Φ := fun _ => iprop(F ={⊤}=∗ F))))).trans wvf
namespace T1c4
/-- The constant-True and constant-later-False postconditions agree at step 0. -/
theorem dlY : OFE.DistLater 1 (fun _ : Unit => iprop(True) : Unit → IProp GY) (fun _ => F) := by
  intro m hm v n' x hn' p
  have : n' = 0 := by omega
  subst this
  exact ⟨fun _ => trivial, fun _ => trivial⟩
end T1c4
-- `Iris.wp_contractive` idx 11: necessary
theorem t1c4_29 : ¬ drop0% Iris.wp_contractive 11 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have hc := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck ⊤ true
    have d := hc.distLater_dist dlY
    have h2 : (iprop(▷ ▷ ⌜False⌝) : IProp GY) ⊢ iprop(WP true @ Stuckness.NotStuck ; ⊤ {{ fun _ => iprop(True) }}) :=
      true_intro.trans (wvi (Φ := fun _ => iprop(True)))
    refine fun n x hx => ?_
    have hn : n ≤ 1 := nn_le hx
    have h3 := (d n x.val hn x.property).mp (h2 n x hx)
    exact (wvf (Φ := fun _ => F) (s := Stuckness.NotStuck) (E := ⊤)) n x h3

-- `Iris.ProgramLogic.wp_step` idx 19: necessary
theorem t1c4_30 : ¬ drop0% Iris.ProgramLogic.wp_step 19 := fun h =>
  stepsF fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck true () 0 [] [] false () [] 0 (fun _ => iprop(True))
    have k1 : (£ 1 : IProp GY) ⊢ iprop(True ∗ £ 1) := emp_sep.2.trans (sep_mono_left true_intro)
    refine entails_wand ((k1.trans ((sep_mono_left (wand_entails h1)).trans wand_elim_left)).trans ?_)
    exact (sep_emp.2.trans ((sep_mono_right (true_intro.trans (wvi (Φ := fun _ => iprop(True))))).trans
      wand_elim_left)).trans (BIFUpdate.mono stepF)

-- `Iris.ProgramLogic.wptp_step` idx 18: necessary
theorem t1c4_31 : ¬ drop0% Iris.ProgramLogic.wptp_step 18 := fun h =>
  stepsF fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck [true] [false] [] [] () () 0
      [fun _ => iprop(True)] 0
    have k1 : (£ 1 : IProp GY) ⊢ iprop(True ∗ £ 1) := emp_sep.2.trans (sep_mono_left true_intro)
    refine entails_wand ((k1.trans ((sep_mono_left (wand_entails h1)).trans wand_elim_left)).trans ?_)
    exact (sep_emp.2.trans ((sep_mono_right wptpT).trans wand_elim_left)).trans
      (exists_elim fun _ => BIFUpdate.mono (stepG (sep_elim_right.trans wptpF)))
-- `Iris.ProgramLogic.wptp_preservation` idx 19: necessary
theorem t1c4_32 : ¬ drop0% Iris.ProgramLogic.wptp_preservation 19 := fun h =>
  stepsF fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .NotStuck 1 [true] [false] [] [] () () 0
      [fun _ => iprop(True)] 0
    have k1 : (£ 1 : IProp GY) ⊢ iprop(True ∗ £ 1) := emp_sep.2.trans (sep_mono_left true_intro)
    refine entails_wand ((k1.trans ((sep_mono_left (wand_entails h1)).trans wand_elim_left)).trans ?_)
    exact (sep_emp.2.trans ((sep_mono_right wptpT).trans wand_elim_left)).trans
      (BIFUpdate.mono (stepG (exists_elim fun _ => sep_elim_right.trans wptpF)))

-- `Iris.ProgramLogic.weakestpre_completeness` idx 12: necessary
theorem t1c4_1 : ¬ indep0% Iris.ProgramLogic.weakestpre_completeness 12 := fun h =>
  lwpT_false fun {_} => @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY 0) wpT iaoT inferInstance ([], ()) .doesFork 0 1 0 true

-- `Iris.ProgramLogic.weakestpre_sem_completeness` idx 19: necessary
theorem t1c4_h1 : ¬ drop0% Iris.ProgramLogic.weakestpre_sem_completeness 19 := fun h =>
  fupd_falseY ⊤ ⊤ fun {_} => by
    have A : ∀ γ, (tpInvIni (TI := tiY γ) : IProp GY) ⊢ |={⊤}=> ⌜False⌝ := fun γ => by
      have := @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY γ) (Wp.wp (PROP := IProp GY) Stuckness.NotStuck)
        WP_lawful_abstract WP_inv_open_abstract (acgY γ) inferInstance true () (fun _ => False)
      exact (wand_entails this).trans ((wand_mono_left true_intro).trans (emp_wand.mp.trans
        (LawfulAbstractWP.wp_value (wp := Wp.wp (PROP := IProp GY) Stuckness.NotStuck) (v := ()) (E := ⊤) (Φ := fun _ => iprop(⌜False⌝))).mp))
    exact (tpInv_alloc (Expr := Bool) (H := TM) (GF := GY)).trans
      (BIUpdateFUpdate.fupd_of_bupd.trans ((BIFUpdate.mono (exists_elim A)).trans fupd_trans))

-- `Iris.ProgramLogic.AbstractLangCompletenessGen.heap_inv_timeless` idx 12: necessary
theorem t1c4_2 : ¬ indep0% Iris.ProgramLogic.AbstractLangCompletenessGen.heap_inv_timeless 12 := fun h =>
  lwpT_false fun {_} => @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY 0) wpT [] ()
-- `Iris.ProgramLogic.AbstractLangCompletenessGen.lang_completeness` idx 12: necessary
theorem t1c4_3 : ¬ indep0% Iris.ProgramLogic.AbstractLangCompletenessGen.lang_completeness 12 := fun h =>
  lwpT_false fun {_} => @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY 0) wpT 0 [] true () ⊤
-- `Iris.ProgramLogic.isCcfg_persistent` idx 12: necessary
theorem t1c4_4 : ¬ indep0% Iris.ProgramLogic.isCcfg_persistent 12 := fun h =>
  lwpT_false fun {_} => @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY 0) wpT inferInstance ([], ()) .doesFork 0
-- `Iris.ProgramLogic.weakestpre_sem_completeness` idx 12: necessary
theorem t1c4_5 : ¬ indep0% Iris.ProgramLogic.weakestpre_sem_completeness 12 := fun h =>
  lwpT_false fun {_} => @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY 0) wpT iaoT inferInstance true () (fun _ => True)
    (n_adeq _ trivial)
-- `Iris.ProgramLogic.weakestpre_sem_completeness_nofork_strong` idx 12: necessary
theorem t1c4_6 : ¬ indep0% Iris.ProgramLogic.weakestpre_sem_completeness_nofork_strong 12 := fun h =>
  lwpT_false fun {_} => @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY 0) wpT iaoT inferInstance true () (fun _ _ => True)
    (n_adeqNF _ trivial)
-- `Iris.ProgramLogic.weakestpre_sem_completeness_nofork` idx 12: necessary
theorem t1c4_7 : ¬ indep0% Iris.ProgramLogic.weakestpre_sem_completeness_nofork 12 := fun h =>
  lwpT_false fun {_} => @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY 0) wpT iaoT inferInstance true () (fun _ _ => True)
    (n_adeqNF _ trivial)
-- `Iris.ProgramLogic.AbstractEctxLangCompletenessGen.heap_inv_timeless` idx 13: necessary
theorem t1c4_8 : ¬ indep0% Iris.ProgramLogic.AbstractEctxLangCompletenessGen.heap_inv_timeless 13 := fun h =>
  bwpT_false fun {_} => @h Bool Unit Unit Unit Unit nEL GY .hasNoLC (@igY (@EctxLanguage.instLanguage _ _ _ _ _ nEL) _) TM _ (tiY 0) wpT [] ()
-- `Iris.ProgramLogic.AbstractEctxLangCompletenessGen.ectx_lang_completeness` idx 13: necessary
theorem t1c4_9 : ¬ indep0% Iris.ProgramLogic.AbstractEctxLangCompletenessGen.ectx_lang_completeness 13 := fun h =>
  bwpT_false fun {_} => @h Bool Unit Unit Unit Unit nEL GY .hasNoLC (@igY (@EctxLanguage.instLanguage _ _ _ _ _ nEL) _) TM _ (tiY 0) wpT 0 [] true () () ⊤
-- `Iris.ProgramLogic.weakestpre_ectx_to_prim_completeness` idx 13: necessary
theorem t1c4_10 : ¬ indep0% Iris.ProgramLogic.weakestpre_ectx_to_prim_completeness 13 := fun h =>
  bwpT_false fun {_} => @h Bool Unit Unit Unit Unit nEL GY .hasNoLC (@igY (@EctxLanguage.instLanguage _ _ _ _ _ nEL) _) TM _ (tiY 0) wpT 0 [] true () ⊤
-- `Iris.ProgramLogic.weakestpre_sem_completeness_nofork_strong` idx 19: necessary
theorem t1c4_h2 : ¬ drop0% Iris.ProgramLogic.weakestpre_sem_completeness_nofork_strong 19 := fun h =>
  fupd_falseY ⊤ ⊤ fun {_} => by
    have A : ∀ γ, (tpInvIni (TI := tiY γ) : IProp GY) ⊢ |={⊤}=> ⌜False⌝ := fun γ => by
      have := @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY γ) (Wp.wp (PROP := IProp GY) Stuckness.NotStuck)
        WP_lawful_abstract WP_inv_open_abstract (acgY γ) inferInstance true () (fun _ _ => False)
      exact (wand_entails this).trans ((wand_mono_left true_intro).trans (emp_wand.mp.trans
        ((LawfulAbstractWP.wp_value (wp := Wp.wp (PROP := IProp GY) Stuckness.NotStuck) (v := ()) (E := ⊤)).mp.trans
          (BIFUpdate.mono (exists_elim fun _ => sep_elim_right.trans (sep_elim_right.trans sep_elim_right))))))
    exact (tpInv_alloc (Expr := Bool) (H := TM) (GF := GY)).trans
      (BIUpdateFUpdate.fupd_of_bupd.trans ((BIFUpdate.mono (exists_elim A)).trans fupd_trans))
-- `Iris.ProgramLogic.weakestpre_sem_completeness_nofork` idx 19: necessary
theorem t1c4_h3 : ¬ drop0% Iris.ProgramLogic.weakestpre_sem_completeness_nofork 19 := fun h =>
  fupd_falseY ⊤ ⊤ fun {_} => by
    have A : ∀ γ, (tpInvIni (TI := tiY γ) : IProp GY) ⊢ |={⊤}=> ⌜False⌝ := fun γ => by
      have := @h Bool Unit Unit Unit nLang GY .hasNoLC igY TM _ (tiY γ) (Wp.wp (PROP := IProp GY) Stuckness.NotStuck)
        WP_lawful_abstract WP_inv_open_abstract (acgY γ) inferInstance true () (fun _ _ => False)
      exact (wand_entails this).trans ((wand_mono_left true_intro).trans (emp_wand.mp.trans
        ((LawfulAbstractWP.wp_value (wp := Wp.wp (PROP := IProp GY) Stuckness.NotStuck) (v := ()) (E := ⊤)).mp.trans
          (BIFUpdate.mono (exists_elim fun _ => sep_elim_right)))))
    exact (tpInv_alloc (Expr := Bool) (H := TM) (GF := GY)).trans
      (BIUpdateFUpdate.fupd_of_bupd.trans ((BIFUpdate.mono (exists_elim A)).trans fupd_trans))
-- `Iris.atomic_wp_seq_step` idx 17: necessary
theorem t1c4_33 : ¬ drop0% Iris.atomic_wp_seq_step 17 := fun h =>
  strip_false (GF := GY) fun {_} => by
    have h1 := @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .nil .nil .nil true ∅ (fun _ => iprop(True))
      (fun _ _ => iprop(True)) (fun _ _ _ => none) (fun _ _ _ => ())
    have hA : ⊢ atomic_wp (GF := GY) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) (TP := Tele.nil.{0}) true ∅ (fun _ => iprop(True))
        (fun _ _ => iprop(True)) (fun _ _ _ => none) (fun _ _ _ => ()) := by
      haveI : @Language.Atomic Bool Unit Unit Unit nLang .WeaklyAtomic true := ⟨fun hs => hs.elim⟩
      refine Entails.trans ?_ (atomic_seq_wp_atomic (ι := @igY nLang _) (Λ := nLang) (e := true) (E := ∅))
      iintro _ %Φ %x _ H
      iapply (wvi (Φ := Φ) (s := Stuckness.NotStuck) (E := ∅))
      iapply H
      all_goals first | exact (true_intro (PROP := IProp GY)) | exact Tele.Arg.nil | (simp only [Option.getD_none]; itrivial)
    refine Entails.trans (Q := iprop(WP true @ Stuckness.NotStuck ; ⊤ {{ fun _ => F }})) ?_ wvf
    iintro HX
    ihave H := h1 $$ []
    · iapply hA
    iapply H
    all_goals first | exact (true_intro (PROP := IProp GY)) | exact Tele.Arg.nil | skip
    inext
    iintro %y _ %z
    unfold Iris.BI.BIBase.wandM
    iexact HX

namespace T1c4
/-- Ectx language on Bool with trivial context and one pure base step `false → true`. -/
@[instance_reducible] def sEL : EctxLanguage Bool Unit Unit Unit Unit where
  baseStep := fun c o r => c.1 = false ∧ r.1 = true ∧ r.2.2 = [] ∧ o = []
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  empty := ()
  comp := fun _ _ => ()
  fill := fun _ e => e
  fill_empty := fun _ => rfl
  fill_comp := fun _ _ _ => rfl
  fill_inj := fun h => h
  fill_val := fun _ _ h => h
  step_by_val := fun _ _ _ => ⟨(), rfl⟩
  val_stuck := fun h => by obtain ⟨h1, -⟩ := h; simp only at h1; subst h1; rfl
  base_ctx_step_val := fun _ => .inr rfl
noncomputable abbrev sL : Language Bool Unit Unit Unit := @EctxLanguage.instLanguage _ _ _ _ _ sEL

@[instance_reducible] def gyElem1 : ElemG GY (constOF CoPsetDisjL) := { τ := 1, transp := by unfold GY; rfl }
noncomputable abbrev own1 (γ : GName) : IProp GY := iOwn (E := gyElem1) γ (.valid CoPset.full)
theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩
set_option linter.deprecated false in
theorem own_full_dup_false (γ : GName) : own1 γ ∗ own1 γ ⊢ iprop(⌜False⌝) :=
  iOwn_cmraValid_op.trans fun n x h => by
    have h' : ✓{n} ((DisjointLeibnizSet.valid CoPset.full : CoPsetDisjL) • DisjointLeibnizSet.valid CoPset.full) := h
    change ✓{n} (if CoPset.full ## CoPset.full then _ else _) at h'
    rw [if_neg full_not_disj] at h'
    exact h'
theorem own_full_alloc : ⊢ (|==> ∃ γ, own1 γ : IProp GY) := iOwn_alloc (E := gyElem1) _ trivial
theorem later_false_fupd [InvGS_gen .hasNoLC GY] {E1 E2 : CoPset} {X : IProp GY} :
    ▷ ⌜False⌝ ⊢ |={E1,E2}=> X :=
  (or_intro_l (Q := iprop(|={E1,E2}=> X))).trans (except0_fupd.trans fupd_except0)
theorem sstep : letI := sL; PrimStep.primStep ((false : Bool), ()) ([] : List Unit) (true, (), []) := by
  letI := sEL; exact BaseStep.ContextStep.ofBaseStep () ⟨rfl, rfl, rfl, rfl⟩
/-- One step of `false` (to the value `true`) under a postcondition False. -/
theorem wpS [InvGS_gen .hasNoLC GY] {E : CoPset} :
    letI := sL; (iprop(WP false @ Stuckness.NotStuck ; E {{ fun _ => iprop(⌜False⌝) }}) : IProp GY) ∗ £ 1 ⊢
      iprop(|={E,∅}=> |={∅}▷=>^[1] |={∅}=> ⌜False⌝) := by
  letI := sL
  have A : (iprop(WP false @ Stuckness.NotStuck ; E {{ fun _ => iprop(⌜False⌝) }}) : IProp GY) ⊢ _ :=
    wp_unfold.mp.trans ((forall_elim ()).trans ((forall_elim 0).trans ((forall_elim []).trans ((forall_elim []).trans
      ((forall_elim 0).trans ((sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans (BIFUpdate.mono sep_elim_right))))))))
  have A2 := A.trans (BIFUpdate.mono ((forall_elim true).trans ((forall_elim ()).trans ((forall_elim ([] : List Bool)).trans
    (sep_emp.2.trans ((sep_mono_right (pure_intro sstep)).trans wand_elim_left))))))
  refine ((sep_mono_left A2).trans BIFUpdate.frame_right).trans (BIFUpdate.mono (wand_elim_left.trans ?_))
  exact BIFUpdate.mono (later_mono (BIFUpdate.mono ((BIFUpdate.mono (sep_elim_right.trans (sep_elim_left.trans
    ((wp_value_fupd' (v := ())).mp.trans ((BIFUpdate.mono (fupd_mask_intro_discard (esub E))).trans fupd_trans))))).trans fupd_trans)))
theorem wpS' [InvGS_gen .hasNoLC GY] {E : CoPset} :
    letI := sL; (iprop(WP false @ Stuckness.NotStuck ; E {{ fun _ => iprop(⌜False⌝) }}) : IProp GY) ∗ £ 1 ⊢
      iprop(|={E,∅}=> |={∅}▷=>^[1] ⌜False⌝) :=
  wpS.trans (BIFUpdate.mono (BIFUpdate.mono (later_mono fupd_trans)))
theorem dsubN (N : Namespace) : (↑N : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
end T1c4
open T1c4
-- `Iris.inv_open_maybe_ectxlang_inv` idx 16: necessary
theorem t1c4_34 : ¬ drop0% Iris.inv_open_maybe_ectxlang_inv 16 := fun h =>
  stepsF fun {_} => by
    letI := sL
    have key : ∀ γ, own1 γ ∗ inv nroot (own1 γ) ⊢
        iprop(WP false @ Stuckness.NotStuck ; (⊤ \ ↑nroot) {{ fun _ => iprop(⌜False⌝) }}) := fun γ =>
      sep_comm.1.trans ((sep_mono_right (wand_intro (((sep_mono_left later_intro).trans
        (later_sep.mpr.trans (later_mono (own_full_dup_false γ)))).trans later_false_fupd))).trans
        (@h Bool Unit Unit Unit Unit sEL GY .hasNoLC (@igY sL _) (Wp.wp (PROP := IProp GY) Stuckness.NotStuck)
          WP_bind_abstract false (⊤ \ ↑nroot) nroot (own1 γ) (fun _ => iprop(⌜False⌝)) ⟨(), [], true, (), [], sstep⟩))
    iintro Hlc
    imod own_full_alloc with ⟨%γ, Ho⟩
    imod (inv_alloc_open nroot ⊤ (own1 γ) (dsubN nroot)) with ⟨#Hinv, _⟩
    ihave Hw := key γ $$ [Ho]
    · isplitl [Ho]
      · iexact Ho
      · iexact Hinv
    iapply wpS'
    isplitl [Hw]
    · iexact Hw
    · iexact Hlc

namespace T1c4
/-- The atomic update for `α = β = ▷ own1 γ` and a True postcondition, built from the invariant holding `own1 γ`. -/
theorem auInv [InvGS_gen .hasNoLC GY] (γ : GName) (Φ'' : Tele.nil.{0}.Arg → Tele.nil.{0}.Arg → IProp GY)
    (hΦ : ∀ x y, ⊢ Φ'' x y) :
    inv nroot (own1 γ) ⊢ atomic_update (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) (⊤ \ ∅) ∅
      (fun _ => iprop(▷ own1 γ)) (fun _ _ => iprop(▷ own1 γ)) Φ'' := by
  refine (and_intro .rfl true_intro).trans (aupd_intro (Q := iprop(True)) ?_)
  unfold atomic_acc
  iintro ⟨#Hinv, _⟩
  imod (inv_acc (E := ⊤ \ ∅) (N := nroot) (P := own1 γ) (fun x _ => Std.LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun h => CoPset.mem_empty h⟩)) $$ Hinv with ⟨HI, Hclose⟩
  imod (fupd_mask_subseteq (E1 := (⊤ \ ∅) \ ↑nroot) (esub _)) with Hcl
  imodintro
  iexists Tele.Arg.nil
  iframe HI
  isplit
  · iintro HI
    imod Hcl
    imod Hclose $$ HI
    itrivial
  · iintro %y HI
    imod Hcl
    imod Hclose $$ HI
    imodintro
    iapply (hΦ _ _)
/-- WP of the stuck `false` follows from an update to later False. -/
theorem wp_of_lf [InvGS_gen .hasNoLC GY] {Φ : Unit → IProp GY} :
    iprop(|={⊤,∅}=> ▷ ⌜False⌝) ⊢ iprop(WP false @ Stuckness.NotStuck ; ⊤ {{ Φ }}) := by
  refine Entails.trans ?_ wp_unfold.mpr
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
    wand_intro (sep_elim_left.trans ((BIFUpdate.mono later_false_fupd).trans fupd_trans))
end T1c4
-- `Iris.atomic_wp_inv` idx 19: necessary
theorem t1c4_35 : ¬ drop0% Iris.atomic_wp_inv 19 := fun h =>
  fupd_falseY ⊤ ∅ fun {_} => by
    have h1 := fun γ => @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .nil .nil .nil false ∅
      (fun _ => iprop(▷ own1 γ)) (fun _ _ => iprop(▷ own1 γ)) (fun _ _ _ => none) (fun _ _ _ => ()) nroot (own1 γ)
    iintro
    imod (BIUpdateFUpdate.fupd_of_bupd (E := ⊤) (P := iprop(∃ γ, own1 γ))) $$ [] with ⟨%γ, Ho⟩
    · iapply own_full_alloc
    ihave Hi := inv_alloc nroot ⊤ (own1 γ) $$ [Ho]
    · inext
      iexact Ho
    imod Hi with #Hinv
    ihave Hc := h1 γ $$ []
    · iunfold atomic_wp
      iintro %Φ AU
      iapply wp_of_lf
      ihave AU2 := ((atomic_update_mask_weaken (fun _ _ => CoPset.mem_full)).trans aupd_aacc) $$ AU
      iunfold atomic_acc at AU2
      imod AU2 with ⟨%x, H12, _⟩
      imodintro
      isimp only [Tele.app_bind] at H12
      iapply (later_sep.mpr.trans (later_mono (own_full_dup_false γ)))
      iexact H12
    ihave Hc2 := Hc $$ Hinv
    iunfold atomic_wp at Hc2
    ispecialize Hc2 $$ %(fun _ => iprop(True))
    iapply wpF
    iapply Hc2
    iapply (auInv γ (λ.. x y, iprop(∀.. z, ((fun _ _ _ => none) : Tele.nil.{0}.Arg → Tele.nil.{0}.Arg → Tele.nil.{0}.Arg → Option (IProp GY)) x y z -∗? (fun _ => iprop(True) : Unit → IProp GY) ((fun _ _ _ => ()) x y z))) (fun _ _ => true_intro))
    iexact Hinv

-- `Iris.atomic_wp_mask_weaken` idx 18: necessary
theorem t1c4_36 : ¬ drop0% Iris.atomic_wp_mask_weaken 18 := fun h =>
  fupd_falseY ⊤ ∅ fun {_} => by
    have h1 := fun γ => @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .nil .nil .nil false
      (fun _ => iprop(▷ own1 γ)) (fun _ _ => iprop(▷ own1 γ)) (fun _ _ _ => none) (fun _ _ _ => ()) ⊤ ∅
    iintro
    imod (BIUpdateFUpdate.fupd_of_bupd (E := ⊤) (P := iprop(∃ γ, own1 γ))) $$ [] with ⟨%γ, Ho⟩
    · iapply own_full_alloc
    ihave Hi := inv_alloc nroot ⊤ (own1 γ) $$ [Ho]
    · inext
      iexact Ho
    imod Hi with #Hinv
    ihave Hc := h1 γ $$ []
    · iunfold atomic_wp
      iintro %Φ AU
      iapply wp_of_lf
      imod (inv_acc (E := ⊤) (N := nroot) (P := own1 γ) (dsubN nroot)) $$ Hinv with ⟨HB, _⟩
      ihave AU2 := ((atomic_update_mask_weaken (Eo2 := ⊤ \ ↑nroot)
        (fun _ hx => ((Std.LawfulSet.mem_diff.1 hx).2 CoPset.mem_full).elim)).trans aupd_aacc) $$ AU
      iunfold atomic_acc at AU2
      imod AU2 with ⟨%x, HA, _⟩
      imodintro
      iapply (later_sep.mpr.trans (later_mono (own_full_dup_false γ)))
      isplitl [HA]
      · iexact HA
      · iexact HB
    iunfold atomic_wp at Hc
    ispecialize Hc $$ %(fun _ => iprop(True))
    iapply wpF
    iapply Hc
    iapply (auInv γ (λ.. x y, iprop(∀.. z, ((fun _ _ _ => none) : Tele.nil.{0}.Arg → Tele.nil.{0}.Arg → Tele.nil.{0}.Arg → Option (IProp GY)) x y z -∗? (fun _ => iprop(True) : Unit → IProp GY) ((fun _ _ _ => ()) x y z))) (fun _ _ => true_intro))
    iexact Hinv

-- `Iris.persistent_seq_wp_atomic` idx 16: necessary
theorem t1c4_37 : ¬ drop0% Iris.persistent_seq_wp_atomic 16 := fun h =>
  fupd_falseY ⊤ ∅ fun {_} => by
    have h1 := fun γ => @h .hasNoLC Bool Unit Unit Unit nLang GY (@igY nLang _) .nil .nil false ∅
      (fun _ => iprop(▷ own1 γ)) (fun _ _ => iprop(▷ own1 γ)) (fun _ _ _ => none) (fun _ _ _ => ())
    iintro
    imod (BIUpdateFUpdate.fupd_of_bupd (E := ⊤) (P := iprop(∃ γ, own1 γ))) $$ [] with ⟨%γ, Ho⟩
    · iapply own_full_alloc
    ihave Hi := inv_alloc nroot ⊤ (own1 γ) $$ [Ho]
    · inext
      iexact Ho
    imod Hi with #Hinv
    ihave Hc := h1 γ $$ []
    · iintro %Φ HA _
      iapply wp_of_lf
      imod (inv_acc (E := ⊤) (N := nroot) (P := own1 γ) (dsubN nroot)) $$ Hinv with ⟨HB, _⟩
      iapply (fupd_mask_intro_discard (esub _))
      iapply (later_sep.mpr.trans (later_mono (own_full_dup_false γ)))
      isplitl [HA]
      · iexact HA
      · iexact HB
    iunfold atomic_wp at Hc
    ispecialize Hc $$ %(fun _ => iprop(True))
    iapply wpF
    iapply Hc
    iapply (auInv γ (λ.. x y, iprop(∀.. z, ((fun _ _ _ => none) : Tele.nil.{0}.Arg → Tele.nil.{0}.Arg → Tele.nil.{0}.Arg → Option (IProp GY)) x y z -∗? (fun _ => iprop(True) : Unit → IProp GY) ((fun _ _ _ => ()) x y z))) (fun _ _ => true_intro))
    iexact Hinv

namespace T1c4
/-- Language on Bool: `true` is the value, `false` loops (so no non-value is atomic). -/
@[instance_reducible] def lLang : Language Bool Unit Unit Unit where
  primStep := fun c _ c' => c.1 = false ∧ c'.1 = false ∧ c'.2.2 = []
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by intro e σ obs e' σ' eₜ h; obtain ⟨h1, -⟩ := h; simp only at h1; subst h1; rfl
theorem empty_ne_top : (∅ : CoPset) ≠ ⊤ := fun h => by
  have : Pos.xH ∈ (⊤ : CoPset) := CoPset.mem_full
  rw [← h] at this
  exact CoPset.mem_empty this
/-- Mask-sensitive abstract wp: values as usual, the looping `false` holds at mask ⊤ and is refutable elsewhere. -/
noncomputable def wpM [InvGS_gen .hasNoLC GY] : AbstractWP Bool Unit GY := fun E e Φ =>
  if e then iprop(|={E}=> Φ ()) else iprop(⌜E = ⊤⌝ ∨ |={E,∅}=> ⌜False⌝)
end T1c4

namespace T1c4
/-- `wpM` is lawful over `lLang`. -/
theorem lwpM [InvGS_gen .hasNoLC GY] : @LawfulAbstractWP Bool Unit Unit Unit lLang GY .hasNoLC (@igY lLang _) wpM := by
  letI : Language Bool Unit Unit Unit := lLang
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro E e Φ
    cases e
    · show iprop(|={E}=> (⌜E = ⊤⌝ ∨ |={E,∅}=> ⌜False⌝)) ⊢ iprop(⌜E = ⊤⌝ ∨ |={E,∅}=> ⌜False⌝)
      by_cases hE : E = ⊤
      · exact dropX (pure_intro hE) |>.trans or_intro_l
      · exact (BIFUpdate.mono (or_elim (pure_elim' fun h => absurd h hE) .rfl)).trans (fupd_trans.trans or_intro_r)
    · exact fupd_trans
  · intro E e Φ
    cases e
    · exact .rfl
    · exact fupd_trans
  · intro E Φ v
    cases v; exact .rfl
  · intro E e Φ Ψ
    cases e
    · exact wand_intro sep_elim_left
    · exact wand_intro (BIFUpdate.frame_right.trans (BIFUpdate.mono
        ((sep_mono_right ((forall_elim ()).trans .rfl)).trans (sep_comm.1.trans wand_elim_left))))
  · intro E1 E2 Φ e Hatom
    cases e
    · exact (Hatom.atomic (σ := ()) (obs := []) (e' := false) (σ' := ()) (eₜ := []) ⟨rfl, rfl, rfl⟩
        [] false () [] ⟨rfl, rfl, rfl⟩).elim
    · exact fupd_trans.trans fupd_trans
end T1c4

-- `Iris.LawfulAbstractWP.wp_atomic` idx 14: necessary
theorem t1c4_38 : ¬ drop0% Iris.LawfulAbstractWP.wp_atomic 14 := fun h =>
  fupd_falseY ⊤ ∅ fun {_} => by
    have h1 := @h Bool Unit Unit Unit lLang GY .hasNoLC (@igY lLang _) wpM lwpM ∅ ⊤ (fun _ => iprop(True)) false
    have h2 : iprop(|={∅,⊤}=> emp) ⊢ iprop(|={∅}=> ⌜False⌝) :=
      ((BIFUpdate.mono (show (iprop(emp) : IProp GY) ⊢ iprop(⌜(⊤ : CoPset) = ⊤⌝ ∨ |={⊤,∅}=> ⌜False⌝) from
        (pure_intro rfl).trans or_intro_l)).trans h1).trans (or_elim (pure_elim' fun h => absurd h empty_ne_top) .rfl)
    exact (fupd_mask_subseteq (esub ⊤)).trans ((BIFUpdate.mono h2).trans fupd_trans)

namespace T1c4
/-- Abstract wp that only depends on the mask: True-ish exactly when the mask is everything. -/
noncomputable def wpN [InvGS_gen .hasNoLC GY] : AbstractWP Bool Unit GY := fun E _ _ =>
  iprop(⌜(⊤ : CoPset) ⊆ E⌝ ∨ |={E,∅}=> ⌜False⌝)
theorem top_not_empty : ¬ ((⊤ : CoPset) ⊆ ∅) := fun h => CoPset.mem_empty (h Pos.xH CoPset.mem_full)
/-- `wpN` satisfies the invariant-opening law (with `E₂ ⊆ E₁`) over `nLang`. -/
theorem iaoN [InvGS_gen .hasNoLC GY] : @InvOpenAbstractWP Bool Unit Unit Unit nLang GY .hasNoLC (@igY nLang _) wpN := by
  refine ⟨fun e E₁ E₂ Φ Hsub => ?_⟩
  by_cases h1 : (⊤ : CoPset) ⊆ E₁
  · exact dropX (pure_intro h1) |>.trans or_intro_l
  · have h2 : ¬ ((⊤ : CoPset) ⊆ E₂) := fun h => h1 fun x hx => Hsub x (h x hx)
    refine (BIFUpdate.mono (or_elim ?_ ?_)).trans (fupd_trans.trans or_intro_r)
    · exact exists_elim fun _ => exists_elim fun _ => sep_elim_right.trans (sep_elim_right.trans
        (sep_elim_right.trans (or_elim (pure_elim' fun h => absurd h h2) .rfl)))
    · exact (BIFUpdate.mono (or_elim (pure_elim' fun h => absurd h h1) .rfl)).trans fupd_trans
end T1c4

-- `Iris.InvOpenAbstractWP.inv_open_maybe` idx 14: necessary
theorem t1c4_39 : ¬ drop0% Iris.InvOpenAbstractWP.inv_open_maybe 14 := fun h =>
  fupd_falseY ⊤ ∅ fun {_} => by
    have h1 := @h Bool Unit Unit Unit nLang GY .hasNoLC (@igY nLang _) wpN iaoN false ∅ ⊤ (fun _ => iprop(True))
    have h2 : (iprop(|={∅,⊤}=> emp) : IProp GY) ⊢ iprop(|={∅}=> ⌜False⌝) := by
      refine Entails.trans ?_ (h1.trans (or_elim (pure_elim' fun h => absurd h top_not_empty) .rfl))
      refine BIFUpdate.mono (Entails.trans ?_ or_intro_l)
      iintro _
      iexists (id : Bool → Bool), false
      isplitr
      · ipureintro
        exact @Language.instContext_id Bool Unit Unit Unit nLang
      isplitr
      · ipureintro
        rfl
      isplitr
      · ipureintro
        exact ⟨fun h => h.elim⟩
      unfold wpN
      ileft
      ipureintro
      exact fun _ h => h
    exact (fupd_mask_subseteq (esub ⊤)).trans ((BIFUpdate.mono h2).trans fupd_trans)
