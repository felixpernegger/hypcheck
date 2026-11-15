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

namespace T2c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic COFE Auth

abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare
noncomputable abbrev GMF : OFunctorPre := constOF (HeapView Nat (Agree (DiscreteO Bool)) TM)
/-- Closed-proofs GF (slots 0–3) with a ghost map slot and cancelable invariants (from T1c4). -/
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

@[instance_reducible] def gyElem1 : ElemG GY (constOF CoPsetDisjL) := { τ := 1, transp := by unfold GY; rfl }
/-- Exclusive token: two copies are inconsistent. -/
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
theorem stepG [InvGS_gen .hasNoLC GY] {Y : IProp GY} (g : Y ⊢ iprop(|={⊤,∅}=> ⌜False⌝)) :
    iprop(|={∅}▷=>^[1] |={∅,⊤}=> Y) ⊢ iprop(|={∅}▷=>^[1] ⌜False⌝) :=
  BIFUpdate.mono (later_mono ((BIFUpdate.mono ((BIFUpdate.mono g).trans fupd_trans)).trans fupd_trans))
theorem stepsF (H : ∀ [InvGS_gen .hasNoLC GY], ⊢ (iprop(£ 1 -∗ |={⊤,∅}=> |={∅}▷=>^[1] ⌜False⌝) : IProp GY)) : False :=
  pure_soundness (PROP := IProp GY) (step_fupdN_soundness (hlc := .hasNoLC) 1 1 (P := iprop(⌜False⌝)) fun _ => H)
theorem esub (E : CoPset) : (∅ : CoPset) ⊆ E := fun _ h => (CoPset.mem_empty h).elim
theorem dsubN (N : Namespace) : (↑N : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full

/-- Three-expression language: a0 → a1 (sets the state to true), a1 → a2 only from state true
(resets it), a2 is the value. a0 is not atomic. -/
inductive AE | a0 | a1 | a2
@[instance_reducible] def aLang : Language AE Bool Unit Unit where
  primStep := fun c o r => o = [] ∧ r.2.2 = [] ∧
    ((c.1 = .a0 ∧ r.1 = .a1 ∧ r.2.1 = true) ∨ (c.1 = .a1 ∧ c.2 = true ∧ r.1 = .a2 ∧ r.2.1 = false))
  toVal := fun e => match e with | .a2 => some () | _ => none
  ofVal := fun _ => .a2
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    obtain ⟨-, -, (⟨h1, -⟩ | ⟨h1, -⟩)⟩ := h <;> simp only at h1 <;> subst h1 <;> rfl
attribute [instance] aLang
/-- IrisGS over aLang whose state interpretation holds the token exactly in state true. -/
@[reducible] noncomputable def igA [x : InvGS_gen .hasNoLC GY] (γ : GName) : @IrisGS_gen .hasNoLC AE Unit Bool Unit aLang GY :=
  { invGS := x, stateInterp := fun σ _ _ _ => if σ then own1 γ else iprop(emp), numLatersPerStep := fun _ => 0,
    forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }
end T2c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic T2c3
namespace T2c3
/-- Variant of aLang where a1 in state false loops (so nothing is stuck). -/
@[instance_reducible] def nLangA : Language AE Bool Unit Unit where
  primStep := fun c o r => o = [] ∧ r.2.2 = [] ∧
    ((c.1 = .a0 ∧ r.1 = .a1 ∧ r.2.1 = true) ∨ (c.1 = .a1 ∧ c.2 = true ∧ r.1 = .a2 ∧ r.2.1 = false) ∨
     (c.1 = .a1 ∧ c.2 = false ∧ r.1 = .a1 ∧ r.2.1 = false))
  toVal := fun e => match e with | .a2 => some () | _ => none
  ofVal := fun _ => .a2
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    obtain ⟨-, -, (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)⟩ := h <;> simp only at h1 <;> subst h1 <;> rfl
@[reducible] noncomputable def igN [x : InvGS_gen .hasNoLC GY] (γ : GName) : @IrisGS_gen .hasNoLC AE Unit Bool Unit nLangA GY :=
  letI := nLangA
  { invGS := x, stateInterp := fun σ _ _ _ => if σ then own1 γ else iprop(emp), numLatersPerStep := fun _ => 0,
    forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }
theorem wpN1 [InvGS_gen .hasNoLC GY] (γ : GName) (E : CoPset) (C : IProp GY) :
    letI := nLangA; letI := igN γ;
    ⊢ (iprop((▷ own1 γ -∗ C) -∗ WP AE.a1 @ Stuckness.NotStuck ; E {{ fun _ => C }}) : IProp GY) := by
  letI := nLangA; letI := igN γ
  refine BI.true_intro.trans (loeb_weak ?_)
  have hv : (ToVal.toVal AE.a1 : Option Unit) = none := rfl
  iintro IH Hc
  iapply wp_unfold.mpr
  simp only [wp.pre, hv]
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hcl
  isplitr
  · ipureintro
    cases σ₁
    · exact ⟨[], .a1, false, [], rfl, rfl, .inr (.inr ⟨rfl, rfl, rfl, rfl⟩)⟩
    · exact ⟨[], .a2, false, [], rfl, rfl, .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
  iintro %e₂ %σ₂ %eₜ %Hs Hlc
  have hn : IrisGS_gen.numLatersPerStep AE Unit Bool Unit GY ns = 0 := rfl
  isimp only [hn, step_fupdN]
  obtain ⟨-, rfl, (⟨h, -⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩)⟩ := Hs
  · cases h
  · isimp only [stateInterp, igN, ite_true] at Hσ
    imodintro
    inext
    imodintro
    imod Hcl
    imodintro
    isplitl []
    · exact (show (iprop(emp) : IProp GY) ⊢ (if false = true then own1 γ else iprop(emp)) from .rfl)
    isplitl [Hc Hσ]
    · iapply (wp_value' (v := ()))
      iapply Hc
      inext
      iexact Hσ
    · iclear Hlc
      iclear IH
      exact BigSepL.bigSepL_nil.2
  · imodintro
    inext
    imodintro
    imod Hcl
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    isplitl [IH Hc]
    · iapply IH
      iexact Hc
    · iclear Hlc
      exact BigSepL.bigSepL_nil.2
end T2c3

namespace T2c3
theorem wpN0 [InvGS_gen .hasNoLC GY] (γ : GName) (E : CoPset) (C : IProp GY) :
    letI := nLangA; letI := igN γ;
    (iprop(▷ own1 γ ∗ (▷ own1 γ -∗ C)) : IProp GY) ⊢ iprop(WP AE.a0 @ Stuckness.NotStuck ; E {{ fun _ => C }}) := by
  letI := nLangA; letI := igN γ
  refine Entails.trans ?_ wp_unfold.mpr
  have hv : (ToVal.toVal AE.a0 : Option Unit) = none := rfl
  simp only [wp.pre, hv]
  iintro ⟨Ho, Hc⟩ %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hcl
  isplitr
  · ipureintro
    exact ⟨[], .a1, true, [], rfl, rfl, .inl ⟨rfl, rfl, rfl⟩⟩
  iintro %e₂ %σ₂ %eₜ %Hs Hlc
  obtain ⟨-, rfl, (⟨-, rfl, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩)⟩ := Hs
  rotate_left
  · cases h
  · cases h
  have hn : IrisGS_gen.numLatersPerStep AE Unit Bool Unit GY ns = 0 := rfl
  isimp only [hn, step_fupdN, List.length_nil]
  imodintro
  inext
  imodintro
  imod Hcl
  imodintro
  isplitl [Ho]
  · exact (show (own1 γ : IProp GY) ⊢ (if true = true then own1 γ else iprop(emp)) from .rfl)
  isplitl [Hc]
  · iapply (wpN1 γ E C)
    iexact Hc
  · iclear Hlc
    iclear Hσ
    exact BigSepL.bigSepL_nil.2
theorem runN0 [InvGS_gen .hasNoLC GY] (γ : GName) :
    letI := nLangA; letI := igN γ;
    (iprop(inv nroot (own1 γ) ∗ WP AE.a0 @ Stuckness.NotStuck ; ⊤ {{ fun _ => iprop(True) }} ∗ £ 1) : IProp GY) ⊢
      iprop(|={⊤,∅}=> |={∅}▷=>^[1] ⌜False⌝) := by
  letI := nLangA; letI := igN γ
  have hv : (ToVal.toVal AE.a0 : Option Unit) = none := rfl
  iintro ⟨#Hinv, Hw, Hlc⟩
  ihave Hw := wp_unfold.mp $$ Hw
  isimp only [wp.pre, hv] at Hw
  ispecialize Hw $$ %false %0 %([] : List Unit) %([] : List Unit) %0
  imod Hw $$ [] with ⟨_, Hst⟩
  · iclear Hinv
    exact (show (iprop(emp) : IProp GY) ⊢ (if false = true then own1 γ else iprop(emp)) from .rfl)
  ispecialize Hst $$ %AE.a1 %true %([] : List AE) [] Hlc
  · ipureintro
    exact ⟨rfl, rfl, .inl ⟨rfl, rfl, rfl⟩⟩
  have hn : IrisGS_gen.numLatersPerStep AE Unit Bool Unit GY 0 = 0 := rfl
  isimp only [hn, step_fupdN] at Hst
  isimp only [step_fupdN]
  imod Hst
  imodintro
  iapply fupd_intro
  inext
  imod Hst
  imod Hst with ⟨Hσ, -, -⟩
  imod (inv_acc (E := ⊤) (N := nroot) (P := own1 γ) (dsubN nroot)) $$ Hinv with ⟨HI, -⟩
  iapply later_false_fupd
  iapply (later_sep.mpr.trans (later_mono (own_full_dup_false γ)))
  isplitl [Hσ]
  · inext
    isimp only [stateInterp, igN, ite_true] at Hσ
    iexact Hσ
  · iexact HI
/-- The atomic update for α = β = ▷ own1 γ built from the invariant holding own1 γ (from T1c4). -/
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
end T2c3
-- `Iris.atomic_seq_wp_atomic` idx 17: necessary
theorem t2c3_4 : ¬ drop0% Iris.atomic_seq_wp_atomic 17 := fun h =>
  stepsF fun {_} => by
    iintro Hlc
    imod own_full_alloc with ⟨%γ, Ho⟩
    ihave Hi := inv_alloc nroot ⊤ (own1 γ) $$ [Ho]
    · inext
      iexact Ho
    imod Hi with #Hinv
    letI := nLangA; letI := igN γ
    have h1 := @h .hasNoLC AE Bool Unit Unit nLangA GY (igN γ) .nil .nil .nil .a0 ∅
      (fun _ => iprop(▷ own1 γ)) (fun _ _ => iprop(▷ own1 γ)) (fun _ _ _ => none) (fun _ _ _ => ())
    have hA : ⊢ atomic_wp (GF := GY) (TA := Tele.nil.{0}) (TB := Tele.nil.{0}) (TP := Tele.nil.{0}) AE.a0 ∅
        (fun _ => iprop(▷ own1 γ)) (fun _ _ => iprop(▷ own1 γ)) (fun _ _ _ => none) (fun _ _ _ => ()) := by
      refine Entails.trans ?_ h1
      iintro _ %Φ %x Hα H
      iapply (wpN0 γ ∅ (Φ ()))
      isplitl [Hα]
      · iexact Hα
      · iintro Hβ
        ispecialize H $$ %Tele.Arg.nil Hβ %Tele.Arg.nil
        ihave H2 := (show iprop(none -∗? Φ ()) ⊢ Φ () from .rfl) $$ H
        iexact H2
    ihave Hc := hA
    iunfold atomic_wp at Hc
    ispecialize Hc $$ %(fun _ => iprop(True))
    ihave Hw := Hc $$ []
    · iapply (auInv γ (λ.. x y, iprop(∀.. z, ((fun _ _ _ => none) : Tele.nil.{0}.Arg → Tele.nil.{0}.Arg → Tele.nil.{0}.Arg → Option (IProp GY)) x y z -∗? (fun _ => iprop(True) : Unit → IProp GY) ((fun _ _ _ => ()) x y z))) (fun _ _ => true_intro))
      iexact Hinv
    iapply runN0 γ
    isplitl []
    · iexact Hinv
    isplitl [Hw]
    · iexact Hw
    · iexact Hlc
namespace T2c3
theorem wpA1 [InvGS_gen .hasNoLC GY] (γ : GName) (E : CoPset) (C : IProp GY) :
    letI := igA γ; (iprop(▷ own1 γ -∗ C) : IProp GY) ⊢ iprop(WP AE.a1 @ Stuckness.MaybeStuck ; E {{ fun _ => C }}) := by
  letI := igA γ
  refine Entails.trans ?_ wp_unfold.mpr
  have hv : (ToVal.toVal AE.a1 : Option Unit) = none := rfl
  simp only [wp.pre, hv]
  iintro Hc %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hcl
  isplitr
  · ipureintro; trivial
  iintro %e₂ %σ₂ %eₜ %Hs Hlc
  obtain ⟨-, rfl, (⟨h, -⟩ | ⟨-, rfl, rfl, rfl⟩)⟩ := Hs
  · cases h
  isimp only [stateInterp, igA, ite_true, ite_false] at Hσ
  have hn : IrisGS_gen.numLatersPerStep AE Unit Bool Unit GY ns = 0 := rfl
  isimp only [hn, step_fupdN, List.length_nil]
  imodintro
  inext
  imodintro
  imod Hcl
  imodintro
  isplitl []
  · exact (show (iprop(emp) : IProp GY) ⊢ (if false = true then own1 γ else iprop(emp)) from .rfl)
  isplitl [Hc Hσ]
  · iapply (wp_value' (v := ()))
    iapply Hc
    inext
    iexact Hσ
  · iclear Hcl
    iclear Hlc
    exact BigSepL.bigSepL_nil.2
theorem wpA0 [InvGS_gen .hasNoLC GY] (γ : GName) (E : CoPset) (C : IProp GY) :
    letI := igA γ; (iprop(▷ own1 γ ∗ (▷ own1 γ -∗ C)) : IProp GY) ⊢ iprop(WP AE.a0 @ Stuckness.MaybeStuck ; E {{ fun _ => C }}) := by
  letI := igA γ
  refine Entails.trans ?_ wp_unfold.mpr
  have hv : (ToVal.toVal AE.a0 : Option Unit) = none := rfl
  simp only [wp.pre, hv]
  iintro ⟨Ho, Hc⟩ %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hcl
  isplitr
  · ipureintro; trivial
  iintro %e₂ %σ₂ %eₜ %Hs Hlc
  obtain ⟨-, rfl, (⟨-, rfl, rfl⟩ | ⟨h, -⟩)⟩ := Hs
  rotate_left
  · cases h
  have hn : IrisGS_gen.numLatersPerStep AE Unit Bool Unit GY ns = 0 := rfl
  isimp only [hn, step_fupdN, List.length_nil]
  imodintro
  inext
  imodintro
  imod Hcl
  imodintro
  isplitl [Ho]
  · exact (show (own1 γ : IProp GY) ⊢ (if true = true then own1 γ else iprop(emp)) from .rfl)
  isplitl [Hc]
  · iapply (wpA1 γ E C)
    iexact Hc
  · iclear Hlc
    iclear Hσ
    exact BigSepL.bigSepL_nil.2
end T2c3
namespace T2c3
/-- Running a0 at mask ⊤ from state false hands the token to the state interpretation while the
invariant holding the token must be closed again: one step to False. -/
theorem runA0 [InvGS_gen .hasNoLC GY] (γ : GName) :
    letI := igA γ; (iprop(inv nroot (own1 γ) ∗ WP AE.a0 @ Stuckness.MaybeStuck ; ⊤ {{ fun _ => iprop(True) }} ∗ £ 1) : IProp GY) ⊢
      iprop(|={⊤,∅}=> |={∅}▷=>^[1] ⌜False⌝) := by
  letI := igA γ
  have hv : (ToVal.toVal AE.a0 : Option Unit) = none := rfl
  iintro ⟨#Hinv, Hw, Hlc⟩
  ihave Hw := wp_unfold.mp $$ Hw
  isimp only [wp.pre, hv] at Hw
  ispecialize Hw $$ %false %0 %([] : List Unit) %([] : List Unit) %0
  imod Hw $$ [] with ⟨_, Hst⟩
  · iclear Hinv
    exact (show (iprop(emp) : IProp GY) ⊢ (if false = true then own1 γ else iprop(emp)) from .rfl)
  ispecialize Hst $$ %AE.a1 %true %([] : List AE) [] Hlc
  · ipureintro
    exact ⟨rfl, rfl, .inl ⟨rfl, rfl, rfl⟩⟩
  have hn : IrisGS_gen.numLatersPerStep AE Unit Bool Unit GY 0 = 0 := rfl
  isimp only [hn, step_fupdN] at Hst
  isimp only [step_fupdN]
  imod Hst
  imodintro
  iapply fupd_intro
  inext
  imod Hst
  imod Hst with ⟨Hσ, -, -⟩
  imod (inv_acc (E := ⊤) (N := nroot) (P := own1 γ) (dsubN nroot)) $$ Hinv with ⟨HI, -⟩
  iapply later_false_fupd
  iapply (later_sep.mpr.trans (later_mono (own_full_dup_false γ)))
  isplitl [Hσ]
  · inext
    isimp only [stateInterp, igA, ite_true] at Hσ
    iexact Hσ
  · iexact HI
end T2c3
-- `Iris.wp_atomic` idx 13: necessary
theorem t2c3_2 : ¬ drop0% Iris.wp_atomic 13 := fun h =>
  stepsF fun {_} => by
    iintro Hlc
    imod own_full_alloc with ⟨%γ, Ho⟩
    ihave Hi := inv_alloc nroot ⊤ (own1 γ) $$ [Ho]
    · inext
      iexact Ho
    imod Hi with #Hinv
    letI := igA γ
    have key : (inv nroot (own1 γ) : IProp GY) ⊢ iprop(WP AE.a0 @ Stuckness.MaybeStuck ; ⊤ {{ fun _ => iprop(True) }}) :=
      ((wand_entails (inv_acc (dsubN nroot))).trans (BIFUpdate.mono (wpA0 γ (⊤ \ ↑nroot) iprop(|={⊤ \ ↑nroot, ⊤}=> True)))).trans
        (@h .hasNoLC AE Bool Unit Unit aLang GY (igA γ) .MaybeStuck ⊤ (⊤ \ ↑nroot) .a0 (fun _ => iprop(True)))
    ihave Hw := key $$ Hinv
    iapply runA0 γ
    isplitl []
    · iexact Hinv
    isplitl [Hw]
    · iexact Hw
    · iexact Hlc
namespace T2c3
theorem fupd_falseY (E1 E2 : CoPset) (H : ∀ [InvGS_gen .hasNoLC GY], ⊢ (iprop(|={E1,E2}=> ⌜False⌝) : IProp GY)) : False :=
  pure_soundness (PROP := IProp GY)
    (fupd_soundness .hasNoLC 0 (E1 := E1) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))
theorem twA1 [InvGS_gen .hasNoLC GY] (γ : GName) (E : CoPset) (C : IProp GY) :
    letI := igA γ; (iprop(▷ own1 γ -∗ C) : IProp GY) ⊢ iprop(WP AE.a1 @ Stuckness.MaybeStuck ; E [{ fun _ => C }]) := by
  letI := igA γ
  refine Entails.trans ?_ twp.unfold.mpr
  have hv : (ToVal.toVal AE.a1 : Option Unit) = none := rfl
  simp only [twp.pre, hv]
  iintro Hc %σ₁ %ns %obs %nt Hσ
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hcl
  isplitr
  · ipureintro; trivial
  iintro %κ %e₂ %σ₂ %eₜ %Hs
  obtain ⟨rfl, rfl, (⟨h, -⟩ | ⟨-, rfl, rfl, rfl⟩)⟩ := Hs
  · cases h
  isimp only [stateInterp, igA, ite_true] at Hσ
  imod Hcl
  imodintro
  isplitr
  · ipureintro; rfl
  isplitl []
  · exact (show (iprop(emp) : IProp GY) ⊢ (if false = true then own1 γ else iprop(emp)) from .rfl)
  isplitl [Hc Hσ]
  · iapply (twp.value' (v := ()))
    iapply Hc
    inext
    iexact Hσ
  · exact BigSepL.bigSepL_nil.2
theorem twA0 [InvGS_gen .hasNoLC GY] (γ : GName) (E : CoPset) (C : IProp GY) :
    letI := igA γ; (iprop(▷ own1 γ ∗ (▷ own1 γ -∗ C)) : IProp GY) ⊢ iprop(WP AE.a0 @ Stuckness.MaybeStuck ; E [{ fun _ => C }]) := by
  letI := igA γ
  refine Entails.trans ?_ twp.unfold.mpr
  have hv : (ToVal.toVal AE.a0 : Option Unit) = none := rfl
  simp only [twp.pre, hv]
  iintro ⟨Ho, Hc⟩ %σ₁ %ns %obs %nt Hσ
  iclear Hσ
  imod Ho
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hcl
  isplitr
  · ipureintro; trivial
  iintro %κ %e₂ %σ₂ %eₜ %Hs
  obtain ⟨rfl, rfl, (⟨-, rfl, rfl⟩ | ⟨h, -⟩)⟩ := Hs
  rotate_left
  · cases h
  imod Hcl
  imodintro
  isplitr
  · ipureintro; rfl
  isplitl [Ho]
  · exact (show (own1 γ : IProp GY) ⊢ (if true = true then own1 γ else iprop(emp)) from .rfl)
  isplitl [Hc]
  · iapply (twA1 γ E C)
    iexact Hc
  · exact BigSepL.bigSepL_nil.2
theorem runT0 [InvGS_gen .hasNoLC GY] (γ : GName) :
    letI := igA γ; (iprop(inv nroot (own1 γ) ∗ WP AE.a0 @ Stuckness.MaybeStuck ; ⊤ [{ fun _ => iprop(True) }]) : IProp GY) ⊢
      iprop(|={⊤,∅}=> ⌜False⌝) := by
  letI := igA γ
  have hv : (ToVal.toVal AE.a0 : Option Unit) = none := rfl
  iintro ⟨#Hinv, Hw⟩
  ihave Hw := twp.unfold.mp $$ Hw
  isimp only [twp.pre, hv] at Hw
  ispecialize Hw $$ %false %0 %([] : List Unit) %0
  imod Hw $$ [] with ⟨_, Hst⟩
  · iclear Hinv
    exact (show (iprop(emp) : IProp GY) ⊢ (if false = true then own1 γ else iprop(emp)) from .rfl)
  imod Hst $$ %([] : List Unit) %AE.a1 %true %([] : List AE) [] with ⟨_, Hσ, -, -⟩
  · ipureintro
    exact ⟨rfl, rfl, .inl ⟨rfl, rfl, rfl⟩⟩
  isimp only [stateInterp, igA, ite_true] at Hσ
  imod (inv_acc (E := ⊤) (N := nroot) (P := own1 γ) (dsubN nroot)) $$ Hinv with ⟨HI, -⟩
  iapply later_false_fupd
  iapply (later_sep.mpr.trans (later_mono (own_full_dup_false γ)))
  isplitl [Hσ]
  · inext
    iexact Hσ
  · iexact HI
end T2c3
-- `Iris.twp.atomic` idx 13: necessary
theorem t2c3_3 : ¬ drop0% Iris.twp.atomic 13 := fun h =>
  fupd_falseY ⊤ ∅ fun {_} => by
    iintro
    imod (BIUpdateFUpdate.fupd_of_bupd (E := ⊤) (P := iprop(∃ γ, own1 γ))) $$ [] with ⟨%γ, Ho⟩
    · iapply own_full_alloc
    ihave Hi := inv_alloc nroot ⊤ (own1 γ) $$ [Ho]
    · inext
      iexact Ho
    imod Hi with #Hinv
    letI := igA γ
    have key : (inv nroot (own1 γ) : IProp GY) ⊢ iprop(WP AE.a0 @ Stuckness.MaybeStuck ; ⊤ [{ fun _ => iprop(True) }]) :=
      ((wand_entails (inv_acc (dsubN nroot))).trans (BIFUpdate.mono (twA0 γ (⊤ \ ↑nroot) iprop(|={⊤ \ ↑nroot, ⊤}=> True)))).trans
        (@h .hasNoLC AE Bool Unit Unit aLang GY (igA γ) .MaybeStuck ⊤ (⊤ \ ↑nroot) .a0 (fun _ => iprop(True)))
    ihave Hw := key $$ Hinv
    iapply runT0 γ
    isplitl []
    · iexact Hinv
    · iexact Hw
namespace T2c3
/-- Language on Bool with no steps; true is the only value (from T1c4). -/
@[instance_reducible] def nLang : Language Bool Unit Unit Unit where
  primStep := fun _ _ _ => False
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by intro e σ obs e' σ' eₜ h; exact h.elim
@[reducible] noncomputable def igY [x : InvGS_gen .hasNoLC GY] : @IrisGS_gen .hasNoLC Bool Unit Unit Unit nLang GY :=
  letI := nLang
  { invGS := x, stateInterp := fun _ _ _ _ => iprop(True), numLatersPerStep := fun _ => 0,
    forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }
theorem n_irr : ¬ (letI := nLang; PrimStep.Reducible (Expr := Bool) (State := Unit) (Obs := List Unit) (false, ())) := by
  rintro ⟨_, _, _, _, hs⟩; exact hs
/-- With state interpretation True, WP of the stuck false gives an update to False. -/
theorem wpF [InvGS_gen .hasNoLC GY] {E : CoPset} {Φ : Unit → IProp GY} :
    letI := nLang; letI := igY; iprop(WP false @ Stuckness.NotStuck ; E {{ Φ }}) ⊢ iprop(|={E,∅}=> ⌜False⌝) := by
  letI := nLang; letI := igY
  refine wp_unfold.mp.trans ?_
  refine (forall_elim ()).trans ((forall_elim 0).trans ((forall_elim []).trans ((forall_elim []).trans
    ((forall_elim 0).trans ?_))))
  refine (sep_emp.2.trans (sep_mono .rfl true_intro)).trans (wand_elim_left.trans ?_)
  exact BIFUpdate.mono (sep_elim_left.trans (pure_mono n_irr))
/-- WP of the stuck false follows from an update to later False. -/
theorem wp_of_lf [InvGS_gen .hasNoLC GY] {E : CoPset} {Φ : Unit → IProp GY} :
    letI := nLang; letI := igY; iprop(|={E,∅}=> ▷ ⌜False⌝) ⊢ iprop(WP false @ Stuckness.NotStuck ; E {{ Φ }}) := by
  letI := nLang; letI := igY
  refine Entails.trans ?_ wp_unfold.mpr
  exact forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
    wand_intro (sep_elim_left.trans ((BIFUpdate.mono later_false_fupd).trans fupd_trans))
/-- The token together with an invariant holding it makes every WP at mask ⊤ trivial. -/
theorem wp_top [InvGS_gen .hasNoLC GY] (γ : GName) {Φ : Unit → IProp GY} :
    letI := nLang; letI := igY; iprop(own1 γ ∗ inv nroot (own1 γ)) ⊢ iprop(WP false @ Stuckness.NotStuck ; ⊤ {{ Φ }}) := by
  letI := nLang; letI := igY
  refine Entails.trans ?_ wp_of_lf
  iintro ⟨Ho, #Hinv⟩
  imod (inv_acc (E := ⊤) (N := nroot) (P := own1 γ) (dsubN nroot)) $$ Hinv with ⟨HI, -⟩
  iapply later_false_fupd
  iapply (later_sep.mpr.trans (later_mono (own_full_dup_false γ)))
  isplitl [Ho]
  · inext
    iexact Ho
  · iexact HI
/-- Soundness shape for dropped mask inclusions: from a proof of WP false at ⊤ out of the token and
an invariant holding it, any route to WP false at ⊤ ∖ nroot is unsound (the invariant is allocated
open and its closer discarded, so the world stays consistent). -/
theorem mask_route (H : ∀ [InvGS_gen .hasNoLC GY] (γ : GName),
    letI := nLang; letI := igY; iprop(own1 γ ∗ inv nroot (own1 γ)) ⊢
      iprop(WP false @ Stuckness.NotStuck ; (⊤ \ ↑nroot) {{ fun _ => iprop(True) }})) : False :=
  fupd_falseY ⊤ ∅ fun {_} => by
    letI := nLang; letI := igY
    iintro
    imod (BIUpdateFUpdate.fupd_of_bupd (E := ⊤) (P := iprop(∃ γ, own1 γ))) $$ [] with ⟨%γ, Ho⟩
    · iapply own_full_alloc
    imod (inv_alloc_open nroot ⊤ (own1 γ) (dsubN nroot)) with ⟨#Hinv, -⟩
    ihave Hw := H γ $$ [Ho]
    · isplitl [Ho]
      · iexact Ho
      · iexact Hinv
    iapply wpF
    iexact Hw
end T2c3
-- `Iris.wp_frame_step_l'` idx 15: necessary
theorem t2c3_5 : ¬ drop0% Iris.wp_frame_step_l' 15 := fun h =>
  mask_route fun {_} γ => by
    letI := nLang; letI := igY
    refine Entails.trans ?_ ((@h .hasNoLC Bool Unit Unit Unit nLang GY igY .NotStuck (⊤ \ ↑nroot) ⊤ false
      (fun _ => iprop(True)) iprop(True) rfl).trans (wp_mono fun _ => sep_elim_right))
    exact (wp_top γ).trans (emp_sep.2.trans (sep_mono_left ((true_intro (P := iprop(emp))).trans later_intro)))
-- `Iris.wp_frame_step_r'` idx 15: necessary
theorem t2c3_6 : ¬ drop0% Iris.wp_frame_step_r' 15 := fun h =>
  mask_route fun {_} γ => by
    letI := nLang; letI := igY
    refine Entails.trans ?_ ((@h .hasNoLC Bool Unit Unit Unit nLang GY igY .NotStuck (⊤ \ ↑nroot) ⊤ false
      (fun _ => iprop(True)) iprop(True) rfl).trans (wp_mono fun _ => sep_elim_left))
    exact (wp_top γ).trans (sep_emp.2.trans (sep_mono_right ((true_intro (P := iprop(emp))).trans later_intro)))

-- `Iris.wp_step_fupdN` idx 16: necessary
theorem t2c3_7 : ¬ drop0% Iris.wp_step_fupdN 16 := fun h =>
  mask_route fun {_} γ => by
    letI := nLang; letI := igY
    have h1 := wand_entails (@h .hasNoLC Bool Unit Unit Unit nLang GY igY .NotStuck (⊤ \ ↑nroot) ⊤ false
      iprop(True) (fun _ => iprop(True)) 0 rfl)
    refine Entails.trans ?_ h1
    iintro H
    isplit
    · iintro %σ %ns %obs %nt _
      iapply (fupd_mask_intro_discard (esub _))
      ipureintro
      exact Nat.zero_le _
    · isplitl []
      · exact (fupd_mask_subseteq (esub _)).trans (BIFUpdate.mono (BIFUpdate.mono true_intro))
      · iapply (wp_top γ)
        iexact H


namespace T2c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic COFE Auth
noncomputable abbrev GNF : OFunctorPre := constOF (HeapView Nat (Agree (DiscreteO Nat)) TM)
/-- Closed-proofs GF with a ghost map Nat → Nat (thread pools over Nat) and cancelable invariants. -/
noncomputable def GN : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF⟩
  | 1  => ⟨constOF CoPsetDisjL⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3  => ⟨AuthURF (constOF Credit)⟩
  | 4  => ⟨GNF⟩
  | _  => ⟨CInvF⟩
instance gnWsat : WsatGpreS GN where
  inv := { τ := 0, transp := by unfold GN; rfl }
  enabled := { τ := 1, transp := by unfold GN; rfl }
  disabled := { τ := 2, transp := by unfold GN; rfl }
instance gnLc : LcGpreS GN where
  lc_elem := { τ := 3, transp := by unfold GN; rfl }
instance gnInv : InvGpreS GN where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance
instance gnGM : GhostMapG GN Nat Nat TM := ⟨{ τ := 4, transp := by unfold GN; rfl }⟩
instance gnCInv : CInvG GN := ⟨{ τ := 5, transp := by unfold GN; rfl }⟩
@[reducible] def tiN (γ : GName) : TpinvGS GN Nat TM := { toGhostMapG := inferInstance, tp_name := γ }

/-- Language on Nat: 0 is the value, odd e steps to e - 1, even e ≥ 2 steps to e - 2. With the
contexts e ↦ e + 2c, every e ≥ 3 is a non-atomic context around the atomic redex 1 or 2. -/
@[instance_reducible] def cLang : Language Nat Unit Unit Unit where
  primStep := fun c o r => o = [] ∧ r.2.2 = [] ∧
    ((c.1 % 2 = 1 ∧ r.1 = c.1 - 1) ∨ (c.1 % 2 = 0 ∧ 2 ≤ c.1 ∧ r.1 = c.1 - 2))
  toVal := fun e => if e = 0 then some () else none
  ofVal := fun _ => 0
  coe_of_toVal_eq_some := by intro e v h; by_cases h0 : e = 0 <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    obtain ⟨-, -, h⟩ := h
    have : e ≠ 0 := by omega
    simp [this]
attribute [instance] cLang
theorem fupd_falseN (E1 E2 : CoPset) (H : ∀ [InvGS_gen .hasNoLC GN], ⊢ (iprop(|={E1,E2}=> ⌜False⌝) : IProp GN)) : False :=
  pure_soundness (PROP := IProp GN)
    (fupd_soundness .hasNoLC 0 (E1 := E1) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans H))
theorem c_toVal (e : Nat) : (ToVal.toVal e : Option Unit) = if e = 0 then some () else none := rfl
theorem c_step {e e' : Nat} {σ σ' : Unit} {o : List Unit} {t : List Nat} :
    PrimStep.primStep (e, σ) o (e', σ', t) ↔ (o = [] ∧ t = [] ∧ ((e % 2 = 1 ∧ e' = e - 1) ∨ (e % 2 = 0 ∧ 2 ≤ e ∧ e' = e - 2))) :=
  Iff.rfl
instance cCtx (c : Nat) : Language.Context (fun e : Nat => e + 2 * c) where
  toVal_eq_none_fill := by
    intro e h
    rw [c_toVal] at h ⊢
    by_cases h0 : e = 0
    · simp [h0] at h
    · have : e + 2 * c ≠ 0 := by omega
      simp only [this, ↓reduceIte]
  primStep_fill := by
    intro e σ obs e' σ' eₜ h
    rw [c_step] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, ?_⟩
    omega
  primStep_fill_inv := by
    intro e σ obs K_e' σ' eₜ hv h
    rw [c_toVal] at hv
    have he : e ≠ 0 := by intro h0; simp [h0] at hv
    rw [c_step] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases Nat.mod_two_eq_zero_or_one e with hp | hp
    · refine ⟨e - 2, by omega, ?_⟩
      rw [c_step]; exact ⟨h1, h2, by omega⟩
    · refine ⟨e - 1, by omega, ?_⟩
      rw [c_step]; exact ⟨h1, h2, by omega⟩
theorem c_atomic {e : Nat} (h1 : 1 ≤ e) (h2 : e ≤ 2) : Language.Atomic .WeaklyAtomic e := by
  refine ⟨fun {σ obs e' σ' eₜ} h => ?_⟩
  rw [c_step] at h
  obtain ⟨-, -, h⟩ := h
  have : e' = 0 := by omega
  subst this
  intro _ _ _ _ hs
  rw [c_step] at hs
  omega
theorem c_red {e : Nat} (h : e ≠ 0) (σ : Unit) : PrimStep.Reducible (Expr := Nat) (State := Unit) (Obs := List Unit) (e, σ) := by
  rcases Nat.mod_two_eq_zero_or_one e with hp | hp
  · exact ⟨[], e - 2, (), [], (c_step).2 ⟨rfl, rfl, .inr ⟨hp, by omega, rfl⟩⟩⟩
  · exact ⟨[], e - 1, (), [], (c_step).2 ⟨rfl, rfl, .inl ⟨hp, rfl⟩⟩⟩

@[reducible] noncomputable def igC [x : InvGS_gen .hasNoLC GN] : IrisGS_gen .hasNoLC Nat GN :=
  { invGS := x, stateInterp := fun _ _ _ _ => iprop(True), numLatersPerStep := fun _ => 0,
    forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }
attribute [instance] igC
/-- Lawful abstract wp over cLang that is trivial on the atomic redexes 1 and 2 and refutable on
every non-atomic e ≥ 3 (no bind law, no invariant-opening law). -/
noncomputable def wpC [InvGS_gen .hasNoLC GN] : AbstractWP Nat Unit GN := fun E e Φ =>
  if e = 0 then iprop(|={E}=> Φ ()) else if e ≤ 2 then iprop(True) else iprop(|={E,∅}=> ⌜False⌝)
theorem wpC0 [InvGS_gen .hasNoLC GN] {E Φ} : wpC E 0 Φ = iprop(|={E}=> Φ ()) := rfl
theorem wpC12 [InvGS_gen .hasNoLC GN] {E Φ} {e : Nat} (h0 : e ≠ 0) (h2 : e ≤ 2) : wpC E e Φ = iprop(True) := by
  simp only [wpC, h0, h2, ↓reduceIte]
theorem wpC3 [InvGS_gen .hasNoLC GN] {E Φ} {e : Nat} (h0 : e ≠ 0) (h2 : ¬ e ≤ 2) : wpC E e Φ = iprop(|={E,∅}=> ⌜False⌝) := by
  simp only [wpC, h0, h2, ↓reduceIte]
theorem c_not_atomic {e : Nat} (h2 : ¬ e ≤ 2) (h : Language.Atomic .WeaklyAtomic e) : False := by
  rcases Nat.mod_two_eq_zero_or_one e with hp | hp
  · have hr := c_red (e := e - 2) (by omega) ()
    obtain ⟨o, e'', σ'', t, hs⟩ := hr
    exact h.atomic (σ := ()) (obs := []) (e' := e - 2) (σ' := ()) (eₜ := []) ((c_step).2 ⟨rfl, rfl, .inr ⟨hp, by omega, rfl⟩⟩) o e'' σ'' t hs
  · have hr := c_red (e := e - 1) (by omega) ()
    obtain ⟨o, e'', σ'', t, hs⟩ := hr
    exact h.atomic (σ := ()) (obs := []) (e' := e - 1) (σ' := ()) (eₜ := []) ((c_step).2 ⟨rfl, rfl, .inl ⟨hp, rfl⟩⟩) o e'' σ'' t hs
theorem lwpC [InvGS_gen .hasNoLC GN] : LawfulAbstractWP (Expr := Nat) (GF := GN) wpC := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro E e Φ
    by_cases h0 : e = 0
    · subst h0; rw [wpC0]; exact fupd_trans
    by_cases h2 : e ≤ 2
    · rw [wpC12 h0 h2]; exact true_intro
    · rw [wpC3 h0 h2]; exact fupd_trans
  · intro E e Φ
    by_cases h0 : e = 0
    · subst h0; rw [wpC0, wpC0]; exact fupd_trans
    by_cases h2 : e ≤ 2
    · rw [wpC12 h0 h2, wpC12 h0 h2]
    · rw [wpC3 h0 h2, wpC3 h0 h2]
  · intro E Φ v
    cases v; exact .rfl
  · intro E e Φ Ψ
    by_cases h0 : e = 0
    · subst h0; rw [wpC0, wpC0]
      exact wand_intro (BIFUpdate.frame_right.trans (BIFUpdate.mono
        ((sep_mono_right ((forall_elim ()).trans .rfl)).trans (sep_comm.1.trans wand_elim_left))))
    by_cases h2 : e ≤ 2
    · rw [wpC12 h0 h2, wpC12 h0 h2]; exact wand_intro (true_intro (PROP := IProp GN))
    · rw [wpC3 h0 h2, wpC3 h0 h2]; exact wand_intro sep_elim_left
  · intro E1 E2 Φ e Hatom
    by_cases h0 : e = 0
    · subst h0; rw [wpC0, wpC0]; exact fupd_trans.trans fupd_trans
    by_cases h2 : e ≤ 2
    · rw [wpC12 h0 h2, wpC12 h0 h2]; exact true_intro (PROP := IProp GN)
    · exact (c_not_atomic h2 Hatom).elim

attribute [instance] lwpC
theorem c_split (e : Nat) (h : e ≠ 0) : ∃ c e', e = e' + 2 * c ∧ 1 ≤ e' ∧ e' ≤ 2 := by
  rcases Nat.mod_two_eq_zero_or_one e with hp | hp
  · exact ⟨(e - 2) / 2, 2, by omega, by omega, by omega⟩
  · exact ⟨(e - 1) / 2, 1, by omega, by omega, by omega⟩
/-- Completeness data for wpC: every reducible thread is an atomic redex 1 or 2 in a context. -/
@[reducible] noncomputable def acgC [InvGS_gen .hasNoLC GN] (γ : GName) :
    @AbstractLangCompletenessGen Nat Unit Unit Unit cLang GN .hasNoLC igC TM _ (tiN γ) wpC lwpC :=
  letI := tiN γ
  { heap_inv := fun _ _ => iprop(True), heap_inv_timeless := fun _ _ => inferInstance,
    lang_completeness := fun {n C e₁ σ E} => by
      iintro %hr _ _
      have h0 : e₁ ≠ 0 := by
        rintro rfl
        obtain ⟨_, _, _, _, hs⟩ := hr
        rw [c_step] at hs
        omega
      obtain ⟨c, e', he, h1, h2⟩ := c_split e₁ h0
      imodintro
      ileft
      iexists (fun e : Nat => e + 2 * c), e'
      isplitr
      · ipureintro; exact cCtx c
      isplitr
      · ipureintro; exact he
      isplitr
      · ipureintro; rw [c_toVal]; simp only [show e' ≠ 0 by omega, ↓reduceIte]
      isplitr
      · ipureintro; exact c_atomic h1 h2
      iintro %Ψ _
      rw [wpC12 (by omega) h2]
      itrivial }
end T2c3
open Iris Iris.BI Iris.Std Iris.ProgramLogic T2c3
-- `Iris.ProgramLogic.weakestpre_sem_completeness` idx 13: necessary
theorem t2c3_8 : ¬ drop0% Iris.ProgramLogic.weakestpre_sem_completeness 13 := fun h =>
  T2c3.fupd_falseN ⊤ ∅ fun {_} => by
    have A : ∀ γ, (tpInvIni (TI := tiN γ) : IProp GN) ⊢ |={⊤,∅}=> ⌜False⌝ := fun γ => by
      have := @h Nat Unit Unit Unit cLang GN .hasNoLC igC TM _ (tiN γ) wpC lwpC (acgC γ) inferInstance 3 () (fun _ => True)
        ⟨fun _ _ _ _ => trivial, fun _ _ e2 _ _ _ => by
          by_cases h0 : e2 = 0
          · subst h0; exact .inl rfl
          · exact .inr (c_red h0 _)⟩
      refine (wand_entails this).trans ((wand_mono_left true_intro).trans (emp_wand.mp.trans ?_))
      rw [wpC3 (by omega) (by omega)]
    exact (tpInv_alloc (Expr := Nat) (H := TM) (GF := GN)).trans
      (BIUpdateFUpdate.fupd_of_bupd.trans ((BIFUpdate.mono (exists_elim A)).trans fupd_trans))
namespace T2c3
theorem c_len {ρ : List Nat × Unit} {o : List Unit} {ρ' : List Nat × Unit} (hs : Language.Step ρ o ρ') :
    ρ'.1.length = ρ.1.length := by
  cases hs with
  | atomic H t₁ t₂ =>
    obtain ⟨-, rfl, -⟩ := (c_step).1 H
    simp
theorem c_rtg {C C' : List Nat × Unit} (h : FromMathlib.Relation.ReflTransGen (@Language.ErasedStep Nat Unit Unit Unit cLang) C C') :
    C'.1.length = C.1.length := by
  induction h with
  | refl => rfl
  | tail _ hs ih => obtain ⟨_, hs⟩ := hs; rw [c_len hs, ih]
theorem c_adeqNF : @AdequateNoFork Nat Unit Unit Unit cLang .NotStuck 3 () (fun _ _ => True) :=
  ⟨fun hr => c_rtg hr, fun _ => trivial, fun {_ _ e2} _ _ _ => by
    by_cases h0 : e2 = 0
    · subst h0; exact .inl rfl
    · exact .inr (c_red h0 _)⟩
end T2c3
-- `Iris.ProgramLogic.weakestpre_sem_completeness_nofork` idx 13: necessary
theorem t2c3_9 : ¬ drop0% Iris.ProgramLogic.weakestpre_sem_completeness_nofork 13 := fun h =>
  T2c3.fupd_falseN ⊤ ∅ fun {_} => by
    have A : ∀ γ, (tpInvIni (TI := tiN γ) : IProp GN) ⊢ |={⊤,∅}=> ⌜False⌝ := fun γ => by
      have := @h Nat Unit Unit Unit cLang GN .hasNoLC igC TM _ (tiN γ) wpC lwpC (acgC γ) inferInstance 3 () (fun _ _ => True)
        c_adeqNF
      refine (wand_entails this).trans ((wand_mono_left true_intro).trans (emp_wand.mp.trans ?_))
      rw [wpC3 (by omega) (by omega)]
    exact (tpInv_alloc (Expr := Nat) (H := TM) (GF := GN)).trans
      (BIUpdateFUpdate.fupd_of_bupd.trans ((BIFUpdate.mono (exists_elim A)).trans fupd_trans))
-- `Iris.ProgramLogic.weakestpre_sem_completeness_nofork_strong` idx 13: necessary
theorem t2c3_10 : ¬ drop0% Iris.ProgramLogic.weakestpre_sem_completeness_nofork_strong 13 := fun h =>
  T2c3.fupd_falseN ⊤ ∅ fun {_} => by
    have A : ∀ γ, (tpInvIni (TI := tiN γ) : IProp GN) ⊢ |={⊤,∅}=> ⌜False⌝ := fun γ => by
      have := @h Nat Unit Unit Unit cLang GN .hasNoLC igC TM _ (tiN γ) wpC lwpC (acgC γ) inferInstance 3 () (fun _ _ => True)
        c_adeqNF
      refine (wand_entails this).trans ((wand_mono_left true_intro).trans (emp_wand.mp.trans ?_))
      rw [wpC3 (by omega) (by omega)]
    exact (tpInv_alloc (Expr := Nat) (H := TM) (GF := GN)).trans
      (BIUpdateFUpdate.fupd_of_bupd.trans ((BIFUpdate.mono (exists_elim A)).trans fupd_trans))
-- `Iris.ProgramLogic.weakestpre_completeness` idx 13: necessary
theorem t2c3_11 : ¬ drop0% Iris.ProgramLogic.weakestpre_completeness 13 := fun h =>
  T2c3.fupd_falseN ⊤ ∅ fun {_} => by
    have A : ∀ γ, (tpInvIni (TI := tiN γ) : IProp GN) ⊢ |={⊤,∅}=> ⌜False⌝ := fun γ => by
      letI := tiN γ; letI := acgC γ
      have Hsafe0 : cfgSafeForking (([3] : List Nat), ()) .doesFork :=
        fun {C₂} _ => ⟨fun {e2} _ => by
          by_cases h0 : e2 = 0
          · subst h0; exact .inl rfl
          · exact .inr (c_red h0 _), fun hf => Forking.noConfusion hf⟩
      iintro Hini
      imod (tpInv_set [3]) $$ Hini with ⟨Hauth, Hfrags⟩
      imod (CancelableInvariant.alloc ⊤ completenessN (cfgInv (wp := wpC) (([3] : List Nat), ()) .doesFork)) $$ [Hauth] with ⟨%γc, #Hinv, Hq⟩
      · inext
        iexists (([3] : List Nat), ())
        iframe Hauth
        isplitr
        · exact true_intro
        isplitr
        · ipureintro; exact Hsafe0
        · ipureintro; exact .refl
      ihave He0 := BigSepL.bigSepL_singleton $$ Hfrags
      ihave Hccfg : iprop(isCcfg (wp := wpC) (([3] : List Nat), ()) .doesFork γc) $$ [Hinv]
      · unfold isCcfg; itrivial
      ihave Hwp := (@h Nat Unit Unit Unit cLang GN .hasNoLC igC TM _ (tiN γ) wpC lwpC (acgC γ) inferInstance
        (([3] : List Nat), ()) .doesFork γc _ 0 3) $$ Hccfg Hq He0
      ihave Hw2 := (show wpC ⊤ 3 _ ⊢ iprop(|={⊤,∅}=> ⌜False⌝) by rw [wpC3 (by omega) (by omega)]) $$ Hwp
      iexact Hw2
    exact (tpInv_alloc (Expr := Nat) (H := TM) (GF := GN)).trans
      (BIUpdateFUpdate.fupd_of_bupd.trans ((BIFUpdate.mono (exists_elim A)).trans fupd_trans))

open Iris Iris.BI Iris.Std Iris.ProgramLogic T2c3
namespace T2c3
/-- One-step language on Bool: false steps to the value true. -/
@[instance_reducible] def oLang : Language Bool Unit Unit Unit where
  primStep := fun c o r => c.1 = false ∧ r.1 = true ∧ r.2.2 = [] ∧ o = []
  toVal := fun e => if e then some () else none
  ofVal := fun _ => true
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := fun _ => rfl
  val_stuck := by intro e σ obs e' σ' eₜ h; obtain ⟨h1, -⟩ := h; simp only at h1; subst h1; rfl
/-- IrisGS with real later credits, state interpretation True and a non-superadditive
number of credits per step: 100 at step count 0, 1 otherwise. -/
@[reducible] noncomputable def igL [x : InvGS_gen .hasLC GY] : @IrisGS_gen .hasLC Bool Unit Unit Unit oLang GY :=
  letI := oLang
  { invGS := x, stateInterp := fun _ _ _ _ => iprop(True), numLatersPerStep := fun n => if n = 0 then 100 else 1,
    forkPost := fun _ => iprop(True), stateInterp_mono := fun _ _ _ _ => fupd_intro }
/-- Running a WP of false at step count 1 turns 4 credits into the postcondition. -/
theorem runL [InvGS_gen .hasLC GY] {Φ : Unit → IProp GY} :
    letI := oLang; letI := igL;
    iprop(WP false @ Stuckness.MaybeStuck ; ⊤ {{ Φ }} ∗ £ 4) ⊢ iprop(|={⊤}=> Φ ()) := by
  letI := oLang; letI := igL
  have hv : (ToVal.toVal false : Option Unit) = none := rfl
  iintro ⟨Hw, H4⟩
  ihave Hw := wp_unfold.mp $$ Hw
  isimp only [wp.pre, hv] at Hw
  ispecialize Hw $$ %() %1 %([] : List Unit) %([] : List Unit) %0
  imod Hw $$ [] with ⟨_, Hst⟩
  · exact true_intro
  ihave H22 := (lc_split (PROP := IProp GY) (n := 2) (m := 2)).mp $$ H4
  icases H22 with ⟨Ha, Hb⟩
  have hn : IrisGS_gen.numLatersPerStep Bool Unit Unit Unit GY 1 = 1 := rfl
  isimp only [hn] at Hst
  ispecialize Hst $$ %true %() %([] : List Bool) [] Ha
  · ipureintro
    exact ⟨rfl, rfl, rfl, rfl⟩
  ihave Hst2 := (lc_fupd_add_step_fupdN (PROP := IProp GY) ∅ ∅ ⊤ _ 2) $$ Hb Hst
  imod Hst2 with ⟨_, Hv, _⟩
  ihave Hv2 := (wp_value_fupd' (s := .MaybeStuck) (E := ⊤) (Φ := Φ) (v := ())).mp $$ Hv
  iexact Hv2
end T2c3
-- `Iris.wp_credit_access` idx 14: necessary
theorem t2c3_12 : ¬ drop0% Iris.wp_credit_access 14 := fun h => by
  have key : ∀ [InvGS_gen .hasLC GY], ⊢ (letI := oLang; letI := igL;
      iprop(WP false @ Stuckness.MaybeStuck ; ⊤ {{ fun _ => (iprop(£ 102) : IProp GY) }}) : IProp GY) := fun {_} => by
    letI := oLang; letI := igL
    have h1 := @h .hasLC Bool Unit Unit Unit oLang GY igL .MaybeStuck ⊤ false (fun _ => (iprop(£ 102) : IProp GY)) (iprop(£ 100) : IProp GY) rfl
    have hv : (ToVal.toVal false : Option Unit) = none := rfl
    have hU : ⊢ (iprop(∀ (σ₁ : Unit) ns obs nt,
      stateInterp σ₁ ns obs nt ={⊤}=∗
      ∃ k m, stateInterp σ₁ m obs nt ∗ ⌜ns = m + k⌝ ∗ (
        ∀ nt (σ₂ : Unit) obs, £ (IrisGS_gen.numLatersPerStep Bool Unit Unit Unit GY k) -∗ stateInterp σ₂ (m+1) obs nt ={⊤}=∗
          stateInterp σ₂ (ns+1) obs nt ∗ £ 100)) : IProp GY) := by
      iintro %σ %ns %obs %nt _
      imodintro
      iexists 0, ns
      isplitr
      · exact true_intro
      isplitr
      · ipureintro; omega
      iintro %nt' %σ₂ %obs' Hc _
      imodintro
      isplitr
      · exact true_intro
      · have hn0 : IrisGS_gen.numLatersPerStep Bool Unit Unit Unit GY 0 = 100 := rfl
        isimp only [hn0] at Hc
        iexact Hc
    have hW : ⊢ iprop(WP false @ Stuckness.MaybeStuck ; ⊤ {{ fun _ => (iprop(£ 100 ={⊤}=∗ £ 102) : IProp GY) }}) := by
      iapply wp_unfold.mpr
      simp only [wp.pre, hv]
      iintro %σ %ns %obs %obs' %nt Hσ
      iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
      iintro Hcl
      isplitr
      · ipureintro; trivial
      iintro %e₂ %σ₂ %eₜ %Hs Hc
      obtain ⟨-, rfl, rfl, -⟩ := Hs
      have h2 : 2 ≤ IrisGS_gen.numLatersPerStep Bool Unit Unit Unit GY ns + 1 := by
        show 2 ≤ (if ns = 0 then 100 else 1) + 1
        split <;> omega
      ihave Hc2 := lc_weaken (PROP := IProp GY) 2 h2 $$ Hc
      iapply (step_fupdN_intro (Std.LawfulSet.subset_refl))
      iapply laterN_intro
      imod Hcl
      imodintro
      isplitr
      · exact true_intro
      isplitl [Hc2]
      · iapply (wp_value' (v := ()))
        iintro H100
        imodintro
        ihave H := (lc_split (PROP := IProp GY) (n := 100) (m := 2)).mpr $$ [H100 Hc2]
        · isplitl [H100]
          · iexact H100
          · iexact Hc2
        iexact H
      · iclear Hσ
        iclear Hcl
        exact BigSepL.bigSepL_nil.2
    iintro
    ihave HU := hU
    ihave HW := hW
    ihave K := h1 $$ HU
    iapply K
    iapply (wp_mono fun _ => ?_) $$ HW
    exact .rfl
  have L : ∀ [InvGS_gen .hasLC GY], ⊢ (iprop(£ 4 -∗ |={⊤}=> ⌜False⌝) : IProp GY) := fun {_} => by
    letI := oLang; letI := igL
    refine BI.true_intro.trans (loeb_weak ?_)
    iintro HP H4
    ihave G := (runL (Φ := fun _ => (iprop(£ 102) : IProp GY))) $$ [H4]
    · isplitl []
      · iapply key
      · iexact H4
    imod G
    ihave G2 := (lc_split (PROP := IProp GY) (n := 1) (m := 101)).mp $$ G
    icases G2 with ⟨H1, H101⟩
    ihave HP2 := (lc_fupd_elim_later (PROP := IProp GY) (E := ⊤)) $$ H1 HP
    imod HP2
    ihave H4' := (lc_weaken (PROP := IProp GY) 4 (by omega)) $$ H101
    iapply HP2 $$ H4'
  exact pure_soundness (PROP := IProp GY)
    (fupd_soundness .hasLC 4 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)) fun _ => L)

open OFE
universe u_1 u_2 u_3 u_4

/- Removable: total-WP induction does not need NonExpansive Ψ. Replace Ψ by its non-expansive
interior Ψ' x := ∀ y, (x ≡ y) -∗ Ψ y (internal equality); Ψ' ⊢ Ψ, and the induction premise
for Ψ' follows from the one for Ψ by rewriting along x ≡ y inside pre' (non-expansive on
non-expansive predicates) and monotonicity twp.pre_mono (no NE needed). -/
-- `Iris.twp.induction` idx 10: removable
theorem t2c3_1 : drop% Iris.twp.induction 10 := by
  intro hlc Expr State Obs Val Λ GF ι s Ψ
  letI : OFE CoPset := OFE.ofDiscrete _
  letI : OFE Expr := OFE.ofDiscrete _
  letI : OFE Val := OFE.ofDiscrete _
  let A := Iris.twp.Internal.Args Expr Val GF
  let Ψ' : CoPset → Expr → (Val → IProp GF) → IProp GF := fun E e Φ =>
    iprop(∀ y : A, internalEq (PROP := IProp GF) ((E, e, Φ) : A) y -∗ Ψ y.1 y.2.1 y.2.2)
  haveI hne : NonExpansive (fun x : A => Ψ' x.1 x.2.1 x.2.2) :=
    ⟨fun {_ _ _} h => forall_ne fun _ => wand_ne.ne ((internalEq.instInternalEq_ne _).ne h .rfl) .rfl⟩
  haveI hne2 : NonExpansive (fun x : A => iprop(Ψ' x.1 x.2.1 x.2.2 ∧ TotalWp.totalWp s x.1 x.2.1 x.2.2)) := by
    refine ⟨fun {n x y} h => and_ne.ne (hne.ne h) ?_⟩
    obtain ⟨E₁, e₁, Φ₁⟩ := x
    obtain ⟨E₂, e₂, Φ₂⟩ := y
    obtain ⟨hE, he, hΦ⟩ := h
    obtain rfl := show E₁ = E₂ from hE
    obtain rfl := show e₁ = e₂ from he
    exact Iris.twp.ne.ne hΦ
  have key := Iris.twp.induction (ι := ι) s Ψ'
  have h1 : ∀ E e Φ, Ψ' E e Φ ⊢ Ψ E e Φ := fun E e Φ =>
    (forall_elim ((E, e, Φ) : A)).trans ((wand_mono_left internalEq.refl).trans (emp_wand.1))
  have hrw : ∀ x y : A, iprop(internalEq (PROP := IProp GF) x y ∗
      Iris.twp.Internal.pre' s (fun z : A => iprop(Ψ' z.1 z.2.1 z.2.2 ∧ TotalWp.totalWp s z.1 z.2.1 z.2.2)) x) ⊢
      Iris.twp.Internal.pre' s (fun z : A => iprop(Ψ' z.1 z.2.1 z.2.2 ∧ TotalWp.totalWp s z.1 z.2.1 z.2.2)) y := by
    intro x y
    haveI := (Iris.twp.Internal.pre'_mono (ι := ι) s).mono_pred_ne (Φ := fun z : A => iprop(Ψ' z.1 z.2.1 z.2.2 ∧ TotalWp.totalWp s z.1 z.2.1 z.2.2))
    exact (sep_mono_left (internalEq.rewrite _)).trans (sep_and.trans imp_elim_left)
  iintro #IH %e %E %Φ Hw
  iapply h1
  ihave K := key
  iapply K $$ [] Hw
  imodintro
  iintro %e' %E' %Φ' Hpre %y Heq
  ihave H2 := hrw ((E', e', Φ') : A) y $$ [Heq Hpre]
  · isplitl [Heq]
    · iexact Heq
    · iexact Hpre
  iapply IH
  ihave M := Iris.twp.pre_mono (ι := ι) s (fun E e Φ => iprop(Ψ' E e Φ ∧ TotalWp.totalWp s E e Φ))
    (fun E e Φ => iprop(Ψ E e Φ ∧ TotalWp.totalWp s E e Φ))
  iapply M $$ [] H2
  imodintro
  iintro %E'' %e'' %Φ'' H3
  isplit
  · iapply h1
    iapply BI.and_elim_l $$ H3
  · iapply BI.and_elim_r $$ H3
