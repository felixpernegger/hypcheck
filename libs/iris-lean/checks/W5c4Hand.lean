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
namespace W5c4
open Iris Iris.BI Iris.OFE Iris.Std

section gen
variable {PROP : Type _} [Sbi PROP] {A : Type _} [OFE A] (R : A → A → PROP)

theorem rtc_intro (x₁ x₂ : A) : biRtcPre R x₂ (fun x => biRtc R x x₂) x₁ ⊢ biRtc R x₁ x₂ := by
  unfold biRtcPre biRtc
  iintro H %Φ #Hc
  iapply Hc
  iunfold biRtcPre
  icases H with ⟨H | ⟨%x', HR, Hr⟩⟩
  · ileft; iexact H
  · iright; iexists x'; iframe HR
    ispecialize Hr $$ %Φ
    iapply Hr; iexact Hc

theorem tc_intro (x₁ x₂ : A) : biTcPre R x₂ (fun x => biTc R x x₂) x₁ ⊢ biTc R x₁ x₂ := by
  unfold biTcPre biTc
  iintro H %Φ #Hc
  iapply Hc
  iunfold biTcPre
  icases H with ⟨H | ⟨%x', HR, Hr⟩⟩
  · ileft; iexact H
  · iright; iexists x'; iframe HR
    ispecialize Hr $$ %Φ
    iapply Hr; iexact Hc

theorem rtc_refl' (x : A) : ⊢ biRtc R x x :=
  (or_intro_left_trans (affinely_intro internalEq.refl)).trans (rtc_intro R x x)

theorem rtc_left' (x₁ x₂ x₃ : A) : R x₁ x₂ -∗ biRtc R x₂ x₃ -∗ biRtc R x₁ x₃ := by
  iintro H₁ H₂
  iapply rtc_intro
  unfold biRtcPre
  iright; iexists x₂; iframe

theorem rtc_once' (x₁ x₂ : A) : R x₁ x₂ -∗ biRtc R x₁ x₂ := by
  iintro H
  iapply rtc_left' $$ H
  iapply rtc_refl'

instance rtcNE (y : A) : NonExpansive (fun x => biRtc R x y) := NonExpansive₂.ne_left (biRtc R) y

theorem rtc_trans' (x₁ x₂ x₃ : A) :
    biRtc R x₁ x₂ -∗ biRtc R x₂ x₃ -∗ biRtc R x₁ x₃ := by
  irevert %x₁
  letI : NonExpansive (fun x => iprop(biRtc R x₂ x₃ -∗ biRtc R x x₃)) :=
    (NonExpansive₂.ne_right BIBase.wand (biRtc R x₂ x₃)).comp
      (NonExpansive₂.ne_left (biRtc R) x₃)
  iapply bi_rtc_ind_left
  iintro !> %x₁ ⟨Heq|⟨%x', HR, IH⟩⟩ H₂
  · irewrite [Heq]; itrivial
  · iapply rtc_left' R x₁ x' x₃ $$ HR
    iapply IH; itrivial

theorem rtc_right' (x y z : A) : biRtc R x y -∗ R y z -∗ biRtc R x z := by
  iintro Hrtc HR
  iapply rtc_trans' $$ Hrtc
  iapply rtc_once' $$ HR

instance tcNE (y : A) : NonExpansive (fun x => biTc R x y) :=
  inferInstanceAs (NonExpansive (bi_least_fixpoint (biTcPre R y)))

theorem tc_left' (x₁ x₂ x₃ : A) :
    R x₁ x₂ -∗ biTc R x₂ x₃ -∗ biTc R x₁ x₃ := by
  iintro H₁ H₂
  iapply tc_intro
  unfold biTcPre
  iright
  iexists x₂
  iframe

theorem tc_once' (x₁ x₂ : A) : R x₁ x₂ -∗ biTc R x₁ x₂ := by
  iintro H
  iapply tc_intro
  unfold biTcPre
  ileft
  iexact H

theorem tc_trans' (x₁ x₂ x₃ : A) :
    biTc R x₁ x₂ -∗ biTc R x₂ x₃ -∗ biTc R x₁ x₃ := by
  letI : NonExpansive (fun x => iprop(biTc R x₂ x₃ -∗ biTc R x x₃)) :=
    (NonExpansive₂.ne_right BIBase.wand (biTc R x₂ x₃)).comp (tcNE R x₃)
  irevert %x₁
  iapply bi_tc_ind_left
  iintro !> %x₁ ⟨H | ⟨%x', HR, IH⟩⟩ H₂
  · iapply tc_left' $$ H H₂
  · iapply tc_left' $$ HR
    iapply IH; itrivial

theorem tc_right' (x y z : A) : biTc R x y -∗ R y z -∗ biTc R x z := by
  iintro Htc HR
  iapply tc_trans' $$ Htc
  iapply tc_once'; itrivial

theorem tc_rtc_left' (x y z : A) : biRtc R x y -∗ biTc R y z -∗ biTc R x z := by
  letI : NonExpansive (fun x => iprop(biTc R y z -∗ biTc R x z)) :=
    (NonExpansive₂.ne_right BIBase.wand (biTc R y z)).comp (tcNE R z)
  irevert %x
  iapply bi_rtc_ind_left
  iintro !> %x ⟨Heq | ⟨%x', HR, IH⟩⟩ Hyz
  · irewrite [Heq]
    itrivial
  · iapply tc_left' $$ HR
    iapply IH; itrivial

theorem tc_rtc' (x y : A) : biTc R x y -∗ biRtc R x y := by
  letI : NonExpansive (fun x => biRtc R x y) := NonExpansive₂.ne_left (biRtc R) y
  irevert %x
  iapply bi_tc_ind_left
  iintro !> %x ⟨H | ⟨%x', HR, IH⟩⟩
  · iapply rtc_once'; itrivial
  · iapply rtc_left' $$ HR IH

theorem rtc_strong' (x₂ : A) (Φ : A → PROP) [NonExpansive Φ] :
    ⊢ □ (∀ x₁, <affine> (x₁ ≡ x₂) ∨ (∃ x', R x₁ x' ∗ (Φ x' ∧ biRtc R x' x₂)) -∗ Φ x₁) -∗
      ∀ x₁, biRtc R x₁ x₂ -∗ Φ x₁ := by
  letI : NonExpansive (fun x => iprop(Φ x ∧ biRtc R x x₂)) :=
    ⟨fun _ _ _ h => and_ne.ne (NonExpansive.ne h) (NonExpansive₂.ne_left (biRtc R) x₂ |>.ne h)⟩
  iintro #H %x₁ Hr
  ihave Hc := bi_rtc_ind_left R x₂ (fun x => iprop(Φ x ∧ biRtc R x x₂))
  ispecialize Hc $$ []
  · iintro !> %x Hx
    isplit
    · iapply H; iexact Hx
    · iapply rtc_intro; unfold biRtcPre
      icases Hx with ⟨Hx | ⟨%x', HR, Hb⟩⟩
      · ileft; iexact Hx
      · iright; iexists x'; iframe HR; icases Hb with ⟨-, Hb⟩; iexact Hb
  ispecialize Hc $$ %x₁ Hr
  icases Hc with ⟨Hc, -⟩
  iexact Hc

theorem tc_strong' (x₂ : A) (Φ : A → PROP) (hΦ : NonExpansive Φ) :
    ⊢ □ (∀ x₁, R x₁ x₂ ∨
        (∃ x', R x₁ x' ∗ (Φ x' ∧ biTc R x' x₂)) -∗ Φ x₁) -∗
      ∀ x₁, biTc R x₁ x₂ -∗ Φ x₁ := by
  letI : NonExpansive (fun x => iprop(Φ x ∧ biTc R x x₂)) :=
    ⟨fun _ _ _ h => and_ne.ne (NonExpansive.ne h) ((tcNE R x₂).ne h)⟩
  iintro #H %x₁ Hr
  ihave Hc := bi_tc_ind_left R x₂ (fun x => iprop(Φ x ∧ biTc R x x₂))
  ispecialize Hc $$ []
  · iintro !> %x Hx
    isplit
    · iapply H; iexact Hx
    · iapply tc_intro; unfold biTcPre
      icases Hx with ⟨Hx | ⟨%x', HR, Hb⟩⟩
      · ileft; iexact Hx
      · iright; iexists x'; iframe HR; icases Hb with ⟨-, Hb⟩; iexact Hb
  ispecialize Hc $$ %x₁ Hr
  icases Hc with ⟨Hc, -⟩
  iexact Hc

end gen

/-- Truncation OFE on naturals (copy of Probe1 TN): 1 and 2 agree at step 0. -/
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
theorem tn_dist {n} {x y : TN} : x ≡{n}≡ y ↔ min x.v (n+1) = min y.v (n+1) := Iff.rfl
theorem tn12 : (⟨1⟩ : TN) ≡{0}≡ ⟨2⟩ := rfl

theorem ieq_holds {A} [OFE A] {a b : A} {n} : (iprop(a ≡ b) : SiProp).holds n ↔ a ≡{n}≡ b := Iff.rfl
theorem aff_holds {P : SiProp} {n} : (iprop(<affine> P) : SiProp).holds n ↔ P.holds n :=
  ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- Relation true exactly when the source is 1 (not non-expansive on TN). -/
def R1 : TN → TN → SiProp := fun x _ => iprop(⌜x = ⟨1⟩⌝)

theorem r1_10 : ⊢ biRtc R1 ⟨1⟩ ⟨0⟩ := by
  ihave H := W5c4.rtc_left' R1 ⟨1⟩ ⟨0⟩ ⟨0⟩
  iapply H
  · unfold R1; ipureintro; rfl
  · iapply W5c4.rtc_refl'

theorem r1_20 : (biRtc R1 ⟨2⟩ ⟨0⟩).holds 0 :=
  ((rtcNE R1 ⟨0⟩).ne tn12 (Nat.le_refl 0)).mp (r1_10 0 trivial)

/-- Relation true exactly when the target is 1 (not non-expansive on TN). -/
def R2 : TN → TN → SiProp := fun _ y => iprop(⌜y = ⟨1⟩⌝)

theorem not_holds {P : SiProp} {n} (h : P ⊢ iprop(False)) : ¬ P.holds n := fun hp => h n hp

/-- Transitive closure of R2 towards 2 is empty. -/
theorem tc_r2_false (x : TN) : biTc R2 x ⟨2⟩ ⊢ iprop(False) := by
  iintro H
  ihave Hi := bi_tc_ind_left R2 ⟨2⟩ (fun _ => (iprop(False) : SiProp))
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    icases Hx with ⟨Hx | ⟨%x', -, Hf⟩⟩
    · unfold R2; icases Hx with %hx; cases hx
    · iexact Hf
  iapply Hi $$ %x H

theorem tc_r2_01 : ⊢ biTc R2 ⟨0⟩ ⟨1⟩ := by
  ihave H := W5c4.tc_once' R2 ⟨0⟩ ⟨1⟩
  iapply H
  unfold R2; ipureintro; rfl

theorem tc_r1_10 : ⊢ biTc R1 ⟨1⟩ ⟨0⟩ := by
  ihave H := W5c4.tc_once' R1 ⟨1⟩ ⟨0⟩
  iapply H
  unfold R1; ipureintro; rfl

theorem tc_r1_20 : (biTc R1 ⟨2⟩ ⟨0⟩).holds 0 :=
  ((tcNE R1 ⟨0⟩).ne tn12 (Nat.le_refl 0)).mp (tc_r1_10 0 trivial)

theorem rtc_r2_12 : (biRtc R2 ⟨1⟩ ⟨2⟩).holds 0 :=
  ((bi_rtc_ne R2).ne (Dist.rfl) tn12 (Nat.le_refl 0)).mp (rtc_refl' R2 ⟨1⟩ 0 trivial)

theorem rtc_r2_02 : (biRtc R2 ⟨0⟩ ⟨2⟩).holds 0 :=
  rtc_left' R2 ⟨0⟩ ⟨1⟩ ⟨2⟩ 0 trivial 0 (Nat.le_refl 0) rfl 0 (Nat.le_refl 0) rtc_r2_12

end W5c4

open W5c4 Iris Iris.BI Iris.OFE Iris.Std

-- `Iris.bi_rtc_unfold` idx 5: necessary (SiProp, TN, R x _ = ⌜x = 1⌝: biRtc R 2 0 holds at step 0 by non-expansiveness of biRtc, the unfolding does not)
theorem w5c4_1 : ¬ drop0% Iris.bi_rtc_unfold 5 := fun h => by
  have e := @h SiProp TN _ _ R1 ⟨2⟩ ⟨0⟩
  have h0 := r1_20
  rw [e] at h0
  unfold biRtcPre at h0
  simp [aff_holds, ieq_holds, tn_dist, R1] at h0

-- `Iris.bi_tc_unfold` idx 5: necessary (SiProp, TN, R x _ = ⌜x = 1⌝: biTc R 2 0 holds at step 0, the unfolding does not)
theorem w5c4_2 : ¬ drop0% Iris.bi_tc_unfold 5 := fun h => by
  have e := @h SiProp TN _ _ R1 ⟨2⟩ ⟨0⟩
  have h0 := tc_r1_20
  rw [e] at h0
  unfold biTcPre at h0
  simp [R1] at h0

-- `Iris.bi_rtc_inv` idx 5: necessary (SiProp, TN, R x _ = ⌜x = 1⌝, x = 2, z = 0)
theorem w5c4_3 : ¬ drop0% Iris.bi_rtc_inv 5 := fun h => by
  have h0 := @h SiProp TN _ _ R1 ⟨2⟩ ⟨0⟩ 0 trivial 0 (Nat.le_refl 0) r1_20
  simp [aff_holds, ieq_holds, tn_dist, R1] at h0

-- `Iris.bi_tc_ne` idx 5: necessary (SiProp, TN, R _ y = ⌜y = 1⌝: biTc R 0 1 holds, biTc R 0 2 is empty, 1 and 2 agree at step 0)
theorem w5c4_4 : ¬ drop0% Iris.bi_tc_ne 5 := fun h => by
  exact not_holds (tc_r2_false ⟨0⟩)
    (((@h SiProp TN _ _ R2).ne (n := 0) (x₁ := ⟨0⟩) (x₂ := ⟨0⟩) Dist.rfl tn12 (Nat.le_refl 0)).mp (tc_r2_01 0 trivial))

-- `Iris.instNonExpansiveBiTc` idx 5: necessary (SiProp, TN, R _ y = ⌜y = 1⌝: biTc R 0 1 holds, biTc R 0 2 is empty)
theorem w5c4_5 : ¬ drop0% Iris.instNonExpansiveBiTc 5 := fun h => by
  exact not_holds (tc_r2_false ⟨0⟩)
    (((@h SiProp TN _ _ R2 ⟨0⟩).ne (n := 0) tn12 (Nat.le_refl 0)).mp (tc_r2_01 0 trivial))

-- `Iris.bi_tc_rtc_right` idx 5: necessary (SiProp, TN, R _ y = ⌜y = 1⌝, x = 0, y = 1, z = 2: biRtc R 1 2 holds at step 0, biTc R 0 2 is empty)
theorem w5c4_6 : ¬ drop0% Iris.bi_tc_rtc_right 5 := fun h =>
  not_holds (tc_r2_false ⟨0⟩)
    (@h SiProp TN _ _ R2 ⟨0⟩ ⟨1⟩ ⟨2⟩ 0 trivial 0 (Nat.le_refl 0) (tc_r2_01 0 trivial) 0 (Nat.le_refl 0) rtc_r2_12)

-- `Iris.bi_rtc_tc` idx 5: necessary (SiProp, TN, R _ y = ⌜y = 1⌝, x = 0, y = 2: biRtc R 0 2 holds at step 0, the right side does not)
theorem w5c4_7 : ¬ drop0% Iris.bi_rtc_tc 5 := fun h => by
  have h0 := (@h SiProp TN _ _ R2 ⟨0⟩ ⟨2⟩).1 0 rtc_r2_02
  rcases h0 with h0 | h0
  · simp [aff_holds, ieq_holds, tn_dist] at h0
  · exact not_holds (tc_r2_false ⟨0⟩) h0

-- `Iris.bi_rtc_pre_mono` idx 5: necessary (SiProp, TN, R x _ = ⌜x = 1⌝, Φ = True: biRtcPre R 0 Φ holds at 1, not at 2, though 1 and 2 agree at step 0)
theorem w5c4_8 : ¬ drop0% Iris.bi_rtc_pre_mono 5 := fun h => by
  have e := ((@h SiProp TN _ _ R1 ⟨0⟩).mono_pred_ne (Φ := fun _ => iprop(True))).ne (n := 0) tn12 (Nat.le_refl 0)
  unfold biRtcPre at e
  simp [aff_holds, ieq_holds, tn_dist, R1] at e
  exact e ⟨0⟩

-- `Iris.bi_tc_pre_mono` idx 5: necessary (SiProp, TN, R x _ = ⌜x = 1⌝, Φ = False: biTcPre R 0 Φ holds at 1, not at 2)
theorem w5c4_9 : ¬ drop0% Iris.bi_tc_pre_mono 5 := fun h => by
  have e := ((@h SiProp TN _ _ R1 ⟨0⟩).mono_pred_ne (Φ := fun _ => iprop(False))).ne (n := 0) tn12 (Nat.le_refl 0)
  unfold biTcPre at e
  simp [R1] at e

-- `Iris.bi_nsteps_ne` idx 5: necessary (SiProp, TN, R x _ = ⌜x = 1⌝, n = 1: one step from 1 to 0 holds, from 2 not)
theorem w5c4_10 : ¬ drop0% Iris.bi_nsteps_ne 5 := fun h => by
  have e := (@h SiProp TN _ _ R1 1).ne (n := 0) (y₁ := ⟨0⟩) (y₂ := ⟨0⟩) tn12 Dist.rfl (Nat.le_refl 0)
  simp [biNsteps, aff_holds, ieq_holds, tn_dist, R1] at e

-- `Iris.bi_nsteps_once_inv` idx 5: necessary (SiProp, TN, R _ y = ⌜y = 1⌝, x = 0, y = 2: the step to 1 is 0-close to 2)
theorem w5c4_11 : ¬ drop0% Iris.bi_nsteps_once_inv 5 := fun h => by
  have h0 := @h SiProp TN _ _ R2 ⟨0⟩ ⟨2⟩ 0 trivial 0 (Nat.le_refl 0)
    (by simp [biNsteps, aff_holds, ieq_holds, tn_dist, R2])
  simp [R2] at h0

-- `Iris.bi_nsteps_trans` idx 5: necessary (SiProp, TN, R x _ = ⌜x = 1⌝, n = 0, m = 1, x = 2, y = 1, z = 0)
theorem w5c4_12 : ¬ drop0% Iris.bi_nsteps_trans 5 := fun h => by
  have h0 := @h SiProp TN _ _ R1 0 1 ⟨2⟩ ⟨1⟩ ⟨0⟩ 0 trivial 0 (Nat.le_refl 0)
    (by simp [biNsteps, aff_holds, ieq_holds, tn_dist]) 0 (Nat.le_refl 0)
    (by simp [biNsteps, aff_holds, ieq_holds, tn_dist, R1])
  simp [biNsteps, R1] at h0

-- `Iris.bi_nsteps_right` idx 5: necessary (SiProp, TN, R x _ = ⌜x = 1⌝, n = 0, x = 2, y = 1, z = 0)
theorem w5c4_13 : ¬ drop0% Iris.bi_nsteps_right 5 := fun h => by
  have h0 := @h SiProp TN _ _ R1 0 ⟨2⟩ ⟨1⟩ ⟨0⟩ 0 trivial 0 (Nat.le_refl 0)
    (by simp [biNsteps, aff_holds, ieq_holds, tn_dist]) 0 (Nat.le_refl 0)
    (by simp [R1])
  simp [biNsteps, R1] at h0

-- `Iris.bi_nsteps_inv_right` idx 5: necessary (SiProp, TN, R _ y = ⌜y = 1⌝, n = 0, x = 0, z = 2)
theorem w5c4_14 : ¬ drop0% Iris.bi_nsteps_inv_right 5 := fun h => by
  have h0 := (@h SiProp TN _ _ R2 0 ⟨0⟩ ⟨2⟩) 0
    (by simp [biNsteps, aff_holds, ieq_holds, tn_dist, R2])
  simp [biNsteps, R2] at h0

-- `Iris.bi_tc_nsteps` idx 5: necessary (SiProp, TN, R _ y = ⌜y = 1⌝, x = 0, y = 2: one step holds at step 0, biTc R 0 2 is empty)
theorem w5c4_15 : ¬ drop0% Iris.bi_tc_nsteps 5 := fun h =>
  not_holds (tc_r2_false ⟨0⟩) ((@h SiProp TN _ _ R2 ⟨0⟩ ⟨2⟩).2 0
    (SiProp.exists_holds.mpr ⟨1, by simp [biNsteps, aff_holds, ieq_holds, tn_dist, R2]⟩))

-- `Iris.bi_rtc_nsteps` idx 5: necessary (SiProp, TN, R x _ = ⌜x = 1⌝, x = 2, y = 0: biRtc R 2 0 holds at step 0, no step sequence from 2)
theorem w5c4_16 : ¬ drop0% Iris.bi_rtc_nsteps 5 := fun h => by
  have h0 := (@h SiProp TN _ _ R1 ⟨2⟩ ⟨0⟩).1 0 r1_20
  obtain ⟨k, hk⟩ := SiProp.exists_holds.mp h0
  cases k <;> simp [biNsteps, aff_holds, ieq_holds, tn_dist, R1] at hk

namespace W5c4
instance tn0disc : DiscreteE (⟨0⟩ : TN) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩

theorem prem_rtc : ⊢ (□ ∀ x₁ : TN, (<affine> (x₁ ≡ ⟨0⟩) ∨ ∃ x', R1 x₁ x' ∗ (⌜x' ≠ (⟨2⟩ : TN)⌝ : SiProp)) -∗
    (⌜x₁ ≠ ⟨2⟩⌝ : SiProp)) := by
  iintro !> %x₁ Hx
  icases Hx with ⟨Hx | ⟨%x', HR, -⟩⟩
  · ihave %e := (affinely_elim.trans (discrete_eq_mp (PROP := SiProp) (a := x₁) (b := (⟨0⟩ : TN)))) $$ Hx
    ipureintro; subst e; simp
  · unfold R1; icases HR with %e; ipureintro; subst e; simp

theorem prem_tc : ⊢ (□ ∀ x₁ : TN, (R1 x₁ ⟨0⟩ ∨ ∃ x', R1 x₁ x' ∗ (⌜x' ≠ (⟨2⟩ : TN)⌝ : SiProp)) -∗
    (⌜x₁ ≠ ⟨2⟩⌝ : SiProp)) := by
  iintro !> %x₁ Hx
  icases Hx with ⟨HR | ⟨%x', HR, -⟩⟩
  · unfold R1; icases HR with %e; ipureintro; subst e; simp
  · unfold R1; icases HR with %e; ipureintro; subst e; simp
end W5c4

-- `Iris.bi_rtc_ind_left` idx 7: necessary (SiProp, TN, R x _ = ⌜x = 1⌝, x₂ = 0, Φ x = ⌜x ≠ 2⌝ is closed under the step but biRtc R 2 0 holds at step 0)
theorem w5c4_17 : ¬ drop0% Iris.bi_rtc_ind_left 7 := fun h => by
  have h0 := @h SiProp TN _ _ R1 ⟨0⟩ (fun x => iprop(⌜x ≠ ⟨2⟩⌝)) 0 trivial 0 (Nat.le_refl 0) (prem_rtc 0 trivial)
  exact SiProp.forall_holds.mp h0 ⟨2⟩ 0 (Nat.le_refl 0) r1_20 rfl

-- `Iris.bi_tc_ind_left` idx 7: necessary (SiProp, TN, R x _ = ⌜x = 1⌝, x₂ = 0, Φ x = ⌜x ≠ 2⌝ is closed under the step but biTc R 2 0 holds at step 0)
theorem w5c4_18 : ¬ drop0% Iris.bi_tc_ind_left 7 := fun h => by
  have h0 := @h SiProp TN _ _ R1 ⟨0⟩ (fun x => iprop(⌜x ≠ ⟨2⟩⌝)) 0 trivial 0 (Nat.le_refl 0) (prem_tc 0 trivial)
  exact SiProp.forall_holds.mp h0 ⟨2⟩ 0 (Nat.le_refl 0) tc_r1_20 rfl

namespace W5c4
section gen2
variable {PROP : Type _} [Sbi PROP] {A : Type _} [OFE A] (R : A → A → PROP)

theorem rtc_pers' [∀ x y, Persistent (R x y)] (x y : A) : Persistent (biRtc R x y) where
  persistent := by
    letI : NonExpansive (fun x => iprop(<pers> biRtc R x y)) :=
      persistently_ne.comp (NonExpansive₂.ne_left (biRtc R) y)
    irevert %x
    iapply bi_rtc_ind_left
    iintro !> %x ⟨#Heq|⟨%x', #HR, #Hrtc⟩⟩
    · irewrite [Heq]
      iapply rtc_refl'
    · iapply rtc_left' $$ HR Hrtc

theorem tc_pers' [∀ x y, Persistent (R x y)] (x y : A) : Persistent (biTc R x y) where
  persistent := by
    letI : NonExpansive (fun x => iprop(<pers> biTc R x y)) :=
      persistently_ne.comp (tcNE R y)
    irevert %x
    iapply bi_tc_ind_left
    iintro !> %x ⟨#H | ⟨%x', #_, #_⟩⟩ !>
    · iapply tc_once' ; itrivial
    · iapply tc_left' <;> itrivial

theorem tc_abs' [∀ x y, Absorbing (R x y)] (x y : A) : Absorbing (biTc R x y) where
  absorbing := by
    iapply wand_elim_swap
    revert x
    letI _ : NonExpansive fun x => iprop(True -∗ biTc R x y) :=
      (NonExpansive₂.ne_right BIBase.wand iprop(True)).comp (tcNE R y)
    iapply bi_tc_ind_left
    iintro !> %x HF HT
    icases HF with ⟨H | ⟨%x', HR, IH⟩⟩
    · iapply tc_once'
      iclear HT
      iexact H
    · iapply tc_left' $$ HR
      iapply IH
      iexact HT
end gen2
end W5c4

-- `Iris.bi_rtc_refl` idx 5: removable (biRtc R x x is introduced by the left disjunct of the fixpoint; only closure of the fixpoint under its step is used, which needs no non-expansiveness of R)
theorem w5c4_19 : drop% Iris.bi_rtc_refl 5 := by
  intro PROP A _ _ R; exact rtc_refl' R

-- `Iris.bi_rtc_left` idx 5: removable (introduction rule of the least fixpoint, proved by unfolding its definition; no non-expansiveness of R needed)
theorem w5c4_20 : drop% Iris.bi_rtc_left 5 := by
  intro PROP A _ _ R; exact rtc_left' R

-- `Iris.bi_rtc_once` idx 5: removable (from the non-expansiveness-free refl and left rules)
theorem w5c4_21 : drop% Iris.bi_rtc_once 5 := by
  intro PROP A _ _ R; exact rtc_once' R

-- `Iris.bi_rtc_trans` idx 5: removable (induction on the first closure with a predicate non-expansive by bi_rtc_ne, which has no hypothesis; step by the hypothesis-free left rule)
theorem w5c4_22 : drop% Iris.bi_rtc_trans 5 := by
  intro PROP A _ _ R; exact rtc_trans' R

-- `Iris.bi_rtc_right` idx 5: removable (from the hypothesis-free trans and once rules)
theorem w5c4_23 : drop% Iris.bi_rtc_right 5 := by
  intro PROP A _ _ R; exact rtc_right' R

-- `Iris.bi_rtc_strong_ind_left` idx 5: removable (Φ ∧ biRtc R · x₂ is non-expansive and closed under the step, so plain induction applies; no non-expansiveness of R needed)
theorem w5c4_24 : drop% Iris.bi_rtc_strong_ind_left 5 := by
  intro PROP A _ _ R x₂ Φ _; exact rtc_strong' R x₂ Φ


-- `Iris.bi_rtc_persistent` idx 5: removable (the library induction goes through with the hypothesis-free refl and left rules)
theorem w5c4_26 : drop% Iris.bi_rtc_persistent 5 := by
  intro PROP A _ _ R _ x y; exact rtc_pers' R x y

-- `Iris.bi_tc_strong_ind_left` idx 5: removable (Φ ∧ biTc R · x₂ is non-expansive in the first argument without hypotheses and closed under the step)
theorem w5c4_27 : drop% Iris.bi_tc_strong_ind_left 5 := by
  intro PROP A _ _ R x₂ Φ hΦ; exact tc_strong' R x₂ Φ hΦ

-- `Iris.bi_tc_left` idx 5: removable (introduction rule of the least fixpoint, proved by unfolding its definition)
theorem w5c4_28 : drop% Iris.bi_tc_left 5 := by
  intro PROP A _ _ R; exact tc_left' R

-- `Iris.bi_tc_once` idx 5: removable (introduction rule of the least fixpoint, proved by unfolding its definition)
theorem w5c4_29 : drop% Iris.bi_tc_once 5 := by
  intro PROP A _ _ R; exact tc_once' R

-- `Iris.bi_tc_trans` idx 5: removable (induction on the first closure; biTc R · z is non-expansive in its first argument for every R)
theorem w5c4_30 : drop% Iris.bi_tc_trans 5 := by
  intro PROP A _ _ R; exact tc_trans' R

-- `Iris.bi_tc_right` idx 5: removable (from the hypothesis-free trans and once rules)
theorem w5c4_31 : drop% Iris.bi_tc_right 5 := by
  intro PROP A _ _ R; exact tc_right' R

-- `Iris.bi_tc_rtc_left` idx 5: removable (induction on biRtc; rewriting along x ≡ y only needs non-expansiveness of biTc R · z in its first argument, which holds for every R)
theorem w5c4_32 : drop% Iris.bi_tc_rtc_left 5 := by
  intro PROP A _ _ R; exact tc_rtc_left' R

-- `Iris.bi_tc_rtc` idx 5: removable (induction on biTc with the hypothesis-free once and left rules of biRtc)
theorem w5c4_33 : drop% Iris.bi_tc_rtc 5 := by
  intro PROP A _ _ R; exact tc_rtc' R


-- `Iris.bi_tc_absorbing` idx 5: removable (induction with True -∗ biTc R · y, non-expansive for every R; steps by the hypothesis-free once and left rules)
theorem w5c4_35 : drop% Iris.bi_tc_absorbing 5 := by
  intro PROP A _ _ R _ x y; exact tc_abs' R x y

-- `Iris.bi_tc_persistent` idx 5: removable (the library induction goes through with the hypothesis-free once and left rules)
theorem w5c4_36 : drop% Iris.bi_tc_persistent 5 := by
  intro PROP A _ _ R _ x y; exact tc_pers' R x y

namespace W5c4
/-- Two-element commutative monoid (e unit, a idempotent) with the equality order: a non-affine UORA (copy of Probe3 NA). -/
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

theorem na_true_not_emp : ¬ ((iprop(True) : UPred NA) ⊢ iprop(emp)) := fun h => by
  have H := h 0 ⟨.a, trivial⟩ trivial
  cases H

/-- Two-element monoid (e unit, a absorbing) with the extension order: an affine UORA (copy of Probe3 AF). -/
inductive AF | e | a deriving DecidableEq

def AF.op : AF → AF → AF
  | .e, y => y
  | .a, _ => .a

instance : OFE AF := OFE.ofDiscrete AF
instance : OFE.Discrete AF := ⟨id⟩

instance instORAAF : ORA AF := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := AF.op
  Valid := fun _ => True
  Order := fun x y => x = .e ∨ x = y
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := by intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all
  op_mono_left := by intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [AF.op]
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; exact .inl rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; exact .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact .inr rfl
  increasing_closed := by intro x y hx h z; cases x <;> cases y <;> cases z <;> simp_all [AF.op] }

instance : OrderRefl AF := ⟨fun x => show x = .e ∨ x = x from .inr rfl⟩

instance instUORAAF : UORA AF where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

instance : IncOrd AF := ⟨by
  intro x y ⟨z, hz⟩
  show x = .e ∨ x = y
  cases x <;> cases z <;> simp_all [Op.op, AF.op]⟩

theorem af_not_pers : ¬ Persistent (UPred.ownM AF.a) := fun h => by
  have H := h.persistent 0 ⟨AF.a, trivial⟩ (.inr rfl)
  rcases H with H | H <;> cases H

instance ne2const {PROP : Type _} [BI PROP] {A : Type _} [OFE A] (P : PROP) :
    NonExpansive₂ (fun (_ _ : A) => P) := by constructor; intros; exact Dist.rfl

def RT : Unit → Unit → UPred NA := fun _ _ => iprop(True)
def RE : Unit → Unit → UPred NA := fun _ _ => iprop(emp)
def RA : Unit → Unit → UPred AF := fun _ _ => UPred.ownM AF.a
def RAT : TN → TN → UPred AF := fun _ _ => UPred.ownM AF.a

theorem rt_tc : (iprop(True) : UPred NA) ⊢ biTc RT () () := wand_entails (tc_once' RT () ())

theorem rt_rtc : (iprop(True) : UPred NA) ⊢ biRtc RT () () :=
  sep_emp.mpr.trans ((sep_mono_right (rtc_refl' RT ())).trans (wand_elim (wand_entails (rtc_left' RT () () ()))))

instance : NonExpansive₂ RA := ne2const _
instance : NonExpansive₂ RAT := ne2const _
instance : NonExpansive₂ RE := ne2const _

theorem re_tc : biTc RE () () ⊢ iprop(emp) := by
  iintro H
  ihave Hi := bi_tc_ind_left RE () (fun _ => (iprop(emp) : UPred NA))
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    unfold RE
    icases Hx with ⟨Hx | ⟨%x', Hx, Hy⟩⟩
    · iexact Hx
    · iexact Hy
  iapply Hi $$ %() H

theorem ra_tc : biTc RA () () ⊢ UPred.ownM AF.a := by
  iintro H
  ihave Hi := bi_tc_ind_left RA () (fun _ => UPred.ownM AF.a)
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    unfold RA
    icases Hx with ⟨Hx | ⟨%x', Hx, -⟩⟩
    · iexact Hx
    · iexact Hx
  iapply Hi $$ %() H

theorem rat_rtc : biRtc RAT ⟨1⟩ ⟨0⟩ ⊢ UPred.ownM AF.a := by
  letI : NonExpansive (fun x : TN => iprop(UPred.ownM AF.a ∨ <affine> (x ≡ ⟨0⟩))) :=
    ⟨fun _ _ _ h => or_ne.ne .rfl (affinely_ne.ne ((internalEq.ne_l _).ne h))⟩
  iintro H
  ihave Hi := bi_rtc_ind_left RAT ⟨0⟩ (fun x : TN => iprop(UPred.ownM AF.a ∨ <affine> (x ≡ ⟨0⟩)))
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    unfold RAT
    icases Hx with ⟨Hx | ⟨%x', Hx, -⟩⟩
    · iright; iexact Hx
    · ileft; iexact Hx
  ispecialize Hi $$ %⟨1⟩ H
  icases Hi with ⟨Hi | Hi⟩
  · iexact Hi
  · ihave %e := (affinely_elim.trans (discrete_eq_mp (PROP := UPred AF) (a := (⟨1⟩ : TN)) (b := (⟨0⟩ : TN)))) $$ Hi
    cases e
end W5c4

-- `Iris.bi_rtc_affine` idx 5: necessary (UPred NA non-affine, A = Unit, R = True: True ⊢ R ∗ biRtc R () () ⊢ biRtc R () (), so affinity would give True ⊢ emp)
theorem w5c4_25 : ¬ drop0% Iris.bi_rtc_affine 5 := fun h =>
  na_true_not_emp (rt_rtc.trans (@h (UPred NA) Unit _ _ RT () ()).affine)

-- `Iris.bi_tc_affine` idx 5: necessary (UPred NA non-affine, A = Unit, R = True: True ⊢ biTc R () (), so affinity would give True ⊢ emp)
theorem w5c4_34 : ¬ drop0% Iris.bi_tc_affine 5 := fun h =>
  na_true_not_emp (rt_tc.trans (@h (UPred NA) Unit _ _ RT () ()).affine)

-- `Iris.bi_tc_absorbing` idx 6: necessary (UPred NA non-affine, A = Unit, R = emp: biTc R () () ⊣⊢ emp, and emp is not absorbing)
theorem w5c4_37 : ¬ drop0% Iris.bi_tc_absorbing 6 := fun h =>
  na_true_not_emp (((sep_emp.mpr).trans ((sep_mono_right (wand_entails (tc_once' RE () ()))).trans
    (@h (UPred NA) Unit _ _ RE _ () ()).absorbing)).trans re_tc)

-- `Iris.bi_tc_persistent` idx 6: necessary (affine UPred AF, A = Unit, R = ownM a: biTc R () () ⊣⊢ ownM a, which is not persistent)
theorem w5c4_38 : ¬ drop0% Iris.bi_tc_persistent 6 := fun h =>
  af_not_pers ⟨(wand_entails (tc_once' RA () ())).trans
    (((@h (UPred AF) Unit _ _ RA _ () ()).persistent).trans (persistently_mono ra_tc))⟩

-- `Iris.bi_rtc_persistent` idx 6: necessary (affine UPred AF, A = TN, R = ownM a, x = 1, y = 0: biRtc R 1 0 ⊣⊢ ownM a, which is not persistent)
theorem w5c4_39 : ¬ drop0% Iris.bi_rtc_persistent 6 := fun h =>
  af_not_pers ⟨(sep_emp.mpr.trans ((sep_mono_right (rtc_refl' RAT ⟨0⟩)).trans (wand_elim (wand_entails (rtc_left' RAT ⟨1⟩ ⟨0⟩ ⟨0⟩))))).trans
    (((@h (UPred AF) TN _ _ RAT _ ⟨1⟩ ⟨0⟩).persistent).trans (persistently_mono rat_rtc))⟩

namespace W5c4
/-- SiProp true only at step 0 (not timeless). -/
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩

def RF : TN → TN → SiProp := fun _ _ => iprop(False)
instance : NonExpansive₂ RF := ne2const _
instance (x y : TN) : Timeless (RF x y) := by unfold RF; infer_instance
def RS : Unit → Unit → SiProp := fun _ _ => s0
instance : NonExpansive₂ RS := ne2const _
def RSB : DiscreteO Bool → DiscreteO Bool → SiProp := fun _ _ => s0
instance : NonExpansive₂ RSB := ne2const _

instance : Timeless (iprop(emp) : SiProp) := ⟨fun n h => by
  cases n with
  | zero => exact .inr trivial
  | succ n => exact .inr trivial⟩

theorem rf_rtc (x : TN) : biRtc RF x ⟨2⟩ ⊢ iprop(x ≡ ⟨2⟩) := by
  letI : NonExpansive (fun x : TN => (iprop(x ≡ ⟨2⟩) : SiProp)) := internalEq.ne_l _
  iintro H
  ihave Hi := bi_rtc_ind_left RF ⟨2⟩ (fun x : TN => (iprop(x ≡ ⟨2⟩) : SiProp))
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    unfold RF
    icases Hx with ⟨Hx | ⟨%x', Hx, -⟩⟩
    · iexact Hx
    · icases Hx with %Hx; exact Hx.elim
  iapply Hi $$ %x H

theorem rs_tc : biTc RS () () ⊢ s0 := by
  iintro H
  ihave Hi := bi_tc_ind_left RS () (fun _ => s0)
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    unfold RS
    icases Hx with ⟨Hx | ⟨%x', Hx, -⟩⟩
    · iexact Hx
    · iexact Hx
  iapply Hi $$ %() H

theorem rsb_rtc : biRtc RSB ⟨true⟩ ⟨false⟩ ⊢ s0 := by
  iintro H
  ihave Hi := bi_rtc_ind_left RSB ⟨false⟩ (fun x => iprop(s0 ∨ <affine> (x ≡ ⟨false⟩)))
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    unfold RSB
    icases Hx with ⟨Hx | ⟨%x', Hx, -⟩⟩
    · iright; iexact Hx
    · ileft; iexact Hx
  ispecialize Hi $$ %⟨true⟩ H
  icases Hi with ⟨Hi | Hi⟩
  · iexact Hi
  · ihave %e := (affinely_elim.trans (discrete_eq_mp (PROP := SiProp) (a := (⟨true⟩ : DiscreteO Bool)) (b := ⟨false⟩))) $$ Hi
    cases e

theorem ne_of_disc {PROP : Type _} [Sbi PROP] {A : Type _} [OFE A] [OFE.Discrete A] (R : A → A → PROP) :
    NonExpansive₂ R := by
  constructor
  intro n x₁ x₂ hx y₁ y₂ hy
  have e1 : x₁ = x₂ := OFE.Discrete.discrete_0 (hx.le (Nat.zero_le n))
  have e2 : y₁ = y₂ := OFE.Discrete.discrete_0 (hy.le (Nat.zero_le n))
  subst e1; subst e2; exact Dist.rfl
end W5c4

-- `Iris.bi_nsteps_timeless` idx 5: necessary (SiProp, non-discrete TN, R = False, n = 0: biNsteps R 0 1 2 = <affine> (1 ≡ 2) holds only at step 0)
theorem w5c4_40 : ¬ drop0% Iris.bi_nsteps_timeless 5 := fun h => by
  have H := (@h SiProp TN _ _ _ RF 0 _ ⟨1⟩ ⟨2⟩).timeless 1 (by simp [biNsteps, aff_holds, ieq_holds, tn_dist])
  rcases H with H | H
  · exact H
  · simp [biNsteps, aff_holds, ieq_holds, tn_dist] at H

-- `Iris.bi_rtc_timeless` idx 5: necessary (SiProp, non-discrete TN, R = False: biRtc R 1 2 holds at step 0 (1 ≡{0}≡ 2), implies 1 ≡ 2, false at step 1)
theorem w5c4_41 : ¬ drop0% Iris.bi_rtc_timeless 5 := fun h => by
  have H := (@h SiProp TN _ _ _ RF _ _ ⟨1⟩ ⟨2⟩).timeless 1
    (show (biRtc RF ⟨1⟩ ⟨2⟩).holds 0 from
      ((bi_rtc_ne RF).ne (Dist.rfl) tn12 (Nat.le_refl 0)).mp (rtc_refl' RF ⟨1⟩ 0 trivial))
  rcases H with H | H
  · exact H
  · have := rf_rtc ⟨1⟩ 1 H
    simp [ieq_holds, tn_dist] at this

-- `Iris.bi_nsteps_timeless` idx 8: necessary (SiProp, A = Unit, R = s0 true only at step 0, n = 1)
theorem w5c4_42 : ¬ drop0% Iris.bi_nsteps_timeless 8 := fun h => by
  have H := (@h SiProp Unit _ _ _ _ RS 1 () ()).timeless 1
    (by simp [biNsteps, aff_holds, ieq_holds, RS, s0])
  rcases H with H | H
  · exact H
  · simp [biNsteps, RS, s0] at H

-- `Iris.bi_tc_timeless` idx 8: necessary (SiProp, A = Unit, R = s0 true only at step 0: biTc R () () ⊣⊢ s0)
theorem w5c4_43 : ¬ drop0% Iris.bi_tc_timeless 8 := fun h => by
  have H := (@h SiProp Unit _ _ _ _ RS _ () ()).timeless 1
    (show (biTc RS () ()).holds 0 from tc_once' RS () () 0 trivial 0 (Nat.le_refl 0) rfl)
  rcases H with H | H
  · exact H
  · exact absurd (rs_tc 1 H) (by simp [s0])

-- `Iris.bi_rtc_timeless` idx 8: necessary (SiProp, A = DiscreteO Bool, R = s0 true only at step 0: biRtc R true false ⊣⊢ s0)
theorem w5c4_44 : ¬ drop0% Iris.bi_rtc_timeless 8 := fun h => by
  have H := (@h SiProp (DiscreteO Bool) _ _ _ _ RSB _ ⟨true⟩ ⟨false⟩).timeless 1
    (show (biRtc RSB ⟨true⟩ ⟨false⟩).holds 0 from
      rtc_left' RSB ⟨true⟩ ⟨false⟩ ⟨false⟩ 0 trivial 0 (Nat.le_refl 0) rfl 0 (Nat.le_refl 0) (rtc_refl' RSB ⟨false⟩ 0 trivial))
  rcases H with H | H
  · exact H
  · exact absurd (rsb_rtc 1 H) (by simp [s0])

-- `Iris.bi_tc_timeless` idx 7: removable (derivable: OFE.Discrete A with Leibniz equality makes every R non-expansive)
theorem w5c4_45 : drop% Iris.bi_tc_timeless 7 := by
  intro PROP A _ _ _ _ R _ x y
  exact @bi_tc_timeless PROP A _ _ _ _ R (ne_of_disc R) _ x y

namespace W5c4
/-- Every slot is the mono-nat functor (copy of Probe3 GFmn). -/
def GFmn : BundledGFunctors := fun _ => ⟨MonoNatRF⟩

instance monoZG_GFmn : MonoZG GFmn where
  natG := { elem := { τ := 0, transp := rfl }, name := 0 }

/-- An update to `⌜False⌝` cannot be valid (copy of Probe3). -/
theorem bupd_false_unsound {GF : BundledGFunctors} (H : ⊢ (|==> iprop(⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF) (UPred.bupd_soundness H)

/-- Every slot is the mono-list functor over `Unit` (copy of Probe3 GFml). -/
def GFml : BundledGFunctors := fun _ => ⟨constOF (MonoList (DiscreteO Unit))⟩

instance monoListG_GFml : MonoListG GFml Unit where
  elem := { τ := 0, transp := rfl }
end W5c4

-- `Iris.MonoNat.lb_own_le` idx 5: necessary (GF with mono-nat slots: allocate ●0 ∗ ◯0, weaken ◯0 to ◯1, auth_lb_own_valid gives 1 ≤ 0; an update to False is unsound)
theorem w5c4_46 : ¬ drop0% Iris.MonoNat.lb_own_le 5 := fun h => bupd_false_unsound (GF := GFmn) (by
  imod (MonoNat.own_alloc (GF := GFmn) 0) with ⟨%γ, Ha, Hl⟩
  ihave Hl' := (@h GFmn _ γ 0 1) $$ Hl
  ihave %Hv := MonoNat.auth_lb_own_valid γ _ _ _ $$ Ha Hl'
  exfalso
  exact absurd Hv.2 (by show ¬ ((1 : Nat) ≤ 0); decide))

-- `Iris.MonoNat.own_alloc_strong` idx 4: necessary (P = False: the update would produce ⌜False⌝)
theorem w5c4_47 : ¬ drop0% Iris.MonoNat.own_alloc_strong 4 := fun h => bupd_false_unsound (GF := GFmn) (by
  imod (@h GFmn _ (fun _ => False) 0) with ⟨%γ, %f, -⟩
  exact f.elim)

-- `Iris.MonoNat.own_update` idx 5: necessary (allocate ●1 ∗ ◯1, update ●1 to ●0, then ●0 and ◯1 contradict auth_lb_own_valid)
theorem w5c4_48 : ¬ drop0% Iris.MonoNat.own_update 5 := fun h => bupd_false_unsound (GF := GFmn) (by
  imod (MonoNat.own_alloc (GF := GFmn) 1) with ⟨%γ, Ha, Hl⟩
  imod (@h GFmn _ γ 1 0) $$ Ha with ⟨Ha, -⟩
  ihave %Hv := MonoNat.auth_lb_own_valid γ _ _ _ $$ Ha Hl
  exfalso
  exact absurd Hv.2 (by show ¬ ((1 : Nat) ≤ 0); decide))

-- `Iris.MonoZ.lb_own_le` idx 5: necessary (allocate ●0 ∗ ◯0, weaken to ◯1, auth_lb_own_valid gives 1 ≤ 0)
theorem w5c4_49 : ¬ drop0% Iris.MonoZ.lb_own_le 5 := fun h => bupd_false_unsound (GF := GFmn) (by
  imod (MonoZ.own_alloc (GF := GFmn) 0 (by decide)) with ⟨%γ, Ha, Hl⟩
  ihave Hl' := (@h GFmn _ γ 0 1 (by decide)) $$ Hl
  ihave %Hv := MonoZ.auth_lb_own_valid γ _ _ _ $$ Ha Hl'
  exfalso
  omega)

-- `Iris.MonoZ.lb_own_le` idx 6: necessary (n = 0, n' = -1: ◯MZ (-1) carries ⌜0 ≤ -1⌝; ◯MZ 0 is obtained by lb_own_0)
theorem w5c4_50 : ¬ drop0% Iris.MonoZ.lb_own_le 6 := fun h => bupd_false_unsound (GF := GFmn) (by
  imod (MonoZ.lb_own_0 (GF := GFmn) 0) with Hl
  ihave Hl' := (@h GFmn _ 0 0 (-1) (by decide)) $$ Hl
  unfold MonoZ.lb_own
  icases Hl' with ⟨%f, -⟩
  exfalso
  omega)

-- `Iris.MonoZ.own_update` idx 5: necessary (allocate ●1 ∗ ◯1, update ●1 to ●0, then ●0 and ◯1 contradict auth_lb_own_valid)
theorem w5c4_51 : ¬ drop0% Iris.MonoZ.own_update 5 := fun h => bupd_false_unsound (GF := GFmn) (by
  imod (MonoZ.own_alloc (GF := GFmn) 1 (by decide)) with ⟨%γ, Ha, Hl⟩
  imod (@h GFmn _ γ 1 0) $$ Ha with ⟨Ha, -⟩
  ihave %Hv := MonoZ.auth_lb_own_valid γ _ _ _ $$ Ha Hl
  exfalso
  omega)

-- `Iris.MonoList.lb_own_le` idx 6: necessary (GF with mono-list slots over Unit: allocate ●[] ∗ ◯[], weaken to ◯[()], auth_lb_own_valid gives [()] <+: [])
theorem w5c4_52 : ¬ drop0% Iris.MonoList.lb_own_le 6 := fun h => bupd_false_unsound (GF := GFml) (by
  imod (MonoList.own_alloc (GF := GFml) ([] : List Unit)) with ⟨%γ, Ha, Hl⟩
  ihave Hl' := (@h GFml Unit _ γ [] [()]) $$ Hl
  ihave %Hv := MonoList.auth_lb_own_valid γ _ _ _ $$ Ha Hl'
  exfalso
  simp at Hv)

-- `Iris.MonoList.idx_own_get` idx 7: necessary (allocate ●[] ∗ ◯[], get ◯ML[0] (), auth_idx_lookup gives [][0]? = some ())
theorem w5c4_53 : ¬ drop0% Iris.MonoList.idx_own_get 7 := fun h => bupd_false_unsound (GF := GFml) (by
  imod (MonoList.own_alloc (GF := GFml) ([] : List Unit)) with ⟨%γ, Ha, Hl⟩
  ihave Hl' := (@h GFml Unit _ γ [] 0 ()) $$ Hl
  ihave %Hv := MonoList.auth_idx_lookup γ _ _ _ _ $$ Ha Hl'
  exfalso
  simp at Hv)

namespace W5c4
abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare

/-- Every slot is the ghost-map functor for prophecy maps over Nat keys and Nat values. -/
def GFpm : BundledGFunctors := fun _ => ⟨constOF (HeapView Nat (Agree (DiscreteO (List Nat))) TM)⟩

instance pmPre : prophMapPreS Nat Nat GFpm TM := ⟨⟨{ τ := 0, transp := rfl }⟩⟩
end W5c4

-- `Iris.resolves_insert` idx 8: necessary (P = V = Nat, ExtTreeMap, pvs = [], R = {1 ↦ [0]}, p = 0: key 1 still maps to [0], not to the empty resolution list)
theorem w5c4_54 : ¬ drop0% Iris.resolves_insert 8 := fun h => by
  have := @h Nat Nat TM _ _ [] 0 (PartialMap.insert (∅ : TM (List Nat)) 1 [0]) 1 [0] (by
    rw [Iris.Std.LawfulPartialMap.get?_insert_ne (by decide), Iris.Std.LawfulPartialMap.get?_insert_eq rfl])
  simp [prophListResolves] at this

-- `Iris.ProphMap.new_proph` idx 12: necessary (GF with a ghost-map slot: init, create prophecy 0 legally, then again with 0 already used: two proph 0 contradict proph_exclusive)
theorem w5c4_55 : ¬ drop0% Iris.ProphMap.new_proph 12 := fun h => bupd_false_unsound (GF := GFpm) (by
  imod (ProphMap.init (GF := GFpm) (P := Nat) (V := Nat) (H := TM) ([] : ProphValList Nat Nat)
    (∅ : Std.ExtTreeSet Nat compare)) with ⟨%G, Hi⟩
  imod (@ProphMap.new_proph GFpm Nat Nat TM _ (Std.ExtTreeSet Nat compare) _ G _ 0 ∅ [] LawfulSet.mem_empty) $$ Hi with ⟨Hi, Hp1⟩
  imod (@h GFpm Nat Nat TM _ (Std.ExtTreeSet Nat compare) _ G _ 0 ({0} ∪ ∅) []) $$ Hi with ⟨-, Hp2⟩
  ihave %f := proph_exclusive (GF := GFpm) (P := Nat) (V := Nat) (H := TM) 0 _ _ $$ Hp1 Hp2
  exact f.elim)

namespace W5c4
section iter
variable {PROP : Type _} [Sbi PROP] {A : Type _} [OFE A] (R : A → A → PROP)

/-- Finite unrollings of the transitive-closure step. -/
def itT (x₂ : A) : Nat → A → PROP
  | 0, _ => iprop(False)
  | k+1, x => iprop(R x x₂ ∨ ∃ x', R x x' ∗ itT x₂ k x')

theorem itT_ne [NonExpansive₂ R] (x₂ : A) (k : Nat) : NonExpansive (itT R x₂ k) := by
  induction k with
  | zero => constructor; intros; exact Dist.rfl
  | succ k ih =>
    constructor; intro n x y h
    exact or_ne.ne (NonExpansive₂.ne h .rfl) (exists_ne fun _ => sep_ne.ne (NonExpansive₂.ne h .rfl) .rfl)

theorem muT_ne [NonExpansive₂ R] (x₂ : A) : NonExpansive (fun x => iprop(∃ k, itT R x₂ k x)) := by
  constructor; intro n x y h
  exact exists_ne fun k => (itT_ne R x₂ k).ne h

theorem tc_le_muT [NonExpansive₂ R] (x₂ x : A) : biTc R x x₂ ⊢ iprop(∃ k, itT R x₂ k x) := by
  letI := muT_ne R x₂
  iintro H
  ihave Hi := bi_tc_ind_left R x₂ (fun x => iprop(∃ k, itT R x₂ k x))
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    icases Hx with ⟨Hx | ⟨%x', HR, Hk⟩⟩
    · iexists 1; simp only [itT]; ileft; iexact Hx
    · icases Hk with ⟨%k, Hk⟩
      iexists k+1; simp only [itT]; iright; iexists x'; iframe
  iapply Hi $$ %x H

theorem itT_le_tc (x₂ : A) (k : Nat) : ∀ x, itT R x₂ k x ⊢ biTc R x x₂ := by
  induction k with
  | zero => intro x; simp only [itT]; exact false_elim
  | succ k ih =>
    intro x
    simp only [itT]
    iintro H
    iapply tc_intro
    unfold biTcPre
    icases H with ⟨H | ⟨%x', HR, Hk⟩⟩
    · ileft; iexact H
    · iright; iexists x'; iframe HR; iapply (ih x'); iexact Hk

theorem itT_le_phi (x₂ : A) (Φ : A → PROP) (k : Nat) :
    iprop(□ (∀ x₁, R x₁ x₂ ∨ (∃ x', R x₁ x' ∗ (Φ x' ∧ biTc R x' x₂)) -∗ Φ x₁)) ⊢
      ∀ x, itT R x₂ k x -∗ Φ x := by
  induction k with
  | zero => iintro #H %x Hx; simp only [itT]; icases Hx with %f; exact f.elim
  | succ k ih =>
    iintro #H %x Hx
    ihave #IH := ih $$ H
    simp only [itT]
    iapply H
    icases Hx with ⟨Hx | ⟨%x', HR, Hk⟩⟩
    · ileft; iexact Hx
    · iright; iexists x'; iframe HR
      isplit
      · iapply IH $$ Hk
      · iapply (itT_le_tc R x₂ k x'); iexact Hk

theorem tc_strong_noNE [NonExpansive₂ R] (x₂ : A) (Φ : A → PROP) :
    ⊢ □ (∀ x₁, R x₁ x₂ ∨
        (∃ x', R x₁ x' ∗ (Φ x' ∧ biTc R x' x₂)) -∗ Φ x₁) -∗
      ∀ x₁, biTc R x₁ x₂ -∗ Φ x₁ := by
  iintro #H %x₁ Hb
  ihave Hm := (tc_le_muT R x₂ x₁) $$ Hb
  icases Hm with ⟨%k, Hk⟩
  ihave Hl := (itT_le_phi R x₂ Φ k) $$ H
  iapply Hl $$ Hk

instance itT_timeless [∀ x y, Timeless (R x y)] (x₂ : A) (k : Nat) (x : A) : Timeless (itT R x₂ k x) := by
  induction k generalizing x with
  | zero => simp only [itT]; infer_instance
  | succ k ih => simp only [itT]; infer_instance

theorem tc_eq_muT [NonExpansive₂ R] (x x₂ : A) : biTc R x x₂ = iprop(∃ k, itT R x₂ k x) :=
  BIBase.BiEntails.to_eq ⟨tc_le_muT R x₂ x, exists_elim fun k => itT_le_tc R x₂ k x⟩

theorem tc_timeless' [NonExpansive₂ R] [∀ x y, Timeless (R x y)] (x y : A) : Timeless (biTc R x y) := by
  rw [tc_eq_muT]; infer_instance


/-- Finite unrollings of the reflexive-transitive-closure step. -/
def itR (x₂ : A) : Nat → A → PROP
  | 0, _ => iprop(False)
  | k+1, x => iprop(<affine> (x ≡ x₂) ∨ ∃ x', R x x' ∗ itR x₂ k x')

theorem itR_ne [NonExpansive₂ R] (x₂ : A) (k : Nat) : NonExpansive (itR R x₂ k) := by
  induction k with
  | zero => constructor; intros; exact Dist.rfl
  | succ k ih =>
    constructor; intro n x y h
    exact or_ne.ne (affinely_ne.ne ((internalEq.ne_l x₂).ne h)) (exists_ne fun _ => sep_ne.ne (NonExpansive₂.ne h .rfl) .rfl)

theorem muR_ne [NonExpansive₂ R] (x₂ : A) : NonExpansive (fun x => iprop(∃ k, itR R x₂ k x)) := by
  constructor; intro n x y h
  exact exists_ne fun k => (itR_ne R x₂ k).ne h

theorem rtc_le_muR [NonExpansive₂ R] (x₂ x : A) : biRtc R x x₂ ⊢ iprop(∃ k, itR R x₂ k x) := by
  letI := muR_ne R x₂
  iintro H
  ihave Hi := bi_rtc_ind_left R x₂ (fun x => iprop(∃ k, itR R x₂ k x))
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    icases Hx with ⟨Hx | ⟨%x', HR, Hk⟩⟩
    · iexists 1; simp only [itR]; ileft; iexact Hx
    · icases Hk with ⟨%k, Hk⟩
      iexists k+1; simp only [itR]; iright; iexists x'; iframe
  iapply Hi $$ %x H

theorem itR_le_rtc (x₂ : A) (k : Nat) : ∀ x, itR R x₂ k x ⊢ biRtc R x x₂ := by
  induction k with
  | zero => intro x; simp only [itR]; exact false_elim
  | succ k ih =>
    intro x
    simp only [itR]
    iintro H
    iapply rtc_intro
    unfold biRtcPre
    icases H with ⟨H | ⟨%x', HR, Hk⟩⟩
    · ileft; iexact H
    · iright; iexists x'; iframe HR; iapply (ih x'); iexact Hk

theorem itR_le_phi (x₂ : A) (Φ : A → PROP) (k : Nat) :
    iprop(□ (∀ x₁, <affine> (x₁ ≡ x₂) ∨ (∃ x', R x₁ x' ∗ (Φ x' ∧ biRtc R x' x₂)) -∗ Φ x₁)) ⊢
      ∀ x, itR R x₂ k x -∗ Φ x := by
  induction k with
  | zero => iintro #H %x Hx; simp only [itR]; icases Hx with %f; exact f.elim
  | succ k ih =>
    iintro #H %x Hx
    ihave #IH := ih $$ H
    simp only [itR]
    iapply H
    icases Hx with ⟨Hx | ⟨%x', HR, Hk⟩⟩
    · ileft; iexact Hx
    · iright; iexists x'; iframe HR
      isplit
      · iapply IH $$ Hk
      · iapply (itR_le_rtc R x₂ k x'); iexact Hk

theorem rtc_strong_noNE [NonExpansive₂ R] (x₂ : A) (Φ : A → PROP) :
    ⊢ □ (∀ x₁, <affine> (x₁ ≡ x₂) ∨ (∃ x', R x₁ x' ∗ (Φ x' ∧ biRtc R x' x₂)) -∗ Φ x₁) -∗
      ∀ x₁, biRtc R x₁ x₂ -∗ Φ x₁ := by
  iintro #H %x₁ Hb
  ihave Hm := (rtc_le_muR R x₂ x₁) $$ Hb
  icases Hm with ⟨%k, Hk⟩
  ihave Hl := (itR_le_phi R x₂ Φ k) $$ H
  iapply Hl $$ Hk
end iter
end W5c4

-- `Iris.bi_tc_strong_ind_left` idx 8: removable (given NonExpansive₂ R, biTc R · x₂ entails ∃ k, k-fold unrolling of the step, a non-expansive predicate closed under the step; each unrolling entails Φ by induction on k using the premise, so Φ need not be non-expansive)
theorem w5c4_56 : drop% Iris.bi_tc_strong_ind_left 8 := by
  intro PROP A _ _ R _ x₂ Φ; exact tc_strong_noNE R x₂ Φ

-- `Iris.bi_rtc_strong_ind_left` idx 8: removable (given NonExpansive₂ R, biRtc R · x₂ entails ∃ k, k-fold unrolling of the step, a non-expansive predicate closed under the step; each unrolling entails Φ by induction on k using the premise)
theorem w5c4_57 : drop% Iris.bi_rtc_strong_ind_left 8 := by
  intro PROP A _ _ R _ x₂ Φ; exact rtc_strong_noNE R x₂ Φ

-- `Iris.bi_tc_timeless` idx 3: removable (given NonExpansive₂ R, biTc R x y = ∃ k, k-fold unrolling built from R by ∨, ∃, ∗ and False only, all timeless; emp does not occur)
theorem w5c4_58 : drop% Iris.bi_tc_timeless 3 := by
  intro PROP A _ _ _ R _ _ x y; exact tc_timeless' R x y

-- `Iris.bi_tc_timeless` idx 5: removable (given NonExpansive₂ R, biTc R x y = ∃ k, k-fold unrolling built from timeless R by ∨, ∃, ∗ and False; no internal equality occurs, so discreteness of A is not needed)
theorem w5c4_59 : drop% Iris.bi_tc_timeless 5 := by
  intro PROP A _ _ _ R _ _ x y; exact tc_timeless' R x y
namespace W5c4
/-- Step-indexed predicates over the Bool-or monoid with exact splitting, downward closed in the step
and resource-blind at step 0. As a BI, emp holds at every resource at step 0 but only at false later,
so emp is not timeless (a non-affine BI with non-timeless emp). -/
structure TP where
  holds : Nat → Bool → Prop
  mono {n n' : Nat} {m : Bool} : holds n m → n' ≤ n → holds n' m
  irr {m m' : Bool} : holds 0 m → holds 0 m'

theorem TP.ext' : {P Q : TP} → (∀ n m, P.holds n m ↔ Q.holds n m) → P = Q
  | ⟨p, _, _⟩, ⟨q, _, _⟩, h => by
    have : p = q := funext fun n => funext fun m => propext (h n m)
    subst this; rfl

def TP.emp : TP where
  holds n m := n = 0 ∨ m = false
  mono h hle := by rcases h with h | h; exact .inl (by omega); exact .inr h
  irr _ := .inl rfl
def TP.pure (φ : Prop) : TP where
  holds _ _ := φ
  mono h _ := h
  irr h := h
def TP.and (P Q : TP) : TP where
  holds n m := P.holds n m ∧ Q.holds n m
  mono h hle := ⟨P.mono h.1 hle, Q.mono h.2 hle⟩
  irr h := ⟨P.irr h.1, Q.irr h.2⟩
def TP.or (P Q : TP) : TP where
  holds n m := P.holds n m ∨ Q.holds n m
  mono h hle := h.elim (fun h => .inl (P.mono h hle)) (fun h => .inr (Q.mono h hle))
  irr h := h.elim (fun h => .inl (P.irr h)) (fun h => .inr (Q.irr h))
def TP.imp (P Q : TP) : TP where
  holds n m := ∀ n', n' ≤ n → P.holds n' m → Q.holds n' m
  mono h hle n'' h'' hp := h n'' (Nat.le_trans h'' hle) hp
  irr h n' hn' hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) (P.irr hp))
def TP.sForall (Ψ : TP → Prop) : TP where
  holds n m := ∀ p, Ψ p → p.holds n m
  mono h hle p hp := p.mono (h p hp) hle
  irr h p hp := p.irr (h p hp)
def TP.sExists (Ψ : TP → Prop) : TP where
  holds n m := ∃ p, Ψ p ∧ p.holds n m
  mono h hle := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.mono h hle⟩
  irr h := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.irr h⟩
def TP.sep (P Q : TP) : TP where
  holds n m := ∃ a b, m = Bool.or a b ∧ P.holds n a ∧ Q.holds n b
  mono h hle := let ⟨a, b, e, hp, hq⟩ := h; ⟨a, b, e, P.mono hp hle, Q.mono hq hle⟩
  irr {_ m'} h := let ⟨_, _, _, hp, hq⟩ := h; ⟨m', false, by cases m' <;> rfl, P.irr hp, Q.irr hq⟩
def TP.wand (P Q : TP) : TP where
  holds n m := ∀ n', n' ≤ n → ∀ b, P.holds n' b → Q.holds n' (Bool.or m b)
  mono h hle n'' h'' b hp := h n'' (Nat.le_trans h'' hle) b hp
  irr h n' hn' b hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) b hp)
def TP.pers (P : TP) : TP where
  holds n _ := P.holds n false
  mono h hle := P.mono h hle
  irr h := h
def TP.later (P : TP) : TP where
  holds n m := match n with | 0 => True | k+1 => P.holds k m
  mono {n n' m} h hle := by
    cases n' with
    | zero => trivial
    | succ k' => cases n with
      | zero => omega
      | succ k => exact P.mono h (by omega)
  irr _ := trivial

instance : BIBase TP where
  Entails P Q := ∀ n m, P.holds n m → Q.holds n m
  emp := TP.emp
  pure := TP.pure
  and := TP.and
  or := TP.or
  imp := TP.imp
  sForall := TP.sForall
  sExists := TP.sExists
  sep := TP.sep
  wand := TP.wand
  persistently := TP.pers
  later := TP.later

/-- Step-indexed OFE on TP: n-equal when they agree at all steps ≤ n and all resources. -/
instance tpOFE : OFE TP where
  Dist n P Q := ∀ n', n' ≤ n → ∀ m, (P.holds n' m ↔ Q.holds n' m)
  dist_eqv := ⟨fun _ _ _ _ => Iff.rfl, fun h n' hn m => (h n' hn m).symm,
    fun h1 h2 n' hn m => (h1 n' hn m).trans (h2 n' hn m)⟩
  eq_dist' {P Q} := ⟨fun h => h ▸ fun _ _ _ _ => Iff.rfl, fun h => TP.ext' fun n m => h n n (Nat.le_refl n) m⟩
  dist_lt h hm n' hn m := h n' (by omega) m

instance tpCOFE : IsCOFE TP where
  compl c := {
    holds n m := (c n).holds n m
    mono {n n' m} h hle := ((c.cauchy hle) n' (Nat.le_refl n') m).mp ((c n).mono h hle)
    irr h := (c 0).irr h }
  conv_compl {n c} n' hn m := by
    show (c n').holds n' m ↔ (c n).holds n' m
    exact ((c.cauchy hn) n' (Nat.le_refl n') m).symm

instance tpBI : BI TP where
  entails_refl _ _ h := h
  entails_trans h1 h2 n m h := h2 n m (h1 n m h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ _ h => h, fun _ _ h => h⟩,
    fun ⟨h1, h2⟩ => TP.ext' fun n m => ⟨h1 n m, h2 n m⟩⟩
  and_ne := ⟨fun _ _ _ h1 _ _ h2 n' hn m => and_congr (h1 n' hn m) (h2 n' hn m)⟩
  or_ne := ⟨fun _ _ _ h1 _ _ h2 n' hn m => or_congr (h1 n' hn m) (h2 n' hn m)⟩
  imp_ne := ⟨fun _ _ _ h1 _ _ h2 n' hn m => forall_congr' fun n'' => imp_congr_right fun hle =>
    imp_congr (h1 n'' (Nat.le_trans hle hn) m) (h2 n'' (Nat.le_trans hle hn) m)⟩
  sep_ne := ⟨fun _ _ _ h1 _ _ h2 n' hn m => exists_congr fun a => exists_congr fun b => and_congr_right fun _ =>
    and_congr (h1 n' hn a) (h2 n' hn b)⟩
  wand_ne := ⟨fun _ _ _ h1 _ _ h2 n' hn m => forall_congr' fun n'' => imp_congr_right fun hle => forall_congr' fun b =>
    imp_congr (h1 n'' (Nat.le_trans hle hn) b) (h2 n'' (Nat.le_trans hle hn) _)⟩
  persistently_ne := ⟨fun _ _ _ h n' hn _ => h n' hn false⟩
  later_ne := ⟨fun n _ _ h n' hn m => by
    cases n' with
    | zero => exact Iff.rfl
    | succ k => exact h k (by omega) m⟩
  sForall_ne {n P Q} h n' hn m := ⟨fun hp q hq => by
      obtain ⟨p, hp', hpq⟩ := h.2 q hq
      exact (hpq n' hn m).mp (hp p hp'),
    fun hq p hp => by
      obtain ⟨q, hq', hpq⟩ := h.1 p hp
      exact (hpq n' hn m).mpr (hq q hq')⟩
  sExists_ne {n P Q} h n' hn m := ⟨fun ⟨p, hp, hh⟩ => by
      obtain ⟨q, hq, hpq⟩ := h.1 p hp
      exact ⟨q, hq, (hpq n' hn m).mp hh⟩,
    fun ⟨q, hq, hh⟩ => by
      obtain ⟨p, hp, hpq⟩ := h.2 q hq
      exact ⟨p, hp, (hpq n' hn m).mpr hh⟩⟩
  pure_intro h _ _ _ := h
  pure_elim' h n m hφ := h hφ n m trivial
  and_elim_l _ _ h := h.1
  and_elim_r _ _ h := h.2
  and_intro h1 h2 n m h := ⟨h1 n m h, h2 n m h⟩
  or_intro_l _ _ h := .inl h
  or_intro_r _ _ h := .inr h
  or_elim h1 h2 n m h := h.elim (h1 n m) (h2 n m)
  imp_intro {P _ _} h n m hp n' hle hq := h n' m ⟨P.mono hp hle, hq⟩
  imp_elim h n m hpq := h n m hpq.1 n (Nat.le_refl n) hpq.2
  sForall_intro h n m hp p hΨ := h p hΨ n m hp
  sForall_elim hΨ n m h := h _ hΨ
  sExists_intro hΨ n m h := ⟨_, hΨ, h⟩
  sExists_elim h n m := fun ⟨p, hp, hh⟩ => h p hp n m hh
  sep_mono h1 h2 n m := fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, h1 n a hp, h2 n b hq⟩
  emp_sep {P} := ⟨fun n m ⟨a, b, e, he, hp⟩ => by
      rcases he with he | he
      · subst he; exact P.irr hp
      · subst he; cases b <;> (subst e; exact hp),
    fun n m hp => ⟨false, m, by cases m <;> rfl, .inr rfl, hp⟩⟩
  sep_symm n m := fun ⟨a, b, e, hp, hq⟩ => ⟨b, a, by rw [e, Bool.or_comm], hq, hp⟩
  sep_assoc_l n m := fun ⟨_, c, e, ⟨a, b, e', hp, hq⟩, hr⟩ =>
    ⟨a, or b c, by rw [e, e', Bool.or_assoc], hp, b, c, rfl, hq, hr⟩
  wand_intro {P _ _} h n m hp n' hle b hq := h n' (Bool.or m b) ⟨m, b, rfl, P.mono hp hle, hq⟩
  wand_elim h n m := fun ⟨a, b, e, hp, hq⟩ => e ▸ h n a hp n (Nat.le_refl n) b hq
  persistently_mono h n _ hp := h n false hp
  persistently_idem_2 _ _ h := h
  persistently_emp_2 _ _ _ := .inr rfl
  persistently_and_2 _ _ h := h
  persistently_absorb_l n m := fun ⟨_, _, _, hp, _⟩ => hp
  persistently_and_l n m := fun ⟨hp, hq⟩ => ⟨false, m, by cases m <;> rfl, hp, hq⟩
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
    | succ k => exact fun p hp => h _ ⟨p, rfl⟩ (k+1) (Nat.le_refl _) hp
  later_sExists_false n m h := by
    cases n with
    | zero => exact .inl trivial
    | succ k =>
      obtain ⟨p, hp, hh⟩ := h
      exact .inr ⟨_, ⟨p, rfl⟩, hp, hh⟩
  later_sep := ⟨fun n m h => by
      cases n with
      | zero => exact ⟨m, false, by cases m <;> rfl, trivial, trivial⟩
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
      refine .inr fun n' hle hf => ?_
      cases n' with
      | zero => exact P.mono h (Nat.zero_le _)
      | succ j => exact hf.elim

theorem tp_emp_not_timeless : ¬ Timeless (emp : TP) := fun ⟨h⟩ => by
  have := h 1 true (.inl rfl)
  rcases this with h1 | h1
  · exact h1
  · rcases h1 with h1 | h1 <;> simp at h1

instance : SiPure TP where
  siPure Pi := ⟨fun n _ => Pi.holds n, fun h hle => Pi.closed h hle, fun h => h⟩

instance : SiEmpValid TP where
  siEmpValid P := ⟨fun n => P.holds n false, fun h hle => P.mono h hle⟩

/-- TP is a step-indexed BI (siPure is resource-blind, siEmpValid evaluates at the unit `false`). -/
instance tpSbi : Sbi TP where
  siPure_ne := ⟨fun _ _ _ h n' hn _ => h hn⟩
  siEmpValid_ne := ⟨fun _ _ _ h n' hn => h n' hn false⟩
  siPure_mono H n _ h := H n h
  siEmpValid_mono H n h := H n false h
  siEmpValid_siPure := ⟨fun _ h => h, fun _ h => h⟩
  siPure_siEmpValid _ _ h := h
  siPure_imp_mpr n m h n' hle hp := h n' hle hp
  siPure_sForall_mpr n m h p hp := h _ ⟨p, rfl⟩ n (Nat.le_refl n) hp
  persistently_imp_siPure n m h n' hle hp := h n' hle hp
  siPure_later := ⟨fun n m h => by cases n <;> exact h, fun n m h => by cases n <;> exact h⟩
  siPure_absorbing _ := ⟨fun n m ⟨_, _, _, _, h⟩ => h⟩
  siEmpValid_later_mp n h := by cases n <;> exact h
  siEmpValid_affinely_mpr n h := ⟨.inr rfl, h⟩
  prop_ext_siEmpValid {P Q} n h n' hn m :=
    ⟨fun hp => h.1 n' hn m hp, fun hq => h.2 n' hn m hq⟩
end W5c4

namespace W5c4
def RFt : Unit → Unit → TP := fun _ _ => iprop(False)
instance : NonExpansive₂ RFt := ne2const _
instance (x y : Unit) : Timeless (RFt x y) := by unfold RFt; infer_instance

theorem rft_rtc : biRtc RFt () () ⊢ iprop(emp) := by
  iintro H
  ihave Hi := bi_rtc_ind_left RFt () (fun _ => (iprop(emp) : TP))
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    unfold RFt
    icases Hx with ⟨Hx | ⟨%x', Hx, -⟩⟩
    · iapply affinely_elim_emp; iexact Hx
    · icases Hx with %Hx; exact Hx.elim
  iapply Hi $$ %() H
end W5c4

-- `Iris.bi_nsteps_timeless` idx 3: necessary (Sbi TP with non-timeless emp, A = Unit, R = False: biNsteps R 0 () () = <affine> (() ≡ ()) ⊣⊢ emp)
theorem w5c4_60 : ¬ drop0% Iris.bi_nsteps_timeless 3 := fun h => by
  have e : (iprop(emp) : TP) = biNsteps RFt 0 () () :=
    BIBase.BiEntails.to_eq ⟨bi_nsteps_zero RFt (), affinely_elim_emp⟩
  exact tp_emp_not_timeless (e ▸ @h TP Unit _ _ _ RFt 0 _ () ())

-- `Iris.bi_rtc_timeless` idx 3: necessary (Sbi TP with non-timeless emp, A = Unit, R = False: biRtc R () () ⊣⊢ emp)
theorem w5c4_61 : ¬ drop0% Iris.bi_rtc_timeless 3 := fun h => by
  have e : (iprop(emp) : TP) = biRtc RFt () () :=
    BIBase.BiEntails.to_eq ⟨rtc_refl' RFt (), rft_rtc⟩
  exact tp_emp_not_timeless (e ▸ @h TP Unit _ _ _ RFt _ _ () ())
