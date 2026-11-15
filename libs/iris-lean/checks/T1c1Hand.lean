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


open Iris Iris.BI in
-- `Iris.BI.impl_timeless` idx 2: removable (no Loeb needed: ▷(P→Q) ⊢ ▷False ∨ (▷False → P → Q) (later_false_em) and ⊢ P → ▷False ∨ Q (Timeless Q); combine)
theorem t1c1_4 : drop% Iris.BI.impl_timeless 2 := by
  intro PROP _ P Q _
  refine ⟨?_⟩
  have h1 : iprop(▷ (P → Q)) ⊢ iprop(P → ▷ False ∨ Q) :=
    imp_intro ((and_mono_right later_intro).trans
      (later_and.mpr.trans ((later_mono imp_elim_left).trans Timeless.timeless)))
  have h3 : iprop((▷ False → (P → Q)) ∧ (P → ▷ False ∨ Q)) ⊢ iprop(P → Q) := by
    refine imp_intro ?_
    have h2 : iprop(((▷ False → (P → Q)) ∧ (P → ▷ False ∨ Q)) ∧ P) ⊢ iprop(((▷ False → (P → Q)) ∧ P) ∧ (▷ False ∨ Q)) :=
      and_intro (and_mono_left and_elim_l) ((and_mono_left and_elim_r).trans imp_elim_left)
    refine h2.trans (and_or_left.mp.trans (or_elim ?_ and_elim_r))
    exact (and_intro ((and_intro (and_elim_l.trans and_elim_l) and_elim_r).trans imp_elim_left) (and_elim_l.trans and_elim_r)).trans imp_elim_left
  exact (and_intro later_false_em h1).trans (and_or_right.mp.trans (or_elim (and_elim_l.trans or_intro_l) (h3.trans or_intro_r)))

open Iris Iris.BI in
-- `Iris.BI.only0_except0` idx 2: removable (▷False → ▷False ∨ P is valid in every BI)
theorem t1c1_7 : drop% Iris.BI.only0_except0 2 := by
  intro PROP _ P
  exact ⟨true_intro, imp_intro (and_elim_r.trans or_intro_l)⟩

open Iris Iris.BI in
-- `Iris.BI.only0_intuitionistically_mpr` idx 2: removable (only0_persistently_mpr plus the mpr half of only0_affinely, which needs neither Loeb nor Timeless emp)
theorem t1c1_8 : drop% Iris.BI.only0_intuitionistically_mpr 2 := by
  intro PROP _ _ P
  exact (affinely_mono only0_persistently_mpr).trans (imp_intro ((and_intro (and_elim_l.trans affinely_elim_emp) ((and_mono_left affinely_elim).trans imp_elim_left)).trans .rfl))

open Iris Iris.BI in
-- `Iris.BI.only0_intuitionistically_mpr` idx 3: removable (same proof as idx 2: Timeless emp unused)
theorem t1c1_9 : drop% Iris.BI.only0_intuitionistically_mpr 3 := by
  intro PROP _ _ P
  exact (affinely_mono only0_persistently_mpr).trans (imp_intro ((and_intro (and_elim_l.trans affinely_elim_emp) ((and_mono_left affinely_elim).trans imp_elim_left)).trans .rfl))

namespace T1c1
open Iris Iris.BI
/-- Timeless wand without Loeb (helper). -/
theorem wandT {PROP : Type _} [BI PROP] {P Q : PROP} [Timeless Q] : Timeless iprop(P -∗ Q) := by
  refine ⟨?_⟩
  have h1 : iprop(▷ (P -∗ Q)) ⊢ iprop(P -∗ ▷ False ∨ Q) :=
    wand_intro ((sep_mono_right later_intro).trans
      (later_sep.mpr.trans ((later_mono wand_elim_left).trans Timeless.timeless)))
  have h3 : iprop((▷ False → (P -∗ Q)) ∧ (P -∗ ▷ False ∨ Q)) ⊢ iprop(P -∗ Q) := by
    refine wand_intro ?_
    refine sep_and_right.trans ((and_mono_right wand_elim_left).trans (and_or_left.mp.trans (or_elim ?_ and_elim_r)))
    exact and_comm.mp.trans (persistent_and_sep_distrib.trans ((sep_mono imp_elim_right and_elim_r).trans wand_elim_left))
  exact (and_intro later_false_em h1).trans (and_or_right.mp.trans (or_elim (and_elim_l.trans or_intro_l) (h3.trans or_intro_r)))
end T1c1

open Iris Iris.BI in
-- `Iris.BI.wand_timeless` idx 2: removable (no Loeb needed: later_false_em plus P -∗ ▷False ∨ Q, ▷False persistent (helper wandT))
theorem t1c1_5 : drop% Iris.BI.wand_timeless 2 := by
  intro PROP _ P Q _
  exact T1c1.wandT

open Iris Iris.BI in
-- `Iris.BI.wandIff_timeless` idx 2: removable (both wands timeless by wandT, then and_timeless)
theorem t1c1_6 : drop% Iris.BI.wandIff_timeless 2 := by
  intro PROP _ P Q _ _
  haveI : Timeless iprop(P -∗ Q) := T1c1.wandT
  haveI : Timeless iprop(Q -∗ P) := T1c1.wandT
  exact inferInstanceAs (Timeless iprop((P -∗ Q) ∧ (Q -∗ P)))



open Iris Iris.BI in
-- `Iris.BI.loeb_alt_wand` idx 2: removable (no affinity needed: for ▷P ⊢ P put Q := True -∗ P; then ▷Q ⊢ Q, so emp ⊢ □(▷Q -∗ Q) ⊢ Q and True ⊢ emp ∗ True ⊢ P; the other direction is loeb_wand)
theorem t1c1_1 : drop% Iris.BI.loeb_alt_wand 2 := by
  intro PROP _
  refine ⟨fun _ P => loeb_wand P, fun h => ⟨fun {P} hP => ?_⟩⟩
  have hQ : iprop(▷ (True -∗ P)) ⊢ iprop(True -∗ P) := later_wand.trans (wand_mono later_intro hP)
  have h1 : (emp : PROP) ⊢ iprop(▷ (True -∗ P) -∗ (True -∗ P)) := wand_intro (emp_sep.mp.trans hQ)
  have h2 : (emp : PROP) ⊢ iprop(□ (▷ (True -∗ P) -∗ (True -∗ P))) :=
    and_intro .rfl (BI.persistently_emp_2.trans (persistently_mono h1))
  exact emp_sep.mpr.trans ((sep_mono_left (h2.trans (h _))).trans wand_elim_left)



namespace T1c1
open Iris Iris.BI Iris.OFE
/-- The least fixpoint of a monotone, persistence-preserving F is persistent, with no Affine/Absorbing
assumption: lfp ∧ <pers> lfp is persistent and F-closed, so lfp ⊢ lfp ∧ <pers> lfp. -/
theorem lfp_pers {PROP A : Type _} [BI PROP] [OFE A] (F : (A → PROP) → A → PROP) [BIMonoPred F]
    (hP : ∀ (Φ : A → PROP) [∀ x, Persistent (Φ x)] (x : A), Persistent (F Φ x)) (x : A) :
    Persistent (bi_least_fixpoint F x) := by
  let X : A → PROP := fun y => iprop(bi_least_fixpoint F y ∧ <pers> bi_least_fixpoint F y)
  haveI hXne : NonExpansive X :=
    ⟨fun _ _ _ h => and_ne.ne (NonExpansive.ne h) (persistently_ne.ne (NonExpansive.ne h))⟩
  haveI hXp : ∀ y, Persistent (X y) := fun y =>
    ⟨and_elim_r.trans ((and_intro .rfl BI.persistently_idem_2).trans BI.persistently_and_2)⟩
  haveI hF : ∀ y, Persistent (F X y) := hP X
  have step : ∀ y, F X y ⊢ bi_least_fixpoint F y := fun y => by
    rw [least_fixpoint_unfold F (x := y)]
    iintro H
    iapply (mono_pred (Φ := X) (Ψ := bi_least_fixpoint F)) $$ [] H
    iintro !> %z ⟨Hz, -⟩
    iexact Hz
  have key : ⊢ □ (∀ y, F X y -∗ X y) := by
    iintro !> %y H
    iapply (show F X y ⊢ X y from and_intro (step y) (Persistent.persistent.trans (persistently_mono (step y))))
    iexact H
  refine ⟨?_⟩
  iintro HL
  ihave Hk := key
  ihave H2 := (least_fixpoint_iter F (Φ := X)) $$ Hk
  ihave H3 := H2 $$ %x HL
  icases H3 with ⟨-, H4⟩
  iexact H4
end T1c1

open Iris T1c1 in
-- `Iris.least_fixpoint_persistent_affine` idx 6: removable (lfp ∧ <pers> lfp is persistent and F-closed (F preserves persistence, is monotone), so lfp ⊢ <pers> lfp by least_fixpoint_iter; Affine preservation unused)
theorem t1c1_2 : drop% Iris.least_fixpoint_persistent_affine 6 := by
  intro PROP A _ _ F _ hP x
  exact lfp_pers F hP x

open Iris T1c1 in
-- `Iris.least_fixpoint_persistent_absorbing` idx 6: removable (same proof as least_fixpoint_persistent_affine idx 6 (helper lfp_pers); Absorbing preservation unused)
theorem t1c1_3 : drop% Iris.least_fixpoint_persistent_absorbing 6 := by
  intro PROP A _ _ F _ hP x
  exact lfp_pers F hP x



namespace T1c1
open Iris Iris.BI Iris.OFE

/-! KW: an affine Kripke BI on four worlds a ≤ b ≤ c and d (isolated). Later at a looks at b; later is
trivially true at b, c, d (▷ False holds there). Persistently at a looks at a and d, elsewhere at the world
itself. ▷ commutes with <pers>, but <pers> (▷ False ∨ X) ⊬ ▷ False ∨ <pers> X for X := "not d" (at a):
a BI without BIPersistentlyExist where except0 does not commute with persistently. -/
inductive KW | a | b | c | d deriving DecidableEq

/-- The Kripke order. -/
def kle : KW → KW → Prop
  | .a, v => v ≠ .d
  | .b, v => v = .b ∨ v = .c
  | .c, v => v = .c
  | .d, v => v = .d

theorem kle_refl : ∀ w, kle w w
  | .a => fun h => nomatch h
  | .b => .inl rfl
  | .c => rfl
  | .d => rfl

theorem kle_ba {v : KW} (h : kle .b v) : kle .a v := by
  rcases h with rfl | rfl <;> exact fun h => nomatch h
theorem kle_cb {v : KW} (h : kle .c v) : kle .b v := .inr h

/-- Up-closed predicates on KW. -/
structure KQ where
  p : KW → Prop
  up_ab : p .a → p .b
  up_bc : p .b → p .c

theorem KQ.ext' {P Q : KQ} (h : ∀ w, P.p w ↔ Q.p w) : P = Q := by
  cases P; cases Q; congr; funext w; exact propext (h w)

theorem KQ.mono (P : KQ) : ∀ {v w : KW}, kle v w → P.p v → P.p w
  | .a, .a, _, h => h
  | .a, .b, _, h => P.up_ab h
  | .a, .c, _, h => P.up_bc (P.up_ab h)
  | .a, .d, e, _ => absurd rfl e
  | .b, .b, _, h => h
  | .b, .c, _, h => P.up_bc h
  | .b, .a, e, _ => by rcases e with e | e <;> cases e
  | .b, .d, e, _ => by rcases e with e | e <;> cases e
  | .c, .c, _, h => h
  | .c, .a, e, _ => by cases e
  | .c, .b, e, _ => by cases e
  | .c, .d, e, _ => by cases e
  | .d, .d, _, h => h
  | .d, .a, e, _ => by cases e
  | .d, .b, e, _ => by cases e
  | .d, .c, e, _ => by cases e

instance : COFE KQ := COFE.ofDiscrete _

/-- Kripke implication. -/
def KQ.imp (P Q : KQ) : KQ :=
  ⟨fun w => ∀ v, kle w v → P.p v → Q.p v, fun h v hv => h v (kle_ba hv), fun h v hv => h v (kle_cb hv)⟩

theorem KQ.imp_p {P Q : KQ} {w} (h : (KQ.imp P Q).p w) : P.p w → Q.p w := h w (kle_refl w)

theorem KQ.imp_intro' {R P Q : KQ} (h : ∀ w, R.p w ∧ P.p w → Q.p w) : ∀ w, R.p w → (KQ.imp P Q).p w :=
  fun _ hR v hv hP => h v ⟨R.mono hv hR, hP⟩

instance kwBase : BIBase KQ where
  Entails P Q := ∀ w, P.p w → Q.p w
  emp := ⟨fun _ => True, fun _ => trivial, fun _ => trivial⟩
  pure φ := ⟨fun _ => φ, id, id⟩
  and P Q := ⟨fun w => P.p w ∧ Q.p w, fun h => ⟨P.up_ab h.1, Q.up_ab h.2⟩, fun h => ⟨P.up_bc h.1, Q.up_bc h.2⟩⟩
  or P Q := ⟨fun w => P.p w ∨ Q.p w, fun h => h.imp P.up_ab Q.up_ab, fun h => h.imp P.up_bc Q.up_bc⟩
  imp := KQ.imp
  sForall Ψ := ⟨fun w => ∀ p, Ψ p → p.p w, fun h p hp => p.up_ab (h p hp), fun h p hp => p.up_bc (h p hp)⟩
  sExists Ψ := ⟨fun w => ∃ p, Ψ p ∧ p.p w, fun ⟨p, hp, h⟩ => ⟨p, hp, p.up_ab h⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, p.up_bc h⟩⟩
  sep P Q := ⟨fun w => P.p w ∧ Q.p w, fun h => ⟨P.up_ab h.1, Q.up_ab h.2⟩, fun h => ⟨P.up_bc h.1, Q.up_bc h.2⟩⟩
  wand := KQ.imp
  persistently P := ⟨fun w => P.p w ∧ (w = .a → P.p .d), fun h => ⟨P.up_ab h.1, (fun e => nomatch e)⟩,
    fun h => ⟨P.up_bc h.1, fun e => nomatch e⟩⟩
  later P := ⟨fun w => w = .a → P.p .b, (fun _ e => nomatch e), (fun _ e => nomatch e)⟩

instance kwBI : BI KQ where
  entails_refl _ h := h
  entails_trans h1 h2 w h := h2 w (h1 w h)
  equiv_iff {P Q} := ⟨fun e => e ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h1, h2⟩ => KQ.ext' fun w => ⟨h1 w, h2 w⟩⟩
  and_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  or_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  imp_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  sForall_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sExists_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sep_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  wand_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  later_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  persistently_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  pure_intro h _ _ := h
  pure_elim' h w hφ := h hφ w trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 w h := ⟨h1 w h, h2 w h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 w h := h.elim (h1 w) (h2 w)
  imp_intro h := KQ.imp_intro' h
  imp_elim h w hPQ := KQ.imp_p (h w hPQ.1) hPQ.2
  sForall_intro h w hP p hp := h p hp w hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h w := fun ⟨p, hp, hpw⟩ => h p hp w hpw
  sep_mono h1 h2 w h := ⟨h1 w h.1, h2 w h.2⟩
  emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩
  sep_symm _ h := ⟨h.2, h.1⟩
  sep_assoc_l _ h := ⟨h.1.1, h.1.2, h.2⟩
  wand_intro h := KQ.imp_intro' h
  wand_elim h w hPQ := KQ.imp_p (h w hPQ.1) hPQ.2
  persistently_mono h w hp := ⟨h w hp.1, fun e => h _ (hp.2 e)⟩
  persistently_idem_2 _ hp := ⟨hp, fun e => ⟨hp.2 e, (fun e2 => nomatch e2)⟩⟩
  persistently_emp_2 _ _ := ⟨trivial, fun _ => trivial⟩
  persistently_and_2 _ h := ⟨⟨h.1.1, h.2.1⟩, fun e => ⟨h.1.2 e, h.2.2 e⟩⟩
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1.1, h.2⟩
  later_mono h _ hl e := h _ (hl e)
  later_intro {P} w h e := by subst e; exact P.up_ab h
  later_sForall_2 _ h e p hp := KQ.imp_p (h _ ⟨p, rfl⟩) hp e
  later_sExists_false w hl := by
    cases w with
    | a =>
      obtain ⟨p, hp, hpb⟩ := hl rfl
      exact .inr ⟨_, ⟨p, rfl⟩, hp, fun _ => hpb⟩
    | b => exact .inl fun e => nomatch e
    | c => exact .inl fun e => nomatch e
    | d => exact .inl fun e => nomatch e
  later_sep := ⟨fun _ h => ⟨fun e => (h e).1, fun e => (h e).2⟩, fun _ h e => ⟨h.1 e, h.2 e⟩⟩
  later_persistently := ⟨fun _ h => ⟨fun e => (h e).1, (fun _ e2 => nomatch e2)⟩,
    fun _ h e => ⟨h.1 e, (fun e2 => nomatch e2)⟩⟩
  later_false_em {P} w h := by
    cases w with
    | a =>
      refine .inr fun v hv hf => ?_
      cases v with
      | a => exact absurd rfl hf
      | b => exact h rfl
      | c => exact P.up_bc (h rfl)
      | d => exact absurd rfl hv
    | b => exact .inl fun e => nomatch e
    | c => exact .inl fun e => nomatch e
    | d => exact .inl fun e => nomatch e

/-- X holds everywhere except at d. -/
def kX : KQ := ⟨fun w => w ≠ .d, (fun _ e => nomatch e), (fun _ e => nomatch e)⟩

/-- <pers> ◇ kX holds at a. -/
theorem kw_pe : (iprop(<pers> ◇ kX) : KQ).p .a :=
  ⟨.inr (fun e => nomatch e), (fun _ => .inl fun e => nomatch e)⟩

/-- ◇ <pers> kX fails at a. -/
theorem kw_ep (h : (iprop(◇ <pers> kX) : KQ).p .a) : False :=
  h.elim (fun hl => hl rfl) (fun hr => hr.2 rfl rfl)

end T1c1

namespace T1c1
open Iris Iris.BI
instance kxT : Timeless kX := ⟨fun w h => by
  cases w with
  | a => exact .inr (fun e => nomatch e)
  | b => exact .inl fun e => nomatch e
  | c => exact .inl fun e => nomatch e
  | d => exact .inl fun e => nomatch e⟩
instance kempT : Timeless (PROP := KQ) emp := ⟨fun w _ => .inr trivial⟩
/-- <pers> kX is not timeless: ▷ <pers> kX holds at a, ◇ <pers> kX does not. -/
theorem kw_pnt (h : Timeless iprop(<pers> kX : KQ)) : False :=
  kw_ep (h.timeless .a (fun _ => (⟨(fun e => nomatch e), (fun e => nomatch e)⟩ : KW.b ≠ .d ∧ (KW.b = .a → KW.d ≠ .d))))

/-- KQ with later = id: every proposition is timeless. -/
def KQ1 := KQ
instance : COFE KQ1 := COFE.ofDiscrete _
instance kw1Base : BIBase KQ1 where
  Entails P Q := ∀ w, P.p w → Q.p w
  emp := ⟨fun _ => True, fun _ => trivial, fun _ => trivial⟩
  pure φ := ⟨fun _ => φ, id, id⟩
  and P Q := ⟨fun w => P.p w ∧ Q.p w, fun h => ⟨P.up_ab h.1, Q.up_ab h.2⟩, fun h => ⟨P.up_bc h.1, Q.up_bc h.2⟩⟩
  or P Q := ⟨fun w => P.p w ∨ Q.p w, fun h => h.imp P.up_ab Q.up_ab, fun h => h.imp P.up_bc Q.up_bc⟩
  imp := KQ.imp
  sForall Ψ := ⟨fun w => ∀ p, Ψ p → p.p w, fun h p hp => p.up_ab (h p hp), fun h p hp => p.up_bc (h p hp)⟩
  sExists Ψ := ⟨fun w => ∃ p, Ψ p ∧ p.p w, fun ⟨p, hp, h⟩ => ⟨p, hp, p.up_ab h⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, p.up_bc h⟩⟩
  sep P Q := ⟨fun w => P.p w ∧ Q.p w, fun h => ⟨P.up_ab h.1, Q.up_ab h.2⟩, fun h => ⟨P.up_bc h.1, Q.up_bc h.2⟩⟩
  wand := KQ.imp
  persistently P := ⟨fun w => P.p w ∧ (w = .a → P.p .d), fun h => ⟨P.up_ab h.1, (fun e => nomatch e)⟩,
    fun h => ⟨P.up_bc h.1, fun e => nomatch e⟩⟩
  later P := P

instance kw1BI : BI KQ1 where
  entails_refl _ h := h
  entails_trans h1 h2 w h := h2 w (h1 w h)
  equiv_iff {P Q} := ⟨fun e => e ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h1, h2⟩ => KQ.ext' fun w => ⟨h1 w, h2 w⟩⟩
  and_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  or_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  imp_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  sForall_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sExists_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sep_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  wand_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  later_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  persistently_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  pure_intro h _ _ := h
  pure_elim' h w hφ := h hφ w trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 w h := ⟨h1 w h, h2 w h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 w h := h.elim (h1 w) (h2 w)
  imp_intro h := KQ.imp_intro' h
  imp_elim h w hPQ := KQ.imp_p (h w hPQ.1) hPQ.2
  sForall_intro h w hP p hp := h p hp w hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h w := fun ⟨p, hp, hpw⟩ => h p hp w hpw
  sep_mono h1 h2 w h := ⟨h1 w h.1, h2 w h.2⟩
  emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩
  sep_symm _ h := ⟨h.2, h.1⟩
  sep_assoc_l _ h := ⟨h.1.1, h.1.2, h.2⟩
  wand_intro h := KQ.imp_intro' h
  wand_elim h w hPQ := KQ.imp_p (h w hPQ.1) hPQ.2
  persistently_mono h w hp := ⟨h w hp.1, fun e => h _ (hp.2 e)⟩
  persistently_idem_2 _ hp := ⟨hp, fun e => ⟨hp.2 e, (fun e2 => nomatch e2)⟩⟩
  persistently_emp_2 _ _ := ⟨trivial, fun _ => trivial⟩
  persistently_and_2 _ h := ⟨⟨h.1.1, h.2.1⟩, fun e => ⟨h.1.2 e, h.2.2 e⟩⟩
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 w h p hp := KQ.imp_p (h _ ⟨p, rfl⟩) hp
  later_sExists_false _ := fun ⟨p, hp, h⟩ => .inr ⟨_, ⟨p, rfl⟩, hp, h⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr (fun _ _ hf => hf.elim)

/-- Identity embedding of KQ1 (later = id) into KW: a BiEmbed, not a BiEmbedLater. -/
@[instance_reducible] def kwE : BiEmbed KQ1 KQ where
  embed P := P
  ne := ⟨fun _ _ _ h => h⟩
  mono := fun h => h
  emp_valid_inj := fun _ h => h
  emp_2 := fun _ h => h
  impl_2 := fun _ _ _ h => h
  forall_2 := fun _ _ h w hR p hp => h p hp w hR
  exist_1 := fun _ _ h w ⟨p, hp, hw⟩ => h p hp w hw
  sep := fun _ _ => ⟨fun _ h => h, fun _ h => h⟩
  wand_2 := fun _ _ _ h => h
  persistently := fun _ => ⟨fun _ h => h, fun _ h => h⟩
/-- In KQ1 every proposition is timeless. -/
theorem kq1T (P : KQ1) : Timeless P := ⟨fun _ h => .inr h⟩
/-- Holds at b and c only: timeless in KQ1, not in KW. -/
def kB : KQ := ⟨fun w => w = .b ∨ w = .c, (fun h => nomatch h), (fun _ => .inr rfl)⟩
theorem kB_nt (h : Timeless (kB : KQ)) : False := by
  rcases h.timeless .a (fun _ => .inl rfl) with h | h
  · exact h rfl
  · rcases h with h | h <;> cases h
end T1c1

open Iris Iris.BI T1c1 in
-- `Iris.BI.embed_timeless` idx 5: necessary (identity embedding of KQ1 (KW with later = id) into KW; kB timeless in KQ1, not in KW)
theorem t1c1_20 : ¬ drop0% Iris.BI.embed_timeless 5 := fun h =>
  kB_nt (@h KQ1 KQ _ _ kwE (kB : KQ1) (kq1T _))

open Iris Iris.BI T1c1 in
-- `Iris.BI.except0_persistently` idx 2: necessary (KW (affine Kripke BI, no BIPersistentlyExist), P = kX: <pers> ◇ kX holds at a, ◇ <pers> kX does not)
theorem t1c1_10 : ¬ drop0% Iris.BI.except0_persistently 2 := fun h => kw_ep ((@h KQ kwBI kX).2 .a kw_pe)
open Iris Iris.BI T1c1 in
-- `Iris.BI.except0_intuitionistically` idx 2: necessary (KW, P = kX at world a)
theorem t1c1_11 : ¬ drop0% Iris.BI.except0_intuitionistically 2 := fun h =>
  kw_ep ((@h KQ kwBI kX .a ⟨trivial, kw_pe⟩).elim (fun hl => .inl hl) (fun hr => .inr hr.2))
open Iris Iris.BI T1c1 in
-- `Iris.BI.except0_intuitionisticallyIf` idx 2: necessary (KW, p = true, P = kX at world a)
theorem t1c1_12 : ¬ drop0% Iris.BI.except0_intuitionisticallyIf 2 := fun h =>
  kw_ep ((@h KQ kwBI true kX .a ⟨trivial, kw_pe⟩).elim (fun hl => .inl hl) (fun hr => .inr hr.2))
open Iris Iris.BI T1c1 in
-- `Iris.BI.persistently_timeless` idx 2: necessary (KW, P = kX timeless, <pers> kX not timeless (fails at a, holds at b))
theorem t1c1_13 : ¬ drop0% Iris.BI.persistently_timeless 2 := fun h => kw_pnt (@h KQ kwBI kX kxT)
open Iris Iris.BI T1c1 in
-- `Iris.BI.intuitionistically_timeless` idx 2: necessary (KW (emp = True timeless), P = kX: □ kX not timeless)
theorem t1c1_14 : ¬ drop0% Iris.BI.intuitionistically_timeless 2 := fun h =>
  kw_ep (((@h KQ kwBI kempT kX kxT).timeless .a (fun _ => (⟨trivial, (fun e => nomatch e), (fun e => nomatch e)⟩ : True ∧ KW.b ≠ .d ∧ (KW.b = .a → KW.d ≠ .d)))).elim
    (fun hl => .inl hl) (fun hr => .inr hr.2))



namespace T1c1
open Iris Iris.BI Iris.OFE

/-! BQ: a non-affine, non-Loeb BI on three worlds o ≤ l, o ≤ r (l, r incomparable) and resources Bool × Bool
(componentwise or, exact splitting). Later at o looks at o itself (a loop, so not Loeb); later is trivially true
at l and r, so ▷ False = "at l or r" is not False. -/
inductive BW | o | l | r deriving DecidableEq

def BM := Bool × Bool
def bop (a b : BM) : BM := (Bool.or a.1 b.1, Bool.or a.2 b.2)
def bu : BM := (false, false)
theorem bop_comm (a b : BM) : bop a b = bop b a := by
  unfold bop; rw [Bool.or_comm a.1, Bool.or_comm a.2]
theorem bop_assoc (a b c : BM) : bop (bop a b) c = bop a (bop b c) := by
  rcases a with ⟨_|_, _|_⟩ <;> rcases b with ⟨_|_, _|_⟩ <;> rcases c with ⟨_|_, _|_⟩ <;> rfl
theorem bu_bop (a : BM) : bop bu a = a := by
  rcases a with ⟨_|_, _|_⟩ <;> rfl
theorem bop_bu (a : BM) : bop a bu = a := by rw [bop_comm, bu_bop]

def ble : BW → BW → Prop
  | .o, _ => True
  | .l, v => v = .l
  | .r, v => v = .r

theorem ble_refl : ∀ w, ble w w
  | .o => trivial
  | .l => rfl
  | .r => rfl

/-- World-up-closed predicates on BW × BM. -/
structure BQ where
  p : BW → BM → Prop
  up_l {m} : p .o m → p .l m
  up_r {m} : p .o m → p .r m

theorem BQ.ext' {P Q : BQ} (h : ∀ w m, P.p w m ↔ Q.p w m) : P = Q := by
  cases P; cases Q; congr; funext w m; exact propext (h w m)

theorem BQ.mono (P : BQ) : ∀ {v w : BW} {m}, ble v w → P.p v m → P.p w m
  | .o, .o, _, _, h => h
  | .o, .l, _, _, h => P.up_l h
  | .o, .r, _, _, h => P.up_r h
  | .l, .l, _, _, h => h
  | .r, .r, _, _, h => h
  | .l, .o, _, e, _ => by cases e
  | .l, .r, _, e, _ => by cases e
  | .r, .o, _, e, _ => by cases e
  | .r, .l, _, e, _ => by cases e

theorem ble_trans : ∀ {u v w : BW}, ble u v → ble v w → ble u w
  | .o, _, _, _, _ => trivial
  | .l, _, _, e1, e2 => by cases e1; exact e2
  | .r, _, _, e1, e2 => by cases e1; exact e2

instance : COFE BQ := COFE.ofDiscrete _

def BQ.imp (P Q : BQ) : BQ :=
  ⟨fun w m => ∀ v, ble w v → P.p v m → Q.p v m,
   fun h v hv => h v trivial, fun h v hv => h v trivial⟩
def BQ.wand (P Q : BQ) : BQ :=
  ⟨fun w m => ∀ v, ble w v → ∀ b, P.p v b → Q.p v (bop m b),
   fun h v hv => h v trivial, fun h v hv => h v trivial⟩

instance bqBase : BIBase BQ where
  Entails P Q := ∀ w m, P.p w m → Q.p w m
  emp := ⟨fun _ m => m = bu, id, id⟩
  pure φ := ⟨fun _ _ => φ, id, id⟩
  and P Q := ⟨fun w m => P.p w m ∧ Q.p w m, fun h => ⟨P.up_l h.1, Q.up_l h.2⟩, fun h => ⟨P.up_r h.1, Q.up_r h.2⟩⟩
  or P Q := ⟨fun w m => P.p w m ∨ Q.p w m, fun h => h.imp P.up_l Q.up_l, fun h => h.imp P.up_r Q.up_r⟩
  imp := BQ.imp
  sForall Ψ := ⟨fun w m => ∀ p, Ψ p → p.p w m, fun h p hp => p.up_l (h p hp), fun h p hp => p.up_r (h p hp)⟩
  sExists Ψ := ⟨fun w m => ∃ p, Ψ p ∧ p.p w m, fun ⟨p, hp, h⟩ => ⟨p, hp, p.up_l h⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, p.up_r h⟩⟩
  sep P Q := ⟨fun w m => ∃ a b, m = bop a b ∧ P.p w a ∧ Q.p w b,
    fun ⟨a, b, e, h1, h2⟩ => ⟨a, b, e, P.up_l h1, Q.up_l h2⟩, fun ⟨a, b, e, h1, h2⟩ => ⟨a, b, e, P.up_r h1, Q.up_r h2⟩⟩
  wand := BQ.wand
  persistently P := ⟨fun w _ => P.p w bu, P.up_l, P.up_r⟩
  later P := ⟨fun w m => w = .o → P.p .o m, (fun _ e => nomatch e), (fun _ e => nomatch e)⟩

instance bqBI : BI BQ where
  entails_refl _ _ h := h
  entails_trans h1 h2 w m h := h2 w m (h1 w m h)
  equiv_iff {P Q} := ⟨fun e => e ▸ ⟨fun _ _ h => h, fun _ _ h => h⟩,
    fun ⟨h1, h2⟩ => BQ.ext' fun w m => ⟨h1 w m, h2 w m⟩⟩
  and_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  or_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  imp_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  sForall_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sExists_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2⟩⟩
  sep_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  wand_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [(h₁ : _ = _), (h₂ : _ = _)])⟩
  later_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  persistently_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (h : _ = _))⟩
  pure_intro h _ _ _ := h
  pure_elim' h w m hφ := h hφ w m trivial
  and_elim_l _ _ h := h.1
  and_elim_r _ _ h := h.2
  and_intro h1 h2 w m h := ⟨h1 w m h, h2 w m h⟩
  or_intro_l _ _ h := .inl h
  or_intro_r _ _ h := .inr h
  or_elim h1 h2 w m h := h.elim (h1 w m) (h2 w m)
  imp_intro {R _ _} h w m hR v hv hP := h v m ⟨R.mono hv hR, hP⟩
  imp_elim h w m hPQ := h w m hPQ.1 w (ble_refl w) hPQ.2
  sForall_intro h w m hP p hp := h p hp w m hP
  sForall_elim hp _ _ h := h _ hp
  sExists_intro hp _ _ h := ⟨_, hp, h⟩
  sExists_elim h w m := fun ⟨p, hp, hpw⟩ => h p hp w m hpw
  sep_mono h1 h2 w m := fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, h1 w a hp, h2 w b hq⟩
  emp_sep {P} := ⟨fun w m ⟨a, b, e, he, hp⟩ => by
      subst he; rw [bu_bop] at e; subst e; exact hp,
    fun w m hp => ⟨bu, m, (bu_bop m).symm, rfl, hp⟩⟩
  sep_symm w m := fun ⟨a, b, e, hp, hq⟩ => ⟨b, a, by rw [e, bop_comm], hq, hp⟩
  sep_assoc_l w m := fun ⟨_, c, e, ⟨a, b, e', hp, hq⟩, hr⟩ =>
    ⟨a, bop b c, by rw [e, e', bop_assoc], hp, b, c, rfl, hq, hr⟩
  wand_intro {P _ _} h w m hp v hv b hq := h v (bop m b) ⟨m, b, rfl, P.mono hv hp, hq⟩
  wand_elim h w m := fun ⟨a, b, e, hp, hq⟩ => e ▸ h w a hp w (ble_refl w) b hq
  persistently_mono h w _ hp := h w bu hp
  persistently_idem_2 _ _ h := h
  persistently_emp_2 _ _ _ := rfl
  persistently_and_2 _ _ h := h
  persistently_absorb_l w m := fun ⟨_, _, _, hp, _⟩ => hp
  persistently_and_l w m := fun ⟨hp, hq⟩ => ⟨bu, m, (bu_bop m).symm, hp, hq⟩
  later_mono h _ m hp e := h _ m (hp e)
  later_intro {P} w m h e := by subst e; exact h
  later_sForall_2 w m h e p hp := h _ ⟨p, rfl⟩ w (ble_refl w) hp e
  later_sExists_false w m hl := by
    cases w with
    | o =>
      obtain ⟨p, hp, hpo⟩ := hl rfl
      exact .inr ⟨_, ⟨p, rfl⟩, hp, fun _ => hpo⟩
    | l => exact .inl fun e => nomatch e
    | r => exact .inl fun e => nomatch e
  later_sep := ⟨fun w m h => by
      cases w with
      | o => obtain ⟨a, b, e, h1, h2⟩ := h rfl; exact ⟨a, b, e, fun _ => h1, fun _ => h2⟩
      | l => exact ⟨m, bu, (bop_bu m).symm, (fun e => nomatch e), (fun e => nomatch e)⟩
      | r => exact ⟨m, bu, (bop_bu m).symm, (fun e => nomatch e), (fun e => nomatch e)⟩,
    fun w m h e => by subst e; obtain ⟨a, b, e, h1, h2⟩ := h; exact ⟨a, b, e, h1 rfl, h2 rfl⟩⟩
  later_persistently := ⟨fun _ _ h => h, fun _ _ h => h⟩
  later_false_em {P} w m h := by
    cases w with
    | o =>
      refine .inr fun v hv hf => ?_
      cases v with
      | o => exact absurd rfl hf
      | l => exact P.up_l (h rfl)
      | r => exact P.up_r (h rfl)
    | l => exact .inl fun e => nomatch e
    | r => exact .inl fun e => nomatch e

def bx : BM := (true, false)
def by' : BM := (false, true)
/-- Holds exactly at l. -/
def bL : BQ := ⟨fun w _ => w = .l, (fun e => nomatch e), (fun e => nomatch e)⟩
/-- Holds exactly at r. -/
def bR : BQ := ⟨fun w _ => w = .r, (fun e => nomatch e), (fun e => nomatch e)⟩
/-- Owns exactly x at l, exactly y at r. -/
def bP : BQ := ⟨fun w m => (w = .l ∧ m = bx) ∨ (w = .r ∧ m = by'),
  (fun h => by rcases h with ⟨e, _⟩ | ⟨e, _⟩ <;> cases e), (fun h => by rcases h with ⟨e, _⟩ | ⟨e, _⟩ <;> cases e)⟩
/-- Owns exactly y at l, exactly x at r. -/
def bQ : BQ := ⟨fun w m => (w = .l ∧ m = by') ∨ (w = .r ∧ m = bx),
  (fun h => by rcases h with ⟨e, _⟩ | ⟨e, _⟩ <;> cases e), (fun h => by rcases h with ⟨e, _⟩ | ⟨e, _⟩ <;> cases e)⟩
theorem bq_ent {P Q : BQ} (h : P ⊢ Q) : ∀ w m, P.p w m → Q.p w m := h
end T1c1

open Iris Iris.BI T1c1 in
-- `Iris.BI.only0_or` idx 2: necessary (BQ (non-Loeb branching BI: o loops, l and r dead), P = at l, Q = at r: <only0> (P ∨ Q) holds at o, neither disjunct)
theorem t1c1_15 : ¬ drop0% Iris.BI.only0_or 2 := fun h => by
  have := bq_ent (@h BQ bqBI bL bR).1 .o bu (fun v _ hf => by
    cases v with
    | o => exact absurd rfl hf
    | l => exact .inl rfl
    | r => exact .inr rfl)
  rcases this with h1 | h1
  · exact nomatch (h1 .r trivial (fun e => nomatch e))
  · exact nomatch (h1 .l trivial (fun e => nomatch e))

open Iris Iris.BI T1c1 in
-- `Iris.BI.only0_sep` idx 2: necessary (BQ at (o, xy): P ∗ Q splits as x,y at l and y,x at r, no uniform split)
theorem t1c1_16 : ¬ drop0% Iris.BI.only0_sep 2 := fun h => by
  have := bq_ent (@h BQ bqBI bP bQ).1 .o (true, true) (fun v _ hf => by
    cases v with
    | o => exact absurd rfl hf
    | l => exact ⟨bx, by', rfl, .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩⟩
    | r => exact ⟨by', bx, rfl, .inr ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩⟩)
  obtain ⟨a, b, _, ha, _⟩ := this
  have h1 := ha .l trivial (fun e => nomatch e)
  have h2 := ha .r trivial (fun e => nomatch e)
  rcases h1 with ⟨_, e1⟩ | ⟨e, _⟩
  · rcases h2 with ⟨e, _⟩ | ⟨_, e2⟩
    · cases e
    · rw [e1] at e2; cases e2
  · cases e

open Iris Iris.BI T1c1 in
-- `Iris.BI.only0_absorbingly` idx 2: necessary (BQ at (o, xy), P = exactly x at l, exactly y at r)
theorem t1c1_17 : ¬ drop0% Iris.BI.only0_absorbingly 2 := fun h => by
  have := bq_ent (@h BQ bqBI bP).1 .o (true, true) (fun v _ hf => by
    cases v with
    | o => exact absurd rfl hf
    | l => exact ⟨by', bx, rfl, trivial, .inl ⟨rfl, rfl⟩⟩
    | r => exact ⟨bx, by', rfl, trivial, .inr ⟨rfl, rfl⟩⟩)
  obtain ⟨a, b, _, _, hb⟩ := this
  have h1 := hb .l trivial (fun e => nomatch e)
  have h2 := hb .r trivial (fun e => nomatch e)
  rcases h1 with ⟨_, e1⟩ | ⟨e, _⟩
  · rcases h2 with ⟨e, _⟩ | ⟨_, e2⟩
    · cases e
    · rw [e1] at e2; cases e2
  · cases e



namespace T1c1
open Iris Iris.BI Iris.Std Iris.Std.LawfulSet

/-! MK: predicates on masks (CoPset) with sep = disjoint union, emp = {∅}, persistently P := P ∅,
later = id: a non-affine discrete BI. With W E := {E} (exact ownership of the mask tokens),
fupd E1 E2 P := W E1 -∗ W E2 ∗ P is a lawful, mask-sensitive BIFUpdate. -/
def MK := CoPset → Prop

theorem mU {p : Pos} {A B : CoPset} : p ∈ A ∪ B ↔ p ∈ A ∨ p ∈ B := mem_union
theorem me {p : Pos} {A B : CoPset} (e : A = B) : p ∈ A ↔ p ∈ B := by rw [e]
theorem dj0 {A : CoPset} : (∅ : CoPset) ## A := fun _ ⟨h, _⟩ => CoPset.mem_empty h
theorem djs {A B : CoPset} (d : A ## B) : B ## A := fun p ⟨h1, h2⟩ => d p ⟨h2, h1⟩

instance : BIBase MK where
  Entails P Q      := ∀ x, P x → Q x
  emp            x := x = ∅
  pure φ         _ := φ
  and P Q        x := P x ∧ Q x
  or P Q         x := P x ∨ Q x
  imp P Q        x := P x → Q x
  sForall Ψ      x := ∀ p, Ψ p → p x
  sExists Ψ      x := ∃ p, Ψ p ∧ p x
  sep P Q        x := ∃ a b, a ## b ∧ x = a ∪ b ∧ P a ∧ Q b
  wand P Q       x := ∀ y, x ## y → P y → Q (x ∪ y)
  persistently P _ := P ∅
  later P        x := P x

instance : COFE MK := COFE.ofDiscrete _

instance mkBI : BI MK where
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
  sep_mono h1 h2 _ := fun ⟨a, b, d, e, ha, hb⟩ => ⟨a, b, d, e, h1 a ha, h2 b hb⟩
  emp_sep := ⟨fun _ ⟨a, b, _, e, ha, hb⟩ => by
      have ha' : a = ∅ := ha
      subst ha'; rw [union_empty_left] at e; subst e; exact hb,
    fun x h => ⟨∅, x, dj0, union_empty_left.symm, rfl, h⟩⟩
  sep_symm _ := fun ⟨a, b, d, e, ha, hb⟩ => ⟨b, a, djs d, e.trans union_comm, hb, ha⟩
  sep_assoc_l _ := fun ⟨ab, c, d2, e1, ⟨a, b, d1, e2, ha, hb⟩, hc⟩ =>
    ⟨a, b ∪ c,
      fun p ⟨h1, h2⟩ => (mU.1 h2).elim (fun hb => d1 p ⟨h1, hb⟩)
        (fun hc => d2 p ⟨(me e2).2 (mU.2 (.inl h1)), hc⟩),
      by rw [e1, e2, union_assoc], ha, b, c,
      fun p ⟨h1, h2⟩ => d2 p ⟨(me e2).2 (mU.2 (.inr h1)), h2⟩, rfl, hb, hc⟩
  wand_intro h x hP y hd hQ := h (x ∪ y) ⟨x, y, hd, rfl, hP, hQ⟩
  wand_elim h _ := fun ⟨a, b, d, e, ha, hb⟩ => e ▸ h a ha b d hb
  persistently_mono h _ hP := h ∅ hP
  persistently_idem_2 _ h := h
  persistently_emp_2 _ _ := (rfl : (∅ : CoPset) = ∅)
  persistently_and_2 _ h := h
  persistently_absorb_l _ := fun ⟨_, _, _, _, ha, _⟩ => ha
  persistently_and_l x h := ⟨∅, x, dj0, union_empty_left.symm, h.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr fun _ => h

/-- Mask-ownership fancy update on MK. -/
def mfupd (E1 E2 : CoPset) (P : MK) : MK := fun S =>
  S ## E1 → ∃ B, E2 ## B ∧ S ∪ E1 = E2 ∪ B ∧ P B

theorem sub_eq {E1 E2 : CoPset} (h : E2 ⊆ E1) : E1 = E2 ∪ (E1 \ E2) :=
  CoPset.ext fun p => ⟨fun hp => by
      by_cases h2 : p ∈ E2
      · exact mU.2 (.inl h2)
      · exact mU.2 (.inr (mem_diff.2 ⟨hp, h2⟩)),
    fun hp => (mU.1 hp).elim (h p) (fun h' => (mem_diff.1 h').1)⟩

instance mkFupd : BIFUpdate MK where
  fupd := mfupd
  ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  subset {E1 E2} h S hS _ := ⟨E1 \ E2, fun p ⟨h1, h2⟩ => (mem_diff.1 h2).2 h1,
    by rw [show S = ∅ from hS, union_empty_left]; exact sub_eq h,
    fun _ => ⟨∅, djs dj0, by
      rw [union_comm, union_empty_right]; exact (sub_eq h).symm, rfl⟩⟩
  except0 _ h := h.elim (fun f => f.elim) id
  mono h _ hf hd := let ⟨B, d, e, hp⟩ := hf hd; ⟨B, d, e, h B hp⟩
  trans {E1 E2 E3} _ S hf hd :=
    let ⟨B, d, e, hq⟩ := hf hd
    let ⟨B', d', e', hp⟩ := hq (djs d)
    ⟨B', d', e.trans (union_comm.trans e'), hp⟩
  mask_frame_right_strong {E1 E2 Ef _} hdisj S hf hd := by
    have hd1 : S ## E1 := fun p ⟨h1, h2⟩ => hd p ⟨h1, mU.2 (.inl h2)⟩
    obtain ⟨B, d, e, hp⟩ := hf hd1
    have hin : ∀ p, p ∈ E2 ∨ p ∈ B → p ∈ Ef → False := fun p h hf' => by
      have h' : p ∈ S ∪ E1 := (me e).2 (mU.2 h)
      rcases mU.1 h' with h' | h'
      · exact hd p ⟨h', mU.2 (.inr hf')⟩
      · exact hdisj p ⟨h', hf'⟩
    refine ⟨B, fun p ⟨h1, h2⟩ => (mU.1 h1).elim (fun h1 => d p ⟨h1, h2⟩) (fun h1 => hin p (.inr h2) h1), ?_,
      hp (fun p ⟨h1, h2⟩ => hin p (.inl h1) h2)⟩
    apply CoPset.ext; intro p
    have := @me p _ _ e
    simp only [mU] at this ⊢
    constructor
    · rintro (h | h | h)
      · rcases this.1 (.inl h) with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases this.1 (.inr h) with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · exact .inl (.inr h)
    · rintro ((h | h) | h)
      · rcases this.2 (.inl h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact .inr (.inr h)
      · rcases this.2 (.inr h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
  frame_right {E1 E2} _ _ S := fun ⟨A, C, dAC, eS, hf, hR⟩ hd => by
    have hA : A ## E1 := fun p ⟨h1, h2⟩ => hd p ⟨(me eS).2 (mU.2 (.inl h1)), h2⟩
    have hC : C ## E1 := fun p ⟨h1, h2⟩ => hd p ⟨(me eS).2 (mU.2 (.inr h1)), h2⟩
    obtain ⟨B, d, e, hp⟩ := hf hA
    have hin : ∀ p, p ∈ E2 ∨ p ∈ B → p ∈ C → False := fun p h hc => by
      rcases mU.1 ((me e).2 (mU.2 h)) with h' | h'
      · exact dAC p ⟨h', hc⟩
      · exact hC p ⟨hc, h'⟩
    refine ⟨B ∪ C, fun p ⟨h1, h2⟩ => (mU.1 h2).elim (fun h2 => d p ⟨h1, h2⟩) (fun h2 => hin p (.inl h1) h2), ?_,
      B, C, fun p ⟨h1, h2⟩ => hin p (.inr h1) h2, rfl, hp, hR⟩
    rw [eS]
    apply CoPset.ext; intro p
    have := @me p _ _ e
    simp only [mU] at this ⊢
    constructor
    · rintro ((h | h) | h)
      · rcases this.1 (.inl h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact .inr (.inr h)
      · rcases this.1 (.inr h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
    · rintro (h | h | h)
      · rcases this.2 (.inl h) with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases this.2 (.inr h) with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · exact .inl (.inr h)

theorem top_ne_empty : (⊤ : CoPset) ≠ ∅ := fun h => CoPset.mem_empty (p := .xH) (by rw [← h]; exact CoPset.mem_full)

end T1c1

namespace T1c1
open Iris Iris.BI
@[instance_reducible] def idEmb (PROP : Type _) [BI PROP] : BiEmbed PROP PROP where
  embed := id
  ne := ⟨fun _ _ _ h => h⟩
  mono := fun h => h
  emp_valid_inj := fun _ h => h
  emp_2 := .rfl
  impl_2 := fun _ _ => .rfl
  forall_2 := fun _ _ h => sForall_intro h
  exist_1 := fun _ _ h => sExists_elim h
  sep := fun _ _ => .rfl
  wand_2 := fun _ _ => .rfl
  persistently := fun _ => .rfl
-- helper: constant-True fancy update on any BI (lawful; all laws hold trivially)
@[reducible] def topF (PROP : Type _) [BI PROP] : BIFUpdate PROP where
  fupd _ _ _ := iprop(True)
  ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  subset _ := true_intro
  except0 := true_intro
  mono _ := .rfl
  trans := true_intro
  mask_frame_right_strong _ := true_intro
  frame_right := true_intro
theorem topFU : @BiEmbedFUpd MK MK _ _ (idEmb _) (topF MK) (topF MK) :=
  @BiEmbedFUpd.mk MK MK _ _ (idEmb _) (topF MK) (topF MK) (fun _ _ _ => .rfl)
-- helper: the mask update of False fails at the empty mask
theorem mk_false : ¬ mfupd ∅ ∅ (iprop(False) : MK) ∅ := fun h =>
  let ⟨_, _, _, f⟩ := h dj0; f
end T1c1

open Iris Iris.BI T1c1 in
-- `Iris.BI.embed_embed_fupd` idx 11: necessary (MK with identity embeddings, fupd mkFupd / const True / const True: composite fails at |={∅}=> False)
theorem t1c1_18 : ¬ drop0% Iris.BI.embed_embed_fupd 11 := fun h =>
  mk_false ((@h MK MK _ _ MK _ (idEmb MK) (idEmb MK) mkFupd (topF MK) (topF MK) topFU).embed_fupd ∅ ∅ iprop(False) |>.mpr ∅ trivial)
open Iris Iris.BI T1c1 in
-- `Iris.BI.embed_embed_fupd` idx 12: necessary (MK with identity embeddings, fupd const True / const True / mkFupd)
theorem t1c1_19 : ¬ drop0% Iris.BI.embed_embed_fupd 12 := fun h =>
  mk_false ((@h MK MK _ _ MK _ (idEmb MK) (idEmb MK) (topF MK) (topF MK) mkFupd topFU).embed_fupd ∅ ∅ iprop(False) |>.mp ∅ trivial)



namespace T1c1
open Iris Iris.BI COFE Auth
abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare
abbrev HV0 := HeapView Nat (Agree (DiscreteO Unit)) TM
abbrev HV1 := HeapView Nat (Agree (DiscreteO GName)) TM
/-- Closed-proofs GF (invariant, mask, credit slots 0–3), gen-heap slots 4–6 (heap and meta HeapViews over
ExtTreeMap Nat, MetaUR) and the inv-heap Auth slot (≥ 7); L = Nat, V = Unit. -/
noncomputable def GI : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF⟩
  | 1  => ⟨constOF CoPsetDisjL⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3  => ⟨AuthURF (constOF Credit)⟩
  | 4  => ⟨constOF HV0⟩
  | 5  => ⟨constOF HV1⟩
  | 6  => ⟨constOF MetaUR⟩
  | _  => ⟨constOF (Auth (InvHeapMapUR Unit TM))⟩
instance giWsat : WsatGpreS GI where
  inv := { τ := 0, transp := by unfold GI; rfl }
  enabled := { τ := 1, transp := by unfold GI; rfl }
  disabled := { τ := 2, transp := by unfold GI; rfl }
instance giLc : LcGpreS GI where
  lc_elem := { τ := 3, transp := by unfold GI; rfl }
instance giInv : InvGpreS GI where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance
instance giHeap : genHeapPreS Nat Unit GI TM where
  heap := ⟨{ τ := 4, transp := by unfold GI; rfl }⟩
  metaInfo := ⟨{ τ := 5, transp := by unfold GI; rfl }⟩
  metaData := { τ := 6, transp := by unfold GI; rfl }
@[reducible] def giIH : invHeapPreS Nat Unit GI TM where
  invHeap := { τ := 7, transp := by unfold GI; rfl }

open Iris.Std.LawfulSet in
theorem empty_diffN (N : Namespace) : (∅ \ ↑N : CoPset) = ∅ := by
  ext x; rw [mem_diff]; simp [mem_empty]
open Iris.Std.LawfulSet in
/-- An update at the empty mask, framed into any mask. -/
theorem frame0 {PROP : Type _} [BI PROP] [BIFUpdate PROP] {P : PROP} (N : Namespace) (E : CoPset) :
    (|={∅, ∅ \ ↑N}=> P) ⊢ |={E, E}=> P := by
  have := fupd_mask_frame_right (P := P) (E1 := ∅) (E2 := ∅ \ ↑N) (Ef := E) dj0
  rw [empty_diffN, union_empty_left] at this; rw [empty_diffN]; exact this
theorem hN_top : (↑invHeapN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
theorem two_full' (G : genHeapGS Nat Unit GI TM) :
    pointsTo (G := G) 0 (.own 1) () ∗ pointsTo (G := G) 0 (.own 1) () ⊢ iprop(⌜False⌝) :=
  pointsTo_op_cmraValid.trans (and_elim_l.trans (pure_mono fun hv => absurd (DFrac.valid_own_op hv) (by simp)))
open Iris.Std.LawfulSet in
/-- An update at the empty mask (no mask change), framed into any mask. -/
theorem frame00 {PROP : Type _} [BI PROP] [BIFUpdate PROP] {P : PROP} (E : CoPset) :
    (|={∅, ∅}=> P) ⊢ |={E, E}=> P := by
  have := fupd_mask_frame_right (P := P) (E1 := ∅) (E2 := ∅) (Ef := E) dj0
  rw [union_empty_left] at this; exact this
section
variable [J : invHeapGS Nat Unit GI TM]
/-- The exclusive inv-heap fragment also yields the persistent one. -/
theorem split_frag (I : Unit → Prop) :
    (invPointsToOwn (L := Nat) (H := TM) 0 () I : IProp GI) ⊢ invPointsToOwn (L := Nat) (H := TM) 0 () I ∗ invPointsTo (L := Nat) (H := TM) 0 I := by
  unfold invPointsToOwn invPointsTo
  refine .trans ?_ iOwn_op.mp
  rw [← Auth.frag_op, Heap.singleton_op_singleton]
  have e : ∀ (a : Option (Excl (DiscreteO Unit))) (b : Agree (DiscreteO (Unit → Prop))),
      ((a, b) • (none, b) : Option (Excl (DiscreteO Unit)) × Agree (DiscreteO (Unit → Prop))) = (a, b) := by
    intro a b; show (a • none, b • b) = (a, b); rw [Agree.idemp]; cases a <;> rfl
  rw [e]
/-- Two exclusive inv-heap fragments for the same location are contradictory. -/
theorem two_frag (I I' : Unit → Prop) :
    (invPointsToOwn (L := Nat) (H := TM) 0 () I : IProp GI) ∗ invPointsToOwn (L := Nat) (H := TM) 0 () I' ⊢ iprop(⌜False⌝) := by
  unfold invPointsToOwn
  refine iOwn_cmraValid_op.trans fun n x h => ?_
  have h' : ✓{n} ((Auth.frag _ : Auth (InvHeapMapUR Unit TM)) • (Auth.frag _ : Auth (InvHeapMapUR Unit TM))) := h
  rw [← Auth.frag_op, Auth.frag_validN, Heap.singleton_op_singleton, Heap.singleton_validN_iff] at h'
  exact h'.1
end
/-- Allocated gen heap {[0 := ()]} and inv heap: if False follows (under a fancy update) from
invHeapInv ∗ 0 ↦ (), then False. -/
theorem gi_false (E2 : CoPset)
    (K : ∀ (_ : InvGS_gen .hasNoLC GI) (G : genHeapGS Nat Unit GI TM) (_ : invHeapGS Nat Unit GI TM),
      (invHeapInv (L := Nat) (V := Unit) (H := TM) : IProp GI) ∗ pointsTo (G := G) 0 (.own 1) () ⊢
        |={⊤, E2}=> iprop(⌜False⌝)) : False := by
  refine pure_soundness (PROP := IProp GI) (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := E2) (P := iprop(⌜False⌝)) fun I => ?_)
  iintro -
  imod (genHeap_init (L := Nat) (V := Unit) (GF := GI) (H := TM) (Iris.Std.PartialMap.singleton 0 ())) with ⟨%G, -, Hp, -⟩
  ihave Hp2 : pointsTo (G := G) 0 (.own 1) () $$ [Hp]
  · iapply (BI.BigSepM.bigSepM_singleton (M := TM) (Φ := fun l v => pointsTo (G := G) l (.own 1) v) (i := 0) (x := ())).1
    iexact Hp
  haveI := giIH
  imod (invHeap_init Nat Unit (GF := GI) (H := TM) (hlc := .hasNoLC) ⊤) with ⟨%J, Hinv⟩
  imod Hinv
  iapply (K I G J)
  isplitl [Hinv]
  · iexact Hinv
  · iexact Hp2
end T1c1

open Iris Iris.BI T1c1 in
-- `Iris.invPointsTo_acc` idx 12: necessary (GI (wsat + gen heap + inv heap), E = ∅: opening without the mask duplicates 0 ↦ ())
theorem t1c1_21 : ¬ drop0% Iris.invPointsTo_acc 12 := fun h => gi_false (⊤ \ ↑invHeapN) fun I G J => by
  iintro ⟨#Hinv, Hp⟩
  imod (make_invPointsTo (hlc := .hasNoLC) (l := (0 : Nat)) (v := ()) (I := fun _ => True) (E := ⊤) hN_top trivial) $$ Hinv Hp with Hs
  ihave #Hb := invPointsToOwn_inv (0 : Nat) () (fun _ => True) $$ Hs
  ihave X := (h (hlc := .hasNoLC) (GF := GI) (L := Nat) (V := Unit) (H := TM) (E := ∅) (l := 0) (I := fun _ => True)) $$ Hinv Hb
  ihave X2 := frame0 invHeapN ⊤ $$ X
  imod X2 with ⟨%v, -, A, -⟩
  imod (invPointsTo_acc (E := ⊤) (l := (0 : Nat)) (I := fun _ => True) hN_top) $$ Hinv Hb with ⟨%v', -, B, -⟩
  imodintro
  iapply (two_full' G)
  isplitl [A]
  · iexact A
  · iexact B

open Iris Iris.BI T1c1 in
-- `Iris.make_invPointsTo` idx 15: necessary (GI, I = False: the inv-heap entry then yields ⌜False⌝ via invPointsToOwn_acc)
theorem t1c1_22 : ¬ drop0% Iris.make_invPointsTo 15 := fun h => gi_false (⊤ \ ↑invHeapN) fun I G J => by
  iintro ⟨#Hinv, Hp⟩
  imod ((h (hlc := .hasNoLC) (GF := GI) (L := Nat) (V := Unit) (H := TM) (l := 0) (v := ()) (I := fun _ => False) (E := ⊤) hN_top)) $$ Hinv Hp with Hs
  imod (invPointsToOwn_acc (E := ⊤) (l := (0 : Nat)) (v := ()) (I := fun _ => False) hN_top) $$ Hinv Hs with ⟨%hf, -⟩
  exact hf.elim

open Iris Iris.BI T1c1 in
-- `Iris.invPointsToOwn_acc` idx 14: necessary (GI, E = ∅: second 0 ↦ () alongside the real opening via 0 ↦_I □)
theorem t1c1_23 : ¬ drop0% Iris.invPointsToOwn_acc 14 := fun h => gi_false (⊤ \ ↑invHeapN) fun I G J => by
  iintro ⟨#Hinv, Hp⟩
  imod (make_invPointsTo (hlc := .hasNoLC) (l := (0 : Nat)) (v := ()) (I := fun _ => True) (E := ⊤) hN_top trivial) $$ Hinv Hp with Hs
  icases (split_frag (fun _ => True)) $$ Hs with ⟨Hs, #Hb⟩
  ihave X := (h (hlc := .hasNoLC) (GF := GI) (L := Nat) (V := Unit) (H := TM) (E := ∅) (l := 0) (v := ()) (I := fun _ => True)) $$ Hinv Hs
  ihave X2 := frame0 invHeapN ⊤ $$ X
  imod X2 with ⟨-, A, -⟩
  imod (invPointsTo_acc (E := ⊤) (l := (0 : Nat)) (I := fun _ => True) hN_top) $$ Hinv Hb with ⟨%v', -, B, -⟩
  imodintro
  iapply (two_full' G)
  isplitl [A]
  · iexact A
  · iexact B

open Iris Iris.BI T1c1 in
-- `Iris.invPointsToOwn_acc_strong` idx 11: necessary (GI, E = ∅: second 0 ↦ () alongside the real opening via 0 ↦_I □)
theorem t1c1_24 : ¬ drop0% Iris.invPointsToOwn_acc_strong 11 := fun h => gi_false (⊤ \ ↑invHeapN) fun I G J => by
  iintro ⟨#Hinv, Hp⟩
  imod (make_invPointsTo (hlc := .hasNoLC) (l := (0 : Nat)) (v := ()) (I := fun _ => True) (E := ⊤) hN_top trivial) $$ Hinv Hp with Hs
  icases (split_frag (fun _ => True)) $$ Hs with ⟨Hs, #Hb⟩
  ihave X := (h (hlc := .hasNoLC) (GF := GI) (L := Nat) (V := Unit) (H := TM) (E := ∅)) $$ Hinv
  ihave X2 := frame0 invHeapN ⊤ $$ X
  imod X2 with F
  icases F $$ %0 %() %(fun _ => True) Hs with ⟨-, A, -⟩
  imod (invPointsTo_acc (E := ⊤) (l := (0 : Nat)) (I := fun _ => True) hN_top) $$ Hinv Hb with ⟨%v', -, B, -⟩
  imodintro
  iapply (two_full' G)
  isplitl [A]
  · iexact A
  · iexact B

open Iris Iris.BI T1c1 in
-- `Iris.make_invPointsTo` idx 14: necessary (GI, E = ∅: a second exclusive 0 ↦_I () fragment from the points-to taken out of the opened invariant)
theorem t1c1_25 : ¬ drop0% Iris.make_invPointsTo 14 := fun h => gi_false (⊤ \ ↑invHeapN) fun I G J => by
  iintro ⟨#Hinv, Hp⟩
  imod (make_invPointsTo (hlc := .hasNoLC) (l := (0 : Nat)) (v := ()) (I := fun _ => True) (E := ⊤) hN_top trivial) $$ Hinv Hp with Hs
  icases (split_frag (fun _ => True)) $$ Hs with ⟨Hs, #Hb⟩
  imod (invPointsTo_acc (E := ⊤) (l := (0 : Nat)) (I := fun _ => True) hN_top) $$ Hinv Hb with ⟨%v', -, B, -⟩
  ihave X := (h (hlc := .hasNoLC) (GF := GI) (L := Nat) (V := Unit) (H := TM) (l := 0) (v := ()) (I := fun _ => True) (E := ∅) trivial) $$ Hinv B
  ihave X2 := frame00 (⊤ \ ↑invHeapN) $$ X
  imod X2 with Hs2
  imodintro
  iapply (two_frag (fun _ => True) (fun _ => True))
  isplitl [Hs]
  · iexact Hs
  · iexact Hs2



namespace T1c1
open Iris Iris.BI Iris.OFE
abbrev RM := Bool × Bool
def rop (a b : RM) : RM := (Bool.or a.1 b.1, Bool.or a.2 b.2)
def ru : RM := (false, false)
theorem rop_comm (a b : RM) : rop a b = rop b a := by
  unfold rop; rw [Bool.or_comm a.1, Bool.or_comm a.2]
theorem rop_assoc (a b c : RM) : rop (rop a b) c = rop a (rop b c) := by
  rcases a with ⟨_|_, _|_⟩ <;> rcases b with ⟨_|_, _|_⟩ <;> rcases c with ⟨_|_, _|_⟩ <;> rfl
theorem ru_bop (a : RM) : rop ru a = a := by
  rcases a with ⟨_|_, _|_⟩ <;> rfl
theorem rop_ru (a : RM) : rop a ru = a := by rw [rop_comm, ru_bop]
theorem rop_self (a : RM) : rop a a = a := by
  rcases a with ⟨_|_, _|_⟩ <;> rfl
theorem rop_eq_ru {a b : RM} (h : rop a b = ru) : a = ru := by
  revert h; rcases a with ⟨_|_, _|_⟩ <;> rcases b with ⟨_|_, _|_⟩ <;> decide

/-- Level-0 restriction: a set of resources is either inside {ru} or contains every non-unit. -/
def R0 (S : RM → Prop) : Prop := (∀ m, S m → m = ru) ∨ (∀ m, m ≠ ru → S m)

/-- TR: step-indexed predicates over Bool × Bool (componentwise or, exact splitting), down-closed in the
step, whose step-0 slice satisfies R0. emp = exactly the unit at every step (so emp is timeless),
non-affine; the R0 restriction makes some persistent propositions non-laterable. -/
structure TR where
  holds : Nat → RM → Prop
  mono {n n' : Nat} {m : RM} : holds n m → n' ≤ n → holds n' m
  r0 : R0 (holds 0)

theorem TR.ext' : {P Q : TR} → (∀ n m, P.holds n m ↔ Q.holds n m) → P = Q
  | ⟨p, _, _⟩, ⟨q, _, _⟩, h => by
    have : p = q := funext fun n => funext fun m => propext (h n m)
    subst this; rfl

def TR.emp : TR where
  holds _ m := m = ru
  mono h _ := h
  r0 := .inl fun _ h => h
def TR.pure (φ : Prop) : TR where
  holds _ _ := φ
  mono h _ := h
  r0 := by
    by_cases h : φ
    · exact .inr fun _ _ => h
    · exact .inl fun _ h' => (h h').elim
def TR.and (P Q : TR) : TR where
  holds n m := P.holds n m ∧ Q.holds n m
  mono h hle := ⟨P.mono h.1 hle, Q.mono h.2 hle⟩
  r0 := by
    rcases P.r0 with hp | hp
    · exact .inl fun m h => hp m h.1
    rcases Q.r0 with hq | hq
    · exact .inl fun m h => hq m h.2
    · exact .inr fun m hm => ⟨hp m hm, hq m hm⟩
def TR.or (P Q : TR) : TR where
  holds n m := P.holds n m ∨ Q.holds n m
  mono h hle := h.elim (fun h => .inl (P.mono h hle)) (fun h => .inr (Q.mono h hle))
  r0 := by
    rcases P.r0 with hp | hp
    · rcases Q.r0 with hq | hq
      · exact .inl fun m h => h.elim (hp m) (hq m)
      · exact .inr fun m hm => .inr (hq m hm)
    · exact .inr fun m hm => .inl (hp m hm)
def TR.imp (P Q : TR) : TR where
  holds n m := ∀ n', n' ≤ n → P.holds n' m → Q.holds n' m
  mono h hle n'' h'' hp := h n'' (Nat.le_trans h'' hle) hp
  r0 := by
    rcases Q.r0 with hq | hq
    · rcases P.r0 with hp | hp
      · refine .inr fun m hm n' hn' h => ?_
        obtain rfl : n' = 0 := by omega
        exact absurd (hp m h) hm
      · refine .inl fun m h => Classical.byContradiction fun hm => hm (hq m (h 0 (Nat.le_refl 0) (hp m hm)))
    · refine .inr fun m hm n' hn' _ => ?_
      obtain rfl : n' = 0 := by omega
      exact hq m hm
def TR.sForall (Ψ : TR → Prop) : TR where
  holds n m := ∀ p, Ψ p → p.holds n m
  mono h hle p hp := p.mono (h p hp) hle
  r0 := by
    by_cases hs : ∃ p, Ψ p ∧ ∀ m, p.holds 0 m → m = ru
    · obtain ⟨p, hp, hs⟩ := hs
      exact .inl fun m h => hs m (h p hp)
    · refine .inr fun m hm p hp => ?_
      rcases p.r0 with h | h
      · exact (hs ⟨p, hp, h⟩).elim
      · exact h m hm
def TR.sExists (Ψ : TR → Prop) : TR where
  holds n m := ∃ p, Ψ p ∧ p.holds n m
  mono h hle := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.mono h hle⟩
  r0 := by
    by_cases hs : ∃ p, Ψ p ∧ ∀ m, m ≠ ru → p.holds 0 m
    · obtain ⟨p, hp, hs⟩ := hs
      exact .inr fun m hm => ⟨p, hp, hs m hm⟩
    · refine .inl fun m ⟨p, hp, h⟩ => ?_
      rcases p.r0 with h' | h'
      · exact h' m h
      · exact (hs ⟨p, hp, h'⟩).elim
def TR.sep (P Q : TR) : TR where
  holds n m := ∃ a b, m = rop a b ∧ P.holds n a ∧ Q.holds n b
  mono h hle := let ⟨a, b, e, hp, hq⟩ := h; ⟨a, b, e, P.mono hp hle, Q.mono hq hle⟩
  r0 := by
    rcases P.r0 with hp | hp
    · rcases Q.r0 with hq | hq
      · exact .inl fun m ⟨a, b, e, ha, hb⟩ => by rw [e, hp a ha, hq b hb]; rfl
      · by_cases h0 : P.holds 0 ru
        · exact .inr fun m hm => ⟨ru, m, (ru_bop m).symm, h0, hq m hm⟩
        · exact .inl fun m ⟨a, b, e, ha, hb⟩ => absurd (hp a ha ▸ ha) h0
    · rcases Q.r0 with hq | hq
      · by_cases h0 : Q.holds 0 ru
        · exact .inr fun m hm => ⟨m, ru, (rop_ru m).symm, hp m hm, h0⟩
        · exact .inl fun m ⟨a, b, e, ha, hb⟩ => absurd (hq b hb ▸ hb) h0
      · exact .inr fun m hm => ⟨m, m, (rop_self m).symm, hp m hm, hq m hm⟩
def TR.wand (P Q : TR) : TR where
  holds n m := ∀ n', n' ≤ n → ∀ b, P.holds n' b → Q.holds n' (rop m b)
  mono h hle n'' h'' b hp := h n'' (Nat.le_trans h'' hle) b hp
  r0 := by
    rcases Q.r0 with hq | hq
    · by_cases hs : ∃ c, P.holds 0 c
      · obtain ⟨c, hc⟩ := hs
        exact .inl fun m h => rop_eq_ru (hq _ (h 0 (Nat.le_refl 0) c hc))
      · exact .inr fun m _ n' hn' b hb => by
          obtain rfl : n' = 0 := by omega
          exact (hs ⟨b, hb⟩).elim
    · exact .inr fun m hm n' hn' b _ => by
        obtain rfl : n' = 0 := by omega
        exact hq _ fun e => hm (rop_eq_ru e)
def TR.pers (P : TR) : TR where
  holds n _ := P.holds n ru
  mono h hle := P.mono h hle
  r0 := by
    by_cases h : P.holds 0 ru
    · exact .inr fun _ _ => h
    · exact .inl fun _ h' => (h h').elim
def TR.later (P : TR) : TR where
  holds n m := match n with | 0 => True | k+1 => P.holds k m
  mono {n n' m} h hle := by
    cases n' with
    | zero => trivial
    | succ k' => cases n with
      | zero => omega
      | succ k => exact P.mono h (by omega)
  r0 := .inr fun _ _ => trivial

instance : BIBase TR where
  Entails P Q := ∀ n m, P.holds n m → Q.holds n m
  emp := TR.emp
  pure := TR.pure
  and := TR.and
  or := TR.or
  imp := TR.imp
  sForall := TR.sForall
  sExists := TR.sExists
  sep := TR.sep
  wand := TR.wand
  persistently := TR.pers
  later := TR.later

instance : COFE TR := COFE.ofDiscrete _

instance trBI : BI TR where
  entails_refl _ _ h := h
  entails_trans h1 h2 n m h := h2 n m (h1 n m h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ _ h => h, fun _ _ h => h⟩,
    fun ⟨h1, h2⟩ => TR.ext' fun n m => ⟨h1 n m, h2 n m⟩⟩
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
  imp_intro {P _ _} h n m hp n' hle hq := h n' m ⟨P.mono hp hle, hq⟩
  imp_elim h n m hpq := h n m hpq.1 n (Nat.le_refl n) hpq.2
  sForall_intro h n m hp p hΨ := h p hΨ n m hp
  sForall_elim hΨ n m h := h _ hΨ
  sExists_intro hΨ n m h := ⟨_, hΨ, h⟩
  sExists_elim h n m := fun ⟨p, hp, hh⟩ => h p hp n m hh
  sep_mono h1 h2 n m := fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, h1 n a hp, h2 n b hq⟩
  emp_sep {P} := ⟨fun n m ⟨a, b, e, he, hp⟩ => by
      have he' : a = ru := he
      subst he'; rw [ru_bop] at e; subst e; exact hp,
    fun n m hp => ⟨ru, m, (ru_bop m).symm, rfl, hp⟩⟩
  sep_symm n m := fun ⟨a, b, e, hp, hq⟩ => ⟨b, a, by rw [e, rop_comm], hq, hp⟩
  sep_assoc_l n m := fun ⟨_, c, e, ⟨a, b, e', hp, hq⟩, hr⟩ =>
    ⟨a, rop b c, by rw [e, e', rop_assoc], hp, b, c, rfl, hq, hr⟩
  wand_intro {P _ _} h n m hp n' hle b hq := h n' (rop m b) ⟨m, b, rfl, P.mono hp hle, hq⟩
  wand_elim h n m := fun ⟨a, b, e, hp, hq⟩ => e ▸ h n a hp n (Nat.le_refl n) b hq
  persistently_mono h n _ hp := h n ru hp
  persistently_idem_2 _ _ h := h
  persistently_emp_2 _ _ _ := (rfl : ru = ru)
  persistently_and_2 _ _ h := h
  persistently_absorb_l n m := fun ⟨_, _, _, hp, _⟩ => hp
  persistently_and_l n m := fun ⟨hp, hq⟩ => ⟨ru, m, (ru_bop m).symm, hp, hq⟩
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
      | zero => exact ⟨m, ru, (rop_ru m).symm, trivial, trivial⟩
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


theorem trEmpT : Timeless (emp : TR) := ⟨fun n m h => by
  cases n with
  | zero => exact .inl trivial
  | succ k => exact .inr h⟩
/-- Persistent, non-affine, not laterable: everything at step 0, the unit and (true, false) at step 1. -/
def tP : TR where
  holds n m := n = 0 ∨ (n = 1 ∧ (m = ru ∨ m = (true, false)))
  mono {n n' m} h hle := by
    rcases h with h | ⟨h1, h2⟩
    · exact .inl (by omega)
    · by_cases h' : n' = 0
      · exact .inl h'
      · exact .inr ⟨by omega, h2⟩
  r0 := .inr fun _ _ => .inl rfl
theorem tPpers : Persistent tP := ⟨fun n m h => by
  rcases h with h | ⟨h1, _⟩
  · exact .inl h
  · exact .inr ⟨h1, .inl rfl⟩⟩
theorem tP_nonlat (hl : Laterable tP) : False := by
  obtain ⟨hl⟩ := hl
  have h1 := hl 1 (true, false) (.inr ⟨rfl, .inr rfl⟩)
  obtain ⟨p, ⟨Q, hp⟩, hpm⟩ := h1
  subst hp
  obtain ⟨a, b, e, hQ, hb, hw⟩ := hpm
  have hb' : b = ru := hb
  subst hb'
  rw [rop_ru] at e
  subst e
  rcases Q.r0 with hs | hs
  · exact absurd (hs _ hQ) (by decide)
  · have h2 := hw 1 (Nat.le_refl 1) (false, true) (hs _ (by decide))
    rcases h2 with h3 | h3
    · exact h3
    · rcases h3 with h3 | ⟨_, h3 | h3⟩ <;> simp [rop, ru] at h3
end T1c1

open Iris Iris.BI T1c1 in
-- `Iris.intuitionistic_laterable` idx 4: necessary (TR (non-affine step-indexed BI on Bool×Bool, exact emp at every step so emp timeless, step-0 slices inside {unit} or containing all non-units), P = everything at step 0, unit and (true,false) at step 1: persistent, not affine, not laterable)
theorem t1c1_26 : ¬ drop0% Iris.intuitionistic_laterable 4 := fun h => tP_nonlat (@h TR trBI tP trEmpT tPpers)



namespace T1c1
open Iris Iris.BI Iris.OFE

/-! PQ b: the classical affine BI on Bool → Prop (componentwise; sep = and, persistently = later = id) with a
non-discrete OFE: for b = false every two props are 0-close (PROP2), for b = true 0-close means equal at
`true` (PROP1, finer). The identity embedding PQ true → PQ false is a BiEmbed. -/
def PQ (_ : Bool) := Bool → Prop

instance pqOFE (b : Bool) : OFE (PQ b) where
  Dist n x y := (n = 0 ∧ (b = true → x true = y true)) ∨ x = y
  dist_eqv := ⟨fun _ => .inr rfl,
    fun h => h.elim (fun ⟨h0, h1⟩ => .inl ⟨h0, fun e => (h1 e).symm⟩) (fun e => .inr e.symm),
    fun h1 h2 => by
      rcases h1 with ⟨a0, a1⟩ | rfl
      · rcases h2 with ⟨_, b1⟩ | rfl
        · exact .inl ⟨a0, fun e => (a1 e).trans (b1 e)⟩
        · exact .inl ⟨a0, a1⟩
      · exact h2⟩
  eq_dist' := ⟨fun e _ => .inr e, fun h => (h 1).elim (fun ⟨h0, _⟩ => nomatch h0) id⟩
  dist_lt h hlt := h.elim (fun ⟨h0, _⟩ => absurd hlt (by omega)) .inr

theorem pq_mk {b n} {x y : PQ b} (h1 : n ≠ 0 → ∀ c, x c ↔ y c) (h2 : b = true → (x true ↔ y true)) :
    x ≡{n}≡ y := by
  by_cases hn : n = 0
  · exact .inl ⟨hn, fun e => propext (h2 e)⟩
  · exact .inr (funext fun c => propext (h1 hn c))
theorem pq_get {b n} {x y : PQ b} (h : x ≡{n}≡ y) : (n ≠ 0 → ∀ c, x c = y c) ∧ (b = true → x true = y true) :=
  match h with
  | .inl ⟨h0, h1⟩ => ⟨fun hn => absurd h0 hn, h1⟩
  | .inr e => ⟨fun _ _ => e ▸ rfl, fun _ => e ▸ rfl⟩

instance pqCOFE (b : Bool) : COFE (PQ b) where
  compl c := c 1
  conv_compl {n c} := by
    cases n with
    | zero => exact c.cauchy (Nat.zero_le 1)
    | succ k =>
      have h := c.cauchy (n := 1) (i := k + 1) (by omega)
      rcases h with ⟨h0, _⟩ | e
      · cases h0
      · exact .inr e.symm

theorem pq_ne2 {b} (f : Prop → Prop → Prop) :
    @NonExpansive₂ (PQ b) (PQ b) (PQ b) _ _ _ (fun (x y : PQ b) => (fun c => f (x c) (y c) : PQ b)) :=
  ⟨fun _ _ _ h1 _ _ h2 => pq_mk (fun hn c => by rw [(pq_get h1).1 hn c, (pq_get h2).1 hn c])
    (fun e => by show f _ _ ↔ f _ _; rw [(pq_get h1).2 e, (pq_get h2).2 e])⟩

instance pqBase (b : Bool) : BIBase (PQ b) where
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
  persistently P x := P x
  later P        x := P x

theorem pq_liftRel {b n} {Ψ Ψ' : PQ b → Prop} (h : liftRel (Dist n) Ψ Ψ') (c : Bool)
    (hc : n ≠ 0 ∨ (b = true ∧ c = true)) :
    (∀ p, Ψ p → (∃ p', Ψ' p' ∧ (p c ↔ p' c))) ∧ (∀ p', Ψ' p' → (∃ p, Ψ p ∧ (p c ↔ p' c))) := by
  have key : ∀ {p p' : PQ b}, p ≡{n}≡ p' → (p c ↔ p' c) := fun hd => by
    rcases hc with hn | ⟨hb, rfl⟩
    · rw [(pq_get hd).1 hn c]
    · rw [(pq_get hd).2 hb]
  exact ⟨fun p hp => let ⟨p', hp', hd⟩ := h.1 p hp; ⟨p', hp', key hd⟩,
    fun p' hp' => let ⟨p, hp, hd⟩ := h.2 p' hp'; ⟨p, hp, key hd⟩⟩

instance pqBI (b : Bool) : BI (PQ b) where
  entails_refl _ h := h
  entails_trans h1 h2 x h := h2 x (h1 x h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h₁, h₂⟩ => funext fun σ => propext ⟨h₁ σ, h₂ σ⟩⟩
  and_ne          := pq_ne2 And
  or_ne           := pq_ne2 Or
  imp_ne          := pq_ne2 (fun a b => a → b)
  sep_ne          := pq_ne2 And
  wand_ne         := pq_ne2 (fun a b => a → b)
  persistently_ne := ⟨fun _ _ _ h => h⟩
  later_ne        := ⟨fun _ _ _ h => h⟩
  sForall_ne {n Ψ Ψ'} h := pq_mk
    (fun hn c => let k := pq_liftRel h c (.inl hn)
      ⟨fun H p' hp' => let ⟨p, hp, e⟩ := k.2 p' hp'; e.1 (H p hp),
       fun H p hp => let ⟨p', hp', e⟩ := k.1 p hp; e.2 (H p' hp')⟩)
    (fun hb => let k := pq_liftRel h true (.inr ⟨hb, rfl⟩)
      ⟨fun H p' hp' => let ⟨p, hp, e⟩ := k.2 p' hp'; e.1 (H p hp),
       fun H p hp => let ⟨p', hp', e⟩ := k.1 p hp; e.2 (H p' hp')⟩)
  sExists_ne {n Ψ Ψ'} h := pq_mk
    (fun hn c => let k := pq_liftRel h c (.inl hn)
      ⟨fun ⟨p, hp, H⟩ => let ⟨p', hp', e⟩ := k.1 p hp; ⟨p', hp', e.1 H⟩,
       fun ⟨p', hp', H⟩ => let ⟨p, hp, e⟩ := k.2 p' hp'; ⟨p, hp, e.2 H⟩⟩)
    (fun hb => let k := pq_liftRel h true (.inr ⟨hb, rfl⟩)
      ⟨fun ⟨p, hp, H⟩ => let ⟨p', hp', e⟩ := k.1 p hp; ⟨p', hp', e.1 H⟩,
       fun ⟨p', hp', H⟩ => let ⟨p, hp, e⟩ := k.2 p' hp'; ⟨p, hp, e.2 H⟩⟩)
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
  persistently_mono h x hP := h x hP
  persistently_idem_2 _ h := h
  persistently_emp_2 _ _ := trivial
  persistently_and_2 _ h := h
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr fun _ => h

/-- Identity embedding PQ true → PQ false (the coarser OFE). -/
@[instance_reducible] def pqE : BiEmbed (PQ true) (PQ false) where
  embed P := P
  ne := ⟨fun _ _ _ h => pq_mk (fun hn c => by rw [(pq_get h).1 hn c]) (fun e => nomatch e)⟩
  mono := fun h => h
  emp_valid_inj := fun _ h => h
  emp_2 := fun _ h => h
  impl_2 := fun _ _ _ h => h
  forall_2 := fun _ _ h x hR p hp => h p hp x hR
  exist_1 := fun _ _ h x ⟨p, hp, hx⟩ => h p hp x hx
  sep := fun _ _ => ⟨fun _ h => h, fun _ h => h⟩
  wand_2 := fun _ _ _ h => h
  persistently := fun _ => ⟨fun _ h => h, fun _ h => h⟩

/-- A commutative monoid op: first component (false) is and, second (true) is a2 ∧ b2 ∧ (a1 ∨ b1). -/
def mop {b : Bool} (x y : PQ b) : PQ b := fun c => match c with
  | false => x false ∧ y false
  | true => x true ∧ y true ∧ (x false ∨ y false)
def mu {b : Bool} : PQ b := fun _ => True

theorem mop_ext {b : Bool} {x y : PQ b} (h0 : x false ↔ y false) (h1 : x true ↔ y true) : x = y :=
  funext fun c => match c with
    | false => propext h0
    | true => propext h1

instance mopMon : Iris.Algebra.MonoidOps (mop (b := false)) mu where
  op_ne := ⟨fun n x₁ x₂ h1 y₁ y₂ h2 => pq_mk (fun hn c => by
      rw [show x₁ = x₂ from funext ((pq_get h1).1 hn), show y₁ = y₂ from funext ((pq_get h2).1 hn)])
      (fun e => nomatch e)⟩
  op_assoc {x y z} := mop_ext
    (by show ((x false ∧ y false) ∧ z false) ↔ (x false ∧ (y false ∧ z false)); exact and_assoc)
    (by
      show ((x true ∧ y true ∧ (x false ∨ y false)) ∧ z true ∧ ((x false ∧ y false) ∨ z false)) ↔
        (x true ∧ (y true ∧ z true ∧ (y false ∨ z false)) ∧ (x false ∨ (y false ∧ z false)))
      by_cases a : x false <;> by_cases b : y false <;> by_cases c : z false <;> simp [a, b, c] <;> (constructor <;> intro h <;> simp_all))
  op_comm {x y} := mop_ext
    (by show (x false ∧ y false) ↔ (y false ∧ x false); exact and_comm)
    (by
      show (x true ∧ y true ∧ (x false ∨ y false)) ↔ (y true ∧ x true ∧ (y false ∨ x false))
      by_cases a : x false <;> by_cases b : y false <;> simp [a, b] <;> (constructor <;> intro h <;> simp_all))
  op_left_id {x} := mop_ext
    (by show (True ∧ x false) ↔ x false; simp)
    (by show (True ∧ x true ∧ (True ∨ x false)) ↔ x true; simp)
end T1c1

open Iris Iris.BI T1c1 in
-- `Iris.BI.mkEmbedHom` idx 9: necessary (dependent: PQ true → PQ false identity embedding (Bool → Prop, PROP1 OFE finer at step 0), op = (a1 ∧ b1, a2 ∧ b2 ∧ (a1 ∨ b1)), unit True: lawful on PROP2, op not NonExpansive₂ on PROP1)
theorem t1c1_27 : ¬ indep0% Iris.BI.mkEmbedHom 9 := fun h => by
  have hm := @h (PQ true) (PQ false) _ _ pqE mop mop mu mu mopMon (fun {_ _} => rfl) rfl
  have hd := hm.op_ne.ne (n := 0) (x₁ := fun c => match c with | false => True | true => True)
    (x₂ := fun c => match c with | false => False | true => True) (.inl ⟨rfl, fun _ => rfl⟩)
    (y₁ := fun c => match c with | false => False | true => True)
    (y₂ := fun c => match c with | false => False | true => True) (.inr rfl)
  have := (pq_get hd).2 rfl
  have h2 : (True ∧ True ∧ (True ∨ False)) = (True ∧ True ∧ (False ∨ False)) := this
  simp at h2
