import Std
import Lean

/-!
Hand pass `WPRest` (hand15): the 202 unresolved hypotheses of `Std.WP` outside the spec lemmas
(`Basic`, `Frame`, `Conjunctive`, `Assertion`, `EStack`, `Monad.Sound`, `Monad.Conjunctive`,
`Triple.Basic/Conjunctive/Monad`, `Gadget.Assert`, `Gadget.ForIn`) and of `Std.Do` (`Do.WP.Sound`,
`Do.WP.Basic`, `Do.Triple.Basic`). Each declaration proves `¬T'` (`¬ drop0% T i`; for the 16
dependent rows `¬ indep0% T i`).

199 necessary, 0 removable, 0 independent; 3 left unresolved (`[LawfulMonad m]` of the `WPSound`
lifting instances for `StateT`/`ExceptT`/`OptionT`, see the final report).

Reusable models (namespace `WPRestHand`, Std.WP side; `open Lean.Order Std.WP`):
* `M3` (`bot, a, b, c, top`): the diamond as a classical `CompleteLattice` with decidable `M3.le`;
  `M3.himp_a_bot : a ⇨ ⊥ = top`, `M3.not_meet_himp_le`, `M3.not_heyting`, `M3.bot_eq`/`M3.top_eq`
  (`⊥`/`⊤` are the constructors), `M3.himp_fun_a_bot` (pointwise version on `Unit → M3`),
  `F2.nondet : NondetFun M3 F2 Bool` (values `a`/`b`, total).
* one-program `WP` types: `AngP` (angelic `∃ v, post v`, not conjunctive), `HonL` (honest over `M3`),
  `ExcM3` (`wp = (a ⊑ e)`, exception postconditions in `M3`), `HonPM3`, `HonPP`, `AngS` (angelic over
  states `Bool`), `ExcB` (`wp = E true`), `FC`/`FCE` (frame closures over the swap `sw`, whose action
  law fails), `botWP` (`wp ≡ False` on `Id Unit`).
* `WPMonad` models (synonyms of `Id`): `TopM` (`wp ≡ True`, unsound, lawful attach), `AngM`
  (`wp = ∃ a, post a`, not conjunctive, has `MonadTail`), `AngL` (`⨆ a, post a` over `M3`), `IdL`
  (honest over `M3`), `TrivA` (trivial non-lawful `MonadAttach`, `TrivA.not_lawful`).
* frame helpers: `not_ps_true`, `not_frameOp_true` (constant-`True` op), `sw`/`ps_sw` (swap on
  `Bool → Prop`), `swFrame`, `flip_not_frames` (`modify not` in `StateM Bool` does not frame).
* `ForIn`: `C1` (one element `0` for the `Id` loop, `Option` loops skip it), `C0` (empty membership).
Std.Do side (namespace `WPRestHand.Do`): `TopDo` (`wp ≡ ⌜True⌝`), `ZB` (copied from `DoSPredHand`,
`bind ≡ none`, `WPSound` with `wp ≡ ⌜True⌝`), `TrivDo` (trivial attach), `ent`/`ent1`/`trip`
(build `⊢ₛ`/triples in `SPred []`, `SPred [σ]`), `id_may`, `topdo_may`, `not_ensures_false`.

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/WPRestHand.lean`.
-/

set_option linter.unusedVariables false


open Lean Meta Elab Term in
/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

open Lean Meta Elab Term in
/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)



section WPPart
open Lean.Order Std.WP

open Lean.Order Std.WP

namespace WPRestHand

/-! ## Model `M3`: the five-element diamond lattice (not distributive, so not `Heyting`). -/

inductive M3 | bot | a | b | c | top
  deriving DecidableEq

def M3.le : M3 → M3 → Bool
  | .bot, _ => true
  | _, .top => true
  | x, y => x == y

/-- Join of the elements selected by five flags (for `bot, a, b, c, top`). -/
def M3.supB (p0 p1 p2 p3 p4 : Bool) : M3 :=
  if p4 then .top
  else if (p1 && p2) || (p1 && p3) || (p2 && p3) then .top
  else if p1 then .a else if p2 then .b else if p3 then .c else .bot

theorem M3.supB_spec (p0 p1 p2 p3 p4 : Bool) (y : M3) :
    M3.le (M3.supB p0 p1 p2 p3 p4) y = true ↔
      ((p0 = true → M3.le .bot y = true) ∧ (p1 = true → M3.le .a y = true) ∧
       (p2 = true → M3.le .b y = true) ∧ (p3 = true → M3.le .c y = true) ∧
       (p4 = true → M3.le .top y = true)) := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;> cases y <;> decide

instance : PartialOrder M3 where
  rel x y := M3.le x y = true
  rel_refl {x} := by cases x <;> rfl
  rel_trans {x y z} h1 h2 := by cases x <;> cases y <;> cases z <;> simp_all [M3.le]
  rel_antisymm {x y} h1 h2 := by cases x <;> cases y <;> simp_all [M3.le]

theorem M3.forall_iff (P : M3 → Prop) :
    (∀ x, P x) ↔ P .bot ∧ P .a ∧ P .b ∧ P .c ∧ P .top :=
  ⟨fun h => ⟨h _, h _, h _, h _, h _⟩, fun ⟨h0, h1, h2, h3, h4⟩ x => by cases x <;> assumption⟩

open Classical in
noncomputable instance : CompleteLattice M3 where
  has_sup c := ⟨M3.supB (decide (c .bot)) (decide (c .a)) (decide (c .b)) (decide (c .c))
      (decide (c .top)), fun y => by
    show M3.le _ y = true ↔ _
    rw [M3.supB_spec, M3.forall_iff]
    simp only [decide_eq_true_eq]; rfl⟩

theorem M3.rel_iff {x y : M3} : x ⊑ y ↔ M3.le x y = true := Iff.rfl

theorem M3.eq_bot_of_le_a_b {x : M3} (h1 : x ⊑ .a) (h2 : x ⊑ .b) : x = .bot := by
  cases x <;> simp_all [M3.rel_iff, M3.le]
theorem M3.eq_bot_of_le_a_c {x : M3} (h1 : x ⊑ .a) (h2 : x ⊑ .c) : x = .bot := by
  cases x <;> simp_all [M3.rel_iff, M3.le]
theorem M3.eq_bot_of_le_b_c {x : M3} (h1 : x ⊑ .b) (h2 : x ⊑ .c) : x = .bot := by
  cases x <;> simp_all [M3.rel_iff, M3.le]
theorem M3.eq_top_of_b_c_le {x : M3} (h1 : M3.b ⊑ x) (h2 : M3.c ⊑ x) : x = .top := by
  cases x <;> simp_all [M3.rel_iff, M3.le]
theorem M3.eq_top_of_a_b_le {x : M3} (h1 : M3.a ⊑ x) (h2 : M3.b ⊑ x) : x = .top := by
  cases x <;> simp_all [M3.rel_iff, M3.le]
theorem M3.not_a_le_bot : ¬ (M3.a ⊑ M3.bot) := fun h => Bool.noConfusion (h : M3.le .a .bot = true)
theorem M3.not_c_le_bot : ¬ (M3.c ⊑ M3.bot) := fun h => Bool.noConfusion (h : M3.le .c .bot = true)

theorem M3.meet_a_b : (M3.a ⊓ M3.b : M3) = .bot :=
  M3.eq_bot_of_le_a_b (meet_le_left _ _) (meet_le_right _ _)
theorem M3.meet_a_c : (M3.a ⊓ M3.c : M3) = .bot :=
  M3.eq_bot_of_le_a_c (meet_le_left _ _) (meet_le_right _ _)
theorem M3.meet_b_c : (M3.b ⊓ M3.c : M3) = .bot :=
  M3.eq_bot_of_le_b_c (meet_le_left _ _) (meet_le_right _ _)

/-- `a ⇨ ⊥ = ⊤` in `M3` (both `b` and `c` meet `a` in `⊥`). -/
theorem M3.himp_a_bot : (M3.a ⇨ M3.bot : M3) = .top :=
  M3.eq_top_of_b_c_le (le_himp_of_meet_le_left (by rw [M3.meet_a_b]; exact PartialOrder.rel_refl))
    (le_himp_of_meet_le_left (by rw [M3.meet_a_c]; exact PartialOrder.rel_refl))

theorem M3.a_le_meet_top : M3.a ⊑ (M3.a ⊓ M3.top : M3) :=
  le_meet _ _ _ PartialOrder.rel_refl (rfl : M3.le .a .top = true)

/-- `a ⊓ (a ⇨ ⊥) ⋢ ⊥`: modus ponens fails in `M3`. -/
theorem M3.not_meet_himp_le : ¬ ((M3.a ⊓ (M3.a ⇨ M3.bot) : M3) ⊑ M3.bot) := by
  rw [M3.himp_a_bot]; intro h; exact M3.not_a_le_bot (PartialOrder.rel_trans M3.a_le_meet_top h)

theorem M3.not_heyting : ¬ Heyting M3 := fun h =>
  M3.not_meet_himp_le (@meet_himp_le M3 _ M3.a M3.bot (h M3.a))

end WPRestHand

namespace WPRestHand
theorem M3.bot_eq : (⊥ : M3) = .bot := PartialOrder.rel_antisymm (bot_le _) (rfl : M3.le .bot _ = true)
theorem M3.top_eq : (⊤ : M3) = .top :=
  PartialOrder.rel_antisymm (by cases (⊤ : M3) <;> rfl) (le_top _)
end WPRestHand

namespace WPRestHand

/-! ## `WP` models on one-program types (`Value := Unit` or `Bool`). -/

/-- Angelic chaos: `wp _ post _ = ∃ v, post v` (monotone, not conjunctive). -/
inductive AngP | mk
instance AngP.wp : WP AngP Bool Prop EStackEnd where
  trans _ := ⟨fun post _ => ∃ v, post v⟩
  trans_monotone _ := fun _ _ _ _ _ hp ⟨v, h⟩ => ⟨v, hp v h⟩

/-- Honest program over `M3`: `wp _ post _ = post ()`. -/
inductive HonL | mk
instance HonL.wp : WP HonL Unit M3 EStackEnd where
  trans _ := ⟨fun post _ => post ()⟩
  trans_monotone _ := fun _ _ _ _ _ hp => hp ()
instance HonL.conj (x : HonL) : WPConjunctive x where
  wp_meet_wp_le q1 q2 _ _ := by
    show q1 () ⊓ q2 () ⊑ (q1 ⊓ q2) ()
    rw [meet_apply]

/-- Exception-only program over `M3` exception postconditions: `wp _ _ e = (a ⊑ e)`. -/
inductive ExcM3 | mk
instance ExcM3.wp : WP ExcM3 Unit Prop M3 where
  trans _ := ⟨fun _ e => M3.a ⊑ e⟩
  trans_monotone _ := fun _ _ _ _ he _ h => PartialOrder.rel_trans h he
instance ExcM3.conj (x : ExcM3) : WPConjunctive x where
  wp_meet_wp_le _ _ e1 e2 := by
    show (M3.a ⊑ e1) ⊓ (M3.a ⊑ e2) ⊑ (M3.a ⊑ e1 ⊓ e2)
    rw [meet_prop_eq_and]; exact fun ⟨h1, h2⟩ => le_meet _ _ _ h1 h2

/-- Honest program over `Prop` with `M3` exception postconditions: `wp _ post _ = post ()`. -/
inductive HonPM3 | mk
instance HonPM3.wp : WP HonPM3 Unit Prop M3 where
  trans _ := ⟨fun post _ => post ()⟩
  trans_monotone _ := fun _ _ _ _ _ hp => hp ()

/-! ## Monad models (synonyms of `Id`). -/

/-- `wp ≡ True`: a lawful `WPMonad` that proves everything (unsound). -/
def TopM : Type → Type := Id
instance : Monad TopM := inferInstanceAs (Monad Id)
instance : MonadAttach TopM := inferInstanceAs (MonadAttach Id)
instance : LawfulMonadAttach TopM := inferInstanceAs (LawfulMonadAttach Id)
instance TopM.wpm : WPMonad TopM Prop EStackEnd where
  toLawfulMonad := inferInstanceAs (LawfulMonad Id)
  toWP _ := { trans := fun _ => ⟨fun _ _ => True⟩, trans_monotone := fun _ _ _ _ _ _ _ h => h }
  pure_le_wp_pure _ _ _ := fun _ => trivial
  bind_le_wp_bind _ _ _ _ := fun _ => trivial

/-- Angelic chaos: `wp x post _ = ∃ a, post a` (lawful `WPMonad`, not conjunctive). -/
def AngM : Type → Type := Id
instance : Monad AngM := inferInstanceAs (Monad Id)
instance : MonadTail AngM := inferInstanceAs (MonadTail Id)
instance AngM.wpm : WPMonad AngM Prop EStackEnd where
  toLawfulMonad := inferInstanceAs (LawfulMonad Id)
  toWP _ := { trans := fun _ => ⟨fun post _ => ∃ a, post a⟩,
              trans_monotone := fun _ _ _ _ _ _ hp ⟨a, h⟩ => ⟨a, hp a h⟩ }
  pure_le_wp_pure x _ _ := fun h => ⟨x, h⟩
  bind_le_wp_bind _ _ _ _ := fun ⟨_, b, h⟩ => ⟨b, h⟩

/-- `Id` with the trivial (`CanReturn _ _ := True`) attach, which is not lawful. -/
def TrivA : Type → Type := Id
instance : Monad TrivA := inferInstanceAs (Monad Id)
instance : MonadAttach TrivA := @MonadAttach.trivial TrivA _
instance TrivA.wpm : WPMonad TrivA Prop EStackEnd := inferInstanceAs (WPMonad Id Prop EStackEnd)

theorem TrivA.not_lawful : ¬ LawfulMonadAttach TrivA := fun h =>
  Nat.succ_ne_zero 0 (h.canReturn_map_imp (P := fun n : Nat => n = 0)
    (x := (pure ⟨0, rfl⟩ : TrivA {n : Nat // n = 0})) (a := 1) trivial)

/-- Honest `Id` with `M3` assertions: `wp x post _ = post x`. -/
def IdL : Type → Type := Id
instance : Monad IdL := inferInstanceAs (Monad Id)
instance : MonadTail IdL := inferInstanceAs (MonadTail Id)
instance IdL.wpm : WPMonad IdL M3 EStackEnd where
  toLawfulMonad := inferInstanceAs (LawfulMonad Id)
  toWP _ := { trans := fun x => ⟨fun post _ => post x⟩, trans_monotone := fun x _ _ _ _ _ hp => hp x }
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := PartialOrder.rel_refl

end WPRestHand

namespace WPRestHand


/-! ## Std.WP.Basic -/

-- `Std.WP.WP.wp_monotone_post`: `Id`, precondition `True`, postcondition `False`.
theorem wp_monotone_post_11 : ¬ drop0% Std.WP.WP.wp_monotone_post 11 :=
  fun H => H (Prog := Id Unit) (x := ()) (post := fun _ => True) (post' := fun _ => False) (eposts := ()) trivial

-- `Std.WP.WP.wp_monotone`: `Id`, precondition `True`, postcondition `False`.
theorem wp_monotone_12 : ¬ drop0% Std.WP.WP.wp_monotone 12 :=
  fun H => H (Prog := Id Unit) (x := ()) (post := fun _ => True) (post' := fun _ => False) (eposts := ()) (eposts' := ()) PartialOrder.rel_refl trivial

-- `Std.WP.WP.wp_monotone`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_monotone_13 : ¬ drop0% Std.WP.WP.wp_monotone 13 :=
  fun H => H (Prog := Option Unit) (x := none) (post := fun _ => True) (post' := fun _ => True) (eposts := fun _ => True) (eposts' := fun _ => False) PartialOrder.rel_refl trivial

-- `Std.WP.WP.wp_monotone_epost`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_monotone_epost_11 : ¬ drop0% Std.WP.WP.wp_monotone_epost 11 :=
  fun H => H (Prog := Option Unit) (x := none) (post := fun _ => True) (eposts := fun _ => True) (eposts' := fun _ => False) trivial

-- `Std.WP.WP.wp_monotone_post_le`: `Id`, precondition `True`, postcondition `False`.
theorem wp_monotone_post_le_11 : ¬ drop0% Std.WP.WP.wp_monotone_post_le 11 :=
  fun H => H (Prog := Id Unit) () (fun _ => True) (fun _ => False) () (pre := True) (fun h => h) trivial

-- `Std.WP.WP.wp_monotone_post_le`: `Id`, precondition `True`, postcondition `False`.
theorem wp_monotone_post_le_13 : ¬ drop0% Std.WP.WP.wp_monotone_post_le 13 :=
  fun H => H (Prog := Id Unit) () (fun _ => False) (fun _ => False) () PartialOrder.rel_refl (pre := True) trivial

-- `Std.WP.WP.wp_monotone_epost_le`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_monotone_epost_le_11 : ¬ drop0% Std.WP.WP.wp_monotone_epost_le 11 :=
  fun H => H (Prog := Option Unit) none (fun _ => True) (fun _ => True) (fun _ => False) (pre := True) (fun h => h) trivial

-- `Std.WP.WP.wp_monotone_epost_le`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_monotone_epost_le_13 : ¬ drop0% Std.WP.WP.wp_monotone_epost_le 13 :=
  fun H => H (Prog := Option Unit) none (fun _ => True) (fun _ => False) (fun _ => False) PartialOrder.rel_refl (pre := True) trivial

-- `Std.WP.WP.wp_monotone_bot_le`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_monotone_bot_le_11 : ¬ drop0% Std.WP.WP.wp_monotone_bot_le 11 :=
  fun H => H (Prog := Option Unit) none (fun _ => True) (fun _ => False) (pre := True) trivial

-- `Std.WP.WP.wp_consequence`: `Id`, precondition `True`, postcondition `False`.
theorem wp_consequence_11 : ¬ drop0% Std.WP.WP.wp_consequence 11 :=
  fun H => H (Prog := Id Unit) () (fun _ => True) (fun _ => False) () trivial

-- `Std.WP.WP.wp_consequence_econs`: `Id`, precondition `True`, postcondition `False`.
theorem wp_consequence_econs_12 : ¬ drop0% Std.WP.WP.wp_consequence_econs 12 :=
  fun H => H (Prog := Id Unit) () (fun _ => True) (fun _ => False) () () PartialOrder.rel_refl trivial

-- `Std.WP.WP.wp_consequence_econs`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_consequence_econs_13 : ¬ drop0% Std.WP.WP.wp_consequence_econs 13 :=
  fun H => H (Prog := Option Unit) none (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => False) PartialOrder.rel_refl trivial

-- `Std.WP.WP.wp_econs`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_econs_11 : ¬ drop0% Std.WP.WP.wp_econs 11 :=
  fun H => H (Prog := Option Unit) none (fun _ => True) (fun _ => True) (fun _ => False) trivial

-- `Std.WP.WP.wp_consequence_le`: `Id`, precondition `True`, postcondition `False`.
theorem wp_consequence_le_11 : ¬ drop0% Std.WP.WP.wp_consequence_le 11 :=
  fun H => H (Prog := Id Unit) () (fun _ => True) (fun _ => False) () (pre := True) (fun h => h) trivial

-- `Std.WP.WP.wp_consequence_le`: `Id`, precondition `True`, postcondition `False`.
theorem wp_consequence_le_13 : ¬ drop0% Std.WP.WP.wp_consequence_le 13 :=
  fun H => H (Prog := Id Unit) () (fun _ => False) (fun _ => False) () PartialOrder.rel_refl (pre := True) trivial

-- `Std.WP.WP.wp_econs_le`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_econs_le_11 : ¬ drop0% Std.WP.WP.wp_econs_le 11 :=
  fun H => H (Prog := Option Unit) none (fun _ => True) (fun _ => True) (fun _ => False) (pre := True) (fun h => h) trivial

-- `Std.WP.WP.wp_econs_le`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_econs_le_13 : ¬ drop0% Std.WP.WP.wp_econs_le 13 :=
  fun H => H (Prog := Option Unit) none (fun _ => True) (fun _ => False) (fun _ => False) PartialOrder.rel_refl (pre := True) trivial

-- `Std.WP.WP.wp_econs_bot_le`: `none` in `Option` reads the exception postcondition; `True` there, `False` after weakening.
theorem wp_econs_bot_le_11 : ¬ drop0% Std.WP.WP.wp_econs_bot_le 11 :=
  fun H => H (Prog := Option Unit) none (fun _ => True) (fun _ => False) (pre := True) trivial

-- `Std.WP.wp_le_wp_of_eq`: `x = false`, `y = true` in `Id Bool`, postcondition `(· = true)`.
theorem wp_le_wp_of_eq_9 : ¬ drop0% Std.WP.wp_le_wp_of_eq 9 :=
  fun H => Bool.noConfusion (H (Prog := Id Bool) (x := false) (y := true) (fun b => b = true) () rfl : false = true)

/-! ## Std.WP.Triple.Basic / Triple.Monad -/

-- `Std.WP.Triple.le_wp`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_le_wp_11 : ¬ drop0% Std.WP.Triple.le_wp 11 :=
  fun H => H (Prog := Id Unit) (x := ()) (pre := True) (post := fun _ => False) (eposts := ()) trivial

-- `Std.WP.Triple.entails_wp_of_pre_post`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_entails_wp_of_pre_post_13 : ¬ drop0% Std.WP.Triple.entails_wp_of_pre_post 13 :=
  fun H => H (Prog := Id Unit) (x := ()) (pre := True) (pre' := True) (post := fun _ => False) (post' := fun _ => False) (eposts := ()) (fun h => h) PartialOrder.rel_refl trivial

-- `Std.WP.Triple.entails_wp_of_pre_post`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_entails_wp_of_pre_post_14 : ¬ drop0% Std.WP.Triple.entails_wp_of_pre_post 14 :=
  fun H => H (Prog := Id Unit) (x := ()) (pre := True) (pre' := False) (post := fun _ => False) (post' := fun _ => False) (eposts := ()) ⟨False.elim⟩ PartialOrder.rel_refl trivial

-- `Std.WP.Triple.entails_wp_of_pre_post`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_entails_wp_of_pre_post_15 : ¬ drop0% Std.WP.Triple.entails_wp_of_pre_post 15 :=
  fun H => H (Prog := Id Unit) (x := ()) (pre := True) (pre' := True) (post := fun _ => False) (post' := fun _ => True) (eposts := ()) ⟨fun h => h⟩ (fun h => h) trivial

-- `Std.WP.Triple.entails_wp_of_pre`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_entails_wp_of_pre_12 : ¬ drop0% Std.WP.Triple.entails_wp_of_pre 12 :=
  fun H => H (Prog := Id Unit) (x := ()) (pre := True) (pre' := True) (post := fun _ => False) (eposts := ()) (fun h => h) trivial

-- `Std.WP.Triple.entails_wp_of_pre`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_entails_wp_of_pre_13 : ¬ drop0% Std.WP.Triple.entails_wp_of_pre 13 :=
  fun H => H (Prog := Id Unit) (x := ()) (pre := True) (pre' := False) (post := fun _ => False) (eposts := ()) ⟨False.elim⟩ trivial

-- `Std.WP.Triple.entails_wp_of_post`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_entails_wp_of_post_12 : ¬ drop0% Std.WP.Triple.entails_wp_of_post 12 :=
  fun H => H (Prog := Id Unit) (x := ()) (pre := True) (post := fun _ => False) (post' := fun _ => False) (eposts := ()) PartialOrder.rel_refl trivial

-- `Std.WP.Triple.entails_wp_of_post`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_entails_wp_of_post_13 : ¬ drop0% Std.WP.Triple.entails_wp_of_post 13 :=
  fun H => H (Prog := Id Unit) (x := ()) (pre := True) (post := fun _ => False) (post' := fun _ => True) (eposts := ()) ⟨fun h => h⟩ trivial

-- `Std.WP.Triple.pure`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_pure_12 : ¬ drop0% Std.WP.Triple.pure 12 :=
  fun H => (H (m := Id) (pre := True) (post := fun _ => False) (eposts := ()) ()).le_wp trivial

-- `Std.WP.Triple.bind`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_bind_15 : ¬ drop0% Std.WP.Triple.bind 15 :=
  fun H => (H (m := Id) (pre := True) (post := fun _ => False) (eposts := ()) (pure ()) (fun _ => pure ())
    (fun _ => False) (fun _ => ⟨False.elim⟩)).le_wp trivial

-- `Std.WP.Triple.bind`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_bind_16 : ¬ drop0% Std.WP.Triple.bind 16 :=
  fun H => (H (m := Id) (pre := True) (post := fun _ => False) (eposts := ()) (pure ()) (fun _ => pure ())
    (fun _ => True) ⟨fun h => h⟩).le_wp trivial

-- `Std.WP.Triple.map`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_map_15 : ¬ drop0% Std.WP.Triple.map 15 :=
  fun H => (H (m := Id) (pre := True) (post := fun _ => False) (eposts := ()) (fun _ : Unit => ()) (pure ())).le_wp trivial

-- `Std.WP.Triple.seq`: `Id`, precondition `True`, postcondition `False`.
theorem Triple_seq_15 : ¬ drop0% Std.WP.Triple.seq 15 :=
  fun H => (H (m := Id) (pre := True) (post := fun _ => False) (eposts := ()) (pure (fun _ : Unit => ())) (pure ())).le_wp trivial

end WPRestHand

namespace WPRestHand

/-! ## Std.WP.Triple.Conjunctive, Std.WP.Conjunctive -/

-- `Std.WP.Triple.and`: the angelic `AngP` meets `∃ v, v = true` and `∃ v, v = false` but not their meet.
theorem Triple_and_8 : ¬ drop0% Std.WP.Triple.and 8 := by
  intro H
  have h := (H (x := AngP.mk) (pre₁ := True) (pre₂ := True) (post₁ := fun v => v = true)
    (post₂ := fun v => v = false) (eposts₁ := ()) (eposts₂ := ()) ⟨fun _ => ⟨true, rfl⟩⟩
    ⟨fun _ => ⟨false, rfl⟩⟩).le_wp
  rw [meet_prop_eq_and] at h
  obtain ⟨v, hv⟩ := h ⟨trivial, trivial⟩
  rw [meet_apply, meet_prop_eq_and] at hv
  exact Bool.noConfusion (hv.1.symm.trans hv.2)

-- `Std.WP.Triple.and`: `Id`, first triple `⦃True⦄ () ⦃False⦄` false.
theorem Triple_and_15 : ¬ drop0% Std.WP.Triple.and 15 := by
  intro H
  have h := (H (Prog := Id Unit) (x := ()) (pre₁ := True) (pre₂ := True) (post₁ := fun _ => False)
    (post₂ := fun _ => True) (eposts₁ := ()) (eposts₂ := ()) ⟨fun h => h⟩).le_wp
  rw [meet_prop_eq_and] at h
  have h' : ((fun _ : Unit => False) ⊓ (fun _ => _) : Unit → Prop) () := h ⟨trivial, trivial⟩
  rw [meet_apply, meet_prop_eq_and] at h'
  exact h'.1

-- `Std.WP.Triple.and`: symmetric.
theorem Triple_and_16 : ¬ drop0% Std.WP.Triple.and 16 := by
  intro H
  have h := (H (Prog := Id Unit) (x := ()) (pre₁ := True) (pre₂ := True) (post₁ := fun _ => True)
    (post₂ := fun _ => False) (eposts₁ := ()) (eposts₂ := ()) ⟨fun h => h⟩).le_wp
  rw [meet_prop_eq_and] at h
  have h' : ((fun _ : Unit => _) ⊓ (fun _ => False) : Unit → Prop) () := h ⟨trivial, trivial⟩
  rw [meet_apply, meet_prop_eq_and] at h'
  exact h'.2

/-- `x ⊑ p ⇨ q` for functions when `p v ∧ x v → q v` pointwise. -/
theorem le_himp_fun {α : Type} {p q x : α → Prop} (h : ∀ v, p v → x v → q v) : x ⊑ p ⇨ q :=
  le_himp_of_meet_le_left fun v => by rw [meet_apply, meet_prop_eq_and]; exact fun ⟨h1, h2⟩ => h v h1 h2

-- `Std.WP.Triple.mp`: the angelic `AngP` (not conjunctive).
theorem Triple_mp_8 : ¬ drop0% Std.WP.Triple.mp 8 := by
  intro H
  have h := (H (x := AngP.mk) (pre₁ := True) (pre₂ := True) (post₁ := fun v => v = true)
    (post₂ := fun _ => False) (eposts₁ := ()) (eposts₂ := ()) ⟨fun _ => ⟨true, rfl⟩⟩
    ⟨fun _ => ⟨false, le_himp_fun (p := fun v => v = true) (x := fun v => v = false) (fun v h1 h2 => Bool.noConfusion (h1.symm.trans h2)) false rfl⟩⟩).le_wp
  rw [meet_prop_eq_and] at h
  obtain ⟨v, hv⟩ := h ⟨trivial, trivial⟩
  rw [meet_apply, meet_prop_eq_and] at hv
  exact hv.2

/-- In `Unit → M3`: `(fun _ => a) ⇨ (fun _ => ⊥)` is `⊤` at `()`. -/
theorem M3.himp_fun_a_bot : ((fun _ : Unit => M3.a) ⇨ (fun _ => M3.bot)) () = M3.top := by
  apply M3.eq_top_of_b_c_le
  · exact le_himp_of_meet_le_left (x := fun _ : Unit => M3.b) (fun _ => by
      rw [meet_apply]; exact PartialOrder.rel_of_eq M3.meet_a_b) ()
  · exact le_himp_of_meet_le_left (x := fun _ : Unit => M3.c) (fun _ => by
      rw [meet_apply]; exact PartialOrder.rel_of_eq M3.meet_a_c) ()

-- `Std.WP.Triple.mp`: `HonL` over the non-Heyting `M3`; `a ⊓ (a ⇨ ⊥) ⋢ ⊥`.
theorem Triple_mp_9 : ¬ drop0% Std.WP.Triple.mp 9 := by
  intro H
  have h := (H (x := HonL.mk) (pre₁ := M3.a) (pre₂ := ((fun _ : Unit => M3.a) ⇨ (fun _ => M3.bot)) ())
    (post₁ := fun _ => M3.a) (post₂ := fun _ => M3.bot) (eposts₁ := ()) (eposts₂ := ())
    ⟨PartialOrder.rel_refl⟩ ⟨PartialOrder.rel_refl⟩).le_wp
  change _ ⊑ ((fun _ : Unit => M3.a) ⊓ (fun _ => M3.bot)) () at h
  rw [meet_apply, M3.himp_fun_a_bot] at h
  exact M3.not_a_le_bot (PartialOrder.rel_trans M3.a_le_meet_top
    (PartialOrder.rel_trans h (meet_le_right _ _)))

-- `Std.WP.Triple.mp`: `ExcM3` with exception postconditions in the non-Heyting `M3`.
theorem Triple_mp_10 : ¬ drop0% Std.WP.Triple.mp 10 := by
  intro H
  have h := (H (x := ExcM3.mk) (pre₁ := True) (pre₂ := True) (post₁ := fun _ => True)
    (post₂ := fun _ => True) (eposts₁ := M3.a) (eposts₂ := M3.bot)
    ⟨fun _ => PartialOrder.rel_refl⟩
    ⟨fun _ => by show M3.a ⊑ (M3.a ⇨ M3.bot); rw [M3.himp_a_bot]; exact (rfl : M3.le .a .top = true)⟩).le_wp
  rw [meet_prop_eq_and] at h
  exact M3.not_a_le_bot (PartialOrder.rel_trans (h ⟨trivial, trivial⟩) (meet_le_right _ _))

-- `Std.WP.Triple.mp`: `Id`, first triple `⦃True⦄ () ⦃False⦄` false.
theorem Triple_mp_17 : ¬ drop0% Std.WP.Triple.mp 17 := by
  intro H
  have h := (H (Prog := Id Unit) (x := ()) (pre₁ := True) (pre₂ := True) (post₁ := fun _ => False)
    (post₂ := fun _ => False) (eposts₁ := ()) (eposts₂ := ())
    ⟨fun _ => le_himp_fun (p := fun _ : Unit => False) (q := fun _ => False) (x := fun _ => True)
      (fun _ h _ => h) () trivial⟩).le_wp
  rw [meet_prop_eq_and] at h
  have h' : ((fun _ : Unit => False) ⊓ (fun _ => _) : Unit → Prop) () := h ⟨trivial, trivial⟩
  rw [meet_apply, meet_prop_eq_and] at h'
  exact h'.1

-- `Std.WP.Triple.mp`: `Id`, second triple dropped, `post₂ = False`.
theorem Triple_mp_18 : ¬ drop0% Std.WP.Triple.mp 18 := by
  intro H
  have h := (H (Prog := Id Unit) (x := ()) (pre₁ := True) (pre₂ := True) (post₁ := fun _ => True)
    (post₂ := fun _ => False) (eposts₁ := ()) (eposts₂ := ()) ⟨fun h => h⟩).le_wp
  rw [meet_prop_eq_and] at h
  have h' : ((fun _ : Unit => _) ⊓ (fun _ => False) : Unit → Prop) () := h ⟨trivial, trivial⟩
  rw [meet_apply, meet_prop_eq_and] at h'
  exact h'.2

-- `Std.WP.Triple.observe`: `HonL` over the non-Heyting `M3` for `obs` and `prog`.
theorem Triple_observe_10 : ¬ drop0% Std.WP.Triple.observe 10 := by
  intro H
  have h := (H (obs := HonL.mk) (prog := HonL.mk) (pre := M3.a) (post := fun _ => M3.a) (eposts := ())
    (post' := fun _ => M3.bot) (eposts' := ()) (fun _ => PartialOrder.rel_refl) ⟨PartialOrder.rel_refl⟩
    ⟨by show M3.a ⊑ ((fun _ : Unit => M3.a) ⇨ (fun _ => M3.bot)) ()
        rw [M3.himp_fun_a_bot]; exact (rfl : M3.le .a .top = true)⟩).le_wp
  exact M3.not_a_le_bot h

-- `Std.WP.Triple.observe`: `obs := ExcM3`, `prog := HonPM3` (exception postconditions in `M3`).
theorem Triple_observe_11 : ¬ drop0% Std.WP.Triple.observe 11 := by
  intro H
  have h := (H (obs := ExcM3.mk) (prog := HonPM3.mk) (pre := True) (post := fun _ => True)
    (eposts := M3.a) (post' := fun _ => False) (eposts' := M3.a)
    (fun _ h => absurd (M3.bot_eq ▸ h : M3.a ⊑ M3.bot) M3.not_a_le_bot) ⟨fun _ => PartialOrder.rel_refl⟩
    ⟨fun _ => by show M3.a ⊑ (M3.a ⇨ ⊥); rw [M3.bot_eq, M3.himp_a_bot]; exact (rfl : M3.le .a .top = true)⟩).le_wp
  exact h trivial

-- `Std.WP.Triple.observe`: `obs := AngP` (not conjunctive), `prog := ()` in `Id`.
theorem Triple_observe_13 : ¬ drop0% Std.WP.Triple.observe 13 := by
  intro H
  have h := (H (obs := AngP.mk) (Prog' := Id Unit) (prog := ()) (pre := True) (post := fun v => v = true)
    (eposts := ()) (post' := fun _ => False) (eposts' := ()) (fun C h => (show ∃ _ : Bool, C from h).elim fun _ h => h) ⟨fun _ => ⟨true, rfl⟩⟩
    ⟨fun _ => ⟨false, le_himp_fun (p := fun v => v = true) (x := fun v => v = false)
      (fun v h1 h2 => Bool.noConfusion (h1.symm.trans h2)) false rfl⟩⟩).le_wp
  exact h trivial

-- `Std.WP.Triple.observe`: `obs := set true` in `StateM Bool` changes the state.
theorem Triple_observe_20 : ¬ drop0% Std.WP.Triple.observe 20 := by
  intro H
  have h := (H (obs := (set true : StateM Bool PUnit)) (prog := (pure () : StateM Bool Unit))
    (pre := fun s => s = false) (post := fun _ _ => True) (eposts := ()) (post' := fun _ s => s = true)
    (eposts' := ()) ⟨fun _ _ => trivial⟩
    ⟨fun s _ => le_himp_of_meet_le_left (x := fun _ s => s = true) (meet_le_right _ _) () true rfl⟩).le_wp
  exact Bool.noConfusion (h false rfl)

-- `Std.WP.Triple.observe`: `Id`, `post = False` makes `hgoal` trivial.
theorem Triple_observe_21 : ¬ drop0% Std.WP.Triple.observe 21 := by
  intro H
  have h := (H (Prog := Id Unit) (Prog' := Id Unit) (obs := ()) (prog := ()) (pre := True) (post := fun _ => False)
    (eposts := ()) (post' := fun _ => False) (eposts' := ()) (fun _ => PartialOrder.rel_refl)
    ⟨fun _ => le_himp_fun (p := fun _ : Unit => False) (q := fun _ => False) (x := fun _ => True)
      (fun _ h _ => h) () trivial⟩).le_wp
  exact h trivial

-- `Std.WP.Triple.observe`: `Id`, `post = True`, goal `False`.
theorem Triple_observe_22 : ¬ drop0% Std.WP.Triple.observe 22 := by
  intro H
  have h := (H (Prog := Id Unit) (Prog' := Id Unit) (obs := ()) (prog := ()) (pre := True) (post := fun _ => True)
    (eposts := ()) (post' := fun _ => False) (eposts' := ()) (fun _ => PartialOrder.rel_refl)
    ⟨fun h => h⟩).le_wp
  exact h trivial

-- `Std.WP.WPConjunctive.wp_meet_wp_le`: the angelic `AngP` is not conjunctive.
theorem WPConjunctive_wp_meet_wp_le_8 : ¬ drop0% Std.WP.WPConjunctive.wp_meet_wp_le 8 := by
  intro H
  have h := @H AngP Bool Prop EStackEnd inferInstance inferInstance AngP.wp AngP.mk
    (fun v => v = true) (fun v => v = false) () ()
  change (∃ v, v = true) ⊓ (∃ v, v = false) ⊑ ∃ v, ((fun v => v = true) ⊓ (fun v => v = false)) v at h
  rw [meet_prop_eq_and] at h
  obtain ⟨v, hv⟩ := h ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩
  rw [meet_apply, meet_prop_eq_and] at hv
  exact Bool.noConfusion (hv.1.symm.trans hv.2)

/-! ## Std.WP.Assertion, Std.WP.EStack, Std.WP.Gadget.Assert -/

-- `Std.WP.Assertion.NondetFun.le_of_total_le`: `True ⋢ False` in `Prop`.
theorem NondetFun_le_of_total_le_9 : ¬ drop0% Std.WP.Assertion.NondetFun.le_of_total_le 9 :=
  fun H => H (Pred := Prop) (Fun := Unit) () (P := True) (Q := False) trivial

/-- A total nondeterministic function into `Bool` over `M3`: `true ↦ a`, `false ↦ b`. -/
inductive F2 | mk
instance F2.nondet : Std.WP.Assertion.NondetFun M3 F2 Bool where
  EvalsTo _ v := if v then M3.a else M3.b
  total _ := by
    rw [M3.top_eq]
    exact M3.eq_top_of_a_b_le (le_iSup (fun v : Bool => if v then M3.a else M3.b) true)
      (le_iSup (fun v : Bool => if v then M3.a else M3.b) false)

-- `Std.WP.Assertion.NondetFun.le_of_total_le`: in `M3`, `c` meets both values `a`, `b` in `⊥`.
theorem NondetFun_le_of_total_le_8 : ¬ drop0% Std.WP.Assertion.NondetFun.le_of_total_le 8 := by
  intro H
  refine M3.not_c_le_bot (H (Pred := M3) (Fun := F2) (α := Bool) F2.mk (P := M3.c) (Q := M3.bot) ?_)
  refine iSup_le _ _ fun v => ?_
  cases v
  · exact PartialOrder.rel_of_eq M3.meet_b_c
  · exact PartialOrder.rel_of_eq M3.meet_a_c

instance PropToEStack : Std.WP.ToEStack Prop Prop := ⟨id, id⟩

-- `Std.WP.ToEStack.le_of_toEStack_le`: without the premise every `x ⊑ y`; `True ⋢ False`.
theorem ToEStack_le_of_toEStack_le_7 : ¬ drop0% Std.WP.ToEStack.le_of_toEStack_le 7 :=
  fun H => @H Prop Prop inferInstance inferInstance PropToEStack True False trivial

-- `Std.WP.Spec.assertGadget`: `IdL` over `M3`, `as = a`, `post = ⊥`.
theorem Spec_assertGadget_10 : ¬ drop0% Std.WP.Spec.assertGadget 10 :=
  fun H => M3.not_meet_himp_le (H (m := IdL) (post := fun _ => M3.bot) (eposts := ()) M3.a).le_wp

end WPRestHand

namespace WPRestHand

/-! ## Std.WP.Monad.Sound -/

theorem top_le_ofProp_true {p : Prop} (hp : p) : (⊤ : Prop) ⊑ ⌜p⌝ := by
  rw [CompleteLattice.ofProp_prop_eq]; exact fun _ => hp

theorem top_le_ofProp_fun {σ : Type} {p : Prop} (hp : p) (s : σ) : (⊤ : Prop) ⊑ (⌜p⌝ : σ → Prop) s := by
  rw [CompleteLattice.ofProp_apply]; exact top_le_ofProp_true hp

-- `Std.WP.LawfulWPMonadAttach.of_canReturn_wp`: `TrivA` (trivial attach) is not lawful.
theorem LawfulWPMonadAttach_of_canReturn_wp_5 : ¬ indep0% Std.WP.LawfulWPMonadAttach.of_canReturn_wp 5 :=
  fun H => TrivA.not_lawful (H (m := TrivA) (Pred := Prop) (EPosts := EStackEnd) (x := (pure 0 : TrivA Nat))
    (P := fun _ => True) (a := 0) trivial (top_le_ofProp_true trivial))

-- `Std.WP.LawfulWPMonadAttach.of_canReturn_wp`: `TopM` (`wp ≡ True`) proves `False` about `pure 0`.
theorem LawfulWPMonadAttach_of_canReturn_wp_9 : ¬ drop0% Std.WP.LawfulWPMonadAttach.of_canReturn_wp 9 :=
  fun H => @H TopM Prop EStackEnd inferInstance inferInstance inferInstance inferInstance inferInstance TopM.wpm
    Nat (pure 0) (fun _ => False) 0 rfl (fun _ => trivial)

-- `Std.WP.LawfulWPMonadAttach.of_canReturn_wp`: `pure 0` in `Id`, `a = 1`, `P = (· = 0)`.
theorem LawfulWPMonadAttach_of_canReturn_wp_14 : ¬ drop0% Std.WP.LawfulWPMonadAttach.of_canReturn_wp 14 :=
  fun H => Nat.succ_ne_zero 0 (H (m := Id) (Pred := Prop) (EPosts := EStackEnd) (x := (pure 0 : Id Nat))
    (P := fun n => n = 0) (a := 1) (top_le_ofProp_true rfl))

-- `Std.WP.LawfulWPMonadAttach.of_canReturn_wp`: `P = False` at `pure 0` in `Id`.
theorem LawfulWPMonadAttach_of_canReturn_wp_15 : ¬ drop0% Std.WP.LawfulWPMonadAttach.of_canReturn_wp 15 :=
  fun H => H (m := Id) (Pred := Prop) (EPosts := EStackEnd) (x := (pure 0 : Id Nat)) (P := fun _ => False)
    (a := 0) rfl

-- `Std.WP.ExceptT.instLawfulWPMonadAttach`: `TrivA` (trivial attach) is not lawful.
theorem ExceptT_instLawfulWPMonadAttach_6 : ¬ indep0% Std.WP.ExceptT.instLawfulWPMonadAttach 6 :=
  fun H => TrivA.not_lawful (H (ε := Unit) (m := TrivA) (Pred := Prop) (EPosts := EStackEnd))

-- `Std.WP.ExceptT.instLawfulWPMonadAttach`: over `TopM` the lifted `wp` proves `False` about `pure 0`.
theorem ExceptT_instLawfulWPMonadAttach_10 : ¬ drop0% Std.WP.ExceptT.instLawfulWPMonadAttach 10 :=
  fun H => (H (ε := Unit) (m := TopM) (Pred := Prop) (EPosts := EStackEnd)).of_canReturn_wp
    (x := (pure 0 : ExceptT Unit TopM Nat)) (P := fun _ => False) (a := 0) rfl (fun _ => trivial)

-- `Std.WP.OptionT.instLawfulWPMonadAttach`: `TrivA` (trivial attach) is not lawful.
theorem OptionT_instLawfulWPMonadAttach_5 : ¬ indep0% Std.WP.OptionT.instLawfulWPMonadAttach 5 :=
  fun H => TrivA.not_lawful (H (m := TrivA) (Pred := Prop) (EPosts := EStackEnd))

-- `Std.WP.OptionT.instLawfulWPMonadAttach`: over `TopM` the lifted `wp` proves `False` about `pure 0`.
theorem OptionT_instLawfulWPMonadAttach_9 : ¬ drop0% Std.WP.OptionT.instLawfulWPMonadAttach 9 :=
  fun H => (H (m := TopM) (Pred := Prop) (EPosts := EStackEnd)).of_canReturn_wp
    (x := (pure 0 : OptionT TopM Nat)) (P := fun _ => False) (a := 0) rfl (fun _ => trivial)

-- `Std.WP.StateT.instLawfulWPMonadAttach`: `TrivA` (trivial attach) is not lawful.
theorem StateT_instLawfulWPMonadAttach_6 : ¬ indep0% Std.WP.StateT.instLawfulWPMonadAttach 6 :=
  fun H => TrivA.not_lawful (H (σ := Unit) (m := TrivA) (Pred := Prop) (EPosts := EStackEnd))

-- `Std.WP.StateT.instLawfulWPMonadAttach`: over `TopM` the lifted `wp` proves `False` about `pure 0`.
theorem StateT_instLawfulWPMonadAttach_10 : ¬ drop0% Std.WP.StateT.instLawfulWPMonadAttach 10 :=
  fun H => (H (σ := Unit) (m := TopM) (Pred := Prop) (EPosts := EStackEnd)).of_canReturn_wp
    (x := (pure 0 : StateT Unit TopM Nat)) (P := fun _ => False) (a := 0) ⟨(), (), rfl⟩ (fun _ _ => trivial)

-- `Std.WP.ReaderT.instLawfulWPMonadAttach`: `TrivA` (trivial attach) is not lawful.
theorem ReaderT_instLawfulWPMonadAttach_6 : ¬ indep0% Std.WP.ReaderT.instLawfulWPMonadAttach 6 :=
  fun H => TrivA.not_lawful (H (ρ := Unit) (m := TrivA) (Pred := Prop) (EPosts := EStackEnd))

-- `Std.WP.ReaderT.instLawfulWPMonadAttach`: over `TopM` the lifted `wp` proves `False` about `pure 0`.
theorem ReaderT_instLawfulWPMonadAttach_10 : ¬ drop0% Std.WP.ReaderT.instLawfulWPMonadAttach 10 :=
  fun H => (H (ρ := Unit) (m := TopM) (Pred := Prop) (EPosts := EStackEnd)).of_canReturn_wp
    (x := (pure 0 : ReaderT Unit TopM Nat)) (P := fun _ => False) (a := 0) ⟨(), rfl⟩ (fun _ _ => trivial)

-- `Std.WP.ReaderT.of_canReturn_run_wp`: `TrivA` (trivial attach) is not lawful.
theorem ReaderT_of_canReturn_run_wp_6 : ¬ indep0% Std.WP.ReaderT.of_canReturn_run_wp 6 :=
  fun H => TrivA.not_lawful (H (ρ := Unit) (m := TrivA) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0)
    (r := ()) (a := 0) (fun _ => True) trivial (top_le_ofProp_fun (p := True) trivial ()))

-- `Std.WP.ReaderT.of_canReturn_run_wp`: base `TopM` (`wp ≡ True`), `P = False`.
theorem ReaderT_of_canReturn_run_wp_10 : ¬ drop0% Std.WP.ReaderT.of_canReturn_run_wp 10 :=
  fun H => H (m := TopM) (ρ := Unit) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0) (r := ()) (a := 0)
    (fun _ => False) rfl (fun _ => trivial)

-- `Std.WP.ReaderT.of_canReturn_run_wp`: `pure 0` over `Id`, `a = 1`, `P = (· = 0)`.
theorem ReaderT_of_canReturn_run_wp_16 : ¬ drop0% Std.WP.ReaderT.of_canReturn_run_wp 16 :=
  fun H => Nat.succ_ne_zero 0 (H (m := Id) (ρ := Unit) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0)
    (r := ()) (a := 1) (fun n => n = 0) (top_le_ofProp_fun (p := (0 : Nat) = 0) rfl ()))

-- `Std.WP.ReaderT.of_canReturn_run_wp`: `P = False` at `pure 0` over `Id`.
theorem ReaderT_of_canReturn_run_wp_17 : ¬ drop0% Std.WP.ReaderT.of_canReturn_run_wp 17 :=
  fun H => H (m := Id) (ρ := Unit) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0) (r := ()) (a := 0)
    (fun _ => False) rfl

-- `Std.WP.StateT.of_canReturn_run_wp`: `TrivA` (trivial attach) is not lawful.
theorem StateT_of_canReturn_run_wp_6 : ¬ indep0% Std.WP.StateT.of_canReturn_run_wp 6 :=
  fun H => TrivA.not_lawful (H (σ := Unit) (m := TrivA) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0)
    (s := ()) (p := (0, ())) (fun _ => True) trivial (top_le_ofProp_true trivial))

-- `Std.WP.StateT.of_canReturn_run_wp`: base `TopM` (`wp ≡ True`), `P = False`.
theorem StateT_of_canReturn_run_wp_10 : ¬ drop0% Std.WP.StateT.of_canReturn_run_wp 10 :=
  fun H => H (m := TopM) (σ := Unit) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0) (s := ()) (p := (0, ()))
    (fun _ => False) rfl (fun _ => trivial)

-- `Std.WP.StateT.of_canReturn_run_wp`: `pure 0` over `Id`, `p = (1, ())`, `P = (·.1 = 0)`.
theorem StateT_of_canReturn_run_wp_16 : ¬ drop0% Std.WP.StateT.of_canReturn_run_wp 16 :=
  fun H => Nat.succ_ne_zero 0 (H (m := Id) (σ := Unit) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0)
    (s := ()) (p := (1, ())) (fun q => q.1 = 0) (top_le_ofProp_true rfl))

-- `Std.WP.StateT.of_canReturn_run_wp`: `P = False` at `pure 0` over `Id`.
theorem StateT_of_canReturn_run_wp_17 : ¬ drop0% Std.WP.StateT.of_canReturn_run_wp 17 :=
  fun H => H (m := Id) (σ := Unit) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0) (s := ()) (p := (0, ()))
    (fun _ => False) rfl

-- `Std.WP.ExceptT.of_canReturn_run_wp`: `TrivA` (trivial attach) is not lawful.
theorem ExceptT_of_canReturn_run_wp_6 : ¬ indep0% Std.WP.ExceptT.of_canReturn_run_wp 6 :=
  fun H => TrivA.not_lawful (H (ε := Unit) (m := TrivA) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0)
    (x := .ok 0) (fun _ => True) trivial (top_le_ofProp_true trivial))

-- `Std.WP.ExceptT.of_canReturn_run_wp`: base `TopM` (`wp ≡ True`), `P = False`.
theorem ExceptT_of_canReturn_run_wp_10 : ¬ drop0% Std.WP.ExceptT.of_canReturn_run_wp 10 :=
  fun H => H (m := TopM) (ε := Unit) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0) (x := .ok 0)
    (fun _ => False) rfl (fun _ => trivial)

-- `Std.WP.ExceptT.of_canReturn_run_wp`: `pure 0` over `Id`, `x = .ok 1`, `P = (· = .ok 0)`.
theorem ExceptT_of_canReturn_run_wp_15 : ¬ drop0% Std.WP.ExceptT.of_canReturn_run_wp 15 :=
  fun H => Nat.succ_ne_zero 0 (Except.ok.inj (H (m := Id) (ε := Unit) (Pred := Prop) (EPosts := EStackEnd)
    (prog := pure 0) (x := .ok 1) (fun r => r = .ok 0) (top_le_ofProp_true rfl)))

-- `Std.WP.ExceptT.of_canReturn_run_wp`: `P = False` at `pure 0` over `Id`.
theorem ExceptT_of_canReturn_run_wp_16 : ¬ drop0% Std.WP.ExceptT.of_canReturn_run_wp 16 :=
  fun H => H (m := Id) (ε := Unit) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0) (x := .ok 0)
    (fun _ => False) rfl

-- `Std.WP.OptionT.of_canReturn_run_wp`: `TrivA` (trivial attach) is not lawful.
theorem OptionT_of_canReturn_run_wp_5 : ¬ indep0% Std.WP.OptionT.of_canReturn_run_wp 5 :=
  fun H => TrivA.not_lawful (H (m := TrivA) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0)
    (x := some 0) (fun _ => True) trivial (top_le_ofProp_true trivial))

-- `Std.WP.OptionT.of_canReturn_run_wp`: base `TopM` (`wp ≡ True`), `P = False`.
theorem OptionT_of_canReturn_run_wp_9 : ¬ drop0% Std.WP.OptionT.of_canReturn_run_wp 9 :=
  fun H => H (m := TopM) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0) (x := some 0)
    (fun _ => False) rfl (fun _ => trivial)

-- `Std.WP.OptionT.of_canReturn_run_wp`: `pure 0` over `Id`, `x = some 1`, `P = (· = some 0)`.
theorem OptionT_of_canReturn_run_wp_14 : ¬ drop0% Std.WP.OptionT.of_canReturn_run_wp 14 :=
  fun H => Nat.succ_ne_zero 0 (Option.some.inj (H (m := Id) (Pred := Prop) (EPosts := EStackEnd)
    (prog := pure 0) (x := some 1) (fun r => r = some 0) (top_le_ofProp_true rfl)))

-- `Std.WP.OptionT.of_canReturn_run_wp`: `P = False` at `pure 0` over `Id`.
theorem OptionT_of_canReturn_run_wp_15 : ¬ drop0% Std.WP.OptionT.of_canReturn_run_wp 15 :=
  fun H => H (m := Id) (Pred := Prop) (EPosts := EStackEnd) (prog := pure 0) (x := some 0)
    (fun _ => False) rfl

-- `Std.WP.Id.of_run_eq_wp`: `prog = 0`, `x = 1`, `P = (· = 0)`.
theorem Id_of_run_eq_wp_3 : ¬ drop0% Std.WP.Id.of_run_eq_wp 3 :=
  fun H => Nat.succ_ne_zero 0 (H (x := 1) (prog := (pure 0 : Id Nat)) (fun n => n = 0) rfl)

-- `Std.WP.Id.of_run_eq_wp`: `P = False`.
theorem Id_of_run_eq_wp_5 : ¬ drop0% Std.WP.Id.of_run_eq_wp 5 :=
  fun H => H (x := 0) (prog := (pure 0 : Id Nat)) rfl (fun _ => False)

-- `Std.WP.Option.of_eq_wp`: `prog = none`, `x = some 0`, `P = (· = none)`.
theorem Option_of_eq_wp_3 : ¬ drop0% Std.WP.Option.of_eq_wp 3 :=
  fun H => Option.some_ne_none 0 (H (x := some 0) (prog := none) (fun o => o = none) rfl)

-- `Std.WP.Option.of_eq_wp`: `P = False`.
theorem Option_of_eq_wp_5 : ¬ drop0% Std.WP.Option.of_eq_wp 5 :=
  fun H => H (α := Nat) (x := none) (prog := none) rfl (fun _ => False)

-- `Std.WP.StateM.of_run_eq_wp`: `prog = pure 0`, `x = (1, ())`, `P = (·.1 = 0)`.
theorem StateM_of_run_eq_wp_5 : ¬ drop0% Std.WP.StateM.of_run_eq_wp 5 :=
  fun H => Nat.succ_ne_zero 0 (H (x := (1, ())) (prog := (pure 0 : StateM Unit Nat)) (s := ()) (fun p => p.1 = 0) rfl)

-- `Std.WP.StateM.of_run_eq_wp`: `P = False`.
theorem StateM_of_run_eq_wp_7 : ¬ drop0% Std.WP.StateM.of_run_eq_wp 7 :=
  fun H => H (x := (0, ())) (prog := (pure 0 : StateM Unit Nat)) (s := ()) rfl (fun _ => False)

-- `Std.WP.StateM.of_run'_eq_wp`: `prog = pure 0`, `x = 1`, `P = (· = 0)`.
theorem StateM_of_run'_eq_wp_5 : ¬ drop0% Std.WP.StateM.of_run'_eq_wp 5 :=
  fun H => Nat.succ_ne_zero 0 (H (x := 1) (prog := (pure 0 : StateM Unit Nat)) (s := ()) (fun n => n = 0) rfl)

-- `Std.WP.StateM.of_run'_eq_wp`: `P = False`.
theorem StateM_of_run'_eq_wp_7 : ¬ drop0% Std.WP.StateM.of_run'_eq_wp 7 :=
  fun H => H (x := 0) (prog := (pure 0 : StateM Unit Nat)) (s := ()) rfl (fun _ => False)

-- `Std.WP.ReaderM.of_run_eq_wp`: `prog = pure 0`, `x = 1`, `P = (· = 0)`.
theorem ReaderM_of_run_eq_wp_5 : ¬ drop0% Std.WP.ReaderM.of_run_eq_wp 5 :=
  fun H => Nat.succ_ne_zero 0 (H (x := 1) (prog := (pure 0 : ReaderM Unit Nat)) (r := ()) (fun n => n = 0) rfl)

-- `Std.WP.ReaderM.of_run_eq_wp`: `P = False`.
theorem ReaderM_of_run_eq_wp_7 : ¬ drop0% Std.WP.ReaderM.of_run_eq_wp 7 :=
  fun H => H (x := 0) (prog := (pure 0 : ReaderM Unit Nat)) (r := ()) rfl (fun _ => False)

-- `Std.WP.Except.of_eq_wp`: `prog = .ok 0`, `x = .ok 1`, `P = (· = .ok 0)`.
theorem Except_of_eq_wp_4 : ¬ drop0% Std.WP.Except.of_eq_wp 4 :=
  fun H => Nat.succ_ne_zero 0 (Except.ok.inj (H (ε := Unit) (x := .ok 1) (prog := .ok 0) (fun r => r = .ok 0) rfl))

-- `Std.WP.Except.of_eq_wp`: `P = False`.
theorem Except_of_eq_wp_6 : ¬ drop0% Std.WP.Except.of_eq_wp 6 :=
  fun H => H (ε := Unit) (α := Nat) (x := .ok 0) (prog := .ok 0) rfl (fun _ => False)

-- `Std.WP.EStateM.of_run_eq_wp`: `prog = pure 0`, `x = .ok 1 ()`, `P` = "ok with value 0".
theorem EStateM_of_run_eq_wp_6 : ¬ drop0% Std.WP.EStateM.of_run_eq_wp 6 :=
  fun H => Nat.succ_ne_zero 0 (H (ε := Unit) (σ := Unit) (x := .ok 1 ()) (prog := pure 0) (s := ())
    (fun r => match r with | .ok a _ => a = 0 | .error _ _ => False) rfl)

-- `Std.WP.EStateM.of_run_eq_wp`: `P = False`.
theorem EStateM_of_run_eq_wp_8 : ¬ drop0% Std.WP.EStateM.of_run_eq_wp 8 :=
  fun H => H (ε := Unit) (σ := Unit) (α := Nat) (x := .ok 0 ()) (prog := pure 0) (s := ()) rfl (fun _ => False)

/-! ## Std.WP.Monad.Conjunctive: lifting over the non-conjunctive `AngM` -/

-- `Std.WP.StateT.instWPConjunctive`: base `AngM`.
theorem StateT_instWPConjunctive_10 : ¬ drop0% Std.WP.StateT.instWPConjunctive 10 := by
  intro H
  have h := (H (m := AngM) (σ := Unit) (α := Bool) (Pred := Prop) (EPosts := EStackEnd)
    (fun s => (pure (true, s) : AngM (Bool × Unit)))).wp_meet_wp_le
    (fun b _ => b = true) (fun b _ => b = false) () () ()
  rw [meet_apply, meet_prop_eq_and] at h
  obtain ⟨⟨b, s⟩, hb⟩ := h ⟨⟨(true, ()), rfl⟩, ⟨(false, ()), rfl⟩⟩
  change ((fun b _ => b = true) ⊓ (fun b _ => b = false) : Bool → Unit → Prop) b s at hb
  rw [meet_apply, meet_apply, meet_prop_eq_and] at hb
  exact Bool.noConfusion (hb.1.symm.trans hb.2)

-- `Std.WP.ReaderT.instWPConjunctive`: base `AngM`.
theorem ReaderT_instWPConjunctive_10 : ¬ drop0% Std.WP.ReaderT.instWPConjunctive 10 := by
  intro H
  have h := (H (m := AngM) (ρ := Unit) (α := Bool) (Pred := Prop) (EPosts := EStackEnd)
    (fun _ => (pure true : AngM Bool))).wp_meet_wp_le
    (fun b _ => b = true) (fun b _ => b = false) () () ()
  rw [meet_apply, meet_prop_eq_and] at h
  obtain ⟨b, hb⟩ := h ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩
  change ((fun b _ => b = true) ⊓ (fun b _ => b = false) : Bool → Unit → Prop) b () at hb
  rw [meet_apply, meet_apply, meet_prop_eq_and] at hb
  exact Bool.noConfusion (hb.1.symm.trans hb.2)

-- `Std.WP.OptionT.instWPConjunctive`: base `AngM`.
theorem OptionT_instWPConjunctive_9 : ¬ drop0% Std.WP.OptionT.instWPConjunctive 9 := by
  intro H
  have h := (H (m := AngM) (α := Bool) (Pred := Prop) (EPosts := EStackEnd)
    (OptionT.mk (pure (some true) : AngM (Option Bool)))).wp_meet_wp_le
    (fun b => b = true) (fun b => b = false) (fun _ => False, ()) (fun _ => False, ())
  rw [meet_prop_eq_and] at h
  obtain ⟨o, ho⟩ := h ⟨⟨some true, rfl⟩, ⟨some false, rfl⟩⟩
  cases o with
  | none =>
    change (((fun _ => False, ()) ⊓ (fun _ => False, ()) : (Unit → Prop) × EStackEnd).1 ()) at ho
    rw [Prod.fst_meet, meet_apply, meet_prop_eq_and] at ho; exact ho.1
  | some b =>
    change ((fun b => b = true) ⊓ (fun b => b = false) : Bool → Prop) b at ho
    rw [meet_apply, meet_prop_eq_and] at ho
    exact Bool.noConfusion (ho.1.symm.trans ho.2)

-- `Std.WP.ExceptT.instWPConjunctive`: base `AngM`.
theorem ExceptT_instWPConjunctive_10 : ¬ drop0% Std.WP.ExceptT.instWPConjunctive 10 := by
  intro H
  have h := (H (m := AngM) (ε := Unit) (α := Bool) (Pred := Prop) (EPosts := EStackEnd)
    (ExceptT.mk (pure (.ok true) : AngM (Except Unit Bool)))).wp_meet_wp_le
    (fun b => b = true) (fun b => b = false) (fun _ => False, ()) (fun _ => False, ())
  rw [meet_prop_eq_and] at h
  obtain ⟨o, ho⟩ := h ⟨⟨.ok true, rfl⟩, ⟨.ok false, rfl⟩⟩
  cases o with
  | error e =>
    change (((fun _ => False, ()) ⊓ (fun _ => False, ()) : (Unit → Prop) × EStackEnd).1 e) at ho
    rw [Prod.fst_meet, meet_apply, meet_prop_eq_and] at ho; exact ho.1
  | ok b =>
    change ((fun b => b = true) ⊓ (fun b => b = false) : Bool → Prop) b at ho
    rw [meet_apply, meet_prop_eq_and] at ho
    exact Bool.noConfusion (ho.1.symm.trans ho.2)

end WPRestHand

namespace WPRestHand

/-! ## Std.WP.Frame -/

theorem ps_sup_empty_le {L : Type} [CompleteLattice L] (f : L → L) [PreservesSup f] (z : L) :
    f (CompleteLattice.sup (fun _ => False)) ⊑ z := by
  rw [PreservesSup.map_sup (f := f)]
  exact sup_le _ (fun _ ⟨_, h, _⟩ => h.elim)

/-- The constant `True` map on `Prop` does not preserve suprema (copied from `OrderHand`). -/
theorem not_ps_true : ¬ PreservesSup (fun _ : Prop => True) :=
  fun _ => ps_sup_empty_le (fun _ : Prop => True) False trivial

theorem not_frameOp_true {EPosts : Type} [CompleteLattice EPosts] (opE : Unit → EPosts → EPosts) :
    ¬ FrameOp (fun (_ : Unit) (_ : Prop) => True) EPosts opE :=
  fun h => not_ps_true (h.preservesSup ())

/-- An order automorphism preserves suprema (copied from `OrderHand`). -/
theorem ps_of_iso {L : Type} [CompleteLattice L] (f g : L → L) (hf : ∀ a b, a ⊑ b → f a ⊑ f b)
    (hg : ∀ a b, a ⊑ b → g a ⊑ g b) (hgf : ∀ a, g (f a) = a) (hfg : ∀ a, f (g a) = a) :
    PreservesSup f where
  map_sup s := by
    apply PartialOrder.rel_antisymm
    · have : CompleteLattice.sup s ⊑ g (CompleteLattice.sup (fun y => ∃ x, s x ∧ y = f x)) :=
        sup_le _ fun x hx => by
          rw [← hgf x]; exact hg _ _ (le_sup _ ⟨x, hx, rfl⟩)
      have := hf _ _ this
      rwa [hfg] at this
    · exact sup_le _ fun _ ⟨x, hx, e⟩ => e ▸ hf _ _ (le_sup _ hx)

/-- Swap on `Bool → Prop` (from `OrderHand`). -/
def sw (P : Bool → Prop) : Bool → Prop := fun b => P (!b)
instance ps_sw : PreservesSup sw :=
  ps_of_iso sw sw (fun _ _ h b => h _) (fun _ _ h b => h _)
    (fun P => funext fun b => by simp [sw]) (fun P => funext fun b => by simp [sw])

/-- `Prop` program with a `Prop` exception postcondition: `wp _ Q _ = Q ()`. -/
inductive HonPP | mk
instance HonPP.wp : WP HonPP Unit Prop Prop where
  trans _ := ⟨fun post _ => post ()⟩
  trans_monotone _ := fun _ _ _ _ _ hp => hp ()
instance HonPP.conj (x : HonPP) : WPConjunctive x where
  wp_meet_wp_le q1 q2 _ _ := by
    show q1 () ⊓ q2 () ⊑ (q1 ⊓ q2) ()
    rw [meet_apply]

/-- Angelic over states: `wp _ Q _ _ = ∃ s', Q () s'` (not conjunctive). -/
inductive AngS | mk
instance AngS.wp : WP AngS Unit (Bool → Prop) EStackEnd where
  trans _ := ⟨fun Q _ _ => ∃ s', Q () s'⟩
  trans_monotone _ := fun _ _ _ _ _ hp _ ⟨s', h⟩ => ⟨s', hp () s' h⟩

/-- Reads the exception postcondition at `true`: `wp _ _ E = E true`. -/
inductive ExcB | mk
instance ExcB.wp : WP ExcB Unit Prop (Bool → Prop) where
  trans _ := ⟨fun _ E => E true⟩
  trans_monotone _ := fun _ _ _ _ he _ h => he true h
instance ExcB.conj (x : ExcB) : WPConjunctive x where
  wp_meet_wp_le _ _ e1 e2 := by
    show e1 true ⊓ e2 true ⊑ (e1 ⊓ e2) true
    rw [meet_apply]

/-- `FrameOp` for `meet` on `Prop` with the swap on the exception channel `Bool → Prop`. -/
instance swFrame : FrameOp (meet : Prop → Prop → Prop) (Bool → Prop) (fun _ => sw) :=
  @FrameOp.mk Prop _ Prop meet (Bool → Prop) _ (fun _ => sw) (fun _ => inferInstance) (fun _ => ps_sw)

/-- In `StateM Bool`, `modify not` does not frame `(· = true)` (under the guard `True`). -/
theorem flip_not_frames
    (h : ∀ Q E, ((fun _ => True) ⊓ meet (fun s : Bool => s = true) (wp (modify not : StateM Bool PUnit) Q E) : Bool → Prop) ⊑
      wp (modify not : StateM Bool PUnit) (fun a => meet (fun s : Bool => s = true) (Q a)) (FrameOp.ignore (fun s : Bool => s = true) E)) :
    False := by
  have h1 := h (fun _ _ => True) () true
  change ((fun _ => True) ⊓ ((fun s : Bool => s = true) ⊓ (fun _ => True)) : Bool → Prop) true →
    ((fun s : Bool => s = true) ⊓ (fun _ => True) : Bool → Prop) false at h1
  rw [meet_apply, meet_apply, meet_apply, meet_prop_eq_and, meet_prop_eq_and, meet_prop_eq_and] at h1
  exact Bool.noConfusion (h1 ⟨trivial, rfl, trivial⟩).1

-- `Std.WP.WP.Frames.op_wp_le_wp_op`: `op` = constant `True` on `Prop` does not preserve suprema.
theorem Frames_op_wp_le_wp_op_10 : ¬ indep0% Std.WP.WP.Frames.op_wp_le_wp_op 10 :=
  fun H => not_frameOp_true _ (H (Prog := Id Unit) (op := fun (_ : Unit) (_ : Prop) => True)
    (opE := fun _ (e : EStackEnd) => e) (x := ()) (F := ()) (P := True) (fun _ => True) ())

-- `Std.WP.WP.Frames.op_wp_le_wp_op`: `modify not` in `StateM Bool` does not frame `(· = true)`.
theorem Frames_op_wp_le_wp_op_14 : ¬ drop0% Std.WP.WP.Frames.op_wp_le_wp_op 14 :=
  fun H => flip_not_frames fun Q E => H (Prog := StateM Bool PUnit)
    (op := (meet : (Bool → Prop) → (Bool → Prop) → (Bool → Prop))) (opE := FrameOp.ignore)
    (x := modify not) (F := fun s => s = true) (P := fun _ => True) Q E

-- `Std.WP.meet_op_wp_upperAdjoint_le_wp`: `op` = constant `True` on `Prop`.
theorem meet_op_wp_upperAdjoint_le_wp_10 : ¬ indep0% Std.WP.meet_op_wp_upperAdjoint_le_wp 10 :=
  fun H => not_frameOp_true _ (H (Prog := Id Unit) (op := fun (_ : Unit) (_ : Prop) => True)
    (opE := fun _ (e : EStackEnd) => e) (x := ()) (F := ()) (P := True) (Q := fun _ => True) (E := ()))

-- `Std.WP.meet_op_wp_upperAdjoint_le_wp`: `modify not` in `StateM Bool`, `F = (· = true)`, `Q = False`.
theorem meet_op_wp_upperAdjoint_le_wp_16 : ¬ drop0% Std.WP.meet_op_wp_upperAdjoint_le_wp 16 := by
  intro H
  have h := H (Prog := StateM Bool PUnit) (op := (meet : (Bool → Prop) → (Bool → Prop) → (Bool → Prop)))
    (opE := FrameOp.ignore) (x := modify not) (F := fun s => s = true) (P := fun _ => True)
    (Q := fun _ _ => False) (E := ()) true
  have hu : (fun s : Bool => s = false) ⊑
      PreservesSup.upperAdjoint (meet (fun s : Bool => s = true)) (fun _ => False) :=
    PreservesSup.le_upperAdjoint _ (fun s => by
      rw [meet_apply, meet_prop_eq_and]; exact fun ⟨h1, h2⟩ => Bool.noConfusion (h1.symm.trans h2))
  apply h
  rw [meet_apply, meet_apply, meet_prop_eq_and, meet_prop_eq_and]
  exact ⟨trivial, rfl, hu false rfl⟩

-- `Std.WP.WP.frames_of_frameClosure`: `op` = constant `True` on `Prop` (action laws hold trivially).
theorem frames_of_frameClosure_10 : ¬ indep0% Std.WP.WP.frames_of_frameClosure 10 :=
  fun H => not_frameOp_true _ (H (Prog := Id Unit) (fun (_ : Unit) (_ : Prop) => True)
    (opE := fun _ (e : EStackEnd) => e) (fun _ _ => ()) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (x := ()) (F := ()) (P := True))

-- `Std.WP.WP.frames_of_frameClosure`: `StateM Bool` is not a frame closure; `modify not` does not frame.
theorem frames_of_frameClosure_17 : ¬ drop0% Std.WP.WP.frames_of_frameClosure 17 :=
  fun H => flip_not_frames fun Q E => (H (Prog := StateM Bool PUnit)
    (meet : (Bool → Prop) → (Bool → Prop) → (Bool → Prop)) (opE := FrameOp.ignore) meet
    (fun _ _ _ => meet_assoc) (fun _ _ _ => rfl) (x := modify not) (F := fun s => s = true)
    (P := fun _ => True)).op_wp_le_wp_op Q E

-- `Std.WP.WP.frames_of_conjunctive`: `opE` = constant `True` on `Prop` does not preserve suprema.
theorem frames_of_conjunctive_10 : ¬ indep0% Std.WP.WP.frames_of_conjunctive 10 :=
  fun H => not_ps_true ((H (x := HonPP.mk) (opE := fun _ _ => True) (F := True) (P := True)
    (meet_le_right _ _) (fun _ _ => trivial)).preservesSupE True)

-- `Std.WP.WP.frames_of_conjunctive`: `AngS` (angelic over states) is not conjunctive.
theorem frames_of_conjunctive_8 : ¬ drop0% Std.WP.WP.frames_of_conjunctive 8 := by
  intro H
  have h := (H (x := AngS.mk) (opE := FrameOp.ignore) (F := fun s => s = true) (P := fun _ => True)
    (fun _ _ => ⟨true, rfl⟩) (fun _ => PartialOrder.rel_of_eq (Subsingleton.elim _ _))).op_wp_le_wp_op
    (fun _ s => s = false) () true
  rw [meet_apply, meet_apply, meet_prop_eq_and, meet_prop_eq_and] at h
  obtain ⟨s, hs⟩ := h ⟨trivial, rfl, ⟨false, rfl⟩⟩
  change ((fun s : Bool => s = true) ⊓ (fun s => s = false) : Bool → Prop) s at hs
  rw [meet_apply, meet_prop_eq_and] at hs
  exact Bool.noConfusion (hs.1.symm.trans hs.2)

-- `Std.WP.WP.frames_of_conjunctive`: `modify not` in `StateM Bool` (`hF` fails, `hE` trivial on `Unit`).
theorem frames_of_conjunctive_13 : ¬ drop0% Std.WP.WP.frames_of_conjunctive 13 :=
  fun H => flip_not_frames fun Q E => (H (x := (modify not : StateM Bool PUnit)) (opE := FrameOp.ignore)
    (F := fun s => s = true) (P := fun _ => True)
    (fun _ => PartialOrder.rel_of_eq (Subsingleton.elim _ _))).op_wp_le_wp_op Q E

-- `Std.WP.WP.frames_of_conjunctive`: `ExcB` with `opE = swap` on `Bool → Prop` (`hE` fails).
theorem frames_of_conjunctive_14 : ¬ drop0% Std.WP.WP.frames_of_conjunctive 14 := by
  intro H
  have h := (H (x := ExcB.mk) (opE := fun _ => sw) (F := True) (P := True)
    (fun _ => le_top (fun _ : Bool => True) false trivial)).op_wp_le_wp_op (fun _ => True) (fun b => b = true)
  rw [meet_prop_eq_and, meet_prop_eq_and] at h
  exact Bool.noConfusion (h ⟨trivial, trivial, rfl⟩)

-- `Std.WP.WP.withFrameClosure_le_wp_iff`: `op` = constant `True` on `Prop`.
theorem withFrameClosure_le_wp_iff_9 : ¬ indep0% Std.WP.WP.withFrameClosure_le_wp_iff 9 :=
  fun H => not_frameOp_true _ (H (Prog := Id Unit) (fun (_ : Unit) (_ : Prop) => True)
    (opE := fun _ (e : EStackEnd) => e) inferInstance () (fun _ => True) () True)

-- `Std.WP.WP.le_wp_of_withFrameClosure_eq`: `op` = constant `True` on `Prop`.
theorem le_wp_of_withFrameClosure_eq_9 : ¬ indep0% Std.WP.WP.le_wp_of_withFrameClosure_eq 9 :=
  fun H => not_frameOp_true _ (H (Prog := Id Unit) (op := fun (_ : Unit) (_ : Prop) => True)
    (opE := fun _ (e : EStackEnd) => e) (base := inferInstance) (I := inferInstance) (x := ())
    (Q := fun _ => True) (E := ()) (pre := True) (fun _ _ => trivial))

/-- The interpretation of `Id Unit` with `wp ≡ False`. -/
@[instance_reducible] def botWP : WP (Id Unit) Unit Prop EStackEnd where
  trans _ := ⟨fun _ _ => False⟩
  trans_monotone _ := fun _ _ _ _ _ _ h => h

-- `Std.WP.WP.le_wp_of_withFrameClosure_eq`: `I := botWP` is not the frame closure of `Id`.
theorem le_wp_of_withFrameClosure_eq_12 : ¬ drop0% Std.WP.WP.le_wp_of_withFrameClosure_eq 12 :=
  fun H => H (Prog := Id Unit) (op := fun (_ : Unit) => (id : Prop → Prop)) (opE := FrameOp.ignore)
    (base := inferInstance) (I := botWP) (x := ()) (Q := fun _ => True) (E := ()) (pre := True)
    (fun _ h => h) trivial

-- `Std.WP.WP.le_wp_of_withFrameClosure_eq`: `op = id`, the closure of `Id` at `Q = False` is `False`.
theorem le_wp_of_withFrameClosure_eq_17 : ¬ drop0% Std.WP.WP.le_wp_of_withFrameClosure_eq 17 := by
  intro H
  have h := H (Prog := Id Unit) (op := fun (_ : Unit) => (id : Prop → Prop)) (opE := FrameOp.ignore)
    (base := inferInstance) (x := ()) (Q := fun _ => False) (E := ()) (pre := True) rfl trivial
  have h2 : (⨅ _ : Unit, PreservesSup.upperAdjoint (id : Prop → Prop) False) := h
  rw [PreservesSup.upperAdjoint_id] at h2
  exact iInf_le (fun _ : Unit => False) () h2

end WPRestHand

namespace WPRestHand

/-! ## Std.WP.Frame: frame closures over a family that violates the action law -/

theorem sw_sw (P : Bool → Prop) : sw (sw P) = P := funext fun b => by simp [sw]

theorem ua_sw_le (y : Bool → Prop) : PreservesSup.upperAdjoint sw y ⊑ sw y := by
  have h := PreservesSup.upperAdjoint_le sw y
  have h2 : sw (sw (PreservesSup.upperAdjoint sw y)) ⊑ sw y := fun b => h (!b)
  rwa [sw_sw] at h2

instance swOpFrame : FrameOp (fun (_ : Unit) => sw) EStackEnd FrameOp.ignore :=
  @FrameOp.mk (Bool → Prop) _ Unit (fun _ => sw) EStackEnd _ FrameOp.ignore (fun _ => ps_sw) (fun _ => inferInstance)

/-- Base transformer "assume the state is `true`": `Q ↦ fun s => Q () s ∧ s = true`. -/
def tAssume : PredTrans (Bool → Prop) EStackEnd Unit := ⟨fun Q _ s => Q () s ∧ s = true⟩

/-- `FC`: the frame closure of `tAssume` over the one-resource family `sw` (with `sw ∘ sw ≠ sw`). -/
inductive FC | mk
noncomputable instance FC.wp : WP FC Unit (Bool → Prop) EStackEnd :=
  WP.withFrameClosure (fun (_ : Unit) => sw) (opE := FrameOp.ignore)
    { trans := fun _ => tAssume, trans_monotone := fun _ _ _ _ _ _ hp s ⟨h1, h2⟩ => ⟨hp () s h1, h2⟩ }

-- `Std.WP.WP.frames_of_frameClosure`: `FC`, the frame closure over `op = fun _ => sw` (action law fails).
theorem frames_of_frameClosure_12 : ¬ drop0% Std.WP.WP.frames_of_frameClosure 12 := by
  intro H
  have hF := (H (Prog := FC) (fun (_ : Unit) => sw) (opE := FrameOp.ignore) (fun _ _ => ())
    (fun _ _ _ => rfl) (x := FC.mk) (F := ()) (P := fun _ => True)
    ⟨fun _ => tAssume, fun _ => rfl⟩).op_wp_le_wp_op (fun _ s => s = false) () true
  rw [meet_apply, meet_prop_eq_and] at hF
  have hl : (fun s : Bool => s = false) ⊑ wp FC.mk (fun _ s => s = false) () :=
    le_iInf _ _ fun _ => PreservesSup.le_upperAdjoint sw fun s (hs : (!s) = false) =>
      (show ((!s) = false) ∧ s = true from ⟨hs, by cases s <;> simp_all⟩)
  have h1 : (wp FC.mk (fun a => sw ((fun _ s => s = false : Unit → Bool → Prop) a)) (FrameOp.ignore () ()) :
      Bool → Prop) ⊑ sw (tAssume.apply (fun a => sw (sw ((fun _ s => s = false : Unit → Bool → Prop) a)))
        (FrameOp.ignore () ())) :=
    PartialOrder.rel_trans (iInf_le _ ()) (ua_sw_le _)
  exact Bool.noConfusion (h1 true (hF ⟨trivial, (hl false rfl : wp FC.mk (fun _ s => s = false) () (!true))⟩)).2

/-- `FrameOp` for `op = fun _ => id` on `Prop` with the swap on the exception channel. -/
instance idSwFrame : FrameOp (fun (_ : Unit) => (id : Prop → Prop)) (Bool → Prop) (fun _ => sw) :=
  @FrameOp.mk Prop _ Unit (fun _ => id) (Bool → Prop) _ (fun _ => sw)
    (fun _ => (inferInstance : PreservesSup (id : Prop → Prop))) (fun _ => ps_sw)

/-- `FCE`: the frame closure of "`wp _ _ E = E true`" over `op = id`, `opE = sw` (`sw ∘ sw ≠ sw`). -/
inductive FCE | mk
noncomputable instance FCE.wp : WP FCE Unit Prop (Bool → Prop) :=
  WP.withFrameClosure (fun (_ : Unit) => (id : Prop → Prop)) (opE := fun _ => sw)
    { trans := fun _ => ⟨fun _ E => E true⟩, trans_monotone := fun _ _ _ _ _ he _ h => he true h }

-- `Std.WP.WP.frames_of_frameClosure`: `FCE`, the frame closure over `opE = fun _ => sw` (companion action law fails).
theorem frames_of_frameClosure_13 : ¬ drop0% Std.WP.WP.frames_of_frameClosure 13 := by
  intro H
  have hF := (H (Prog := FCE) (fun (_ : Unit) => (id : Prop → Prop)) (opE := fun _ => sw) (fun _ _ => ())
    (fun _ _ _ => rfl) (x := FCE.mk) (F := ()) (P := True)
    ⟨fun _ => ⟨fun _ E => E true⟩, fun _ => rfl⟩).op_wp_le_wp_op (fun _ => True) (fun b => b = false)
  rw [meet_prop_eq_and] at hF
  have hl : True ⊑ wp FCE.mk (fun _ => True) (fun b => b = false) :=
    le_iInf _ _ fun _ => by rw [PreservesSup.upperAdjoint_id]; exact fun _ => rfl
  have h1 : (wp FCE.mk (fun a => id ((fun _ => True : Unit → Prop) a)) (sw (fun b => b = false)) : Prop) ⊑
      PreservesSup.upperAdjoint (id : Prop → Prop) ((sw (sw (fun b => b = false))) true) := iInf_le _ ()
  rw [PreservesSup.upperAdjoint_id] at h1
  exact Bool.noConfusion (h1 (hF ⟨trivial, hl trivial⟩) : (!!true) = false)

end WPRestHand

namespace WPRestHand

/-! ## Std.WP.Gadget.ForIn -/

/-- Angelic chaos over `M3`: `wp x post _ = ⨆ a, post a` (lawful `WPMonad`). -/
def AngL : Type → Type := Id
instance : Monad AngL := inferInstanceAs (Monad Id)
instance : MonadTail AngL := inferInstanceAs (MonadTail Id)
noncomputable instance AngL.wpm : WPMonad AngL M3 EStackEnd where
  toLawfulMonad := inferInstanceAs (LawfulMonad Id)
  toWP _ := { trans := fun _ => ⟨fun post _ => ⨆ a, post a⟩,
              trans_monotone := fun _ _ _ _ _ _ hp =>
                iSup_le _ _ fun a => PartialOrder.rel_trans (hp a) (le_iSup _ a) }
  pure_le_wp_pure x post _ := le_iSup post x
  bind_le_wp_bind _ _ post _ := iSup_le _ _ fun _ => iSup_le _ _ fun b => le_iSup post b

/-- A container with one element `0` for the `Id` loop, and with `Option` loops that skip it. -/
structure C1 where mk ::
instance : ForIn Id C1 Nat where
  forIn _ init f := match f 0 init with | .yield b => pure b | .done b => pure b
instance : ForIn Option C1 Nat where
  forIn _ init _ := pure init
theorem C1.toList : ForIn.toList C1.mk = [0] := rfl

/-- `C1` with membership `(· = 0)` and an `Option` `forIn'` that skips the element. -/
instance C1.memEq : Membership Nat C1 := ⟨fun _ a => a = 0⟩
instance : ForIn' Option C1 Nat C1.memEq where
  forIn' _ init _ := pure init
instance : Std.Internal.LawfulMemForInId C1 Nat where
  mem_toList_iff {a xs} := by
    rw [show xs = C1.mk from rfl, C1.toList, List.mem_singleton]; exact Iff.rfl

/-- `C1` with empty membership. -/
def C0 := C1
instance : ForIn Id C0 Nat := inferInstanceAs (ForIn Id C1 Nat)
instance C0.memF : Membership Nat C0 := ⟨fun _ _ => False⟩
instance : ForIn' Id C0 Nat C0.memF where
  forIn' _ init _ := pure init

-- `Std.WP.Spec.forInPure`: `C1` whose `Option` loop skips the element the `Id` loop yields.
theorem Spec_forInPure_12 : ¬ drop0% Std.WP.Spec.forInPure 12 := by
  intro H
  have h := (H (m := Option) (ρ := C1) (xs := C1.mk) (init := (0 : Nat))
    (f := fun _ b => some (.yield (b + 1))) (eposts := fun _ => False)
    (show Std.WP.Invariant Nat Nat Prop from fun pref _ b => b = pref.length)
    (fun pref cur suff _ b => ⟨fun (hb : b = pref.length) =>
      (by simp [hb] : b + 1 = (pref ++ [cur]).length)⟩)).le_wp
  exact Nat.zero_ne_one (h rfl)

-- `Std.WP.Spec.forInPure`: `Id`, list `[0]`, invariant `pref = []` (false at the end).
theorem Spec_forInPure_18 : ¬ drop0% Std.WP.Spec.forInPure 18 :=
  fun H => List.cons_ne_nil 0 [] ((H (m := Id) (xs := [0]) (init := (0 : Nat)) (f := fun _ b => pure (.yield b))
    (eposts := ()) (show Std.WP.Invariant Nat Nat Prop from fun pref _ _ => pref = [])).le_wp rfl)

-- `Std.WP.Spec.forInPure'`: `C0` (empty membership) whose `Id` loop yields `0`.
theorem Spec_forInPure'_13 : ¬ indep0% Std.WP.Spec.forInPure' 13 := fun H => by
  have h := H (m := Id) (Pred := Prop) (EPosts := EStackEnd) (ρ := C0) (xs := C1.mk) (init := (0 : Nat))
    (f := fun _ _ b => pure (.yield b)) (show Std.WP.Invariant Nat Nat Prop from fun _ _ _ => True) (eposts := ())
  exact (h.mem_toList_iff (a := 0) (xs := C1.mk)).mp (List.mem_singleton.mpr rfl : (0 : Nat) ∈ [0])

-- `Std.WP.Spec.forInPure'`: `C1` whose `Option` loop skips the element the `Id` loop yields.
theorem Spec_forInPure'_14 : ¬ drop0% Std.WP.Spec.forInPure' 14 := by
  intro H
  have h := (H (m := Option) (ρ := C1) (xs := C1.mk) (init := (0 : Nat))
    (f := fun _ _ b => some (.yield (b + 1))) (eposts := fun _ => False)
    (show Std.WP.Invariant Nat Nat Prop from fun pref _ b => b = pref.length)
    (fun pref cur suff _ b => ⟨fun (hb : b = pref.length) =>
      (by simp [hb] : b + 1 = (pref ++ [cur]).length)⟩)).le_wp
  exact Nat.zero_ne_one (h rfl)

-- `Std.WP.Spec.forInPure'`: `Id`, list `[0]`, invariant `pref = []` (false at the end).
theorem Spec_forInPure'_20 : ¬ drop0% Std.WP.Spec.forInPure' 20 :=
  fun H => List.cons_ne_nil 0 [] ((H (m := Id) (xs := [0]) (init := (0 : Nat)) (f := fun _ _ b => pure (.yield b))
    (eposts := ()) (show Std.WP.Invariant Nat Nat Prop from fun pref _ _ => pref = [])).le_wp rfl)

/-- `c ⊑ ⨆ _, ⊥` fails in `M3`. -/
theorem M3.not_c_le_iSup_bot {β : Type} (h : M3.c ⊑ ⨆ _ : β, M3.bot) : False :=
  M3.not_c_le_bot (PartialOrder.rel_trans h (iSup_le _ _ fun _ => PartialOrder.rel_refl))

theorem M3.F2_meet_c (b : Bool) : ((if b then M3.a else M3.b) ⊓ M3.c : M3) ⊑ M3.bot := by
  cases b
  · exact PartialOrder.rel_of_eq M3.meet_b_c
  · exact PartialOrder.rel_of_eq M3.meet_a_c

-- `Std.WP.Spec.forInLoop_invariant_variant`: `AngL` over the non-Heyting `M3`, measure values `a`/`b`,
-- invariant `c` (meets both in `⊥`), exit invariant `⊥`.
theorem Spec_forInLoop_invariant_variant_16 : ¬ drop0% Std.WP.Spec.forInLoop_invariant_variant 16 :=
  fun H => M3.not_c_le_iSup_bot (β := Nat) (H (m := AngL) (Fun := F2) (γ := Bool) (l := ⟨⟩) (init := (0 : Nat))
    (f := fun _ b => pure (.done b)) (fun _ => F2.mk) (fun flag _ => cond flag M3.bot M3.c) ()
    (fun _ mb => ⟨PartialOrder.rel_trans (M3.F2_meet_c mb) (rfl : M3.le .bot _ = true)⟩)).le_wp

-- `Std.WP.Spec.forInLoop_invariant_variant`: `AngM` (`wp = ∃`), exit invariant `False`.
theorem Spec_forInLoop_invariant_variant_20 : ¬ drop0% Std.WP.Spec.forInLoop_invariant_variant 20 := by
  intro H
  obtain ⟨_, h⟩ := (H (m := AngM) (Fun := Nat) (γ := Nat) (l := ⟨⟩) (init := (0 : Nat))
    (f := fun _ b => pure (.done b)) (fun _ => (0 : Nat)) (fun flag _ => flag = false) ()).le_wp rfl
  exact Bool.noConfusion h

-- `Std.WP.Spec.forInLoop_invariant`: `AngL` over `M3` as for forInLoop_invariant_variant.
theorem Spec_forInLoop_invariant_12 : ¬ drop0% Std.WP.Spec.forInLoop_invariant 12 :=
  fun H => M3.not_c_le_iSup_bot (β := Nat) (H (m := AngL) (l := ⟨⟩) (init := (0 : Nat))
    (f := fun _ b => pure (.done b)) (Std.WP.Variant.ofMeasure (Pred := M3) (fun _ : Nat => F2.mk))
    (fun flag _ => cond flag M3.bot M3.c) ()
    (fun _ mb => ⟨PartialOrder.rel_trans (M3.F2_meet_c mb) (rfl : M3.le .bot _ = true)⟩)).le_wp

-- `Std.WP.Spec.forInLoop_invariant`: `AngM`, exit invariant `False`.
theorem Spec_forInLoop_invariant_16 : ¬ drop0% Std.WP.Spec.forInLoop_invariant 16 := by
  intro H
  obtain ⟨_, h⟩ := (H (m := AngM) (l := ⟨⟩) (init := (0 : Nat)) (f := fun _ b => pure (.done b))
    (Std.WP.Variant.ofMeasure (Pred := Prop) (fun _ : Nat => (0 : Nat))) (fun flag _ => flag = false) ()).le_wp rfl
  exact Bool.noConfusion h

-- `Std.WP.Spec.forInLoop_variant`: `AngL` over `M3` as for forInLoop_invariant_variant.
theorem Spec_forInLoop_variant_16 : ¬ drop0% Std.WP.Spec.forInLoop_variant 16 :=
  fun H => M3.not_c_le_iSup_bot (β := Nat) (H (m := AngL) (Fun := F2) (γ := Bool) (l := ⟨⟩) (init := (0 : Nat))
    (f := fun _ b => pure (.done b)) (fun _ => F2.mk)
    (show Std.WP.WhileInvariant Nat M3 from fun flag _ => cond flag M3.bot M3.c) ()
    (fun _ mb => ⟨PartialOrder.rel_trans (M3.F2_meet_c mb) (rfl : M3.le .bot _ = true)⟩)).le_wp

-- `Std.WP.Spec.forInLoop_variant`: `AngM`, exit invariant `False`.
theorem Spec_forInLoop_variant_20 : ¬ drop0% Std.WP.Spec.forInLoop_variant 20 := by
  intro H
  obtain ⟨_, h⟩ := (H (m := AngM) (Fun := Nat) (γ := Nat) (l := ⟨⟩) (init := (0 : Nat))
    (f := fun _ b => pure (.done b)) (fun _ => (0 : Nat))
    (show Std.WP.WhileInvariant Nat Prop from fun flag _ => flag = false) ()).le_wp rfl
  exact Bool.noConfusion h

end WPRestHand

end WPPart

section DoPart

namespace WPRestHand.Do
open Std.Do

/-! ## `Std.Do` models -/

/-- `Id` whose `Std.Do` `wp` is constantly `⌜True⌝` (conjunctive, unsound). -/
def TopDo : Type → Type := Id
instance : Monad TopDo := inferInstanceAs (Monad Id)
instance : LawfulMonad TopDo := inferInstanceAs (LawfulMonad Id)
instance : MonadAttach TopDo := inferInstanceAs (MonadAttach Id)
instance : LawfulMonadAttach TopDo := inferInstanceAs (LawfulMonadAttach Id)
instance TopDo.wp : WP TopDo .pure where
  wp _ := ⟨fun _ => SPred.pure True, fun _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩⟩

/-- `Option` with `bind` constantly `none` (copied from `DoSPredHand.ZB`): not a lawful monad, lawful
`attach`, every `Ensures` holds; with `wp ≡ ⌜True⌝` it is `WPSound`. -/
def ZB (α : Type) : Type := Option α
instance : Monad ZB where
  pure a := (some a : Option _)
  bind _ _ := (none : Option _)
  map f x := Option.map f (show Option _ from x)
instance : MonadAttach ZB where
  CanReturn x a := (show Option _ from x) = some a
  attach x := Option.attach (show Option _ from x)
instance : LawfulMonadAttach ZB where
  map_attach {_ x} := by cases x <;> rfl
  canReturn_map_imp {_ P x a} h := by
    cases x with
    | none => cases h
    | some z => cases h; exact z.2
instance ZB.wp : WP ZB .pure where
  wp _ := ⟨fun _ => SPred.pure True, fun _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩⟩
instance ZB.sound : WPSound ZB .pure where
  ensures_of_wp _ := ⟨⟨(none : Option _), ⟨fun _ => rfl⟩⟩⟩

/-- `Id` with the trivial (non-lawful) attach; `wp`/`WPSound` from `Id`. -/
def TrivDo : Type → Type := Id
instance : Monad TrivDo := inferInstanceAs (Monad Id)
instance : LawfulMonad TrivDo := inferInstanceAs (LawfulMonad Id)
instance : MonadAttach TrivDo := @MonadAttach.trivial TrivDo _
instance TrivDo.wp : WP TrivDo .pure := inferInstanceAs (WP Id .pure)
instance TrivDo.sound : WPSound TrivDo .pure := inferInstanceAs (WPSound Id .pure)

theorem ent {P Q : SPred []} (h : P.down → Q.down) : P ⊢ₛ Q := h
theorem trip {α : Type} {x : Id α} {P : Assertion .pure} {Q : PostCond α .pure}
    (h : P.down → (wp⟦x⟧ Q).down) : Triple x P Q := Triple.iff.mpr (ent h)

theorem not_ensures_false {α : Type} (x : Id α) : ¬ Internal.Ensures (fun _ => False) x :=
  fun ⟨⟨y, _⟩⟩ => (show {a : α // False} from y).2

theorem id_may {α : Type} (a : α) : Internal.MayReturn (pure a : Id α) a :=
  ⟨fun ⟨⟨y, hy⟩⟩ => by
    have h : (show {b : α // _} from y).1 = a := hy.bind_eq (fun b => (pure b : Id α))
    exact h ▸ (show {b : α // _} from y).2⟩

theorem topdo_may {α : Type} (a : α) : Internal.MayReturn (pure a : TopDo α) a :=
  ⟨fun ⟨⟨y, hy⟩⟩ => by
    have h : (show {b : α // _} from y).1 = a := hy.bind_eq (fun b => (pure b : TopDo α))
    exact h ▸ (show {b : α // _} from y).2⟩

theorem id_triple_false {α : Type} (x : Id α) :
    ¬ Triple x (SPred.pure True : Assertion .pure) (PostCond.noThrow fun _ => SPred.pure False) :=
  fun h => h trivial

/-! ## Std.Do.Triple.Basic -/

-- `Std.Do.Triple.of_entails_wp`: `Id`, `⦃True⦄ pure 0 ⦃False⦄`.
theorem Triple_of_entails_wp_7 : ¬ drop0% Std.Do.Triple.of_entails_wp 7 :=
  fun H => id_triple_false _ (H (m := Id) (x := (pure 0 : Id Nat)))

-- `Std.Do.Triple.entails_wp_of_pre_post`: `Id`, pre `True`, post `False`.
theorem Triple_entails_wp_of_pre_post_9 : ¬ drop0% Std.Do.Triple.entails_wp_of_pre_post 9 :=
  fun H => H (m := Id) (x := (pure 0 : Id Nat)) (P := SPred.pure True) (P' := SPred.pure True)
    (Q := PostCond.noThrow fun _ => SPred.pure False) (Q' := PostCond.noThrow fun _ => SPred.pure False)
    SPred.entails.rfl PostCond.entails.rfl trivial

-- `Std.Do.Triple.entails_wp_of_pre_post`: `Id`, `P' = False` makes the triple trivial.
theorem Triple_entails_wp_of_pre_post_10 : ¬ drop0% Std.Do.Triple.entails_wp_of_pre_post 10 :=
  fun H => H (m := Id) (x := (pure 0 : Id Nat)) (P := SPred.pure True) (P' := SPred.pure False)
    (Q := PostCond.noThrow fun _ => SPred.pure False) (Q' := PostCond.noThrow fun _ => SPred.pure False)
    (trip fun h => False.elim h) PostCond.entails.rfl trivial

-- `Std.Do.Triple.entails_wp_of_pre_post`: `Id`, `Q' = True`, `Q = False`.
theorem Triple_entails_wp_of_pre_post_11 : ¬ drop0% Std.Do.Triple.entails_wp_of_pre_post 11 :=
  fun H => H (m := Id) (x := (pure 0 : Id Nat)) (P := SPred.pure True) (P' := SPred.pure True)
    (Q := PostCond.noThrow fun _ => SPred.pure False) (Q' := PostCond.noThrow fun _ => SPred.pure True)
    (trip fun h => h) SPred.entails.rfl trivial

-- `Std.Do.Triple.entails_wp_of_pre`: `Id`, pre `True`, post `False`.
theorem Triple_entails_wp_of_pre_8 : ¬ drop0% Std.Do.Triple.entails_wp_of_pre 8 :=
  fun H => H (m := Id) (x := (pure 0 : Id Nat)) (P := SPred.pure True) (P' := SPred.pure True)
    (Q := PostCond.noThrow fun _ => SPred.pure False) SPred.entails.rfl trivial

-- `Std.Do.Triple.entails_wp_of_pre`: `Id`, `P' = False`.
theorem Triple_entails_wp_of_pre_9 : ¬ drop0% Std.Do.Triple.entails_wp_of_pre 9 :=
  fun H => H (m := Id) (x := (pure 0 : Id Nat)) (P := SPred.pure True) (P' := SPred.pure False)
    (Q := PostCond.noThrow fun _ => SPred.pure False) (trip fun h => False.elim h) trivial

-- `Std.Do.Triple.entails_wp_of_post`: `Id`, pre `True`, post `False`.
theorem Triple_entails_wp_of_post_8 : ¬ drop0% Std.Do.Triple.entails_wp_of_post 8 :=
  fun H => H (m := Id) (x := (pure 0 : Id Nat)) (P := SPred.pure True)
    (Q := PostCond.noThrow fun _ => SPred.pure False) (Q' := PostCond.noThrow fun _ => SPred.pure False)
    PostCond.entails.rfl trivial

-- `Std.Do.Triple.entails_wp_of_post`: `Id`, `Q' = True`, `Q = False`.
theorem Triple_entails_wp_of_post_9 : ¬ drop0% Std.Do.Triple.entails_wp_of_post 9 :=
  fun H => H (m := Id) (x := (pure 0 : Id Nat)) (P := SPred.pure True)
    (Q := PostCond.noThrow fun _ => SPred.pure False) (Q' := PostCond.noThrow fun _ => SPred.pure True)
    (trip fun h => h) trivial

-- `Std.Do.Triple.pure`: `Id`, pre `True`, post `False`.
theorem Triple_pure_8 : ¬ drop0% Std.Do.Triple.pure 8 :=
  fun H => id_triple_false _ (H (m := Id) (P := SPred.pure True) (Q := PostCond.noThrow fun _ => SPred.pure False) 0)

-- `Std.Do.Triple.bind`: `Id`, intermediate `Q = False` makes `hf` trivial.
theorem Triple_bind_11 : ¬ drop0% Std.Do.Triple.bind 11 :=
  fun H => id_triple_false _ (H (m := Id) (P := SPred.pure True) (Q := fun _ => SPred.pure False)
    (R := PostCond.noThrow fun _ => SPred.pure False) (pure 0 : Id Nat) (fun _ => (pure 0 : Id Nat))
    (fun _ => trip fun h => False.elim h))

-- `Std.Do.Triple.bind`: `Id`, intermediate `Q = True`, final `False`.
theorem Triple_bind_12 : ¬ drop0% Std.Do.Triple.bind 12 :=
  fun H => id_triple_false _ (H (m := Id) (P := SPred.pure True) (Q := fun _ => SPred.pure True)
    (R := PostCond.noThrow fun _ => SPred.pure False) (pure 0 : Id Nat) (fun _ => (pure 0 : Id Nat))
    (fun h => h))

-- `Std.Do.Triple.and`: `Id`, `Q₁ = False`.
theorem Triple_and_9 : ¬ drop0% Std.Do.Triple.and 9 :=
  fun H => (H (m := Id) (P₁ := SPred.pure True) (P₂ := SPred.pure True)
    (Q₁ := PostCond.noThrow fun _ => SPred.pure False) (Q₂ := PostCond.noThrow fun _ => SPred.pure True)
    (pure 0 : Id Nat) (trip fun h => h) ⟨trivial, trivial⟩).1

-- `Std.Do.Triple.and`: `Id`, `Q₂ = False`.
theorem Triple_and_10 : ¬ drop0% Std.Do.Triple.and 10 :=
  fun H => (H (m := Id) (P₁ := SPred.pure True) (P₂ := SPred.pure True)
    (Q₁ := PostCond.noThrow fun _ => SPred.pure True) (Q₂ := PostCond.noThrow fun _ => SPred.pure False)
    (pure 0 : Id Nat) (trip fun h => h) ⟨trivial, trivial⟩).2

-- `Std.Do.Triple.mp`: `Id`, `Q₁ = False` makes `h₂` trivial.
theorem Triple_mp_9 : ¬ drop0% Std.Do.Triple.mp 9 :=
  fun H => (H (m := Id) (P₁ := SPred.pure True) (P₂ := SPred.pure True)
    (Q₁ := PostCond.noThrow fun _ => SPred.pure False) (Q₂ := PostCond.noThrow fun _ => SPred.pure False)
    (pure 0 : Id Nat) (trip fun _ h => h) ⟨trivial, trivial⟩).1

-- `Std.Do.Triple.mp`: `Id`, `Q₁ = True`, `Q₂ = False`.
theorem Triple_mp_10 : ¬ drop0% Std.Do.Triple.mp 10 :=
  fun H => (H (m := Id) (P₁ := SPred.pure True) (P₂ := SPred.pure True)
    (Q₁ := PostCond.noThrow fun _ => SPred.pure True) (Q₂ := PostCond.noThrow fun _ => SPred.pure False)
    (pure 0 : Id Nat) (trip fun h => h) ⟨trivial, trivial⟩).2

-- `Std.Do.Triple.observe`: `obs := set true` in `StateM Bool` changes the state.
theorem Triple_observe_10 : ¬ drop0% Std.Do.Triple.observe 10 :=
  fun H => Bool.noConfusion (H (m := StateM Bool) (ps := .arg Bool .pure) (obs := (set true : StateM Bool PUnit))
    (prog := (pure () : StateM Bool Unit)) (Pre := fun s => SPred.pure (s = false))
    (Q := PostCond.noThrow fun _ _ => SPred.pure True) (Post := PostCond.noThrow fun _ s => SPred.pure (s = true))
    (fun _ _ => trivial) (Triple.iff.mpr fun _ _ _ => rfl) false rfl)

-- `Std.Do.Triple.observe`: `Id`, `Q = False` makes `hgoal` trivial.
theorem Triple_observe_11 : ¬ drop0% Std.Do.Triple.observe 11 :=
  fun H => id_triple_false _ (H (m := Id) (obs := (pure () : Id Unit)) (prog := (pure () : Id Unit))
    (Pre := SPred.pure True) (Q := PostCond.noThrow fun _ => SPred.pure False)
    (Post := PostCond.noThrow fun _ => SPred.pure False) (fun _ h => h) (trip fun _ h => False.elim h))

-- `Std.Do.Triple.observe`: `Id`, `Q = True`, `Post = False`.
theorem Triple_observe_12 : ¬ drop0% Std.Do.Triple.observe 12 :=
  fun H => id_triple_false _ (H (m := Id) (obs := (pure () : Id Unit)) (prog := (pure () : Id Unit))
    (Pre := SPred.pure True) (Q := PostCond.noThrow fun _ => SPred.pure True)
    (Post := PostCond.noThrow fun _ => SPred.pure False) (fun _ h => h) (trip fun h => h))

/-! ## Std.Do.WP.Basic -/

-- `Std.Do.EStateM.of_wp_run_eq`: `prog = pure 0`, `x = .ok 1 ()`, `P` = "ok with value 0".
theorem EStateM_of_wp_run_eq_6 : ¬ drop0% Std.Do.EStateM.of_wp_run_eq 6 :=
  fun H => Nat.succ_ne_zero 0 (H (ε := Unit) (σ := Unit) (s := ()) (x := .ok 1 ()) (prog := pure 0)
    (fun r => match r with | .ok a _ => a = 0 | .error _ _ => False) (fun _ => rfl))

-- `Std.Do.EStateM.of_wp_run_eq`: `P = False`.
theorem EStateM_of_wp_run_eq_8 : ¬ drop0% Std.Do.EStateM.of_wp_run_eq 8 :=
  fun H => H (ε := Unit) (σ := Unit) (s := ()) (α := Nat) (x := .ok 0 ()) (prog := pure 0) rfl (fun _ => False)

end WPRestHand.Do

namespace WPRestHand.Do
open Std.Do

theorem ent1 {σ : Type} {P Q : SPred [σ]} (h : ∀ s, (P s).down → (Q s).down) : P ⊢ₛ Q := h

theorem topdo_not_ens {β : Type} (x : TopDo β) : ¬ Internal.Ensures (fun _ => False) x :=
  fun ⟨⟨y, _⟩⟩ => (show {b : β // False} from y).2

/-! ## Std.Do.WP.Sound -/

-- `Std.Do.WPSound.ensures_of_wp`: `TopDo` (`wp ≡ ⌜True⌝`) has no `False`-refinement of `pure 0`.
theorem WPSound_ensures_of_wp_4 : ¬ drop0% Std.Do.WPSound.ensures_of_wp 4 :=
  fun H => topdo_not_ens _ (@H TopDo .pure inferInstance TopDo.wp Nat (pure 0) (fun _ => False) (ent fun _ => trivial))

-- `Std.Do.WPSound.ensures_of_wp`: `Id`, `P = False`.
theorem WPSound_ensures_of_wp_8 : ¬ drop0% Std.Do.WPSound.ensures_of_wp 8 :=
  fun H => not_ensures_false _ (@H Id .pure inferInstance inferInstance inferInstance Nat (pure 0) (fun _ => False))

-- `Std.Do.WPSound.of_wp`: `TopDo`, `P = False` at `pure 0`.
theorem WPSound_of_wp_4 : ¬ drop0% Std.Do.WPSound.of_wp 4 :=
  fun H => H (m := TopDo) (ps := .pure) (x := (pure 0 : TopDo Nat)) (a := 0) (P := fun _ => False)
    (topdo_may 0) (ent fun _ => trivial)

-- `Std.Do.WPSound.of_wp`: `Id`, `pure 0`, `a = 1`, `P = (· = 0)`.
theorem WPSound_of_wp_9 : ¬ drop0% Std.Do.WPSound.of_wp 9 :=
  fun H => Nat.succ_ne_zero 0 (H (m := Id) (x := (pure 0 : Id Nat)) (a := 1) (P := fun n => n = 0) (ent fun _ => rfl))

-- `Std.Do.WPSound.of_wp`: `Id`, `P = False`.
theorem WPSound_of_wp_10 : ¬ drop0% Std.Do.WPSound.of_wp 10 :=
  fun H => H (m := Id) (x := (pure 0 : Id Nat)) (a := 0) (P := fun _ => False) (id_may 0)

-- `Std.Do.WPSound.of_wp_canReturn`: `ZB` (`bind ≡ none`, lawful attach, `wp ≡ ⌜True⌝`, `WPSound`).
theorem WPSound_of_wp_canReturn_3 : ¬ drop0% Std.Do.WPSound.of_wp_canReturn 3 :=
  fun H => H (m := ZB) (ps := .pure) (x := (pure 0 : ZB Nat)) (a := 0) (P := fun _ => False) rfl (ent fun _ => trivial)

-- `Std.Do.WPSound.of_wp_canReturn`: `TopDo` (lawful, `wp ≡ ⌜True⌝`).
theorem WPSound_of_wp_canReturn_5 : ¬ drop0% Std.Do.WPSound.of_wp_canReturn 5 :=
  fun H => H (m := TopDo) (ps := .pure) (x := (pure 0 : TopDo Nat)) (a := 0) (P := fun _ => False) rfl (ent fun _ => trivial)

-- `Std.Do.WPSound.of_wp_canReturn`: `TrivDo` (trivial attach), `pure 0`, `a = 1`.
theorem WPSound_of_wp_canReturn_7 : ¬ drop0% Std.Do.WPSound.of_wp_canReturn 7 :=
  fun H => Nat.succ_ne_zero 0 (H (m := TrivDo) (ps := .pure) (x := (pure 0 : TrivDo Nat)) (a := 1) (P := fun n => n = 0)
    trivial (ent fun _ => rfl))

-- `Std.Do.WPSound.of_wp_canReturn`: `Id`, `pure 0`, `a = 1`.
theorem WPSound_of_wp_canReturn_12 : ¬ drop0% Std.Do.WPSound.of_wp_canReturn 12 :=
  fun H => Nat.succ_ne_zero 0 (H (m := Id) (x := (pure 0 : Id Nat)) (a := 1) (P := fun n => n = 0) (ent fun _ => rfl))

-- `Std.Do.WPSound.of_wp_canReturn`: `Id`, `P = False`.
theorem WPSound_of_wp_canReturn_13 : ¬ drop0% Std.Do.WPSound.of_wp_canReturn 13 :=
  fun H => H (m := Id) (x := (pure 0 : Id Nat)) (a := 0) (P := fun _ => False) rfl

-- `Std.Do.instWPSoundReaderTArg`: base `TopDo`.
theorem instWPSoundReaderTArg_5 : ¬ drop0% Std.Do.instWPSoundReaderTArg 5 := fun H =>
  match ((H (m := TopDo) (ps := .pure) (ρ := Unit)).ensures_of_wp (x := (pure 0 : ReaderT Unit TopDo Nat))
    (P := fun _ => False) (ent1 fun _ _ => trivial)) with
  | ⟨⟨y, _⟩⟩ => ((y : Unit → {a : Nat // False}) ()).2

-- `Std.Do.instWPSoundStateTArgOfLawfulMonad`: base `TopDo`.
theorem instWPSoundStateTArgOfLawfulMonad_6 : ¬ drop0% Std.Do.instWPSoundStateTArgOfLawfulMonad 6 := fun H =>
  match ((H (m := TopDo) (ps := .pure) (σ := Unit)).ensures_of_wp (x := (pure 0 : StateT Unit TopDo Nat))
    (P := fun _ => False) (ent1 fun _ _ => trivial)) with
  | ⟨⟨y, _⟩⟩ => ((y : Unit → {a : Nat // False} × Unit) ()).1.2

-- `Std.Do.instWPSoundExceptTExceptPureOfLawfulMonad`: base `TopDo`; a refinement of `pure 0` is
-- `.error ()` (then binding `pure 1` differs) or carries a proof of `False`.
theorem instWPSoundExceptTExceptPureOfLawfulMonad_5 : ¬ drop0% Std.Do.instWPSoundExceptTExceptPureOfLawfulMonad 5 := by
  intro H
  obtain ⟨⟨y, hy⟩⟩ := (H (m := TopDo) (ε := Unit)).ensures_of_wp (x := (pure 0 : ExceptT Unit TopDo Nat))
    (P := fun _ => False) (ent fun _ => trivial)
  have h1 := hy.bind_eq (fun _ => (pure 1 : ExceptT Unit TopDo Nat))
  revert h1
  rcases y with _ | ⟨_, h⟩
  · exact fun h1 => nomatch (h1 : (Except.error () : Except Unit Nat) = Except.ok 1)
  · exact h.elim

-- `Std.Do.instWPSoundOptionTExceptPUnitPureOfLawfulMonad`: base `TopDo`; as for `ExceptT`.
theorem instWPSoundOptionTExceptPUnitPureOfLawfulMonad_4 : ¬ drop0% Std.Do.instWPSoundOptionTExceptPUnitPureOfLawfulMonad 4 := by
  intro H
  obtain ⟨⟨y, hy⟩⟩ := (H (m := TopDo)).ensures_of_wp (x := (pure 0 : OptionT TopDo Nat))
    (P := fun _ => False) (ent fun _ => trivial)
  have h1 := hy.bind_eq (fun _ => (pure 1 : OptionT TopDo Nat))
  revert h1
  rcases y with _ | ⟨_, h⟩
  · exact fun h1 => nomatch (h1 : (none : Option Nat) = some 1)
  · exact h.elim

-- `Std.Do.Id.of_wp_run_eq`: `prog = pure 0`, `x = 1`, `P = (· = 0)`.
theorem Id_of_wp_run_eq_3 : ¬ drop0% Std.Do.Id.of_wp_run_eq 3 :=
  fun H => Nat.succ_ne_zero 0 (H (x := 1) (prog := (pure 0 : Id Nat)) (fun n => n = 0) (ent fun _ => rfl))

-- `Std.Do.Id.of_wp_run_eq`: `P = False`.
theorem Id_of_wp_run_eq_5 : ¬ drop0% Std.Do.Id.of_wp_run_eq 5 :=
  fun H => H (x := 0) (prog := (pure 0 : Id Nat)) rfl (fun _ => False)

-- `Std.Do.ReaderT.ensures_of_wp_run`: base `TopDo`, `P = False`.
theorem ReaderT_ensures_of_wp_run_4 : ¬ drop0% Std.Do.ReaderT.ensures_of_wp_run 4 :=
  fun H => topdo_not_ens _ (H (m := TopDo) (ps := .pure) (prog := (pure 0 : ReaderT Unit TopDo Nat)) ()
    (fun _ => False) (ent fun _ => trivial))

-- `Std.Do.ReaderT.ensures_of_wp_run`: base `Id`, `P = False`.
theorem ReaderT_ensures_of_wp_run_10 : ¬ drop0% Std.Do.ReaderT.ensures_of_wp_run 10 :=
  fun H => not_ensures_false _ (H (m := Id) (prog := (pure 0 : ReaderT Unit Id Nat)) () (fun _ => False))

-- `Std.Do.ReaderT.of_wp_run`: base `ZB` (not a lawful monad).
theorem ReaderT_of_wp_run_3 : ¬ drop0% Std.Do.ReaderT.of_wp_run 3 :=
  fun H => H (m := ZB) (ps := .pure) (prog := fun _ => (pure 0 : ZB Nat)) (r := ()) (a := 0) (fun _ => False) rfl
    (ent fun _ => trivial)

-- `Std.Do.ReaderT.of_wp_run`: base `TopDo`.
theorem ReaderT_of_wp_run_5 : ¬ drop0% Std.Do.ReaderT.of_wp_run 5 :=
  fun H => H (m := TopDo) (ps := .pure) (prog := pure 0) (r := ()) (a := 0) (fun _ => False) rfl (ent fun _ => trivial)

-- `Std.Do.ReaderT.of_wp_run`: base `TrivDo` (trivial attach), `a = 1`.
theorem ReaderT_of_wp_run_7 : ¬ drop0% Std.Do.ReaderT.of_wp_run 7 :=
  fun H => Nat.succ_ne_zero 0 (H (m := TrivDo) (ps := .pure) (prog := pure 0) (r := ()) (a := 1) (fun n => n = 0)
    trivial (ent fun _ => rfl))

-- `Std.Do.ReaderT.of_wp_run`: base `Id`, `a = 1`.
theorem ReaderT_of_wp_run_14 : ¬ drop0% Std.Do.ReaderT.of_wp_run 14 :=
  fun H => Nat.succ_ne_zero 0 (H (m := Id) (prog := pure 0) (r := ()) (a := 1) (fun n => n = 0) (ent fun _ => rfl))

-- `Std.Do.ReaderT.of_wp_run`: base `Id`, `P = False`.
theorem ReaderT_of_wp_run_15 : ¬ drop0% Std.Do.ReaderT.of_wp_run 15 :=
  fun H => H (m := Id) (prog := (pure 0 : ReaderT Unit Id Nat)) (r := ()) (a := 0) (fun _ => False) rfl

-- `Std.Do.ReaderM.of_wp_run_eq`: `prog = pure 0`, `x = 1`.
theorem ReaderM_of_wp_run_eq_5 : ¬ drop0% Std.Do.ReaderM.of_wp_run_eq 5 :=
  fun H => Nat.succ_ne_zero 0 (H (x := 1) (r := ()) (prog := pure 0) (fun n => n = 0) (ent fun _ => rfl))

-- `Std.Do.ReaderM.of_wp_run_eq`: `P = False`.
theorem ReaderM_of_wp_run_eq_7 : ¬ drop0% Std.Do.ReaderM.of_wp_run_eq 7 :=
  fun H => H (α := Nat) (x := 0) (r := ()) (prog := pure 0) rfl (fun _ => False)

-- `Std.Do.StateT.ensures_of_wp_run`: base `TopDo`, `P = False`.
theorem StateT_ensures_of_wp_run_4 : ¬ drop0% Std.Do.StateT.ensures_of_wp_run 4 :=
  fun H => topdo_not_ens _ (H (m := TopDo) (ps := .pure) (prog := (pure 0 : StateT Unit TopDo Nat)) ()
    (fun _ => False) (ent fun _ => trivial))

-- `Std.Do.StateT.ensures_of_wp_run`: base `Id`, `P = False`.
theorem StateT_ensures_of_wp_run_10 : ¬ drop0% Std.Do.StateT.ensures_of_wp_run 10 :=
  fun H => not_ensures_false _ (H (m := Id) (prog := (pure 0 : StateT Unit Id Nat)) () (fun _ => False))

-- `Std.Do.StateT.of_wp_run`: base `ZB` (not a lawful monad).
theorem StateT_of_wp_run_3 : ¬ drop0% Std.Do.StateT.of_wp_run 3 :=
  fun H => H (m := ZB) (ps := .pure) (prog := fun s => (pure (0, s) : ZB (Nat × Unit))) (s := ()) (p := (0, ()))
    (fun _ => False) rfl (ent fun _ => trivial)

-- `Std.Do.StateT.of_wp_run`: base `TopDo`.
theorem StateT_of_wp_run_5 : ¬ drop0% Std.Do.StateT.of_wp_run 5 :=
  fun H => H (m := TopDo) (ps := .pure) (prog := pure 0) (s := ()) (p := (0, ())) (fun _ => False) rfl
    (ent fun _ => trivial)

-- `Std.Do.StateT.of_wp_run`: base `TrivDo` (trivial attach), `p = (1, ())`.
theorem StateT_of_wp_run_7 : ¬ drop0% Std.Do.StateT.of_wp_run 7 :=
  fun H => Nat.succ_ne_zero 0 (H (m := TrivDo) (ps := .pure) (prog := pure 0) (s := ()) (p := (1, ()))
    (fun q => q.1 = 0) trivial (ent fun _ => rfl))

-- `Std.Do.StateT.of_wp_run`: base `Id`, `p = (1, ())`.
theorem StateT_of_wp_run_14 : ¬ drop0% Std.Do.StateT.of_wp_run 14 :=
  fun H => Nat.succ_ne_zero 0 (H (m := Id) (prog := pure 0) (s := ()) (p := (1, ())) (fun q => q.1 = 0)
    (ent fun _ => rfl))

-- `Std.Do.StateT.of_wp_run`: base `Id`, `P = False`.
theorem StateT_of_wp_run_15 : ¬ drop0% Std.Do.StateT.of_wp_run 15 :=
  fun H => H (m := Id) (prog := (pure 0 : StateT Unit Id Nat)) (s := ()) (p := (0, ())) (fun _ => False) rfl

-- `Std.Do.StateM.of_wp_run_eq`: `prog = pure 0`, `x = (1, ())`.
theorem StateM_of_wp_run_eq_5 : ¬ drop0% Std.Do.StateM.of_wp_run_eq 5 :=
  fun H => Nat.succ_ne_zero 0 (H (x := (1, ())) (s := ()) (prog := pure 0) (fun q => q.1 = 0) (ent fun _ => rfl))

-- `Std.Do.StateM.of_wp_run_eq`: `P = False`.
theorem StateM_of_wp_run_eq_7 : ¬ drop0% Std.Do.StateM.of_wp_run_eq 7 :=
  fun H => H (α := Nat) (x := (0, ())) (s := ()) (prog := pure 0) rfl (fun _ => False)

-- `Std.Do.StateM.of_wp_run'_eq`: `prog = pure 0`, `x = 1`.
theorem StateM_of_wp_run'_eq_5 : ¬ drop0% Std.Do.StateM.of_wp_run'_eq 5 :=
  fun H => Nat.succ_ne_zero 0 (H (x := 1) (s := ()) (prog := pure 0) (fun n => n = 0) (ent fun _ => rfl))

-- `Std.Do.StateM.of_wp_run'_eq`: `P = False`.
theorem StateM_of_wp_run'_eq_7 : ¬ drop0% Std.Do.StateM.of_wp_run'_eq 7 :=
  fun H => H (α := Nat) (x := 0) (s := ()) (prog := (pure 0 : StateM Unit Nat)) rfl (fun _ => False)

-- `Std.Do.ExceptT.ensures_of_wp_run`: base `TopDo`, `P = False`.
theorem ExceptT_ensures_of_wp_run_4 : ¬ drop0% Std.Do.ExceptT.ensures_of_wp_run 4 :=
  fun H => topdo_not_ens _ (H (m := TopDo) (prog := (pure 0 : ExceptT Unit TopDo Nat)) (fun _ => False)
    (ent fun _ => trivial))

-- `Std.Do.ExceptT.ensures_of_wp_run`: base `Id`, `P = False`.
theorem ExceptT_ensures_of_wp_run_9 : ¬ drop0% Std.Do.ExceptT.ensures_of_wp_run 9 :=
  fun H => not_ensures_false _ (H (m := Id) (prog := (pure 0 : ExceptT Unit Id Nat)) (fun _ => False))

-- `Std.Do.ExceptT.of_wp_run`: base `ZB` (not a lawful monad).
theorem ExceptT_of_wp_run_2 : ¬ drop0% Std.Do.ExceptT.of_wp_run 2 :=
  fun H => H (m := ZB) (prog := ExceptT.mk (pure (.ok 0) : ZB (Except Unit Nat))) (x := .ok 0) (fun _ => False) rfl
    (ent fun _ => trivial)

-- `Std.Do.ExceptT.of_wp_run`: base `TopDo`.
theorem ExceptT_of_wp_run_4 : ¬ drop0% Std.Do.ExceptT.of_wp_run 4 :=
  fun H => H (m := TopDo) (ε := Unit) (prog := pure 0) (x := .ok 0) (fun _ => False) rfl (ent fun _ => trivial)

-- `Std.Do.ExceptT.of_wp_run`: base `TrivDo` (trivial attach), `x = .ok 1`.
theorem ExceptT_of_wp_run_6 : ¬ drop0% Std.Do.ExceptT.of_wp_run 6 :=
  fun H => Nat.succ_ne_zero 0 (Except.ok.inj (H (m := TrivDo) (ε := Unit) (prog := pure 0) (x := .ok 1)
    (fun r => r = .ok 0) trivial (ent fun _ => rfl)))

-- `Std.Do.ExceptT.of_wp_run`: base `Id`, `x = .ok 1`.
theorem ExceptT_of_wp_run_12 : ¬ drop0% Std.Do.ExceptT.of_wp_run 12 :=
  fun H => Nat.succ_ne_zero 0 (Except.ok.inj (H (m := Id) (ε := Unit) (prog := pure 0) (x := .ok 1)
    (fun r => r = .ok 0) (ent fun _ => rfl)))

-- `Std.Do.ExceptT.of_wp_run`: base `Id`, `P = False`.
theorem ExceptT_of_wp_run_13 : ¬ drop0% Std.Do.ExceptT.of_wp_run 13 :=
  fun H => H (m := Id) (ε := Unit) (prog := (pure 0 : ExceptT Unit Id Nat)) (x := .ok 0) (fun _ => False) rfl

-- `Std.Do.Except.of_wp_eq`: `prog = .ok 0`, `x = .ok 1`.
theorem Except_of_wp_eq_4 : ¬ drop0% Std.Do.Except.of_wp_eq 4 :=
  fun H => Nat.succ_ne_zero 0 (Except.ok.inj (H (ε := Unit) (x := .ok 1) (prog := .ok 0) (fun r => r = .ok 0)
    (ent fun _ => rfl)))

-- `Std.Do.Except.of_wp_eq`: `P = False`.
theorem Except_of_wp_eq_6 : ¬ drop0% Std.Do.Except.of_wp_eq 6 :=
  fun H => H (ε := Unit) (α := Nat) (x := .ok 0) (prog := .ok 0) rfl (fun _ => False)

-- `Std.Do.Except.of_wp`: `P = False`.
theorem Except_of_wp_4 : ¬ drop0% Std.Do.Except.of_wp 4 :=
  fun H => H (ε := Unit) (α := Nat) (prog := .ok 0) (fun _ => False)

-- `Std.Do.OptionT.ensures_of_wp_run`: base `TopDo`, `P = False`.
theorem OptionT_ensures_of_wp_run_4 : ¬ drop0% Std.Do.OptionT.ensures_of_wp_run 4 :=
  fun H => topdo_not_ens _ (H (m := TopDo) (prog := (pure 0 : OptionT TopDo Nat)) (fun _ => False)
    (ent fun _ => trivial))

-- `Std.Do.OptionT.ensures_of_wp_run`: base `Id`, `P = False`.
theorem OptionT_ensures_of_wp_run_8 : ¬ drop0% Std.Do.OptionT.ensures_of_wp_run 8 :=
  fun H => not_ensures_false _ (H (m := Id) (prog := (pure 0 : OptionT Id Nat)) (fun _ => False))

-- `Std.Do.OptionT.of_wp_run`: base `ZB` (not a lawful monad).
theorem OptionT_of_wp_run_2 : ¬ drop0% Std.Do.OptionT.of_wp_run 2 :=
  fun H => H (m := ZB) (prog := OptionT.mk (pure (some 0) : ZB (Option Nat))) (x := some 0) (fun _ => False) rfl
    (ent fun _ => trivial)

-- `Std.Do.OptionT.of_wp_run`: base `TopDo`.
theorem OptionT_of_wp_run_4 : ¬ drop0% Std.Do.OptionT.of_wp_run 4 :=
  fun H => H (m := TopDo) (prog := pure 0) (x := some 0) (fun _ => False) rfl (ent fun _ => trivial)

-- `Std.Do.OptionT.of_wp_run`: base `TrivDo` (trivial attach), `x = some 1`.
theorem OptionT_of_wp_run_6 : ¬ drop0% Std.Do.OptionT.of_wp_run 6 :=
  fun H => Nat.succ_ne_zero 0 (Option.some.inj (H (m := TrivDo) (prog := pure 0) (x := some 1)
    (fun r => r = some 0) trivial (ent fun _ => rfl)))

-- `Std.Do.OptionT.of_wp_run`: base `Id`, `x = some 1`.
theorem OptionT_of_wp_run_11 : ¬ drop0% Std.Do.OptionT.of_wp_run 11 :=
  fun H => Nat.succ_ne_zero 0 (Option.some.inj (H (m := Id) (prog := pure 0) (x := some 1)
    (fun r => r = some 0) (ent fun _ => rfl)))

-- `Std.Do.OptionT.of_wp_run`: base `Id`, `P = False`.
theorem OptionT_of_wp_run_12 : ¬ drop0% Std.Do.OptionT.of_wp_run 12 :=
  fun H => H (m := Id) (prog := (pure 0 : OptionT Id Nat)) (x := some 0) (fun _ => False) rfl

-- `Std.Do.Option.of_wp_eq`: `prog = none`, `x = some 0`, `P = (· = none)`.
theorem Option_of_wp_eq_3 : ¬ drop0% Std.Do.Option.of_wp_eq 3 :=
  fun H => Option.some_ne_none 0 (H (x := some 0) (prog := none) (fun o => o = none) (ent fun _ => rfl))

-- `Std.Do.Option.of_wp_eq`: `P = False`.
theorem Option_of_wp_eq_5 : ¬ drop0% Std.Do.Option.of_wp_eq 5 :=
  fun H => H (α := Nat) (x := none) (prog := none) rfl (fun _ => False)

end WPRestHand.Do

end DoPart
