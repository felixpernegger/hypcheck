import Lean

/-!
Hand pass `CoreA` (hand13): the 100 unresolved hypotheses of `Init.Core` (84), `Init.Prelude` (9)
and `Init.Classical` (7): basic logic, `Eq`/`HEq`/cast lemmas, `Nonempty`/`Subsingleton`/`Decidable`
instances, `ite`/`dite`, `Setoid`/`Quot`/`Quotient`/`Squash`, relations (`Equivalence`,
`Relation.TransGen`, `Std.Symm`, `Std.Trichotomous`) and the `Std` identity classes.

95 necessary, 5 removable, 0 independent.

Reusable models (namespace `CoreAHand`):
* `bFalse : BEq Bool` (never equal: not reflexive), `bTrue : BEq Bool` (always equal: reflexive,
  not lawful).
* `eqSetoid α`, `eqEquiv α`: the equality setoid / equivalence (used on `Bool` and `True`).
* `rNe` (`≠` on `Bool`: symmetric, not transitive), `rLt` (`<` on `Bool`: trichotomous `rLt_trich`,
  not symmetric; `false` has no predecessor, `true` no successor, so `transGen_head`/`transGen_last`
  refute `Relation.TransGen` chains).
* `bool_ne_unit : Bool = Unit → False` refutes type equations; `ndrec_const` evaluates `▸` in a
  constant family.
* Empty types (`False`, `Empty`, `PSum False False`, `Id Empty`) for the `Nonempty` rows, `Bool`,
  `Unit × Bool`, `Unit → Bool` for the `Subsingleton` rows.

Most refutations need a carrier with two distinct elements, so they use `drop1%`/`indep1%`
(universes set to 1): at universe 0 every carrier is a proposition and several of these `T'` hold by
proof irrelevance/`propext` (e.g. `type_eq_of_heq`, `Subsingleton.helim`, `noConfusion_of_Nat`).

Removable (5): the dependent `Nonempty α` of `Classical.epsilon_spec_aux` (follows from the
independent premise `∃ y, p y`), and the instance arguments of
`Std.LawfulLeftIdentity.toLeftIdentity`, `Std.LawfulRightIdentity.toRightIdentity`,
`Std.Identity.toLeftIdentity`, `Std.LawfulIdentity.toIdentity` (the conclusions are the field-free
marker classes LeftIdentity, RightIdentity, Identity, which hold for every operation).

Run with the lean4 repo's stage1 binary: `runs/hand13/lean.sh checks/CoreAHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option warn.classDefReducibility false

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
/-- `drop0% T i`: like `drop% T i`, with all universes set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => levelZero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `drop1% T i`: like `drop% T i`, with all universes set to `1` (for refutations). -/
elab "drop1% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep0% T i`: like `indep% T i`, with all universes set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => levelZero
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
/-- `indep1% T i`: like `indep% T i`, with all universes set to `1` (for refutations). -/
elab "indep1% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
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

namespace CoreAHand

/-! ## Models -/

/-- A `BEq Bool` that never reports equality (not reflexive). -/
def bFalse : BEq Bool := ⟨fun _ _ => false⟩
/-- A `BEq Bool` that always reports equality (reflexive, not lawful). -/
def bTrue : BEq Bool := ⟨fun _ _ => true⟩

/-- The equality setoid. -/
def eqSetoid (α : Sort u) : Setoid α := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
theorem eqEquiv (α : Sort u) : Equivalence (@Eq α) := ⟨Eq.refl, Eq.symm, Eq.trans⟩

/-- Inequality on `Bool`: symmetric, not transitive, not reflexive. -/
abbrev rNe (a b : Bool) : Prop := a ≠ b
/-- `<` on `Bool`: trichotomous, not symmetric; `false` has no predecessor, `true` no successor. -/
abbrev rLt (a b : Bool) : Prop := a = false ∧ b = true
theorem rLt_trich : Std.Trichotomous rLt := ⟨fun a b => by cases a <;> cases b <;> decide⟩

-- Helper: a chain in the transitive closure starts with an `r`-step.
theorem transGen_head {α : Sort u} {r : α → α → Prop} {a c : α} (h : Relation.TransGen r a c) :
    ∃ b, r a b := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

-- Helper: a chain in the transitive closure ends with an `r`-step.
theorem transGen_last {α : Sort u} {r : α → α → Prop} {a c : α} (h : Relation.TransGen r a c) :
    ∃ b, r b c := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

-- Helper: the types Bool and Unit differ (Unit is a subsingleton).
theorem bool_ne_unit (h : Bool = Unit) : False := by
  have : Subsingleton Bool := h ▸ inferInstance
  exact absurd (Subsingleton.elim true false) (by decide)

-- Helper: transport along an equation in a constant family is the identity.
theorem ndrec_const {α : Sort u} {β : Sort v} {x y : α} (e : x = y) (b : β) :
    Eq.ndrec (motive := fun _ => β) b e = b := by
  cases e; rfl

/-! ## Classical -/

-- `Classical.choose_spec`: dependent `h : ∃ x, p x`; refuted with p false everywhere.
theorem Classical.choose_spec_h2 : ¬ indep0% Classical.choose_spec 2 :=
  fun h => (@h True (fun _ => False)).elim fun _ hx => hx

-- `Classical.exists_true_of_nonempty`: an empty type has no element.
theorem Classical.exists_true_of_nonempty_h1 : ¬ drop0% Classical.exists_true_of_nonempty 1 :=
  fun h => (@h False).elim fun x _ => x

-- `Classical.epsilon_spec_aux`: dependent `h : Nonempty α` (the instance of `epsilon`). Removable: it follows from the independent premise `∃ y, p y`.
theorem Classical.epsilon_spec_aux_h1 : indep% Classical.epsilon_spec_aux 1 :=
  fun _ ⟨y, _⟩ => ⟨y⟩

-- `Classical.epsilon_spec_aux`: without `∃ y, p y`, p false everywhere.
theorem Classical.epsilon_spec_aux_h3 : ¬ drop0% Classical.epsilon_spec_aux 3 :=
  fun h => @h True ⟨trivial⟩ (fun _ => False)

-- `Classical.epsilon_spec`: dependent `hex : ∃ y, p y`; refuted with p false everywhere.
theorem Classical.epsilon_spec_h2 : ¬ indep0% Classical.epsilon_spec 2 :=
  fun h => (@h True (fun _ => False)).elim fun _ hx => hx

-- `Classical.axiomOfChoice`: the empty relation on a one-point domain has no choice function.
theorem Classical.axiomOfChoice_h3 : ¬ drop0% Classical.axiomOfChoice 3 :=
  fun h => (@h True (fun _ => True) (fun _ _ => False)).elim fun _ hf => hf trivial

-- `Exists.choose_spec`: dependent `P : ∃ a, p a`; refuted with p false everywhere.
theorem Exists.choose_spec_h2 : ¬ indep0% Exists.choose_spec 2 :=
  fun h => (@h True (fun _ => False)).elim fun _ hx => hx

/-! ## Nonempty -/

-- `PSum.nonemptyLeft`: PSum False False is empty.
theorem PSum.nonemptyLeft_h2 : ¬ drop0% PSum.nonemptyLeft 2 := fun h => by
  obtain ⟨a | a⟩ := @h False False <;> exact a.elim

-- `PSum.nonemptyRight`: PSum False False is empty.
theorem PSum.nonemptyRight_h2 : ¬ drop0% PSum.nonemptyRight 2 := fun h => by
  obtain ⟨a | a⟩ := @h False False <;> exact a.elim

-- `Sum.nonemptyLeft`: Empty ⊕ Empty is empty.
theorem Sum.nonemptyLeft_h2 : ¬ drop0% Sum.nonemptyLeft 2 := fun h => by
  obtain ⟨a | a⟩ := @h Empty Empty <;> exact a.elim

-- `Sum.nonemptyRight`: Empty ⊕ Empty is empty.
theorem Sum.nonemptyRight_h2 : ¬ drop0% Sum.nonemptyRight 2 := fun h => by
  obtain ⟨a | a⟩ := @h Empty Empty <;> exact a.elim

-- `instNonemptyProd`: Empty × Unit is empty.
theorem instNonemptyProd_h2 : ¬ drop0% instNonemptyProd 2 := fun h => by
  obtain ⟨x⟩ := @h Empty Unit ⟨()⟩; exact x.1.elim

-- `instNonemptyProd`: Unit × Empty is empty.
theorem instNonemptyProd_h3 : ¬ drop0% instNonemptyProd 3 := fun h => by
  obtain ⟨x⟩ := @h Unit Empty ⟨()⟩; exact x.2.elim

-- `instNonemptyMProd`: MProd Empty Unit is empty.
theorem instNonemptyMProd_h2 : ¬ drop0% instNonemptyMProd 2 := fun h => by
  obtain ⟨x⟩ := @h Empty Unit ⟨()⟩; exact x.1.elim

-- `instNonemptyMProd`: MProd Unit Empty is empty.
theorem instNonemptyMProd_h3 : ¬ drop0% instNonemptyMProd 3 := fun h => by
  obtain ⟨x⟩ := @h Unit Empty ⟨()⟩; exact x.2.elim

-- `instNonemptyPProd`: PProd False True is empty.
theorem instNonemptyPProd_h2 : ¬ drop0% instNonemptyPProd 2 := fun h => by
  obtain ⟨x⟩ := @h False True ⟨trivial⟩; exact x.1.elim

-- `instNonemptyPProd`: PProd True False is empty.
theorem instNonemptyPProd_h3 : ¬ drop0% instNonemptyPProd 3 := fun h => by
  obtain ⟨x⟩ := @h True False ⟨trivial⟩; exact x.2.elim

-- `Nonempty.elim`: without `Nonempty α`, α := False, p := False.
theorem Nonempty.elim_h2 : ¬ drop0% Nonempty.elim 2 := fun h => @h False False (fun a => a)

-- `Nonempty.elim`: without the elimination premise, p := False.
theorem Nonempty.elim_h3 : ¬ drop0% Nonempty.elim 3 := fun h => @h True False ⟨trivial⟩

-- `Pi.instNonempty`: True → False is empty.
theorem Pi.instNonempty_h2 : ¬ drop0% Pi.instNonempty 2 := fun h => by
  obtain ⟨f⟩ := @h True (fun _ => False); exact f trivial

-- `instNonemptyOfMonad`: Id Empty is empty.
theorem instNonemptyOfMonad_h3 : ¬ drop0% instNonemptyOfMonad 3 := fun h => by
  obtain ⟨x⟩ := @h Id Empty inferInstance; exact Empty.elim x

/-! ## BEq -/

-- `LawfulSingleton.insert_empty_eq`: on Nat with empty collection 0, insert ignoring the element, singleton 1.
theorem LawfulSingleton.insert_empty_eq_h5 : ¬ drop0% LawfulSingleton.insert_empty_eq 5 :=
  fun h => absurd (@h Nat Nat ⟨0⟩ ⟨fun _ b => b⟩ ⟨fun _ => 1⟩ 0) (by decide)

-- `beq_of_eq`: bFalse is not reflexive.
theorem beq_of_eq_h2 : ¬ drop0% beq_of_eq 2 :=
  fun h => absurd (@h Bool bFalse true true rfl) (by decide)

-- `not_eq_of_beq_eq_false`: bFalse reports true and true unequal.
theorem not_eq_of_beq_eq_false_h2 : ¬ drop0% not_eq_of_beq_eq_false 2 :=
  fun h => @h Bool bFalse true true rfl rfl

-- `ne_of_beq_false`: bFalse reports true and true unequal.
theorem ne_of_beq_false_h2 : ¬ drop0% ne_of_beq_false 2 :=
  fun h => @h Bool bFalse true true rfl rfl

-- `beq_false_of_ne`: bTrue reports true and false equal.
theorem beq_false_of_ne_h2 : ¬ drop0% beq_false_of_ne 2 :=
  fun h => absurd (@h Bool bTrue true false (by decide)) (by decide)

-- `Subtype.instReflBEq`: the subtype of bFalse is not reflexive.
theorem Subtype.instReflBEq_h3 : ¬ drop0% Subtype.instReflBEq 3 :=
  fun h => absurd (@ReflBEq.rfl _ _ (@h Bool (fun _ => True) bFalse) ⟨true, trivial⟩) (by decide)

-- `Subtype.instLawfulBEq`: the subtype of bFalse is not reflexive.
theorem Subtype.instLawfulBEq_h3 : ¬ drop0% Subtype.instLawfulBEq 3 :=
  fun h => absurd (@ReflBEq.rfl _ _ (@h Bool (fun _ => True) bFalse).toReflBEq ⟨true, trivial⟩)
    (by decide)

/-! ## Eq, HEq, casts -/

-- `Eq.substr`: without `b = a`, p := (· = true), a := true, b := false.
theorem Eq.substr_h4 : ¬ drop1% Eq.substr 4 :=
  fun h => absurd (@h Bool (fun x => x = true) true false rfl) (by decide)

-- `Eq.substr`: without `p a`, p := False.
theorem Eq.substr_h5 : ¬ drop0% Eq.substr 5 :=
  fun h => @h True (fun _ => False) trivial trivial rfl

-- `Eq.subst`: without `motive a`, motive := False.
theorem Eq.subst_h5 : ¬ drop0% Eq.subst 5 :=
  fun h => @h True (fun _ => False) trivial trivial rfl

-- `type_eq_of_heq`: Bool ≠ Unit (needs universe 1; inhabited propositions are equal).
theorem type_eq_of_heq_h4 : ¬ drop1% type_eq_of_heq 4 :=
  fun h => bool_ne_unit (@h Bool Unit true ())

-- `eqRec_heq`: dependent `h : a = a'`; true ≠ false in Bool.
theorem eqRec_heq_h4 : ¬ indep1% eqRec_heq 4 :=
  fun h => absurd (@h Bool (fun _ => Unit) true false ()) (by decide)

-- `eqRec_heq_iff`: dependent `h : a = b`; true ≠ false in Bool.
theorem eqRec_heq_iff_h6 : ¬ indep1% eqRec_heq_iff 6 :=
  fun h => absurd (@h Unit Bool true (fun _ _ => Unit) false () ()) (by decide)

-- `heq_eqRec_iff`: dependent `h : a = b`; true ≠ false in Bool.
theorem heq_eqRec_iff_h6 : ¬ indep1% heq_eqRec_iff 6 :=
  fun h => absurd (@h Unit Bool true (fun _ _ => Unit) false () ()) (by decide)

-- `apply_eqRec`: dependent `h : a = b`; true ≠ false in Bool.
theorem apply_eqRec_h5 : ¬ indep1% apply_eqRec 5 :=
  fun h => absurd (@h Unit Bool true (fun _ _ => Unit) false (fun _ => ())) (by decide)

-- `heq_of_eqRec_eq`: dependent `h₁ : α = β`; Bool ≠ Unit.
theorem heq_of_eqRec_eq_h4 : ¬ indep1% heq_of_eqRec_eq 4 :=
  fun h => bool_ne_unit (@h Bool Unit true ())

-- `cast_heq`: dependent `h : α = β`; True ≠ False.
theorem cast_heq_h2 : ¬ indep0% cast_heq 2 :=
  fun h => cast (@h True False trivial) trivial

-- `Subsingleton.helim`: without `α = β`, HEq () true would give Unit = Bool.
theorem Subsingleton.helim_h3 : ¬ drop1% Subsingleton.helim 3 :=
  fun h => bool_ne_unit (type_eq_of_heq (@h Unit Bool inferInstance () true)).symm

-- `PSigma.eta`: dependent `h₁ : a₁ = a₂`; true ≠ false in Bool.
theorem PSigma.eta_h6 : ¬ indep1% PSigma.eta 6 :=
  fun h => absurd (@h Bool (fun _ => Unit) true false () ()) (by decide)

-- `PSigma.eta`: without `h₁ ▸ b₁ = b₂`, ⟨(), true⟩ ≠ ⟨(), false⟩.
theorem PSigma.eta_h7 : ¬ drop1% PSigma.eta 7 :=
  fun h => absurd (congrArg (fun x : (_ : Unit) ×' Bool => x.2)
    (@h Unit (fun _ => Bool) () () true false rfl)) (by decide)

-- `congr`: without `f₁ = f₂`, two different constant functions.
theorem congr_h6 : ¬ drop1% congr 6 :=
  fun h => absurd (@h Unit Bool (fun _ => true) (fun _ => false) () () rfl) (by decide)

-- `congrFun`: without `f = g`, two different constant functions.
theorem congrFun_h4 : ¬ drop1% congrFun 4 :=
  fun h => absurd (@h Unit (fun _ => Bool) (fun _ => true) (fun _ => false) ()) (by decide)

-- `congrFun'`: without `f = g`, two different constant functions.
theorem congrFun'_h4 : ¬ drop1% congrFun' 4 :=
  fun h => absurd (@h Unit Bool (fun _ => true) (fun _ => false) ()) (by decide)

-- `Exists.elim`: without the elimination premise, b := False.
theorem Exists.elim_h4 : ¬ drop0% Exists.elim 4 :=
  fun h => @h True (fun _ => True) False ⟨trivial, trivial⟩

-- `Iff.subst`: without `a ↔ b`, p := id, a := True, b := False.
theorem Iff.subst_h3 : ¬ drop% Iff.subst 3 := fun h => @h True False id trivial

-- `Iff.subst`: without `p a`, p := False.
theorem Iff.subst_h4 : ¬ drop% Iff.subst 4 := fun h => @h True True (fun _ => False) Iff.rfl

-- `noConfusion_of_Nat`: without `a = b`, f := id on Nat, a := 0, b := 1.
theorem noConfusion_of_Nat_h4 : ¬ drop1% noConfusion_of_Nat 4 := fun h => @h Nat id 0 1

/-! ## Decidable, ite, dite -/

-- `toBoolUsing_eq_true`: p := False.
theorem toBoolUsing_eq_true_h2 : ¬ drop% toBoolUsing_eq_true 2 :=
  fun h => absurd (@h False instDecidableFalse) (by decide)

-- `of_toBoolUsing_eq_true`: p := False.
theorem of_toBoolUsing_eq_true_h2 : ¬ drop% of_toBoolUsing_eq_true 2 :=
  fun h => @h False instDecidableFalse

-- `of_toBoolUsing_eq_false`: p := True.
theorem of_toBoolUsing_eq_false_h2 : ¬ drop% of_toBoolUsing_eq_false 2 :=
  fun h => @h True instDecidableTrue trivial

-- `if_pos`: c := False.
theorem if_pos_h2 : ¬ drop1% if_pos 2 :=
  fun h => absurd (@h False instDecidableFalse Bool true false) (by decide)

-- `if_neg`: c := True.
theorem if_neg_h2 : ¬ drop1% if_neg 2 :=
  fun h => absurd (@h True instDecidableTrue Bool true false) (by decide)

-- `dite_eq_left`: dependent `hc : c`; c := False.
theorem dite_eq_left_h2 : ¬ indep0% dite_eq_left 2 :=
  fun h => @h False instDecidableFalse True (fun _ => trivial) (fun _ => trivial)

-- `dif_pos`: dependent `hc : c`; c := False.
theorem dif_pos_h2 : ¬ indep0% dif_pos 2 :=
  fun h => @h False instDecidableFalse True (fun _ => trivial) (fun _ => trivial)

-- `dite_eq_right`: dependent `hnc : ¬c`; c := True.
theorem dite_eq_right_h2 : ¬ indep0% dite_eq_right 2 :=
  fun h => @h True instDecidableTrue True (fun _ => trivial) (fun _ => trivial) trivial

-- `dif_neg`: dependent `hnc : ¬c`; c := True.
theorem dif_neg_h2 : ¬ indep0% dif_neg 2 :=
  fun h => @h True instDecidableTrue True (fun _ => trivial) (fun _ => trivial) trivial

/-! ## Subsingleton -/

-- `instSubsingletonProd`: Bool × Unit is not a subsingleton.
theorem instSubsingletonProd_h2 : ¬ drop0% instSubsingletonProd 2 :=
  fun h => absurd (congrArg Prod.fst (@Subsingleton.elim _ (@h Bool Unit inferInstance) (true, ()) (false, ())))
    (by decide)

-- `instSubsingletonProd`: Unit × Bool is not a subsingleton.
theorem instSubsingletonProd_h3 : ¬ drop0% instSubsingletonProd 3 :=
  fun h => absurd (congrArg Prod.snd (@Subsingleton.elim _ (@h Unit Bool inferInstance) ((), true) ((), false)))
    (by decide)

-- `recSubsingleton`: p := True, the true branch is Bool.
theorem recSubsingleton_h4 : ¬ drop1% recSubsingleton 4 :=
  fun h => absurd (@Subsingleton.elim Bool
    (@h True instDecidableTrue (fun _ => Bool) (fun _ => Unit) (fun _ => inferInstance)) true false) (by decide)

-- `recSubsingleton`: p := False, the false branch is Bool.
theorem recSubsingleton_h5 : ¬ drop1% recSubsingleton 5 :=
  fun h => absurd (@Subsingleton.elim Bool
    (@h False instDecidableFalse (fun _ => Unit) (fun _ => Bool) (fun _ => inferInstance)) true false) (by decide)

-- `Pi.instSubsingleton`: Unit → Bool is not a subsingleton.
theorem Pi.instSubsingleton_h2 : ¬ drop1% Pi.instSubsingleton 2 :=
  fun h => absurd (congrFun (@Subsingleton.elim _ (@h Unit (fun _ => Bool)) (fun _ => true) (fun _ => false)) ())
    (by decide)

/-! ## Relations, Setoid -/

-- `Equivalence.refl`: the empty relation is not reflexive.
theorem Equivalence.refl_h2 : ¬ drop0% Equivalence.refl 2 :=
  fun h => @h True (fun _ _ => False) trivial

-- `Equivalence.symm`: rLt is not symmetric.
theorem Equivalence.symm_h2 : ¬ drop1% Equivalence.symm 2 :=
  fun h => absurd (@h Bool rLt false true (by decide)) (by decide)

-- `Equivalence.symm`: without `r x y`, Eq on Bool, x := true, y := false.
theorem Equivalence.symm_h5 : ¬ drop1% Equivalence.symm 5 :=
  fun h => absurd (@h Bool Eq (eqEquiv Bool) true false) (by decide)

-- `Equivalence.trans`: rNe is not transitive.
theorem Equivalence.trans_h2 : ¬ drop1% Equivalence.trans 2 :=
  fun h => absurd (@h Bool rNe true false true (by decide) (by decide)) (by decide)

-- `Equivalence.trans`: without `r x y`, Eq on Bool, x := true, y z := false.
theorem Equivalence.trans_h6 : ¬ drop1% Equivalence.trans 6 :=
  fun h => absurd (@h Bool Eq (eqEquiv Bool) true false false rfl) (by decide)

-- `Equivalence.trans`: without `r y z`, Eq on Bool, x y := true, z := false.
theorem Equivalence.trans_h7 : ¬ drop1% Equivalence.trans 7 :=
  fun h => absurd (@h Bool Eq (eqEquiv Bool) true true false rfl) (by decide)

-- `Relation.TransGen.trans`: without `TransGen r a b`, rLt, a := true (no successor), b := false, c := true.
theorem Relation.TransGen.trans_h5 : ¬ drop1% Relation.TransGen.trans 5 := fun h => by
  obtain ⟨_, e, _⟩ := transGen_head (@h Bool rLt true false true (.single (by decide)))
  exact Bool.noConfusion e

-- `Relation.TransGen.trans`: without `TransGen r b c`, rLt, a := false, b := true, c := false (no predecessor).
theorem Relation.TransGen.trans_h6 : ¬ drop1% Relation.TransGen.trans 6 := fun h => by
  obtain ⟨_, _, e⟩ := transGen_last (@h Bool rLt false true false (.single (by decide)))
  exact Bool.noConfusion e

-- `Subtype.ext`: two different elements of a subtype of Bool.
theorem Subtype.ext_h4 : ¬ drop1% Subtype.ext 4 :=
  fun h => absurd (congrArg Subtype.val (@h Bool (fun _ => True) ⟨true, trivial⟩ ⟨false, trivial⟩)) (by decide)

-- `Subtype.eq`: two different elements of a subtype of Bool.
theorem Subtype.eq_h4 : ¬ drop1% Subtype.eq 4 :=
  fun h => absurd (congrArg Subtype.val (@h Bool (fun _ => True) ⟨true, trivial⟩ ⟨false, trivial⟩)) (by decide)

-- `Setoid.symm`: without `a ≈ b`, equality setoid on Bool.
theorem Setoid.symm_h4 : ¬ drop1% Setoid.symm 4 :=
  fun h => absurd (@h Bool (eqSetoid Bool) true false) (fun (e : false = true) => Bool.noConfusion e)

-- `Setoid.trans`: without `a ≈ b`, equality setoid on Bool.
theorem Setoid.trans_h5 : ¬ drop1% Setoid.trans 5 :=
  fun h => absurd (@h Bool (eqSetoid Bool) true false false (show false = false from rfl))
    (fun (e : true = false) => Bool.noConfusion e)

-- `Setoid.trans`: without `b ≈ c`, equality setoid on Bool.
theorem Setoid.trans_h6 : ¬ drop1% Setoid.trans 6 :=
  fun h => absurd (@h Bool (eqSetoid Bool) true true false (show true = true from rfl))
    (fun (e : true = false) => Bool.noConfusion e)

-- `Std.Symm.symm`: without `r a b`, the empty relation (vacuously symmetric).
theorem Std.Symm.symm_h5 : ¬ drop0% Std.Symm.symm 5 :=
  fun h => @h True (fun _ _ => False) ⟨fun _ _ x => x⟩ trivial trivial

-- `Std.Trichotomous.trichotomous`: without `¬r a b`, rLt with a := false, b := true.
theorem Std.Trichotomous.trichotomous_h5 : ¬ drop1% Std.Trichotomous.trichotomous 5 :=
  fun h => absurd (@h Bool rLt rLt_trich false true (by decide)) (by decide)

-- `Std.Trichotomous.trichotomous`: without `¬r b a`, rLt with a := true, b := false.
theorem Std.Trichotomous.trichotomous_h6 : ¬ drop1% Std.Trichotomous.trichotomous 6 :=
  fun h => absurd (@h Bool rLt rLt_trich true false (by decide)) (by decide)

/-! ## Identity classes -/

-- `Std.LawfulLeftIdentity.toLeftIdentity`: removable, the marker class LeftIdentity has no fields.
theorem Std.LawfulLeftIdentity.toLeftIdentity_h4 : drop% Std.LawfulLeftIdentity.toLeftIdentity 4 := ⟨⟩

-- `Std.LawfulRightIdentity.toRightIdentity`: removable, the marker class RightIdentity has no fields.
theorem Std.LawfulRightIdentity.toRightIdentity_h4 : drop% Std.LawfulRightIdentity.toRightIdentity 4 := ⟨⟩

-- `Std.Identity.toLeftIdentity`: removable, the marker class LeftIdentity has no fields.
theorem Std.Identity.toLeftIdentity_h3 : drop% Std.Identity.toLeftIdentity 3 := ⟨⟩

-- `Std.LawfulIdentity.toIdentity`: removable, Identity only extends the field-free marker classes.
theorem Std.LawfulIdentity.toIdentity_h3 : drop% Std.LawfulIdentity.toIdentity 3 :=
  fun {_ op o} => have : Std.LeftIdentity op o := ⟨⟩; have : Std.RightIdentity op o := ⟨⟩; ⟨⟩

-- `Std.LawfulIdentity.toLawfulLeftIdentity`: the left projection on Bool has no left identity.
theorem Std.LawfulIdentity.toLawfulLeftIdentity_h3 : ¬ drop1% Std.LawfulIdentity.toLawfulLeftIdentity 3 :=
  fun h => absurd ((@h Bool (fun a _ => a) true).left_id false) (by decide)

-- `Std.LawfulIdentity.toLawfulRightIdentity`: the right projection on Bool has no right identity.
theorem Std.LawfulIdentity.toLawfulRightIdentity_h3 : ¬ drop1% Std.LawfulIdentity.toLawfulRightIdentity 3 :=
  fun h => absurd ((@h Bool (fun _ b => b) true).right_id false) (by decide)

-- `Std.LawfulCommIdentity.toLawfulIdentity`: dependent `hc : Commutative op`; the left projection on Bool.
theorem Std.LawfulCommIdentity.toLawfulIdentity_h3 : ¬ indep1% Std.LawfulCommIdentity.toLawfulIdentity 3 :=
  fun h => absurd ((@h Bool (fun a _ => a) true).comm true false) (by decide)

-- `Std.LawfulCommIdentity.toLawfulIdentity`: without the instance, `||` with o := true is commutative but true is no identity.
theorem Std.LawfulCommIdentity.toLawfulIdentity_h4 : ¬ drop1% Std.LawfulCommIdentity.toLawfulIdentity 4 :=
  fun h => absurd ((@h Bool (· || ·) true ⟨Bool.or_comm⟩).left_id false) (by decide)

/-! ## Quotients -/

-- `Quot.liftBeta`: dependent `c` (respect of r); the total relation on Bool with f := id.
theorem Quot.liftBeta_h4 : ¬ indep1% Quot.liftBeta 4 :=
  fun h => absurd (@h Bool (fun _ _ => True) Bool id true true false trivial) (by decide)

-- `Quot.indBeta`: dependent `p`; motive := False.
theorem Quot.indBeta_h3 : ¬ indep0% Quot.indBeta 3 :=
  fun h => @h True (fun _ _ => True) (fun _ => False) trivial trivial

-- `Quot.inductionOn`: motive := False.
theorem Quot.inductionOn_h4 : ¬ drop0% Quot.inductionOn 4 :=
  fun h => @h True (fun _ _ => True) (fun _ => False) (Quot.mk _ trivial)

-- `Quot.indepCoherent`: without coherence, the total relation on Bool with f := id into the constant family Bool.
theorem Quot.indepCoherent_h4 : ¬ drop1% Quot.indepCoherent 4 :=
  fun h => absurd (congrArg (fun x : PSigma (fun _ : Quot (fun _ _ : Bool => True) => Bool) => x.2)
    (@h Bool (fun _ _ => True) (fun _ => Bool) id true false trivial)) (by decide)

-- `Quot.indepCoherent`: without `r a b`, the empty relation on Bool (classes of true and false differ).
theorem Quot.indepCoherent_h7 : ¬ drop1% Quot.indepCoherent 7 :=
  fun h => absurd (congrArg (fun x => Quot.lift (r := fun _ _ : Bool => False) id (fun _ _ p => p.elim) x.1)
    (@h Bool (fun _ _ => False) (fun _ => Unit) (fun _ => ()) (fun _ _ p => p.elim) true false)) (by decide)

-- `Quot.liftIndepPr1`: dependent coherence `h`; the total relation on Bool with f := id into the constant family Bool.
theorem Quot.liftIndepPr1_h4 : ¬ indep1% Quot.liftIndepPr1 4 :=
  fun h => absurd ((ndrec_const _ _).symm.trans
    (@h Bool (fun _ _ => True) (fun _ => Bool) id (Quot.mk _ true) true false trivial)) (by decide)

-- `Quotient.sound`: without `a ≈ b`, equality setoid on Bool.
theorem Quotient.sound_h4 : ¬ drop1% Quotient.sound 4 :=
  fun h => absurd (Quotient.exact (@h Bool (eqSetoid Bool) true false))
    (fun (e : true = false) => Bool.noConfusion e)

-- `Quotient.exact`: without the quotient equation, equality setoid on Bool.
theorem Quotient.exact_h4 : ¬ drop1% Quotient.exact 4 :=
  fun h => absurd (@h Bool (eqSetoid Bool) true false) (fun (e : true = false) => Bool.noConfusion e)

-- `Quotient.ind`: motive := False.
theorem Quotient.ind_h3 : ¬ drop0% Quotient.ind 3 :=
  fun h => @h True (eqSetoid True) (fun _ => False) (Quotient.mk _ trivial)

-- `Quotient.inductionOn`: motive := False.
theorem Quotient.inductionOn_h4 : ¬ drop0% Quotient.inductionOn 4 :=
  fun h => @h True (eqSetoid True) (fun _ => False) (Quotient.mk _ trivial)

-- `Quotient.ind₂`: motive := False.
theorem Quotient.ind₂_h5 : ¬ drop0% Quotient.ind₂ 5 :=
  fun h => @h True True (eqSetoid True) (eqSetoid True) (fun _ _ => False)
    (Quotient.mk _ trivial) (Quotient.mk _ trivial)

-- `Quotient.inductionOn₂`: motive := False.
theorem Quotient.inductionOn₂_h7 : ¬ drop0% Quotient.inductionOn₂ 7 :=
  fun h => @h True True (eqSetoid True) (eqSetoid True) (fun _ _ => False)
    (Quotient.mk _ trivial) (Quotient.mk _ trivial)

-- `Quotient.inductionOn₃`: motive := False.
theorem Quotient.inductionOn₃_h10 : ¬ drop0% Quotient.inductionOn₃ 10 :=
  fun h => @h True True True (eqSetoid True) (eqSetoid True) (eqSetoid True) (fun _ _ _ => False)
    (Quotient.mk _ trivial) (Quotient.mk _ trivial) (Quotient.mk _ trivial)

-- `Squash.ind`: motive := False.
theorem Squash.ind_h2 : ¬ drop0% Squash.ind 2 :=
  fun h => @h True (fun _ => False) (Squash.mk trivial)

end CoreAHand
