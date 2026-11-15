import Lean

/-!
Hand pass over cluster `IOrdBasic` (hand13): the 117 unresolved hypotheses of
`Init.Internal.Order.Basic` (the `Lean.Order` domain theory behind `partial_fixpoint`: `PartialOrder`
fields, sups, `CCPO`/`CompleteLattice`, `monotone`/`admissible`, `lfp`/`fix`/`iterates`, pointwise,
`PProd`/`Prod`/`FlatOrder` orders, `MonoBind` and its monad-transformer instances, the
(reverse) implication orders, and `Example.find_spec`). For hypothesis `hᵢ` of `T` each declaration
proves `¬T'` (`dropU% T i [levels]`) or, for the 15 dependent ones, `¬ ∀ indep, Hᵢ`
(`indepU% T i [levels]`), with the universes fixed as listed (mostly `1`, so that `Sort u` binders
can be instantiated with a `Type`).

117 necessary, 0 removable, 0 independent.

Models (reusable):
* `ImplicationOrder` (library `PartialOrder`/`CompleteLattice`, plus `ccpoImp : CCPO`): the
  two-point order `False ⊑ True`; total (`imp_chain`). `fun x => ¬ x` is not monotone
  (`not_mono_not`), the identity is not monotone into `ReverseImplicationOrder` (`id_not_rmono`);
  `lfp Not` and `lfp (fun _ => True)` hold (`lfp_not`, `lfp_true`).
* `W := Nat → ImplicationOrder` (pointwise, `CCPO` and `CompleteLattice`): `wa`/`wb` incomparable
  (`W_not_chain`); infinite chain `wlt k` (`n < k`) with supremum `⊤` (`wlt_chain`, `wlt_csup`);
  `x = ⊥` admissible (`adm_bot`) but `Pmid ∨ (x = ⊥)` not (refutes `admissible_or`); non-monotone
  `fpre` whose `lfp` (meet of `wa`, `wb`) is not prefixed; non-monotone `fmeet` with `lfp = wa`
  and a meet `⊥` with `f ⊥ = wb` (refutes `hm` of `lfp_le_of_le_meet`); monotone `fone` with
  `lfp = ⊤`, `f ⊥ = wa`.
* `Option Bool`/`FlatOrder none` (library flat `CCPO`, `MonoBind Option`): `some true`, `some false`
  incomparable (`opt_not_chain`), and the full set has no sup (`opt_no_sup`); `fit`
  (`none ↦ some true ↦ some false`) has non-chain iterates; `gsw` (`none ↦ some (), some () ↦ none`)
  is not monotone (`opt_not_mono`).
* `not_adm`: a predicate false everywhere is not admissible (empty chain), e.g. on `Unit`.
* Broken monads: `CB α := Bool` with `bind x _ := !x` (bind antitone in the first argument, also
  through `ExceptT`/`OptionT`/`ReaderT`/`StateT`/`StateRefT'`); `WB α := Bool × α` with
  `bind x f := ((f x.2).1 && !x.1, (f x.2).2)` (makes `StateRefT'.run` antitone; `ST` lifted by
  `liftST`), and `bindR` on `WB` (antitone in the continuation).

Run with the lean4 repo's stage1 binary: `lean checks/IOrdBasicHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open Lean Meta Elab Term in
/-- `dropU% T i [l₁, …]`: `T` without its non-dependent Prop binder `i`, universes set to `l₁, …`. -/
elab "dropU% " T:ident i:num " [" ls:num,* "]" : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let ls := ls.getElems.toList.map fun l => Level.ofNat l.getNat
  unless ls.length == ci.levelParams.length do throwError "{n} has universes {ci.levelParams}"
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams ls) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indepU% T i [l₁, …]`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T`, universes set to `l₁, …`. -/
elab "indepU% " T:ident i:num " [" ls:num,* "]" : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let ls := ls.getElems.toList.map fun l => Level.ofNat l.getNat
  unless ls.length == ci.levelParams.length do throwError "{n} has universes {ci.levelParams}"
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams ls) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

open Lean Order

namespace IOrdBasicHand

/-! ## Models -/

instance ccpoImp : CCPO ImplicationOrder where
  toPartialOrder := ImplicationOrder.instOrder
  has_csup {c} _ := CompleteLattice.has_sup c

abbrev W := Nat → ImplicationOrder

def wa : W := fun n => n = 0
def wb : W := fun n => n = 1
def wbot : W := fun _ => False
def wtop : W := fun _ => True

theorem W_ab : ¬ (wa ⊑ wb ∨ wb ⊑ wa) := by
  rintro (h | h)
  · exact absurd (show (0:Nat) = 1 from h 0 rfl) (by decide)
  · exact absurd (show (1:Nat) = 0 from h 1 rfl) (by decide)

theorem W_not_chain {c : W → Prop} (ha : c wa) (hb : c wb) : ¬ chain c :=
  fun h => W_ab (h _ _ ha hb)

theorem not_adm {α : Sort u} [CCPO α] {P : α → Prop} (hP : ∀ x, ¬ P x) : ¬ admissible P :=
  fun h => hP _ (h _ (chain_empty α) (fun _ hx => False.elim hx))

theorem imp_chain (c : ImplicationOrder → Prop) : chain c := fun x y _ _ => by
  rcases Classical.em (x : Prop) with hx | hx
  · right; exact fun _ => hx
  · left; exact fun h => (hx h).elim

theorem not_mono_not : ¬ @monotone ImplicationOrder _ ImplicationOrder _ (fun x => ¬ x) :=
  fun h => h False True (fun e => e.elim) (fun e => e) trivial

theorem id_not_rmono :
    ¬ @monotone ImplicationOrder _ ReverseImplicationOrder _ (fun x => x) :=
  fun h => h False True (fun e => False.elim e) trivial

theorem opt_le_none {α} {x : Option α} (h : x ⊑ none) : x = none := by
  change @FlatOrder.rel (Option α) none x none at h
  cases h <;> rfl

theorem opt_some_le {α} {a : α} {s : Option α} (h : some a ⊑ s) : s = some a := by
  change @FlatOrder.rel (Option α) none (some a) s at h
  cases h; rfl

theorem opt_none_le {α} (x : Option α) : (none : Option α) ⊑ x := FlatOrder.rel.bot

theorem opt_tf : ¬ ((some true : Option Bool) ⊑ some false ∨ (some false : Option Bool) ⊑ some true) := by
  rintro (h | h) <;> cases opt_some_le h

theorem opt_not_chain {c : Option Bool → Prop} (ht : c (some true)) (hf : c (some false)) : ¬ chain c :=
  fun h => opt_tf (h _ _ ht hf)

theorem opt_no_sup {c : Option Bool → Prop} (ht : c (some true)) (hf : c (some false)) (s : Option Bool) :
    ¬ is_sup c s := fun h => by
  have h1 := opt_some_le ((h s).mp PartialOrder.rel_refl _ ht)
  have h2 := opt_some_le ((h s).mp PartialOrder.rel_refl _ hf)
  rw [h1] at h2; cases h2

theorem opt_not_mono {γ : Sort u} [PartialOrder γ] {β} {F : γ → Option β} (x y : γ) (hxy : x ⊑ y)
    (b : β) (h1 : F x = some b) (h2 : F y = none) : ¬ monotone F := fun hm => by
  have := hm x y hxy
  rw [h1, h2] at this
  cases opt_le_none this

theorem csup_empty_opt {α} : CCPO.csup (chain_empty (Option α)) = none :=
  opt_le_none (csup_le (x := none) (chain_empty _) (fun _ h => False.elim h))

/-- Constant `Bool` functor whose bind negates: bind is antitone in its first argument. -/
structure CB (α : Type) where
  b : Bool

instance : Monad CB where
  pure _ := ⟨true⟩
  bind x _ := ⟨!x.b⟩

instance (α) : PartialOrder (CB α) where
  rel x y := x.b = true → y.b = true
  rel_refl := id
  rel_trans h₁ h₂ := fun h => h₂ (h₁ h)
  rel_antisymm := by
    intro ⟨x⟩ ⟨y⟩ h₁ h₂
    cases x <;> cases y <;> simp_all

/-- Writer-like `Bool × α` whose bind returns `flag (f a) && !flag x`. -/
structure WB (α : Type) where
  flag : Bool
  val : α

instance : Monad WB where
  pure a := ⟨true, a⟩
  bind x f := ⟨(f x.val).flag && !x.flag, (f x.val).val⟩

instance (α) : PartialOrder (WB α) where
  rel x y := (x.flag = true → y.flag = true) ∧ x.val = y.val
  rel_refl := ⟨id, rfl⟩
  rel_trans h₁ h₂ := ⟨fun h => h₂.1 (h₁.1 h), h₁.2.trans h₂.2⟩
  rel_antisymm := by
    intro ⟨x, a⟩ ⟨y, b⟩ h₁ h₂
    obtain ⟨h₁, rfl⟩ := h₁
    cases x <;> cases y <;> simp_all

@[instance_reducible] noncomputable def liftST {m : Type → Type} (ret : ∀ {α}, α → m α) : MonadLiftT (ST Unit) m :=
  ⟨fun x => ret (x (Classical.choice inferInstance)).val⟩

/-! ## PartialOrder fields, sups -/

-- `Lean.Order.PartialOrder.rel_trans`
theorem rel_trans_5 : ¬ dropU% Lean.Order.PartialOrder.rel_trans 5 [1] :=
  fun h => @h ImplicationOrder _ True False False id trivial

-- `Lean.Order.PartialOrder.rel_trans`
theorem rel_trans_6 : ¬ dropU% Lean.Order.PartialOrder.rel_trans 6 [1] :=
  fun h => @h ImplicationOrder _ True True False id trivial

-- `Lean.Order.PartialOrder.rel_antisymm`
theorem rel_antisymm_4 : ¬ dropU% Lean.Order.PartialOrder.rel_antisymm 4 [1] :=
  fun h => cast (@h ImplicationOrder _ True False (fun _ => trivial)) trivial

-- `Lean.Order.PartialOrder.rel_antisymm`
theorem rel_antisymm_5 : ¬ dropU% Lean.Order.PartialOrder.rel_antisymm 5 [1] :=
  fun h => cast (@h ImplicationOrder _ False True (fun _ => trivial)).symm trivial

-- `Lean.Order.PartialOrder.rel_of_eq`
theorem rel_of_eq_4 : ¬ dropU% Lean.Order.PartialOrder.rel_of_eq 4 [1] :=
  fun h => @h ImplicationOrder _ True False trivial

-- `Lean.Order.is_sup_unique`
theorem is_sup_unique_5 : ¬ dropU% Lean.Order.is_sup_unique 5 [1] :=
  fun h => cast (@h ImplicationOrder _ (fun _ => False) True False
    (fun _ => ⟨fun _ _ e => e.elim, fun _ e => e.elim⟩)) trivial

-- `Lean.Order.is_sup_unique`
theorem is_sup_unique_6 : ¬ dropU% Lean.Order.is_sup_unique 6 [1] :=
  fun h => cast (@h ImplicationOrder _ (fun _ => False) False True
    (fun _ => ⟨fun _ _ e => e.elim, fun _ e => e.elim⟩)).symm trivial

-- `Lean.Order.CCPO.has_csup`
theorem has_csup_3 : ¬ dropU% Lean.Order.CCPO.has_csup 3 [1] := fun h => by
  obtain ⟨s, hs⟩ := @h (Option Bool) _ (fun _ => True)
  exact opt_no_sup trivial trivial s hs

-- `Lean.Order.CCPO.csup_spec`
theorem csup_spec_3 : ¬ indepU% Lean.Order.CCPO.csup_spec 3 [1] :=
  fun h => W_not_chain trivial trivial (@h W _ (fun _ => True))

-- `Lean.Order.csup_le`
theorem csup_le_4 : ¬ indepU% Lean.Order.csup_le 4 [1] :=
  fun h => W_not_chain (Or.inl rfl) (Or.inr rfl)
    (@h W _ wtop (fun y => y = wa ∨ y = wb) (fun _ _ _ _ => trivial))

-- `Lean.Order.csup_le`
theorem csup_le_5 : ¬ dropU% Lean.Order.csup_le 5 [1] := fun h =>
  @h ImplicationOrder _ False (fun y => y) (imp_chain _)
    (le_csup (c := fun y : ImplicationOrder => (y : Prop)) (imp_chain _) (y := True) trivial trivial)

-- `Lean.Order.le_csup`
theorem le_csup_3 : ¬ indepU% Lean.Order.le_csup 3 [1] :=
  fun h => W_not_chain trivial trivial (@h W _ (fun _ => True) wa trivial)

-- `Lean.Order.le_csup`
theorem le_csup_5 : ¬ dropU% Lean.Order.le_csup 5 [1] := fun h =>
  csup_le (α := ImplicationOrder) (x := False) (imp_chain (fun _ => False)) (fun _ e => e.elim)
    (@h ImplicationOrder _ (fun _ => False) (imp_chain _) True trivial)

-- `Lean.Order.sup_le`
theorem sup_le_4 : ¬ dropU% Lean.Order.sup_le 4 [1] := fun h =>
  @h ImplicationOrder _ False (fun y => y)
    (le_sup (c := fun y : ImplicationOrder => (y : Prop)) (y := True) trivial trivial)

-- `Lean.Order.le_sup`
theorem le_sup_4 : ¬ dropU% Lean.Order.le_sup 4 [1] := fun h =>
  sup_le (α := ImplicationOrder) (x := False) (fun _ => False) (fun _ e => e.elim)
    (@h ImplicationOrder _ (fun _ => False) True trivial)

-- `Lean.Order.le_inf`
theorem le_inf_4 : ¬ dropU% Lean.Order.le_inf 4 [1] := fun h =>
  inf_le (c := fun y : ImplicationOrder => ¬ (y : Prop)) (y := False) (fun e => e)
    (@h ImplicationOrder _ True (fun y => ¬ (y : Prop)) trivial)

-- `Lean.Order.inf_le`
theorem inf_le_4 : ¬ dropU% Lean.Order.inf_le 4 [1] := fun h =>
  @h ImplicationOrder _ (fun _ => False) False
    (le_inf (α := ImplicationOrder) (x := True) (c := fun _ => False) (fun _ e => e.elim) trivial)

/-! ## monotone, admissible -/

-- `Lean.Order.monotone_compose`
theorem monotone_compose_8 : ¬ dropU% Lean.Order.monotone_compose 8 [1, 1, 1] :=
  fun h => not_mono_not (@h ImplicationOrder _ ImplicationOrder _ ImplicationOrder _
    (fun x => ¬ x) (fun x => x) monotone_id)

-- `Lean.Order.monotone_compose`
theorem monotone_compose_9 : ¬ dropU% Lean.Order.monotone_compose 9 [1, 1, 1] :=
  fun h => not_mono_not (@h ImplicationOrder _ ImplicationOrder _ ImplicationOrder _
    (fun x => x) (fun x => ¬ x) monotone_id)

-- `Lean.Order.admissible_and`
theorem admissible_and_4 : ¬ dropU% Lean.Order.admissible_and 4 [1] :=
  fun h => not_adm (fun _ h => h.1) (@h Unit _ (fun _ => False) (fun _ => True) admissible_const_true)

-- `Lean.Order.admissible_and`
theorem admissible_and_5 : ¬ dropU% Lean.Order.admissible_and 5 [1] :=
  fun h => not_adm (fun _ h => h.2) (@h Unit _ (fun _ => True) (fun _ => False) admissible_const_true)

-- `Lean.Order.chain_conj`
theorem chain_conj_4 : ¬ dropU% Lean.Order.chain_conj 4 [1] :=
  fun h => W_not_chain (c := fun x => True ∧ True) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
    (@h W _ (fun _ => True) (fun _ => True))

-- `Lean.Order.csup_conj`
theorem csup_conj_4 : ¬ indepU% Lean.Order.csup_conj 4 [1] :=
  fun h => W_not_chain trivial trivial
    (@h W _ (fun _ => True) (fun _ => True) (fun x _ => ⟨x, trivial, PartialOrder.rel_refl, trivial⟩))

-- `Lean.Order.csup_conj`
theorem csup_conj_5 : ¬ dropU% Lean.Order.csup_conj 5 [1] := fun h => by
  have e := @h ImplicationOrder _ (fun _ => True) (fun y => ¬ (y : Prop)) (imp_chain _)
  have h1 : (CCPO.csup (imp_chain (fun _ => True)) : Prop) :=
    le_csup (α := ImplicationOrder) (imp_chain (fun _ => True)) (y := True) trivial trivial
  rw [e] at h1
  exact csup_le (α := ImplicationOrder) (x := False) (chain_conj _ _ (imp_chain _))
    (fun (y : ImplicationOrder) (hy : True ∧ ¬ (y : Prop)) (hyy : (y : Prop)) => hy.2 hyy) h1

/-- `x ↦ "x n holds for n < k"`, an infinite chain in `W` with supremum `wtop`. -/
def wlt (k : Nat) : W := fun n => n < k

theorem wlt_chain : chain (fun x : W => ∃ k, x = wlt k) := by
  rintro _ _ ⟨k, rfl⟩ ⟨k', rfl⟩
  rcases Nat.le_total k k' with h | h
  · left; intro n hn; exact Nat.lt_of_lt_of_le hn h
  · right; intro n hn; exact Nat.lt_of_lt_of_le hn h

theorem wlt_csup (n : Nat) : (CCPO.csup wlt_chain : W) n :=
  le_csup wlt_chain (y := wlt (n+1)) ⟨n+1, rfl⟩ n (Nat.lt_succ_self n)

/-- `x = ⊥` is admissible in `W`. -/
theorem adm_bot : admissible (fun x : W => ∀ n, ¬ x n) := fun c hc h n hn =>
  csup_le (x := wbot) hc (fun y hy m hm => h y hy m hm) n hn

/-- `P` with `P ∨ (x = ⊥)` true on the chain `wlt` but false at its supremum `wtop`. -/
def Pmid (x : W) : Prop := (∃ n, x n) ∧ ∃ n, ¬ x n

theorem Pmid_or_bot : ∀ x, (∃ k, x = wlt k) → (Pmid x ∨ ∀ n, ¬ x n) := by
  rintro _ ⟨k, rfl⟩
  cases k with
  | zero => right; intro n hn; exact Nat.not_lt_zero _ hn
  | succ k => left; exact ⟨⟨0, Nat.succ_pos k⟩, ⟨k+1, Nat.lt_irrefl _⟩⟩

-- `Lean.Order.admissible_or`
theorem admissible_or_4 : ¬ dropU% Lean.Order.admissible_or 4 [1] := fun h => by
  have := @h W _ Pmid (fun x => ∀ n, ¬ x n) adm_bot _ wlt_chain Pmid_or_bot
  rcases this with ⟨_, n, hn⟩ | hb
  · exact hn (wlt_csup n)
  · exact hb 0 (wlt_csup 0)

-- `Lean.Order.admissible_or`
theorem admissible_or_5 : ¬ dropU% Lean.Order.admissible_or 5 [1] := fun h => by
  have := @h W _ (fun x => ∀ n, ¬ x n) Pmid adm_bot _ wlt_chain (fun x hx => (Pmid_or_bot x hx).symm)
  rcases this with hb | ⟨_, n, hn⟩
  · exact hb 0 (wlt_csup 0)
  · exact hn (wlt_csup n)

-- `Lean.Order.admissible_pi`
theorem admissible_pi_4 : ¬ dropU% Lean.Order.admissible_pi 4 [1, 1] :=
  fun h => not_adm (fun _ h => h ()) (@h Unit _ Unit (fun _ _ => False))

/-! ## lfp -/

/-- On `W`: `x ↦ x` unless `x = ⊥`, `⊥ ↦ ⊤`; prefixed points are the `x ≠ ⊥`, with meet `⊥`. -/
def fpre (x : W) : W := fun n => x n ∨ ¬ ∃ m, x m

theorem fpre_lfp_a : lfp fpre ⊑ wa := inf_le (show fpre wa ⊑ wa from
  fun n hn => hn.resolve_right (fun h => h ⟨0, rfl⟩))

theorem fpre_lfp_b : lfp fpre ⊑ wb := inf_le (show fpre wb ⊑ wb from
  fun n hn => hn.resolve_right (fun h => h ⟨1, rfl⟩))

-- `Lean.Order.lfp_prefixed`
theorem lfp_prefixed_3 : ¬ dropU% Lean.Order.lfp_prefixed 3 [1] := fun h => by
  have h0 : lfp fpre 0 := @h W _ fpre 0 (Or.inr (fun ⟨m, hm⟩ => by
    have h1 : m = 0 := fpre_lfp_a m hm
    have h2 : m = 1 := fpre_lfp_b m hm
    omega))
  exact absurd (show (0:Nat) = 1 from fpre_lfp_b 0 h0) (by decide)

theorem lfp_not : (lfp (fun x : ImplicationOrder => ¬ x) : Prop) := by
  have : @PartialOrder.rel ImplicationOrder _ True (lfp (fun x : ImplicationOrder => ¬ x)) :=
    le_inf (fun y hy _ => Classical.byContradiction fun hn => hy hn |> hn)
  exact this trivial

theorem lfp_true : (lfp (fun _ : ImplicationOrder => True) : Prop) := by
  have : @PartialOrder.rel ImplicationOrder _ True (lfp (fun _ : ImplicationOrder => True)) :=
    le_inf (fun y hy => hy)
  exact this trivial

-- `Lean.Order.lfp_postfixed`
theorem lfp_postfixed_3 : ¬ dropU% Lean.Order.lfp_postfixed 3 [1] :=
  fun h => @h ImplicationOrder _ (fun x => ¬ x) lfp_not lfp_not

-- `Lean.Order.lfp_fix`
theorem lfp_fix_3 : ¬ dropU% Lean.Order.lfp_fix 3 [1] :=
  fun h => cast (@h ImplicationOrder _ (fun x => ¬ x)) lfp_not lfp_not

-- `Lean.Order.lfp_monotone_fix`
theorem lfp_monotone_fix_3 : ¬ indepU% Lean.Order.lfp_monotone_fix 3 [1] :=
  fun h => not_mono_not (@h ImplicationOrder _ (fun x => ¬ x))

-- `Lean.Order.lfp_le_of_le`
theorem lfp_le_of_le_4 : ¬ dropU% Lean.Order.lfp_le_of_le 4 [1] :=
  fun h => @h ImplicationOrder _ False (fun _ => True) lfp_true

-- `Lean.Order.lfp_le_of_le_monotone`
theorem lfp_le_of_le_monotone_3 : ¬ indepU% Lean.Order.lfp_le_of_le_monotone 3 [1] :=
  fun h => not_mono_not (@h ImplicationOrder _ (fun x => ¬ x) True (fun _ => trivial))

-- `Lean.Order.lfp_le_of_le_monotone`
theorem lfp_le_of_le_monotone_5 : ¬ dropU% Lean.Order.lfp_le_of_le_monotone 5 [1] :=
  fun h => @h ImplicationOrder _ (fun _ => True) (monotone_const _) False lfp_true

/-- On `W`, non-monotone: `⊥ ↦ wb`, `wa ↦ wa`, everything else `↦ ⊤`; its `lfp` is `wa`. -/
noncomputable def fmeet (y : W) : W :=
  open Classical in if y = wbot then wb else if y = wa then wa else wtop

theorem wa_ne_bot : wa ≠ wbot := fun h => cast (congrFun h 0) (rfl : (0:Nat) = 0)

theorem fmeet_lfp_le : lfp fmeet ⊑ wa := inf_le (show fmeet wa ⊑ wa by
  simp only [fmeet, if_neg wa_ne_bot, if_pos rfl]; exact PartialOrder.rel_refl)

theorem fmeet_le_lfp : wa ⊑ lfp fmeet := le_inf (fun y hy => by
  by_cases h1 : y = wbot
  · simp only [fmeet, if_pos h1] at hy
    subst h1; exact absurd (hy 1 rfl) id
  · by_cases h2 : y = wa
    · subst h2; exact PartialOrder.rel_refl
    · simp only [fmeet, if_neg h1, if_neg h2] at hy
      exact fun n _ => hy n trivial)

-- `Lean.Order.lfp_le_of_le_meet`
theorem lfp_le_of_le_meet_3 : ¬ dropU% Lean.Order.lfp_le_of_le_meet 3 [1] := fun h => by
  have hm : is_meet wb (lfp fmeet) wbot :=
    ⟨fun _ e => False.elim e, fun _ e => False.elim e, fun z hzb hzl n hz => by
      have h1 : n = 1 := hzb n hz
      have h2 : n = 0 := fmeet_lfp_le n (hzl n hz)
      omega⟩
  have hf : fmeet wbot ⊑ wb := by
    simp only [fmeet, if_pos rfl]; exact PartialOrder.rel_refl
  have := @h W _ fmeet wb wbot hm hf
  exact absurd (show (0:Nat) = 1 from this 0 (fmeet_le_lfp 0 rfl)) (by decide)

/-- On `W`, monotone: `x ↦ (n = 0 ∨ x 0)`; its `lfp` is `⊤` but `f ⊥ = wa`. -/
def fone (x : W) : W := fun n => n = 0 ∨ x 0

theorem fone_mono : monotone fone := fun x y h n hn => hn.imp id (h 0)

theorem fone_lfp (n : Nat) : (lfp fone : W) n :=
  le_inf (x := wtop) (fun y hy m _ => hy m (Or.inr (hy 0 (Or.inl rfl)))) n trivial

-- `Lean.Order.lfp_le_of_le_meet`
theorem lfp_le_of_le_meet_6 : ¬ dropU% Lean.Order.lfp_le_of_le_meet 6 [1] := fun h => by
  have := @h W _ fone fone_mono wa wbot (fun n hn => hn.resolve_right id)
  exact absurd (show (1:Nat) = 0 from this 1 (fone_lfp 1)) (by decide)

-- `Lean.Order.lfp_le_of_le_meet`
theorem lfp_le_of_le_meet_7 : ¬ dropU% Lean.Order.lfp_le_of_le_meet 7 [1] :=
  fun h => @h ImplicationOrder _ (fun _ => True) (monotone_const _) False False
    ⟨id, fun e => False.elim e, fun _ hz _ => hz⟩ lfp_true

-- `Lean.Order.lfp_le_of_le_meet_monotone`
theorem lfp_le_of_le_meet_monotone_3 : ¬ indepU% Lean.Order.lfp_le_of_le_meet_monotone 3 [1] :=
  fun h => not_mono_not (@h ImplicationOrder _ (fun x => ¬ x) True True (fun _ => trivial))

-- `Lean.Order.lfp_le_of_le_meet_monotone`
theorem lfp_le_of_le_meet_monotone_6 : ¬ dropU% Lean.Order.lfp_le_of_le_meet_monotone 6 [1] := fun h => by
  have := @h W _ fone fone_mono wa wbot (fun n hn => hn.resolve_right id)
  exact absurd (show (1:Nat) = 0 from this 1 (fone_lfp 1)) (by decide)

-- `Lean.Order.lfp_le_of_le_meet_monotone`
theorem lfp_le_of_le_meet_monotone_7 : ¬ dropU% Lean.Order.lfp_le_of_le_meet_monotone 7 [1] :=
  fun h => @h ImplicationOrder _ (fun _ => True) (monotone_const _) False False
    ⟨id, fun e => False.elim e, fun _ hz _ => hz⟩ lfp_true

/-! ## fix, iterates -/

/-- On `Option Bool`: `none ↦ some true ↦ some false ↦ some false` (not monotone). -/
def fit : Option Bool → Option Bool
  | none => some true
  | some _ => some false

theorem fit_iter_t : iterates fit (some true) := by
  have h0 : iterates fit (CCPO.csup (chain_empty (Option Bool))) :=
    iterates.sup (chain_empty _) (fun _ h => False.elim h)
  rw [csup_empty_opt] at h0
  exact iterates.step h0

theorem fit_iter_f : iterates fit (some false) := iterates.step fit_iter_t

-- `Lean.Order.chain_iterates`
theorem chain_iterates_3 : ¬ dropU% Lean.Order.chain_iterates 3 [1] :=
  fun h => opt_not_chain fit_iter_t fit_iter_f (@h (Option Bool) _ fit)

-- `Lean.Order.rel_f_of_iterates`
theorem rel_f_of_iterates_3 : ¬ dropU% Lean.Order.rel_f_of_iterates 3 [1] := fun h => by
  have := @h (Option Bool) _ fit (some true) fit_iter_t
  cases opt_some_le this

-- `Lean.Order.rel_f_of_iterates`
theorem rel_f_of_iterates_5 : ¬ dropU% Lean.Order.rel_f_of_iterates 5 [1] := fun h => by
  have := @h (Option Bool) _ (fun _ => none) (monotone_const _) (some true)
  cases opt_le_none this

-- `Lean.Order.fix_eq`
theorem fix_eq_3 : ¬ indepU% Lean.Order.fix_eq 3 [1] :=
  fun h => not_mono_not (@h ImplicationOrder _ (fun x => ¬ x))

-- `Lean.Order.fix_induct`
theorem fix_induct_3 : ¬ indepU% Lean.Order.fix_induct 3 [1] :=
  fun h => not_mono_not (@h ImplicationOrder _ (fun x => ¬ x) (fun _ => True)
    admissible_const_true (fun _ _ => trivial))

-- `Lean.Order.fix_induct`
theorem fix_induct_5 : ¬ dropU% Lean.Order.fix_induct 5 [1] :=
  fun h => @h Unit _ id monotone_id (fun _ => False) (fun _ e => e)

-- `Lean.Order.fix_induct`
theorem fix_induct_6 : ¬ dropU% Lean.Order.fix_induct 6 [1] := fun h =>
  @h (Option Bool) _ (fun _ => some true) (monotone_const _) (fun x => x = some true → False)
    (Option.admissible_eq_some False true) (fix_eq (f := fun _ : Option Bool => some true) (monotone_const _))

/-! ## Pointwise order -/

-- `Lean.Order.monotone_of_monotone_apply`
theorem monotone_of_monotone_apply_6 : ¬ dropU% Lean.Order.monotone_of_monotone_apply 6 [1, 1, 1] :=
  fun h => not_mono_not (fun x y hxy =>
    @h Unit (fun _ => ImplicationOrder) ImplicationOrder _ _ (fun x _ => ¬ x) x y hxy ())

-- `Lean.Order.monotone_apply`
theorem monotone_apply_7 : ¬ dropU% Lean.Order.monotone_apply 7 [1, 1, 1] :=
  fun h => not_mono_not (@h Unit (fun _ => ImplicationOrder) ImplicationOrder _ _ () (fun x _ => ¬ x))

-- `Lean.Order.is_meet_pi`
theorem is_meet_pi_6 : ¬ dropU% Lean.Order.is_meet_pi 6 [1, 1] :=
  fun h => (@h Unit (fun _ => ImplicationOrder) _ (fun _ => False) (fun _ => False) (fun _ => True)).1 () trivial

-- `Lean.Order.chain_apply`
theorem chain_apply_4 : ¬ dropU% Lean.Order.chain_apply 4 [1, 1] :=
  fun h => opt_not_chain ⟨fun _ => some true, trivial, rfl⟩ ⟨fun _ => some false, trivial, rfl⟩
    (@h Unit (fun _ => Option Bool) _ (fun _ => True) ())

-- `Lean.Order.fun_csup_is_sup`
theorem fun_csup_is_sup_4 : ¬ indepU% Lean.Order.fun_csup_is_sup 4 [1, 1] :=
  fun h => W_not_chain trivial trivial (@h Nat (fun _ => ImplicationOrder) _ (fun _ => True))

-- `Lean.Order.fun_csup_eq`
theorem fun_csup_eq_4 : ¬ indepU% Lean.Order.fun_csup_eq 4 [1, 1] :=
  fun h => W_not_chain trivial trivial (@h Nat (fun _ => ImplicationOrder) _ (fun _ => True))

-- `Lean.Order.admissible_apply`
theorem admissible_apply_5 : ¬ dropU% Lean.Order.admissible_apply 5 [1, 1] :=
  fun h => not_adm (fun _ e => e) (@h Unit (fun _ => Unit) _ (fun _ _ => False) ())

-- `Lean.Order.admissible_pi_apply`
theorem admissible_pi_apply_4 : ¬ dropU% Lean.Order.admissible_pi_apply 4 [1, 1] :=
  fun h => not_adm (fun _ e => e ()) (@h Unit (fun _ => Unit) _ (fun _ _ => False))

/-! ## ite, dite -/

-- `Lean.Order.monotone_ite`
theorem monotone_ite_8 : ¬ dropU% Lean.Order.monotone_ite 8 [1, 1] :=
  fun h => not_mono_not (@h ImplicationOrder ImplicationOrder _ _ True _ (fun x => ¬ x) (fun x => x) monotone_id)

-- `Lean.Order.monotone_ite`
theorem monotone_ite_9 : ¬ dropU% Lean.Order.monotone_ite 9 [1, 1] :=
  fun h => not_mono_not (@h ImplicationOrder ImplicationOrder _ _ False _ (fun x => x) (fun x => ¬ x) monotone_id)

-- `Lean.Order.monotone_dite`
theorem monotone_dite_8 : ¬ dropU% Lean.Order.monotone_dite 8 [1, 1] :=
  fun h => not_mono_not (@h ImplicationOrder ImplicationOrder _ _ True _ (fun x _ => ¬ x) (fun x _ => x)
    (monotone_of_monotone_apply _ (fun _ => monotone_id)))

-- `Lean.Order.monotone_dite`
theorem monotone_dite_9 : ¬ dropU% Lean.Order.monotone_dite 9 [1, 1] :=
  fun h => not_mono_not (@h ImplicationOrder ImplicationOrder _ _ False _ (fun x _ => x) (fun x _ => ¬ x)
    (monotone_of_monotone_apply _ (fun _ => monotone_id)))

/-! ## PProd, Prod -/

theorem meet_tt : @is_meet ImplicationOrder _ True True True := ⟨id, id, fun _ h _ => h⟩

-- `Lean.Order.is_meet_pprod`
theorem is_meet_pprod_7 : ¬ dropU% Lean.Order.is_meet_pprod 7 [1, 1] :=
  fun h => (@h ImplicationOrder ImplicationOrder _ _ ⟨False, True⟩ ⟨False, True⟩ ⟨True, True⟩ meet_tt).1.1 trivial

-- `Lean.Order.is_meet_pprod`
theorem is_meet_pprod_8 : ¬ dropU% Lean.Order.is_meet_pprod 8 [1, 1] :=
  fun h => (@h ImplicationOrder ImplicationOrder _ _ ⟨True, False⟩ ⟨True, False⟩ ⟨True, True⟩ meet_tt).1.2 trivial

-- `Lean.Order.PProd.monotone_mk`
theorem PProd_monotone_mk_8 : ¬ dropU% Lean.Order.PProd.monotone_mk 8 [1, 1, 1] :=
  fun h => not_mono_not (PProd.monotone_fst (@h ImplicationOrder ImplicationOrder ImplicationOrder _ _ _
    (fun x => ¬ x) (fun x => x) monotone_id))

-- `Lean.Order.PProd.monotone_mk`
theorem PProd_monotone_mk_9 : ¬ dropU% Lean.Order.PProd.monotone_mk 9 [1, 1, 1] :=
  fun h => not_mono_not (PProd.monotone_snd (@h ImplicationOrder ImplicationOrder ImplicationOrder _ _ _
    (fun x => x) (fun x => ¬ x) monotone_id))

-- `Lean.Order.PProd.monotone_fst`
theorem PProd_monotone_fst_7 : ¬ dropU% Lean.Order.PProd.monotone_fst 7 [1, 1, 1] :=
  fun h => not_mono_not (@h ImplicationOrder Unit ImplicationOrder _ _ _ (fun x => ⟨¬ x, ()⟩))

-- `Lean.Order.PProd.monotone_snd`
theorem PProd_monotone_snd_7 : ¬ dropU% Lean.Order.PProd.monotone_snd 7 [1, 1, 1] :=
  fun h => not_mono_not (@h Unit ImplicationOrder ImplicationOrder _ _ _ (fun x => ⟨(), ¬ x⟩))

-- `Lean.Order.PProd.chain.chain_fst`
theorem chain_fst_5 : ¬ dropU% Lean.Order.PProd.chain.chain_fst 5 [1, 1] :=
  fun h => opt_not_chain ⟨(), trivial⟩ ⟨(), trivial⟩ (@h (Option Bool) Unit _ _ (fun _ => True))

-- `Lean.Order.PProd.chain.chain_snd`
theorem chain_snd_5 : ¬ dropU% Lean.Order.PProd.chain.chain_snd 5 [1, 1] :=
  fun h => opt_not_chain ⟨(), trivial⟩ ⟨(), trivial⟩ (@h Unit (Option Bool) _ _ (fun _ => True))

theorem pprod_not_chain : ¬ chain (fun _ : ImplicationOrder ×' ImplicationOrder => True) := fun h => by
  rcases h ⟨True, False⟩ ⟨False, True⟩ trivial trivial with h | h
  · exact h.1 trivial
  · exact h.2 trivial

-- `Lean.Order.prod_csup_is_sup`
theorem prod_csup_is_sup_5 : ¬ indepU% Lean.Order.prod_csup_is_sup 5 [1, 1] :=
  fun h => pprod_not_chain (@h ImplicationOrder ImplicationOrder _ _ (fun _ => True))

-- `Lean.Order.prod_csup_eq`
theorem prod_csup_eq_5 : ¬ indepU% Lean.Order.prod_csup_eq 5 [1, 1] :=
  fun h => pprod_not_chain (@h ImplicationOrder ImplicationOrder _ _ (fun _ => True))

-- `Lean.Order.admissible_pprod_fst`
theorem admissible_pprod_fst_5 : ¬ dropU% Lean.Order.admissible_pprod_fst 5 [1, 1] :=
  fun h => not_adm (fun _ e => e) (@h Unit Unit _ _ (fun _ => False))

-- `Lean.Order.admissible_pprod_snd`
theorem admissible_pprod_snd_5 : ¬ dropU% Lean.Order.admissible_pprod_snd 5 [1, 1] :=
  fun h => not_adm (fun _ e => e) (@h Unit Unit _ _ (fun _ => False))

-- `Lean.Order.Prod.mk_le`
theorem Prod_mk_le_7 : ¬ dropU% Lean.Order.Prod.mk_le 7 [0, 0] :=
  fun h => (@h ImplicationOrder ImplicationOrder _ _ True True (False, True) id).1 trivial

-- `Lean.Order.Prod.mk_le`
theorem Prod_mk_le_8 : ¬ dropU% Lean.Order.Prod.mk_le 8 [0, 0] :=
  fun h => (@h ImplicationOrder ImplicationOrder _ _ True True (True, False) id).2 trivial

-- `Lean.Order.Prod.mk_le_snd`
theorem Prod_mk_le_snd_6 : ¬ dropU% Lean.Order.Prod.mk_le_snd 6 [0, 0] :=
  fun h => (@h ImplicationOrder ImplicationOrder _ _ True (True, False)).2 trivial

-- `Lean.Order.Prod.is_sup_of_pprod`
theorem Prod_is_sup_of_pprod_6 : ¬ dropU% Lean.Order.Prod.is_sup_of_pprod 6 [0, 0] := fun h =>
  ((@h ImplicationOrder ImplicationOrder _ _ (fun _ => False) ⟨True, True⟩ (False, False)).mpr
    (fun _ e => False.elim e)).1 trivial

/-! ## FlatOrder -/

-- `Lean.Order.flat_csup_is_sup`
theorem flat_csup_is_sup_3 : ¬ dropU% Lean.Order.flat_csup_is_sup 3 [1] :=
  fun h => opt_no_sup (c := fun _ => True) trivial trivial _ (@h (Option Bool) none (fun _ => True))

-- `Lean.Order.flat_csup_eq`
theorem flat_csup_eq_3 : ¬ indepU% Lean.Order.flat_csup_eq 3 [1] :=
  fun h => opt_not_chain (c := fun _ => True) trivial trivial (@h (Option Bool) none (fun _ => True))

-- `Lean.Order.admissible_flatOrder`
theorem admissible_flatOrder_3 : ¬ dropU% Lean.Order.admissible_flatOrder 3 [1] :=
  fun h => not_adm (fun _ e => e) (@h Unit () (fun _ => False))

/-! ## MonoBind -/

-- `Lean.Order.MonoBind.bind_mono_left`
theorem bind_mono_left_3 : ¬ dropU% Lean.Order.MonoBind.bind_mono_left 3 [0, 0] := fun h =>
  absurd (@h CB _ _ Unit Unit ⟨false⟩ ⟨true⟩ (fun _ => ⟨true⟩) (fun _ => rfl) rfl) (by decide)

-- `Lean.Order.MonoBind.bind_mono_left`
theorem bind_mono_left_9 : ¬ dropU% Lean.Order.MonoBind.bind_mono_left 9 [0, 0] := fun h => by
  have := @h Option _ _ _ Unit Unit (some ()) none some
  cases opt_le_none this

/-- `WB` with a bind that negates the continuation's flag: antitone in the continuation. -/
@[instance_reducible] def bindR : Bind WB := ⟨fun x f => ⟨!(f x.val).flag, (f x.val).val⟩⟩

-- `Lean.Order.MonoBind.bind_mono_right`
theorem bind_mono_right_3 : ¬ dropU% Lean.Order.MonoBind.bind_mono_right 3 [0, 0] := fun h => by
  have := @h WB bindR (fun _ => inferInstance) Unit Unit ⟨true, ()⟩ (fun _ => ⟨false, ()⟩) (fun _ => ⟨true, ()⟩)
    (fun _ => ⟨fun _ => rfl, rfl⟩)
  exact absurd (this.1 rfl) (by decide)

-- `Lean.Order.MonoBind.bind_mono_right`
theorem bind_mono_right_9 : ¬ dropU% Lean.Order.MonoBind.bind_mono_right 9 [0, 0] := fun h => by
  have := @h Option _ _ _ Unit Unit (some ()) some (fun _ => none)
  cases opt_le_none this

-- `Lean.Order.monotone_bind`
theorem monotone_bind_3 : ¬ dropU% Lean.Order.monotone_bind 3 [0, 0, 1] := fun h =>
  absurd (@h CB _ _ Unit Unit (CB Unit) _ id (fun _ _ => ⟨true⟩) (fun _ _ e => e) (monotone_const _)
    ⟨false⟩ ⟨true⟩ (fun _ => rfl) rfl) (by decide)

/-- `none ↦ some (), some () ↦ none`: not monotone. -/
def gsw : Option Unit → Option Unit
  | none => some ()
  | some _ => none

theorem gsw_not_mono : ¬ monotone gsw := opt_not_mono none (some ()) (opt_none_le _) () rfl rfl

-- `Lean.Order.monotone_bind`
theorem monotone_bind_10 : ¬ dropU% Lean.Order.monotone_bind 10 [0, 0, 1] :=
  fun h => opt_not_mono none (some ()) (opt_none_le _) () rfl rfl
    (@h Option _ _ _ Unit Unit (Option Unit) _ gsw (fun _ => some) (monotone_const _))

-- `Lean.Order.monotone_bind`
theorem monotone_bind_11 : ¬ dropU% Lean.Order.monotone_bind 11 [0, 0, 1] :=
  fun h => opt_not_mono none (some ()) (opt_none_le _) () rfl rfl
    (@h Option _ _ _ Unit Unit (Option Unit) _ (fun _ => some ()) (fun x _ => gsw x) (monotone_const _))

-- `Lean.Order.instMonoBindExceptT`
theorem instMonoBindExceptT_4 : ¬ dropU% Lean.Order.instMonoBindExceptT 4 [0, 0] := fun h =>
  absurd (@MonoBind.bind_mono_left _ _ _ (@h CB Unit _ _) Unit Unit (CB.mk false) (CB.mk true)
    (fun _ => CB.mk true) (fun _ => rfl) rfl) (by decide)

-- `Lean.Order.instMonoBindOptionT`
theorem instMonoBindOptionT_3 : ¬ dropU% Lean.Order.instMonoBindOptionT 3 [0, 0] := fun h =>
  absurd (@MonoBind.bind_mono_left _ _ _ (@h CB _ _) Unit Unit (CB.mk false) (CB.mk true)
    (fun _ => CB.mk true) (fun _ => rfl) rfl) (by decide)

-- `Lean.Order.instMonoBindReaderT`
theorem instMonoBindReaderT_4 : ¬ dropU% Lean.Order.instMonoBindReaderT 4 [0, 0] := fun h =>
  absurd (@MonoBind.bind_mono_left _ _ _ (@h CB Unit _ _) Unit Unit (fun _ => CB.mk false)
    (fun _ => CB.mk true) (fun _ _ => CB.mk true) (fun _ _ => rfl) () rfl) (by decide)

-- `Lean.Order.instMonoBindStateT`
theorem instMonoBindStateT_4 : ¬ dropU% Lean.Order.instMonoBindStateT 4 [0, 0] := fun h =>
  absurd (@MonoBind.bind_mono_left _ _ _ (@h CB Unit _ _) Unit Unit (fun _ => CB.mk false)
    (fun _ => CB.mk true) (fun _ _ => CB.mk true) (fun _ _ => rfl) () rfl) (by decide)

noncomputable def aRef : ST.Ref Unit Unit := Classical.choice inferInstance

-- `Lean.Order.instMonoBindStateRefT'`
theorem instMonoBindStateRefT'_5 : ¬ dropU% Lean.Order.instMonoBindStateRefT' 5 [] := fun h =>
  absurd (@MonoBind.bind_mono_left _ _ _ (@h CB Unit Unit _ _) Unit Unit (fun _ => CB.mk false)
    (fun _ => CB.mk true) (fun _ _ => CB.mk true) (fun _ _ => rfl) aRef rfl) (by decide)

-- `Lean.Order.monotone_exceptTRun`
theorem monotone_exceptTRun_8 : ¬ dropU% Lean.Order.monotone_exceptTRun 8 [1, 0, 0] :=
  fun h => opt_not_mono none (some ()) (opt_none_le _) (.ok ()) rfl rfl
    (@h (Option Unit) Option Unit Unit _ _ _ (fun x => (gsw x).map Except.ok))

-- `Lean.Order.monotone_optionTRun`
theorem monotone_optionTRun_7 : ¬ dropU% Lean.Order.monotone_optionTRun 7 [1, 0, 0] :=
  fun h => opt_not_mono none (some ()) (opt_none_le _) (some ()) rfl rfl
    (@h (Option Unit) Option Unit _ _ _ (fun x => (gsw x).map some))

-- `Lean.Order.monotone_readerTRun`
theorem monotone_readerTRun_8 : ¬ dropU% Lean.Order.monotone_readerTRun 8 [1, 0, 0] :=
  fun h => opt_not_mono none (some ()) (opt_none_le _) () rfl rfl
    (@h (Option Unit) Option Unit Unit _ _ _ (fun x _ => gsw x) ())

-- `Lean.Order.monotone_stateTRun`
theorem monotone_stateTRun_8 : ¬ dropU% Lean.Order.monotone_stateTRun 8 [1, 0, 0] :=
  fun h => opt_not_mono none (some ()) (opt_none_le _) ((), ()) rfl rfl
    (@h (Option Unit) Option Unit Unit _ _ _ (fun x s => (gsw x).map (·, s)) ())

-- `Lean.Order.monotone_stateRefT'Run`
theorem monotone_stateRefT'Run_11 : ¬ dropU% Lean.Order.monotone_stateRefT'Run 11 [1] := fun h => by
  have := @h (Option Unit) Option Unit Unit Unit _ _ (liftST some) _ _ (fun x _ => gsw x) ()
  have h2 := this none (some ()) (opt_none_le _)
  cases opt_le_none h2

-- `Lean.Order.monotone_stateRefT'Run`
theorem monotone_stateRefT'Run_9 : ¬ dropU% Lean.Order.monotone_stateRefT'Run 9 [1] := fun h => by
  have := @h (WB Unit) WB Unit Unit Unit _ _ (liftST (WB.mk false)) _ (fun x _ => x)
    (fun _ _ h _ => h) ()
  exact absurd ((this ⟨false, ()⟩ ⟨true, ()⟩ ⟨fun _ => rfl, rfl⟩).1 rfl) (by decide)

-- `Lean.Order.instMonoBindEST`
theorem instMonoBindEST_2 : ¬ indepU% Lean.Order.instMonoBindEST 2 [] :=
  fun h => (@h Empty Unit).elim fun e => e.elim

-- `Lean.Order.instMonoBindEIO`
theorem instMonoBindEIO_1 : ¬ indepU% Lean.Order.instMonoBindEIO 1 [] :=
  fun h => (@h Empty).elim fun e => e.elim

/-! ## Implication orders -/

-- `Lean.Order.implication_order_monotone_exists`
theorem implication_order_monotone_exists_4 : ¬ dropU% Lean.Order.implication_order_monotone_exists 4 [1, 1] :=
  fun h => by
    obtain ⟨_, hn⟩ := @h ImplicationOrder _ Unit (fun x _ => ¬ x) False True (fun e => False.elim e) ⟨(), id⟩
    exact hn trivial

-- `Lean.Order.implication_order_monotone_forall`
theorem implication_order_monotone_forall_4 : ¬ dropU% Lean.Order.implication_order_monotone_forall 4 [1, 1] :=
  fun h => @h ImplicationOrder _ Unit (fun x _ => ¬ x) False True (fun e => False.elim e) (fun _ => id) () trivial

-- `Lean.Order.implication_order_monotone_and`
theorem implication_order_monotone_and_4 : ¬ dropU% Lean.Order.implication_order_monotone_and 4 [1] :=
  fun h => (@h ImplicationOrder _ (fun x => ¬ x) (fun _ => True) (monotone_const _) False True
    (fun e => False.elim e) ⟨id, trivial⟩).1 trivial

-- `Lean.Order.implication_order_monotone_and`
theorem implication_order_monotone_and_5 : ¬ dropU% Lean.Order.implication_order_monotone_and 5 [1] :=
  fun h => (@h ImplicationOrder _ (fun _ => True) (fun x => ¬ x) (monotone_const _) False True
    (fun e => False.elim e) ⟨trivial, id⟩).2 trivial

-- `Lean.Order.implication_order_monotone_or`
theorem implication_order_monotone_or_4 : ¬ dropU% Lean.Order.implication_order_monotone_or 4 [1] :=
  fun h => (@h ImplicationOrder _ (fun x => ¬ x) (fun _ => False) (monotone_const _) False True
    (fun e => False.elim e) (Or.inl id)).elim (fun hn => hn trivial) id

-- `Lean.Order.implication_order_monotone_or`
theorem implication_order_monotone_or_5 : ¬ dropU% Lean.Order.implication_order_monotone_or 5 [1] :=
  fun h => (@h ImplicationOrder _ (fun _ => False) (fun x => ¬ x) (monotone_const _) False True
    (fun e => False.elim e) (Or.inr id)).elim id (fun hn => hn trivial)

-- `Lean.Order.coind_monotone_exists`
theorem coind_monotone_exists_4 : ¬ dropU% Lean.Order.coind_monotone_exists 4 [1, 1] :=
  fun h => by
    obtain ⟨_, hn⟩ := @h ImplicationOrder _ Unit (fun x _ => x) False True (fun e => False.elim e) ⟨(), trivial⟩
    exact hn

-- `Lean.Order.coind_monotone_forall`
theorem coind_monotone_forall_4 : ¬ dropU% Lean.Order.coind_monotone_forall 4 [1, 1] :=
  fun h => @h ImplicationOrder _ Unit (fun x _ => x) False True (fun e => False.elim e) (fun _ => trivial) ()

-- `Lean.Order.coind_monotone_and`
theorem coind_monotone_and_4 : ¬ dropU% Lean.Order.coind_monotone_and 4 [1] :=
  fun h => (@h ImplicationOrder _ (fun x => x) (fun _ => True) (monotone_const _) False True
    (fun e => False.elim e) ⟨trivial, trivial⟩).1

-- `Lean.Order.coind_monotone_and`
theorem coind_monotone_and_5 : ¬ dropU% Lean.Order.coind_monotone_and 5 [1] :=
  fun h => (@h ImplicationOrder _ (fun _ => True) (fun x => x) (monotone_const _) False True
    (fun e => False.elim e) ⟨trivial, trivial⟩).2

-- `Lean.Order.coind_monotone_or`
theorem coind_monotone_or_4 : ¬ dropU% Lean.Order.coind_monotone_or 4 [1] :=
  fun h => (@h ImplicationOrder _ (fun x => x) (fun _ => False) (monotone_const _) False True
    (fun e => False.elim e) (Or.inl trivial)).elim id id

-- `Lean.Order.coind_monotone_or`
theorem coind_monotone_or_5 : ¬ dropU% Lean.Order.coind_monotone_or 5 [1] :=
  fun h => (@h ImplicationOrder _ (fun _ => False) (fun x => x) (monotone_const _) False True
    (fun e => False.elim e) (Or.inr trivial)).elim id id

-- `Lean.Order.coind_not`
theorem coind_not_3 : ¬ dropU% Lean.Order.coind_not 3 [1] :=
  fun h => @h ImplicationOrder _ (fun x => x) False True (fun e => False.elim e) id trivial

-- `Lean.Order.ind_not`
theorem ind_not_3 : ¬ dropU% Lean.Order.ind_not 3 [1] :=
  fun h => @h ImplicationOrder _ (fun x => ¬ x) False True (fun e => False.elim e) (fun hn => hn trivial) id

-- `Lean.Order.ind_impl`
theorem ind_impl_4 : ¬ dropU% Lean.Order.ind_impl 4 [1] :=
  fun h => @h ImplicationOrder _ (fun x => x) (fun _ => False) (monotone_const _) False True
    (fun e => False.elim e) id trivial

-- `Lean.Order.ind_impl`
theorem ind_impl_5 : ¬ dropU% Lean.Order.ind_impl 5 [1] :=
  fun h => @h ImplicationOrder _ (fun _ => True) (fun x => ¬ x) (monotone_const _) False True
    (fun e => False.elim e) (fun _ => id) trivial trivial

-- `Lean.Order.coind_impl`
theorem coind_impl_4 : ¬ dropU% Lean.Order.coind_impl 4 [1] :=
  fun h => @h ImplicationOrder _ (fun x => ¬ x) (fun _ => False) (monotone_const _) False True
    (fun e => False.elim e) (fun hn => hn trivial) id

-- `Lean.Order.coind_impl`
theorem coind_impl_5 : ¬ dropU% Lean.Order.coind_impl 5 [1] :=
  fun h => @h ImplicationOrder _ (fun _ => True) (fun x => x) (monotone_const _) False True
    (fun e => False.elim e) (fun _ => trivial) trivial

/-! ## Example -/

-- `Lean.Order.Example.find_spec`
theorem find_spec_3 : ¬ dropU% Lean.Order.Example.find_spec 3 [] :=
  fun h => absurd (@h (fun _ => false) 0 0).2 (by decide)

end IOrdBasicHand
