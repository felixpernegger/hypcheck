import Lean.Elab.Command
import Cslib
-- CSLib toolkit header (copy of hypcheck runs/hand22/Header.lean with `import Cslib`; ~150 MB, 1.5 s to import)


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
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
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

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
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

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

section

namespace W3c2
open Relation

theorem rtgInv {α : Type} {r : α → α → Prop} (P : α → Prop) (hP : ∀ a b, r a b → P a → P b)
    {a b : α} (h : ReflTransGen r a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hP _ _ hbc ih

theorem eqvEmpty {α : Type} {a b : α} (h : EqvGen (fun _ _ : α => False) a b) : a = b := by
  induction h with
  | rel _ _ h => exact h.elim
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem rtgEmpty {α : Type} {a b : α} (h : ReflTransGen (fun _ _ : α => False) a b) : a = b :=
  (rtgInv (fun x => x = a) (fun _ _ h _ => h.elim) h rfl).symm

theorem tgEmpty {α : Type} {a b : α} (h : TransGen (fun _ _ : α => False) a b) : False := by
  induction h with
  | single h => exact h
  | tail _ h _ => exact h

end W3c2
open W3c2 Relation

-- `WellFounded.ofTransGen` idx 2: necessary (total relation on Unit)
theorem rel1 : ¬ drop0% WellFounded.ofTransGen 2 := fun h =>
  (h (α := Unit) (r := fun _ _ => True)).induction (C := fun _ => False) () (fun x ih => ih x trivial)

-- `Relation.comp_le_comp` idx 5: necessary
theorem rel2 : ¬ drop0% Relation.comp_le_comp 5 := fun h => by
  obtain ⟨_, h1, _⟩ := h (α := Unit) (s := fun _ _ => True) (s' := fun _ _ => False)
    (r := fun _ _ => True) (r' := fun _ _ => True) (fun _ _ x => x) () () ⟨(), trivial, trivial⟩
  exact h1

-- `Relation.comp_le_comp` idx 6: necessary
theorem rel3 : ¬ drop0% Relation.comp_le_comp 6 := fun h => by
  obtain ⟨_, _, h1⟩ := h (α := Unit) (r := fun _ _ => True) (r' := fun _ _ => False)
    (s := fun _ _ => True) (s' := fun _ _ => True) (fun _ _ x => x) () () ⟨(), trivial, trivial⟩
  exact h1

-- `Relation.comp_self_le` idx 2: necessary (successor relation)
theorem rel4 : ¬ drop0% Relation.comp_self_le 2 := fun h =>
  absurd (h (α := ℕ) (fun a b => b = a + 1) 0 2 ⟨1, rfl, rfl⟩) (by decide)

-- `Relation.ReflGen.to_eqvGen` idx 4: necessary (empty relation)
theorem rel5 : ¬ drop0% Relation.ReflGen.to_eqvGen 4 := fun h =>
  absurd (eqvEmpty (h (α := Bool) (r := fun _ _ => False) (a := true) (b := false))) (by decide)

-- `Relation.TransGen.to_eqvGen` idx 4: necessary (empty relation)
theorem rel6 : ¬ drop0% Relation.TransGen.to_eqvGen 4 := fun h =>
  absurd (eqvEmpty (h (α := Bool) (r := fun _ _ => False) (a := true) (b := false))) (by decide)

-- `Relation.ReflTransGen.to_eqvGen` idx 4: necessary (empty relation)
theorem rel7 : ¬ drop0% Relation.ReflTransGen.to_eqvGen 4 := fun h =>
  absurd (eqvEmpty (h (α := Bool) (r := fun _ _ => False) (a := true) (b := false))) (by decide)

-- `Equivalence.eqvGen_le` idx 3: necessary (empty relations on Unit)
theorem rel8 : ¬ drop0% Equivalence.eqvGen_le 3 := fun h =>
  h (α := Unit) (r₁ := fun _ _ => False) (r₂ := fun _ _ => False) (fun _ _ x => x) () () (EqvGen.refl ())

-- `Equivalence.eqvGen_le` idx 4: necessary
theorem rel9 : ¬ drop0% Equivalence.eqvGen_le 4 := fun h =>
  absurd (h (α := Bool) (r₁ := fun _ _ => True) (r₂ := (· = ·)) eq_equivalence true false
    (EqvGen.rel _ _ trivial)) (by decide)

-- `Relation.Join.single` idx 4: necessary (successor relation)
theorem rel10 : ¬ drop0% Relation.Join.single 4 := fun h => by
  obtain ⟨c, h1, h2⟩ := h (α := ℕ) (r := fun a b => b = a + 1) (a := 0) (b := 1) rfl
  simp at h1 h2; omega

-- `Relation.instReflJoin₂` idx 3: necessary
theorem rel11 : ¬ drop0% Relation.instReflJoin₂ 3 := fun h => by
  obtain ⟨c, h1, _⟩ := (@h Unit (fun _ _ => False) (fun _ _ => True) ⟨fun _ => trivial⟩).refl ()
  exact h1

-- `Relation.instReflJoin₂` idx 4: necessary
theorem rel12 : ¬ drop0% Relation.instReflJoin₂ 4 := fun h => by
  obtain ⟨c, _, h1⟩ := (@h Unit (fun _ _ => True) (fun _ _ => False) ⟨fun _ => trivial⟩).refl ()
  exact h1

-- `Relation.Join₂.join₂_le` idx 4: necessary (successor relation is not transitive)
theorem rel13 : ¬ drop0% Relation.Join₂.join₂_le 4 := fun h =>
  absurd (h (α := ℕ) (r := fun a b => b = a + 1) (r₁ := fun a b => b = a + 1)
    (r₂ := fun a b => a = b + 1) (fun _ _ x => x) (fun _ _ x => x) 0 2 ⟨1, rfl, rfl⟩) (by decide)

-- `Relation.Join₂.join₂_le` idx 5: necessary
theorem rel14 : ¬ drop0% Relation.Join₂.join₂_le 5 := fun h =>
  absurd (h (α := Bool) (r := (· = ·)) (r₁ := fun _ _ => True) (r₂ := (· = ·))
    (fun _ _ x => x.symm) true false ⟨false, trivial, rfl⟩) (by decide)

-- `Relation.Join₂.join₂_le` idx 6: necessary
theorem rel15 : ¬ drop0% Relation.Join₂.join₂_le 6 := fun h =>
  absurd (h (α := Bool) (r := (· = ·)) (r₁ := (· = ·)) (r₂ := fun _ _ => True)
    (fun _ _ x => x) true false ⟨true, rfl, trivial⟩) (by decide)

-- `Relation.Join₂.mono` idx 5: necessary
theorem rel16 : ¬ drop0% Relation.Join₂.mono 5 := fun h => by
  obtain ⟨_, h1, _⟩ := h (α := Unit) (r₁ := fun _ _ => True) (r₁' := fun _ _ => False)
    (r₂ := fun _ _ => True) (r₂' := fun _ _ => True) (fun _ _ x => x) () () ⟨(), trivial, trivial⟩
  exact h1

-- `Relation.Join₂.mono` idx 6: necessary
theorem rel17 : ¬ drop0% Relation.Join₂.mono 6 := fun h => by
  obtain ⟨_, _, h1⟩ := h (α := Unit) (r₂ := fun _ _ => True) (r₂' := fun _ _ => False)
    (r₁ := fun _ _ => True) (r₁' := fun _ _ => True) (fun _ _ x => x) () () ⟨(), trivial, trivial⟩
  exact h1

-- `Equivalence.join_reflTransGen_le` idx 3: necessary (empty relations on Unit)
theorem rel18 : ¬ drop0% Equivalence.join_reflTransGen_le 3 := fun h =>
  h (α := Unit) (r₁ := fun _ _ => False) (r₂ := fun _ _ => False) (fun _ _ x => x) () ()
    ⟨(), .refl, .refl⟩

-- `Equivalence.join_reflTransGen_le` idx 4: necessary
theorem rel19 : ¬ drop0% Equivalence.join_reflTransGen_le 4 := fun h =>
  absurd (h (α := Bool) (r₁ := fun _ _ => True) (r₂ := (· = ·)) eq_equivalence true false
    ⟨false, .single trivial, .refl⟩) (by decide)

-- `Relation.join₂_reflTransGen_le` idx 4: necessary (empty relation is not reflexive)
theorem rel20 : ¬ drop0% Relation.join₂_reflTransGen_le 4 := fun h =>
  @h Unit (fun _ _ => False) (fun _ _ => False) (fun _ _ => False) ⟨fun _ _ _ h _ => h⟩
    (fun _ _ x => x) (fun _ _ x => x) () () ⟨(), .refl, .refl⟩

-- `Relation.join₂_reflTransGen_le` idx 5: necessary (reflexive successor relation)
theorem rel21 : ¬ drop0% Relation.join₂_reflTransGen_le 5 := fun h => by
  have := @h ℕ (fun a b => a = b ∨ b = a + 1) (fun a b => a = b ∨ b = a + 1)
    (fun a b => a = b ∨ a = b + 1) ⟨fun _ => Or.inl rfl⟩ (fun _ _ x => x)
    (fun _ _ x => by rcases x with x | x <;> simp_all) 0 2
    ⟨2, .tail (.single (Or.inr rfl)) (Or.inr rfl), .refl⟩
  simp at this

-- `Relation.join₂_reflTransGen_le` idx 6: necessary
theorem rel22 : ¬ drop0% Relation.join₂_reflTransGen_le 6 := fun h =>
  absurd (h (α := Bool) (r := (· = ·)) (r₁ := fun _ _ => True) (r₂ := (· = ·))
    (fun _ _ x => x.symm) true false ⟨false, .single trivial, .refl⟩) (by decide)

-- `Relation.join₂_reflTransGen_le` idx 7: necessary
theorem rel23 : ¬ drop0% Relation.join₂_reflTransGen_le 7 := fun h =>
  absurd (h (α := Bool) (r := (· = ·)) (r₁ := (· = ·)) (r₂ := fun _ _ => True)
    (fun _ _ x => x) true false ⟨true, .refl, .single trivial⟩) (by decide)

-- `Relation.join₂_reflTransGen_le_of_isEquiv` idx 4: necessary (empty relation)
theorem rel24 : ¬ drop0% Relation.join₂_reflTransGen_le_of_isEquiv 4 := fun h =>
  h (α := Unit) (r := fun _ _ => False) (r₁ := fun _ _ => False) (r₂ := fun _ _ => False)
    (fun _ _ x => x) (fun _ _ x => x) () () ⟨(), .refl, .refl⟩

-- `Relation.join₂_reflTransGen_le_of_isEquiv` idx 5: necessary
theorem rel25 : ¬ drop0% Relation.join₂_reflTransGen_le_of_isEquiv 5 := fun h =>
  absurd (h (α := Bool) (r := (· = ·)) (r₁ := fun _ _ => True) (r₂ := (· = ·))
    (fun _ _ x => x) true false ⟨false, .single trivial, .refl⟩) (by decide)

-- `Relation.join₂_reflTransGen_le_of_isEquiv` idx 6: necessary
theorem rel26 : ¬ drop0% Relation.join₂_reflTransGen_le_of_isEquiv 6 := fun h =>
  absurd (h (α := Bool) (r := (· = ·)) (r₁ := (· = ·)) (r₂ := fun _ _ => True)
    (fun _ _ x => x) true false ⟨true, .refl, .single trivial⟩) (by decide)

-- `Equivalence.join₂_reflTransGen_le` idx 4: necessary (empty relation)
theorem rel27 : ¬ drop0% Equivalence.join₂_reflTransGen_le 4 := fun h =>
  h (α := Unit) (r := fun _ _ => False) (r₁ := fun _ _ => False) (r₂ := fun _ _ => False)
    (fun _ _ x => x) (fun _ _ x => x) () () ⟨(), .refl, .refl⟩

-- `Equivalence.join₂_reflTransGen_le` idx 5: necessary
theorem rel28 : ¬ drop0% Equivalence.join₂_reflTransGen_le 5 := fun h =>
  absurd (h (α := Bool) (r := (· = ·)) (r₁ := fun _ _ => True) (r₂ := (· = ·)) eq_equivalence
    (fun _ _ x => x) true false ⟨false, .single trivial, .refl⟩) (by decide)

-- `Equivalence.join₂_reflTransGen_le` idx 6: necessary
theorem rel29 : ¬ drop0% Equivalence.join₂_reflTransGen_le 6 := fun h =>
  absurd (h (α := Bool) (r := (· = ·)) (r₁ := (· = ·)) (r₂ := fun _ _ => True) eq_equivalence
    (fun _ _ x => x) true false ⟨true, .refl, .single trivial⟩) (by decide)

-- `Relation.reflTransGen_mono_closed` idx 3: necessary
theorem rel30 : ¬ drop0% Relation.reflTransGen_mono_closed 3 := fun h => by
  have := h (α := Bool) (r₁ := fun _ _ => True) (r₂ := fun _ _ => False) (fun _ _ x => x.elim)
  have h2 : ReflTransGen (fun _ _ : Bool => True) true false := .single trivial
  rw [this] at h2; exact absurd (rtgEmpty h2) (by decide)

-- `Relation.reflTransGen_mono_closed` idx 4: necessary
theorem rel31 : ¬ drop0% Relation.reflTransGen_mono_closed 4 := fun h => by
  have := h (α := Bool) (r₁ := fun _ _ => False) (r₂ := fun _ _ => True) (fun _ _ x => x.elim)
  have h2 : ReflTransGen (fun _ _ : Bool => True) true false := .single trivial
  rw [← this] at h2; exact absurd (rtgEmpty h2) (by decide)

-- `Relation.join_inl_reflTransGen` idx 5: necessary (empty relations)
theorem rel32 : ¬ drop0% Relation.join_inl_reflTransGen 5 := fun h => by
  have := h (α := Bool) (r₁ := fun _ _ => False) (r₂ := fun _ _ => False) (a := true) (b := false)
  exact absurd (rtgInv (fun x => x = true) (fun _ _ h _ => by simp at h) this rfl) (by decide)

-- `Relation.join_inr_reflTransGen` idx 5: necessary (empty relations)
theorem rel33 : ¬ drop0% Relation.join_inr_reflTransGen 5 := fun h => by
  have := h (α := Bool) (r₁ := fun _ _ => False) (r₂ := fun _ _ => False) (a := true) (b := false)
  exact absurd (rtgInv (fun x => x = true) (fun _ _ h _ => by simp at h) this rfl) (by decide)

-- `Relation.acyclic_le` idx 3: necessary
theorem rel34 : ¬ drop0% Relation.acyclic_le 3 := fun h =>
  h (α := Unit) (r := fun _ _ => True) (s := fun _ _ => False) ⟨fun _ h => tgEmpty h⟩ |>.irrefl ()
    (.single trivial)

-- `Relation.acyclic_le` idx 4: necessary
theorem rel35 : ¬ drop0% Relation.acyclic_le 4 := fun h =>
  h (α := Unit) (r := fun _ _ => True) (s := fun _ _ => True) (fun _ _ x => x) |>.irrefl () (.single trivial)

end

section

namespace W3c2
open Cslib ωSequence

-- `segment f 0 = 0` for every `f` (from W1c2)
theorem segz (f : ℕ → ℕ) : Nat.segment f 0 = 0 := by
  unfold Nat.segment
  rw [Nat.count_succ, Nat.count_zero]
  split <;> rfl

theorem seg1 (f : ℕ → ℕ) (h0 : 0 ∈ Set.range f) (h1 : 1 ∈ Set.range f) : Nat.segment f 1 = 1 := by
  unfold Nat.segment
  rw [Nat.count_succ, Nat.count_succ, Nat.count_zero, if_pos h0, if_pos h1]

-- count of a predicate true at 0 and false on 1..n
theorem cnt1 (p : ℕ → Prop) {_ : DecidablePred p} (n : ℕ) (h0 : p 0)
    (h : ∀ m, 0 < m → m ≤ n → ¬ p m) : Nat.count p (n + 1) = 1 := by
  induction n with
  | zero => rw [Nat.count_succ, Nat.count_zero, if_pos h0]
  | succ n ih =>
    rw [Nat.count_succ, ih (fun m h1 h2 => h m h1 (by omega)), if_neg (h _ (by omega) le_rfl)]

-- flatten at position 0 is the head of the first list
theorem flat0 {α : Type} [Inhabited α] (L : ωSequence (List α)) : L.flatten 0 = (L 0)[0]! := by
  rw [flatten_def, segz]; simp

-- first list empty, all others `[1]`
def LS : ωSequence (List ℕ) := ⟨fun k => if k = 0 then [] else [1]⟩

theorem LS0 : LS.flatten 0 = 0 := by rw [flat0]; rfl
theorem LS1 : (LS.drop 1).flatten 0 = 1 := by rw [flat0]; rfl

end W3c2
open W3c2 Cslib ωSequence

-- `Cslib.ωSequence.cumLen_strictMono` idx 2: necessary (all lists empty)
theorem om1 : ¬ drop0% Cslib.ωSequence.cumLen_strictMono 2 := fun h =>
  absurd (h (α := ℕ) (ls := ⟨fun _ => []⟩) (show 0 < 1 by decide)) (by simp [cumLen])

universe u in
-- `Cslib.ωSequence.cumLen_segment_zero` idx 2: removable (for n below the first length, 0 is the
-- only value of cumLen that is ≤ n, whatever the other lengths)
theorem om2 : drop% Cslib.ωSequence.cumLen_segment_zero 2 := by
  intro α ls n h_n
  have hge : ∀ k, 0 < k → (ls 0).length ≤ ls.cumLen k := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = 1 + j := ⟨k - 1, by omega⟩
    rw [cumLen_one_add_drop]; omega
  unfold Nat.segment
  rw [cnt1 _ n ⟨0, rfl⟩]
  rintro m hm hmn ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp at hk; omega
  · have := hge k hk0; omega

-- `Cslib.ωSequence.cumLen_segment_zero` idx 4: necessary (singletons, n = 1)
theorem om3 : ¬ drop0% Cslib.ωSequence.cumLen_segment_zero 4 := fun h =>
  absurd (h (α := ℕ) (ls := ⟨fun _ => [0]⟩) (fun _ => by simp) 1)
    (by rw [seg1 _ ⟨0, rfl⟩ ⟨1, rfl⟩]; decide)

-- `Cslib.ωSequence.cumLen_segment_one_add` idx 2: necessary (all lists empty, n = 0)
theorem om4 : ¬ drop0% Cslib.ωSequence.cumLen_segment_one_add 2 := fun h => by
  have := h (α := ℕ) (ls := ⟨fun _ => []⟩) 0 (by simp)
  simp only [Nat.zero_sub, segz] at this; omega

-- `Cslib.ωSequence.cumLen_segment_one_add` idx 4: necessary (singletons, n = 0)
theorem om5 : ¬ drop0% Cslib.ωSequence.cumLen_segment_one_add 4 := fun h => by
  have := h (α := ℕ) (ls := ⟨fun _ => [0]⟩) (fun _ => by simp) 0
  rw [segz] at this; omega

-- `Cslib.ωSequence.flatten_get_add` idx 6: necessary (first list empty)
theorem om6 : ¬ drop0% Cslib.ωSequence.flatten_get_add 6 := fun h => by
  have := h (α := ℕ) LS (n := 1) (k := 0) (by decide)
  have e : LS.cumLen 1 + 0 = 0 := rfl
  rw [e, LS0] at this; exact absurd this (by decide)

-- `Cslib.ωSequence.cons_flatten` idx 3: necessary (first list empty)
theorem om7 : ¬ drop0% Cslib.ωSequence.cons_flatten 3 := fun h => by
  have := congrArg (fun s => s 0) (h (α := ℕ) (ls := LS))
  simp only [LS0] at this
  rw [show LS.head = [] from rfl, tail_eq_drop] at this
  exact absurd (LS1.symm.trans this) (by decide)

-- `Cslib.ωSequence.append_flatten` idx 3: necessary (first list empty, n = 1)
theorem om8 : ¬ drop0% Cslib.ωSequence.append_flatten 3 := fun h => by
  have := congrArg (fun s => s 0) (h (α := ℕ) (ls := LS) 1)
  simp only [LS0] at this
  exact absurd (LS1.symm.trans this) (by decide)

-- `Cslib.ωSequence.flatten_take_drop` idx 3: necessary (first list empty, n = 1)
theorem om9 : ¬ drop0% Cslib.ωSequence.flatten_take_drop 3 := fun h => by
  have := congrArg (fun s => s 0) (h (α := ℕ) (ls := LS) 1).2
  rw [LS1, show LS.cumLen 1 = 0 from rfl] at this
  exact absurd (this.trans LS0) (by decide)

-- `Cslib.ωSequence.flatten_take` idx 3: necessary (first list empty, n = 2)
theorem om10 : ¬ drop0% Cslib.ωSequence.flatten_take 3 := fun h => by
  have := h (α := ℕ) (ls := LS) 2
  rw [show LS.cumLen 2 = 1 from rfl] at this
  have e : LS.flatten.take 1 = [0] := by simp [take, LS0]
  rw [e] at this; exact absurd this (by decide)

-- `Cslib.ωSequence.flatten_drop` idx 3: necessary (first list empty, n = 1)
theorem om11 : ¬ drop0% Cslib.ωSequence.flatten_drop 3 := fun h => by
  have := congrArg (fun s => s 0) (h (α := ℕ) (ls := LS) 1)
  rw [LS1, show LS.cumLen 1 = 0 from rfl] at this
  exact absurd (this.trans LS0) (by decide)

-- `Cslib.ωSequence.extract_flatten` idx 3: necessary (first list empty, n = 1)
theorem om12 : ¬ drop0% Cslib.ωSequence.extract_flatten 3 := fun h => by
  have := h (α := ℕ) (ls := LS) 1
  rw [show LS.cumLen 1 = 0 from rfl, show LS.cumLen (1 + 1) = 1 from rfl] at this
  have e : LS.flatten.extract 0 1 = [0] := by simp [extract, LS0]
  rw [e] at this; exact absurd this (by decide)

-- `Cslib.ωSequence.segment_toSegs_cumLen` idx 2: necessary (f = 0, 1, 0, 0, …)
theorem om13 : ¬ drop0% Cslib.ωSequence.segment_toSegs_cumLen 2 := fun h => by
  have := congrFun (h (α := ℕ) (f := fun n => if n = 1 then 1 else 0) rfl ⟨id⟩) 2
  simp [cumLen, toSegs] at this

-- `Cslib.ωSequence.segment_toSegs_cumLen` idx 3: necessary (f = n + 1)
theorem om14 : ¬ drop0% Cslib.ωSequence.segment_toSegs_cumLen 3 := fun h => by
  have := congrFun (h (α := ℕ) (f := fun n => n + 1) (fun a b h => by simpa using h) ⟨id⟩) 0
  simp [cumLen] at this

-- `Cslib.ωSequence.strictMono_flatten` idx 3: necessary (f = 0)
theorem om15 : ¬ drop0% Cslib.ωSequence.strictMono_flatten 3 := fun h => by
  have := congrArg (fun s => s 0) (h (α := ℕ) (f := fun _ => 0) rfl ⟨fun _ => 1⟩)
  simp only [flat0] at this
  exact absurd this (by decide)

-- `Cslib.ωSequence.strictMono_flatten` idx 4: necessary (f = n + 1)
theorem om16 : ¬ drop0% Cslib.ωSequence.strictMono_flatten 4 := fun h => by
  have := congrArg (fun s => s 0) (h (α := ℕ) (f := fun n => n + 1)
    (fun a b h => by simpa using h) ⟨id⟩)
  simp only [flat0] at this
  exact absurd this (by decide)

-- `Cslib.ωSequence.frequently_in_strictMono` idx 2: necessary (f = 0)
theorem om17 : ¬ drop0% Cslib.ωSequence.frequently_in_strictMono 2 := fun h => by
  have := h (p := fun _ => True) (f := fun _ => 0)
    (Filter.frequently_atTop.mpr fun a => ⟨a, le_rfl, trivial⟩)
  simp at this

-- `Cslib.ωSequence.frequently_in_strictMono` idx 3: necessary (p = False)
theorem om18 : ¬ drop0% Cslib.ωSequence.frequently_in_strictMono 3 := fun h => by
  have := h (p := fun _ => False) (f := id) strictMono_id
  simp at this

-- `Cslib.ωSequence.ext` idx 3: necessary
theorem om19 : ¬ drop0% Cslib.ωSequence.ext 3 := fun h =>
  Bool.noConfusion (congrArg (fun s => s.get 0)
    (h (α := Bool) (s₁ := ⟨fun _ => true⟩) (s₂ := ⟨fun _ => false⟩)))

-- `Cslib.ωSequence.append_right_injective` idx 4: necessary (x = [])
theorem om20 : ¬ drop0% Cslib.ωSequence.append_right_injective 4 := fun h =>
  Bool.noConfusion (congrArg (fun s => s.get 0) (h (α := Bool) [] ⟨fun _ => true⟩ ⟨fun _ => false⟩))

namespace W3c2
theorem appEq : ([0] ++ω (⟨fun _ => 0⟩ : ωSequence ℕ)) = ([] ++ω ⟨fun _ => 0⟩) :=
  ωSequence.ext fun n => by cases n <;> rfl
end W3c2

-- `Cslib.ωSequence.append_left_injective` idx 6: necessary ([0] ++ω 0 = [] ++ω 0)
theorem om21 : ¬ drop0% Cslib.ωSequence.append_left_injective 6 := fun h =>
  absurd (h (α := ℕ) [0] [] _ _ appEq) (by decide)

-- `Cslib.ωSequence.append_left_right_injective` idx 6: necessary ([0] ++ω 0 = [] ++ω 0)
theorem om22 : ¬ drop0% Cslib.ωSequence.append_left_right_injective 6 := fun h =>
  absurd (h (α := ℕ) [0] [] _ _ appEq).1 (by decide)

-- `Cslib.ωSequence.drop_append_of_le_length` idx 4: necessary (x = [], n = 1)
theorem om23 : ¬ drop0% Cslib.ωSequence.drop_append_of_le_length 4 := fun h =>
  absurd (congrArg (fun s => s.get 0) (h (α := ℕ) 1 [] ⟨id⟩)) (by decide)

-- `Cslib.ωSequence.drop_append_of_ge_length` idx 4: necessary (xl = [5], n = 0)
theorem om24 : ¬ drop0% Cslib.ωSequence.drop_append_of_ge_length 4 := fun h =>
  absurd (congrArg (fun s => s.get 0) (h (α := ℕ) (xl := [5]) (xs := ⟨fun _ => 0⟩) (n := 0)))
    (by decide)

-- `Cslib.ωSequence.take_theorem` idx 3: necessary
theorem om25 : ¬ drop0% Cslib.ωSequence.take_theorem 3 := fun h =>
  Bool.noConfusion (congrArg (fun s => s.get 0) (h (α := Bool) ⟨fun _ => true⟩ ⟨fun _ => false⟩))

universe u in
-- `Cslib.ωSequence.drop_extract` idx 5: removable (if k > n - m both sides are empty)
theorem om26 : drop% Cslib.ωSequence.drop_extract 5 := by
  intro α xs m n k
  by_cases hk : k ≤ n - m
  · exact drop_extract hk
  · rw [List.drop_eq_nil_of_le (by simp; omega), eq_comm, extract_eq_nil_iff]; omega

end

section

open Cslib ωSequence Set

namespace W3c2
theorem freqNot0 : ∃ᶠ k in Filter.atTop, (⟨id⟩ : ωSequence ℕ) k ∉ ({0} : Set ℕ) :=
  Filter.frequently_atTop.mpr fun a => ⟨a + 1, by omega, by simp⟩
end W3c2
open W3c2

-- `Cslib.ωSequence.Step.mk` idx 4: necessary (p = univ, q = ∅)
theorem tp1 : ¬ drop0% Cslib.ωSequence.Step.mk 4 := fun h =>
  h (xs := (⟨fun _ => true⟩ : ωSequence Bool)) (p := univ) (q := ∅) 0 (mem_univ _)

-- `Cslib.ωSequence.LeadsTo.mk` idx 4: necessary (p = univ, q = ∅)
theorem tp2 : ¬ drop0% Cslib.ωSequence.LeadsTo.mk 4 := fun h => by
  obtain ⟨_, _, hk⟩ := h (xs := (⟨fun _ => true⟩ : ωSequence Bool)) (p := univ) (q := ∅) 0 (mem_univ _)
  exact hk

-- `Cslib.ωSequence.step_leadsTo` idx 4: necessary (p = univ, q = ∅)
theorem tp3 : ¬ drop0% Cslib.ωSequence.step_leadsTo 4 := fun h => by
  obtain ⟨_, _, hk⟩ := h (xs := (⟨fun _ => true⟩ : ωSequence Bool)) (p := univ) (q := ∅) 0 (mem_univ _)
  exact hk

-- `Cslib.ωSequence.leadsTo_trans` idx 6: necessary (p = q = univ, r = ∅)
theorem tp4 : ¬ drop0% Cslib.ωSequence.leadsTo_trans 6 := fun h => by
  obtain ⟨_, _, hk⟩ := h (xs := (⟨fun _ => true⟩ : ωSequence Bool)) (p := univ) (q := univ) (r := ∅)
    (fun k _ => ⟨k, le_rfl, mem_univ _⟩) 0 (mem_univ _)
  exact hk

-- `Cslib.ωSequence.leadsTo_cases_or` idx 6: necessary (p = q = univ, r = s = ∅)
theorem tp5 : ¬ drop0% Cslib.ωSequence.leadsTo_cases_or 6 := fun h => by
  obtain ⟨_, _, hk⟩ := h (xs := (⟨fun _ => true⟩ : ωSequence Bool)) (p := univ) (q := univ) (r := ∅)
    (s := ∅) (fun k hk => (hk.2 (mem_univ _)).elim) 0 (mem_univ _)
  simp at hk

-- `Cslib.ωSequence.leadsTo_cases_or` idx 7: necessary (p = univ, q = r = s = ∅)
theorem tp6 : ¬ drop0% Cslib.ωSequence.leadsTo_cases_or 7 := fun h => by
  obtain ⟨_, _, hk⟩ := h (xs := (⟨fun _ => true⟩ : ωSequence Bool)) (p := univ) (q := ∅) (r := ∅)
    (s := ∅) (fun k hk => hk.2.elim) 0 (mem_univ _)
  simp at hk

-- `Cslib.ωSequence.until_frequently_not_leadsTo` idx 4: necessary (xs = id, p = {0}, q = ∅)
theorem tp7 : ¬ drop0% Cslib.ωSequence.until_frequently_not_leadsTo 4 := fun h => by
  obtain ⟨_, _, hk⟩ := h (xs := (⟨id⟩ : ωSequence ℕ)) (p := {0}) (q := ∅) freqNot0 0 rfl
  exact hk

-- `Cslib.ωSequence.until_frequently_not_leadsTo` idx 5: necessary (constant xs, p = univ, q = ∅)
theorem tp8 : ¬ drop0% Cslib.ωSequence.until_frequently_not_leadsTo 5 := fun h => by
  obtain ⟨_, _, hk⟩ := h (xs := (⟨fun _ => true⟩ : ωSequence Bool)) (p := univ) (q := ∅)
    (fun _ _ => mem_univ _) 0 (mem_univ _)
  exact hk

-- `Cslib.ωSequence.until_frequently_leadsTo_and` idx 4: necessary (xs = id, p = {0}, q = {0}ᶜ)
theorem tp9 : ¬ drop0% Cslib.ωSequence.until_frequently_leadsTo_and 4 := fun h => by
  obtain ⟨_, _, hk⟩ := h (xs := (⟨id⟩ : ωSequence ℕ)) (p := {0}) (q := {0}ᶜ) freqNot0 0 rfl
  exact hk.2 hk.1

-- `Cslib.ωSequence.until_frequently_leadsTo_and` idx 5: necessary (constant xs, p = univ, q = ∅)
theorem tp10 : ¬ drop0% Cslib.ωSequence.until_frequently_leadsTo_and 5 := fun h => by
  obtain ⟨_, _, hk⟩ := h (xs := (⟨fun _ => true⟩ : ωSequence Bool)) (p := univ) (q := ∅)
    (fun _ _ => mem_univ _) 0 (mem_univ _)
  exact hk.2

-- `Cslib.ωSequence.frequently_leadsTo_frequently` idx 4: necessary (p = q = ∅)
theorem tp11 : ¬ drop0% Cslib.ωSequence.frequently_leadsTo_frequently 4 := fun h => by
  have := h (xs := (⟨fun _ => true⟩ : ωSequence Bool)) (p := ∅) (q := ∅) (fun _ hk => hk.elim)
  simp at this

end

section

namespace W3c2
-- bind-counting monad (W1c0), breaks `LawfulMonad`
@[instance_reducible] def cntM : Monad (fun α => ℕ × α) where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1 + 1, (f x.2).2)
-- same, with a `map` that adds 5 (so `map ≠ bind ∘ pure`)
@[instance_reducible] def cntM5 : Monad (fun α => ℕ × α) where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1 + 1, (f x.2).2)
  map f x := (x.1 + 5, f x.2)
-- polynomial functors: one operation with one / no argument
def PU : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩
def PE : PFunctor.{0, 0} := ⟨Unit, fun _ => Empty⟩
end W3c2
open W3c2 PFunctor

-- `PFunctor.ext` idx 2: necessary (head types Unit and Empty differ)
theorem pf1 : ¬ indep0% PFunctor.ext 2 := fun h =>
  (cast (h (P := ⟨Unit, fun _ => Empty⟩) (Q := ⟨Empty, fun _ => Empty⟩)) ()).elim

-- `PFunctor.FreeM.induction` idx 3: necessary (motive False, unary operation)
theorem pf2 : ¬ drop0% PFunctor.FreeM.induction 3 := fun h =>
  h (P := PU) (α := Unit) (motive := fun _ => False) (fun _ _ ih => ih ()) (FreeM.pure ())

-- `PFunctor.FreeM.induction` idx 4: necessary (motive False, empty value type)
theorem pf3 : ¬ drop0% PFunctor.FreeM.induction 4 := fun h =>
  h (P := PE) (α := Empty) (motive := fun _ => False) (fun a => a.elim)
    (FreeM.liftBind () (fun e => e.elim))

-- `PFunctor.FreeM.Interprets.apply_pure` idx 6: necessary (Option, eval = none)
theorem pf4 : ¬ drop0% PFunctor.FreeM.Interprets.apply_pure 6 := fun h =>
  absurd (h (P := PU) (m := Option) (α := Unit) (handler := fun _ => none)
    (eval := fun _ => none) ()) (by decide)

-- `PFunctor.FreeM.Interprets.apply_lift_bind` idx 6: necessary (Option, eval = some (), handler = none)
theorem pf5 : ¬ drop0% PFunctor.FreeM.Interprets.apply_lift_bind 6 := fun h =>
  absurd (h (P := PU) (m := Option) (α := Unit) (handler := fun _ => none)
    (eval := fun _ => some ()) () (fun _ => FreeM.pure ())) (by decide)

-- `PFunctor.FreeM.Interprets.eq` idx 6: necessary (Option, eval = none)
theorem pf6 : ¬ drop0% PFunctor.FreeM.Interprets.eq 6 := fun h =>
  absurd (congrFun (h (P := PU) (m := Option) (α := Unit) (handler := fun _ => none)
    (eval := fun _ => none)) (FreeM.pure ())) (by decide)

-- `PFunctor.FreeM.liftM_bind` idx 4: necessary (bind-counting monad)
theorem pf7 : ¬ drop0% PFunctor.FreeM.liftM_bind 4 := fun h =>
  absurd (congrArg Prod.fst (@h PU (fun α => ℕ × α) cntM (fun _ => (0, ())) Unit Unit
    (FreeM.pure ()) (fun _ => FreeM.pure ()))) (by decide)

-- `PFunctor.FreeM.isMonadHom_liftM` idx 4: necessary (bind-counting monad)
theorem pf8 : ¬ drop0% PFunctor.FreeM.isMonadHom_liftM 4 := fun h =>
  absurd (congrArg Prod.fst (@Cslib.IsMonadHom.map_bind PU.FreeM (fun α => ℕ × α) _ cntM _
    (@h PU (fun α => ℕ × α) cntM (fun _ => (0, ()))) Unit Unit (FreeM.pure ())
    (fun _ => FreeM.pure ()))) (by decide)

-- `PFunctor.FreeM.liftM_map` idx 3: necessary (bind-counting monad)
theorem pf9 : ¬ drop0% PFunctor.FreeM.liftM_map 3 := fun h =>
  absurd (congrArg Prod.fst (@h PU (fun α => ℕ × α) cntM Unit Unit id (fun _ => (0, ()))
    (FreeM.pure ()))) (by decide)

-- `PFunctor.FreeM.liftM_seq` idx 3: necessary (bind-counting monad)
theorem pf10 : ¬ drop0% PFunctor.FreeM.liftM_seq 3 := fun h =>
  absurd (congrArg Prod.fst (@h PU (fun α => ℕ × α) cntM Unit Unit (fun _ => (0, ()))
    (FreeM.pure id) (FreeM.pure ()))) (by decide)

-- `PFunctor.FreeM.liftM_seqLeft` idx 3: necessary (bind-counting monad)
theorem pf11 : ¬ drop0% PFunctor.FreeM.liftM_seqLeft 3 := fun h =>
  absurd (congrArg Prod.fst (@h PU (fun α => ℕ × α) cntM Unit Unit (fun _ => (0, ()))
    (FreeM.pure ()) (FreeM.pure ()))) (by decide)

-- `PFunctor.FreeM.liftM_seqRight` idx 3: necessary (bind-counting monad)
theorem pf12 : ¬ drop0% PFunctor.FreeM.liftM_seqRight 3 := fun h =>
  absurd (congrArg Prod.fst (@h PU (fun α => ℕ × α) cntM Unit Unit (fun _ => (0, ()))
    (FreeM.pure ()) (FreeM.pure ()))) (by decide)

-- `PFunctor.FreeM.liftM_lift` idx 3: necessary (bind-counting monad)
theorem pf13 : ¬ drop0% PFunctor.FreeM.liftM_lift 3 := fun h =>
  absurd (congrArg Prod.fst (@h PU (fun α => ℕ × α) cntM (fun _ => (0, ())) ())) (by decide)

-- `PFunctor.FreeM.liftM_liftObj` idx 4: necessary (bind-counting monad whose map adds 5)
theorem pf14 : ¬ drop0% PFunctor.FreeM.liftM_liftObj 4 := fun h =>
  absurd (congrArg Prod.fst (@h PU (fun α => ℕ × α) Unit cntM5 (fun _ => (0, ()))
    ⟨(), fun _ => ()⟩)) (by decide)

-- `PFunctor.FreeM.liftM_comp` idx 3: necessary (bind-counting monad)
theorem pf15 : ¬ drop0% PFunctor.FreeM.liftM_comp 3 := fun h =>
  absurd (congrArg Prod.fst (@h PU (fun α => ℕ × α) cntM PU Unit (FreeM.lift ())
    (fun _ => FreeM.pure ()) (fun _ => (0, ())))) (by decide)

-- `PFunctor.FreeM.foldFreeM_unique` idx 6: necessary (h = false, onValue = true)
theorem pf16 : ¬ drop0% PFunctor.FreeM.foldFreeM_unique 6 := fun h =>
  Bool.noConfusion (congrFun (h (P := PU) (α := Unit) (β := Bool) (fun _ => true)
    (fun _ _ => false) (fun _ => false) (fun _ _ => rfl)) (FreeM.pure ()))

-- `PFunctor.FreeM.foldFreeM_unique` idx 7: necessary (h = false, onEffect = true)
theorem pf17 : ¬ drop0% PFunctor.FreeM.foldFreeM_unique 7 := fun h =>
  Bool.noConfusion (congrFun (h (P := PE) (α := Unit) (β := Bool) (fun _ => false)
    (fun _ _ => true) (fun _ => false) (fun _ => rfl)) (FreeM.liftBind () (fun e => e.elim)))

-- `PFunctor.FreeM.toWOfIsEmpty_lift_bind` idx 2: necessary (α = Unit)
theorem pf18 : ¬ indep0% PFunctor.FreeM.toWOfIsEmpty_lift_bind 2 := fun h =>
  (h (P := PU) (α := Unit) () (fun _ => FreeM.pure ())).false ()

-- `PFunctor.FreeM.toWOfIsEmpty_lift_bind'` idx 2: necessary (α = Unit)
theorem pf19 : ¬ indep0% PFunctor.FreeM.toWOfIsEmpty_lift_bind' 2 := fun h =>
  (h (P := PU) (α := Unit) () (fun _ => FreeM.pure ())).false ()

-- `PFunctor.FreeM.toWOfIsEmpty_toFreeM` idx 2: necessary (α = Unit)
theorem pf20 : ¬ indep0% PFunctor.FreeM.toWOfIsEmpty_toFreeM 2 := fun h =>
  (h (P := PE) (α := Unit) (WType.mk () (fun e => e.elim))).false ()

-- `PFunctor.W.toFreeM_toWOfIsEmpty` idx 2: necessary (α = Unit)
theorem pf21 : ¬ indep0% PFunctor.W.toFreeM_toWOfIsEmpty 2 := fun h =>
  (h (P := PU) (α := Unit) (FreeM.pure ())).false ()

-- `PFunctor.FreeM.equivWOfIsEmpty_symm_apply` idx 2: necessary (α = Unit)
theorem pf22 : ¬ indep0% PFunctor.FreeM.equivWOfIsEmpty_symm_apply 2 := fun h =>
  (h (P := PE) (α := Unit) (WType.mk () (fun e => e.elim))).false ()

-- `PFunctor.FreeM.equivWOfIsEmpty_apply` idx 2: necessary (α = Unit)
theorem pf23 : ¬ indep0% PFunctor.FreeM.equivWOfIsEmpty_apply 2 := fun h =>
  (h (P := PU) (α := Unit) (FreeM.pure ())).false ()

open Polynomial in
universe u in
-- `Polynomial.monotone_eval` idx 3: removable (IsOrderedRing follows from CanonicallyOrderedAdd)
theorem po1 : drop% Polynomial.monotone_eval 3 := by
  intro R _ _ _ p
  have : IsOrderedRing R :=
    { add_le_add_left := fun a b h c => by
        obtain ⟨d, rfl⟩ := exists_add_of_le h; rw [add_right_comm]; exact le_self_add
      zero_le_one := zero_le
      toPosMulMono := inferInstance
      toMulPosMono := inferInstance }
  exact Polynomial.monotone_eval p

open Polynomial in
-- `Polynomial.monotone_eval` idx 4: necessary (ℤ, p = -X)
theorem po2 : ¬ drop0% Polynomial.monotone_eval 4 := fun h => by
  have := h (R := ℤ) (-X) (show (0 : ℤ) ≤ 1 by decide)
  simp at this

open Polynomial in
universe u in
-- `Polynomial.eval_mono` idx 3: removable (IsOrderedRing follows from CanonicallyOrderedAdd)
theorem po3 : drop% Polynomial.eval_mono 3 := by
  intro R _ _ _ p a b hab
  have : IsOrderedRing R :=
    { add_le_add_left := fun a b h c => by
        obtain ⟨d, rfl⟩ := exists_add_of_le h; rw [add_right_comm]; exact le_self_add
      zero_le_one := zero_le
      toPosMulMono := inferInstance
      toMulPosMono := inferInstance }
  exact Polynomial.eval_mono p hab

open Polynomial in
-- `Polynomial.eval_mono` idx 4: necessary (ℤ, p = -X)
theorem po4 : ¬ drop0% Polynomial.eval_mono 4 := fun h => by
  have := h (R := ℤ) (-X) (show (0 : ℤ) ≤ 1 by decide)
  simp at this

open Polynomial in
-- `Polynomial.eval_mono` idx 8: necessary (ℕ, p = X, a = 1, b = 0)
theorem po5 : ¬ drop0% Polynomial.eval_mono 8 := fun h => by
  have := h (R := ℕ) X (a := 1) (b := 0)
  simp at this

-- `Set.saturates_eq_biUnion` idx 5: necessary (f = ∅, s = univ on Unit)
theorem sat1 : ¬ drop0% Set.saturates_eq_biUnion 5 := fun h => by
  have := h (ι := Unit) (α := Unit) (f := fun _ => ∅) (s := Set.univ) (fun _ h => by simp at h)
  have h2 := this ▸ Set.mem_univ ()
  simp at h2

end

section

namespace W3c2
open MeasureTheory Set
-- Bool with the trivial σ-algebra
def B0 : Type := Bool
instance : MeasurableSpace B0 := ⊥
instance : Finite B0 := inferInstanceAs (Finite Bool)
instance : DecidableEq B0 := inferInstanceAs (DecidableEq Bool)
def bt : B0 := true
def bf : B0 := false
end W3c2
open W3c2 MeasureTheory Set
open scoped ENNReal

-- `MeasureTheory.HasFiniteSupport.exists_finite_measure_compl_zero` idx 3: necessary (counting measure on ℕ)
theorem fs1 : ¬ drop0% MeasureTheory.HasFiniteSupport.exists_finite_measure_compl_zero 3 := fun h => by
  obtain ⟨s, hs, h0⟩ := h (α := ℕ) (μ := Measure.count)
  rw [Measure.count_eq_zero_iff, compl_empty_iff] at h0
  exact Set.infinite_univ (h0 ▸ hs)

-- `MeasureTheory.HasFiniteSupport.exists_eq_sum_smul_dirac` idx 4: necessary (counting measure on ℕ)
theorem fs2 : ¬ drop0% MeasureTheory.HasFiniteSupport.exists_eq_sum_smul_dirac 4 := fun h => by
  obtain ⟨s, hs⟩ := h (α := ℕ) Measure.count
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset s
  have := congrArg (fun μ : Measure ℕ => μ {a}) hs
  simp [Measure.dirac_apply'] at this
  exact ha this

-- `MeasureTheory.HasFiniteSupport.isFiniteMeasure` idx 3: necessary (Lebesgue measure on ℝ)
theorem fs3 : ¬ drop0% MeasureTheory.HasFiniteSupport.isFiniteMeasure 3 := fun h => by
  have := @h ℝ _ volume _
  exact (measure_lt_top (volume : Measure ℝ) univ).ne (by simp)

-- `MeasureTheory.HasFiniteSupport.isFiniteMeasure` idx 4: necessary (∞ • dirac on Unit)
theorem fs4 : ¬ drop0% MeasureTheory.HasFiniteSupport.isFiniteMeasure 4 := fun h => by
  have := @h Unit _ (∞ • Measure.dirac ()) ⟨⟨univ, finite_univ, by simp⟩⟩
  exact (measure_lt_top (∞ • Measure.dirac () : Measure Unit) univ).ne (by simp)

-- `MeasureTheory.NullMeasurableSet.of_hasFiniteSupport` idx 2: necessary (Bool with the trivial
-- σ-algebra, μ = dirac true + dirac false, t = {true})
theorem fs5 : ¬ drop0% MeasureTheory.NullMeasurableSet.of_hasFiniteSupport 2 := fun h => by
  have hn := @h B0 _ (Measure.dirac bt + Measure.dirac bf) ⟨⟨univ, finite_univ, by simp⟩⟩ {bt}
  obtain ⟨T, hsub, hT, hae⟩ := hn.exists_measurable_superset_ae_eq
  rcases MeasurableSpace.measurableSet_bot_iff.mp hT with rfl | rfl
  · exact hsub rfl
  · rw [ae_eq_set] at hae
    have e : (univ \ {bt} : Set B0) = {bf} := by
      change (univ \ {true} : Set Bool) = {false}; ext x; cases x <;> simp
    have h1 := hae.1
    rw [e, Measure.coe_add, Pi.add_apply, Measure.dirac_apply_of_mem (a := bf) (s := {bf}) rfl]
      at h1
    simp at h1

end

section

namespace W3c2
open MeasureTheory Set
-- product measure of a null cylinder is null, without σ-finiteness
theorem piCylNull {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) (i : ι) {s : Set (X i)} (hs : μ i s = 0) :
    Measure.pi μ (Function.eval i ⁻¹' s) = 0 := by
  classical
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, htm, hμt⟩
  refine measure_mono_null (preimage_mono hst) ?_
  rw [← univ_pi_update_univ]
  have hm : MeasurableSet (pi univ (Function.update (fun j => (univ : Set (X j))) i t)) := by
    rw [univ_pi_update_univ]; exact measurable_pi_apply i htm
  rw [Measure.pi, toMeasure_apply _ _ hm]
  refine le_antisymm ((OuterMeasure.pi_pi_le _ _).trans ?_) zero_le
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hμt])]
end W3c2
open W3c2 MeasureTheory Set

universe u_1 u_2 in
-- `MeasureTheory.instHasFiniteSupportForallPiOfIsFiniteMeasure` idx 6: removable (a null cylinder
-- has product measure 0 by the outer-measure bound, no σ-finiteness needed)
theorem fs7 : drop% MeasureTheory.instHasFiniteSupportForallPiOfIsFiniteMeasure 6 := by
  intro ι _ X _ μ _
  refine ⟨?_⟩
  choose s hs hμ using fun i => HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ i)
  refine ⟨univ.pi s, Finite.pi hs, ?_⟩
  refine measure_mono_null ?_ (measure_iUnion_null fun i => piCylNull μ i (hμ i))
  intro f hf
  simpa using hf

namespace W3c2
-- ℕ with the trivial σ-algebra
def N0 : Type := ℕ
instance : MeasurableSpace N0 := ⊥
instance : Infinite N0 := inferInstanceAs (Infinite ℕ)
def n0 : N0 := (0 : ℕ)
end W3c2

-- `MeasureTheory.instHasFiniteSupportForallPiOfIsFiniteMeasure` idx 5: necessary (ι = Unit,
-- ℕ with the trivial σ-algebra, μ = dirac 0: finite, but every nonempty set has measure 1)
theorem fs8 : ¬ drop0% MeasureTheory.instHasFiniteSupportForallPiOfIsFiniteMeasure 5 := fun h => by
  have hfs := @h Unit _ (fun _ => N0) (fun _ => inferInstance) (fun _ => Measure.dirac n0) _
  obtain ⟨S, hS, h0⟩ := hfs.exists_finite_measure_compl_zero
  have : Infinite (Unit → N0) := Infinite.of_injective (fun n (_ : Unit) => n) (fun a b h => congrFun h ())
  obtain ⟨f, hf⟩ := hS.infinite_compl.nonempty
  have hT := measurableSet_toMeasurable (Measure.pi fun _ : Unit => Measure.dirac n0) Sᶜ
  have hbot : (MeasurableSpace.pi : MeasurableSpace (Unit → N0)) = ⊥ := by
    show ⨆ a : Unit, MeasurableSpace.comap (fun b : Unit → N0 => b a) (⊥ : MeasurableSpace N0) = ⊥
    simp [MeasurableSpace.comap_bot]
  have hT' : @MeasurableSet _ ⊥ (toMeasurable (Measure.pi fun _ : Unit => Measure.dirac n0) Sᶜ) := by
    rw [← hbot]; exact hT
  rcases MeasurableSpace.measurableSet_bot_iff.mp hT' with he | he
  · have := subset_toMeasurable (Measure.pi fun _ : Unit => Measure.dirac n0) Sᶜ hf
    rw [he] at this; exact this
  · rw [← measure_toMeasurable, he, Measure.pi_univ] at h0
    simp at h0

namespace W3c2
-- Bool × Set ℕ with the countable/cocountable σ-algebra (singletons measurable)
def CC : Type := Bool × Set ℕ
instance ccMS : MeasurableSpace CC where
  MeasurableSet' s := s.Countable ∨ sᶜ.Countable
  measurableSet_empty := Or.inl countable_empty
  measurableSet_compl s h := by
    rcases h with h | h
    · exact Or.inr (by simpa using h)
    · exact Or.inl h
  measurableSet_iUnion f hf := by
    by_cases H : ∀ i, (f i).Countable
    · exact Or.inl (countable_iUnion H)
    · simp only [not_forall] at H
      obtain ⟨i, hi⟩ := H
      exact Or.inr (((hf i).resolve_left hi).mono (compl_subset_compl.mpr (subset_iUnion f i)))
instance : MeasurableSingletonClass CC := ⟨fun x => Or.inl (countable_singleton (x : Bool × Set ℕ))⟩
-- the half {x | x.1 = b} is uncountable
theorem ccHalf (b : Bool) : ¬ ({x : CC | (x : Bool × Set ℕ).1 = b} : Set CC).Countable := fun hc => by
  have hsub : (univ : Set (Set ℕ)) ⊆
      (fun x : CC => (x : Bool × Set ℕ).2) '' {x : CC | (x : Bool × Set ℕ).1 = b} :=
    fun r _ => ⟨((b, r) : Bool × Set ℕ), rfl, rfl⟩
  have h2 : (univ : Set (Set ℕ)).Countable := (hc.image _).mono hsub
  obtain ⟨f, hf⟩ := @exists_surjective_nat (Set ℕ) _ (Set.countable_univ_iff.mp h2)
  exact Function.cantor_surjective f hf
end W3c2

-- `MeasureTheory.NullMeasurableSet.of_hasFiniteSupport` idx 4: necessary (Bool × Set ℕ with the
-- countable/cocountable σ-algebra and counting measure; the half {x | x.1 = true} is not null-measurable)
theorem fs9 : ¬ drop0% MeasureTheory.NullMeasurableSet.of_hasFiniteSupport 4 := fun h => by
  have hn := h (α := CC) (μ := Measure.count) {x : CC | (x : Bool × Set ℕ).1 = true}
  obtain ⟨T, hsub, hT, hae⟩ := hn.exists_measurable_superset_ae_eq
  change T.Countable ∨ Tᶜ.Countable at hT
  rcases hT with hT | hT
  · exact ccHalf true (hT.mono hsub)
  · rw [ae_eq_set] at hae
    have h1 := Measure.count_eq_zero_iff.mp hae.1
    rw [sdiff_eq_empty] at h1
    refine ccHalf false (hT.mono ?_)
    intro x hx hxT
    have := h1 hxT
    simp only [mem_setOf_eq] at hx this
    rw [hx] at this; exact Bool.false_ne_true this

end

section

namespace W3c2
open MeasureTheory Set

-- inside a finite measurable set G, the point a0 has a minimal measurable neighbourhood A ⊆ G
theorem atomEx {α : Type*} [MeasurableSpace α] (G : Finset α) (a0 : α) (ha : a0 ∈ G)
    (hG : MeasurableSet (G : Set α)) :
    ∃ A : Finset α, A ⊆ G ∧ a0 ∈ A ∧ MeasurableSet (A : Set α) ∧ ∀ T, MeasurableSet T →
      (a0 ∈ T → (A : Set α) ⊆ T) ∧ (a0 ∉ T → Disjoint (A : Set α) T) := by
  classical
  obtain ⟨A, hA, hmin⟩ := (G.powerset.filter (fun A : Finset α => a0 ∈ A ∧ MeasurableSet (A : Set α))).exists_min_image
    Finset.card ⟨G, by simp [ha, hG]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA hmin
  refine ⟨A, hA.1, hA.2.1, hA.2.2, fun T hT => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hc := hmin (A.filter (· ∈ T)) ⟨(Finset.filter_subset _ _).trans hA.1,
      by simp [hA.2.1, h], by rw [Finset.coe_filter]; exact hA.2.2.inter hT⟩
    have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ A) hc
    intro x hx
    have : x ∈ A.filter (· ∈ T) := by rw [heq]; exact hx
    exact (Finset.mem_filter.mp this).2
  · have hc := hmin (A.filter (· ∉ T)) ⟨(Finset.filter_subset _ _).trans hA.1,
      by simp [hA.2.1, h], by rw [Finset.coe_filter]; exact hA.2.2.diff hT⟩
    have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ A) hc
    refine Set.disjoint_left.mpr fun x hx hxT => ?_
    have : x ∈ A.filter (· ∉ T) := by rw [heq]; exact hx
    exact (Finset.mem_filter.mp this).2 hxT

-- a measure concentrated on a finite measurable set is a weighted sum of Dirac masses
theorem fsSum {α : Type*} [MeasurableSpace α] (G : Finset α) : ∀ (μ : Measure α),
    MeasurableSet (G : Set α) → μ (G : Set α)ᶜ = 0 →
    ∃ s ⊆ G, ∀ T, MeasurableSet T → μ T = ∑ a ∈ s, μ {a} * T.indicator 1 a := by
  classical
  induction G using Finset.strongInduction with
  | H G ih =>
  intro μ hG h0
  rcases G.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
  · refine ⟨∅, Finset.empty_subset _, fun T _ => ?_⟩
    simp only [Finset.coe_empty, compl_empty] at h0
    simp [measure_mono_null (subset_univ T) h0]
  · obtain ⟨A, hAG, haA, hAm, hAT⟩ := atomEx G a0 ha0 hG
    have hG'm : MeasurableSet ((G \ A : Finset α) : Set α) := by
      rw [Finset.coe_sdiff]; exact hG.diff hAm
    have hlt : G \ A ⊂ G := Finset.sdiff_ssubset hAG ⟨a0, haA⟩
    obtain ⟨s', hs'G, hs'⟩ := ih (G \ A) hlt (μ.restrict ((G \ A : Finset α) : Set α)) hG'm
      (by rw [Measure.restrict_apply' hG'm]; simp)
    refine ⟨insert a0 s', Finset.insert_subset ha0 (hs'G.trans Finset.sdiff_subset), fun T hT => ?_⟩
    have ha0s' : a0 ∉ s' := fun h => (Finset.mem_sdiff.mp (hs'G h)).2 haA
    rw [Finset.sum_insert ha0s']
    have hGu : (G : Set α) = (A : Set α) ∪ ((G \ A : Finset α) : Set α) := by
      rw [Finset.coe_sdiff, Set.union_diff_cancel (Finset.coe_subset.mpr hAG)]
    have e1 : μ T = μ (T ∩ A) + μ.restrict ((G \ A : Finset α) : Set α) T := by
      rw [Measure.restrict_apply hT, ← measure_inter_conull (s := T) h0, hGu, Set.inter_union_distrib_left]
      refine measure_union ?_ (hT.inter hG'm)
      refine Set.disjoint_left.mpr fun x hx hx' => ?_
      rw [Finset.coe_sdiff] at hx'
      exact hx'.2.2 hx.2
    have hsing : μ {a0} = μ A := by
      refine le_antisymm (measure_mono (Set.singleton_subset_iff.mpr haA)) ?_
      rw [← measure_toMeasurable {a0}]
      exact measure_mono ((hAT _ (measurableSet_toMeasurable μ {a0})).1
        (subset_toMeasurable μ {a0} rfl))
    have e2 : μ (T ∩ A) = μ {a0} * T.indicator 1 a0 := by
      by_cases h : a0 ∈ T
      · rw [Set.inter_eq_right.mpr ((hAT T hT).1 h), hsing, Set.indicator_of_mem h]; simp
      · rw [Set.inter_comm, ((hAT T hT).2 h).inter_eq, Set.indicator_of_notMem h]; simp
    have e3 : ∀ a ∈ s', μ.restrict ((G \ A : Finset α) : Set α) {a} = μ {a} := by
      intro a ha
      rw [Measure.restrict_apply' hG'm, Set.inter_eq_left.mpr
        (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr (hs'G ha)))]
    rw [e1, e2, hs' T hT]
    congr 1
    exact Finset.sum_congr rfl fun a ha => by rw [e3 a ha]
end W3c2
open W3c2 MeasureTheory Set

universe u_1 in
-- `MeasureTheory.HasFiniteSupport.exists_eq_sum_smul_dirac` idx 2: removable (shrink the finite
-- support to a finite measurable set and split off minimal measurable neighbourhoods)
theorem fs10 : drop% MeasureTheory.HasFiniteSupport.exists_eq_sum_smul_dirac 2 := by
  intro α _ μ _
  obtain ⟨F, hF, hμ⟩ := HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ)
  set N := toMeasurable μ Fᶜ
  have hNF : Nᶜ ⊆ F := Set.compl_subset_comm.mp (subset_toMeasurable μ Fᶜ)
  have hfin : (Nᶜ).Finite := hF.subset hNF
  obtain ⟨s, -, hs⟩ := fsSum hfin.toFinset μ (by rw [Set.Finite.coe_toFinset]; exact (measurableSet_toMeasurable μ Fᶜ).compl)
    (by simp [N, measure_toMeasurable, hμ])
  refine ⟨s, Measure.ext fun T hT => ?_⟩
  rw [hs T hT, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hT, smul_eq_mul]

end
