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

section P0

open Cslib Cslib.RelationAlgebra

namespace U1c1

/-- Z/3 as an atom structure. -/
def Z3 : AtomStructure (Fin 3) where
  conv r := -r
  id := {0}
  cycles := {x | x.1 + x.2.1 = x.2.2}
  assoc := by
    intro r q p s t
    simp only [Set.mem_setOf_eq]
    decide +revert
  id_cycle_right := by
    intro s r p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    decide +revert
  exists_id_cycle_right := by
    intro r
    exact ⟨0, rfl, by simp⟩
  cycle_left := by
    intro r s t
    simp only [Set.mem_setOf_eq]
    decide +revert

-- the integers as an atom structure (infinite)
def ZZ : AtomStructure ℤ where
  conv r := -r
  id := {0}
  cycles := {x | x.1 + x.2.1 = x.2.2}
  assoc := by
    intro r q p s t
    simp only [Set.mem_setOf_eq]
    intro h1 h2
    exact ⟨r + s, by omega, rfl⟩
  id_cycle_right := by
    intro s r p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    omega
  exists_id_cycle_right := by
    intro r
    exact ⟨0, rfl, by simp⟩
  cycle_left := by
    intro r s t
    simp only [Set.mem_setOf_eq]
    omega

end U1c1

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.assoc` idx 7: necessary (Z/3: s = t = q = 0, r = 0, p = 1)
theorem as7 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.assoc 7 := fun h => by
  have := @h (Fin 3) Z3 0 0 1 0 0 (by simp [Z3])
  obtain ⟨q', h1, h2⟩ := this
  simp only [Z3, Set.mem_setOf_eq] at h1 h2
  revert q'; decide

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.assoc` idx 8: necessary (Z/3: r = q = p = 0, s = 0, t = 1)
theorem as8 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.assoc 8 := fun h => by
  have := @h (Fin 3) Z3 0 0 0 0 1 (by simp [Z3])
  obtain ⟨q', h1, h2⟩ := this
  simp only [Z3, Set.mem_setOf_eq] at h1 h2
  revert q'; decide

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.id_cycle_right` idx 5: necessary (Z/3: s = 1, r = 0, p = 1)
theorem icr5 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.id_cycle_right 5 := fun h => by
  have := @h (Fin 3) Z3 1 0 1 (by simp [Z3])
  exact absurd this (by decide)

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.id_cycle_right` idx 6: necessary (Z/3: s = 0, r = 0, p = 1)
theorem icr6 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.id_cycle_right 6 := fun h => by
  have := @h (Fin 3) Z3 0 0 1 (by simp [Z3])
  exact absurd this (by decide)

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.cycle_left` idx 5: necessary (Z/3: r = 0, t = 0, s = 1)
theorem cl5 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.cycle_left 5 := fun h => by
  have := @h (Fin 3) Z3 0 1 0
  simp [Z3] at this

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.conv_cycles` idx 5: necessary (Z/3: r = s = 0, t = 1)
theorem cc5 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.conv_cycles 5 := fun h => by
  have := @h (Fin 3) Z3 0 0 1
  simp [Z3] at this

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.assoc_symm` idx 7: necessary (Z/3: r = s = q = 0, t = 0, p = 1)
theorem asy7 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.assoc_symm 7 := fun h => by
  have := @h (Fin 3) Z3 0 0 0 1 0 (by simp [Z3])
  obtain ⟨q', h1, h2⟩ := this
  simp only [Z3, Set.mem_setOf_eq] at h1 h2
  revert q'; decide

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.assoc_symm` idx 8: necessary (Z/3: q = t = p = 0, r = 0, s = 1)
theorem asy8 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.assoc_symm 8 := fun h => by
  have := @h (Fin 3) Z3 0 1 0 0 0 (by simp [Z3])
  obtain ⟨q', h1, h2⟩ := this
  simp only [Z3, Set.mem_setOf_eq] at h1 h2
  revert q'; decide

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.conv_eq_self_of_mem_id` idx 3: necessary (Z/3: conv 1 = 2 ≠ 1)
theorem ce3 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.conv_eq_self_of_mem_id 3 := fun h => by
  have := @h (Fin 3) Z3 1
  exact absurd this (by decide)

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.id_cycle_left` idx 5: necessary (Z/3: s = 1, r = 0, p = 1)
theorem icl5 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.id_cycle_left 5 := fun h => by
  have := @h (Fin 3) Z3 1 0 1 (by simp [Z3])
  exact absurd this (by decide)

open U1c1 in
-- `Cslib.RelationAlgebra.AtomStructure.id_cycle_left` idx 6: necessary (Z/3: s = 0, r = 0, p = 1)
theorem icl6 : ¬ drop0% Cslib.RelationAlgebra.AtomStructure.id_cycle_left 6 := fun h => by
  have := @h (Fin 3) Z3 0 0 1 (by simp [Z3])
  exact absurd this (by decide)

open U1c1 in
-- `Cslib.RelationAlgebra.ComplexAlgebra.instFinite` idx 2: necessary (integers as atom structure: Set ℤ infinite)
theorem fin2 : ¬ drop0% Cslib.RelationAlgebra.ComplexAlgebra.instFinite 2 := fun h => by
  have : Finite (ComplexAlgebra ZZ) := h ZZ
  have : Finite (Set ℤ) := Finite.of_equiv _ (ComplexAlgebra.equivSet ZZ)
  exact not_finite (Set ℤ)

open U1c1 in
-- `Cslib.RelationAlgebra.ComplexAlgebra.ext` idx 4: necessary (Z/3: ∅ ≠ univ)
theorem cext4 : ¬ drop0% Cslib.RelationAlgebra.ComplexAlgebra.ext 4 := fun h => by
  have := congrArg (fun x : ComplexAlgebra Z3 => (0 : Fin 3) ∈ x) (@h (Fin 3) Z3 ⟨∅⟩ ⟨Set.univ⟩)
  simp at this

end P0

section P1

open Cslib Cslib.RelationAlgebra

namespace U1c1

/-- Every Boolean algebra is a relation algebra with composition `⊓`, identity `⊤`, converse `id`. -/
def BA (β : Type) := β
instance BA.ba (β : Type) [h : BooleanAlgebra β] : BooleanAlgebra (BA β) := h
instance BA.inst (β : Type) [BooleanAlgebra β] : RelationAlgebra (BA β) where
  mul a b := a ⊓ b
  one := ⊤
  mul_assoc := inf_assoc
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  star := id
  star_involutive := fun _ => rfl
  star_mul := inf_comm
  sup_mul := inf_sup_right
  star_sup := fun _ _ => rfl
  tarski := fun a b => by
    show a ⊓ (a ⊓ b)ᶜ ≤ bᶜ
    rw [compl_inf, inf_sup_left, inf_compl_self, bot_sup_eq]
    exact inf_le_right

abbrev SB := BA (Set Bool)
theorem atT : IsAtom (({true} : Set Bool) : SB) := Set.isAtom_singleton true

theorem SB_not_integral : ¬ IsIntegral SB := fun h => by
  have h2 := h.2 ({true} : Set Bool) (show ({true} : Set Bool) < (1 : SB) from
    show ({true} : Set Bool) < Set.univ from by
      refine lt_of_le_of_ne (Set.subset_univ _) fun e => ?_
      have : false ∈ (Set.univ : Set Bool) := trivial
      rw [← e] at this; simp at this)
  exact absurd h2 (Set.singleton_ne_empty true)

/-- evaluation at `true`: a relation algebra hom from `SB` to the complex algebra of the trivial group -/
def evH : RelationAlgebraHom SB (ComplexAlgebra (AtomStructure.ofGroup PUnit.{1})) where
  toFun x := ⟨{_u | true ∈ (show Set Bool from x)}⟩
  map_sup' _ _ := by ext; exact Iff.rfl
  map_inf' _ _ := by ext; exact Iff.rfl
  map_top' := by ext; exact Iff.rfl
  map_bot' := by ext; exact Iff.rfl
  map_one' := by
    ext u
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => trivial⟩
  map_mul' x y := by
    ext u
    constructor
    · intro h; exact ⟨(), h.1, (), h.2, Subsingleton.elim _ _⟩
    · rintro ⟨r, hr, s, hs, _⟩; exact ⟨hr, hs⟩
  map_star' x := by
    ext u
    constructor
    · intro h; exact ⟨(), h, Subsingleton.elim _ _⟩
    · rintro ⟨r, hr, _⟩; exact hr

end U1c1

open U1c1 in
-- `Cslib.RelationAlgebra.atom_cycle_left_iff` idx 5: necessary (Set Bool with ⊓; r = s = ⊤, p = {true})
theorem acli5 : ¬ drop0% Cslib.RelationAlgebra.atom_cycle_left_iff 5 := fun H => by
  have := (@H SB _ (⊤ : Set Bool) (⊤ : Set Bool) ({true} : Set Bool) atT).1 (show _ ≤ _ from fun _ _ => ⟨trivial, trivial⟩)
  have h2 : false ∈ ({true} : Set Bool) :=
    ((show (⊤ : Set Bool) ⊆ (⊤ : Set Bool) ⊓ ({true} : Set Bool) from this) (show false ∈ (⊤ : Set Bool) from trivial)).2
  simp at h2

open U1c1 in
-- `Cslib.RelationAlgebra.atom_cycle_left_iff` idx 6: necessary (Set Bool with ⊓; p = ⊥, s = {true})
theorem acli6 : ¬ drop0% Cslib.RelationAlgebra.atom_cycle_left_iff 6 := fun H => by
  have := (@H SB _ (⊤ : Set Bool) ({true} : Set Bool) (⊥ : Set Bool) atT).1 bot_le
  have h3 : ({true} : Set Bool) ⊆ (⊤ : Set Bool) ⊓ (⊥ : Set Bool) := this
  exact (h3 (show true ∈ ({true} : Set Bool) from rfl)).2

open U1c1 in
-- `Cslib.RelationAlgebra.GroupRepresentable.of_injective` idx 5: necessary (evaluation hom SB → complex algebra of the trivial group)
theorem gri5 : ¬ drop0% Cslib.RelationAlgebra.GroupRepresentable.of_injective 5 := fun H =>
  SB_not_integral (GroupRepresentable.isIntegral
    (@H SB (ComplexAlgebra (AtomStructure.ofGroup PUnit.{1})) _ _ evH
      ⟨PUnit.{1}, inferInstance, RelationAlgebraHom.id _, fun _ _ h => h⟩))

open U1c1 in
-- `Cslib.RelationAlgebra.GroupRepresentable.of_injective` idx 6: necessary (identity hom of SB; SB is not group representable)
theorem gri6 : ¬ drop0% Cslib.RelationAlgebra.GroupRepresentable.of_injective 6 := fun H =>
  SB_not_integral (GroupRepresentable.isIntegral
    (@H SB SB _ _ (RelationAlgebraHom.id SB) (fun _ _ h => h)))

open U1c1 in
-- `Cslib.RelationAlgebra.GroupRepresentable.isIntegral` idx 2: necessary (SB is a relation algebra that is not integral)
theorem gii2 : ¬ drop0% Cslib.RelationAlgebra.GroupRepresentable.isIntegral 2 := fun H =>
  SB_not_integral (@H SB _)

open U1c1 in
-- `Cslib.RelationAlgebraHom.isIntegral_of_injective` idx 5: necessary (evaluation hom SB → complex algebra of the trivial group, not injective)
theorem hii5 : ¬ drop0% Cslib.RelationAlgebraHom.isIntegral_of_injective 5 := fun H =>
  SB_not_integral (@H SB (ComplexAlgebra (AtomStructure.ofGroup PUnit.{1})) _ _ evH
    ComplexAlgebra.isIntegral_ofGroup)

open U1c1 in
-- `Cslib.RelationAlgebraHom.isIntegral_of_injective` idx 6: necessary (identity hom of SB; SB is not integral)
theorem hii6 : ¬ drop0% Cslib.RelationAlgebraHom.isIntegral_of_injective 6 := fun H =>
  SB_not_integral (@H SB SB _ _ (RelationAlgebraHom.id SB) (fun _ _ h => h))

end P1

section P2

open Cslib Cslib.Logic Cslib.Logic.PL Cslib.Logic.PL.NaturalDeduction Cslib.Logic.InferenceSystem

namespace U1c1

/-- successor on `ℕ∞` as an order hom (its only fixed point is `⊤`) -/
def sc : ℕ∞ →o ℕ∞ := ⟨fun a => a + 1, fun a b h => by show a + 1 ≤ b + 1; gcongr⟩

theorem scTop (v : ℕ∞) (h : sc v = v) : v = ⊤ := by
  induction v using ENat.recTopCoe with
  | top => rfl
  | coe n =>
    have h' : (n : ℕ∞) + 1 = n := h
    norm_cast at h'
    omega

theorem scNe {a : ℕ∞} (ha : a ≠ ⊤) : sc a ≠ ⊤ := by
  show a + 1 ≠ ⊤
  simpa using ha

/-- sSup on `Prop` -/
theorem pSup (s : Set Prop) (h : ∀ a ∈ s, ¬ a) : ¬ sSup s := fun ⟨a, ha, h'⟩ => h a ha h'

theorem pSupD (s : Set Propᵒᵈ) (h : ∀ a ∈ s, ¬ OrderDual.ofDual a) : ¬ OrderDual.ofDual (sInf s) :=
  fun ⟨a, ha, h'⟩ => h a ha h'

abbrev PU := Proposition Unit
abbrev E0 : Set PU := ∅

/-- Boolean (Prop-valued) reading of propositions. -/
def ev {Atom : Type} (v : Atom → Prop) : Proposition Atom → Prop
  | .atom x => v x
  | .falsum => False
  | .and a b => ev v a ∧ ev v b
  | .or a b => ev v a ∨ ev v b
  | .imp a b => ev v a → ev v b

/-- soundness of natural deduction for the reading `ev v` -/
theorem sound {Atom : Type} [DecidableEq Atom] {T : Set (Proposition Atom)} {Γ : Ctx Atom}
    {A : Proposition Atom} (v : Atom → Prop) (D : Derivation T Γ A) (hT : ∀ B ∈ T, ev v B) :
    (∀ B ∈ Γ, ev v B) → ev v A := by
  induction D with
  | ax h => exact fun _ => hT _ h
  | ass h => exact fun hΓ => hΓ _ h
  | efq A D ih => exact fun hΓ => (ih hΓ).elim
  | andI _ _ ih1 ih2 => exact fun hΓ => (show _ ∧ _ from ⟨ih1 hΓ, ih2 hΓ⟩)
  | andE₁ _ ih => exact fun hΓ => (show _ ∧ _ from ih hΓ).1
  | andE₂ _ ih => exact fun hΓ => (show _ ∧ _ from ih hΓ).2
  | orI₁ _ ih => exact fun hΓ => (show _ ∨ _ from Or.inl (ih hΓ))
  | orI₂ _ ih => exact fun hΓ => (show _ ∨ _ from Or.inr (ih hΓ))
  | orE _ _ _ ih ih1 ih2 =>
    intro hΓ
    rcases (show _ ∨ _ from ih hΓ) with h | h
    · exact ih1 fun B hB => by
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact h
        · exact hΓ _ hB
    · exact ih2 fun B hB => by
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact h
        · exact hΓ _ hB
  | impI Γ _ ih =>
    exact fun hΓ => (show _ → _ from fun h => ih fun B hB => by
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact h
        · exact hΓ _ hB)
  | impE _ _ ih1 ih2 => exact fun hΓ => (show _ → _ from ih1 hΓ) (ih2 hΓ)

theorem sound' {Atom : Type} [DecidableEq Atom] {T : Set (Proposition Atom)} {Γ : Ctx Atom}
    {A : Proposition Atom} (v : Atom → Prop) (h : DerivableIn (ND T) (Γ, A))
    (hT : ∀ B ∈ T, ev v B) (hΓ : ∀ B ∈ Γ, ev v B) : ev v A :=
  let ⟨D⟩ := h; sound v D hT hΓ

/-- `⊢ ⊥` is not derivable without axioms -/
theorem noBot (h : DerivableIn (ND E0) ((∅ : Ctx Unit), (⊥ : PU))) : False :=
  sound' (fun _ => False) h (by simp) (by simp)

end U1c1

open U1c1 in
-- `OrderHom.nextFixed_le_of_map_le` idx 6: necessary (Bool, f = id, x = true, y = false)
theorem fp6 : ¬ drop0% OrderHom.nextFixed_le_of_map_le 6 := fun h => by
  have := @h Bool _ OrderHom.id true false le_rfl (le_refl false)
  have h2 := (OrderHom.id : Bool →o Bool).le_nextFixed (x := true) le_rfl
  exact absurd (h2.trans this) (by decide)

open U1c1 in
-- `OrderHom.nextFixed_le_of_map_le` idx 7: necessary (Bool, f = const true, x = y = false: fixed point is true)
theorem fp7 : ¬ drop0% OrderHom.nextFixed_le_of_map_le 7 := fun h => by
  let f : Bool →o Bool := OrderHom.const Bool true
  have := @h Bool _ f false false (by decide) le_rfl
  have h2 : (f.nextFixed false (by decide)).1 = true := (f.nextFixed false (by decide)).2.symm
  rw [h2] at this
  exact absurd this (by decide)

open U1c1 in
-- `OrderHom.le_prevFixed_of_map_ge` idx 6: necessary (Bool, f = id, x = false, y = true)
theorem fp8 : ¬ drop0% OrderHom.le_prevFixed_of_map_ge 6 := fun h => by
  have := @h Bool _ OrderHom.id false true le_rfl le_rfl
  have h2 := (OrderHom.id : Bool →o Bool).prevFixed_le (x := false) le_rfl
  exact absurd (this.trans h2) (by decide)

open U1c1 in
-- `OrderHom.le_prevFixed_of_map_ge` idx 7: necessary (Bool, f = const false, x = y = true: fixed point is false)
theorem fp9 : ¬ drop0% OrderHom.le_prevFixed_of_map_ge 7 := fun h => by
  let f : Bool →o Bool := OrderHom.const Bool false
  have := @h Bool _ f true true (by decide) le_rfl
  have h2 : (f.prevFixed true (by decide)).1 = false := (f.prevFixed true (by decide)).2.symm
  rw [h2] at this
  exact absurd this (by decide)

open U1c1 in
-- `OrderHom.nextFixed_induction` idx 6: necessary (Prop, f = id, x = True, p = ¬·)
theorem ni6 : ¬ drop0% OrderHom.nextFixed_induction 6 := fun h => by
  have := @h Prop _ OrderHom.id True le_rfl (fun a => ¬ a) (fun _ h _ _ => h) pSup
  exact this ((OrderHom.id : Prop →o Prop).le_nextFixed (x := True) le_rfl trivial)

open U1c1 in
-- `OrderHom.nextFixed_induction` idx 7: necessary (Prop, f = const True, x = False, p = ¬·)
theorem ni7 : ¬ drop0% OrderHom.nextFixed_induction 7 := fun h => by
  let f : Prop →o Prop := OrderHom.const Prop True
  have := @h Prop _ f False (fun hF => hF.elim) (fun a => ¬ a) (fun h => h) pSup
  have h2 : (f.nextFixed False (fun hF => hF.elim)).1 = True := (f.nextFixed False _).2.symm
  rw [h2] at this
  exact this trivial

open U1c1 in
-- `OrderHom.nextFixed_induction` idx 8: necessary (ℕ∞, f = succ, x = 0, p a = a ≠ ⊤)
theorem ni8 : ¬ drop0% OrderHom.nextFixed_induction 8 := fun h => by
  have := @h ℕ∞ _ sc 0 (zero_le) (fun a => a ≠ ⊤) (by simp)
    (fun a ha _ _ => scNe ha)
  exact this (scTop _ (sc.nextFixed 0 (zero_le)).2)

open U1c1 in
-- `OrderHom.prevFixed_induction` idx 6: necessary (Propᵒᵈ, f = id, x = True, p = ¬ ofDual)
theorem pi6 : ¬ drop0% OrderHom.prevFixed_induction 6 := fun h => by
  have := @h Propᵒᵈ _ OrderHom.id (OrderDual.toDual True) le_rfl (fun a => ¬ OrderDual.ofDual a)
    (fun _ h _ _ => h) pSupD
  have h3 : ((OrderHom.id : Propᵒᵈ →o Propᵒᵈ).prevFixed (OrderDual.toDual True) le_rfl).1 ≤ OrderDual.toDual True :=
    (OrderHom.id : Propᵒᵈ →o Propᵒᵈ).prevFixed_le le_rfl
  exact this ((show True ≤ _ from h3) trivial)

open U1c1 in
-- `OrderHom.prevFixed_induction` idx 7: necessary (Propᵒᵈ, f = const True, x = False)
theorem pi7 : ¬ drop0% OrderHom.prevFixed_induction 7 := fun h => by
  let f : Propᵒᵈ →o Propᵒᵈ := OrderHom.const _ (OrderDual.toDual True)
  have hx : f (OrderDual.toDual False) ≤ OrderDual.toDual False := fun _ => trivial
  have := @h Propᵒᵈ _ f (OrderDual.toDual False) hx (fun a => ¬ OrderDual.ofDual a) (fun hF => hF) pSupD
  have h2 : (f.prevFixed (OrderDual.toDual False) hx).1 = OrderDual.toDual True := (f.prevFixed _ hx).2.symm
  rw [h2] at this
  exact this trivial

open U1c1 in
-- `OrderHom.prevFixed_induction` idx 8: necessary ((ℕ∞)ᵒᵈ, f = succ dual, x = 0, p a = ofDual a ≠ ⊤)
theorem pi8 : ¬ drop0% OrderHom.prevFixed_induction 8 := fun h => by
  have := @h ℕ∞ᵒᵈ _ (OrderHom.dual sc) (OrderDual.toDual 0) (show (0:ℕ∞) ≤ sc 0 from zero_le) (fun a => OrderDual.ofDual a ≠ ⊤) (by simp)
    (fun a ha _ _ => scNe (a := OrderDual.ofDual a) ha)
  exact this (scTop _ (OrderHom.dual sc |>.prevFixed (OrderDual.toDual 0) (show (0:ℕ∞) ≤ sc 0 from zero_le)).2)

-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_collect_ax` idx 5: necessary (T = Γ = ∅, B = ⊥)
theorem nd5 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_collect_ax 5 := fun h => by
  obtain ⟨Δ, hD, hs⟩ := @h Unit _ ∅ ∅ ⊥
  have : Δ = ∅ := Finset.eq_empty_of_forall_notMem fun a ha => hs ha
  subst this
  exact U1c1.noBot (by simpa using hD)

-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_ass_to_ax` idx 6: necessary (T = Γ = Δ = ∅, B = ⊥)
theorem nd6 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_ass_to_ax 6 := fun h => by
  have := @h Unit _ ∅ ∅ ∅ ⊥
  rw [Finset.coe_empty, Set.union_empty] at this
  exact U1c1.noBot this

-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_ax_to_ass` idx 6: necessary (T = Γ = Δ = ∅, B = ⊥)
theorem nd7 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_ax_to_ass 6 := fun h =>
  U1c1.noBot (by simpa using @h Unit _ ∅ ∅ ∅ ⊥)

end P2
