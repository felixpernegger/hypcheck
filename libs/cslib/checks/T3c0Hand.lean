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

/-! ## McKenzie's relation algebra is not representable (T3c0)

Atoms `0 = 1'`, `1 = <`, `2 = >` (converse of `<`), `3 = ]` (symmetric, "incomparable"); composition
`<;< = <`, `<;> = >;< = 1`, `<;] = ];< = < + ]`, `>;] = ];> = > + ]`, `];] = −]` (R. McKenzie, 1970; the
algebra 14_37 in Maddux's list). In a representation on one set, `<` is a transitive relation `L`, `]` a
symmetric relation `C` disjoint from `L` without `C`-triangles, every `L`-edge has a common `C`-neighbour,
every `C`-edge a common `L`-upper bound, and any two points are equal, `L`-related or `C`-related; these
facts are contradictory (`noRepSet`). A representation over a product gives one on the component where
`]` is nonempty (`notRep`). -/

section T3c0
open Cslib Cslib.RelationAlgebra

namespace T3c0

/-- `t ≤ r ; s` for the atoms of McKenzie's algebra. -/
def cyc : Fin 4 → Fin 4 → Fin 4 → Bool
  | 0, s, t => t == s
  | r, 0, t => t == r
  | 1, 1, t => t == 1
  | 1, 2, _ => true
  | 1, 3, t => t == 1 || t == 3
  | 2, 1, _ => true
  | 2, 2, t => t == 2
  | 2, 3, t => t == 2 || t == 3
  | 3, 1, t => t == 1 || t == 3
  | 3, 2, t => t == 2 || t == 3
  | 3, 3, t => t != 3
  | _, _, _ => false

/-- Converse: swaps `<` and `>`. -/
def cnv : Fin 4 → Fin 4
  | 1 => 2
  | 2 => 1
  | r => r

/-- McKenzie's algebra as an atom structure. -/
def McK : AtomStructure (Fin 4) where
  conv := cnv
  id := {0}
  cycles := {x | cyc x.1 x.2.1 x.2.2 = true}
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
    exact ⟨0, rfl, by revert r; decide⟩
  cycle_left := by
    intro r s t
    simp only [Set.mem_setOf_eq]
    decide +revert

abbrev M := ComplexAlgebra McK
def L : M := ⟨{1}⟩
def C : M := ⟨{3}⟩

theorem mem_cyc {r s t : Fin 4} : (r, s, t) ∈ McK.cycles ↔ cyc r s t = true := .rfl
theorem mem_L {t : Fin 4} : t ∈ L ↔ t = 1 := .rfl
theorem mem_C {t : Fin 4} : t ∈ C ↔ t = 3 := .rfl
theorem mem_inf' {x y : M} {t : Fin 4} : t ∈ x ⊓ y ↔ t ∈ x ∧ t ∈ y := .rfl
theorem not_mem_bot' {t : Fin 4} : t ∉ (⊥ : M) := fun h => h
theorem mem_top' {t : Fin 4} : t ∈ (⊤ : M) := trivial
theorem leI {x y : M} (h : ∀ t, t ∈ x → t ∈ y) : x ≤ y := h
theorem mem_one' {t : Fin 4} : t ∈ (1 : M) ↔ t = 0 := .rfl
theorem mem_star' {x : M} {t : Fin 4} : t ∈ star x ↔ cnv t ∈ x := ComplexAlgebra.mem_star

theorem LL : L * L ≤ L := leI fun t => by
  simp only [ComplexAlgebra.mem_mul, mem_L, mem_cyc, exists_eq_left]; revert t; decide
theorem CCC : C * C ⊓ C = ⊥ := by
  ext t
  simp only [mem_inf', ComplexAlgebra.mem_mul, mem_C, mem_cyc, exists_eq_left]
  exact ⟨fun ⟨h, e⟩ => by subst e; exact absurd h (by decide), fun h => absurd h not_mem_bot'⟩
theorem LCC : L ≤ C * C := leI fun t => by
  simp only [ComplexAlgebra.mem_mul, mem_L, mem_C, mem_cyc, exists_eq_left]; revert t; decide
theorem CLG : C ≤ L * star L := leI fun t => by
  simp only [ComplexAlgebra.mem_mul, mem_star', mem_L, mem_C, mem_cyc]
  rintro rfl; exact ⟨1, rfl, 2, rfl, rfl⟩
theorem CC : star C = C := by
  ext t; simp only [mem_star', mem_C]; revert t; decide
theorem LC : L ⊓ C = ⊥ := by
  ext t; simp only [mem_inf', mem_L, mem_C]
  exact ⟨fun ⟨h, e⟩ => absurd (h.symm.trans e) (by decide), fun h => absurd h not_mem_bot'⟩
theorem cover : 1 ⊔ L ⊔ star L ⊔ C = ⊤ := by
  ext t; simp only [ComplexAlgebra.mem_sup, mem_one', mem_star', mem_L, mem_C]
  exact ⟨fun _ => mem_top', fun _ => by clear * -; revert t; decide⟩
theorem C_ne_bot : C ≠ ⊥ := fun h => not_mem_bot' (h ▸ (mem_C.mpr rfl : (3 : Fin 4) ∈ C))

/-- No representation on a single set in which `]` is nonempty. -/
theorem noRepSet {X : Type*} (φ : RelationAlgebraHom M (SetRel X X)) (hC : φ C ≠ ⊥) : False := by
  have mul : ∀ (a b : M) (x z : X), (x, z) ∈ φ (a * b) ↔ ∃ y, (x, y) ∈ φ a ∧ (y, z) ∈ φ b := by
    intro a b x z; rw [map_mul]; rfl
  have st : ∀ (a : M) (x z : X), (x, z) ∈ φ (star a) ↔ (z, x) ∈ φ a := by
    intro a x z; rw [map_star]; rfl
  have le : ∀ (a b : M), a ≤ b → ∀ p, p ∈ φ a → p ∈ φ b := by
    intro a b h p hp
    have e := congrArg φ (sup_eq_right.mpr h)
    rw [map_sup] at e
    exact e ▸ Or.inl hp
  have bot : ∀ (a b : M), a ⊓ b = ⊥ → ∀ p, p ∈ φ a → p ∈ φ b → False := by
    intro a b h p ha hb
    have e := congrArg φ h
    rw [map_inf, map_bot] at e
    have : p ∈ (φ a ⊓ φ b) := ⟨ha, hb⟩
    rw [e] at this; exact this
  -- the facts about `L` and `C` in the representation
  have trans : ∀ x y z, (x, y) ∈ φ L → (y, z) ∈ φ L → (x, z) ∈ φ L :=
    fun x y z h1 h2 => le _ _ LL _ ((mul _ _ _ _).mpr ⟨y, h1, h2⟩)
  have noTri : ∀ x y z, (x, y) ∈ φ C → (y, z) ∈ φ C → (x, z) ∈ φ C → False :=
    fun x y z h1 h2 h3 => bot _ _ CCC _ ((mul _ _ _ _).mpr ⟨y, h1, h2⟩) h3
  have disj : ∀ x z, (x, z) ∈ φ L → (x, z) ∈ φ C → False := fun x z => bot _ _ LC _
  have symm : ∀ x z, (x, z) ∈ φ C → (z, x) ∈ φ C := fun x z h => by
    rw [← CC] at h; exact (st _ _ _).mp h
  have nbr : ∀ x z, (x, z) ∈ φ L → ∃ y, (x, y) ∈ φ C ∧ (y, z) ∈ φ C :=
    fun x z h => (mul _ _ _ _).mp (le _ _ LCC _ h)
  have up : ∀ x z, (x, z) ∈ φ C → ∃ y, (x, y) ∈ φ L ∧ (z, y) ∈ φ L := fun x z h => by
    obtain ⟨y, h1, h2⟩ := (mul _ _ _ _).mp (le _ _ CLG _ h)
    exact ⟨y, h1, (st _ _ _).mp h2⟩
  have tot : ∀ x z, x = z ∨ (x, z) ∈ φ L ∨ (z, x) ∈ φ L ∨ (x, z) ∈ φ C := by
    intro x z
    have h : (x, z) ∈ φ (1 ⊔ L ⊔ star L ⊔ C) := by rw [cover, map_top]; trivial
    simp only [map_sup, map_one] at h
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ((st _ _ _).mp h)))
    · exact Or.inr (Or.inr (Or.inr h))
  -- the contradiction
  obtain ⟨⟨x, z⟩, hxz⟩ : ∃ p, p ∈ φ C := by
    by_contra hh; push Not at hh; exact hC (Set.eq_empty_iff_forall_notMem.mpr hh)
  obtain ⟨y, hxy, hzy⟩ := up x z hxz
  obtain ⟨w, hxw, hwy⟩ := nbr x y hxy
  obtain ⟨w', hzw', hw'y⟩ := nbr z y hzy
  have hzw : (z, w) ∈ φ L := by
    rcases tot z w with rfl | h | h | h
    · exact (disj _ _ hzy hwy).elim
    · exact h
    · exact (disj _ _ (trans _ _ _ h hzy) hwy).elim
    · exact (noTri _ _ _ (symm _ _ hxz) hxw h).elim
  have hxw' : (x, w') ∈ φ L := by
    rcases tot x w' with rfl | h | h | h
    · exact (disj _ _ hxy hw'y).elim
    · exact h
    · exact (disj _ _ (trans _ _ _ h hxy) hw'y).elim
    · exact (noTri _ _ _ hxz hzw' h).elim
  rcases tot w w' with rfl | h | h | h
  · exact disj _ _ hzw hzw'
  · exact disj _ _ (trans _ _ _ hzw h) hzw'
  · exact disj _ _ (trans _ _ _ hxw' h) hxw
  · exact noTri _ _ _ hwy (symm _ _ hw'y) h

/-- McKenzie's algebra is not representable. -/
theorem notRep : ¬ Representable M := by
  rintro ⟨ι, β, ⟨r⟩⟩
  obtain ⟨i, hi⟩ : ∃ i, r.hom C i ≠ ⊥ := by
    by_contra hh; push_neg at hh
    exact C_ne_bot (r.injective (by rw [map_bot]; exact funext hh))
  exact noRepSet ((RelationAlgebraHom.eval (fun i => SetRel (β i) (β i)) i).comp r.hom) hi

/-- A representable algebra that every relation algebra maps to: the empty product. -/
abbrev P0 := ∀ _ : PEmpty.{1}, SetRel PUnit.{1} PUnit.{1}
theorem P0rep : Representable P0 :=
  ⟨PEmpty, fun _ => PUnit, ⟨⟨RelationAlgebraHom.id _, Function.injective_id⟩⟩⟩
def toP0 : RelationAlgebraHom M P0 := RelationAlgebraHom.pi fun i => i.elim

end T3c0
open T3c0

-- `Cslib.RelationAlgebra.GroupRepresentable.representable` idx 2: necessary (McKenzie's algebra is not representable)
theorem grr2 : ¬ drop0% Cslib.RelationAlgebra.GroupRepresentable.representable 2 := fun h =>
  notRep (h (α := M))

-- `Cslib.RelationAlgebra.Representable.of_injective` idx 6: necessary (f = id on McKenzie's algebra)
theorem roi6 : ¬ drop0% Cslib.RelationAlgebra.Representable.of_injective 6 := fun h =>
  notRep (h (RelationAlgebraHom.id M) Function.injective_id)

-- `Cslib.RelationAlgebra.Representable.of_injective` idx 5: necessary (McKenzie's algebra to the one-point algebra)
theorem roi5 : ¬ drop0% Cslib.RelationAlgebra.Representable.of_injective 5 := fun h =>
  notRep (h toP0 P0rep)

end T3c0
