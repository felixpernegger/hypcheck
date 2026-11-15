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


/-! # A1c0: the two private applicative rows (hypothesis map_map, idx 7)

seqRight row: necessary. Model m = Id, n = Const (Function.End Bool), f sends every element of
γ to the constant map with value "γ is not a subsingleton". Constant maps are left zeros under
composition and, for nonempty α, α → β is a subsingleton iff β is, so map_seq holds; seqRight
fails at α = Bool, β = Unit.

seqLeft row (no verdict): seqLeft_of_unit_eqs proves the statement without map_map from the type
equalities (PUnit → α) = α (cast sending the constant function to its value) and
(α → PUnit) = PUnit. A Lean refutation would refute these equalities, which hold in a modified
set model (argument on paper); a set model with an ∈-recursive type weight refutes it, so the
row is likely independent. -/

namespace A1c0

open Classical in
/-- The constant map with value "γ is not a subsingleton". -/
noncomputable def cw (γ : Type) : Function.End Bool := fun _ => decide (¬ Subsingleton γ)

theorem sub_fun_iff {α β : Type} [Nonempty α] : Subsingleton (α → β) ↔ Subsingleton β := by
  refine ⟨fun h => ⟨fun b1 b2 => ?_⟩, fun h => inferInstance⟩
  exact congrFun (h.elim (fun _ => b1) (fun _ => b2)) (Classical.arbitrary α)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_seqRight_of_map_seq_map_map` idx 7: necessary (m = Id, n = Const (Function.End Bool), f = constant map "not a subsingleton"; map_seq holds, seqRight fails at Bool, Unit)
theorem msr7 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_seqRight_of_map_seq_map_map 7 := fun h => by
  have key := @h Id (Functor.Const (Function.End Bool)) _ _ _ _ (fun {γ} _ => cw γ) ?_
    Bool Unit (pure true) (fun _ => pure ())
  · have h1 : cw Unit = cw Bool * cw Unit := key
    have h2 : cw Unit true = cw Bool (cw Unit true) := congrFun h1 true
    have hb : ¬ Subsingleton Bool := fun h => Bool.false_ne_true (h.elim _ _)
    have hu : Subsingleton Unit := inferInstance
    simp [cw, hb, hu] at h2
  · intro α β x y
    have : Nonempty α := ⟨(y ()).run⟩
    change cw β = cw (α → β) * cw α
    funext b
    change cw β b = cw (α → β) (cw α b)
    simp [cw, sub_fun_iff]

/-! ## Supporting lemmas for the seqLeft row (no verdict: independent, kind type-identity) -/

/-- Non-removability half, reduced to a type weight: any c with c (A → B) = c B / c A for
nonempty A, B and c Unit ≠ 1 refutes the seqLeft row without map_map. Such a c exists in the
set-theoretic model (∈-recursion on function sets), not in Lean. -/
theorem msl7_of_weight (c : Type → Multiplicative ℤ)
    (hc : ∀ (A B : Type), Nonempty A → Nonempty B → c (A → B) = c B / c A) (hU : c Unit ≠ 1) :
    ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_seqLeft_of_map_seq_map_map 7 := fun h => by
  have key := @h Id (Functor.Const (Multiplicative ℤ)) _ _ _ _ (fun {γ} _ => c γ) ?_
    Unit Unit (pure ()) (fun _ => pure ())
  · change c Unit = c Unit * c Unit at key
    exact hU (by simpa using key.symm)
  · intro α β x y
    have hα : Nonempty α := ⟨(y ()).run⟩
    have hβ : Nonempty β := ⟨x.run (y ()).run⟩
    change c β = c (α → β) * c α
    rw [hc α β hα hβ]; simp

/-! The consistency half: T' from the unit type equalities. -/

universe u v w

section
variable {m : Type u → Type v} {n : Type u → Type w} [Applicative m] [Applicative n]
  [LawfulApplicative m] [LawfulApplicative n]

/-- Transport along a type equality commutes with any type-indexed family. -/
theorem natCast (f : ∀ {α}, m α → n α) {A B : Type u} (h : A = B) (x : m A) :
    f (cast h <$> x) = cast h <$> f x := by
  subst h
  have : (cast rfl : A → A) = id := funext fun _ => rfl
  simp [this]

/-- Given the type equalities (PUnit → α) = α and (α → PUnit) = PUnit, map_seq alone implies
the seqLeft conclusion, i.e. the seqLeft row without map_map. -/
theorem seqLeft_of_unit_eqs
    (He : ∀ α : Type u, ∃ h : (PUnit.{u+1} → α) = α, ∀ a : α, cast h (fun _ => a) = a)
    (Hk : ∀ α : Type u, (α → PUnit.{u+1}) = PUnit.{u+1})
    (f : ∀ {α}, m α → n α)
    (hs : ∀ {α β} (x : m (α → β)) (y : Unit → m α),
      f (Seq.seq x y) = Seq.seq (f x) (f <| y ·)) :
    ∀ {α β} (x : m α) (y : Unit → m β),
      f (SeqLeft.seqLeft x y) = SeqLeft.seqLeft (f x) (f <| y ·) := by
  have he : ∀ {α : Type u} (x : m α),
      f ((fun a (_ : PUnit.{u+1}) => a) <$> x) = (fun a (_ : PUnit.{u+1}) => a) <$> f x := by
    intro α x
    obtain ⟨h, hh⟩ := He α
    have : (fun a (_ : PUnit.{u+1}) => a) = cast h.symm := funext fun a => by
      have := congrArg (cast h.symm) (hh a); simpa using this
    rw [this]; exact natCast (m := m) (n := n) f h.symm x
  have hx : ∀ {α : Type u} (x : m α),
      f x = Seq.seq ((fun a (_ : PUnit.{u+1}) => a) <$> f x) (fun _ => f (pure PUnit.unit)) := by
    intro α x
    have : x = Seq.seq ((fun a (_ : PUnit.{u+1}) => a) <$> x) (fun _ => pure PUnit.unit) := by
      simp [seq_pure]
    conv_lhs => rw [this]
    rw [hs, he]
  have ht : ∀ {β : Type u} (y : m β),
      f ((fun _ => PUnit.unit.{u+1}) <$> y) =
        Seq.seq ((fun (p : PUnit.{u+1}) (_ : β) => p) <$> f (pure PUnit.unit)) (fun _ => f y) := by
    intro β y
    have e1 : (fun _ => PUnit.unit.{u+1}) <$> y =
        Seq.seq (cast (Hk β).symm <$> (pure PUnit.unit : m PUnit)) (fun _ => y) := by
      rw [map_pure, pure_seq]
    rw [e1, hs, natCast (m := m) (n := n) f (Hk β).symm]
  intro α β x y
  let y' := y (); have hy : y = fun _ => y' := rfl; clear_value y'; subst hy
  have hA : SeqLeft.seqLeft x (fun _ => y') =
      Seq.seq ((fun a (_ : PUnit.{u+1}) => a) <$> x) (fun _ => (fun _ => PUnit.unit) <$> y') := by
    simp [seqLeft_eq, seq_map_assoc, Function.comp_def]; rfl
  rw [hA, hs, he, ht]
  conv_rhs => rw [hx x]
  simp [seqLeft_eq, seq_assoc, map_seq, seq_map_assoc, Function.comp_def]
  rfl

end

end A1c0
