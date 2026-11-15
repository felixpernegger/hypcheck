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

set_option warn.classDefReducibility false

namespace W1c2

-- Broken instances on `Option` (one operation returns `none`), and the tick model on `OS`.
/-- type synonym of `Option` carrying the broken instances (so that instance synthesis cannot
replace them by the standard ones) -/
def BO : Type → Type := Option
abbrev bF : Functor BO := ({ map := fun _ _ => none, mapConst := fun _ _ => none } : Functor Option)
abbrev bFc : Functor BO := ({ map := Option.map, mapConst := fun _ _ => none } : Functor Option)
abbrev bAmap : Applicative BO :=
  ({ (inferInstance : Applicative Option) with map := fun _ _ => none } : Applicative Option)
abbrev bAsl : Applicative BO :=
  ({ (inferInstance : Applicative Option) with seqLeft := fun _ _ => none } : Applicative Option)
abbrev bAsr : Applicative BO :=
  ({ (inferInstance : Applicative Option) with seqRight := fun _ _ => none } : Applicative Option)
abbrev bMmap : Monad BO := ({ (inferInstance : Monad Option) with map := fun _ _ => none } : Monad Option)
abbrev bMseq : Monad BO := ({ (inferInstance : Monad Option) with seq := fun _ _ => none } : Monad Option)
abbrev bAltmap : Alternative BO :=
  ({ (inferInstance : Alternative Option) with map := fun _ _ => none } : Alternative Option)
abbrev bAltOr : Alternative BO :=
  ({ (inferInstance : Alternative Option) with orElse := fun _ _ => none } : Alternative Option)
abbrev bAMmap : AlternativeMonad BO :=
  ({ (inferInstance : AlternativeMonad Option) with map := fun _ _ => none } : AlternativeMonad Option)
abbrev bAMOr : AlternativeMonad BO :=
  ({ (inferInstance : AlternativeMonad Option) with orElse := fun _ _ => none } : AlternativeMonad Option)
abbrev OS := OptionT (StateM ℕ)
abbrev sF : Functor Option := inferInstance
abbrev sA : Applicative Option := inferInstance
abbrev sM : Monad Option := inferInstance
abbrev sAlt : Alternative Option := inferInstance
abbrev sAM : AlternativeMonad Option := inferInstance
abbrev oA : Applicative OS := inferInstance
abbrev oM : Monad OS := inferInstance
abbrev oAlt : Alternative OS := inferInstance
abbrev oAM : AlternativeMonad OS := inferInstance
def tick {α : Type} (x : Option α) : OS α := OptionT.mk (do modify (· + 1); pure x)
/-- final state of a run from 0 -/
def ev {α : Type} (x : OS α) : ℕ := (x.run.run 0).2
/-- result of a run from 0 -/
def evr {α : Type} (x : OS α) : Option α := (x.run.run 0).1
def BS : Type → Type := OS
abbrev bAltFail : Alternative BS := ({ (inferInstance : Alternative OS) with failure := tick none } : Alternative OS)
abbrev bAMFail : AlternativeMonad BS :=
  ({ (inferInstance : AlternativeMonad OS) with failure := tick none } : AlternativeMonad OS)
abbrev bAltOrOS : Alternative BS :=
  ({ (inferInstance : Alternative OS) with orElse := fun _ _ => failure } : Alternative OS)
abbrev bAMOrOS : AlternativeMonad BS :=
  ({ (inferInstance : AlternativeMonad OS) with orElse := fun _ _ => failure } : AlternativeMonad OS)
def tk : OS Unit := OptionT.mk (do modify (· + 1); pure (some ()))
def tkid : OS (ℕ → ℕ) := OptionT.mk (do modify (· + 1); pure (some id))
def gt : OS ℕ := OptionT.mk (do let s ← get; pure (some s))
theorem tick_map {α β : Type} (g : α → β) (x : Option α) : tick (g <$> x) = g <$> tick x := by
  cases x <;> rfl
-- classical non-natural maps
noncomputable def fN {α : Type} : Option α → Option α
  | some a => some a
  | none => @dite _ (Nonempty α) (Classical.propDecidable _) (fun h => some (Classical.choice h))
      (fun _ => none)
noncomputable def cS (α : Type) : ℕ := @ite _ (Subsingleton α) (Classical.propDecidable _) 0 1
theorem cS_unit : cS Unit = 0 := by unfold cS; rw [if_pos (inferInstance : Subsingleton Unit)]
noncomputable def fS {α : Type} (a : Id α) : StateM ℕ α := fun _ => pure (a, cS α)
theorem nsB : ¬ Subsingleton Bool := fun h => absurd (h.elim true false) (by decide)
theorem cS_bool : cS Bool = 1 := by unfold cS; rw [if_neg nsB]

-- Projections with the instances read off the hypothesis (dot notation would re-synthesize them).
section proj
variable {m n : Type → Type} {f : ∀ {α : Type}, m α → n α}
theorem pmap {im : Functor m} {jn : Functor n} (h : @Cslib.IsFunctorHom m n im jn f) {α β : Type}
    (g : α → β) (x : m α) : f (g <$> x) = g <$> f x := h.map_map g x
theorem pconst {im : Functor m} {jn : Functor n} (h : @Cslib.IsFunctorHom m n im jn f) {α β : Type}
    (a : α) (x : m β) : f (Functor.mapConst a x) = Functor.mapConst a (f x) := h.map_mapConst a x
theorem aF {im : Applicative m} {jn : Applicative n} (h : @Cslib.IsApplicativeHom m n im jn f) :
    @Cslib.IsFunctorHom m n im.toFunctor jn.toFunctor f := h.toIsFunctorHom
theorem apure {im : Applicative m} {jn : Applicative n} (h : @Cslib.IsApplicativeHom m n im jn f)
    {α : Type} (a : α) : f (pure a) = pure a := h.map_pure a
theorem aseq {im : Applicative m} {jn : Applicative n} (h : @Cslib.IsApplicativeHom m n im jn f)
    {α β : Type} (x : m (α → β)) (y : Unit → m α) : f (Seq.seq x y) = Seq.seq (f x) (f <| y ·) :=
  h.map_seq x y
theorem mA {im : Monad m} {jn : Monad n} (h : @Cslib.IsMonadHom m n im jn f) :
    @Cslib.IsApplicativeHom m n im.toApplicative jn.toApplicative f := h.toIsApplicativeHom
theorem mbind {im : Monad m} {jn : Monad n} (h : @Cslib.IsMonadHom m n im jn f) {α β : Type}
    (x : m α) (y : α → m β) : f (x >>= y) = f x >>= (f <| y ·) := h.map_bind x y
theorem altA {im : Alternative m} {jn : Alternative n} (h : @Cslib.IsAlternativeHom m n im jn f) :
    @Cslib.IsApplicativeHom m n im.toApplicative jn.toApplicative f := h.toIsApplicativeHom
theorem altF {im : Alternative m} {jn : Alternative n} (h : @Cslib.IsAlternativeHom m n im jn f)
    {α : Type} : f (failure : m α) = failure := h.map_failure
theorem altO {im : Alternative m} {jn : Alternative n} (h : @Cslib.IsAlternativeHom m n im jn f)
    {α : Type} (x : m α) (y : Unit → m α) : f (HOrElse.hOrElse x y) = HOrElse.hOrElse (f x) (f <| y ·) :=
  h.map_orElse x y
theorem amM {im : AlternativeMonad m} {jn : AlternativeMonad n}
    (h : @Cslib.IsAlternativeMonadHom m n im jn f) :
    @Cslib.IsMonadHom m n im.toMonad jn.toMonad f := h.toIsMonadHom
theorem amA {im : AlternativeMonad m} {jn : AlternativeMonad n}
    (h : @Cslib.IsAlternativeMonadHom m n im jn f) :
    @Cslib.IsAlternativeHom m n im.toAlternative jn.toAlternative f := h.toIsAlternativeHom
end proj


-- no `(fun _ _ => False)`-chain from 0 to 1
theorem noChain (c : List ℕ) : ¬ List.IsChainFromTo (fun _ _ : ℕ => False) c 0 1 := by
  rintro ⟨hc, hne, hh, hl⟩
  match c, hc, hne, hh, hl with
  | [x], _, _, hh, hl => simp at hh hl; omega
  | x :: y :: t, hc, _, _, _ => simp at hc

-- `segment f 0 = 0` for every `f`
theorem segz (f : ℕ → ℕ) : Nat.segment f 0 = 0 := by
  unfold Nat.segment
  rw [Nat.count_succ, Nat.count_zero]
  split <;> rfl

-- if 0 and 1 are values of `f` then `segment f 1 = 1`
theorem seg1 (f : ℕ → ℕ) (h0 : 0 ∈ Set.range f) (h1 : 1 ∈ Set.range f) : Nat.segment f 1 = 1 := by
  unfold Nat.segment
  rw [Nat.count_succ, Nat.count_succ, Nat.count_zero, if_pos h0, if_pos h1]

-- sample non-monotone functions
def fA (n : ℕ) : ℕ := if n = 0 then 0 else if n = 1 then 10 else 1
def fB (n : ℕ) : ℕ := if n = 0 then 1 else 0
def fC (n : ℕ) : ℕ := if n = 0 then 5 else n - 1
theorem segA : Nat.segment fA 1 = 1 := seg1 fA ⟨0, rfl⟩ ⟨2, rfl⟩
theorem segB : Nat.segment fB 1 = 1 := seg1 fB ⟨1, rfl⟩ ⟨0, rfl⟩
theorem segC : Nat.segment fC 1 = 1 := seg1 fC ⟨1, rfl⟩ ⟨2, rfl⟩
theorem segI : Nat.segment id 1 = 1 := seg1 id ⟨0, rfl⟩ ⟨1, rfl⟩
theorem sm5 : StrictMono (· + 5 : ℕ → ℕ) := fun _ _ h => Nat.add_lt_add_right h 5

-- `cl α` = whether `α` is a subsingleton (classical); `fR` sets an unset state to `cl α`
noncomputable def cl (α : Type) : Bool := @ite _ (Subsingleton α) (Classical.propDecidable _) true false
theorem cl_arrow {γ δ : Type} (y : γ) : cl (γ → δ) = cl δ := by
  have e : Subsingleton (γ → δ) ↔ Subsingleton δ :=
    ⟨fun h => ⟨fun a b => congrFun (h.elim (fun _ => a) (fun _ => b)) y⟩,
     fun h => ⟨fun f g => funext fun _ => h.elim _ _⟩⟩
  unfold cl
  by_cases hd : Subsingleton δ
  · rw [if_pos (e.mpr hd), if_pos hd]
  · rw [if_neg (fun h => hd (e.mp h)), if_neg hd]
theorem cl_unit : cl Unit = true := by unfold cl; rw [if_pos (inferInstance : Subsingleton Unit)]
theorem cl_bool : cl Bool = false := by
  unfold cl; rw [if_neg (fun h => absurd (h.elim true false) (by decide))]
noncomputable def fR {α : Type} (a : Id α) : StateM (Option Bool) α :=
  fun s => pure (a, match s with | none => some (cl α) | some b => some b)
theorem fR_seq {γ δ : Type} (x : Id (γ → δ)) (y : Unit → Id γ) :
    fR (Seq.seq x y) = Seq.seq (fR x) (fun _ => fR (y ())) := by
  funext s
  cases s with
  | none =>
    show (pure (x (y ()), some (cl δ)) : Id _) = pure (x (y ()), some (cl (γ → δ)))
    rw [cl_arrow (γ := γ) (δ := δ) (y ())]
  | some b => rfl
end W1c2
open W1c2

-- `Cslib.IsFunctorHom.map_map` 5
theorem fmm5 : ¬ drop0% Cslib.IsFunctorHom.map_map 5 := fun h => by
  have := @h Option BO sF bF (fun x => x) Unit Unit id (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsFunctorHom.map_mapConst` 5
theorem fmc5 : ¬ drop0% Cslib.IsFunctorHom.map_mapConst 5 := fun h => by
  have := @h Option BO sF bFc (fun x => x) Unit Unit () (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsFunctorHom.map_mapConst_of_map_map` 4
theorem fmcm4 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsFunctorHom.map_mapConst_of_map_map 4 := fun h => by
  have := @h BO Option bFc sF _ (fun x => x) (fun _ _ => rfl) Unit Unit () (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsFunctorHom.map_mapConst_of_map_map` 5
theorem fmcm5 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsFunctorHom.map_mapConst_of_map_map 5 := fun h => by
  have := @h Option BO sF bFc _ (fun x => x) (fun _ _ => rfl) Unit Unit () (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsFunctorHom.map_mapConst_of_map_map` 7
theorem fmcm7 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsFunctorHom.map_mapConst_of_map_map 7 := fun h => by
  have := @h Option Option sF sF _ _ fN Unit Empty () none
  revert this; simp [fN, Functor.mapConst]

-- `Cslib.IsFunctorHom.mk'` 4
theorem fmk4 : ¬ drop0% Cslib.IsFunctorHom.mk' 4 := fun h => by
  have := pconst (@h BO Option bFc sF _ (fun x => x) (fun _ _ => rfl)) () (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsFunctorHom.mk'` 5
theorem fmk5 : ¬ drop0% Cslib.IsFunctorHom.mk' 5 := fun h => by
  have := pconst (@h Option BO sF bFc _ (fun x => x) (fun _ _ => rfl)) () (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsFunctorHom.mk'` 7
theorem fmk7 : ¬ drop0% Cslib.IsFunctorHom.mk' 7 := fun h => by
  have := pmap (@h Option Option sF sF _ _ fN) (fun e : Empty => (e.elim : Unit)) none
  revert this; simp [fN]

-- `Cslib.IsFunctorHom.comp` 8
theorem fcp8 : ¬ drop0% Cslib.IsFunctorHom.comp 8 := fun h => by
  have := pmap ((@h BO BO Option bF bF sF (fun x => x) (fun x => x)
    (@Cslib.IsFunctorHom.mk BO BO bF bF _ (fun _ _ => rfl) (fun _ _ => rfl)))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsFunctorHom.comp` 9
theorem fcp9 : ¬ drop0% Cslib.IsFunctorHom.comp 9 := fun h => by
  have := pmap ((@h BO Option Option bF sF sF (fun x => x) (fun x => x)
    (@Cslib.IsFunctorHom.mk Option Option sF sF _ (fun _ _ => rfl) (fun _ _ => rfl)))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsApplicativeHom.toIsFunctorHom` 5
theorem atf5 : ¬ drop0% Cslib.IsApplicativeHom.toIsFunctorHom 5 := fun h => by
  have := pmap (@h Option BO sA bAmap (fun x => x)) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsApplicativeHom.map_seq` 5
theorem amq5 : ¬ drop0% Cslib.IsApplicativeHom.map_seq 5 := fun h => by
  have := congrArg ev (@h Option OS sA oA tick Unit Unit (some id) (fun _ => some ()))
  exact absurd this (by decide)

-- `Cslib.IsApplicativeHom.map_seqLeft` 5
theorem asl5 : ¬ drop0% Cslib.IsApplicativeHom.map_seqLeft 5 := fun h => by
  have := congrArg ev (@h Option OS sA oA tick Unit Unit (some ()) (fun _ => some ()))
  exact absurd this (by decide)

-- `Cslib.IsApplicativeHom.map_seqRight` 5
theorem asr5 : ¬ drop0% Cslib.IsApplicativeHom.map_seqRight 5 := fun h => by
  have := congrArg ev (@h Option OS sA oA tick Unit Unit (some ()) (fun _ => some ()))
  exact absurd this (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_map_of_map_pure_map_seq` 4
theorem ammq4 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_map_of_map_pure_map_seq 4 := fun h => by
  have := @h BO Option bAmap sA _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) Unit Unit id (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_map_of_map_pure_map_seq` 5
theorem ammq5 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_map_of_map_pure_map_seq 5 := fun h => by
  have := @h Option BO sA bAmap _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) Unit Unit id (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_map_of_map_pure_map_seq` 7
theorem ammq7 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_map_of_map_pure_map_seq 7 := fun h => by
  have := congrArg (fun z => (z none).2)
    (@h Id (StateM (Option Bool)) _ _ _ _ fR (fun x y => fR_seq x y) Unit Bool (fun _ => true) ())
  have e : some (cl Bool) = some (cl Unit) := this
  rw [cl_unit, cl_bool] at e
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_map_of_map_pure_map_seq` 8
theorem ammq8 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_map_of_map_pure_map_seq 8 := fun h => by
  have := @h Option Option sA sA _ _ fN (fun _ => rfl) Empty Unit (fun e => e.elim) none
  revert this; simp [fN]

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_seqLeft_of_map_seq_map_map` 4
theorem aslm4 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_seqLeft_of_map_seq_map_map 4 := fun h => by
  have := @h BO Option bAsl sA _ (fun x => x) (fun _ _ => rfl) (fun _ _ => rfl) Unit Unit (some ()) (fun _ => some ())
  have e : @Eq (Option _) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_seqLeft_of_map_seq_map_map` 5
theorem aslm5 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_seqLeft_of_map_seq_map_map 5 := fun h => by
  have := @h Option BO sA bAsl _ (fun x => x) (fun _ _ => rfl) (fun _ _ => rfl) Unit Unit (some ()) (fun _ => some ())
  have e : @Eq (Option _) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_seqLeft_of_map_seq_map_map` 8
theorem aslm8 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_seqLeft_of_map_seq_map_map 8 := fun h => by
  have := congrArg ev (@h Option OS sA oA _ _ tick tick_map Unit Unit (some ()) (fun _ => some ()))
  exact absurd this (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_seqRight_of_map_seq_map_map` 4
theorem asrm4 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_seqRight_of_map_seq_map_map 4 := fun h => by
  have := @h BO Option bAsr sA _ (fun x => x) (fun _ _ => rfl) (fun _ _ => rfl) Unit Unit (some ()) (fun _ => some ())
  have e : @Eq (Option _) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_seqRight_of_map_seq_map_map` 5
theorem asrm5 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_seqRight_of_map_seq_map_map 5 := fun h => by
  have := @h Option BO sA bAsr _ (fun x => x) (fun _ _ => rfl) (fun _ _ => rfl) Unit Unit (some ()) (fun _ => some ())
  have e : @Eq (Option _) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsApplicativeHom.map_seqRight_of_map_seq_map_map` 8
theorem asrm8 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsApplicativeHom.map_seqRight_of_map_seq_map_map 8 := fun h => by
  have := congrArg ev (@h Option OS sA oA _ _ tick tick_map Unit Unit (some ()) (fun _ => some ()))
  exact absurd this (by decide)

-- `Cslib.IsApplicativeHom.mk'` 4
theorem amk4 : ¬ drop0% Cslib.IsApplicativeHom.mk' 4 := fun h => by
  have := pmap (aF (@h BO Option bAmap sA _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsApplicativeHom.mk'` 5
theorem amk5 : ¬ drop0% Cslib.IsApplicativeHom.mk' 5 := fun h => by
  have := pmap (aF (@h Option BO sA bAmap _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsApplicativeHom.mk'` 7
theorem amk7 : ¬ drop0% Cslib.IsApplicativeHom.mk' 7 := fun h => by
  have := apure (@h Option Option sA sA _ _ (fun _ => none) (fun _ _ => rfl)) ()
  exact absurd this (by decide)

-- `Cslib.IsApplicativeHom.mk'` 8
theorem amk8 : ¬ drop0% Cslib.IsApplicativeHom.mk' 8 := fun h => by
  have := pmap (aF (@h Option Option sA sA _ _ fN (fun _ => rfl))) (fun e : Empty => (e.elim : Unit)) none
  revert this; simp [fN]

-- `Cslib.IsApplicativeHom.comp` 8
theorem acp8 : ¬ drop0% Cslib.IsApplicativeHom.comp 8 := fun h => by
  have := apure (@h Option Option Option sA sA sA (fun _ => none) (fun x => x) (Cslib.IsApplicativeHom.id Option)) ()
  exact absurd this (by decide)

-- `Cslib.IsApplicativeHom.comp` 9
theorem acp9 : ¬ drop0% Cslib.IsApplicativeHom.comp 9 := fun h => by
  have := apure (@h Option Option Option sA sA sA (fun x => x) (fun _ => none) (Cslib.IsApplicativeHom.id Option)) ()
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.toIsApplicativeHom` 5
theorem mta5 : ¬ drop0% Cslib.IsMonadHom.toIsApplicativeHom 5 := fun h => by
  have := congrArg ev (apure (@h Option OS sM oM tick) ())
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_bind` 5
theorem mmb5 : ¬ drop0% Cslib.IsMonadHom.map_bind 5 := fun h => by
  have := congrArg ev (@h Option OS sM oM tick Unit Unit (some ()) (fun _ => some ()))
  exact absurd this (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsMonadHom.map_map_of_map_pure_map_bind` 4
theorem mmmb4 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsMonadHom.map_map_of_map_pure_map_bind 4 := fun h => by
  have := @h BO Option bMmap sM _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) Unit Unit id (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsMonadHom.map_map_of_map_pure_map_bind` 5
theorem mmmb5 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsMonadHom.map_map_of_map_pure_map_bind 5 := fun h => by
  have := @h Option BO sM bMmap _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) Unit Unit id (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsMonadHom.map_map_of_map_pure_map_bind` 7
theorem mmmb7 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsMonadHom.map_map_of_map_pure_map_bind 7 := fun h => by
  have := congrArg (fun z => (z 5).2) (@h Id (StateM ℕ) _ _ _ _ fS (fun _ _ => rfl) Unit Bool (fun _ => true) ())
  have e : cS Bool = cS Unit := this
  rw [cS_unit, cS_bool] at e
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsMonadHom.map_map_of_map_pure_map_bind` 8
theorem mmmb8 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsMonadHom.map_map_of_map_pure_map_bind 8 := fun h => by
  have := @h Option Option sM sM _ _ fN (fun _ => rfl) Empty Unit (fun e => e.elim) none
  revert this; simp [fN]

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsMonadHom.map_seq_of_map_pure_map_bind` 4
theorem msmb4 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsMonadHom.map_seq_of_map_pure_map_bind 4 := fun h => by
  have := @h BO Option bMseq sM _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) Unit Unit (some id) (fun _ => some ())
  have e : @Eq (Option _) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsMonadHom.map_seq_of_map_pure_map_bind` 5
theorem msmb5 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsMonadHom.map_seq_of_map_pure_map_bind 5 := fun h => by
  have := @h Option BO sM bMseq _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) Unit Unit (some id) (fun _ => some ())
  have e : @Eq (Option _) _ _ := this
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsMonadHom.map_seq_of_map_pure_map_bind` 7
theorem msmb7 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsMonadHom.map_seq_of_map_pure_map_bind 7 := fun h => by
  have := congrArg (fun z => (z 5).2) (@h Id (StateM ℕ) _ _ _ _ fS (fun _ _ => rfl) Unit Bool (fun _ => true) (fun _ => ()))
  have e : cS Bool = cS Unit := this
  rw [cS_unit, cS_bool] at e
  exact absurd e (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.0.Cslib.IsMonadHom.map_seq_of_map_pure_map_bind` 8
theorem msmb8 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.«0».Cslib.IsMonadHom.map_seq_of_map_pure_map_bind 8 := fun h => by
  have := @h Option Option sM sM _ _ fN (fun _ => rfl) Empty Unit none (fun _ => none)
  have h1 : fN (none : Option Unit) = some () := by simp [fN]; exact ⟨()⟩
  have h2 : fN (none : Option Empty) = none := by simp [fN]
  have h3 : ∀ z : Option (Empty → Unit), (z <*> none : Option Unit) = none := fun z => by cases z <;> rfl
  have e : fN (none : Option Unit) = fN (none : Option (Empty → Unit)) <*> fN (none : Option Empty) := this
  rw [h1, h2, h3] at e
  exact absurd e (by decide)

-- `Cslib.IsMonadHom.mk'` 4
theorem mmk4 : ¬ drop0% Cslib.IsMonadHom.mk' 4 := fun h => by
  have := pmap (aF (mA (@h BO Option bMmap sM _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl)))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsMonadHom.mk'` 5
theorem mmk5 : ¬ drop0% Cslib.IsMonadHom.mk' 5 := fun h => by
  have := pmap (aF (mA (@h Option BO sM bMmap _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl)))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsMonadHom.mk'` 7
theorem mmk7 : ¬ drop0% Cslib.IsMonadHom.mk' 7 := fun h => by
  have := apure (mA (@h Option Option sM sM _ _ (fun _ => none) (fun _ _ => rfl))) ()
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.comp` 8
theorem mcp8 : ¬ drop0% Cslib.IsMonadHom.comp 8 := fun h => by
  have := apure (mA (@h Option Option Option sM sM sM (fun _ => none) (fun x => x) (Cslib.IsMonadHom.id Option))) ()
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.comp` 9
theorem mcp9 : ¬ drop0% Cslib.IsMonadHom.comp 9 := fun h => by
  have := apure (mA (@h Option Option Option sM sM sM (fun x => x) (fun _ => none) (Cslib.IsMonadHom.id Option))) ()
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.monadLift` 4
theorem ml4 : ¬ drop0% Cslib.IsMonadHom.monadLift 4 := fun h => by
  have := pmap (aF (mA (@h BO Option bMmap sM _ (⟨fun x => x⟩ : MonadLift BO Option)
    (@LawfulMonadLift.mk BO Option bMmap sM ⟨fun x => x⟩ (fun _ => rfl) (fun _ _ => rfl))))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsMonadHom.monadLift` 5
theorem ml5 : ¬ drop0% Cslib.IsMonadHom.monadLift 5 := fun h => by
  have := pmap (aF (mA (@h Option BO sM bMmap _ (⟨fun x => x⟩ : MonadLift Option BO)
    (@LawfulMonadLift.mk Option BO sM bMmap ⟨fun x => x⟩ (fun _ => rfl) (fun _ _ => rfl))))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsMonadHom.monadLift` 7
theorem ml7 : ¬ drop0% Cslib.IsMonadHom.monadLift 7 := fun h => by
  have := apure (mA (@h Option Option sM sM _ _ (⟨fun _ => none⟩ : MonadLift Option Option))) ()
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.monadLiftT` 4
theorem mlt4 : ¬ drop0% Cslib.IsMonadHom.monadLiftT 4 := fun h => by
  have := pmap (aF (mA (@h BO Option bMmap sM _ (⟨fun x => x⟩ : MonadLiftT BO Option)
    (@LawfulMonadLiftT.mk BO Option bMmap sM ⟨fun x => x⟩ (fun _ => rfl) (fun _ _ => rfl))))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsMonadHom.monadLiftT` 5
theorem mlt5 : ¬ drop0% Cslib.IsMonadHom.monadLiftT 5 := fun h => by
  have := pmap (aF (mA (@h Option BO sM bMmap _ (⟨fun x => x⟩ : MonadLiftT Option BO)
    (@LawfulMonadLiftT.mk Option BO sM bMmap ⟨fun x => x⟩ (fun _ => rfl) (fun _ _ => rfl))))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsMonadHom.monadLiftT` 7
theorem mlt7 : ¬ drop0% Cslib.IsMonadHom.monadLiftT 7 := fun h => by
  have := apure (mA (@h Option Option sM sM _ _ (⟨fun _ => none⟩ : MonadLiftT Option Option))) ()
  exact absurd this (by decide)

-- `Cslib.IsAlternativeHom.toIsApplicativeHom` 5
theorem alta5 : ¬ drop0% Cslib.IsAlternativeHom.toIsApplicativeHom 5 := fun h => by
  have := congrArg ev (apure (@h Option OS sAlt oAlt tick) ())
  exact absurd this (by decide)

-- `Cslib.IsAlternativeHom.map_failure` 5
theorem altf5 : ¬ drop0% Cslib.IsAlternativeHom.map_failure 5 := fun h => by
  have := congrArg ev (@h Option OS sAlt oAlt tick Unit)
  exact absurd this (by decide)

-- `Cslib.IsAlternativeHom.mk'` 4
theorem altk4 : ¬ drop0% Cslib.IsAlternativeHom.mk' 4 := fun h => by
  have := pmap (aF (altA (@h BO Option bAltmap sAlt _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) rfl (fun _ _ => rfl)))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsAlternativeHom.mk'` 5
theorem altk5 : ¬ drop0% Cslib.IsAlternativeHom.mk' 5 := fun h => by
  have := pmap (aF (altA (@h Option BO sAlt bAltmap _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) rfl (fun _ _ => rfl)))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsAlternativeHom.mk'` 7
theorem altk7 : ¬ drop0% Cslib.IsAlternativeHom.mk' 7 := fun h => by
  have := apure (altA (@h Option Option sAlt sAlt _ _ (fun _ => none) (fun _ _ => rfl) rfl (fun _ _ => rfl))) ()
  exact absurd this (by decide)

-- `Cslib.IsAlternativeHom.mk'` 8
theorem altk8 : ¬ drop0% Cslib.IsAlternativeHom.mk' 8 := fun h => by
  have := aseq (altA (@h BS BO bAltOrOS bAltOr (inferInstanceAs (LawfulApplicative OS))
    (inferInstanceAs (LawfulApplicative Option)) evr (fun _ => rfl) rfl (fun _ _ => rfl))) tkid (fun _ => gt)
  have e : @Eq (Option _) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsAlternativeHom.mk'` 9
theorem altk9 : ¬ drop0% Cslib.IsAlternativeHom.mk' 9 := fun h => by
  have := congrArg ev (altF (α := Unit) (@h BS OS bAltFail oAlt (inferInstanceAs (LawfulApplicative OS)) _
    (fun x => x) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)))
  exact absurd this (by decide)

-- `Cslib.IsAlternativeHom.mk'` 10
theorem altk10 : ¬ drop0% Cslib.IsAlternativeHom.mk' 10 := fun h => by
  have := altO (@h Option BO sAlt bAltOr _ (inferInstanceAs (LawfulApplicative Option)) (fun x => x) (fun _ => rfl) (fun _ _ => rfl) rfl) none (fun _ => some ())
  have e : @Eq (Option _) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsAlternativeHom.comp` 8
theorem altc8 : ¬ drop0% Cslib.IsAlternativeHom.comp 8 := fun h => by
  have := apure (altA (@h Option Option Option sAlt sAlt sAlt (fun _ => none) (fun x => x) (Cslib.IsAlternativeHom.id Option))) ()
  exact absurd this (by decide)

-- `Cslib.IsAlternativeHom.comp` 9
theorem altc9 : ¬ drop0% Cslib.IsAlternativeHom.comp 9 := fun h => by
  have := apure (altA (@h Option Option Option sAlt sAlt sAlt (fun x => x) (fun _ => none) (Cslib.IsAlternativeHom.id Option))) ()
  exact absurd this (by decide)

-- `Cslib.IsAlternativeMonadHom.toIsMonadHom` 5
theorem amtm5 : ¬ drop0% Cslib.IsAlternativeMonadHom.toIsMonadHom 5 := fun h => by
  have := congrArg ev (apure (mA (@h Option OS sAM oAM tick)) ())
  exact absurd this (by decide)

-- `Cslib.IsAlternativeMonadHom.map_orElse` 5
theorem amoe5 : ¬ drop0% Cslib.IsAlternativeMonadHom.map_orElse 5 := fun h => by
  have := congrArg ev (@h Option OS sAM oAM tick Unit none (fun _ => none))
  exact absurd this (by decide)

-- `Cslib.IsAlternativeMonadHom.toIsAlternativeHom` 5
theorem amta5 : ¬ drop0% Cslib.IsAlternativeMonadHom.toIsAlternativeHom 5 := fun h => by
  have := congrArg ev (apure (altA (@h Option OS sAM oAM tick)) ())
  exact absurd this (by decide)

-- `Cslib.IsAlternativeMonadHom.map_failure` 5
theorem amf5 : ¬ drop0% Cslib.IsAlternativeMonadHom.map_failure 5 := fun h => by
  have := congrArg ev (@h Option OS sAM oAM tick Unit)
  exact absurd this (by decide)

-- `Cslib.IsAlternativeMonadHom.mk'` 4
theorem amk4' : ¬ drop0% Cslib.IsAlternativeMonadHom.mk' 4 := fun h => by
  have := pmap (aF (mA (amM (@h BO Option bAMmap sAM _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) rfl (fun _ _ => rfl))))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsAlternativeMonadHom.mk'` 5
theorem amk5' : ¬ drop0% Cslib.IsAlternativeMonadHom.mk' 5 := fun h => by
  have := pmap (aF (mA (amM (@h Option BO sAM bAMmap _ (fun x => x) (fun _ => rfl) (fun _ _ => rfl) rfl (fun _ _ => rfl))))) (id : Unit → Unit) (some ())
  have e : @Eq (Option Unit) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsAlternativeMonadHom.mk'` 7
theorem amk7' : ¬ drop0% Cslib.IsAlternativeMonadHom.mk' 7 := fun h => by
  have := apure (mA (amM (@h Option Option sAM sAM _ _ (fun _ => none) (fun _ _ => rfl) rfl (fun _ _ => rfl)))) ()
  exact absurd this (by decide)

-- `Cslib.IsAlternativeMonadHom.mk'` 8
theorem amk8' : ¬ drop0% Cslib.IsAlternativeMonadHom.mk' 8 := fun h => by
  have := mbind (amM (@h BS BO bAMOrOS bAMOr (inferInstanceAs (LawfulMonad OS))
    (inferInstanceAs (LawfulMonad Option)) evr (fun _ => rfl) rfl (fun _ _ => rfl))) tk (fun _ => gt)
  have e : @Eq (Option ℕ) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsAlternativeMonadHom.mk'` 9
theorem amk9' : ¬ drop0% Cslib.IsAlternativeMonadHom.mk' 9 := fun h => by
  have := congrArg ev (altF (α := Unit) (amA (@h BS OS bAMFail oAM (inferInstanceAs (LawfulMonad OS)) _
    (fun x => x) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl))))
  exact absurd this (by decide)

-- `Cslib.IsAlternativeMonadHom.mk'` 10
theorem amk10' : ¬ drop0% Cslib.IsAlternativeMonadHom.mk' 10 := fun h => by
  have := altO (amA (@h Option BO sAM bAMOr _ (inferInstanceAs (LawfulMonad Option)) (fun x => x) (fun _ => rfl) (fun _ _ => rfl) rfl)) none (fun _ => some ())
  have e : @Eq (Option _) _ _ := this
  exact absurd e (by decide)

-- `Cslib.IsAlternativeMonadHom.comp` 8
theorem amc8 : ¬ drop0% Cslib.IsAlternativeMonadHom.comp 8 := fun h => by
  have := apure (mA (amM (@h Option Option Option sAM sAM sAM (fun _ => none) (fun x => x) (Cslib.IsAlternativeMonadHom.id Option)))) ()
  exact absurd this (by decide)

-- `Cslib.IsAlternativeMonadHom.comp` 9
theorem amc9 : ¬ drop0% Cslib.IsAlternativeMonadHom.comp 9 := fun h => by
  have := apure (mA (amM (@h Option Option Option sAM sAM sAM (fun x => x) (fun _ => none) (Cslib.IsAlternativeMonadHom.id Option)))) ()
  exact absurd this (by decide)

-- `Cslib.IsApplicativeHom.map_listMapA` 5
theorem lma5 : ¬ drop0% Cslib.IsApplicativeHom.map_listMapA 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit Unit (fun _ => some ()) []
  exact absurd this (by decide)

-- `Cslib.IsApplicativeHom.map_listForA` 5
theorem lfa5 : ¬ drop0% Cslib.IsApplicativeHom.map_listForA 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit [] (fun _ => some ())
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listMapM'` 5
theorem lmm5 : ¬ drop0% Cslib.IsMonadHom.map_listMapM' 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit Unit (fun _ => some ()) []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listMapMLoop` 5
theorem lml5 : ¬ drop0% Cslib.IsMonadHom.map_listMapMLoop 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit Unit (fun _ => some ()) [] []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listMapM` 5
theorem lmM5 : ¬ drop0% Cslib.IsMonadHom.map_listMapM 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit Unit (fun _ => some ()) []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listForM` 5
theorem lfm5 : ¬ drop0% Cslib.IsMonadHom.map_listForM 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit [] (fun _ => some ())
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listFoldlM` 5
theorem lfl5 : ¬ drop0% Cslib.IsMonadHom.map_listFoldlM 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit Unit (fun _ _ => some ()) () []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listFoldrM` 5
theorem lfr5 : ¬ drop0% Cslib.IsMonadHom.map_listFoldrM 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit Unit (fun _ _ => some ()) () []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listFindSomeM?` 5
theorem lfs5 : ¬ drop0% Cslib.IsMonadHom.map_listFindSomeM? 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit Unit (fun _ => some none) []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listFindM?` 5
theorem lfd5 : ¬ drop0% Cslib.IsMonadHom.map_listFindM? 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit (fun _ => some true) []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listAnyM` 5
theorem lan5 : ¬ drop0% Cslib.IsMonadHom.map_listAnyM 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit (fun _ => some true) []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listAllM` 5
theorem lal5 : ¬ drop0% Cslib.IsMonadHom.map_listAllM 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit (fun _ => some true) []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listFilterAuxM` 5
theorem lfx5 : ¬ drop0% Cslib.IsMonadHom.map_listFilterAuxM 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit (fun _ => some true) [] []
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listFilterM` 5
theorem lfi5 : ¬ drop0% Cslib.IsMonadHom.map_listFilterM 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit (fun _ => some true) []
  exact absurd this (by decide)

-- `Cslib.IsAlternativeHom.map_listFirstM` 5
theorem lfst5 : ¬ drop0% Cslib.IsAlternativeHom.map_listFirstM 5 := fun h => by
  have := congrArg (fun z : OptionT (StateM ℕ) Unit => (z.run.run 0).2)
    (@h Option (OptionT (StateM ℕ)) _ _ (fun x => OptionT.mk (do modify (· + 1); pure x))
      Unit Unit (fun _ => some ()) [])
  exact absurd this (by decide)

-- `Cslib.IsApplicativeHom.map_listSingleton` 1
theorem lsg1 : ¬ drop0% Cslib.IsApplicativeHom.map_listSingleton 1 := fun h => by
  have := @h (fun _ => []) Unit ()
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_listFlatMap` 1
theorem lfb1 : ¬ drop0% Cslib.IsMonadHom.map_listFlatMap 1 := fun h => by
  have := @h (fun l => l ++ l) Unit Unit [()] (fun _ => [()])
  exact absurd this (by decide)

-- `Cslib.IsFunctorHom.map_listNil` 1
theorem lnil1 : ¬ drop0% Cslib.IsFunctorHom.map_listNil 1 := fun h => by
  have := @h (fun {α} l => @dite _ (Nonempty α) (Classical.propDecidable _)
    (fun h => [Classical.choice h]) (fun _ => l)) Unit
  rw [dif_pos ⟨()⟩] at this
  exact List.cons_ne_nil _ _ this

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.List.0.Cslib.List.nil_singleton_append_induction` 2
theorem nsa2 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.List.«0».Cslib.List.nil_singleton_append_induction 2 := fun h =>
  @h Unit (fun l => l ≠ []) (fun a => List.cons_ne_nil _ _) (fun xs ys hx _ => by simp_all) [] rfl

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.List.0.Cslib.List.nil_singleton_append_induction` 3
theorem nsa3 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.List.«0».Cslib.List.nil_singleton_append_induction 3 := fun h =>
  List.cons_ne_nil _ _ (@h Unit (fun l => l = []) rfl (fun xs ys hx hy => by simp [hx, hy]) [()])

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.List.0.Cslib.List.nil_singleton_append_induction` 4
theorem nsa4 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.List.«0».Cslib.List.nil_singleton_append_induction 4 := fun h =>
  absurd (@h Unit (fun l => l.length ≤ 1) (by simp) (fun _ => by simp) [(), ()]) (by decide)

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.List.0.Cslib.eq_ab_or_ba` 1
theorem eab1 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.List.«0».Cslib.eq_ab_or_ba 1 := fun h => by
  have := h [priv% _private.Cslib.Foundations.Control.Monad.IsMonadHom.List.«0».Cslib.Two.b] rfl
  simp at this

-- `_private.Cslib.Foundations.Control.Monad.IsMonadHom.List.0.Cslib.eq_ab_or_ba` 2
theorem eab2 : ¬ drop0% _private.Cslib.Foundations.Control.Monad.IsMonadHom.List.«0».Cslib.eq_ab_or_ba 2 := fun h => by
  have := h [priv% _private.Cslib.Foundations.Control.Monad.IsMonadHom.List.«0».Cslib.Two.a] rfl
  simp at this

-- `Finset.card_filter_not_le_card_filter_of_involution` 5
theorem cfn5 : ¬ drop0% Finset.card_filter_not_le_card_filter_of_involution 5 := fun h => by
  have := @h ℕ {0, 1, 2} (fun _ => 0) (fun x => x = 0) _ (by decide) (by decide)
  exact absurd this (by decide)

-- `Finset.card_div_two_le_card_filter_of_involution` 5
theorem cdt5 : ¬ drop0% Finset.card_div_two_le_card_filter_of_involution 5 := fun h => by
  have := @h ℕ {0, 1, 2, 3} (fun _ => 0) (fun x => x = 0) _ (by decide) (by decide)
  exact absurd this (by decide)

-- `List.IsChainFromTo.head_induction_on` 3
theorem hio3 : ¬ drop0% List.IsChainFromTo.head_induction_on 3 := fun h => by
  have := @h Unit (fun _ _ => True) (fun {chain} {_} {_} _ => chain.length ≠ 1)
    (fun {_} {_} {_} {_} _ hc _ => by
      intro e; apply hc.ne_nil; simpa using e) [()] () () List.isChainFromTo_singleton
  exact this rfl

-- `List.IsChainFromTo.head_induction_on` 4
theorem hio4 : ¬ drop0% List.IsChainFromTo.head_induction_on 4 := fun h => by
  have := @h Unit (fun _ _ => True) (fun {chain} {_} {_} _ => chain.length = 1) rfl [(), ()] () ()
    (List.isChainFromTo_pair_iff.mpr ⟨trivial, rfl, rfl⟩)
  exact absurd this (by decide)

-- `List.IsChainFromTo.head_induction_on` 8
theorem hio8 : ¬ indep0% List.IsChainFromTo.head_induction_on 8 := fun h =>
  (@h Unit (fun _ _ => True) (fun _ => True) trivial (fun _ _ _ => trivial) [] () ()).ne_nil rfl

-- `List.IsChainFromTo.reflTransGen_of_mem` 7
theorem rtm7 : ¬ drop0% List.IsChainFromTo.reflTransGen_of_mem 7 := fun h => by
  have := @h ℕ (fun _ _ => False) [0] 0 0 List.isChainFromTo_singleton 1
  have := (Relation.reflTransGen_iff_eq (fun _ h => h)).mp this
  omega

-- `List.IsChainFromTo.exists_length_lt_of_not_nodup` 5
theorem eln5 : ¬ drop0% List.IsChainFromTo.exists_length_lt_of_not_nodup 5 := fun h => by
  obtain ⟨c, hc, _⟩ := @h ℕ (fun _ _ => False) [0, 0] 0 1 (by decide)
  exact noChain c hc

-- `List.IsChainFromTo.exists_length_lt_of_not_nodup` 6
theorem eln6 : ¬ drop0% List.IsChainFromTo.exists_length_lt_of_not_nodup 6 := fun h => by
  obtain ⟨c, hc, hl⟩ := @h ℕ (fun _ _ => False) [0] 0 0 List.isChainFromTo_singleton
  have hl' : c.length = 0 := by have : c.length < 1 := hl; omega
  exact hc.ne_nil (List.length_eq_zero_iff.mp hl')

-- `List.IsChainFromTo.exists_nodup` 5
theorem enu5 : ¬ drop0% List.IsChainFromTo.exists_nodup 5 := fun h => by
  obtain ⟨c, hc, _⟩ := @h ℕ (fun _ _ => False) [0] 0 1
  exact noChain c hc

-- `Nat.eventually_mul_pow_le_pow` 3
theorem emp3 : ¬ drop0% Nat.eventually_mul_pow_le_pow 3 := fun h => by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (@h 1 1 1)
  have := hN (N + 2) (by omega)
  simp at this

-- `Nat.eventually_add_one_le_pow_div` 1
theorem eap1 : ¬ drop0% Nat.eventually_add_one_le_pow_div 1 := fun h => by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (@h 1)
  have := hN (N + 2) (by omega)
  rw [one_pow, Nat.div_eq_of_lt (by omega)] at this
  omega

-- `Nat.eventually_mul_log_le` 2: removable (`Nat.log b n = 0` for `b ≤ 1`)
theorem eml2 : drop% Nat.eventually_mul_log_le 2 := by
  intro c b
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.eventually_mul_log_le c hb
  · exact Filter.Eventually.of_forall fun n => by simp [Nat.log_of_left_le_one hb]

-- `Nat.nth_succ_gap` 1: removable (`Nat.le_nth_of_lt_nth_succ` needs no infinitude)
theorem nsg1 : drop% Nat.nth_succ_gap 1 := by
  intro p n k hk hk0 hp
  have := Nat.le_nth_of_lt_nth_succ (show k + Nat.nth p n < Nat.nth p (n + 1) by omega) hp
  omega

-- `Nat.nth_succ_gap` 4
theorem nsg4 : ¬ drop0% Nat.nth_succ_gap 4 := fun h =>
  @h (fun _ => True) (by simpa using Set.infinite_univ (α := ℕ)) 0 1 one_pos trivial

-- `Nat.nth_succ_gap` 5
theorem nsg5 : ¬ drop0% Nat.nth_succ_gap 5 := fun h =>
  @h (fun _ => True) (by simpa using Set.infinite_univ (α := ℕ)) 0 0 (by simp) trivial

-- `Nat.nth_of_strictMono` 1
theorem nsm1 : ¬ drop0% Nat.nth_of_strictMono 1 := fun h => by
  have := @h fB 0
  rw [Nat.nth_zero_of_zero ⟨1, rfl⟩] at this
  exact absurd this (by decide)

-- `Nat.strictMono_range_gap` 1
theorem srg1 : ¬ drop0% Nat.strictMono_range_gap 1 := fun h =>
  @h fA 0 1 (by decide) (by decide) ⟨2, rfl⟩

-- `Nat.strictMono_range_gap` 4
theorem srg4 : ¬ drop0% Nat.strictMono_range_gap 4 := fun h =>
  @h id strictMono_id 1 0 (by decide) ⟨0, rfl⟩

-- `Nat.strictMono_range_gap` 5
theorem srg5 : ¬ drop0% Nat.strictMono_range_gap 5 := fun h =>
  @h id strictMono_id 0 1 (by decide) ⟨1, rfl⟩

-- `Nat.segment_idem` 1
theorem sid1 : ¬ drop0% Nat.segment_idem 1 := fun h => by
  have := @h (fun _ => 0) 1
  rw [segz] at this
  exact absurd this (by decide)

-- `Nat.segment_pre_zero` 1
theorem spz1 : ¬ drop0% Nat.segment_pre_zero 1 := fun h => by
  have := @h fC 1 (by decide)
  rw [segC] at this
  exact absurd this (by decide)

-- `Nat.segment_pre_zero` 3
theorem spz3 : ¬ drop0% Nat.segment_pre_zero 3 := fun h => by
  have := @h id strictMono_id 1
  rw [segI] at this
  exact absurd this (by decide)

-- `Nat.segment_zero` 2: removable (`segment f 0 = 0` for every `f`)
theorem sz2 : drop% Nat.segment_zero 2 := fun {f} _ => segz f

-- `Nat.segment_upper_bound` 2: removable (for `k < f 0` the segment is 0 and `k < f 0 < f 1`)
theorem sub2 : drop% Nat.segment_upper_bound 2 := by
  intro f hm k
  by_cases hk : k < f 0
  · rw [Nat.segment_pre_zero hm hk]; exact hk.trans (hm Nat.zero_lt_one)
  · exact Nat.segment_upper_bound' hm (by omega)

-- `Nat.segment_lower_bound` 1
theorem slb1 : ¬ drop0% Nat.segment_lower_bound 1 := fun h => by
  have := @h fA rfl 1
  rw [segA] at this
  exact absurd this (by decide)

-- `Nat.segment_lower_bound` 2
theorem slb2 : ¬ drop0% Nat.segment_lower_bound 2 := fun h => by
  have := @h (· + 5) sm5 0
  rw [segz] at this
  exact absurd this (by decide)

-- `Nat.segment_range_val` 1
theorem srv1 : ¬ drop0% Nat.segment_range_val 1 := fun h => by
  have := @h fA 0 1 (by decide) (by decide)
  rw [segA] at this
  exact absurd this (by decide)

-- `Nat.segment_range_val` 4
theorem srv4 : ¬ drop0% Nat.segment_range_val 4 := fun h => by
  have := @h id strictMono_id 1 0 (by decide)
  rw [segz] at this
  exact absurd this (by decide)

-- `Nat.segment_range_val` 5
theorem srv5 : ¬ drop0% Nat.segment_range_val 5 := fun h => by
  have := @h id strictMono_id 0 1 (by decide)
  rw [segI] at this
  exact absurd this (by decide)

-- `Nat.segment_galois_connection` 1
theorem sgc1 : ¬ drop0% Nat.segment_galois_connection 1 := fun h => by
  have := (@h fA rfl 1 1).mpr (by rw [segA])
  exact absurd this (by decide)

-- `Nat.segment_galois_connection` 2
theorem sgc2 : ¬ drop0% Nat.segment_galois_connection 2 := fun h => by
  have := (@h (· + 5) sm5 0 0).mpr (Nat.zero_le _)
  exact absurd this (by decide)

-- `Nat.base_zero_strictMono` 1
theorem bzs1 : ¬ drop0% Nat.base_zero_strictMono 1 := fun h =>
  absurd (@h (fun _ => 0) 0 1 Nat.zero_lt_one) (by decide)

-- `Nat.segment'_eq_segment` 1
theorem ses1 : ¬ drop0% Nat.segment'_eq_segment 1 := fun h => by
  have e := congrFun (@h fB) 1
  have e2 : Nat.segment (fun x => fB x - fB 0) 0 = Nat.segment fB 1 := e
  rw [segz, segB] at e2
  exact absurd e2 (by decide)

-- `Nat.segment_zero'` 1
theorem sz'1 : ¬ drop0% Nat.segment_zero' 1 := fun h => by
  have := @h fB 1 (by decide)
  rw [segB] at this
  exact absurd this (by decide)

-- `Nat.segment_zero'` 3
theorem sz'3 : ¬ drop0% Nat.segment_zero' 3 := fun h => by
  have := @h id strictMono_id 1
  rw [segI] at this
  exact absurd this (by decide)

-- `Nat.segment_upper_bound'` 3: removable (same argument as for `Nat.segment_upper_bound`)
theorem sub'3 : drop% Nat.segment_upper_bound' 3 := by
  intro f hm k
  by_cases hk : k < f 0
  · rw [Nat.segment_pre_zero hm hk]; exact hk.trans (hm Nat.zero_lt_one)
  · exact Nat.segment_upper_bound' hm (by omega)

-- `Nat.segment_lower_bound'` 1
theorem slb'1 : ¬ drop0% Nat.segment_lower_bound' 1 := fun h => by
  have := @h fA 1 (by decide)
  rw [segA] at this
  exact absurd this (by decide)

-- `Nat.segment_lower_bound'` 3
theorem slb'3 : ¬ drop0% Nat.segment_lower_bound' 3 := fun h => by
  have := @h (· + 5) sm5 0
  rw [segz] at this
  exact absurd this (by decide)
