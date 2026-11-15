import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init
import Batteries.Data.OrderedAssocList
import Batteries.Data.Float.Lemmas

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

/-- `dropN0% T [i, j, …]`: `T` with all the listed (non-dependent) Prop binders dropped at once,
read off the library, universe parameters set to `0` (for refutations of joint removals). -/
elab "dropN0% " T:ident "[" is:num,* "]" : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  let idx := is.getElems.map (·.getNat)
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    for i in idx do
      let x := xs[i]!
      unless ← isProp (← inferType x) do throwError "binder {i} of {n} is not a Prop"
      for j in [i+1:xs.size] do
        if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
      if body.containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    mkForallFVars ((List.range xs.size).filter (!idx.contains ·) |>.map (xs[·]!)).toArray body

open Batteries Std

/-- `main`'s statement of `Batteries.AssocList.orderedFind?_orderedInsert_self` (before this
branch replaced `[LawfulEqCmp cmp] [TransCmp cmp]` by `[ReflCmp cmp]` and dropped `h`), verbatim,
proved from the new library lemma. -/
theorem ofiSelfMain {α : Type u} {β : Type v} {cmp : α → α → Ordering} [LawfulEqCmp cmp]
    [TransCmp cmp] (l : Batteries.AssocList α β) (h : Batteries.AssocList.KeysOrdered cmp l)
    (a : α) (b : β) :
    (Batteries.AssocList.orderedInsert cmp l a b).orderedFind? cmp a = some b :=
  Batteries.AssocList.orderedFind?_orderedInsert_self l a b

-- the statements refuted below, for inspection
#check (dropN0% Batteries.OrderedAssocList.merge_assoc [15, 17])
#check (dropN0% Float.Model.UnpackedFloat.unpack_beq_unpack_iff [3, 4])
#check (dropN0% ofiSelfMain [3, 4])

set_option linter.deprecated false

/-- `merge_assoc` without both `f₂ a none none = none` and `g₂ a none none = none`: with
`f₁ = g₁ = none`, `f₂ = g₂ = some ()`, `l₁ = [(0, ())]`, `l₂ = l₃ = nil` the left side is `nil` and
the right side is `[(0, ())]`. -/
theorem j1 : ¬ dropN0% Batteries.OrderedAssocList.merge_assoc [15, 17] := fun H =>
  absurd (congrArg (·.toAssocList.toList) (H (cmp := (compare : Nat → Nat → Ordering))
    (β₁ := Unit) (β₂ := Unit) (γ₁ := Unit) (β₃ := Unit) (ε := Unit) (γ₂ := Unit)
    (fun _ _ _ => none) (fun _ _ _ => some ()) (fun _ _ _ => none) (fun _ _ _ => some ())
    (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)
    ⟨.cons 0 () .nil, AssocList.keysOrdered_cons_nil⟩ .nil .nil)) (by decide +kernel)

/-- tiny float format: 2 exponent bits, 2 mantissa bits (5 bits in total) -/
abbrev hcF : Float.Model.Format := { mantissaBitsWithoutImplicit := 2, exponentBits := 2 }

/-- `unpack_beq_unpack_iff` without both validity hypotheses: for `b = b' = 13#5` (a non-canonical
NaN of `hcF`) the left side is `false` (NaN is not `beq` to anything) but the right side holds. -/
theorem j2 : ¬ dropN0% Float.Model.UnpackedFloat.unpack_beq_unpack_iff [3, 4] := fun H =>
  absurd (H (spec := hcF) (b := 13#5) (b' := 13#5)) (by decide +kernel)

/-- `orderedFind?_orderedInsert_self` without both `LawfulEqCmp` and `TransCmp` (keeping
`KeysOrdered`): with the never-equal comparison `fun _ _ => .lt`, inserting into `nil` and
looking the key up again gives `none`. -/
theorem j3 : ¬ dropN0% ofiSelfMain [3, 4] := fun H =>
  absurd (H (α := Nat) (β := Unit) (cmp := fun _ _ => .lt) .nil trivial 0 ()) (by decide +kernel)

#print axioms j1
#print axioms j2
#print axioms j3
