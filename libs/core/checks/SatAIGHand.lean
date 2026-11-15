import Std
import Lean

/-!
Hand pass `SatAIG` (hand15): the 232 unresolved hypotheses of `Std.Sat.AIG.*` (Basic, Cached(Gates)Lemmas,
Lemmas, LawfulOperator, LawfulVecOperator, RefVec, If, RefVecOperator.{Fold,Map,Zip}, Relabel, RelabelNat).
194 necessary, 38 removable (all removable ones dependent-derivable bounds except four).

Reusable models (namespace `SatAIGHand`, all over `α = Nat`):
* AIGs without atoms carry the empty cache (`Cache.WF.empty`), so no hash-map evaluation is needed:
  `A2 = #[false, false]`, `A3`, `AT = #[false, gate(¬0,¬0)]` (node 1 is `true`),
  `AG = #[false, gate(¬0,¬0), gate(0,0)]` (two distinct non-constant nodes: `mkGateCached` on `⟨1, 2⟩`
  really pushes a gate, `AG_go`/`AG_gate`/`AG_and`/`AG_or`/`AG_xor`/`AG_beq`/`AG_imp`/`AG_if`).
  AIGs with atoms build the cache with `Cache.WF.push_cache` on literal maps: `AA = #[false, atom 0]`,
  `AA2 = #[false, atom 0, atom 1]`; lookups go through the library lemmas (`Cache.get?_atom`,
  `Cache.get?_eq_none_iff`, `HashMap.getElem?_insert`), never through `decide`.
* `pushF aig`: `aig` with a `.false` node pushed (cache unchanged, `cacheWF_push`).
* Operators: `opC` (returns the empty AIG: not `LawfulOperator`, `opC_not_lawful`, `nlR`, `nlB`),
  `opT` (returns `AT`), `opId` (lawful identity), `opPush` (pushes a `.false` node and points to it:
  lawful, `LawfulMapOperator` and `LawfulZipOperator`), `opPar` (pushes a node, returns node 0 inverted iff
  the input AIG has size 1: lawful but not chainable, `opPar_bad`, `opPar_not_map`, `opPar_not_zip`);
  vector versions `vopC`, `vopT`, `vopId`, `vopPush`.
* Growth lemmas for the recursive `go`s on concrete inputs (`ite_grow`, `map_grow`, `zip_grow`,
  `fold_grow`), unfolding `go` once and bounding the rest with the library's `go_le_size`.
* `denote` evaluation through `denote_idx_false/atom/gate` (`den0`, `AT_den1`, `AA_den1`, `A2_den1`).
* RelabelNat: `inv2_keys` (keys of an `Inv2` map are atoms of `decls`), `inv1_zero`, `map_AA`.

Removable: `h2`-style bounds of `*_decl_eq` / `go_get_aux` / `chainable` / `denote_*_entry` follow from
`le_size`/`go_le_size` of the (lawful) operator; `hdag1`/`hbounds2` of `denote.go_eq_of_isPrefix` follow from
the prefix; `denote_mkAtom_cached` (a `CacheHit` already says the node is the atom), `mkAtomCached_hit_aig`
(a `CacheHit` forces a cache hit by cache validity), the `Nonempty` hypotheses of
`relabel_unsat_iff_of_(not_)Nonempty` (sibling `relabel_unsat_iff`), and `hinj` when `α` is empty.

`refute_indep` (copied from `checks/StdDepHand.lean`) is included for reuse but not used by the verdicts.
Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/SatAIGHand.lean`.
-/

set_option linter.unusedVariables false
set_option maxErrors 10000

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



/-! ## `refute_indep`: small-value counterexample search for `¬ ∀ xs, P`

Instantiates the binders one by one with small candidates and refutes the instantiated conclusion:
types `Nat`/`Bool`/`Unit` (monads `Id`/`Option`), instances by synthesis, `Nat` 0–3, `Bool`, AIG
values built from node 0 (`.false`, present in every AIG: `ref0`, `vec0`, `entry0`), constant
functions, else `default`/`Classical.ofNonempty`. Prop premises are proved and the conclusion is
refuted by `decide`/`omega`/`simp`/`trivial`/`rfl`. Searches at most 150 proof attempts. -/

namespace RefuteIndep
open Std.Sat

/-- A reference to node 0 of any AIG. -/
def ref0 {α : Type} [DecidableEq α] [Hashable α] (aig : AIG α) : aig.Ref := ⟨0, false, aig.hzero⟩
/-- The inverted reference to node 0. -/
def ref1 {α : Type} [DecidableEq α] [Hashable α] (aig : AIG α) : aig.Ref := ⟨0, true, aig.hzero⟩
/-- A vector of `n` references to node 0. -/
def vec0 {α : Type} [DecidableEq α] [Hashable α] (aig : AIG α) : (n : Nat) → aig.RefVec n
  | 0 => .empty
  | n + 1 => (vec0 aig n).push (ref0 aig)
/-- The empty AIG with a reference to its node 0. -/
def entry0 {α : Type} [DecidableEq α] [Hashable α] : AIG.Entrypoint α := ⟨.empty, ref0 _⟩

open Lean Meta Elab Tactic

/-- `c` applied to fresh metavariables, if its result type unifies with `d` and no metavariable is left. -/
def instAt (c : Name) (d : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let e ← mkConstWithFreshMVarLevels c
    let (xs, bis, r) ← forallMetaTelescopeReducing (← inferType e)
    if ← isDefEq r d then
      for x in xs, bi in bis do
        if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
          let some i ← synthInstance? (← instantiateMVars (← inferType x)) | pure ()
          discard <| isDefEq x i
      let v ← instantiateMVars (mkAppN e xs)
      if !v.hasExprMVar then return some v
    s.restore; return none
  catch _ => s.restore; return none

/-- `c` applied to its leading implicit and instance arguments only, if its type then unifies with `d`. -/
def instAtFn (c : Name) (d : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let e ← mkConstWithFreshMVarLevels c
    let mut e := e
    let mut t ← inferType e
    let mut insts := #[]
    repeat
      let .forallE _ dom b bi := t | break
      if bi.isExplicit then break
      let m ← mkFreshExprMVar dom
      if bi.isInstImplicit then insts := insts.push m
      e := mkApp e m; t := b.instantiate1 m
    if ← isDefEq t d then
      for m in insts do
        unless ← m.mvarId!.isAssigned do
          let some i ← synthInstance? (← instantiateMVars (← inferType m)) | pure ()
          discard <| isDefEq m i
      let v ← instantiateMVars e
      if !v.hasExprMVar then return some v
    s.restore; return none
  catch _ => s.restore; return none

def proveBy (budget : IO.Ref Nat) (ty : Expr) : TacticM (Option Expr) := do
  if (← budget.get) == 0 then return none
  budget.modify (· - 1)
  let s ← saveState
  let msgs := (← getThe Core.State).messages
  let mv ← mkFreshExprMVar ty
  try
    let gs ← withoutRecover <| Tactic.run mv.mvarId! (evalTactic (← `(tactic|
      first | decide | omega | (simp; done) | trivial | rfl | (intro h; simp at h) | (intro h; omega) | (intros; omega) | (intros; simp_all; done) | (simp_all; done))))
    modifyThe Core.State ({ · with messages := msgs })
    if gs.isEmpty then
      let p ← instantiateMVars mv
      unless p.hasExprMVar || p.hasSorry do return some p
    s.restore; modifyThe Core.State ({ · with messages := msgs }); return none
  catch _ => s.restore; modifyThe Core.State ({ · with messages := msgs }); return none

partial def cands (budget : IO.Ref Nat) (d : Expr) (bi : BinderInfo) : TacticM (Array Expr) := do
  let d ← instantiateMVars d
  if bi.isInstImplicit || (← isClass? d).isSome then
    return (← try synthInstance? d catch _ => pure none).toArray
  if ← isProp d then return (← proveBy budget d).toArray
  let dw ← whnfR d
  if let .sort u := dw then
    if ← isLevelDefEq u Level.one then return #[mkConst ``Nat, mkConst ``Bool, mkConst ``Unit]
    if ← isLevelDefEq u Level.zero then return #[mkConst ``True, mkConst ``False]
    return #[]
  if let .forallE _ (.sort _) (.sort _) _ := dw then
    return #[mkConst ``Id [Level.zero], mkConst ``Option [Level.zero]]
  if d.isConstOf ``Nat then return #[0, 1, 2, 3].map mkNatLit
  if d.isConstOf ``Bool then return #[mkConst ``Bool.false, mkConst ``Bool.true]
  if d.isConstOf ``Int then return #[mkIntLit 0, mkIntLit 1, mkIntLit (-1)]
  let mut out := #[]
  for c in [``Std.Sat.AIG.empty, ``ref0, ``ref1, ``vec0, ``entry0] do
    if let some v ← instAt c d then out := out.push v
  unless out.isEmpty do return out
  if dw.isForall then
    for c in [``Std.Sat.AIG.mkAndCached, ``Std.Sat.AIG.mkOrCached, ``Std.Sat.AIG.mkNotCached,
        ``Std.Sat.AIG.mkIfCached, ``Std.Sat.AIG.RefVec.ite, ``Std.Sat.AIG.RefVec.map] do
      if let some v ← instAtFn c d then out := out.push v
    unless out.isEmpty do return out
  if dw.isForall then
    let r ← forallTelescope dw fun xs body => do
      if ← isProp body then return #[]
      let cs ← cands budget body .default
      cs.extract 0 2 |>.mapM (mkLambdaFVars xs ·)
    unless r.isEmpty do return r
  if let some i ← (try synthInstance? (mkApp (mkConst ``Inhabited [← getLevel d]) d) catch _ => pure none) then
    return #[mkApp2 (mkConst ``Inhabited.default [← getLevel d]) d i]
  if let some i ← (try synthInstance? (mkApp (mkConst ``Nonempty [← getLevel d]) d) catch _ => pure none) then
    return #[mkApp2 (mkConst ``Classical.ofNonempty [← getLevel d]) d i]
  return #[]

partial def go (budget : IO.Ref Nat) (e ty : Expr) : TacticM (Option Expr) := do
  if (← budget.get) == 0 then return none
  let ty ← instantiateMVars ty
  let ty ← if ty.isForall then pure ty else whnfR ty
  match ty with
  | .forallE _ d b bi =>
    let cs ← cands budget d bi
    -- a binder the rest does not mention needs only one value
    let cs := if b.hasLooseBVars then cs else cs.extract 0 1
    for c in cs do
      if let some p ← go budget (mkApp e c) (b.instantiate1 c) then return some p
    return none
  | _ =>
    let some np ← proveBy budget (mkNot ty) | return none
    logInfo m!"refute_indep: {e}"
    return some (mkApp np e)

elab "refute_indep" : tactic => do
  let g ← getMainGoal
  let some (h, g') ← observing? g.intro1 | throwError "refute_indep: goal is not a negation"
  g'.withContext do
    let budget ← IO.mkRef 150
    let some p ← go budget (mkFVar h) (← h.getType) | throwError "refute_indep: no counterexample"
    g'.assign p
  replaceMainGoal []

end RefuteIndep

/-! ## Models -/

namespace SatAIGHand
open Std Std.Sat Std.Sat.AIG RefuteIndep

/- Cache validity survives pushing a non-atom declaration. -/
theorem cacheWF_push {α} [Hashable α] [DecidableEq α] {decls : Array (Decl α)} {c : HashMap (Decl α) Nat}
    (h : Cache.WF decls c) (d : Decl α) (hd : ∀ a, d ≠ .atom a) : Cache.WF (decls.push d) c where
  sound := fun decl idx hf => by
    obtain ⟨h1, h2⟩ := h.sound decl idx hf
    exact ⟨by simp; omega, by simp [Array.getElem_push, h1, h2]⟩
  atoms := fun i hi a ha => by
    rw [Array.getElem_push] at ha
    split at ha
    · exact h.atoms i _ a ha
    · exact absurd ha (hd a)

/- aig with a .false node pushed (a lawful, growing step). -/
def pushF {α} [Hashable α] [DecidableEq α] (aig : AIG α) : AIG α where
  decls := aig.decls.push .false
  cache := ⟨aig.cache.val, cacheWF_push aig.cache.property .false (by simp)⟩
  hdag := by
    intro i l r h hg
    rw [Array.getElem_push] at hg
    split at hg
    · exact aig.hdag _ hg
    · cases hg
  hzero := by simp
  hconst := by simp [Array.getElem_push, aig.hzero, aig.hconst]

theorem pushF_size {α} [Hashable α] [DecidableEq α] (aig : AIG α) :
    (pushF aig).decls.size = aig.decls.size + 1 := by simp [pushF]

theorem pushF_decl {α} [Hashable α] [DecidableEq α] (aig : AIG α) (i : Nat) (h1 : i < aig.decls.size) (h2) :
    (pushF aig).decls[i]'h2 = aig.decls[i]'h1 := by simp [pushF, Array.getElem_push, h1]

theorem pushF_last {α} [Hashable α] [DecidableEq α] (aig : AIG α) (h) :
    (pushF aig).decls[aig.decls.size]'h = .false := by simp [pushF]

/- Model AIGs (atom-free ones carry the empty cache). -/
/-- #[false, false]. -/
def A2 : AIG Nat := pushF .empty
/-- #[false, false, false]. -/
def A3 : AIG Nat := pushF A2
/-- #[false, gate(¬0, ¬0)]: node 1 is true. -/
def AT : AIG Nat where
  decls := #[.false, .gate (.mk 0 true) (.mk 0 true)]
  cache := ⟨{}, Cache.WF.empty (by intro i h a; match i, h with | 0, _ => nofun | 1, _ => nofun)⟩
  hdag := by
    intro i l r h hg
    match i, h with
    | 0, _ => cases hg
    | 1, _ => cases hg; simp
  hzero := by simp
  hconst := rfl
/-- #[false, gate(¬0, ¬0), gate(0, 0)]: two distinct non-constant gate nodes (true, false). -/
def AG : AIG Nat where
  decls := #[.false, .gate (.mk 0 true) (.mk 0 true), .gate (.mk 0 false) (.mk 0 false)]
  cache := ⟨{}, Cache.WF.empty (by
    intro i h a; match i, h with | 0, _ => nofun | 1, _ => nofun | 2, _ => nofun)⟩
  hdag := by
    intro i l r h hg
    match i, h with
    | 0, _ => cases hg
    | 1, _ => cases hg; simp
    | 2, _ => cases hg; simp
  hzero := by simp
  hconst := rfl
/-- #[false, atom 0]. -/
def AA : AIG Nat where
  decls := #[.false, .atom 0]
  cache := ⟨(∅ : HashMap (Decl Nat) Nat).insert (.atom 0) 1,
    Cache.WF.push_cache (decls := #[.false])
      (Cache.WF.empty (by intro i h a; match i, h with | 0, _ => nofun)) (by simp)⟩
  hdag := by
    intro i l r h hg
    match i, h with
    | 0, _ => cases hg
    | 1, _ => cases hg
  hzero := by simp
  hconst := rfl
/-- #[false, atom 0, atom 1]. -/
def AA2 : AIG Nat where
  decls := #[.false, .atom 0, .atom 1]
  cache := ⟨((∅ : HashMap (Decl Nat) Nat).insert (.atom 0) 1).insert (.atom 1) 2,
    Cache.WF.push_cache (decls := #[.false, .atom 0]) (Cache.WF.push_cache (decls := #[.false])
      (Cache.WF.empty (by intro i h a; match i, h with | 0, _ => nofun)) (by simp)) (by simp)⟩
  hdag := by
    intro i l r h hg
    match i, h with
    | 0, _ => cases hg
    | 1, _ => cases hg
    | 2, _ => cases hg
  hzero := by simp
  hconst := rfl

/- Reference i of an AIG. -/
def rf (aig : AIG Nat) (i : Nat) (inv : Bool := false) (h : i < aig.decls.size := by decide) : aig.Ref :=
  ⟨i, inv, h⟩

theorem den_false {aig : AIG Nat} {i} {inv} (h) (hd : aig.decls[i]'h = .false) (assign) :
    ⟦aig, ⟨i, inv, h⟩, assign⟧ = inv := denote_idx_false hd
theorem den0 (aig : AIG Nat) (inv assign) : ⟦aig, ⟨0, inv, aig.hzero⟩, assign⟧ = inv :=
  denote_idx_false aig.hconst
theorem AT_den1 (inv assign h) : ⟦AT, ⟨1, inv, h⟩, assign⟧ = !inv := by
  rw [denote_idx_gate (lhs := .mk 0 true) (rhs := .mk 0 true) rfl]
  simp [denote_idx_false (aig := AT) (start := 0) rfl]
theorem AA_den1 (inv assign h) : ⟦AA, ⟨1, inv, h⟩, assign⟧ = (assign 0 ^^ inv) :=
  denote_idx_atom (a := 0) rfl
theorem A2_den1 (inv assign h) : ⟦A2, ⟨1, inv, h⟩, assign⟧ = inv := denote_idx_false rfl

theorem AA_mem (x : Nat) : x ∈ AA ↔ x = 0 := by
  show Decl.atom x ∈ #[Decl.false, .atom 0] ↔ _; simp
theorem AA2_mem (x : Nat) : x ∈ AA2 ↔ x = 0 ∨ x = 1 := by
  show Decl.atom x ∈ #[Decl.false, .atom 0, .atom 1] ↔ _; simp
theorem empty_mem (x : Nat) : ¬ x ∈ (AIG.empty : AIG Nat) := by
  show ¬ Decl.atom x ∈ #[Decl.false]; simp

/- Operators: opC shrinks to the empty AIG (unlawful), opId is the identity, opPush pushes a
.false node and points to it (lawful, chainable), opPar pushes a node and returns node 0 inverted
iff the input AIG has size 1 (lawful, not chainable). -/
def opC {β : AIG Nat → Type} : (aig : AIG Nat) → β aig → Entrypoint Nat := fun _ _ => entry0
def opT {β : AIG Nat → Type} : (aig : AIG Nat) → β aig → Entrypoint Nat := fun _ _ => ⟨AT, rf AT 1⟩
def opId {β : AIG Nat → Type} : (aig : AIG Nat) → β aig → Entrypoint Nat := fun aig _ => ⟨aig, ref0 aig⟩
def opPush {β : AIG Nat → Type} : (aig : AIG Nat) → β aig → Entrypoint Nat :=
  fun aig _ => ⟨pushF aig, ⟨aig.decls.size, false, by simp [pushF_size]⟩⟩
def opPar {β : AIG Nat → Type} : (aig : AIG Nat) → β aig → Entrypoint Nat :=
  fun aig _ => ⟨pushF aig, ⟨0, decide (aig.decls.size = 1), (pushF aig).hzero⟩⟩

instance {β} : LawfulOperator Nat β opId where
  le_size _ _ := Nat.le_refl _
  decl_eq _ _ _ _ _ := rfl
instance {β} : LawfulOperator Nat β opPush where
  le_size aig _ := by simp [opPush, pushF_size]
  decl_eq aig _ idx h1 h2 := pushF_decl aig idx h1 h2
instance {β} : LawfulOperator Nat β opPar where
  le_size aig _ := by simp [opPar, pushF_size]
  decl_eq aig _ idx h1 h2 := pushF_decl aig idx h1 h2
instance : RefVec.LawfulMapOperator Nat opPush where
  chainable aig _ _ _ assign := by
    simp only [opPush]
    rw [den_false _ (pushF_last _ _), den_false _ (pushF_last _ _)]
instance : RefVec.LawfulZipOperator Nat opPush where
  chainable aig _ _ _ assign := by
    simp only [opPush]
    rw [den_false _ (pushF_last _ _), den_false _ (pushF_last _ _)]

theorem opC_not_lawful {β : AIG Nat → Type} (x : β A2) : ¬ LawfulOperator Nat β opC :=
  fun h => absurd (h.le_size A2 x) (by show ¬ 2 ≤ 1; omega)
theorem opPar_not_map : ¬ RefVec.LawfulMapOperator Nat opPar := fun h => by
  have := h.chainable .empty (ref0 _) (ref0 _) (by simp [opPar, pushF_size]) (fun _ => false)
  simp only [opPar] at this
  rw [den0, den0] at this
  revert this; decide
theorem opPar_not_zip : ¬ RefVec.LawfulZipOperator Nat opPar := fun h => by
  have := h.chainable .empty ⟨ref0 _, ref0 _⟩ ⟨ref0 _, ref0 _⟩ (by simp [opPar, pushF_size]) (fun _ => false)
  simp only [opPar] at this
  rw [den0, den0] at this
  revert this; decide

/- Vector operators. -/
def vopC {β : AIG Nat → Nat → Type} : {len : Nat} → (aig : AIG Nat) → β aig len → RefVecEntry Nat len :=
  fun {len} _ _ => ⟨.empty, vec0 _ len⟩
def vopId {β : AIG Nat → Nat → Type} : {len : Nat} → (aig : AIG Nat) → β aig len → RefVecEntry Nat len :=
  fun {len} aig _ => ⟨aig, vec0 aig len⟩
def vopPush {β : AIG Nat → Nat → Type} : {len : Nat} → (aig : AIG Nat) → β aig len → RefVecEntry Nat len :=
  fun {len} aig _ => ⟨pushF aig, vec0 _ len⟩
def vopT {β : AIG Nat → Nat → Type} : {len : Nat} → (aig : AIG Nat) → β aig len → RefVecEntry Nat len :=
  fun {len} _ _ => ⟨AT, vec0 _ len⟩
instance {β} : LawfulVecOperator Nat β vopId where
  le_size _ _ := Nat.le_refl _
  decl_eq _ _ _ _ _ := rfl
instance {β} : LawfulVecOperator Nat β vopPush where
  le_size aig _ := by simp [vopPush, pushF_size]
  decl_eq aig _ idx h1 h2 := pushF_decl aig idx h1 h2
theorem vopC_not_lawful {β : AIG Nat → Nat → Type} (x : β A2 0) : ¬ LawfulVecOperator Nat β vopC :=
  fun h => absurd (h.le_size A2 x) (by show ¬ 2 ≤ 1; omega)

end SatAIGHand

/-! ## Std.Sat.AIG.Basic -/

namespace SatAIGHand
open Std Std.Sat Std.Sat.AIG RefuteIndep

theorem nil_noatoms : ∀ (i : Nat) (h : i < (#[] : Array (Decl Nat)).size) (a : Nat), (#[] : Array (Decl Nat))[i] ≠ .atom a :=
  fun i h => by simp at h
theorem f_noatoms : ∀ (i : Nat) (h : i < (#[.false] : Array (Decl Nat)).size) (a : Nat),
    (#[.false] : Array (Decl Nat))[i] ≠ .atom a := by
  intro i h a; match i, h with | 0, _ => nofun

-- `Std.Sat.AIG.Cache.WF.sound`: the map {false ↦ 0} claims index 0 of the empty array.
theorem WF_sound_5 : ¬ drop0% Std.Sat.AIG.Cache.WF.sound 5 := fun H => by
  obtain ⟨h, _⟩ := H (decls := (#[] : Array (Decl Nat))) (cache := (∅ : HashMap (Decl Nat) Nat).insert .false 0)
    .false 0 (by simp)
  simp at h

-- `Std.Sat.AIG.Cache.WF.sound`: the empty cache of the empty array; index 0 is out of bounds.
theorem WF_sound_8 : ¬ drop0% Std.Sat.AIG.Cache.WF.sound 8 := fun H => by
  obtain ⟨h, _⟩ := H (decls := (#[] : Array (Decl Nat))) (cache := ∅) (Cache.WF.empty nil_noatoms) .false 0
  simp at h

-- `Std.Sat.AIG.Cache.WF.atoms`: #[atom 0] with the empty cache.
theorem WF_atoms_5 : ¬ drop0% Std.Sat.AIG.Cache.WF.atoms 5 := fun H => by
  have := H (decls := #[Decl.atom (0 : Nat)]) (cache := ∅) 0 (by decide) 0 rfl
  simp at this

-- `Std.Sat.AIG.Cache.WF.atoms`: index 0 of the empty array (empty cache).
theorem WF_atoms_7 : ¬ indep0% Std.Sat.AIG.Cache.WF.atoms 7 := fun H => by
  have := H (decls := (#[] : Array (Decl Nat))) (cache := ∅) (Cache.WF.empty nil_noatoms) 0
  simp at this

-- `Std.Sat.AIG.Cache.WF.atoms`: #[false] with the empty cache, i = 0, a = 0.
theorem WF_atoms_9 : ¬ drop0% Std.Sat.AIG.Cache.WF.atoms 9 := fun H => by
  have := H (decls := #[Decl.false]) (cache := ∅) (Cache.WF.empty f_noatoms) 0 (by decide) 0
  simp at this

-- `Std.Sat.AIG.Cache.WF.empty`: the empty cache is not valid for #[atom 0].
theorem WF_empty_4 : ¬ drop0% Std.Sat.AIG.Cache.WF.empty 4 := fun H => by
  have := (H (decls := #[Decl.atom (0 : Nat)])).atoms 0 (by decide) 0 rfl
  simp at this

-- `Std.Sat.AIG.Cache.WF.push_cache`: the invalid cache {false ↦ 5} for the empty array.
theorem WF_push_cache_6 : ¬ drop0% Std.Sat.AIG.Cache.WF.push_cache 6 := fun H => by
  have := (H (decls := (#[] : Array (Decl Nat))) (cache := (∅ : HashMap (Decl Nat) Nat).insert .false 5)
    (decl := .atom 0) (by simp)).sound .false 5 (by rw [HashMap.getElem?_insert, if_neg (by decide), HashMap.getElem?_insert_self])
  obtain ⟨h, _⟩ := this
  simp at h

-- `Std.Sat.AIG.Cache.WF.push_cache`: pushing atom 0 a second time onto #[atom 0] (cache hit).
theorem WF_push_cache_7 : ¬ drop0% Std.Sat.AIG.Cache.WF.push_cache 7 := fun H => by
  have hwf : Cache.WF ((#[] : Array (Decl Nat)).push (.atom 0)) ((∅ : HashMap (Decl Nat) Nat).insert (.atom 0) 0) :=
    Cache.WF.push_cache (Cache.WF.empty nil_noatoms) (by simp)
  have := (H (decl := .atom 0) hwf).atoms 0 (by decide) 0 rfl
  simp at this

-- `Std.Sat.AIG.Cache.get?_bounds`: the empty cache of the empty array, idx = 0.
theorem get?_bounds_7 : ¬ drop0% Std.Sat.AIG.Cache.get?_bounds 7 := fun H => by
  have := H (decls := (#[] : Array (Decl Nat))) (idx := 0) ⟨∅, Cache.WF.empty nil_noatoms⟩ .false
  simp at this

-- `Std.Sat.AIG.Cache.get?_property`: the empty cache has no hit.
theorem get?_property_7 : ¬ indep0% Std.Sat.AIG.Cache.get?_property 7 := fun H => by
  have := H (decls := (#[] : Array (Decl Nat))) (idx := 0) ⟨∅, Cache.WF.empty nil_noatoms⟩ .false
  simp at this

-- `Std.Sat.AIG.Cache.get?_atom`: index 0 of the empty array.
theorem get?_atom_6 : ¬ indep0% Std.Sat.AIG.Cache.get?_atom 6 := fun H => by
  have := H (decls := (#[] : Array (Decl Nat))) ⟨∅, Cache.WF.empty nil_noatoms⟩ (i := 0) (a := 0)
  simp at this

-- `Std.Sat.AIG.Cache.get?_atom`: node 0 of #[false] is not an atom.
theorem get?_atom_8 : ¬ indep0% Std.Sat.AIG.Cache.get?_atom 8 := fun H => by
  have := H (decls := #[Decl.false]) ⟨∅, Cache.WF.empty f_noatoms⟩ (i := 0) (hi := by decide) (a := 0)
  simp at this

-- `Std.Sat.AIG.Cache.ofAtoms.complete_succ`: #[atom 0, false], empty map, idx = 1; atom 0 is missing.
theorem complete_succ_6 : ¬ drop0% Std.Sat.AIG.Cache.ofAtoms.complete_succ 6 := fun H => by
  have := H (decls := #[Decl.atom (0 : Nat), .false]) (map := ∅) (idx := 1)
    (by intro h a; simp) 0 (by decide) (by decide) 0 rfl
  simp at this

-- `Std.Sat.AIG.Cache.ofAtoms.complete_succ`: #[atom 0], empty map, idx = 0.
theorem complete_succ_7 : ¬ drop0% Std.Sat.AIG.Cache.ofAtoms.complete_succ 7 := fun H => by
  have := H (decls := #[Decl.atom (0 : Nat)]) (map := ∅) (idx := 0)
    (by intro i h hi; omega) 0 (by decide) (by decide) 0 rfl
  simp at this

-- `Std.Sat.AIG.Cache.ofAtoms.complete_succ`: #[false, atom 0], empty map, idx = 0, i = 1.
theorem complete_succ_10 : ¬ drop0% Std.Sat.AIG.Cache.ofAtoms.complete_succ 10 := fun H => by
  have := H (decls := #[Decl.false, .atom (0 : Nat)]) (map := ∅) (idx := 0)
    (by intro i h hi; omega) (by intro h a; simp) 1 (by decide) 0 rfl
  simp at this

-- `Std.Sat.AIG.Cache.ofAtoms.complete_succ`: #[false], empty map, i = 0 (not an atom).
theorem complete_succ_12 : ¬ drop0% Std.Sat.AIG.Cache.ofAtoms.complete_succ 12 := fun H => by
  have := H (decls := #[Decl.false]) (map := (∅ : HashMap (Decl Nat) Nat)) (idx := 0)
    (by intro i h hi; omega) (by intro h a; simp) 0 (by decide) (by decide) 0
  simp at this

-- `Std.Sat.AIG.atom_unique`: index 5 of AA = #[false, atom 0], the other index at the atom.
theorem atom_unique_6 : ¬ indep0% Std.Sat.AIG.atom_unique 6 := fun H => by
  have := H (aig := AA) (i := 5) (j := 1) (hj := by decide) (a := 0) rfl
  revert this; decide

-- `Std.Sat.AIG.atom_unique`: index 5 of AA = #[false, atom 0], the other index at the atom.
theorem atom_unique_7 : ¬ indep0% Std.Sat.AIG.atom_unique 7 := fun H => by
  have := H (aig := AA) (i := 1) (j := 5) (hi := by decide) (a := 0) rfl
  revert this; decide

-- `Std.Sat.AIG.atom_unique`: AA = #[false, atom 0], i = 0, j = 1.
theorem atom_unique_9 : ¬ drop0% Std.Sat.AIG.atom_unique 9 := fun H => by
  have := H (aig := AA) (i := 0) (j := 1) (hi := by decide) (hj := by decide) (a := 0) rfl
  simp at this

-- `Std.Sat.AIG.atom_unique`: AA = #[false, atom 0], i = 1, j = 0.
theorem atom_unique_10 : ¬ drop0% Std.Sat.AIG.atom_unique 10 := fun H => by
  have := H (aig := AA) (i := 1) (j := 0) (hi := by decide) (hj := by decide) (a := 0) rfl
  simp at this

end SatAIGHand

/-! ## Std.Sat.AIG.CachedLemmas, CachedGatesLemmas -/

namespace SatAIGHand
open Std Std.Sat Std.Sat.AIG RefuteIndep

/- mkGateCached on the two distinct non-constant gate nodes 1, 2 of AG pushes a new gate. -/
theorem AG_go (l r : AG.Ref) (hl : l.gate = 1) (hr : r.gate = 2) :
    (mkGateCached.go AG ⟨l, r⟩).aig.decls.size = 4 := by
  obtain ⟨lg, li, lh⟩ := l
  obtain ⟨rg, ri, rh⟩ := r
  simp only at hl hr
  subst hl hr
  unfold mkGateCached.go
  dsimp only
  split
  · next hit h =>
    exfalso
    rw [Cache.get?_eq_some_iff] at h
    simp [AG] at h
  · split
    all_goals first
      | (exfalso; simp_all [getConstant, AG]; done)
      | skip
    rw [if_neg (by decide)]; rfl

theorem AG_gate (l r : AG.Ref) (hl : l.gate = 1) (hr : r.gate = 2) :
    3 < (AG.mkGateCached ⟨l, r⟩).aig.decls.size := by
  unfold mkGateCached; dsimp only
  rw [if_pos (by rw [hl, hr]; decide), AG_go l r hl hr]; decide

/- The input ⟨1, 2⟩ of AG. -/
def AGin : AG.BinaryInput := ⟨rf AG 1, rf AG 2⟩

theorem AG_and : 3 < (AG.mkAndCached AGin).aig.decls.size := AG_gate _ _ rfl rfl
theorem AG_or : 3 < (AG.mkOrCached AGin).aig.decls.size := AG_gate _ _ rfl rfl
theorem AG_imp : 3 < (AG.mkImpCached AGin).aig.decls.size := AG_gate _ _ rfl rfl
theorem AG_xor : 3 < (AG.mkXorCached AGin).aig.decls.size := by
  unfold mkXorCached; dsimp only
  refine Nat.lt_of_lt_of_le ?_ (mkGateCached_le_size _ _)
  refine Nat.lt_of_lt_of_le ?_ (mkGateCached_le_size _ _)
  exact AG_gate _ _ rfl rfl
theorem AG_beq : 3 < (AG.mkBEqCached AGin).aig.decls.size := by
  unfold mkBEqCached; dsimp only
  refine Nat.lt_of_lt_of_le ?_ (mkGateCached_le_size _ _)
  refine Nat.lt_of_lt_of_le ?_ (mkGateCached_le_size _ _)
  exact AG_gate _ _ rfl rfl

/- mkAtomCached of a new atom pushes it. -/
theorem AA_atom1 : (AA.mkAtomCached 1).aig.decls.size = 3 := by
  rw [mkAtomCached_miss_aig AA (by rw [Cache.get?_eq_none_iff]; show ((∅ : HashMap (Decl Nat) Nat).insert (.atom 0) 1)[Decl.atom 1]? = none; simp)]
  rfl

-- `Std.Sat.AIG.mkNotCached_decl_eq`: removable (dependent), mkNotCached returns the same AIG, so h is h2.
theorem mkNotCached_decl_eq_6 : indep% Std.Sat.AIG.mkNotCached_decl_eq 6 := by
  intro α _ _ idx aig gate h2; exact h2

-- `Std.Sat.AIG.mkNotCached_decl_eq`: removable (dependent), mkNotCached returns the same AIG, so h2 is h.
theorem mkNotCached_decl_eq_7 : indep% Std.Sat.AIG.mkNotCached_decl_eq 7 := by
  intro α _ _ idx aig gate h; exact h

-- `Std.Sat.AIG.mkAndCached_decl_eq`: AG with input ⟨1, 2⟩ grows to size 4; idx = 3.
theorem mkAndCached_decl_eq_6 : ¬ indep0% Std.Sat.AIG.mkAndCached_decl_eq 6 :=
  fun H => absurd (H (idx := 3) (aig := AG) (input := AGin) (h2 := AG_and)) (by decide)

-- `Std.Sat.AIG.mkAndCached_decl_eq`: removable (dependent), mkAndCached is a lawful operator.
theorem mkAndCached_decl_eq_7 : indep% Std.Sat.AIG.mkAndCached_decl_eq 7 := by
  intro α _ _ idx aig input h; exact LawfulOperator.lt_size_of_lt_aig_size (f := mkAndCached) aig input h

-- `Std.Sat.AIG.mkOrCached_decl_eq`: AG with input ⟨1, 2⟩ grows to size 4; idx = 3.
theorem mkOrCached_decl_eq_6 : ¬ indep0% Std.Sat.AIG.mkOrCached_decl_eq 6 :=
  fun H => absurd (H (idx := 3) (aig := AG) (input := AGin) (h2 := AG_or)) (by decide)

-- `Std.Sat.AIG.mkOrCached_decl_eq`: removable (dependent), mkOrCached is a lawful operator.
theorem mkOrCached_decl_eq_7 : indep% Std.Sat.AIG.mkOrCached_decl_eq 7 := by
  intro α _ _ idx aig input h; exact LawfulOperator.lt_size_of_lt_aig_size (f := mkOrCached) aig input h

-- `Std.Sat.AIG.mkXorCached_decl_eq`: AG with input ⟨1, 2⟩ grows; idx = 3.
theorem mkXorCached_decl_eq_6 : ¬ indep0% Std.Sat.AIG.mkXorCached_decl_eq 6 :=
  fun H => absurd (H (idx := 3) (aig := AG) (input := AGin) (h2 := AG_xor)) (by decide)

-- `Std.Sat.AIG.mkXorCached_decl_eq`: removable (dependent), mkXorCached is a lawful operator.
theorem mkXorCached_decl_eq_7 : indep% Std.Sat.AIG.mkXorCached_decl_eq 7 := by
  intro α _ _ idx aig input h; exact LawfulOperator.lt_size_of_lt_aig_size (f := mkXorCached) aig input h

-- `Std.Sat.AIG.mkBEqCached_decl_eq`: AG with input ⟨1, 2⟩ grows; idx = 3.
theorem mkBEqCached_decl_eq_6 : ¬ indep0% Std.Sat.AIG.mkBEqCached_decl_eq 6 :=
  fun H => absurd (H (idx := 3) (aig := AG) (input := AGin) (h2 := AG_beq)) (by decide)

-- `Std.Sat.AIG.mkBEqCached_decl_eq`: removable (dependent), mkBEqCached is a lawful operator.
theorem mkBEqCached_decl_eq_7 : indep% Std.Sat.AIG.mkBEqCached_decl_eq 7 := by
  intro α _ _ idx aig input h; exact LawfulOperator.lt_size_of_lt_aig_size (f := mkBEqCached) aig input h

-- `Std.Sat.AIG.mkImpCached_decl_eq`: AG with input ⟨1, 2⟩ grows; idx = 3.
theorem mkImpCached_decl_eq_6 : ¬ indep0% Std.Sat.AIG.mkImpCached_decl_eq 6 :=
  fun H => absurd (H (idx := 3) (aig := AG) (input := AGin) (h2 := AG_imp)) (by decide)

-- `Std.Sat.AIG.mkImpCached_decl_eq`: removable (dependent), mkImpCached is a lawful operator.
theorem mkImpCached_decl_eq_7 : indep% Std.Sat.AIG.mkImpCached_decl_eq 7 := by
  intro α _ _ idx aig input h; exact LawfulOperator.lt_size_of_lt_aig_size (f := mkImpCached) aig input h

-- `Std.Sat.AIG.denote_mkAtom_cached`: removable, the cache hit hit itself says node hit.idx is atom v.
theorem denote_mkAtom_cached_7 : drop% Std.Sat.AIG.denote_mkAtom_cached 7 := by
  intro α _ _ v assign aig hit
  rw [denote_idx_atom hit.hvalid]; simp

-- `Std.Sat.AIG.mkAtomCached_hit_aig`: removable, a CacheHit for atom var makes the cache lookup hit
-- (cache validity), so the original lemma applies.
theorem mkAtomCached_hit_aig_6 : drop% Std.Sat.AIG.mkAtomCached_hit_aig 6 := by
  intro α _ _ var aig hit
  exact mkAtomCached_hit_aig aig (aig.cache.get?_atom hit.hvalid)

-- `Std.Sat.AIG.mkAtomCached_miss_aig`: atom 0 is already in AA, nothing is pushed.
theorem mkAtomCached_miss_aig_5 : ¬ drop0% Std.Sat.AIG.mkAtomCached_miss_aig 5 := fun H => by
  have h1 := H (aig := AA) (var := 0)
  rw [mkAtomCached_hit_aig AA (AA.cache.get?_atom (i := 1) (hi := by decide) rfl)] at h1
  have := congrArg Array.size h1
  revert this; decide

-- `Std.Sat.AIG.mkAtomCached_decl_eq`: adding atom 1 to AA grows it to size 3; idx = 2.
theorem mkAtomCached_decl_eq_6 : ¬ indep0% Std.Sat.AIG.mkAtomCached_decl_eq 6 :=
  fun H => absurd (H (aig := AA) (var := 1) (idx := 2) (hbound := by rw [AA_atom1]; decide)) (by decide)

-- `Std.Sat.AIG.mkAtomCached_decl_eq`: removable (dependent), mkAtomCached never shrinks the AIG.
theorem mkAtomCached_decl_eq_7 : indep% Std.Sat.AIG.mkAtomCached_decl_eq 7 := by
  intro α _ _ aig var idx h; exact Nat.lt_of_lt_of_le h (mkAtomCached_le_size aig var)

-- `Std.Sat.AIG.mkGateCached.go_decl_eq`: removable (dependent), go never shrinks the AIG.
theorem mkGateCached_go_decl_eq_6 : indep% Std.Sat.AIG.mkGateCached.go_decl_eq 6 := by
  intro α _ _ aig input idx h2; exact Nat.lt_of_lt_of_le h2 (mkGateCached.go_le_size aig input)

-- `Std.Sat.AIG.mkGateCached.go_decl_eq`: go on AG with input ⟨1, 2⟩ grows to size 4; idx = 3.
theorem mkGateCached_go_decl_eq_7 : ¬ indep0% Std.Sat.AIG.mkGateCached.go_decl_eq 7 :=
  fun H => absurd (H (aig := AG) (input := AGin) (idx := 3) (by rw [AG_go _ _ rfl rfl]; decide)) (by decide)

-- `Std.Sat.AIG.mkGateCached_decl_eq`: removable (dependent), mkGateCached never shrinks the AIG.
theorem mkGateCached_decl_eq_6 : indep% Std.Sat.AIG.mkGateCached_decl_eq 6 := by
  intro α _ _ aig input idx h2; exact Nat.lt_of_lt_of_le h2 (mkGateCached_le_size aig input)

-- `Std.Sat.AIG.mkGateCached_decl_eq`: AG with input ⟨1, 2⟩ grows to size 4; idx = 3.
theorem mkGateCached_decl_eq_7 : ¬ indep0% Std.Sat.AIG.mkGateCached_decl_eq 7 :=
  fun H => absurd (H (aig := AG) (input := AGin) (idx := 3) AG_and) (by decide)

-- `Std.Sat.AIG.denote_gate_push`: aig1 = empty, aig2 = #[false, false], input ⟨true, true⟩.
theorem denote_gate_push_8 : ¬ drop0% Std.Sat.AIG.denote_gate_push 8 := fun H => by
  have := H (aig1 := .empty) (aig2 := A2) (input := ⟨ref1 _, ref1 _⟩) (hidx := by decide) (assign := fun _ => false)
  simp only [ref1] at this
  rw [den0, denote_idx_false (aig := A2) rfl] at this
  revert this; decide

end SatAIGHand

/-! ## Std.Sat.AIG.Lemmas, LawfulOperator, LawfulVecOperator, RefVec -/

namespace SatAIGHand
open Std Std.Sat Std.Sat.AIG RefuteIndep

theorem go_atom {decls : Array (Decl Nat)} {x a} {assign h1 h2} (h : decls[x]'h1 = .atom a) :
    denote.go x decls assign h1 h2 = assign a := by
  unfold denote.go; split <;> simp_all
theorem go_false {decls : Array (Decl Nat)} {x} {assign h1 h2} (h : decls[x]'h1 = .false) :
    denote.go x decls assign h1 h2 = false := by
  unfold denote.go; split <;> simp_all

abbrev E0 : AIG Nat := AIG.empty

theorem dag_nil : IsDAG Nat #[] := fun i _ _ h => by simp at h
theorem dag_atom0 : IsDAG Nat #[.atom 0] := fun i _ _ h hg => by
  match i, h with | 0, _ => cases hg

/- A one-element vector. -/
def vec1 (aig : AIG Nat) (r : aig.Ref) : aig.RefVec 1 := RefVec.empty.push r
theorem vec1_get (aig : AIG Nat) (r : aig.Ref) (h) : (vec1 aig r).get 0 h = r :=
  RefVec.get_push_ref_eq _ _

-- `Std.Sat.AIG.IsPrefix.size_le`: #[false] is longer than #[].
theorem IsPrefix_size_le_3 : ¬ drop0% Std.Sat.AIG.IsPrefix.size_le 3 :=
  fun H => absurd (H (α := Nat) (decls1 := #[.false]) (decls2 := #[])) (by decide)

-- `Std.Sat.AIG.IsPrefix.idx_eq`: #[false] is not a prefix of #[].
theorem IsPrefix_idx_eq_3 : ¬ indep0% Std.Sat.AIG.IsPrefix.idx_eq 3 :=
  fun H => absurd (H (α := Nat) (decls1 := #[.false]) (decls2 := #[]) (idx := 0) (h := by decide)).size_le (by decide)

-- `Std.Sat.AIG.IsPrefix.idx_eq`: index 0 of the empty array.
theorem IsPrefix_idx_eq_5 : ¬ indep0% Std.Sat.AIG.IsPrefix.idx_eq 5 :=
  fun H => absurd (H (α := Nat) (decls1 := #[]) (decls2 := #[]) IsPrefix.rfl (idx := 0)) (by decide)

-- `Std.Sat.AIG.denote.go_eq_of_isPrefix`: removable (dependent), a prefix of a DAG is a DAG.
theorem go_eq_of_isPrefix_5 : indep% Std.Sat.AIG.denote.go_eq_of_isPrefix 5 := by
  intro α assign decls1 decls2 start hdag2 hb1 hb2 hp i l r h hg
  exact hdag2 (Nat.lt_of_lt_of_le h hp.size_le) (by rw [hp.idx_eq i h]; exact hg)

-- `Std.Sat.AIG.denote.go_eq_of_isPrefix`: #[false] is a prefix of #[false, gate(1, 1)], which is not a DAG.
theorem go_eq_of_isPrefix_6 : ¬ indep0% Std.Sat.AIG.denote.go_eq_of_isPrefix 6 := fun H => by
  have := H (α := Nat) (assign := fun _ => false) (decls1 := #[.false]) (decls2 := #[.false].push (.gate (.mk 1 false) (.mk 1 false)))
    (start := 0) (hdag1 := IsDAG.empty) (hbounds1 := by decide) (hbounds2 := by decide) IsPrefix_push
  have := this (i := 1) (lhs := .mk 1 false) (rhs := .mk 1 false) (by decide) rfl
  simp at this

-- `Std.Sat.AIG.denote.go_eq_of_isPrefix`: #[] is a prefix of #[false], start = 0.
theorem go_eq_of_isPrefix_7 : ¬ indep0% Std.Sat.AIG.denote.go_eq_of_isPrefix 7 := fun H =>
  absurd (H (assign := fun _ => false) (decls1 := #[]) (decls2 := (#[] : Array (Decl Nat)).push .false) (start := 0)
    (hdag1 := dag_nil) (hdag2 := IsDAG.empty) (hbounds2 := by decide) IsPrefix_push) (by decide)

-- `Std.Sat.AIG.denote.go_eq_of_isPrefix`: removable (dependent), start < decls1.size ≤ decls2.size.
theorem go_eq_of_isPrefix_8 : indep% Std.Sat.AIG.denote.go_eq_of_isPrefix 8 := by
  intro α assign decls1 decls2 start hdag1 hdag2 hb1 hp
  exact Nat.lt_of_lt_of_le hb1 hp.size_le

-- `Std.Sat.AIG.denote.go_eq_of_isPrefix`: #[false] vs #[atom 0] at node 0 under the all-true assignment.
theorem go_eq_of_isPrefix_9 : ¬ drop0% Std.Sat.AIG.denote.go_eq_of_isPrefix 9 := fun H => by
  have := H (assign := fun _ => true) (decls1 := #[.false]) (decls2 := #[.atom 0]) (start := 0)
    (hdag1 := IsDAG.empty) (hdag2 := dag_atom0) (hbounds1 := by decide) (hbounds2 := by decide)
  rw [go_atom (a := 0) rfl, go_false rfl] at this
  simp at this

-- `Std.Sat.AIG.denote.eq_of_isPrefix`: #[false, false] is not a prefix of the empty AIG.
theorem denote_eq_of_isPrefix_6 : ¬ indep0% Std.Sat.AIG.denote.eq_of_isPrefix 6 := fun H =>
  absurd (H (assign := fun _ => false) (entry := ⟨A2, ref0 _⟩) (newAIG := E0)).size_le (by decide)

/-! ### LawfulOperator -/

-- `Std.Sat.AIG.LawfulOperator.le_size`: opC maps #[false, false] to the empty AIG.
theorem LO_le_size_5 : ¬ drop0% Std.Sat.AIG.LawfulOperator.le_size 5 :=
  fun H => absurd (H (β := fun _ => Unit) (f := opC) A2 ()) (by show ¬ 2 ≤ 1; omega)

-- `Std.Sat.AIG.LawfulOperator.decl_eq`: opT replaces node 1 (false) of #[false, false] by a gate.
theorem LO_decl_eq_5 : ¬ drop0% Std.Sat.AIG.LawfulOperator.decl_eq 5 :=
  fun H => absurd (H (β := fun _ => Unit) (f := opT) A2 () 1 (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.LawfulOperator.decl_eq`: the lawful opPush grows the empty AIG; idx = 1.
theorem LO_decl_eq_9 : ¬ indep0% Std.Sat.AIG.LawfulOperator.decl_eq 9 :=
  fun H => absurd (H (β := fun _ => Unit) (f := opPush) (aig := E0) (input := ()) (idx := 1)
    (h2 := by decide)) (by decide)

-- `Std.Sat.AIG.LawfulOperator.decl_eq`: removable (dependent), le_size of the instance itself.
theorem LO_decl_eq_10 : indep% Std.Sat.AIG.LawfulOperator.decl_eq 10 := by
  intro α _ _ β f self aig input idx h1
  exact Nat.lt_of_lt_of_le h1 (self.le_size aig input)

-- `Std.Sat.AIG.LawfulOperator.isPrefix_aig`: opC on #[false, false].
theorem LO_isPrefix_aig_5 : ¬ drop0% Std.Sat.AIG.LawfulOperator.isPrefix_aig 5 :=
  fun H => absurd (H (β := fun _ => Unit) (f := opC) A2 ()).size_le (by show ¬ 2 ≤ 1; omega)

-- `Std.Sat.AIG.LawfulOperator.lt_size`: opC on node 1 of #[false, false].
theorem LO_lt_size_5 : ¬ drop0% Std.Sat.AIG.LawfulOperator.lt_size 5 :=
  fun H => absurd (H (β := fun _ => Unit) (f := opC) ⟨A2, rf A2 1⟩ ()) (by show ¬ 1 < 1; omega)

-- `Std.Sat.AIG.LawfulOperator.lt_size_of_lt_aig_size`: opC on #[false, false], x = 1.
theorem LO_lt_size_of_lt_aig_size_5 : ¬ drop0% Std.Sat.AIG.LawfulOperator.lt_size_of_lt_aig_size 5 :=
  fun H => absurd (H (β := fun _ => Unit) (f := opC) (x := 1) A2 () (by decide)) (by show ¬ 1 < 1; omega)

-- `Std.Sat.AIG.LawfulOperator.lt_size_of_lt_aig_size`: the identity operator on the empty AIG, x = 1.
theorem LO_lt_size_of_lt_aig_size_9 : ¬ drop0% Std.Sat.AIG.LawfulOperator.lt_size_of_lt_aig_size 9 :=
  fun H => absurd (H (β := fun _ => Unit) (f := opId) (x := 1) E0 ()) (by decide)

-- `Std.Sat.AIG.LawfulOperator.le_size_of_le_aig_size`: opC on #[false, false], x = 2.
theorem LO_le_size_of_le_aig_size_5 : ¬ drop0% Std.Sat.AIG.LawfulOperator.le_size_of_le_aig_size 5 :=
  fun H => absurd (H (β := fun _ => Unit) (f := opC) (x := 2) A2 () (by decide)) (by show ¬ 2 ≤ 1; omega)

-- `Std.Sat.AIG.LawfulOperator.le_size_of_le_aig_size`: the identity operator on the empty AIG, x = 2.
theorem LO_le_size_of_le_aig_size_9 : ¬ drop0% Std.Sat.AIG.LawfulOperator.le_size_of_le_aig_size 9 :=
  fun H => absurd (H (β := fun _ => Unit) (f := opId) (x := 2) E0 ()) (by decide)

-- `Std.Sat.AIG.LawfulOperator.denote_input_entry`: opT turns node 1 of #[false, false] into true.
theorem LO_denote_input_entry_5 : ¬ drop0% Std.Sat.AIG.LawfulOperator.denote_input_entry 5 := fun H => by
  have := H (β := fun _ => Unit) (f := opT) (assign := fun _ => false) (entry := ⟨A2, rf A2 1⟩) (input := ())
    (h := by decide)
  simp only [opT, rf] at this
  rw [AT_den1, A2_den1] at this
  revert this; decide

-- `Std.Sat.AIG.LawfulOperator.denote_input_entry`: removable (dependent), lt_size of the lawful operator.
theorem LO_denote_input_entry_9 : indep% Std.Sat.AIG.LawfulOperator.denote_input_entry 9 := by
  intro α _ _ β f inst assign entry input
  exact LawfulOperator.lt_size entry input

-- `Std.Sat.AIG.LawfulOperator.denote_cast_entry`: opT turns node 1 of #[false, false] into true.
theorem LO_denote_cast_entry_5 : ¬ drop0% Std.Sat.AIG.LawfulOperator.denote_cast_entry 5 := fun H => by
  have := H (β := fun _ => Unit) (f := opT) (assign := fun _ => false) (entry := ⟨A2, rf A2 1⟩) (input := ())
    (h := by decide)
  simp only [opT, rf, Ref.cast] at this
  rw [AT_den1, A2_den1] at this
  revert this; decide

-- `Std.Sat.AIG.LawfulOperator.denote_cast_entry`: removable (dependent), le_size of the lawful operator.
theorem LO_denote_cast_entry_9 : indep% Std.Sat.AIG.LawfulOperator.denote_cast_entry 9 := by
  intro α _ _ β f inst assign entry input
  exact LawfulOperator.le_size entry.aig input

-- `Std.Sat.AIG.LawfulOperator.denote_mem_prefix`: the shrinking opC is not lawful.
theorem LO_denote_mem_prefix_5 : ¬ indep0% Std.Sat.AIG.LawfulOperator.denote_mem_prefix 5 := fun H =>
  opC_not_lawful (β := fun _ => Unit) () (H (f := opC) (assign := fun _ => false) (start := 0) (invert := false)
    (aig := E0) (input := ()) (h := by decide))

-- `Std.Sat.AIG.LawfulOperator.denote_mem_prefix`: start = 5 in the empty AIG.
theorem LO_denote_mem_prefix_11 : ¬ indep0% Std.Sat.AIG.LawfulOperator.denote_mem_prefix 11 := fun H =>
  absurd (H (β := fun _ => Unit) (f := opId) (assign := fun _ => false) (start := 5) (invert := false)
    (aig := E0) (input := ())) (by decide)

/-! ### LawfulVecOperator -/

-- `Std.Sat.AIG.LawfulVecOperator.le_size`: vopC maps #[false, false] to the empty AIG.
theorem LVO_le_size_5 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.le_size 5 :=
  fun H => absurd (H (β := fun _ _ => Unit) (f := @vopC (fun _ _ => Unit)) (len := 0) A2 ()) (by show ¬ 2 ≤ 1; omega)

-- `Std.Sat.AIG.LawfulVecOperator.decl_eq`: vopT replaces node 1 of #[false, false] by a gate.
theorem LVO_decl_eq_5 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.decl_eq 5 :=
  fun H => absurd (H (β := fun _ _ => Unit) (f := @vopT (fun _ _ => Unit)) (len := 0) A2 () 1 (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.LawfulVecOperator.decl_eq`: the lawful vopPush grows the empty AIG; idx = 1.
theorem LVO_decl_eq_10 : ¬ indep0% Std.Sat.AIG.LawfulVecOperator.decl_eq 10 :=
  fun H => absurd (H (β := fun _ _ => Unit) (f := @vopPush (fun _ _ => Unit)) (len := 0) (aig := E0) (input := ()) (idx := 1)
    (h2 := by decide)) (by decide)

-- `Std.Sat.AIG.LawfulVecOperator.decl_eq`: removable (dependent), le_size of the instance itself.
theorem LVO_decl_eq_11 : indep% Std.Sat.AIG.LawfulVecOperator.decl_eq 11 := by
  intro α _ _ β f self len aig input idx h1
  exact Nat.lt_of_lt_of_le h1 (self.le_size aig input)

-- `Std.Sat.AIG.LawfulVecOperator.isPrefix_aig`: vopC on #[false, false].
theorem LVO_isPrefix_aig_5 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.isPrefix_aig 5 :=
  fun H => absurd (H (β := fun _ _ => Unit) (f := @vopC (fun _ _ => Unit)) (len := 0) A2 ()).size_le (by show ¬ 2 ≤ 1; omega)

-- `Std.Sat.AIG.LawfulVecOperator.lt_size`: vopC on node 1 of #[false, false].
theorem LVO_lt_size_5 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.lt_size 5 :=
  fun H => absurd (H (β := fun _ _ => Unit) (f := @vopC (fun _ _ => Unit)) (len := 0) ⟨A2, rf A2 1⟩ ()) (by show ¬ 1 < 1; omega)

-- `Std.Sat.AIG.LawfulVecOperator.lt_size_of_lt_aig_size`: vopC on #[false, false], x = 1.
theorem LVO_lt_size_of_lt_aig_size_5 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.lt_size_of_lt_aig_size 5 :=
  fun H => absurd (H (β := fun _ _ => Unit) (f := @vopC (fun _ _ => Unit)) (len := 0) (x := 1) A2 () (by decide))
    (by show ¬ 1 < 1; omega)

-- `Std.Sat.AIG.LawfulVecOperator.lt_size_of_lt_aig_size`: the identity operator on the empty AIG, x = 1.
theorem LVO_lt_size_of_lt_aig_size_10 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.lt_size_of_lt_aig_size 10 :=
  fun H => absurd (H (β := fun _ _ => Unit) (f := @vopId (fun _ _ => Unit)) (len := 0) (x := 1) E0 ()) (by decide)

-- `Std.Sat.AIG.LawfulVecOperator.le_size_of_le_aig_size`: vopC on #[false, false], x = 2.
theorem LVO_le_size_of_le_aig_size_5 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.le_size_of_le_aig_size 5 :=
  fun H => absurd (H (β := fun _ _ => Unit) (f := @vopC (fun _ _ => Unit)) (len := 0) (x := 2) A2 () (by decide))
    (by show ¬ 2 ≤ 1; omega)

-- `Std.Sat.AIG.LawfulVecOperator.le_size_of_le_aig_size`: the identity operator on the empty AIG, x = 2.
theorem LVO_le_size_of_le_aig_size_10 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.le_size_of_le_aig_size 10 :=
  fun H => absurd (H (β := fun _ _ => Unit) (f := @vopId (fun _ _ => Unit)) (len := 0) (x := 2) E0 ()) (by decide)

-- `Std.Sat.AIG.LawfulVecOperator.denote_input_entry`: vopT turns node 1 of #[false, false] into true.
theorem LVO_denote_input_entry_5 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.denote_input_entry 5 := fun H => by
  have := H (β := fun _ _ => Unit) (f := @vopT (fun _ _ => Unit)) (len := 0) (assign := fun _ => false) (entry := ⟨A2, rf A2 1⟩)
    (input := ()) (h := by decide)
  simp only [vopT, rf] at this
  rw [AT_den1, A2_den1] at this
  revert this; decide

-- `Std.Sat.AIG.LawfulVecOperator.denote_input_entry`: removable (dependent), lt_size of the lawful operator.
theorem LVO_denote_input_entry_10 : indep% Std.Sat.AIG.LawfulVecOperator.denote_input_entry 10 := by
  intro α _ _ β f inst len assign entry input
  exact LawfulVecOperator.lt_size entry input

-- `Std.Sat.AIG.LawfulVecOperator.denote_cast_entry`: vopT turns node 1 of #[false, false] into true.
theorem LVO_denote_cast_entry_5 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.denote_cast_entry 5 := fun H => by
  have := H (β := fun _ _ => Unit) (f := @vopT (fun _ _ => Unit)) (len := 0) (assign := fun _ => false) (entry := ⟨A2, rf A2 1⟩)
    (input := ()) (h := by decide)
  simp only [vopT, rf, Ref.cast] at this
  rw [AT_den1, A2_den1] at this
  revert this; decide

-- `Std.Sat.AIG.LawfulVecOperator.denote_cast_entry`: removable (dependent), le_size of the lawful operator.
theorem LVO_denote_cast_entry_10 : indep% Std.Sat.AIG.LawfulVecOperator.denote_cast_entry 10 := by
  intro α _ _ β f inst len assign entry input
  exact LawfulVecOperator.le_size entry.aig input

-- `Std.Sat.AIG.LawfulVecOperator.denote_mem_prefix`: the shrinking vopC is not lawful.
theorem LVO_denote_mem_prefix_5 : ¬ indep0% Std.Sat.AIG.LawfulVecOperator.denote_mem_prefix 5 := fun H =>
  vopC_not_lawful (β := fun _ _ => Unit) () (H (f := @vopC (fun _ _ => Unit)) (len := 0) (assign := fun _ => false) (start := 0)
    (inv := false) (aig := E0) (input := ()) (h := by decide))

-- `Std.Sat.AIG.LawfulVecOperator.denote_mem_prefix`: start = 5 in the empty AIG.
theorem LVO_denote_mem_prefix_12 : ¬ indep0% Std.Sat.AIG.LawfulVecOperator.denote_mem_prefix 12 := fun H =>
  absurd (H (β := fun _ _ => Unit) (f := @vopId (fun _ _ => Unit)) (len := 0) (assign := fun _ => false) (start := 5) (inv := false)
    (aig := E0) (input := ())) (by decide)

-- `Std.Sat.AIG.LawfulVecOperator.denote_input_vec`: vopT turns node 1 of #[false, false] into true.
theorem LVO_denote_input_vec_5 : ¬ drop0% Std.Sat.AIG.LawfulVecOperator.denote_input_vec 5 := fun H => by
  have := H (β := fun _ _ => Unit) (f := @vopT (fun _ _ => Unit)) (len := 1) (assign := fun _ => false) (idx := 0) (hidx := by decide)
    (s := ⟨A2, vec1 A2 (rf A2 1)⟩) (input := ()) (hcast := by decide)
  simp only [vopT, vec1_get, rf, Ref.cast] at this
  rw [AT_den1, A2_den1] at this
  revert this; decide

-- `Std.Sat.AIG.LawfulVecOperator.denote_input_vec`: len = 0, idx = 0.
theorem LVO_denote_input_vec_9 : ¬ indep0% Std.Sat.AIG.LawfulVecOperator.denote_input_vec 9 := fun H =>
  absurd (H (β := fun _ _ => Unit) (f := @vopId (fun _ _ => Unit)) (len := 0) (assign := fun _ => false) (idx := 0)
    (s := ⟨E0, RefVec.empty⟩) (input := ()) (hcast := Nat.le_refl _)) (by decide)

-- `Std.Sat.AIG.LawfulVecOperator.denote_input_vec`: removable (dependent), le_size of the lawful operator.
theorem LVO_denote_input_vec_12 : indep% Std.Sat.AIG.LawfulVecOperator.denote_input_vec 12 := by
  intro α _ _ β f inst len assign idx hidx s input
  exact LawfulVecOperator.le_size s.aig input

/-! ### Lemmas, RefVec -/

-- `Std.Sat.AIG.Ref.gate_cast`: #[false, false] is larger than the empty AIG.
theorem Ref_gate_cast_6 : ¬ indep0% Std.Sat.AIG.Ref.gate_cast 6 :=
  fun H => absurd (H (aig1 := A2) (aig2 := E0) (ref := ref0 _)) (by decide)

-- `Std.Sat.AIG.Ref.cast_eq`: #[false, false] is larger than the empty AIG.
theorem Ref_cast_eq_6 : ¬ indep0% Std.Sat.AIG.Ref.cast_eq 6 :=
  fun H => absurd (H (aig1 := A2) (aig2 := E0) (ref := ref0 _)) (by decide)

-- `Std.Sat.AIG.BinaryInput.lhs_cast`: #[false, false] is larger than the empty AIG.
theorem BinaryInput_lhs_cast_6 : ¬ indep0% Std.Sat.AIG.BinaryInput.lhs_cast 6 :=
  fun H => absurd (H (aig1 := A2) (aig2 := E0) (input := ⟨ref0 _, ref0 _⟩)) (by decide)

-- `Std.Sat.AIG.BinaryInput.rhs_cast`: #[false, false] is larger than the empty AIG.
theorem BinaryInput_rhs_cast_6 : ¬ indep0% Std.Sat.AIG.BinaryInput.rhs_cast 6 :=
  fun H => absurd (H (aig1 := A2) (aig2 := E0) (input := ⟨ref0 _, ref0 _⟩)) (by decide)

-- `Std.Sat.AIG.denote_idx_false`: node 1 of AT is a gate denoting true.
theorem denote_idx_false_8 : ¬ drop0% Std.Sat.AIG.denote_idx_false 8 := fun H => by
  have := H (start := 1) (assign := fun _ => false) (invert := false) (aig := AT) (hstart := by decide)
  rw [AT_den1] at this; revert this; decide

-- `Std.Sat.AIG.denote_idx_atom`: node 0 of the empty AIG under the all-true assignment.
theorem denote_idx_atom_9 : ¬ drop0% Std.Sat.AIG.denote_idx_atom 9 := fun H => by
  have := H (start := 0) (assign := fun _ => true) (invert := false) (a := 0) (aig := E0) (hstart := by decide)
  rw [den0] at this; revert this; decide

-- `Std.Sat.AIG.idx_trichotomy`: prop = False at node 0 (false) of the empty AIG.
theorem idx_trichotomy_7 : ¬ drop0% Std.Sat.AIG.idx_trichotomy 7 := fun H =>
  H (start := 0) (aig := E0) (hstart := by decide) (prop := False) (fun a h => by cases h) (fun l r h => by cases h)

-- `Std.Sat.AIG.idx_trichotomy`: prop = False at node 1 (an atom) of AA.
theorem idx_trichotomy_8 : ¬ drop0% Std.Sat.AIG.idx_trichotomy 8 := fun H =>
  H (start := 1) (aig := AA) (hstart := by decide) (prop := False) (fun h => by cases h) (fun l r h => by cases h)

-- `Std.Sat.AIG.idx_trichotomy`: prop = False at node 1 (a gate) of AT.
theorem idx_trichotomy_9 : ¬ drop0% Std.Sat.AIG.idx_trichotomy 9 := fun H =>
  H (start := 1) (aig := AT) (hstart := by decide) (prop := False) (fun h => by cases h) (fun a h => by cases h)

-- `Std.Sat.AIG.denote_idx_trichotomy`: node 0 of the empty AIG denotes false, claimed res = true.
theorem denote_idx_trichotomy_9 : ¬ drop0% Std.Sat.AIG.denote_idx_trichotomy 9 := fun H => by
  have := H (start := 0) (assign := fun _ => false) (invert := false) (res := true) (aig := E0)
    (hstart := by decide) (fun a h => by cases h) (fun l r h => by cases h)
  rw [den0] at this; revert this; decide

-- `Std.Sat.AIG.denote_idx_trichotomy`: node 1 (atom 0) of AA denotes true, claimed res = false.
theorem denote_idx_trichotomy_10 : ¬ drop0% Std.Sat.AIG.denote_idx_trichotomy 10 := fun H => by
  have := H (start := 1) (assign := fun _ => true) (invert := false) (res := false) (aig := AA)
    (hstart := by decide) (fun h => by cases h) (fun l r h => by cases h)
  rw [AA_den1] at this; revert this; decide

-- `Std.Sat.AIG.denote_idx_trichotomy`: node 1 (a gate) of AT denotes true, claimed res = false.
theorem denote_idx_trichotomy_11 : ¬ drop0% Std.Sat.AIG.denote_idx_trichotomy 11 := fun H => by
  have := H (start := 1) (assign := fun _ => false) (invert := false) (res := false) (aig := AT)
    (hstart := by decide) (fun h => by cases h) (fun a h => by cases h)
  rw [AT_den1] at this; revert this; decide

-- `Std.Sat.AIG.denote_congr`: node 1 (atom 0) of AA under the all-true and all-false assignments.
theorem denote_congr_9 : ¬ drop0% Std.Sat.AIG.denote_congr 9 := fun H => by
  have := H (fun _ => true) (fun _ => false) AA 1 false (by decide)
  rw [AA_den1, AA_den1] at this; revert this; decide

-- `Std.Sat.AIG.of_isConstant`: node 0 of the empty AIG denotes false, b = true.
theorem of_isConstant_7 : ¬ drop0% Std.Sat.AIG.of_isConstant 7 := fun H => by
  have := H (aig := E0) (assign := fun _ => false) (ref := ref0 _) (b := true)
  simp only [ref0] at this; rw [den0] at this; revert this; decide

-- `Std.Sat.AIG.denote_getConstant`: node 0 of the empty AIG denotes false, b = true.
theorem denote_getConstant_7 : ¬ drop0% Std.Sat.AIG.denote_getConstant 7 := fun H => by
  have := H (aig := E0) (assign := fun _ => false) (ref := ref0 _) (b := true)
  simp only [ref0] at this; rw [den0] at this; revert this; decide

-- `Std.Sat.AIG.RefVec.cast_cast`: aig1 = #[false, false], aig2 = empty, aig3 = #[false, false].
theorem RefVec_cast_cast_8 : ¬ indep0% Std.Sat.AIG.RefVec.cast_cast 8 :=
  fun H => absurd (H (len := 0) (aig1 := A2) (aig2 := E0) (aig3 := A2) (s := .empty) (h2 := by decide))
    (by decide)

-- `Std.Sat.AIG.RefVec.cast_cast`: aig1 = empty, aig2 = #[false, false], aig3 = empty.
theorem RefVec_cast_cast_9 : ¬ indep0% Std.Sat.AIG.RefVec.cast_cast 9 :=
  fun H => absurd (H (len := 0) (aig1 := E0) (aig2 := A2) (aig3 := E0) (s := .empty) (h1 := by decide))
    (by decide)

-- `Std.Sat.AIG.RefVec.get_cast`: #[false, false] is larger than the empty AIG.
theorem RefVec_get_cast_9 : ¬ indep0% Std.Sat.AIG.RefVec.get_cast 9 :=
  fun H => absurd (H (len := 1) (aig1 := A2) (aig2 := E0) (s := vec0 _ 1) (idx := 0) (hidx := by decide))
    (by decide)

-- `Std.Sat.AIG.RefVec.get_out_bound`: entry 0 of [node 0] is not the inverted alternative.
theorem RefVec_get_out_bound_8 : ¬ drop0% Std.Sat.AIG.RefVec.get_out_bound 8 := fun H => by
  have := H (aig := E0) (len := 1) (s := vec1 _ (ref0 _)) (idx := 0) (alt := ref1 _)
  rw [RefVec.get_in_bound _ _ _ (by decide), vec1_get] at this
  have := congrArg Ref.invert this
  revert this; decide

-- `Std.Sat.AIG.BinaryRefVec.lhs_get_cast`: len = 0, idx = 0.
theorem lhs_get_cast_8 : ¬ indep0% Std.Sat.AIG.BinaryRefVec.lhs_get_cast 8 :=
  fun H => absurd (H (len := 0) (aig1 := E0) (aig2 := E0) (s := ⟨RefVec.empty, RefVec.empty⟩) (idx := 0)
    (hcast := Nat.le_refl _)) (by decide)

-- `Std.Sat.AIG.BinaryRefVec.lhs_get_cast`: #[false, false] is larger than the empty AIG.
theorem lhs_get_cast_9 : ¬ indep0% Std.Sat.AIG.BinaryRefVec.lhs_get_cast 9 :=
  fun H => absurd (H (len := 1) (aig1 := A2) (aig2 := E0) (s := ⟨vec0 _ 1, vec0 _ 1⟩) (idx := 0)
    (hidx := by decide)) (by decide)

-- `Std.Sat.AIG.BinaryRefVec.rhs_get_cast`: len = 0, idx = 0.
theorem rhs_get_cast_8 : ¬ indep0% Std.Sat.AIG.BinaryRefVec.rhs_get_cast 8 :=
  fun H => absurd (H (len := 0) (aig1 := E0) (aig2 := E0) (s := ⟨RefVec.empty, RefVec.empty⟩) (idx := 0)
    (hcast := Nat.le_refl _)) (by decide)

-- `Std.Sat.AIG.BinaryRefVec.rhs_get_cast`: #[false, false] is larger than the empty AIG.
theorem rhs_get_cast_9 : ¬ indep0% Std.Sat.AIG.BinaryRefVec.rhs_get_cast 9 :=
  fun H => absurd (H (len := 1) (aig1 := A2) (aig2 := E0) (s := ⟨vec0 _ 1, vec0 _ 1⟩) (idx := 0)
    (hidx := by decide)) (by decide)

end SatAIGHand

/-! ## Std.Sat.AIG.If, RefVecOperator.{Fold, Map, Zip} -/

namespace SatAIGHand
open Std Std.Sat Std.Sat.AIG RefuteIndep

/- Unlawful and lawful-but-not-chainable operators on Ref / BinaryInput. -/
theorem nlR : ¬ LawfulOperator Nat AIG.Ref (opC (β := AIG.Ref)) := opC_not_lawful (ref0 A2)
theorem nlB : ¬ LawfulOperator Nat AIG.BinaryInput (opC (β := AIG.BinaryInput)) := opC_not_lawful ⟨ref0 A2, ref0 A2⟩

/- Growth of the vector operators on concrete inputs. -/
theorem AG_if : 3 < (AG.mkIfCached ⟨rf AG 1, rf AG 2, rf AG 2⟩).aig.decls.size := by
  unfold mkIfCached; dsimp only
  refine Nat.lt_of_lt_of_le ?_ (mkOrCached_le_size _ _)
  refine Nat.lt_of_lt_of_le ?_ (mkAndCached_le_size _ _)
  refine Nat.lt_of_lt_of_le ?_ (mkNotCached_le_size _ _)
  exact AG_gate _ _ rfl rfl

theorem ite_grow (s : AG.RefVec 0) :
    3 < (RefVec.ite.go AG 0 (by decide) (rf AG 1) (vec1 AG (rf AG 2)) (vec1 AG (rf AG 2)) s).aig.decls.size := by
  rw [RefVec.ite.go, dif_pos (by decide)]; dsimp only
  refine Nat.lt_of_lt_of_le ?_ (RefVec.ite.go_le_size _ _ _ _ _ _ _)
  exact AG_if

theorem map_grow (s : E0.RefVec 0) (input : E0.RefVec 1) :
    1 < (RefVec.map.go E0 0 (by decide) s input opPush).aig.decls.size := by
  rw [RefVec.map.go, dif_pos (by decide)]; dsimp only
  refine Nat.lt_of_lt_of_le ?_ (RefVec.map.go_le_size _ _ _ _ _)
  show 1 < (pushF E0).decls.size; decide

theorem zip_grow (s : E0.RefVec 0) (lhs rhs : E0.RefVec 1) :
    1 < (RefVec.zip.go E0 0 s (by decide) lhs rhs opPush).aig.decls.size := by
  rw [RefVec.zip.go, dif_pos (by decide)]; dsimp only
  refine Nat.lt_of_lt_of_le ?_ (RefVec.zip.go_le_size _ _ _ _ _ _)
  show 1 < (pushF E0).decls.size; decide

theorem fold_grow (acc : E0.Ref) (input : E0.RefVec 1) :
    1 < (RefVec.fold.go E0 acc 0 1 input opPush).aig.decls.size := by
  rw [RefVec.fold.go, dif_pos (by decide)]; dsimp only
  refine Nat.lt_of_lt_of_le ?_ (RefVec.fold.go_le_size _ _ _ _)
  show 1 < (pushF E0).decls.size; decide

theorem zip0 : (RefVec.zip E0 ⟨RefVec.empty, RefVec.empty⟩ opPush).aig.decls.size = 1 := by
  unfold RefVec.zip; rw [RefVec.zip.go, dif_neg (by decide)]; rfl

theorem fold0 : (RefVec.fold E0 RefVec.empty opPush).aig.decls.size = 1 := by
  unfold RefVec.fold; rw [RefVec.fold.go, dif_neg (by decide)]; rfl

def v0 : E0.RefVec 1 := vec1 E0 (ref0 _)

/-! ### If -/

-- `Std.Sat.AIG.RefVec.ite.go_decl_eq`: go on AG (discriminant node 1, branches node 2) grows; idx = 3.
theorem ite_go_decl_eq_12 : ¬ indep0% Std.Sat.AIG.RefVec.ite.go_decl_eq 12 :=
  fun H => absurd (H (w := 1) (aig := AG) (curr := 0) (hcurr := by decide) (discr := rf AG 1)
    (lhs := vec1 AG (rf AG 2)) (rhs := vec1 AG (rf AG 2)) (s := RefVec.empty) (idx := 3) (h2 := ite_grow _))
    (by decide)

-- `Std.Sat.AIG.RefVec.ite.go_decl_eq`: removable (dependent), ite.go never shrinks the AIG (go_le_size).
theorem ite_go_decl_eq_13 : indep% Std.Sat.AIG.RefVec.ite.go_decl_eq 13 := by
  intro α _ _ w aig curr hcurr discr lhs rhs s idx h1
  exact Nat.lt_of_lt_of_le h1 (RefVec.ite.go_le_size aig curr hcurr discr lhs rhs s)

-- `Std.Sat.AIG.RefVec.ite.go_get_aux`: curr = 0, idx = 0.
theorem ite_go_get_aux_12 : ¬ indep0% Std.Sat.AIG.RefVec.ite.go_get_aux 12 :=
  fun H => absurd (H (w := 0) (aig := E0) (curr := 0) (hcurr := by decide) (discr := ref0 _) (lhs := RefVec.empty)
    (rhs := RefVec.empty) (s := RefVec.empty) (idx := 0) (hfoo := RefVec.ite.go_le_size _ _ _ _ _ _ _)) (by decide)

-- `Std.Sat.AIG.RefVec.ite.go_get_aux`: removable (dependent), ite.go_le_size.
theorem ite_go_get_aux_13 : indep% Std.Sat.AIG.RefVec.ite.go_get_aux 13 := by
  intro α _ _ w aig curr hcurr discr lhs rhs s idx hidx
  exact RefVec.ite.go_le_size aig curr hcurr discr lhs rhs s

-- `Std.Sat.AIG.RefVec.ite.denote_go`: curr = w = 1 with the already computed entry true, while the
-- discriminant is false and the else branch is false; idx = 0.
theorem ite_denote_go_14 : ¬ drop0% Std.Sat.AIG.RefVec.ite.denote_go 14 := fun H => by
  have := H (assign := fun _ => false) (w := 1) (aig := E0) (curr := 1) (hcurr := by decide) (discr := ref0 _)
    (lhs := v0) (rhs := v0) (s := vec1 E0 (ref1 _)) (idx := 0) (hidx1 := by decide)
  rw [RefVec.ite.go_get _ _ _ _ _ _ _ 0 (by decide)] at this
  simp only [vec1_get, v0, ref0, ref1, Ref.cast] at this
  simp only [den0] at this
  revert this; decide

-- `Std.Sat.AIG.RefVec.denote_ite`: w = 0, idx = 0.
theorem denote_ite_8 : ¬ indep0% Std.Sat.AIG.RefVec.denote_ite 8 :=
  fun H => absurd (H (w := 0) (assign := fun _ => false) (aig := E0) (input := ⟨ref0 _, RefVec.empty, RefVec.empty⟩)
    (idx := 0)) (by decide)

/-! ### Fold -/

-- `Std.Sat.AIG.RefVec.fold.go_le_size`: the shrinking opC is not lawful.
theorem fold_go_le_size_9 : ¬ indep0% Std.Sat.AIG.RefVec.fold.go_le_size 9 :=
  fun H => nlB (H (len := 0) (aig := E0) (acc := ref0 _) (idx := 0) (s := RefVec.empty) (f := opC))

-- `Std.Sat.AIG.RefVec.fold_le_size`: the shrinking opC is not lawful.
theorem fold_le_size_7 : ¬ indep0% Std.Sat.AIG.RefVec.fold_le_size 7 :=
  fun H => nlB (H (len := 0) (aig := E0) (vec := RefVec.empty) (func := opC))

-- `Std.Sat.AIG.RefVec.fold.go_decl_eq`: the shrinking opC is not lawful.
theorem fold_go_decl_eq_9 : ¬ indep0% Std.Sat.AIG.RefVec.fold.go_decl_eq 9 :=
  fun H => nlB (H (len := 0) (aig := E0) (acc := ref0 _) (i := 0) (s := RefVec.empty) (f := opC) (idx := 0) (by decide))

-- `Std.Sat.AIG.RefVec.fold.go_decl_eq`: folding opPush over one entry grows the empty AIG; idx = 1.
theorem fold_go_decl_eq_11 : ¬ indep0% Std.Sat.AIG.RefVec.fold.go_decl_eq 11 :=
  fun H => absurd (H (len := 1) (aig := E0) (acc := ref0 _) (i := 0) (s := v0) (f := opPush) (idx := 1)
    (h2 := fold_grow _ _)) (by decide)

-- `Std.Sat.AIG.RefVec.fold.go_decl_eq`: removable (dependent), fold.go_le_size.
theorem fold_go_decl_eq_12 : indep% Std.Sat.AIG.RefVec.fold.go_decl_eq 12 := by
  intro α _ _ len aig acc i s f inst idx h1
  exact Nat.lt_of_lt_of_le h1 (RefVec.fold.go_le_size acc i s f)

-- `Std.Sat.AIG.RefVec.fold_decl_eq`: the shrinking opC is not lawful.
theorem fold_decl_eq_7 : ¬ indep0% Std.Sat.AIG.RefVec.fold_decl_eq 7 :=
  fun H => nlB (H (len := 0) (aig := E0) (vec := RefVec.empty) (func := opC) (idx := 0) (by decide))

-- `Std.Sat.AIG.RefVec.fold_decl_eq`: folding opPush over one entry grows the empty AIG; idx = 1.
theorem fold_decl_eq_9 : ¬ indep0% Std.Sat.AIG.RefVec.fold_decl_eq 9 :=
  fun H => absurd (H (len := 1) (aig := E0) (vec := v0) (func := opPush) (idx := 1)
    (h2 := by unfold RefVec.fold; exact fold_grow _ _)) (by decide)

-- `Std.Sat.AIG.RefVec.fold_decl_eq`: removable (dependent), fold_le_size.
theorem fold_decl_eq_10 : indep% Std.Sat.AIG.RefVec.fold_decl_eq 10 := by
  intro α _ _ len aig vec func inst idx h1
  exact Nat.lt_of_lt_of_le h1 (RefVec.fold_le_size vec func)

-- `Std.Sat.AIG.RefVec.fold_lt_size_of_lt_aig_size`: the shrinking opC is not lawful.
theorem fold_lt_size_of_lt_aig_size_8 : ¬ indep0% Std.Sat.AIG.RefVec.fold_lt_size_of_lt_aig_size 8 :=
  fun H => nlB (H (len := 0) (x := 0) (aig := E0) (vec := RefVec.empty) (func := opC) (by decide))

-- `Std.Sat.AIG.RefVec.fold_lt_size_of_lt_aig_size`: folding over the empty vector keeps the empty AIG; x = 1.
theorem fold_lt_size_of_lt_aig_size_9 : ¬ drop0% Std.Sat.AIG.RefVec.fold_lt_size_of_lt_aig_size 9 :=
  fun H => absurd (H (len := 0) (x := 1) (aig := E0) (vec := RefVec.empty) (func := opPush)) (by rw [fold0]; decide)

-- `Std.Sat.AIG.RefVec.fold_le_size_of_le_aig_size`: the shrinking opC is not lawful.
theorem fold_le_size_of_le_aig_size_8 : ¬ indep0% Std.Sat.AIG.RefVec.fold_le_size_of_le_aig_size 8 :=
  fun H => nlB (H (len := 0) (x := 0) (aig := E0) (vec := RefVec.empty) (func := opC) (by decide))

-- `Std.Sat.AIG.RefVec.fold_le_size_of_le_aig_size`: folding over the empty vector keeps the empty AIG; x = 2.
theorem fold_le_size_of_le_aig_size_9 : ¬ drop0% Std.Sat.AIG.RefVec.fold_le_size_of_le_aig_size 9 :=
  fun H => absurd (H (len := 0) (x := 2) (aig := E0) (vec := RefVec.empty) (func := opPush)) (by rw [fold0]; decide)

end SatAIGHand

namespace SatAIGHand
open Std Std.Sat Std.Sat.AIG RefuteIndep

/- opPar is not chainable: one step from the empty AIG changes its output. -/
theorem opPar_bad {β : AIG Nat → Type} (i1 i2 : β E0) (i2' : β (opPar E0 i1).aig) (a : Nat → Bool)
    (H : ⟦opPar (opPar E0 i1).aig i2', a⟧ = ⟦opPar E0 i2, a⟧) : False := by
  simp only [opPar] at H; rw [den0, den0] at H
  have e1 : (pushF E0).decls.size = 2 := rfl
  have e2 : E0.decls.size = 1 := rfl
  simp [e1, e2] at H

def b0 : E0.BinaryInput := ⟨ref0 _, ref0 _⟩
def bv0 : E0.BinaryRefVec 0 := ⟨RefVec.empty, RefVec.empty⟩

/-! ### Map -/

-- `Std.Sat.AIG.RefVec.LawfulMapOperator.chainable`: the shrinking opC is not lawful.
theorem LMO_chainable_4 : ¬ indep0% Std.Sat.AIG.RefVec.LawfulMapOperator.chainable 4 :=
  fun H => nlR (H (f := opC) (aig := E0) (input1 := ref0 _) (input2 := ref0 _) (h := by decide) (assign := fun _ => false))

-- `Std.Sat.AIG.RefVec.LawfulMapOperator.chainable`: the lawful opPar (output depends on the AIG size) is not chainable.
theorem LMO_chainable_5 : ¬ drop0% Std.Sat.AIG.RefVec.LawfulMapOperator.chainable 5 :=
  fun H => opPar_bad _ _ _ _ (@H Nat _ _ opPar inferInstance E0 (ref0 _) (ref0 _)
    (by simp [opPar, pushF_size]) (fun _ => false))

-- `Std.Sat.AIG.RefVec.LawfulMapOperator.chainable`: removable (dependent), le_size of the lawful operator.
theorem LMO_chainable_9 : indep% Std.Sat.AIG.RefVec.LawfulMapOperator.chainable 9 := by
  intro α _ _ f inst self aig input1 input2 assign
  exact LawfulOperator.le_size aig input1

-- `Std.Sat.AIG.RefVec.LawfulMapOperator.denote_prefix_cast_ref`: the shrinking opC is not lawful.
theorem LMO_denote_prefix_cast_ref_8 : ¬ indep0% Std.Sat.AIG.RefVec.LawfulMapOperator.denote_prefix_cast_ref 8 :=
  fun H => nlR (H (assign := fun _ => false) (aig := E0) (input1 := ref0 _) (input2 := ref0 _) (f := opC) (h := by decide))

-- `Std.Sat.AIG.RefVec.LawfulMapOperator.denote_prefix_cast_ref`: the lawful, non-chainable opPar.
theorem LMO_denote_prefix_cast_ref_9 : ¬ drop0% Std.Sat.AIG.RefVec.LawfulMapOperator.denote_prefix_cast_ref 9 :=
  fun H => opPar_bad _ _ _ _ (H (assign := fun _ => false) (aig := E0) (input1 := ref0 _) (input2 := ref0 _)
    (f := opPar) (h := by simp [opPar, pushF_size]))

-- `Std.Sat.AIG.RefVec.LawfulMapOperator.denote_prefix_cast_ref`: removable (dependent), le_size of the lawful operator.
theorem LMO_denote_prefix_cast_ref_10 : indep% Std.Sat.AIG.RefVec.LawfulMapOperator.denote_prefix_cast_ref 10 := by
  intro α _ _ assign aig input1 input2 f i1 i2
  exact LawfulOperator.le_size aig input1

-- `Std.Sat.AIG.RefVec.map.go_le_size`: the shrinking opC is not lawful.
theorem map_go_le_size_10 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_le_size 10 :=
  fun H => nlR (H (len := 0) (aig := E0) (idx := 0) (hidx := by decide) (s := RefVec.empty) (input := RefVec.empty) (f := opC))

-- `Std.Sat.AIG.RefVec.map.go_le_size`: the lawful, non-chainable opPar.
theorem map_go_le_size_11 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_le_size 11 :=
  fun H => opPar_not_map (H (len := 0) (aig := E0) (idx := 0) (hidx := by decide) (s := RefVec.empty) (input := RefVec.empty) (f := opPar))

-- `Std.Sat.AIG.RefVec.map.go_decl_eq`: the shrinking opC is not lawful.
theorem map_go_decl_eq_10 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_decl_eq 10 :=
  fun H => nlR (H (len := 0) (aig := E0) (i := 0) (hi := by decide) (s := RefVec.empty) (input := RefVec.empty) (f := opC)
    (idx := 0) (h1 := by decide))

-- `Std.Sat.AIG.RefVec.map.go_decl_eq`: the lawful, non-chainable opPar.
theorem map_go_decl_eq_11 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_decl_eq 11 :=
  fun H => opPar_not_map (H (len := 0) (aig := E0) (i := 0) (hi := by decide) (s := RefVec.empty) (input := RefVec.empty)
    (f := opPar) (idx := 0) (h1 := by decide))

-- `Std.Sat.AIG.RefVec.map.go_decl_eq`: mapping opPush over one entry grows the empty AIG; idx = 1.
theorem map_go_decl_eq_13 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_decl_eq 13 :=
  fun H => absurd (H (len := 1) (aig := E0) (i := 0) (hi := by decide) (s := RefVec.empty) (input := v0) (f := opPush)
    (idx := 1) (h2 := map_grow _ _)) (by decide)

-- `Std.Sat.AIG.RefVec.map.go_decl_eq`: removable (dependent), map.go_le_size.
theorem map_go_decl_eq_14 : indep% Std.Sat.AIG.RefVec.map.go_decl_eq 14 := by
  intro α _ _ len aig i hi s input f i1 i2 idx h1
  exact Nat.lt_of_lt_of_le h1 (RefVec.map.go_le_size i hi s input f)

-- `Std.Sat.AIG.RefVec.map_decl_eq`: mapping opPush over one entry grows the empty AIG; idx = 1.
theorem map_decl_eq_7 : ¬ indep0% Std.Sat.AIG.RefVec.map_decl_eq 7 :=
  fun H => absurd (H (len := 1) (aig := E0) (target := ⟨v0, opPush⟩) (idx := 1)
    (h2 := by unfold RefVec.map; exact map_grow _ _)) (by decide)

-- `Std.Sat.AIG.RefVec.map_decl_eq`: removable (dependent), map_le_size.
theorem map_decl_eq_8 : indep% Std.Sat.AIG.RefVec.map_decl_eq 8 := by
  intro α _ _ len aig target idx h1
  exact Nat.lt_of_lt_of_le h1 (RefVec.map_le_size target)

-- `Std.Sat.AIG.RefVec.map.go_get_aux`: the shrinking opC is not lawful.
theorem map_go_get_aux_10 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_get_aux 10 :=
  fun H => nlR (H (len := 1) (aig := E0) (curr := 1) (hcurr := by decide) (s := v0) (input := v0) (f := opC)
    (idx := 0) (hidx := by decide))

-- `Std.Sat.AIG.RefVec.map.go_get_aux`: the lawful, non-chainable opPar.
theorem map_go_get_aux_11 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_get_aux 11 :=
  fun H => opPar_not_map (H (len := 1) (aig := E0) (curr := 1) (hcurr := by decide) (s := v0) (input := v0) (f := opPar)
    (idx := 0) (hidx := by decide))

-- `Std.Sat.AIG.RefVec.map.go_get_aux`: curr = 0, idx = 0.
theorem map_go_get_aux_13 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_get_aux 13 :=
  fun H => absurd (H (len := 0) (aig := E0) (curr := 0) (hcurr := by decide) (s := RefVec.empty) (input := RefVec.empty)
    (f := opPush) (idx := 0) (hfoo := RefVec.map.go_le_size _ _ _ _ _)) (by decide)

-- `Std.Sat.AIG.RefVec.map.go_get_aux`: removable (dependent), map.go_le_size.
theorem map_go_get_aux_14 : indep% Std.Sat.AIG.RefVec.map.go_get_aux 14 := by
  intro α _ _ len aig curr hcurr s input f i1 i2 idx hidx
  exact RefVec.map.go_le_size curr hcurr s input f

-- `Std.Sat.AIG.RefVec.map.go_get`: the shrinking opC is not lawful.
theorem map_go_get_10 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_get 10 :=
  fun H => nlR (H (len := 1) (aig := E0) (curr := 1) (hcurr := by decide) (s := v0) (input := v0) (f := opC)
    (idx := 0) (hidx := by decide))

-- `Std.Sat.AIG.RefVec.map.go_get`: the lawful, non-chainable opPar.
theorem map_go_get_11 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_get 11 :=
  fun H => opPar_not_map (H (len := 1) (aig := E0) (curr := 1) (hcurr := by decide) (s := v0) (input := v0) (f := opPar)
    (idx := 0) (hidx := by decide))

-- `Std.Sat.AIG.RefVec.map.go_denote_mem_prefix`: the shrinking opC is not lawful.
theorem map_go_denote_mem_prefix_12 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_denote_mem_prefix 12 :=
  fun H => nlR (H (len := 0) (assign := fun _ => false) (inv := false) (aig := E0) (curr := 0) (hcurr := by decide)
    (s := RefVec.empty) (input := RefVec.empty) (f := opC) (start := 0) (hstart := by decide))

-- `Std.Sat.AIG.RefVec.map.go_denote_mem_prefix`: the lawful, non-chainable opPar.
theorem map_go_denote_mem_prefix_13 : ¬ indep0% Std.Sat.AIG.RefVec.map.go_denote_mem_prefix 13 :=
  fun H => opPar_not_map (H (len := 0) (assign := fun _ => false) (inv := false) (aig := E0) (curr := 0)
    (hcurr := by decide) (s := RefVec.empty) (input := RefVec.empty) (f := opPar) (start := 0) (hstart := by decide))

-- `Std.Sat.AIG.RefVec.map.denote_go`: the shrinking opC is not lawful.
theorem map_denote_go_11 : ¬ indep0% Std.Sat.AIG.RefVec.map.denote_go 11 :=
  fun H => nlR (H (len := 1) (assign := fun _ => false) (aig := E0) (curr := 0) (hcurr := by decide) (s := RefVec.empty)
    (input := v0) (f := opC) (idx := 0) (hidx1 := by decide) (by decide))

-- `Std.Sat.AIG.RefVec.map.denote_go`: the lawful, non-chainable opPar.
theorem map_denote_go_12 : ¬ indep0% Std.Sat.AIG.RefVec.map.denote_go 12 :=
  fun H => opPar_not_map (H (len := 1) (assign := fun _ => false) (aig := E0) (curr := 0) (hcurr := by decide)
    (s := RefVec.empty) (input := v0) (f := opPar) (idx := 0) (hidx1 := by decide) (by decide))

-- `Std.Sat.AIG.RefVec.map.denote_go`: curr = len = 1 with the already computed entry true, while
-- opPush yields false; idx = 0.
theorem map_denote_go_15 : ¬ drop0% Std.Sat.AIG.RefVec.map.denote_go 15 := fun H => by
  have := H (len := 1) (assign := fun _ => false) (aig := E0) (curr := 1) (hcurr := by decide) (s := vec1 E0 (ref1 _))
    (input := v0) (f := opPush) (idx := 0) (hidx1 := by decide)
  rw [RefVec.map.go_get _ _ _ _ _ 0 (by decide)] at this
  simp only [vec1_get, ref1, Ref.cast, opPush] at this
  rw [den0, den_false _ (pushF_last _ _)] at this
  revert this; decide

-- `Std.Sat.AIG.RefVec.denote_map`: len = 0, idx = 0.
theorem denote_map_8 : ¬ indep0% Std.Sat.AIG.RefVec.denote_map 8 :=
  fun H => absurd (H (len := 0) (assign := fun _ => false) (aig := E0) (target := ⟨RefVec.empty, opPush⟩) (idx := 0))
    (by decide)

/-! ### Zip -/

-- `Std.Sat.AIG.RefVec.LawfulZipOperator.chainable`: the shrinking opC is not lawful.
theorem LZO_chainable_4 : ¬ indep0% Std.Sat.AIG.RefVec.LawfulZipOperator.chainable 4 :=
  fun H => nlB (H (f := opC) (aig := E0) (input1 := b0) (input2 := b0) (h := by decide) (assign := fun _ => false))

-- `Std.Sat.AIG.RefVec.LawfulZipOperator.chainable`: the lawful opPar (output depends on the AIG size) is not chainable.
theorem LZO_chainable_5 : ¬ drop0% Std.Sat.AIG.RefVec.LawfulZipOperator.chainable 5 :=
  fun H => opPar_bad _ _ _ _ (@H Nat _ _ opPar inferInstance E0 b0 b0
    (by simp [opPar, pushF_size]) (fun _ => false))

-- `Std.Sat.AIG.RefVec.LawfulZipOperator.chainable`: removable (dependent), le_size of the lawful operator.
theorem LZO_chainable_9 : indep% Std.Sat.AIG.RefVec.LawfulZipOperator.chainable 9 := by
  intro α _ _ f inst self aig input1 input2 assign
  exact LawfulOperator.le_size aig input1

-- `Std.Sat.AIG.RefVec.LawfulZipOperator.denote_prefix_cast_ref`: the shrinking opC is not lawful.
theorem LZO_denote_prefix_cast_ref_8 : ¬ indep0% Std.Sat.AIG.RefVec.LawfulZipOperator.denote_prefix_cast_ref 8 :=
  fun H => nlB (H (assign := fun _ => false) (aig := E0) (input1 := b0) (input2 := b0) (f := opC) (h := by decide))

-- `Std.Sat.AIG.RefVec.LawfulZipOperator.denote_prefix_cast_ref`: the lawful, non-chainable opPar.
theorem LZO_denote_prefix_cast_ref_9 : ¬ drop0% Std.Sat.AIG.RefVec.LawfulZipOperator.denote_prefix_cast_ref 9 :=
  fun H => opPar_bad _ _ _ _ (H (assign := fun _ => false) (aig := E0) (input1 := b0) (input2 := b0)
    (f := opPar) (h := by simp [opPar, pushF_size]))

-- `Std.Sat.AIG.RefVec.LawfulZipOperator.denote_prefix_cast_ref`: removable (dependent), le_size of the lawful operator.
theorem LZO_denote_prefix_cast_ref_10 : indep% Std.Sat.AIG.RefVec.LawfulZipOperator.denote_prefix_cast_ref 10 := by
  intro α _ _ assign aig input1 input2 f i1 i2
  exact LawfulOperator.le_size aig input1

-- `Std.Sat.AIG.RefVec.zip.go_le_size`: the shrinking opC is not lawful.
theorem zip_go_le_size_11 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_le_size 11 :=
  fun H => nlB (H (len := 0) (aig := E0) (idx := 0) (hidx := by decide) (s := RefVec.empty) (lhs := RefVec.empty)
    (rhs := RefVec.empty) (f := opC))

-- `Std.Sat.AIG.RefVec.zip.go_le_size`: the lawful, non-chainable opPar.
theorem zip_go_le_size_12 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_le_size 12 :=
  fun H => opPar_not_zip (H (len := 0) (aig := E0) (idx := 0) (hidx := by decide) (s := RefVec.empty) (lhs := RefVec.empty)
    (rhs := RefVec.empty) (f := opPar))

-- `Std.Sat.AIG.RefVec.zip_le_size`: the shrinking opC is not lawful.
theorem zip_le_size_7 : ¬ indep0% Std.Sat.AIG.RefVec.zip_le_size 7 :=
  fun H => nlB (H (len := 0) (aig := E0) (input := bv0) (func := opC))

-- `Std.Sat.AIG.RefVec.zip_le_size`: the lawful, non-chainable opPar.
theorem zip_le_size_8 : ¬ indep0% Std.Sat.AIG.RefVec.zip_le_size 8 :=
  fun H => opPar_not_zip (H (len := 0) (aig := E0) (input := bv0) (func := opPar))

-- `Std.Sat.AIG.RefVec.zip.go_decl_eq`: the shrinking opC is not lawful.
theorem zip_go_decl_eq_11 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_decl_eq 11 :=
  fun H => nlB (H (len := 0) (aig := E0) (i := 0) (hi := by decide) (lhs := RefVec.empty) (rhs := RefVec.empty)
    (s := RefVec.empty) (f := opC) (idx := 0) (h1 := by decide))

-- `Std.Sat.AIG.RefVec.zip.go_decl_eq`: the lawful, non-chainable opPar.
theorem zip_go_decl_eq_12 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_decl_eq 12 :=
  fun H => opPar_not_zip (H (len := 0) (aig := E0) (i := 0) (hi := by decide) (lhs := RefVec.empty) (rhs := RefVec.empty)
    (s := RefVec.empty) (f := opPar) (idx := 0) (h1 := by decide))

-- `Std.Sat.AIG.RefVec.zip.go_decl_eq`: zipping with opPush over one entry grows the empty AIG; idx = 1.
theorem zip_go_decl_eq_14 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_decl_eq 14 :=
  fun H => absurd (H (len := 1) (aig := E0) (i := 0) (hi := by decide) (lhs := v0) (rhs := v0) (s := RefVec.empty)
    (f := opPush) (idx := 1) (h2 := zip_grow _ _ _)) (by decide)

-- `Std.Sat.AIG.RefVec.zip.go_decl_eq`: removable (dependent), zip.go_le_size.
theorem zip_go_decl_eq_15 : indep% Std.Sat.AIG.RefVec.zip.go_decl_eq 15 := by
  intro α _ _ len aig i hi lhs rhs s f i1 i2 idx h1
  exact Nat.lt_of_lt_of_le h1 (RefVec.zip.go_le_size i hi s lhs rhs f)

-- `Std.Sat.AIG.RefVec.zip_decl_eq`: the shrinking opC is not lawful.
theorem zip_decl_eq_7 : ¬ indep0% Std.Sat.AIG.RefVec.zip_decl_eq 7 :=
  fun H => nlB (H (len := 0) (aig := E0) (input := bv0) (func := opC) (idx := 0) (h1 := by decide))

-- `Std.Sat.AIG.RefVec.zip_decl_eq`: the lawful, non-chainable opPar.
theorem zip_decl_eq_8 : ¬ indep0% Std.Sat.AIG.RefVec.zip_decl_eq 8 :=
  fun H => opPar_not_zip (H (len := 0) (aig := E0) (input := bv0) (func := opPar) (idx := 0) (h1 := by decide))

-- `Std.Sat.AIG.RefVec.zip_decl_eq`: zipping with opPush over one entry grows the empty AIG; idx = 1.
theorem zip_decl_eq_10 : ¬ indep0% Std.Sat.AIG.RefVec.zip_decl_eq 10 :=
  fun H => absurd (H (len := 1) (aig := E0) (input := ⟨v0, v0⟩) (func := opPush) (idx := 1)
    (h2 := by unfold RefVec.zip; exact zip_grow _ _ _)) (by decide)

-- `Std.Sat.AIG.RefVec.zip_decl_eq`: removable (dependent), zip_le_size.
theorem zip_decl_eq_11 : indep% Std.Sat.AIG.RefVec.zip_decl_eq 11 := by
  intro α _ _ len aig input func i1 i2 idx h1
  exact Nat.lt_of_lt_of_le h1 (RefVec.zip_le_size aig input func)

-- `Std.Sat.AIG.RefVec.zip_lt_size_of_lt_aig_size`: the shrinking opC is not lawful.
theorem zip_lt_size_of_lt_aig_size_8 : ¬ indep0% Std.Sat.AIG.RefVec.zip_lt_size_of_lt_aig_size 8 :=
  fun H => nlB (H (len := 0) (x := 0) (aig := E0) (input := bv0) (func := opC) (by decide))

-- `Std.Sat.AIG.RefVec.zip_lt_size_of_lt_aig_size`: the lawful, non-chainable opPar.
theorem zip_lt_size_of_lt_aig_size_9 : ¬ indep0% Std.Sat.AIG.RefVec.zip_lt_size_of_lt_aig_size 9 :=
  fun H => opPar_not_zip (H (len := 0) (x := 0) (aig := E0) (input := bv0) (func := opPar) (by decide))

-- `Std.Sat.AIG.RefVec.zip_lt_size_of_lt_aig_size`: zipping empty vectors keeps the empty AIG; x = 1.
theorem zip_lt_size_of_lt_aig_size_10 : ¬ drop0% Std.Sat.AIG.RefVec.zip_lt_size_of_lt_aig_size 10 :=
  fun H => absurd (H (len := 0) (x := 1) (aig := E0) (input := ⟨RefVec.empty, RefVec.empty⟩) (func := opPush))
    (by rw [zip0]; decide)

-- `Std.Sat.AIG.RefVec.zip_le_size_of_le_aig_size`: the shrinking opC is not lawful.
theorem zip_le_size_of_le_aig_size_8 : ¬ indep0% Std.Sat.AIG.RefVec.zip_le_size_of_le_aig_size 8 :=
  fun H => nlB (H (len := 0) (x := 0) (aig := E0) (input := bv0) (func := opC) (by decide))

-- `Std.Sat.AIG.RefVec.zip_le_size_of_le_aig_size`: the lawful, non-chainable opPar.
theorem zip_le_size_of_le_aig_size_9 : ¬ indep0% Std.Sat.AIG.RefVec.zip_le_size_of_le_aig_size 9 :=
  fun H => opPar_not_zip (H (len := 0) (x := 0) (aig := E0) (input := bv0) (func := opPar) (by decide))

-- `Std.Sat.AIG.RefVec.zip_le_size_of_le_aig_size`: zipping empty vectors keeps the empty AIG; x = 2.
theorem zip_le_size_of_le_aig_size_10 : ¬ drop0% Std.Sat.AIG.RefVec.zip_le_size_of_le_aig_size 10 :=
  fun H => absurd (H (len := 0) (x := 2) (aig := E0) (input := ⟨RefVec.empty, RefVec.empty⟩) (func := opPush))
    (by rw [zip0]; decide)

-- `Std.Sat.AIG.RefVec.IsPrefix_zip`: the shrinking opC is not lawful.
theorem IsPrefix_zip_7 : ¬ indep0% Std.Sat.AIG.RefVec.IsPrefix_zip 7 :=
  fun H => nlB (H (len := 0) (aig := E0) (input := bv0) (func := opC))

-- `Std.Sat.AIG.RefVec.IsPrefix_zip`: the lawful, non-chainable opPar.
theorem IsPrefix_zip_8 : ¬ indep0% Std.Sat.AIG.RefVec.IsPrefix_zip 8 :=
  fun H => opPar_not_zip (H (len := 0) (aig := E0) (input := bv0) (func := opPar))

-- `Std.Sat.AIG.RefVec.zip.go_get_aux`: the shrinking opC is not lawful.
theorem zip_go_get_aux_11 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_get_aux 11 :=
  fun H => nlB (H (len := 1) (aig := E0) (curr := 1) (hcurr := by decide) (s := v0) (lhs := v0) (rhs := v0) (f := opC)
    (idx := 0) (hidx := by decide))

-- `Std.Sat.AIG.RefVec.zip.go_get_aux`: the lawful, non-chainable opPar.
theorem zip_go_get_aux_12 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_get_aux 12 :=
  fun H => opPar_not_zip (H (len := 1) (aig := E0) (curr := 1) (hcurr := by decide) (s := v0) (lhs := v0) (rhs := v0)
    (f := opPar) (idx := 0) (hidx := by decide))

-- `Std.Sat.AIG.RefVec.zip.go_get_aux`: curr = 0, idx = 0.
theorem zip_go_get_aux_14 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_get_aux 14 :=
  fun H => absurd (H (len := 0) (aig := E0) (curr := 0) (hcurr := by decide) (s := RefVec.empty) (lhs := RefVec.empty)
    (rhs := RefVec.empty) (f := opPush) (idx := 0) (hfoo := RefVec.zip.go_le_size _ _ _ _ _ _)) (by decide)

-- `Std.Sat.AIG.RefVec.zip.go_get_aux`: removable (dependent), zip.go_le_size.
theorem zip_go_get_aux_15 : indep% Std.Sat.AIG.RefVec.zip.go_get_aux 15 := by
  intro α _ _ len aig curr hcurr s lhs rhs f i1 i2 idx hidx
  exact RefVec.zip.go_le_size curr hcurr s lhs rhs f

-- `Std.Sat.AIG.RefVec.zip.go_get`: the shrinking opC is not lawful.
theorem zip_go_get_11 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_get 11 :=
  fun H => nlB (H (len := 1) (aig := E0) (curr := 1) (hcurr := by decide) (s := v0) (lhs := v0) (rhs := v0) (f := opC)
    (idx := 0) (hidx := by decide))

-- `Std.Sat.AIG.RefVec.zip.go_get`: the lawful, non-chainable opPar.
theorem zip_go_get_12 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_get 12 :=
  fun H => opPar_not_zip (H (len := 1) (aig := E0) (curr := 1) (hcurr := by decide) (s := v0) (lhs := v0) (rhs := v0)
    (f := opPar) (idx := 0) (hidx := by decide))

-- `Std.Sat.AIG.RefVec.zip.go_denote_mem_prefix`: the shrinking opC is not lawful.
theorem zip_go_denote_mem_prefix_13 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_denote_mem_prefix 13 :=
  fun H => nlB (H (len := 0) (assign := fun _ => false) (inv := false) (aig := E0) (curr := 0) (hcurr := by decide)
    (s := RefVec.empty) (lhs := RefVec.empty) (rhs := RefVec.empty) (f := opC) (start := 0) (hstart := by decide))

-- `Std.Sat.AIG.RefVec.zip.go_denote_mem_prefix`: the lawful, non-chainable opPar.
theorem zip_go_denote_mem_prefix_14 : ¬ indep0% Std.Sat.AIG.RefVec.zip.go_denote_mem_prefix 14 :=
  fun H => opPar_not_zip (H (len := 0) (assign := fun _ => false) (inv := false) (aig := E0) (curr := 0)
    (hcurr := by decide) (s := RefVec.empty) (lhs := RefVec.empty) (rhs := RefVec.empty) (f := opPar) (start := 0)
    (hstart := by decide))

-- `Std.Sat.AIG.RefVec.zip.denote_go`: the shrinking opC is not lawful.
theorem zip_denote_go_12 : ¬ indep0% Std.Sat.AIG.RefVec.zip.denote_go 12 :=
  fun H => nlB (H (len := 1) (assign := fun _ => false) (aig := E0) (curr := 0) (hcurr := by decide) (s := RefVec.empty)
    (lhs := v0) (rhs := v0) (f := opC) (idx := 0) (hidx1 := by decide) (by decide))

-- `Std.Sat.AIG.RefVec.zip.denote_go`: the lawful, non-chainable opPar.
theorem zip_denote_go_13 : ¬ indep0% Std.Sat.AIG.RefVec.zip.denote_go 13 :=
  fun H => opPar_not_zip (H (len := 1) (assign := fun _ => false) (aig := E0) (curr := 0) (hcurr := by decide)
    (s := RefVec.empty) (lhs := v0) (rhs := v0) (f := opPar) (idx := 0) (hidx1 := by decide) (by decide))

-- `Std.Sat.AIG.RefVec.zip.denote_go`: curr = len = 1 with the already computed entry true, while
-- opPush yields false; idx = 0.
theorem zip_denote_go_16 : ¬ drop0% Std.Sat.AIG.RefVec.zip.denote_go 16 := fun H => by
  have := H (len := 1) (assign := fun _ => false) (aig := E0) (curr := 1) (hcurr := by decide) (s := vec1 E0 (ref1 _))
    (lhs := v0) (rhs := v0) (f := opPush) (idx := 0) (hidx1 := by decide)
  rw [RefVec.zip.go_get _ _ _ _ _ _ 0 (by decide)] at this
  simp only [vec1_get, ref1, Ref.cast, opPush] at this
  rw [den0, den_false _ (pushF_last _ _)] at this
  revert this; decide

-- `Std.Sat.AIG.RefVec.denote_zip`: the shrinking opC is not lawful.
theorem denote_zip_8 : ¬ indep0% Std.Sat.AIG.RefVec.denote_zip 8 :=
  fun H => nlB (H (len := 1) (assign := fun _ => false) (aig := E0) (input := ⟨v0, v0⟩) (func := opC) (idx := 0)
    (hidx := by decide))

-- `Std.Sat.AIG.RefVec.denote_zip`: the lawful, non-chainable opPar.
theorem denote_zip_9 : ¬ indep0% Std.Sat.AIG.RefVec.denote_zip 9 :=
  fun H => opPar_not_zip (H (len := 1) (assign := fun _ => false) (aig := E0) (input := ⟨v0, v0⟩) (func := opPar)
    (idx := 0) (hidx := by decide))

-- `Std.Sat.AIG.RefVec.denote_zip`: len = 0, idx = 0.
theorem denote_zip_11 : ¬ indep0% Std.Sat.AIG.RefVec.denote_zip 11 :=
  fun H => absurd (H (len := 0) (assign := fun _ => false) (aig := E0) (input := bv0) (func := opPush) (idx := 0))
    (by decide)

end SatAIGHand

/-! ## Std.Sat.AIG.Relabel, RelabelNat -/

namespace SatAIGHand
open Std Std.Sat Std.Sat.AIG RefuteIndep

/- The constant relabeling of the two atoms of AA2 is not injective. -/
theorem AA2_notinj : ¬ ∀ x y : Nat, x ∈ AA2 → y ∈ AA2 → (fun _ : Nat => (0 : Nat)) x = (fun _ => 0) y → x = y :=
  fun h => absurd (h 0 1 ((AA2_mem 0).2 (.inl rfl)) ((AA2_mem 1).2 (.inr rfl)) rfl) (by decide)
theorem E0_inj : ∀ x y : Nat, x ∈ E0 → y ∈ E0 → id x = id y → x = y := fun _ _ _ _ h => h
theorem AA_inj : ∀ x y : Nat, x ∈ AA → y ∈ AA → id x = id y → x = y := fun _ _ _ _ h => h

-- `Std.Sat.AIG.Decl.relabel_false`: #[atom 0] at index 0.
theorem Decl_relabel_false_6 : ¬ drop0% Std.Sat.AIG.Decl.relabel_false 6 :=
  fun H => absurd (H (α := Nat) (β := Nat) (idx := 0) (decls := #[.atom 0]) (r := id) (hidx := by decide)) (by decide)

-- `Std.Sat.AIG.Decl.relabel_atom`: #[false] at index 0 is not an atom.
theorem Decl_relabel_atom_7 : ¬ drop0% Std.Sat.AIG.Decl.relabel_atom 7 := fun H => by
  obtain ⟨x, hx, _⟩ := H (α := Nat) (β := Nat) (idx := 0) (a := 0) (decls := #[.false]) (r := id) (hidx := by decide)
  cases hx

-- `Std.Sat.AIG.Decl.relabel_gate`: #[false] at index 0 is not a gate.
theorem Decl_relabel_gate_8 : ¬ drop0% Std.Sat.AIG.Decl.relabel_gate 8 := fun H => by
  have := H (α := Nat) (β := Nat) (idx := 0) (lhs := .mk 0 false) (rhs := .mk 0 false) (decls := #[.false]) (r := id)
    (hidx := by decide)
  cases this

-- `Std.Sat.AIG.relabel_size_eq_size`: the constant relabeling of AA2 (atoms 0, 1) is not injective.
theorem relabel_size_eq_size_8 : ¬ indep0% Std.Sat.AIG.relabel_size_eq_size 8 :=
  fun H => AA2_notinj (H (β := Nat) (aig := AA2) (r := fun _ => 0))

-- `Std.Sat.AIG.relabel_false`: the constant relabeling of AA2 is not injective.
theorem relabel_false_9 : ¬ indep0% Std.Sat.AIG.relabel_false 9 :=
  fun H => AA2_notinj (H (β := Nat) (idx := 0) (aig := AA2) (r := fun _ => 0))

-- `Std.Sat.AIG.relabel_false`: index 5 of the relabeled empty AIG.
theorem relabel_false_10 : ¬ indep0% Std.Sat.AIG.relabel_false 10 :=
  fun H => absurd (H (β := Nat) (idx := 5) (aig := E0) (r := id) (hinj := E0_inj)) (by rw [relabel_size_eq_size]; decide)

-- `Std.Sat.AIG.relabel_false`: node 1 of AA is an atom.
theorem relabel_false_11 : ¬ drop0% Std.Sat.AIG.relabel_false 11 :=
  fun H => absurd (H (β := Nat) (idx := 1) (aig := AA) (r := id) (hinj := AA_inj) (hidx := by rw [relabel_size_eq_size]; decide))
    (by decide)

-- `Std.Sat.AIG.relabel_atom`: the constant relabeling of AA2 is not injective.
theorem relabel_atom_10 : ¬ indep0% Std.Sat.AIG.relabel_atom 10 :=
  fun H => AA2_notinj (H (β := Nat) (idx := 0) (a := 0) (aig := AA2) (r := fun _ => 0))

-- `Std.Sat.AIG.relabel_atom`: index 5 of the relabeled empty AIG.
theorem relabel_atom_11 : ¬ indep0% Std.Sat.AIG.relabel_atom 11 :=
  fun H => absurd (H (β := Nat) (idx := 5) (a := 0) (aig := E0) (r := id) (hinj := E0_inj)) (by rw [relabel_size_eq_size]; decide)

-- `Std.Sat.AIG.relabel_atom`: node 0 of the empty AIG is not an atom.
theorem relabel_atom_12 : ¬ drop0% Std.Sat.AIG.relabel_atom 12 := fun H => by
  obtain ⟨x, hx, _⟩ := H (β := Nat) (idx := 0) (a := 0) (aig := E0) (r := id) (hinj := E0_inj)
    (hidx := by rw [relabel_size_eq_size]; decide)
  cases hx

-- `Std.Sat.AIG.relabel_gate`: the constant relabeling of AA2 is not injective.
theorem relabel_gate_11 : ¬ indep0% Std.Sat.AIG.relabel_gate 11 :=
  fun H => AA2_notinj (H (β := Nat) (idx := 0) (lhs := .mk 0 false) (rhs := .mk 0 false) (aig := AA2) (r := fun _ => 0))

-- `Std.Sat.AIG.relabel_gate`: index 5 of the relabeled empty AIG.
theorem relabel_gate_12 : ¬ indep0% Std.Sat.AIG.relabel_gate 12 :=
  fun H => absurd (H (β := Nat) (idx := 5) (lhs := .mk 0 false) (rhs := .mk 0 false) (aig := E0) (r := id)
    (hinj := E0_inj)) (by rw [relabel_size_eq_size]; decide)

-- `Std.Sat.AIG.relabel_gate`: node 0 of the empty AIG is not a gate.
theorem relabel_gate_13 : ¬ drop0% Std.Sat.AIG.relabel_gate 13 := fun H => by
  have := H (β := Nat) (idx := 0) (lhs := .mk 0 false) (rhs := .mk 0 false) (aig := E0) (r := id) (hinj := E0_inj)
    (hidx := by rw [relabel_size_eq_size]; decide)
  cases this

-- `Std.Sat.AIG.denote_relabel`: the constant relabeling of AA2 is not injective.
theorem denote_relabel_9 : ¬ indep0% Std.Sat.AIG.denote_relabel 9 :=
  fun H => AA2_notinj (H (β := Nat) (invert := false) (aig := AA2) (r := fun _ => 0) (start := 0) (assign := fun _ => false))

-- `Std.Sat.AIG.denote_relabel`: index 5 of the relabeled empty AIG.
theorem denote_relabel_11 : ¬ indep0% Std.Sat.AIG.denote_relabel 11 :=
  fun H => absurd (H (β := Nat) (invert := false) (aig := E0) (r := id) (hinj := E0_inj) (start := 5)
    (assign := fun _ => false)) (by rw [relabel_size_eq_size]; decide)

-- `Std.Sat.AIG.unsat_relabel`: the constant relabeling of AA2 is not injective (node 0 is unsat).
theorem unsat_relabel_10 : ¬ indep0% Std.Sat.AIG.unsat_relabel 10 :=
  fun H => AA2_notinj (H (β := Nat) (idx := 0) (invert := false) (aig := AA2) (r := fun _ => 0) (hidx := by decide)
    (fun assign => den0 _ _ _))

-- `Std.Sat.AIG.unsat_relabel`: node 0 inverted (true) of the relabeled empty AIG is satisfiable.
theorem unsat_relabel_12 : ¬ drop0% Std.Sat.AIG.unsat_relabel 12 := fun H => by
  have := H (β := Nat) (idx := 0) (invert := true) (aig := E0) (r := id) (hinj := E0_inj) (hidx := by decide)
    (fun _ => false)
  rw [den0] at this; revert this; decide

-- `Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty`: removable (dependent), with α empty hinj holds vacuously.
theorem relabel_unsat_iff_of_not_Nonempty_10 : indep% Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty 10 := by
  intro α _ _ β _ _ idx invert aig r hidx2 hne x
  exact absurd ⟨x⟩ hne

-- `Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty`: removable, the sibling relabel_unsat_iff has no such hypothesis.
theorem relabel_unsat_iff_of_not_Nonempty_13 : drop% Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty 13 := by
  intro α _ _ β _ _ idx invert aig r hinj hidx1 hidx2
  exact relabel_unsat_iff

-- `Std.Sat.AIG.relabel_unsat_iff_of_Nonempty`: removable, the sibling relabel_unsat_iff has no such hypothesis.
theorem relabel_unsat_iff_of_Nonempty_8 : drop% Std.Sat.AIG.relabel_unsat_iff_of_Nonempty 8 := by
  intro α _ _ β _ _ idx invert aig r hinj hidx1 hidx2
  exact relabel_unsat_iff

-- `Std.Sat.AIG.relabel_unsat_iff_of_Nonempty`: the constant relabeling of AA2 is not injective.
theorem relabel_unsat_iff_of_Nonempty_11 : ¬ indep0% Std.Sat.AIG.relabel_unsat_iff_of_Nonempty 11 :=
  fun H => AA2_notinj (H (β := Nat) (idx := 0) (invert := false) (aig := AA2) (r := fun _ => 0) (hidx2 := by decide))

-- `Std.Sat.AIG.relabel_unsat_iff`: the constant relabeling of AA2 is not injective.
theorem relabel_unsat_iff_10 : ¬ indep0% Std.Sat.AIG.relabel_unsat_iff 10 :=
  fun H => AA2_notinj (H (β := Nat) (idx := 0) (invert := false) (aig := AA2) (r := fun _ => 0) (hidx2 := by decide))

-- `Std.Sat.AIG.Entrypoint.relabel_size_eq`: the constant relabeling of AA2 is not injective.
theorem Entrypoint_relabel_size_eq_8 : ¬ indep0% Std.Sat.AIG.Entrypoint.relabel_size_eq 8 :=
  fun H => AA2_notinj (H (β := Nat) (entry := ⟨AA2, ref0 _⟩) (r := fun _ => 0))

-- `Std.Sat.AIG.Entrypoint.relabel_unsat_iff`: the constant relabeling of AA2 is not injective.
theorem Entrypoint_relabel_unsat_iff_8 : ¬ indep0% Std.Sat.AIG.Entrypoint.relabel_unsat_iff 8 :=
  fun H => AA2_notinj (H (β := Nat) (entry := ⟨AA2, ref0 _⟩) (r := fun _ => 0))

/-! ### RelabelNat -/

open RelabelNat.State in
/- Every key of a map satisfying Inv2 is an atom of decls. -/
theorem inv2_keys {decls : Array (Decl Nat)} {upper : Nat} {map : HashMap Nat Nat} (hinv : Inv2 decls upper map)
    (a n : Nat) (h : map[a]? = some n) : ∃ i, ∃ hi : i < decls.size, decls[i] = .atom a := by
  induction hinv with
  | empty => simp at h
  | newAtom _ hlt hatom _ ih =>
    rw [HashMap.getElem?_insert] at h
    split at h
    · next he => simp at he; subst he; exact ⟨_, hlt, hatom⟩
    · exact ih h
  | oldAtom _ _ _ _ ih => exact ih h
  | false _ _ _ ih => exact ih h
  | gate _ _ _ ih => exact ih h

open RelabelNat.State in
/- A nonempty Inv1 map gives some key the value 0. -/
theorem inv1_zero {k : Nat} {map : HashMap Nat Nat} (h : Inv1 k map) : k = 0 ∨ ∃ y : Nat, map[y]? = some 0 := by
  induction h with
  | empty => exact .inl rfl
  | insert hinv hfind ih =>
    rename_i n m x
    refine .inr ?_
    rcases ih with rfl | ⟨y, hy⟩
    · exact ⟨x, by simp⟩
    · refine ⟨y, ?_⟩
      rw [HashMap.getElem?_insert]
      split
      · next he => simp at he; subst he; simp_all
      · exact hy

/- In ofAIG AA some atom of AA gets the value 0, and keys outside AA are missing. -/
theorem ofAIG_AA_key (a n : Nat) (h : (RelabelNat.State.ofAIG AA)[a]? = some n) : a = 0 := by
  obtain ⟨i, hi, he⟩ := inv2_keys (RelabelNat.State.ofAIG.Inv2 AA) a n h
  match i, hi with
  | 0, _ => cases he
  | 1, _ => cases he; rfl
theorem ofAIG_AA_zero : (RelabelNat.State.ofAIG AA)[0]? = some 0 := by
  obtain ⟨k, hk⟩ := RelabelNat.State.ofAIG.Inv1 AA
  obtain ⟨n, hn⟩ := RelabelNat.State.ofAIG_find_some (aig := AA) 0 ((AA_mem 0).2 rfl)
  rcases inv1_zero hk with rfl | ⟨y, hy⟩
  · exact absurd (RelabelNat.State.Inv1.lt_of_get?_eq_some _ _ hk hn) (Nat.not_lt_zero _)
  · rwa [ofAIG_AA_key y 0 hy] at hy
theorem map_AA (x : Nat) : relabelNat.map (RelabelNat.State.ofAIG AA) x = 0 := by
  unfold relabelNat.map
  rw [HashMap.getElem!_eq_get!_getElem?]
  by_cases hx : x = 0
  · subst hx; rw [ofAIG_AA_zero]; rfl
  · cases h : (RelabelNat.State.ofAIG AA)[x]? with
    | none => rfl
    | some n => exact absurd (ofAIG_AA_key x n h) hx

-- `Std.Sat.AIG.RelabelNat.State.Inv1.lt_of_get?_eq_some`: the map {0 ↦ 5} with n = 0.
theorem Inv1_lt_of_get?_eq_some_8 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.Inv1.lt_of_get?_eq_some 8 :=
  fun H => absurd (H (α := Nat) (n := 0) (m := 5) (map := (∅ : HashMap Nat Nat).insert 0 5) (x := 0) (by simp))
    (by decide)

-- `Std.Sat.AIG.RelabelNat.State.Inv1.lt_of_get?_eq_some`: the empty map with n = m = 0.
theorem Inv1_lt_of_get?_eq_some_9 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.Inv1.lt_of_get?_eq_some 9 :=
  fun H => absurd (H (α := Nat) (n := 0) (m := 0) (map := ∅) (x := 0) .empty) (by decide)

-- `Std.Sat.AIG.RelabelNat.State.Inv1.property`: the non-injective map {0 ↦ 0, 1 ↦ 0}.
theorem Inv1_property_9 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.Inv1.property 9 :=
  fun H => absurd (H (α := Nat) (n := 0) (m := 0) (x := 0) (y := 1)
    (map := ((∅ : HashMap Nat Nat).insert 0 0).insert 1 0)
    (by rw [HashMap.getElem?_insert, if_neg (by decide), HashMap.getElem?_insert_self]) (by simp)) (by decide)

-- `Std.Sat.AIG.RelabelNat.State.Inv1.property`: {0 ↦ 0} (valid Inv1 1), x = 1, y = 0.
theorem Inv1_property_10 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.Inv1.property 10 :=
  fun H => absurd (H (α := Nat) (n := 1) (m := 0) (x := 1) (y := 0) (map := (∅ : HashMap Nat Nat).insert 0 0)
    (.insert .empty (by simp)) (by simp)) (by decide)

-- `Std.Sat.AIG.RelabelNat.State.Inv1.property`: {0 ↦ 0} (valid Inv1 1), x = 0, y = 1.
theorem Inv1_property_11 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.Inv1.property 11 :=
  fun H => absurd (H (α := Nat) (n := 1) (m := 0) (x := 0) (y := 1) (map := (∅ : HashMap Nat Nat).insert 0 0)
    (.insert .empty (by simp)) (by simp)) (by decide)

-- `Std.Sat.AIG.RelabelNat.State.Inv2.upper_lt_size`: upper = 1 for the empty array.
theorem Inv2_upper_lt_size_6 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.Inv2.upper_lt_size 6 :=
  fun H => absurd (H (α := Nat) (upper := 1) (map := ∅) (decls := #[])) (by decide)

-- `Std.Sat.AIG.RelabelNat.State.Inv2.property`: upper = 0 (Inv2.empty), idx = 0.
theorem Inv2_property_7 : ¬ indep0% Std.Sat.AIG.RelabelNat.State.Inv2.property 7 :=
  fun H => absurd (H (α := Nat) (decls := #[]) (idx := 0) (upper := 0) (map := ∅) (a := 0) .empty) (by decide)

-- `Std.Sat.AIG.RelabelNat.State.Inv2.property`: Inv2 #[] 1 map fails (upper ≤ size).
theorem Inv2_property_9 : ¬ indep0% Std.Sat.AIG.RelabelNat.State.Inv2.property 9 :=
  fun H => absurd (H (α := Nat) (decls := #[]) (idx := 0) (upper := 1) (map := ∅) (hidx := by decide) (a := 0)).upper_lt_size
    (by decide)

-- `Std.Sat.AIG.RelabelNat.State.Inv2.property`: #[false] with the empty map, a = 0.
theorem Inv2_property_10 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.Inv2.property 10 := fun H => by
  obtain ⟨n, hn⟩ := H (α := Nat) (decls := #[.false]) (idx := 0) (upper := 1) (map := ∅) (hidx := by decide) (a := 0)
    (.false .empty (by decide) rfl)
  simp at hn

-- `Std.Sat.AIG.RelabelNat.State.ofAIG_find_unique`: in ofAIG AA the atom 0 has some value n; a = 1, a' = 0.
theorem ofAIG_find_unique_6 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.ofAIG_find_unique 6 := fun H => by
  obtain ⟨n, hn⟩ := RelabelNat.State.ofAIG_find_some (aig := AA) 0 ((AA_mem 0).2 rfl)
  exact absurd (H (n := n) (aig := AA) (a := 1) (a' := 0) hn) (by decide)

-- `Std.Sat.AIG.RelabelNat.State.ofAIG_find_unique`: in ofAIG AA the atom 0 has some value n; a = 0, a' = 1.
theorem ofAIG_find_unique_8 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.ofAIG_find_unique 8 := fun H => by
  obtain ⟨n, hn⟩ := RelabelNat.State.ofAIG_find_some (aig := AA) 0 ((AA_mem 0).2 rfl)
  exact absurd (H (n := n) (aig := AA) (a := 0) (ha := hn) (a' := 1)) (by decide)

-- `Std.Sat.AIG.RelabelNat.State.ofAIG_find_some`: atom 0 is not in the empty AIG, so ofAIG has no key 0.
theorem ofAIG_find_some_5 : ¬ drop0% Std.Sat.AIG.RelabelNat.State.ofAIG_find_some 5 := fun H => by
  obtain ⟨n, hn⟩ := H (aig := E0) (a := 0)
  obtain ⟨i, hi, he⟩ := inv2_keys (RelabelNat.State.ofAIG.Inv2 E0) 0 n hn
  match i, hi with
  | 0, _ => cases he

-- `Std.Sat.AIG.relabelNat.map_inj`: in ofAIG AA the atom 0 and the non-atom 7 both map to 0.
theorem map_inj_6 : ¬ drop0% Std.Sat.AIG.relabelNat.map_inj 6 :=
  fun H => absurd (H AA 7 0 ((AA_mem 0).2 rfl) (by rw [map_AA, map_AA])) (by decide)

-- `Std.Sat.AIG.relabelNat.map_inj`: in ofAIG AA the atom 0 and the non-atom 7 both map to 0.
theorem map_inj_7 : ¬ drop0% Std.Sat.AIG.relabelNat.map_inj 7 :=
  fun H => absurd (H AA 0 7 ((AA_mem 0).2 rfl) (by rw [map_AA, map_AA])) (by decide)

-- `Std.Sat.AIG.relabelNat.map_inj`: the two atoms 0, 1 of AA2.
theorem map_inj_8 : ¬ drop0% Std.Sat.AIG.relabelNat.map_inj 8 :=
  fun H => absurd (H AA2 0 1 ((AA2_mem 0).2 (.inl rfl)) ((AA2_mem 1).2 (.inr rfl))) (by decide)

end SatAIGHand
