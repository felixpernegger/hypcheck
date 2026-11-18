module
-- combinatorial-games: runs/gen/RefuteCore.lean as a module (module system), definitions `meta`; imported by
-- runs/probe/Header.lean. The plain original is runs/gen/RefuteCore_plain.lean.
public import HCHeaderM
public meta import Lean.Elab.Tactic

public section


/-! ## `refute_dep`: mechanical refutation of dependent rows (generic core; from hypcheck's Std Phase 1)

`refute_dep` proves `¬ ∀ indep, Hᵢ` (the statement `¬ indep0% T i` of a dependent row): it instantiates the
hypothesis `h : ∀ indep, Hᵢ` with metavariables, refutes `Hᵢ` with a *strategy* (a model whose law fails, picked
by unification, e.g. `exact MyModel.notLawful`, or `skip` to leave `¬ Hᵢ` to the closers), then fills the
remaining binders by backtracking: types from `refute_type`, data from `refute_value` (and values already given to
binders of the same type), instance premises by instance search, Prop premises by `refute_closer`.

All four lists are extension points: every `macro_rules` alternative of the syntax is one candidate, the most
recently declared first. Library-specific models go in `runs/gen/Models.lean`, e.g.
  macro_rules | `(tactic| refute_strategy) => `(tactic| exact MyModel.notTrans)
  macro_rules | `(refute_value) => `(MyModel.bad)
  macro_rules | `(tactic| refute_closer) => `(tactic| norm_num)
Use it only on dependent rows (on a non-dependent `¬ drop0%` goal it searches for a long time in vain).
No `xs[i]!` in this file: libraries may declare a `]!` token. -/

syntax (name := hcRefuteStrategy) "refute_strategy" : tactic
syntax (name := hcRefuteCloser) "refute_closer" : tactic
syntax (name := hcRefuteValue) "refute_value" : term
syntax (name := hcRefuteType) "refute_type" : term

-- generic defaults (types for `indep0%`'s universe 0: `Type` binders get `Nat`/`Bool`/…, `Sort` binders `Prop`s)
macro_rules | `(refute_type) => `(Nat)
macro_rules | `(refute_type) => `(Bool)
macro_rules | `(refute_type) => `(Unit)
macro_rules | `(refute_type) => `(Empty)
macro_rules | `(refute_type) => `(fun _ => Nat)
macro_rules | `(refute_type) => `(False)
macro_rules | `(refute_type) => `(True)
macro_rules | `(refute_value) => `(⟨0, 0⟩)
macro_rules | `(refute_value) => `(⟨⟩)
macro_rules | `(refute_value) => `(⟨0⟩)
macro_rules | `(refute_value) => `(default)
macro_rules | `(refute_value) => `(id)
macro_rules | `(refute_value) => `(fun _ _ => 0)
macro_rules | `(refute_value) => `(fun _ => 0)
macro_rules | `(refute_value) => `(fun _ => none)
macro_rules | `(refute_value) => `(fun _ _ => false)
macro_rules | `(refute_value) => `(fun _ _ => true)
macro_rules | `(refute_value) => `(fun _ => false)
macro_rules | `(refute_value) => `(fun _ => true)
macro_rules | `(refute_value) => `([0, 1])
macro_rules | `(refute_value) => `([0])
macro_rules | `(refute_value) => `([])
macro_rules | `(refute_value) => `(())
macro_rules | `(refute_value) => `(some 0)
macro_rules | `(refute_value) => `(none)
macro_rules | `(refute_value) => `(false)
macro_rules | `(refute_value) => `(true)
macro_rules | `(refute_value) => `(2)
macro_rules | `(refute_value) => `(1)
macro_rules | `(refute_value) => `(0)
macro_rules | `(refute_value) => `(∅)
macro_rules | `(refute_value) => `(inferInstance)
macro_rules | `(tactic| refute_closer) => `(tactic| simp_all)
macro_rules | `(tactic| refute_closer) => `(tactic| omega)
macro_rules | `(tactic| refute_closer) => `(tactic| simp)
macro_rules | `(tactic| refute_closer) => `(tactic| decide +kernel)
macro_rules | `(tactic| refute_closer) => `(tactic| decide)
macro_rules | `(tactic| refute_closer) => `(tactic| trivial)
macro_rules | `(tactic| refute_closer) => `(tactic| rfl)

namespace HcRefute
open Lean Meta Elab Tactic Term

/-- Every `macro_rules` expansion of `stx` (one per registered alternative), most recent first. -/
meta def alternatives (stx : Syntax) : TacticM (Array Syntax) := do
  let mut out := #[]
  for e in macroAttribute.getEntries (← getEnv) stx.getKind do
    try out := out.push (← liftMacroM (e.value stx)) catch _ => pure ()
  return out

meta def debug : IO Bool := return (← IO.getEnv "REFUTE_DEBUG").isSome

/-- Run `tac` on `g` within `hb` thousand heartbeats; the remaining goals, or `none` on failure. -/
meta def runOn (g : MVarId) (tac : TSyntax `tactic) (hb : Nat) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  let r ← withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
    tryCatchRuntimeEx (some <$> Term.withoutErrToSorry (Tactic.run g (evalTactic tac))) (fun _ => pure none)
  let r ← match r with
    | some gs => if (← instantiateMVars (mkMVar g)).hasSorry then pure none else pure (some gs)
    | none => pure none
  if r.isNone then s.restore
  return r

/-- Close `g` with `tac` (on a fresh goal with the instantiated statement, then transfer the proof). -/
meta def closes (g : MVarId) (tac : TSyntax `tactic) (hb : Nat) : TacticM Bool := do
  let s ← saveState
  let ty ← instantiateMVars (← g.getType)
  let g2 ← g.withContext <| mkFreshExprMVar ty
  match ← runOn g2.mvarId! tac hb with
  | some [] =>
    let pf ← instantiateMVars g2
    if or pf.hasExprMVar pf.hasSorry then s.restore; return false
    g.assign pf; return true
  | _ => s.restore; return false

/-- Elaborate `stx` at type `ty`; succeed only without new unassigned metavariables. -/
meta def elabAt (stx : Term) (ty : Expr) : TacticM (Option Expr) := do
  let s ← saveState
  let r ← withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 400000 }) do
    tryCatchRuntimeEx (do
      let e ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTermEnsuringType stx ty
      let e ← instantiateMVars e
      if or e.hasExprMVar e.hasSorry then return none
      return some e) (fun _ => pure none)
  if r.isNone then s.restore
  return r

meta structure Cands where
  types : Array Term
  values : Array Term
  closers : Array (TSyntax `tactic)

meta partial def search (gs : List MVarId) (fuel : IO.Ref Nat) (failed : IO.Ref (Std.HashSet Expr)) (c : Cands)
    (prev : Array Expr := #[]) : TacticM Bool := do
  let gs ← gs.filterM fun g => return !(← g.isAssigned)
  if gs.isEmpty then return true
  if (← fuel.get) == 0 then return false
  -- a Prop goal without unassigned metavariables first (prunes early)
  let mut ready : Option MVarId := none
  let mut firstData : Option MVarId := none
  for g in gs do
    let ty ← instantiateMVars (← g.getType)
    if ← isProp ty then
      if !ty.hasExprMVar && ready.isNone then ready := some g
    else if firstData.isNone then firstData := some g
  -- most constrained first: a data goal of the Prop goal with the fewest open data goals
  let dataGs ← gs.filterM fun g => return !(← isProp (← instantiateMVars (← g.getType)))
  let mut best : Option (Array MVarId) := none
  if ready.isNone then
    for g in gs do
      let ty ← instantiateMVars (← g.getType)
      if ← isProp ty then
        let ms := (← getMVars ty).filter (dataGs.contains ·)
        if !ms.isEmpty && (match best with | some b => decide (ms.size < b.size) | none => true) then best := some ms
  let mut constrained : Option MVarId := (best.bind fun ms => dataGs.find? (ms.contains ·))
  if let some k := constrained then  -- but the open goals in its type (e.g. its carrier) first
    if let some t := (← getMVars (← instantiateMVars (← k.getType))).find? (dataGs.contains ·) then constrained := some t
  let some g := ready <|> constrained <|> firstData <|> gs.head? | return false
  let rest := gs.filter (· != g)
  let ty ← instantiateMVars (← g.getType)
  if ← isProp ty then
    if (← failed.get).contains ty then return false
    fuel.modify (· - 1)
    if (← isClass? ty).isSome then  -- class premises: instance search only
      let r ← withCurrHeartbeats <| withTheReader Core.Context (fun k => { k with maxHeartbeats := 50000000 }) <|
        tryCatchRuntimeEx (synthInstance? ty) (fun _ => pure none)
      if let some inst := r then
        let s ← saveState
        g.assign inst
        if ← search rest fuel failed c prev then return true
        s.restore
      if ← debug then IO.eprintln s!"refute_dep: no instance for premise {← ppExpr ty}"
      return false
    let mut closed := false
    for tac in c.closers do
      let s ← saveState
      if ← closes g tac 2000 then
        closed := true
        if ← search rest fuel failed c prev then return true
      s.restore
    unless closed do
      failed.modify (·.insert ty)
      if ← debug then IO.eprintln s!"refute_dep: no closer for {← ppExpr ty}"
    return false
  if (← isClass? ty).isSome && !ty.hasExprMVar then  -- data instances
    let some inst ← (try synthInstance? ty catch _ => pure none)
      | if ← debug then IO.eprintln s!"refute_dep: no instance {← ppExpr ty}"
        return false
    g.assign inst
    return ← search rest fuel failed c prev
  let isTy := (← whnf (← inferType ty)).isSort && (← forallTelescopeReducing ty fun _ b => return b.isSort)
  unless isTy do  -- values already given to binders of the same type (e.g. `t₂ := t₁` for an equivalence premise)
    for e in prev do
      let s ← saveState
      if (← isDefEq (← inferType e) ty) && (← isDefEq (mkMVar g) e) then
        if ← search rest fuel failed c prev then return true
      s.restore
  for cand in (if isTy then c.types else c.values) do
    let s ← saveState
    if let some e ← elabAt cand ty then
      if ← isDefEq (mkMVar g) e then
        if ← search rest fuel failed c (if isTy then prev else prev.push e) then return true
    s.restore
  if ← debug then IO.eprintln s!"refute_dep: no value for {← ppExpr ty}"
  return false

syntax (name := refuteDep) "refute_dep" : tactic
@[tactic refuteDep] meta def evalRefuteDep : Tactic := fun _ => do
  let g ← getMainGoal
  let some (h, g') ← observing? g.intro1 | throwError "refute_dep: goal is not a negation"
  g'.withContext do
    let hty ← instantiateMVars (← h.getType)
    let c : Cands := {
      types := (← alternatives (← `(refute_type))).map (⟨·⟩)
      values := (← alternatives (← `(refute_value))).map (⟨·⟩)
      closers := (← alternatives (← `(tactic| refute_closer))).map (⟨·⟩) }
    let strats := (← alternatives (← `(tactic| refute_strategy))).map (⟨·⟩) |>.push (← `(tactic| skip))
    -- `h` may end in a class and become a local instance that sends instance search into loops: search without it
    let lctx := (← getLCtx).erase h
    let linsts := (← getLocalInstances).filter (·.fvar != mkFVar h)
    withLCtx lctx linsts do
    for strat in strats do
      let s ← saveState
      let (xs, _, H) ← forallMetaTelescopeReducing hty
      for x in xs do x.mvarId!.setKind .natural  -- instance binders come out synthetic
      let neg ← mkFreshExprMVar (mkNot H)
      let fuel ← IO.mkRef 400
      let failed ← IO.mkRef ({} : Std.HashSet Expr)
      if let some new ← runOn neg.mvarId! strat 400 then
        g'.assign (mkApp neg (mkAppN (mkFVar h) xs))
        if ← search (xs.toList.map (·.mvarId!) ++ new) fuel failed c then
          let v ← instantiateMVars (mkMVar g')
          unless or v.hasExprMVar v.hasSorry do
            replaceMainGoal []
            return
      s.restore
    throwError "refute_dep: no counterexample found"

end HcRefute

end
