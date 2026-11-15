/-
HCRepair (hypkit v12): proof repair, shared by `HypCheck.lean` (the finder, `--level search|thorough`) and the
stored proofs that `scripts/repair_proofs.py` writes (`hc_repair% T i`). A module of its own, importing only Lean, so
that its source is never parsed inside a library that declares conflicting tokens (iris-lean: `>`, `||`).
Built by `scripts/build_tools.sh` (lake, for the tools) and compiled to `tools/hcrepair/HCRepair.olean` with the
library's `lean`; `scripts/hclean` puts that directory on the search path.

Proof repair: take the library's proof of `T` applied to the binders and remove the hypothesis `h` (binder `i`):
every subterm that mentions `h` is rebuilt from its children; where that fails, a Prop-typed subterm (whose type does
not mention `h`) is replaced by a proof found by cheap tactics in the local context at that point (with `h` erased),
bottom-up (the hole `h` itself first). Auxiliary theorems with internal names are inlined; as a last resort a library
theorem applied to `h` is unfolded and repaired inside (depth-limited). When `h` is an extra argument of a
recursor/`casesOn`/matcher (motive-generalized by `cases`/`induction`/`match`), the motive loses that premise and
every minor premise is rebuilt with `h` as a new hypothesis to eliminate. The caller kernel-checks the result.
-/
import Lean
open Lean Meta Elab Tactic

/-- Whether `v` reaches `sorry` through constants that are not in `env0` (auxiliary declarations a tactic
added, e.g. `match_k`/`proof_k`), transitively (v11.1). -/
partial def auxUsesSorry (env0 : Environment) (v : Expr) : CoreM Bool := do
  let env ← getEnv
  let rec go (todo : List Name) (seen : NameSet) : Bool :=
    match todo with
    | [] => false
    | c :: rest =>
      if seen.contains c || env0.contains c then go rest seen else
      match env.find? c with
      | none => go rest (seen.insert c)
      | some ci =>
        if ci.type.hasSorry || ci.value?.any (·.hasSorry) then true else
        let next := (ci.value?.map (·.getUsedConstants.toList)).getD [] ++ ci.type.getUsedConstants.toList
        go (next ++ rest) (seen.insert c)
  return go v.getUsedConstants.toList {}


structure RepSt where
  cache : Std.HashMap Expr (Option Expr) := {}
  tried : Nat := 0
  closed : Array String := #[]
  inlined : Nat := 0
  unfolded : Nat := 0
  surgeries : Nat := 0
  blocks : Std.HashMap String Nat := {}
  deadline : Nat := 0

abbrev RepM := StateRefT RepSt TermElabM

def closeHole (bad : Array FVarId) (ty : Expr) (tacs : Array (String × TSyntax `tactic)) (hb : Nat) :
    TermElabM (Option (String × Expr)) :=
  withErasedFVars bad do
    for (n, tac) in tacs do
      let s ← saveState
      let env0 ← getEnv
      let r ← withCurrHeartbeats <|
        withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
          tryCatchRuntimeEx (do
            Core.resetMessageLog
            let mvar ← mkFreshExprMVar ty
            let gs ← Tactic.run mvar.mvarId! (evalTactic tac)
            unless gs.isEmpty do return none
            if (← Core.getMessageLog).hasErrors then return none
            let v ← instantiateMVars mvar
            if v.hasSorry || v.hasMVar || bad.any v.containsFVar then return none
            if ← auxUsesSorry env0 v then return none
            return some v)
            (fun _ => return none)
      let env ← getEnv
      s.restore
      setEnv env
      if let some v := r then return some (n, v)
    return none

def repBlock (e : Expr) : RepM Unit := do
  let k := match e.getAppFn with
    | .const c _ => toString c
    | .fvar _ => "(fvar)"
    | .lam .. => "(lam)"
    | .letE .. => "(let)"
    | .proj s _ _ => s!"(proj {s})"
    | _ => "(other)"
  modify fun s => { s with blocks := s.blocks.insert k (s.blocks.getD k 0 + 1) }

/-- Motive position, first minor position, number of minors and arity of a recursor, `casesOn` or matcher
(repair v2). -/
def elimInfo? (c : Name) : MetaM (Option (Nat × Nat × Nat × Nat)) := do
  let env ← getEnv
  if let some mi ← getMatcherInfo? c then
    return some (mi.getMotivePos, mi.getFirstAltPos, mi.numAlts, mi.arity)
  if isCasesOnRecursor env c then
    let some (.inductInfo ii) := env.find? c.getPrefix | return none
    let first := ii.numParams + 1 + ii.numIndices + 1
    return some (ii.numParams, first, ii.ctors.length, first + ii.ctors.length)
  if let some (.recInfo ri) := env.find? c then
    if ri.numMotives != 1 then return none
    return some (ri.numParams, ri.numParams + 1, ri.numMinors, ri.getMajorIdx + 1)
  return none

/-- Pi telescope that only unfolds by `whnfCore` (beta, motive applications), not definitions. -/
partial def telescopeCore {α} (t : Expr) (k : Array Expr → Expr → RepM α) (acc : Array Expr := #[]) : RepM α := do
  match ← whnfCore t with
  | .forallE n d b bi => withLocalDecl n bi d fun y => telescopeCore (b.instantiate1 y) k (acc.push y)
  | t' => k acc t'

mutual
partial def repairE (bad : Array FVarId) (outer : Array FVarId) (tacs : Array (String × TSyntax `tactic))
    (hb maxHoles : Nat) (root : Bool) (e : Expr) (depth : Nat := 0) (maxDepth : Nat := 0) : RepM (Option Expr) := do
  if !bad.any e.containsFVar then return some e
  if let some r := (← get).cache.get? e then return r
  let go := fun e => repairE bad outer tacs hb maxHoles false e depth maxDepth
  let children : RepM (Option Expr) := do
    match e with
    | .fvar _ => return none
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      -- repair v2: `h` passed to a recursor/casesOn/matcher as an extra (motive-generalized) argument.
      if let .const c _ := f then
        if let some (mp, first, nm, arity) ← elimInfo? c then
          if args.size > arity && (args.extract arity args.size).any (fun a => bad.any a.containsFVar) then
            if let some r ← elimSurgery bad outer tacs hb maxHoles depth maxDepth f args mp first nm arity then
              modify fun s => { s with surgeries := s.surgeries + 1 }
              return some r
      if let .const c us := f then
        if c.isInternal && (← get).inlined < 200 then
          if let some (.thmInfo ti) := (← getEnv).find? c then
            modify fun s => { s with inlined := s.inlined + 1 }
            return ← go (mkAppN (ti.value.instantiateLevelParams ti.levelParams us) args).headBeta
      let some f' ← go f | return none
      let mut args' := #[]
      for a in args do
        let some a' ← go a | return none
        args' := args'.push a'
      return some (mkAppN f' args')
    | .lam n t b bi =>
      let some t' ← go t | return none
      withLocalDecl n bi t' fun x => do
        let some b' ← go (b.instantiate1 x) | return none
        return some (← mkLambdaFVars #[x] b')
    | .forallE n t b bi =>
      let some t' ← go t | return none
      withLocalDecl n bi t' fun x => do
        let some b' ← go (b.instantiate1 x) | return none
        return some (← mkForallFVars #[x] b')
    | .letE n t v b _ =>
      let some t' ← go t | return none
      let some v' ← go v | return none
      withLetDecl n t' v' fun x => do
        let some b' ← go (b.instantiate1 x) | return none
        return some (← mkLetFVars #[x] b')
    | .mdata d b => return (← go b).map (.mdata d)
    | .proj s i b => return (← go b).map (.proj s i ·)
    | _ => return none
  let r ← do
    if let some e' ← children then pure (some e') else
    if root then pure none else
    let st ← get
    if st.tried ≥ maxHoles || (← IO.monoMsNow) > st.deadline then pure none else
    let ty? ← try some <$> (instantiateMVars (← inferType e)) catch _ => pure none
    match ty? with
    | none => pure none
    | some ty =>
      if bad.any ty.containsFVar then repBlock e; pure none else
      if !(← try isProp ty catch _ => pure false) then repBlock e; pure none else
      modify fun s => { s with tried := s.tried + 1 }
      match ← closeHole bad ty tacs hb with
      | some (n, v) =>
        modify fun s => { s with closed := s.closed.push n }
        pure (some v)
      | none => repBlock e; pure none
  -- Last resort: unfold a library theorem applied to (something containing) `h` and repair inside its proof.
  let r ← if r.isSome || depth ≥ maxDepth then pure r else do
    match e.getAppFn with
    | .const c us =>
      if (← get).unfolded ≥ 30 || (← IO.monoMsNow) > (← get).deadline then pure none else
      match (← getEnv).find? c with
      | some (.thmInfo ti) =>
        modify fun s => { s with unfolded := s.unfolded + 1 }
        repairE bad outer tacs hb maxHoles root
          (mkAppN (ti.value.instantiateLevelParams ti.levelParams us) e.getAppArgs).headBeta (depth + 1) maxDepth
      | _ => pure none
    | _ => pure none
  -- Cache failures always; successes only if they use no local beyond those of `e` and the outer binders
  -- (a hole proof may use hypotheses in scope at this occurrence only).
  let keep ← match r with
    | none => pure true
    | some v => do
      let (_, fs) ← v.collectFVars.run {}
      let (_, fe) ← e.collectFVars.run {}
      pure (fs.fvarIds.all fun f => fe.fvarSet.contains f || outer.contains f)
  if keep then modify fun s => { s with cache := s.cache.insert e r }
  return r

/-- Old minor premise applied to the binders `ys` of the new minor type (motive without the dropped premise):
binders are matched in order by definitional equality; an induction hypothesis `H → X` of the old motive is
fed `fun _ => ih`; the dropped premise becomes a fresh hypothesis that repair must eliminate as well. -/
partial def surgeryWalk (bad outer : Array FVarId) (tacs : Array (String × TSyntax `tactic)) (hb maxHoles depth maxDepth : Nat)
    (oldMinor : Expr) (ys : Array Expr) (cur : Expr) (ptr : Nat) (acc : Array Expr) (newBad : Array FVarId) :
    RepM (Option Expr) := do
  match ← whnfCore cur with
  | .forallE n dom body _ =>
    if h : ptr < ys.size then
      let yT ← inferType ys[ptr]
      if ← isDefEq dom yT then
        return ← surgeryWalk bad outer tacs hb maxHoles depth maxDepth oldMinor ys (body.instantiate1 ys[ptr])
          (ptr + 1) (acc.push ys[ptr]) newBad
      if let .forallE _ hd hbody _ ← whnfCore dom then
        if !hbody.hasLooseBVars && (← isDefEq hbody yT) then
          let lam := Expr.lam `_ hd ys[ptr] .default
          return ← surgeryWalk bad outer tacs hb maxHoles depth maxDepth oldMinor ys (body.instantiate1 lam)
            (ptr + 1) (acc.push lam) newBad
    if newBad.isEmpty && (← isProp dom) then
      return ← withLocalDeclD n dom fun h' =>
        surgeryWalk bad outer tacs hb maxHoles depth maxDepth oldMinor ys (body.instantiate1 h') ptr (acc.push h')
          (newBad.push h'.fvarId!)
    return none
  | _ =>
    if ptr != ys.size then return none
    let t := (mkAppN oldMinor acc).headBeta
    let some t' ← repairE (bad ++ newBad) outer tacs hb maxHoles false t depth maxDepth | return none
    if newBad.any t'.containsFVar then return none
    return some (← mkLambdaFVars ys t')

/-- Rebuild `f args` (an eliminator applied beyond its arity, with `h` among the extra arguments) with the
motive `fun is => (ps…) → B` minus the premise fed by `h`, and every minor premise rebuilt by `surgeryWalk`. -/
partial def elimSurgery (bad outer : Array FVarId) (tacs : Array (String × TSyntax `tactic)) (hb maxHoles depth maxDepth : Nat)
    (f : Expr) (args : Array Expr) (mp first nMinors arity : Nat) : RepM (Option Expr) := do
  let go := fun e => repairE bad outer tacs hb maxHoles false e depth maxDepth
  let extra := args.extract arity args.size
  let some p := extra.findIdx? (fun a => bad.any a.containsFVar) | return none
  let some motive := args[mp]? | return none
  let newMotive? ← lambdaTelescope motive fun is mb => do
    forallBoundedTelescope mb extra.size fun ps B => do
      if ps.size != extra.size then return none
      let some x := ps[p]? | return none
      let rest := ps.eraseIdxIfInBounds p
      if B.containsFVar x.fvarId! then return none
      for r in rest do
        if (← inferType r).containsFVar x.fvarId! then return none
      return some (← mkLambdaFVars is (← mkForallFVars rest B))
  let some newMotive := newMotive? | return none
  let fty ← inferType f
  let mut newArgs := args.set! mp newMotive
  for k in [:arity] do
    if k == mp then continue
    if first ≤ k && k < first + nMinors then
      let t ← instantiateForall fty (newArgs.extract 0 k)
      let .forallE _ d _ _ ← whnfCore t | return none
      let old := args[k]!
      let oldTy ← inferType old
      let r ← telescopeCore d fun ys _ =>
        surgeryWalk bad outer tacs hb maxHoles depth maxDepth old ys oldTy 0 #[] #[]
      let some m' := r | return none
      newArgs := newArgs.set! k m'
    else
      let some a' ← go args[k]! | return none
      newArgs := newArgs.set! k a'
  let mut extra' := #[]
  for h : i in [:extra.size] do
    if i == p then continue
    let some a' ← go extra[i] | return none
    extra' := extra'.push a'
  return some (mkAppN f ((newArgs.extract 0 arity) ++ extra'))
end

/-- Tactics from source (Mathlib syntax may be unknown here); unparsable ones are skipped. -/
def hcParsedTacs (srcs : List (String × String)) : TermElabM (Array (String × TSyntax `tactic)) := do
  let mut out := #[]
  for (n, src) in srcs do
    match Parser.runParserCategory (← getEnv) `tactic src with
    | .ok stx => out := out.push (n, ⟨stx⟩)
    | .error _ => pure ()
  return out

open Term in
/-- `T'`: the statement of `T` without binder `i` (fresh universe levels, generalized by the declaration). -/
elab "hc_drop_type% " id:ident i:num : term => do
  let ci ← getConstInfo id.getId
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body =>
    mkForallFVars (xs.eraseIdxIfInBounds i.getNat) body

open Term in
elab "hc_repair% " id:ident i:num : term <= expectedType => do
  let n := id.getId
  let ci ← getConstInfo n
  let .thmInfo ti := ci | throwError "{n} is not a theorem"
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let k := i.getNat
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let some x := xs[k]? | throwError "{n} has no binder {k}"
    let rest := xs.eraseIdxIfInBounds k
    let tp ← mkForallFVars rest body
    unless ← isDefEq tp expectedType do
      throwError "{n} without binder {k} is{indentExpr tp}\nnot the stated type{indentExpr expectedType}"
    let pf ← instantiateMVars (mkAppN (ti.value.instantiateLevelParams ci.levelParams us) xs).headBeta
    let holeTacs ← hcParsedTacs [("infer_instance", "(intros; infer_instance)"), ("assumption", "assumption"), ("trivial", "(intros; trivial)"),
      ("omega", "(intros; omega)"), ("simp_all", "(intros; simp_all; done)"),
      ("solve_by_elim", "(intros; solve_by_elim)"), ("grind", "(intros; grind)")]
    let (r?, _) ← (repairE #[x.fvarId!] (rest.map (·.fvarId!)) holeTacs 600 120 true pf 0 3).run
      { deadline := 1 <<< 62 }
    let some v := r? | throwError "proof repair failed for {n} binder {k}"
    if v.containsFVar x.fvarId! then throwError "binder {k} of {n} still occurs after repair"
    instantiateMVars (← mkLambdaFVars rest v)
