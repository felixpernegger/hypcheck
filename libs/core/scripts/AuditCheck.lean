/-
Proof audit checker (appended by `scripts/audit_proofs.py` to a copy of each proof file; not a module).

`#eval HypAudit.run "SPEC.json" "OUT.jsonl"` inspects every theorem the kernel accepted in this file
(`env.constants.map₂` of the kernel environment, so declarations that failed to elaborate are absent)
and writes one JSON line per theorem:
  {"d": decl, "ax": [axioms], "m": [[T, i, pol, kind], …], "chain": …, "to": timeouts}
* `m`: original theorems `T` and binders `i` such that the statement is definitionally
  `T'ᵢ` (pol "removable") or `¬T'ᵢ` (pol "necessary"). kind "plain" = `T` without binder `i`;
  for a dependent binder, "full" = `∀ indep, Hᵢ` over all binders except `i` and those depending on it,
  "narrow" = only the binders `Hᵢ` mentions (closed under types). A positive statement must keep the
  declaration's own universe parameters, each universe of `T` mapped to a distinct one (as `check_hand.py`).
* `chain` (declarations `HypCheckChain.A.h<i>` with a spec entry): "nec" = statement is
  `A'ᵢ → R'ₖ … → B'ⱼ` (B' at the declaration's own, distinct universe parameters), "twin" =
  `T'ᵢ ↔ S'ᵢ` (both sides at distinct own parameters); `ok` says whether every part matched.
Candidates `T` per declaration: the spec's list for that name, plus `T` read off names
`HypCheckProof.T.h<i>…` / `HypCheckChain.T.h<i>` / `HypCheckDrop.T.h<i>`. Spec rows not matched by a
candidate are then tried against every local theorem that matched nothing ("fallback").
Each definitional-equality test runs under its own heartbeat limit; a timeout counts as no match.
-/
section HypAudit
open Lean Meta Elab Command

namespace HypAudit

def mkName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => if !c.isEmpty && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous

/-- Name with all-digit string components turned into numeric ones (`«0»` in private names). -/
def normName : Name → Name
  | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (normName p) s.toNat! else .str (normName p) s
  | .num p k => .num (normName p) k
  | .anonymous => .anonymous

abbrev Variants := List Level × Array (Nat × String × Expr)

/-- All `(i, kind, T'ᵢ)` of `T`, with fresh level metavariables for `T`'s universes. -/
def variants (T : Name) : MetaM Variants := do
  let ci ← getConstInfo T
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let ty := ci.type.instantiateLevelParams ci.levelParams us
  return (us, ← forallTelescope ty fun xs body => do
    let mut out := #[]
    for i in [:xs.size] do
      let x := xs[i]!
      unless ← isProp (← inferType x) do continue
      let mut dep : Array Expr := #[x]
      for j in [i+1:xs.size] do
        let t ← inferType xs[j]!
        if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
      let rest := xs.filter (fun y => !dep.contains y)
      if dep.size > 1 || body.containsFVar x.fvarId! then
        let hx ← inferType x
        out := out.push (i, "full", ← mkForallFVars rest hx)
        let used := rest.filter fun y => hx.containsFVar y.fvarId!
        let mut cl := used
        for y in rest.reverse do
          if cl.contains y then
            let ty ← inferType y
            for z in rest do
              if ty.containsFVar z.fvarId! && !cl.contains z then cl := cl.push z
        let clOrd := rest.filter (cl.contains ·)
        if clOrd.size < rest.size then
          out := out.push (i, "narrow", ← mkForallFVars clOrd hx)
      else
        out := out.push (i, "plain", ← mkForallFVars rest body)
    return out)

structure St where
  cache : Std.HashMap Name (Option Variants) := {}
  timeouts : Nat := 0

abbrev M := StateRefT St MetaM

def getVariants (T : Name) : M (Option Variants) := do
  if let some v := (← get).cache[T]? then return v
  let v ← if (← getEnv).contains T then
      (try some <$> variants T catch _ => pure none) else pure none
  modify fun s => { s with cache := s.cache.insert T v }
  return v

/-- `S =?= t`; with `strict`, `T`'s universes must become distinct universe parameters. -/
def test (S : Expr) (us : List Level) (t : Expr) (strict : Bool) : M Bool := do
  let r ← tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000 }) <|
      (withoutModifyingState <| withNewMCtxDepth (allowLevelAssignments := true) do
        unless ← isDefEq S t do return some false
        if !strict then return some true
        let ls ← us.mapM instantiateLevelMVars
        return some (ls.all (·.isParam) && ls.eraseDups.length == ls.length) : MetaM (Option Bool)))
    (fun _ => pure none)
  match r with
  | some b => return b
  | none => modify (fun s => { s with timeouts := s.timeouts + 1 }); return false

/-- Matches of statement `S` (positive part; `neg` = it was `¬S`) against candidate `T`. -/
def matchCand (S : Expr) (neg : Bool) (T : Name) (only : Option Nat := none) : M (Array Json) := do
  let some (us, vs) ← getVariants T | return #[]
  let mut out := #[]
  for (i, kind, t) in vs do
    if let some k := only then unless k == i do continue
    if ← test S us t (!neg) then
      out := out.push (Json.arr #[toJson T.toString, toJson i, toJson (if neg then "necessary" else "removable"), toJson kind])
  return out

/-- The plain variant `T'ᵢ` of `T` (non-dependent binder), if any. -/
def plainVar (T : Name) (i : Nat) : M (Option (List Level × Expr)) := do
  let some (us, vs) ← getVariants T | return none
  return vs.findSome? fun (j, kind, t) => if j == i && kind == "plain" then some (us, t) else none

def testPlain (S : Expr) (T : Name) (i : Nat) (strict : Bool) : M Bool := do
  let some (us, t) ← plainVar T i | return false
  test S us t strict

/-- Name-derived candidate: `HypCheckProof.T.h<i>…` ↦ `T`. -/
def nameCand (d : Name) : Option Name :=
  let cs := d.components
  match cs.head? with
  | some r =>
    if r == `HypCheckProof || r == `HypCheckChain || r == `HypCheckDrop then
      let rest := cs.tail
      let isH (c : Name) := match c with
        | .str .anonymous s => s.length > 1 && s.front == 'h' && (s.drop 1).all Char.isDigit
        | _ => false
      match rest.zipIdx.reverse.find? (fun (c, _) => isH c) with
      | some (_, k) => some (rest.take k |>.foldl (fun n c => n ++ c) .anonymous)
      | none => none
    else none
  | none => none

def jPair (T : String) (i : Nat) : Json := Json.arr #[toJson T, toJson i]

/-- Check a chain declaration against its claimed structure. -/
def checkChain (d : Name) (ty : Expr) (spec : Json) : M Json := do
  let kind := (spec.getObjValAs? String "kind").toOption.getD ""
  let getP (k : String) : Option (String × Nat) := do
    let a ← (spec.getObjVal? k).toOption
    let t ← (a.getArrVal? 0 >>= (·.getStr?)).toOption
    let i ← (a.getArrVal? 1 >>= (·.getNat?)).toOption
    return (t, i)
  let some (A, i) := getP "a" | return Json.mkObj [("ok", toJson false), ("why", toJson "bad spec")]
  let some (B, j) := getP "b" | return Json.mkObj [("ok", toJson false), ("why", toJson "bad spec")]
  let rs : Array (String × Nat) := match spec.getObjVal? "rs" with
    | .ok (.arr xs) => xs.filterMap fun x => do
        let t ← (x.getArrVal? 0 >>= (·.getStr?)).toOption
        let k ← (x.getArrVal? 1 >>= (·.getNat?)).toOption
        return (t, k)
    | _ => #[]
  let base := [("kind", toJson kind), ("a", jPair A i), ("b", jPair B j),
               ("rs", Json.arr (rs.map fun (t, k) => jPair t k))]
  if kind == "twin" then
    let some (l, r) := ty.iff? | return Json.mkObj (base ++ [("ok", toJson false), ("why", toJson "not an iff")])
    let ok ← testPlain l (mkName A) i true <&&> testPlain r (mkName B) j true
    return Json.mkObj (base ++ [("ok", toJson ok)])
  -- nec: peel 1 + |rs| non-dependent premises
  let mut t := ty
  let mut prem := #[]
  for _ in [:1 + rs.size] do
    match t with
    | .forallE _ dom b _ =>
      if b.hasLooseBVars then return Json.mkObj (base ++ [("ok", toJson false), ("why", toJson "dependent premise")])
      prem := prem.push dom; t := b
    | _ => return Json.mkObj (base ++ [("ok", toJson false), ("why", toJson "too few premises")])
  let mut ok ← testPlain prem[0]! (mkName A) i false
  for (R, k) in rs, p in prem.extract 1 prem.size do
    ok := ok && (← testPlain p (mkName R) k false)
  ok := ok && (← testPlain t (mkName B) j true)
  return Json.mkObj (base ++ [("ok", toJson ok)])

def run (specPath outPath : String) : CommandElabM Unit := liftTermElabM do
  let spec ← match Json.parse (← IO.FS.readFile specPath) with
    | .ok j => pure j
    | .error e => throwError "spec: {e}"
  let candMap : Std.HashMap Name (Array Name) := match spec.getObjVal? "cands" with
    | .ok (.obj kvs) => kvs.foldl (init := {}) fun m k v => m.insert (mkName k) (match v with
        | .arr xs => xs.filterMap fun x => (x.getStr?.toOption.map mkName)
        | _ => #[])
    | _ => {}
  let chainMap : Std.HashMap Name Json := match spec.getObjVal? "chains" with
    | .ok (.obj kvs) => kvs.foldl (init := {}) fun m k v => m.insert (mkName k) v
    | _ => {}
  let rows : Array (Name × Nat × Bool) := match spec.getObjVal? "rows" with
    | .ok (.arr xs) => xs.filterMap fun x => do
        let t ← (x.getArrVal? 0 >>= (·.getStr?)).toOption
        let i ← (x.getArrVal? 1 >>= (·.getNat?)).toOption
        let p ← (x.getArrVal? 2 >>= (·.getStr?)).toOption
        return (mkName t, i, p == "necessary")
    | _ => #[]
  let env ← getEnv
  let kenv := env.toKernelEnv
  -- (constant info taken from the kernel map itself: on-demand constants such as private
  -- `match_1.eq_1` lemmas are there but not always visible to `getConstInfo`)
  let locals := kenv.constants.map₂.toList.filterMap fun (n, ci) =>
    match ci with
    | .thmInfo _ => if (`HypAudit).isPrefixOf n then none else some (n, ci)
    | _ => none
  let locals := locals.toArray.qsort (fun a b => Name.lt a.1 b.1)
  let act : M (Array Json) := do
    let mut recs : Array Json := #[]
    let mut unmatched : Array (Name × Expr × Bool) := #[]
    let mut covered : Std.HashSet (Name × Nat × Bool) := {}
    for (d, ci) in locals do
     try
      let ty := ci.type
      let (S, neg) := match ty.not? with | some s => (s, true) | none => (ty, false)
      let dn := normName d
      let mut cands := (candMap[dn]?.getD #[]) ++ (candMap[normName (privateToUserName d)]?.getD #[])
      if let some c := nameCand dn then
        cands := cands.push c
        unless env.contains c do cands := cands.push (mkPrivateName env c)
      let mut ms := #[]
      for T in cands.toList.eraseDups do
        ms := ms ++ (← matchCand S neg T)
      let mut chainJ := Json.null
      if let some cs := chainMap[dn]? then
        chainJ ← checkChain d ty cs
      for m in ms do
        if let (Except.ok t, Except.ok i) := ((m.getArrVal? 0 >>= (·.getStr?) : Except String String),
            (m.getArrVal? 1 >>= (·.getNat?) : Except String Nat)) then
          covered := covered.insert (mkName t, i, neg)
      if ms.isEmpty && chainJ.isNull then unmatched := unmatched.push (d, S, neg)
      let ax ← collectAxioms d
      recs := recs.push <| Json.mkObj [("d", toJson d.toString), ("ax", toJson (ax.map (·.toString))),
        ("m", Json.arr ms), ("chain", chainJ)]
     catch e =>
      let ax ← try (do let a ← collectAxioms (m := MetaM) d; pure (a.map (·.toString)))
        catch _ => pure #["<axioms unavailable>"]
      recs := recs.push <| Json.mkObj [("d", toJson d.toString), ("ax", toJson ax), ("m", Json.arr #[]),
        ("chain", Json.null), ("err", toJson (← e.toMessageData.toString))]
    -- fallback: uncovered rows against declarations that matched nothing
    let mut fb : Array Json := #[]
    for (T, i, neg) in rows do
      if covered.contains (T, i, neg) then continue
      for (d, S, n) in unmatched do
        unless n == neg do continue
        let ms ← matchCand S neg T (only := some i)
        if !ms.isEmpty then
          covered := covered.insert (T, i, neg)
          fb := fb.push <| Json.mkObj [("d", toJson d.toString), ("m", Json.arr ms)]
          break
    recs := recs.push <| Json.mkObj [("fallback", Json.arr fb), ("timeouts", toJson (← get).timeouts),
      ("nlocal", toJson locals.size)]
    return recs
  let recs ← act.run' {}
  IO.FS.writeFile outPath (String.intercalate "\n" (recs.map (·.compress)).toList ++ "\n")

end HypAudit
end HypAudit
