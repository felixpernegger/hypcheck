import Lean

/-!
# SwapCheck: kernel-check certificates that hold after replacing an opaque constant by a value

Usage (via `scripts/swapcheck.sh CERT.lean`): `lean --run scripts/SwapCheck.lean OLEAN_DIR MODULE`.

A certificate module may declare *swap axioms* `axiom s : @c.{us} = v`, where `c` is an `opaque`
constant, `us` are the axiom's own universe parameters (distinct, in any order), and `v` is a
closed term. Its theorems may use these axioms.

The checker builds the dependency closure of all theorems and swap axioms of `MODULE`, with
* every swapped `c` turned into the definition `c := v`, and
* every swap axiom turned into the theorem `Eq.refl c` (valid because `c` now unfolds to `v`),
and replays that closure through the kernel into an empty environment. Any other axiom in the
closure must be `propext`, `Classical.choice` or `Quot.sound`.

Meaning of success: each theorem `t : S` of `MODULE` is provable in `E[c := v]`, the library
with the opaque `c` replaced by the definition `v`. Every proof valid in the library stays valid
there (the swap only adds the δ-rule `c ≡ v`), and `E[c := v]` is consistent whenever the library
is. So a certificate `t : ¬T'` shows `T'` unprovable, and `t : T'` shows `¬T'` unprovable
(relative to the three standard axioms; `Lean.ofReduceBool` is rejected).
-/

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

structure Swap where
  axiomName : Name
  target : Name
  /-- The new value of `target`, stated in `target`'s own universe parameters. -/
  value : Expr

def parseSwap (env : Environment) (ax : AxiomVal) : Except String Swap := do
  let some (_, lhs, rhs) := ax.type.eq? | throw s!"axiom {ax.name} is not an equation"
  let .const c us := lhs
    | throw s!"axiom {ax.name}: left side is not a bare constant (write `@c = v`)"
  let some (.opaqueInfo o) := env.find? c
    | throw s!"axiom {ax.name}: {c} is not an opaque constant"
  if o.isUnsafe then throw s!"axiom {ax.name}: {c} is unsafe"
  let ps ← us.mapM fun
    | .param p => pure p
    | _ => throw s!"axiom {ax.name}: universe arguments of {c} must be universe parameters"
  unless ps.eraseDups.length == ps.length && ps.length == ax.levelParams.length do
    throw s!"axiom {ax.name}: universe arguments of {c} must be exactly the axiom's parameters"
  if rhs.hasFVar || rhs.hasMVar then throw s!"axiom {ax.name}: value is not closed"
  return { axiomName := ax.name, target := c,
           value := rhs.instantiateLevelParams ps (o.levelParams.map .param) }

/-- Constants an expression needs in the kernel: constants, structures of projections, and the
constants that literals unfold to. Shared subterms are visited once. -/
def exprDeps (e : Expr) (s : NameSet) : NameSet :=
  ((go e).run ({}, s)).2.2
where
  go (e : Expr) : StateM (Std.HashSet Expr × NameSet) Unit := do
    if (← get).1.contains e then return
    modify fun (v, s) => (v.insert e, s)
    let add (n : Name) : StateM (Std.HashSet Expr × NameSet) Unit := modify fun (v, s) => (v, s.insert n)
    match e with
    | .const n _ => add n
    | .proj t _ b => add t; go b
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .lit (.strVal _) => add ``String.ofList; add ``Char.ofNat
    | .lit (.natVal _) => add ``Nat
    | _ => pure ()

def ciDeps (ci : ConstantInfo) : NameSet := Id.run do
  let mut s := exprDeps ci.type {}
  if let some v := ci.value? (allowOpaque := true) then s := exprDeps v s
  match ci with
  | .inductInfo i => for n in i.all ++ i.ctors do s := s.insert n
  | .ctorInfo c => s := s.insert c.induct
  | .recInfo r =>
    for n in r.all do s := s.insert n
    for rule in r.rules do s := exprDeps rule.rhs (s.insert rule.ctor)
  | _ => pure ()
  return s

/-- Constants that a declaration's *statement* depends on: types, definition values and inductive
structure, but not proofs or opaque values (which never unfold). -/
def statementDeps (ci : ConstantInfo) : NameSet := Id.run do
  let mut s := exprDeps ci.type {}
  match ci with
  | .defnInfo d => s := exprDeps d.value s
  | .inductInfo i => for n in i.all ++ i.ctors do s := s.insert n
  | .ctorInfo c => s := s.insert c.induct
  | .recInfo r => for n in r.all do s := s.insert n
  | _ => pure ()
  return s

unsafe def main (args : List String) : IO UInt32 := do
  let [dir, mod] := args
    | IO.eprintln "usage: lean --run SwapCheck.lean OLEAN_DIR MODULE"; return 2
  -- the sysroot of the running `lean`, not the one on PATH
  initSearchPath (← IO.appDir).parent.get! [dir]
  let modName := mod.toName
  enableInitializersExecution
  -- `Lake` is the reference library (Init, Std, Lean, Lake): its axioms are checked below
  let env ← importModules #[{ module := modName }, { module := `Lake }] {} (loadExts := true)
  let some modIdx := env.getModuleIdx? modName | IO.eprintln s!"module {modName} not found"; return 2
  let inMod (n : Name) := env.getModuleIdxFor? n == some modIdx
  -- swaps and roots
  let mut swaps : Array Swap := #[]
  let mut roots : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless inMod n do continue
    match ci with
    | .axiomInfo ax =>
      match parseSwap env ax with
      | .ok s => swaps := swaps.push s; roots := roots.push n
      | .error e => IO.eprintln s!"REJECTED: {e}"; return 1
    | .thmInfo _ => roots := roots.push n
    | _ => pure ()
  for s in swaps do
    if (swaps.filter (·.target == s.target)).size > 1 then
      IO.eprintln s!"REJECTED: more than one swap for {s.target}"; return 1
  -- Library axioms whose statement depends on a swapped constant (through types and definition
  -- values) would no longer be justified after the swap: the certificate must prove each such axiom
  -- `A` as the theorem `A.swapProof`, and `A` is replayed as that theorem.
  let targets := swaps.map (·.target)
  let mut axs : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if let .axiomInfo _ := ci then
      unless inMod n || allowedAxioms.contains n do axs := axs.push n
  let mut rev : Std.HashMap Name (Array Name) := {}
  let mut seen0 : NameSet := {}
  let mut todo0 := axs.toList
  while !todo0.isEmpty do
    let n := todo0.head!
    todo0 := todo0.tail!
    if seen0.contains n then continue
    seen0 := seen0.insert n
    let some ci := env.find? n | continue
    for d in statementDeps ci do
      rev := rev.insert d ((rev.getD d #[]).push n)
      unless seen0.contains d do todo0 := d :: todo0
  let mut reach : NameSet := {}
  let mut todo1 := targets.toList
  while !todo1.isEmpty do
    let n := todo1.head!
    todo1 := todo1.tail!
    if reach.contains n then continue
    reach := reach.insert n
    for m in rev.getD n #[] do todo1 := m :: todo1
  let mut reproved : Std.HashMap Name Name := {}
  let mut missing : Array Name := #[]
  for a in axs do
    unless reach.contains a do continue
    let p := a ++ `swapProof
    let some (.axiomInfo ax) := env.find? a | unreachable!
    match env.find? p with
    | some (.thmInfo t) =>
      unless inMod p && t.type == ax.type && t.levelParams == ax.levelParams do
        IO.eprintln s!"REJECTED: {p} must be a theorem of the certificate with the type of {a}"; return 1
      reproved := reproved.insert a p
    | _ => missing := missing.push a
  unless missing.isEmpty do
    IO.eprintln s!"REJECTED: {missing.size} library axioms depend on a swapped constant; prove each `A` as `A.swapProof`: {missing}"
    return 1
  IO.println s!"library axioms checked: {axs.size}; depending on a swap (re-proved): {reproved.toList.map (·.1)}"
  -- modified constant map
  let modified (n : Name) : Option ConstantInfo := do
    if let some s := swaps.find? (·.target == n) then
      let some (.opaqueInfo o) := env.find? n | none
      return .defnInfo { name := n, levelParams := o.levelParams, type := o.type, value := s.value,
                         hints := .opaque, safety := .safe, all := [n] }
    if let some s := swaps.find? (·.axiomName == n) then
      let some (.axiomInfo a) := env.find? n | none
      let some (ty, lhs, _) := a.type.eq? | none
      return .thmInfo { name := n, levelParams := a.levelParams, type := a.type,
                        value := mkApp2 (.const ``Eq.refl a.type.getAppFn.constLevels!) ty lhs,
                        all := [n] }
    if let some p := reproved[n]? then
      let some (.axiomInfo a) := env.find? n | none
      return .thmInfo { name := n, levelParams := a.levelParams, type := a.type,
                        value := .const p (a.levelParams.map .param), all := [n] }
    env.find? n
  -- closure
  let mut todo := roots.toList ++ [``Eq, ``Nat, ``String, ``String.ofList, ``Char.ofNat]
  let mut seen : NameSet := {}
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := modified n | IO.eprintln s!"REJECTED: unknown constant {n}"; return 1
    if let .axiomInfo _ := ci then
      unless allowedAxioms.contains n do
        IO.eprintln s!"REJECTED: closure uses axiom {n}"; return 1
    if ci.isUnsafe then IO.eprintln s!"REJECTED: closure uses unsafe {n}"; return 1
    newConsts := newConsts.insert n ci
    for d in ciDeps ci do
      unless seen.contains d do todo := d :: todo
  for s in swaps do
    unless seen.contains s.target do
      IO.eprintln s!"note: swap {s.axiomName} of {s.target} is not used"
  IO.println s!"closure: {newConsts.size} constants; swaps: {swaps.map (·.target)}"
  if let some p := (← IO.getEnv "SWAPCHECK_DUMP") then
    IO.FS.writeFile p (String.intercalate "\n" (newConsts.toList.map (toString ·.1)))
  -- replay into an empty environment
  let empty ← mkEmptyEnvironment
  let kenv ← try
      empty.toKernelEnv.replay newConsts
    catch e => IO.eprintln s!"KERNEL REJECTED: {e}"; return 1
  -- report the checked statements
  let ctx : Core.Context := { fileName := "<swapcheck>", fileMap := default }
  for n in roots do
    let some ci := kenv.find? n | IO.eprintln s!"missing after replay: {n}"; return 1
    let (fmt, _) ← (Meta.MetaM.run' (Meta.ppExpr ci.type)).toIO ctx { env }
    let kind := if swaps.any (·.axiomName == n) then "swap" else "theorem"
    IO.println s!"OK {kind} {n} : {fmt.pretty 100000}"
  return 0
