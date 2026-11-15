/-
Lists every theorem that has at least one Prop-valued parameter (explicit, implicit, or
instance-implicit, e.g. `(h : 0 < n)`, `{h : p}`, `[NeZero n]`).

Usage:
  scripts/blean --run PropParams.lean [options]

Options:
  --import M           module to import and scan (repeatable; default: Init, Std).
                       Only theorems from modules with the same root as some `M` are reported.
  --ns N               only report theorems whose name has prefix `N` (repeatable)
  --instances          also report non-Prop instance parameters such as `[Add α]`
  --include-internal   also report auto-generated / private declarations
  --include-private    also report private theorems (not other internal names)  [batteries port]
  --text               human-readable output instead of JSON Lines
  -o FILE              write to FILE instead of stdout

JSON Lines output, one object per theorem:
  {"name", "module", "line", "params": [{"idx", "name", "binder", "prop", "dependent", "type"}]}
Batteries port (2026-11-09) adds: "private", "user_name" (privateToUserName), "has_pos" (declaration range
exists), "deprecated", "deprecated_to" (new name, if any), "alias_of" (the value is a bare constant).
`dependent` is true if a later parameter or the conclusion mentions the parameter, i.e. it
cannot simply be dropped from the statement.
-/
import Lean
open Lean Meta

structure Opts where
  imports : Array Name := #[]
  namespaces : Array Name := #[]
  instances : Bool := false
  internal : Bool := false
  priv : Bool := false
  text : Bool := false
  out? : Option System.FilePath := none

def parseArgs (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--import" :: m :: r => parseArgs { o with imports := o.imports.push m.toName } r
  | "--ns" :: n :: r => parseArgs { o with namespaces := o.namespaces.push n.toName } r
  | "--instances" :: r => parseArgs { o with instances := true } r
  | "--include-internal" :: r => parseArgs { o with internal := true } r
  | "--include-private" :: r => parseArgs { o with priv := true } r
  | "--text" :: r => parseArgs { o with text := true } r
  | "-o" :: f :: r => parseArgs { o with out? := some f } r
  | a :: _ => .error s!"unknown argument: {a}"

def binderStr : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

structure Param where
  idx : Nat
  name : Name
  binder : BinderInfo
  prop : Bool
  dependent : Bool
  type : String

def Param.toJson (p : Param) : Json :=
  Json.mkObj [("idx", p.idx), ("name", toString p.name), ("binder", binderStr p.binder),
    ("prop", p.prop), ("dependent", p.dependent), ("type", p.type)]

/-- Uses `forallTelescope` without reducing, so that e.g. `¬ p` is not unfolded to `p → False`. -/
def collectParams (o : Opts) (type : Expr) : MetaM (Array Param) :=
  forallTelescope type fun xs body => do
    let mut res := #[]
    for h : i in [:xs.size] do
      let fv := xs[i].fvarId!
      let d ← fv.getDecl
      let prop ← isProp d.type
      unless prop || (o.instances && d.binderInfo.isInstImplicit) do continue
      let laterDep ← (xs.extract (i+1) xs.size).anyM fun y => return (← inferType y).containsFVar fv
      res := res.push {
        idx := i, name := d.userName.eraseMacroScopes, binder := d.binderInfo, prop
        dependent := laterDep || body.containsFVar fv
        type := toString (← ppExpr d.type) }
    return res

def textLine (n : Name) (mod : Name) (line : Nat) (ps : Array Param) : String := Id.run do
  let mut s := s!"{n}  ({mod}:{line})\n"
  for p in ps do
    let tags := [binderStr p.binder] ++ (if p.prop then [] else ["non-Prop"]) ++
      (if p.dependent then ["dependent"] else [])
    s := s ++ s!"  #{p.idx} {p.name} : {p.type}  [{", ".intercalate tags}]\n"
  return s

unsafe def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs {} args with
    | .ok o => pure o
    | .error e => IO.eprintln e; return (1 : UInt32)
  let imports := if o.imports.isEmpty then #[`Init, `Std] else o.imports
  let roots := imports.map (·.getRoot)
  enableInitializersExecution
  -- Use the library belonging to the `lean` binary running this script, not the one on PATH.
  initSearchPath (← match (← IO.getEnv "LEAN_SYSROOT") with | some r => pure (r : System.FilePath) | none => getBuildDir)  -- batteries port
  let env ← importModules (imports.map ({ module := · })) {} (loadExts := true)
  let out ← match o.out? with
    | some f => pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk f .write))
    | none => IO.getStdout
  let ctx : Core.Context := { fileName := "<PropParams>", fileMap := default, maxHeartbeats := 0 }
  let act : MetaM (Nat × Nat × Nat) := do
    let mut nThms := 0
    let mut nHits := 0
    let mut nParams := 0
    for mod in env.header.moduleNames, data in env.header.moduleData do
      unless roots.contains mod.getRoot do continue
      for n in data.constNames do
        let some (.thmInfo ci) := env.find? n | continue
        let isPriv := isPrivateName n
        if !o.internal then
          if isPriv then
            unless o.priv do continue
            if (privateToUserName n).isInternalDetail then continue
          else if n.isInternalDetail then continue
        unless o.namespaces.isEmpty || o.namespaces.any (·.isPrefixOf n) do continue
        nThms := nThms + 1
        let ps ← collectParams o ci.type
        if ps.isEmpty then continue
        nHits := nHits + 1
        nParams := nParams + ps.size
        let rng ← findDeclarationRanges? n
        let line := rng.map (·.selectionRange.pos.line) |>.getD 0
        let depr := Linter.isDeprecated env n
        let deprTo := (Linter.getDeprecatedNewName env n).map toString
        let aliasOf : Option String := match ci.value.eta with
          | .const c _ => some (toString c)
          | _ => none
        let extra : List (String × Json) := [("private", isPriv),
          ("user_name", toString (privateToUserName n)), ("has_pos", rng.isSome),
          ("deprecated", depr), ("deprecated_to", match deprTo with | some t => Json.str t | none => Json.null),
          ("alias_of", match aliasOf with | some t => Json.str t | none => Json.null)]
        if o.text then
          out.putStr (textLine n mod line ps)
        else
          let base : List (String × Json) := [("name", toJson (toString n)),
            ("module", toJson (toString mod)), ("line", toJson line),
            ("params", Json.arr (ps.map Param.toJson))]
          out.putStrLn <| Json.compress <| Json.mkObj (base ++ extra)
    return (nThms, nHits, nParams)
  let ((nThms, nHits, nParams), _) ← act.run' {} |>.toIO ctx { env }
  out.flush
  IO.eprintln s!"scanned {nThms} theorems; {nHits} have matching parameters ({nParams} parameters total)"
  return 0
