/-
[HypCheck v12.3: CSLib port v11.1 plus the changes from a benchmark of the mechanical checks;
version history in tool/PLAYBOOK.md "Tool version".]
For every Prop-valued parameter `hᵢ : Hᵢ` of the selected theorems `T : ∀ xs, C`, decide mechanically
whether it can be removed. Let `T'` be `T` without `hᵢ`.

* removable:  `∀ rest, ¬Hᵢ → C` is proved by a cheap tactic; with `T` and `Classical.byCases` this
              yields `T'`. `derivable` additionally records whether `Hᵢ` follows from the other binders.
* necessary:  `¬T'` is proved by instantiating the data variables with small values (numbers,
              bit vectors, `Fin`, lists, ...; type variables become `Nat`/`Bool`, or with class
              constraints `Nat` does not meet, a fitting type from a small pool and the instance index;
              library types get constructor values (depth ≤ 2) or `0`/`1`/`2`/`∅`/`⊥`/`⊤`/`default`).
* unresolved: neither succeeded.

If `hᵢ` occurs in a later binder or in `C` ("dependent"), it can only be removed by substituting a
proof derived from the binders that do not depend on it. Then `removable` means that
`∀ indep, Hᵢ` was proved (and the restated theorem checked), `necessary` that `¬∀ indep, Hᵢ` was
proved by a counterexample. These results carry `"dependent": true`.

Every removable/necessary verdict is backed by a proof of `T'` resp. `¬T'` accepted by the kernel.
With `--proofs FILE` each verdict is also written to `FILE` as Lean source (the tactic and the
witness values, not the proof term), which is elaborated once more right away against the imported
environment; the JSON records the declaration name (`proof`) and whether that check passed
(`proof_ok`, else `proof_error`). Blocks that fail are kept in the file as comments.

Levels (v12): `--level fast` (default): the cheap removal pool (`assumption`, `trivial`, `infer_instance`, `rfl`,
`contradiction`, `decide`, `solve_by_elim`, `simp`, `lia` (else `omega`), `simp_all`, `grind`, and Mathlib's
`tauto`/`linarith`/`positivity`/`norm_num` where they parse). `--level search`: also `exact?`, and proof repair for
non-dependent rows (the library proof of `T` with the uses of `hᵢ` replaced by proofs found in the local context
there, kernel-checked; status removable with `tactic: repair` and no stored proof here: `scripts/repair_proofs.py`
writes and checks those). `--level thorough`: deeper repair. `--goal removable` (= `--no-cex`) skips the
counterexample search; `--goal both` (default) runs it.
Measurement options (benchmark): `--matrix` (every removal tactic separately, timed), `--tacs FILE` (replace the
pool by `name := tactic` lines), `--first` (matrix: stop at the first success), `--repair` (matrix: add repair).

`--recheck FILE` only runs the counterexample search, and only for the (theorem, idx) pairs listed
in `FILE` (e.g. the unresolved results of an earlier run).

Usage:
  scripts/hcrun hypcheck [--import M]... [--module M]... [--ns N]... [--shard k/N]
      [--models FILE] [--claim-dir D] [--skip RESULTS.jsonl] [--only-dependent] [--include-internal] [--include-private] [--only-private] [--recheck RESULTS.jsonl] [--redo RESULTS.jsonl] [--hb N] [--cex-hb N] [--cex-cap N] [--cex-time SECONDS] [--proofs FILE.lean] [--level fast|search|thorough] [--no-exact] [--olean-level private|server] [--goal both|removable] [-o FILE]
Defaults: --import = roots of the --module arguments, --module Init.Data.Nat, --hb 5000, --cex-hb 300, --cex-cap 1500 (heartbeats in thousands).
Output: JSON Lines, one object per Prop parameter.
Parallel runs: use `run.sh`, which starts worker processes that share a `--claim-dir`.
-/
import Lean
import HCRepair
open Lean Meta Elab Tactic

structure Opts where
  modules : Array Name := #[]
  imports : Array Name := #[]
  namespaces : Array Name := #[]
  shard : Nat := 0
  shards : Nat := 1
  hb : Nat := 5000
  matrix : Bool := false
  tacs? : Option System.FilePath := none
  noCex : Bool := false
  first : Bool := false
  /-- v12: 0 fast, 1 search (+ `exact?`, proof repair), 2 thorough (deeper repair). -/
  level : Nat := 0
  /-- `--no-exact`: leave `exact?` out of the search-level removal pool (it is the slowest pool tactic). -/
  noExact : Bool := false
  /-- `--olean-level`: module-system import level. Below `private` (`server`), module-system libraries load
  without proofs (theorems as axioms, much less memory), so proof repair is off (`noProofs`). -/
  oleanLevel : OLeanLevel := .private
  noProofs : Bool := false
  repair : Bool := false
  repairHb : Nat := 300
  repairHoles : Nat := 60
  repairTimeMs : Nat := 15000
  repairDepth : Nat := 2
  cexHb : Nat := 300
  cexCap : Nat := 1500
  cexTimeMs : Nat := 60000
  claimDir? : Option System.FilePath := none
  skip? : Option System.FilePath := none
  onlyDependent : Bool := false
  includeInternal : Bool := false
  includePrivate : Bool := false
  onlyPrivate : Bool := false
  recheck? : Option System.FilePath := none
  /-- With `--recheck FILE`: also retry removal, and seed the search with the recorded witnesses. -/
  redo : Bool := false
  models? : Option System.FilePath := none
  /-- `--extra-tacs FILE` (v12.3): library tactics, lines `remove|cex|prem NAME := TACTIC`, appended to the
  removal pool, the counterexample closers or the premise closers (`tool/hypcheck` passes
  `scripts/tactics_<name>.txt` when it exists). -/
  extraTacs? : Option System.FilePath := none
  out? : Option System.FilePath := none
  proofs? : Option System.FilePath := none

def parseArgs (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--import" :: m :: r => parseArgs { o with imports := o.imports.push m.toName } r
  | "--module" :: m :: r => parseArgs { o with modules := o.modules.push m.toName } r
  | "--ns" :: n :: r => parseArgs { o with namespaces := o.namespaces.push n.toName } r
  | "--shard" :: s :: r => match s.splitOn "/" with
    | [k, n] => match k.toNat?, n.toNat? with
      | some k, some n => parseArgs { o with shard := k, shards := n } r
      | _, _ => .error s!"bad --shard {s}"
    | _ => .error s!"bad --shard {s}"
  | "--recheck" :: f :: r => parseArgs { o with recheck? := some f } r
  | "--redo" :: f :: r => parseArgs { o with recheck? := some f, redo := true } r
  | "--models" :: f :: r => parseArgs { o with models? := some f } r
  | "--extra-tacs" :: f :: r => parseArgs { o with extraTacs? := some f } r
  | "--only-private" :: r => parseArgs { o with includePrivate := true, onlyPrivate := true } r
  | "--include-private" :: r => parseArgs { o with includePrivate := true } r
  | "--include-internal" :: r => parseArgs { o with includeInternal := true } r
  | "--only-dependent" :: r => parseArgs { o with onlyDependent := true } r
  | "--skip" :: f :: r => parseArgs { o with skip? := some f } r
  | "--claim-dir" :: d :: r => parseArgs { o with claimDir? := some d } r
  | "--no-cex" :: r => parseArgs { o with noCex := true } r
  | "--first" :: r => parseArgs { o with first := true } r
  | "--no-exact" :: r => parseArgs { o with noExact := true } r
  | "--olean-level" :: l :: r => match l with
    | "private" => parseArgs { o with oleanLevel := .private } r
    | "server" => parseArgs { o with oleanLevel := .server } r
    | _ => throw s!"--olean-level: private or server, not {l}"
  | "--level" :: l :: r => match l with
    | "fast" => parseArgs { o with level := 0 } r
    | "search" => parseArgs { o with level := 1 } r
    | "thorough" => parseArgs { o with level := 2 } r
    | _ => throw s!"--level: fast, search or thorough, not {l}"
  | "--goal" :: g :: r => match g with
    | "both" => parseArgs { o with noCex := false } r
    | "removable" => parseArgs { o with noCex := true } r
    | _ => throw s!"--goal: both or removable, not {g}"
  | "--repair-depth" :: n :: r => parseArgs { o with repairDepth := n.toNat! } r
  | "--repair" :: r => parseArgs { o with repair := true } r
  | "--repair-hb" :: n :: r => parseArgs { o with repairHb := n.toNat! } r
  | "--repair-holes" :: n :: r => parseArgs { o with repairHoles := n.toNat! } r
  | "--repair-time" :: n :: r => parseArgs { o with repairTimeMs := n.toNat! * 1000 } r
  | "--tacs" :: f :: r => parseArgs { o with tacs? := some f } r
  | "--matrix" :: r => parseArgs { o with matrix := true } r
  | "--hb" :: n :: r => parseArgs { o with hb := n.toNat! } r
  | "--cex-hb" :: n :: r => parseArgs { o with cexHb := n.toNat! } r
  | "--cex-cap" :: n :: r => parseArgs { o with cexCap := n.toNat! } r
  | "--cex-time" :: n :: r => parseArgs { o with cexTimeMs := n.toNat! * 1000 } r
  | "-o" :: f :: r => parseArgs { o with out? := some f } r
  | "--proofs" :: f :: r => parseArgs { o with proofs? := some f } r
  | a :: _ => .error s!"unknown argument: {a}"

def binderStr : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"


/-- Runs `tac` on the closed goal `goal` in an empty local context, so it cannot see the binders of
the telescope we are working in. Timeouts count as failure. The environment is kept on success
because tactics may add auxiliary declarations that the proof refers to. -/
def proveWith (goal : Expr) (tac : TSyntax `tactic) (hb : Nat) : TermElabM (Option Expr) :=
  withLCtx {} {} do
    let s ← saveState
    let env0 ← getEnv
    let r ← withCurrHeartbeats <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
        tryCatchRuntimeEx (do
          -- v11.1 (CSLib): term-elaborating tactics (`nofun`, `exact`, `aesop`) may *log* an error and
          -- recover with `sorry`, e.g. inside an auxiliary `match_k` declaration that `v` only names.
          -- Count any logged error as failure, and require auxiliary constants to be sorry-free.
          Core.resetMessageLog
          let mvar ← mkFreshExprMVar goal
          let gs ← Tactic.run mvar.mvarId! (evalTactic tac)
          unless gs.isEmpty do return none
          if (← Core.getMessageLog).hasErrors then return none
          let v ← instantiateMVars mvar
          if v.hasSorry || v.hasMVar || v.hasFVar then return none
          if ← auxUsesSorry env0 v then return none
          return some v)
          (fun _ => return none)
    let env ← getEnv
    s.restore
    setEnv env
    return r

def firstProof (goal : Expr) (tacs : Array (String × TSyntax `tactic)) (hb : Nat) :
    TermElabM (Option (String × Expr)) := do
  for (n, t) in tacs do
    if let some p ← proveWith goal t hb then return some (n, p)
  return none

def kernelAccepts (lps : List Name) (type value : Expr) : CoreM Bool :=
  withoutModifyingEnv do
    tryCatchRuntimeEx
      (do addDecl <| .thmDecl { name := `_hypCheck_tmp, levelParams := lps, type, value }; return true)
      (fun _ => return false)

/-! ### Proof repair (bench, `--repair`)

Take the library's own proof of `T`, applied to the binders, and remove the hypothesis `h` from it: every
subterm that mentions `h` is rebuilt from its children; where that fails, a Prop-typed subterm (whose type does
not mention `h`) is replaced by a proof found by cheap tactics in the local context at that point (with `h`
erased). Bottom-up: the hole `h` itself first (its statement may be derivable from facts in scope there), then
larger enclosing proofs. Auxiliary theorems with internal names (`_proof_k`, `_simp_k`, ...) are inlined. The
result is kernel-checked against `T'` by the caller. -/


/-! ### Proofs as Lean source (`--proofs`) -/

/-- A verdict's proof as Lean commands, in alternative renderings that are tried in order (readable,
then fully explicit). `expect` lists the declarations it defines together with the statement each
must have, which is compared after elaborating the source. -/
structure ProofBlock where
  decl : Name
  srcs : Array String
  expect : Array (Name × Expr)
  /-- Further renderings with their own expected statements, tried after `srcs` (v7.1). -/
  fallbacks : Array (String × Array (Name × Expr)) := #[]

/-- Hygienic binder names would print as `x✝`, which does not parse. -/
partial def eraseBinderScopes : Expr → Expr
  | .forallE n t b bi => .forallE n.eraseMacroScopes (eraseBinderScopes t) (eraseBinderScopes b) bi
  | .lam n t b bi => .lam n.eraseMacroScopes (eraseBinderScopes t) (eraseBinderScopes b) bi
  | .letE n t v b nd =>
    .letE n.eraseMacroScopes (eraseBinderScopes t) (eraseBinderScopes v) (eraseBinderScopes b) nd
  | .app f a => .app (eraseBinderScopes f) (eraseBinderScopes a)
  | .mdata d e => .mdata d (eraseBinderScopes e)
  | .proj s i e => .proj s i (eraseBinderScopes e)
  | e => e

/-- Replaces auxiliary proof constants (`_proof_n`, `_auxLemma`), which tactics such as `omega`
create in the running session and a fresh file cannot reference, by their values (v7). -/
def expandAuxProofs (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (post := fun e => do
    let .const n us := e | return .continue
    let isAux := n.components.any fun c =>
      let c := c.toString; c.startsWith "_proof_" || c.startsWith "_auxLemma"
    unless isAux do return .continue
    let some ci := env.find? n | return .continue
    let some v := ci.value? (allowOpaque := true) | return .continue
    return .visit (v.instantiateLevelParams ci.levelParams us))

/-- Tactic that re-proves the proof holes of `withProofHoles`. -/
def holeTac : String :=
  "(by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)"

/-- Replaces every proof subterm (other than a variable) by the unknown constant `HCHOLE`, and
`GetElem.getElem xs i h` by `HCGETELEM xs i h`, whose notation would otherwise drop the proof.
`ppSrc` turns them into `holeTac` and `GetElem.getElem`. Proof terms from tactics (`omega`, `simp`)
in statements and values often do not elaborate again (v7.1). -/
def withProofHoles (e : Expr) : MetaM Expr :=
  Meta.transform e
    (pre := fun e => do
      if e.isFVar || e.isBVar then return .continue
      if ← (try isProof e catch _ => pure false) then return .done (mkConst `HCHOLE)
      return .continue)
    (post := fun e => do
      if e.isAppOfArity ``GetElem.getElem 8 then
        let as := e.getAppArgs
        return .done (mkAppN (mkConst `HCGETELEM) #[as[5]!, as[6]!, as[7]!])
      return .done e)

/-- `Rat.mk' n d _ _` with literal `n`, `d` as `n / d` (v9): the structure literal prints its
`reduced` proof, which `decide` cannot re-check (`Nat.gcd` is well-founded). -/
def ratLiterals (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    unless e.isAppOfArity ``Rat.mk' 4 do return .continue
    let some n ← getIntValue? (← whnfR (e.getArg! 0)) <|> pure none | return .continue
    let some d ← getNatValue? (e.getArg! 1) <|> pure none | return .continue
    let rat := mkConst ``Rat
    let num ← if n ≥ 0 then mkNumeral rat n.toNat else mkAppM ``Neg.neg #[← mkNumeral rat n.natAbs]
    return .done (← if d == 1 then pure num else mkAppM ``HDiv.hDiv #[num, ← mkNumeral rat d]))

/-- The environment with every delaborator that a library (not Lean itself) registered erased (v12.3).
Such delaborators may drop arguments, even under `pp.explicit`: combinatorial-games prints
`OfSets.ofSets (Player.cases s t) h` as `!{s | t}`, whose macro then has to re-prove `h` by a tactic. -/
def withoutLibraryDelabs (env : Environment) : Environment :=
  PrettyPrinter.Delaborator.delabAttribute.ext.modifyState env fun s =>
    { s with erased := s.table.fold (init := s.erased) fun acc _ es =>
        es.foldl (init := acc) fun acc e => if e.isBuiltin then acc else acc.insert e.declName }

/-- Prints a closed term so that it parses back: full names, proofs instead of `⋯`, one line. With
the option `hypcheck.explicit` also all implicit arguments and raw literals, which round-trips where
the readable form loses information (types of `none`, model instances, coercions). With
`hypcheck.holes`, proofs are printed as `holeTac` (see `withProofHoles`). -/
def ppSrc (e : Expr) : MetaM String := do
  let e := eraseBinderScopes (← expandAuxProofs (← instantiateMVars e))
  let e ← try ratLiterals e catch _ => pure e
  let holes := (← getOptions).getBool `hypcheck.holes
  let e ← if holes then withProofHoles e else pure e
  let explicit := (← getOptions).getBool `hypcheck.explicit
  let univ := (← getOptions).getBool `hypcheck.universes
  let env ← getEnv
  if (← getOptions).getBool `hypcheck.plain then setEnv (withoutLibraryDelabs env)
  let f ← tryFinally (withOptions (fun o => o |>.setBool `pp.fullNames true |>.setBool `pp.proofs true
      |>.setBool `pp.funBinderTypes true |>.setBool `pp.structureInstanceTypes true
      |>.setBool `pp.explicit explicit |>.setBool `pp.natLit explicit
      |>.setBool `pp.universes univ
      |>.set `format.width (1000000 : Nat)) (ppExpr e)) (setEnv env)
  let s := (toString f).replace "\n" "\n    "
  return if holes then (s.replace "HCGETELEM" "GetElem.getElem").replace "HCHOLE" holeTac else s

/-- The readable and the explicit rendering of a proof block, each also with universe levels (v12.3), the
explicit ones once more without the library's delaborators (v12.3, `withoutLibraryDelabs`), then readable and
explicit with proof holes (v7.1). The levels rendering is for refutations at level 0 of universe-polymorphic
statements: a bare `IGame` re-elaborates as `IGame.{u_1}` ("statement differs"); found in combinatorial-games. -/
def bothSrc (gen : MetaM String) : MetaM (Array String) := do
  let holes (o : Options) := o.setBool `hypcheck.holes true
  let univ (o : Options) := o.setBool `hypcheck.universes true
  let plain (o : Options) := o.setBool `hypcheck.plain true
  return #[← gen, ← withOptions univ gen,
    ← withOptions (·.setBool `hypcheck.explicit true) gen,
    ← withOptions (univ <| ·.setBool `hypcheck.explicit true) gen,
    ← withOptions (plain <| ·.setBool `hypcheck.explicit true) gen,
    ← withOptions (plain <| univ <| ·.setBool `hypcheck.explicit true) gen,
    ← withOptions holes gen, ← withOptions (holes <| ·.setBool `hypcheck.explicit true) gen]

/-- `theorem n.{us} : ty := proof`, declaring only the universe parameters `ty` uses. -/
def thmSrc (n : Name) (lps : List Name) (ty : Expr) (proof : String) (hb : Option Nat := none) :
    MetaM String := do
  let used := (collectLevelParams {} ty).params
  let ls := lps.filter used.contains
  let lv := if ls.isEmpty then "" else ".{" ++ ", ".intercalate (ls.map toString) ++ "}"
  let hdr := match hb with | some h => s!"set_option maxHeartbeats {h} in\n" | none => ""
  return s!"{hdr}theorem {n}{lv} : {← ppSrc ty} := {proof}\n"

/-- The universe parameters among `lps` that `ty` uses, as levels (for `mkConst` of a declaration
emitted by `thmSrc`). -/
def usedLevels (lps : List Name) (ty : Expr) : List Level :=
  let used := (collectLevelParams {} ty).params
  (lps.filter used.contains).map mkLevelParam

def tacText (tacs : Array (String × TSyntax `tactic)) (name : String) : MetaM String := do
  let some (_, t) := tacs.find? (·.1 == name) | throwError "unknown tactic {name}"
  -- Identifiers from quotations are hygienic and would print as `x✝`.
  let t := t.raw.rewriteBottomUp fun
    | .ident _ _ n _ => (mkIdent n.eraseMacroScopes).raw
    | s => s
  return s!"by\n  {(toString (← PrettyPrinter.ppTactic ⟨t⟩)).replace "\n" "\n  "}"

/-- Base name of the declarations emitted for hypothesis `idx` of theorem `thm`. -/
def proofDecl (thm : Name) (idx : Nat) : Name :=
  (`HypCheckProof ++ privateToUserName thm).str s!"h{idx}"

def natVals : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 32, 64, 100]
def intVals : Array Int := #[0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 8, -8, 10, -10, 16, -16, 64, -64]

/-- Closed subterms of `e` (no bound, free or meta variables), e.g. `Int32.maxValue.toInt`. -/
partial def closedSubterms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if !e.hasLooseBVars && !e.hasFVar && !e.hasMVar then acc.push e else acc
  match e with
  | .app f a => closedSubterms a (closedSubterms f acc)
  | .lam _ t b _ | .forallE _ t b _ => closedSubterms b (closedSubterms t acc)
  | .letE _ t v b _ => closedSubterms b (closedSubterms v (closedSubterms t acc))
  | .mdata _ b | .proj _ _ b => closedSubterms b acc
  | _ => acc

/-- Numbers occurring in the statement (literals, and closed `Nat`/`Int` terms such as
`Int32.maxValue.toInt`, evaluated by compiled code), each with its neighbours `c - 1` and `c + 1`.
Counterexamples to boundary conditions often sit exactly there. -/
unsafe def mineValues (stmt : Expr) : MetaM (Array Int) := do
  let mut found : Array Int := #[]
  let mut evaluated := 0
  for e in (closedSubterms stmt).toList.eraseDups do
    if found.size ≥ 60 || evaluated ≥ 40 then break
    if let some n := e.nat? then found := found.push n; continue
    if let some i := e.int? then found := found.push i; continue
    let ty ← try instantiateMVars (← inferType e) catch _ => continue
    unless (ty.isConstOf ``Nat || ty.isConstOf ``Int) && e.getAppFn.isConst do continue
    evaluated := evaluated + 1
    if ty.isConstOf ``Nat then
      if let some n ← (try some <$> evalExpr Nat ty e catch _ => pure none) then found := found.push n
    else
      if let some i ← (try some <$> evalExpr Int ty e catch _ => pure none) then found := found.push i
  let withNeighbours := found.flatMap fun c => #[c, c - 1, c + 1]
  return withNeighbours.toList.eraseDups.toArray.filter (·.natAbs < 2 ^ 70)

/-- `base` with the mined values inserted after its first three entries, without duplicates. -/
def withMined {α} [BEq α] (base mined : Array α) : Array α :=
  ((base.extract 0 3 ++ mined ++ base.extract 3 base.size).toList.eraseDups).toArray
/-- Element indices of the small `List`/`Array` values that are tried. -/
def listShapes : List (List Nat) :=
  [[], [0], [1], [0, 1], [1, 0], [0, 0], [2], [1, 2], [0, 1, 2], [2, 1, 0]]

/-- Hand-made counterexample models (see `models.txt`): closed `(type, value)` pairs. -/
abbrev Models := Array (Expr × Expr × String)

/-- Number of arrows and head constant of a type, `none` for a variable head (matches anything). -/
partial def shapeKey : Expr → Nat × Option Name
  | .forallE _ _ b _ => let (n, h) := shapeKey b; (n + 1, h)
  | .sort _ => (0, some `Sort)
  | e => (0, e.getAppFn.constName?)

def keysMatch (a b : Nat × Option Name) : Bool :=
  a.1 == b.1 && (a.2.isNone || b.2.isNone || a.2 == b.2)

def elabModels (lines : Array String) : TermElabM Models := do
  let mut ms := #[]
  for l in lines do
    let l := ((l.splitOn "--")[0]!).trimAscii.toString
    if l.isEmpty then continue
    let ty :: tms := l.splitOn " := " | continue
    if tms.isEmpty then IO.eprintln s!"model `{l}` has no ` := `"; continue
    let tm := " := ".intercalate tms
    try
      let env ← getEnv
      let tyS ← ofExcept <| Parser.runParserCategory env `term ty
      let tmS ← ofExcept <| Parser.runParserCategory env `term tm
      let (t, v) ← Term.withoutErrToSorry do
        let t ← Term.elabType tyS
        let v ← Term.elabTermEnsuringType tmS t
        Term.synthesizeSyntheticMVarsNoPostponing
        -- Default methods (e.g. `Monad.map` from `bind`) can leave universe levels open.
        let st := collectLevelMVars (collectLevelMVars {} (← instantiateMVars t)) (← instantiateMVars v)
        for m in st.result do
          unless ← isLevelMVarAssigned m do assignLevelMVar m Level.zero
        return (← instantiateMVars t, ← instantiateMVars v)
      if t.hasMVar || v.hasMVar || v.hasSorry then throwError "not closed"
      -- Auxiliary lemmas made while elaborating (e.g. `_simp_1` by `simp`) don't survive into the
      -- per-theorem environments (v9).
      if let some c := v.getUsedConstants.find? ((← getEnv).getModuleIdxFor? · |>.isNone) then
        throwError "uses the non-imported constant {c}; avoid `simp` in model proofs"
      unless ms.any (fun (t', v', _) => t' == t && v' == v) do ms := ms.push (t, v, tm.trimAscii.toString)
    catch e => IO.eprintln s!"model `{l}` rejected: {← e.toMessageData.toString}"
  return ms

/-- The models whose type is `ty` (closed). Keys are compared before and after unfolding
reducible definitions, so a model of type `Lean.RArray Int` also matches `CommRing.Context Int`. -/
def modelsFor (models : Models) (ty : Expr) : MetaM (Array Expr) := do
  let k := shapeKey ty
  let k' := shapeKey (← whnfR ty)
  models.filterMapM fun (t, v, _) => do
    unless keysMatch (shapeKey t) k || keysMatch (shapeKey t) k' do return none
    if t == ty then return some v
    return if ← withNewMCtxDepth (withReducible (isDefEq t ty)) then some v else none

/-- Unfolds class projections applied to structure literals, e.g. `@LT.lt Nat ⟨r⟩ a b` to `r a b`,
so that `Decidable` instances are found for propositions about model instances. -/
def unfoldModelProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let .const fn _ := e.getAppFn | return .continue
    let some info ← getProjectionFnInfo? fn | return .continue
    unless info.fromClass do return .continue
    let args := e.getAppArgs
    unless args.size > info.numParams do return .continue
    let s := args[info.numParams]!
    unless s.isAppOfArity info.ctorName (info.numParams + info.i + 1) ||
        (s.isAppOf info.ctorName && s.getAppNumArgs > info.numParams + info.i) do return .continue
    let field := s.getArg! (info.numParams + info.i)
    return .visit (mkAppN field (args.extract (info.numParams + 1) args.size)).headBeta)

def uintTypes : Array Name := #[``UInt8, ``UInt16, ``UInt32, ``UInt64]
def sintTypes : Array Name := #[``Int8, ``Int16, ``Int32, ``Int64]

/-- The constructor and the (non-dependent, non-Prop) field types of a structure type `ty` that is
not a class, e.g. `Std.Rcc Nat` or `Nat × Bool`. -/
def structFields? (ty : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let .const S us := ty.getAppFn | return none
  let env ← getEnv
  unless isStructure env S && !isClass env S do return none
  let ctor := getStructureCtor env S
  unless ty.getAppNumArgs == ctor.numParams do return none
  let mut cty ← instantiateForall (ctor.type.instantiateLevelParams ctor.levelParams us) ty.getAppArgs
  let mut fields := #[]
  for _ in [:ctor.numFields] do
    let .forallE _ d b _ := cty | return none
    if b.hasLooseBVars || (← isProp d) then return none
    fields := fields.push d
    cty := b
  return some (mkAppN (mkConst ctor.name us) ty.getAppArgs, fields)

/-- A structure (not a class) whose data fields are followed by Prop fields, e.g. `String.Pos s`
(`offset`, `isValid`) or `{ x // p x }`: the constructor applied to the parameters, the data field
types (which must not depend on other fields) and the number of Prop fields (v8). -/
def propStructFields? (ty : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let .const S us := ty.getAppFn | return none
  let env ← getEnv
  unless isStructure env S && !isClass env S do return none
  let ctor := getStructureCtor env S
  unless ty.getAppNumArgs == ctor.numParams && ctor.numFields > 0 do return none
  let cty ← instantiateForall (ctor.type.instantiateLevelParams ctor.levelParams us) ty.getAppArgs
  forallBoundedTelescope cty ctor.numFields fun xs _ => do
    if xs.size != ctor.numFields then return none
    let mut data := #[]
    let mut props := 0
    for x in xs do
      let t ← inferType x
      if ← isProp t then props := props + 1
      else
        if props > 0 || t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then return none
        data := data.push t
    if props == 0 || data.isEmpty then return none
    return some (mkAppN (mkConst ctor.name us) ty.getAppArgs, data)

/-- Values from notation classes (v12 bench): `0`, `1`, `2` (`OfNat`), `∅`, `⊥`, `⊤`; `default` only if
none of these exists. For library types without other candidates (`ℝ`, `IGame`, `Nimber`, `Finset α`, …). -/
def notationValues (ty : Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for n in [0, 1, 2] do
    try
      let e ← instantiateMVars (← mkAppOptM ``OfNat.ofNat #[ty, mkRawNatLit n, none])
      unless e.hasMVar do out := out.push e
    catch _ => pure ()
  for c in [``EmptyCollection.emptyCollection, `Bot.bot, `Top.top] do
    if (← getEnv).contains c then
      try
        let e ← instantiateMVars (← mkAppOptM c #[ty, none])
        unless e.hasMVar do out := out.push e
      catch _ => pure ()
  if out.isEmpty then
    try
      let e ← instantiateMVars (← mkAppOptM ``Inhabited.default #[ty, none])
      unless e.hasMVar do out := out.push e
    catch _ => pure ()
  return out

/-- A non-indexed inductive type that is not a class (v12 bench): values from its constructors. -/
def plainInductive? (ty : Expr) : MetaM (Option InductiveVal) := do
  let .const I _ := ty.getAppFn | return none
  let env ← getEnv
  let some (.inductInfo ii) := env.find? I | return none
  if isClass env I || ii.numIndices != 0 || ty.getAppNumArgs != ii.numParams then return none
  return some ii

/-- Candidate carrier types from the instance index (v12 bench): for a constraint `cls` mentioning the type
variable `x`, the instance conclusions `C T` with `T` closed after setting leftover `Nat` parameters to `2` and
type parameters to `Nat` (e.g. `ℚ` for `Field`, `ZMod 2` via `ZMod.instField`). -/
def harvestCarriers (cls x : Expr) (limit : Nat := 12) : MetaM (Array Expr) := do
  let m ← mkFreshExprMVar (← inferType x)
  let q := cls.replaceFVar x m
  let entries ← try (← getGlobalInstancesIndex).getUnify q catch _ => pure #[]
  let mut out := #[]
  for e in entries do
    if out.size ≥ limit then break
    let some n := e.globalName? | continue
    let s ← saveState
    let r ← try
        let c ← mkConstWithFreshMVarLevels n
        let (_, _, concl) ← forallMetaTelescopeReducing (← inferType c)
        if ← isDefEq concl q then
          let mut t ← instantiateMVars m
          for mv in (t.collectMVars {}).result do
            let mty ← instantiateMVars (← mv.getType)
            if mty.isConstOf ``Nat then mv.assign (mkNatLit 2)
            else if mty.isSort then
              discard <| isDefEq (mkMVar mv) (mkConst ``Nat)
          t ← instantiateMVars t
          pure (if t.hasMVar || t.hasFVar then none else some t)
        else pure none
      catch _ => pure none
    s.restore
    if let some t := r then
      unless out.contains t do out := out.push t
  return out

/-- Whether the counterexample search can assign values to a variable of type `ty`.
`dataVars` are the variables that will themselves receive values (e.g. a type `α := Nat`). -/
partial def isEnumerable (dataVars : Array Expr) (ty : Expr) (models : Models := #[]) : MetaM Bool := do
  if ty.isFVar && dataVars.contains ty then return true
  let ty ← whnfR ty
  -- Dependent functions such as `(a : α) → a ∈ l → β` have no candidates.
  if let .forallE _ _ b _ := ty then
    if b.hasLooseBVars then return false
  if models.any (keysMatch (shapeKey ty) <| shapeKey ·.1) then return true
  -- v10: dependent pairs, Std maps and sets (see `valuesFor`)
  if ty.isAppOfArity ``Sigma 2 || ty.isAppOfArity ``PSigma 2 then
    return ← isEnumerable dataVars ty.appFn!.appArg! models
  if let .const S _ := ty.getAppFn then
    if S.getRoot == `Std && (← getEnv).contains (S ++ `ofList) then return true
  if ty.isAppOfArity ``Vector 2 then return ← isEnumerable dataVars ty.appFn!.appArg! models
  if (uintTypes ++ sintTypes).any ty.isConstOf then return true
  if let .forallE _ a b _ := ty then
    if !b.hasLooseBVars then
      return (← isEnumerable dataVars a models) && (← isEnumerable dataVars b models)
  if let some (_, fs) ← structFields? ty then
    return ← fs.allM (isEnumerable dataVars · models)
  if let some (_, fs) ← propStructFields? ty then
    return ← fs.allM (isEnumerable dataVars · models)
  if ty.isConstOf ``USize || ty.isConstOf ``ISize then return true
  if ty.isSort then return true
  if [``Nat, ``Int, ``Bool, ``Char, ``String].any ty.isConstOf then return true
  if ty.isAppOfArity ``BitVec 1 || ty.isAppOfArity ``Fin 1 then return true
  if ty.isAppOfArity ``List 1 || ty.isAppOfArity ``Array 1 || ty.isAppOfArity ``Option 1 then
    return ← isEnumerable dataVars ty.appArg! models
  -- v12 bench: inductive types (constructor values) and types with notation values.
  if (← plainInductive? ty).isSome then return true
  if !ty.hasFVar && !ty.hasMVar then
    return !(← (try notationValues ty catch _ => pure #[])).isEmpty
  return false

/-- Candidate values, smallest first. `ty` must be closed: earlier data variables are already
replaced by values, so that e.g. the width of `BitVec w` can be evaluated. Instance arguments get
the synthesized instance as their only candidate. -/
partial def valuesFor (ty : Expr) (inst : Bool := false) (mined : Array Int := #[])
    (models : Models := #[]) (depth : Nat := 0) : MetaM (Array Expr) := do
  let ty ← instantiateMVars ty
  let ms ← modelsFor models ty
  if inst then
    let i? ← try synthInstance? ty catch _ => pure none
    -- `DecidableLE`/`DecidableLT`/… for a model relation: unfold the model and synthesize (v8.1).
    let i? ← match i? with
      | some i => pure (some i)
      | none => try
          forallTelescope (← whnfR ty) fun xs body => do
            let body ← whnfR body
            unless body.isAppOfArity ``Decidable 1 do return none
            let p := (← unfoldModelProjs body.appArg!).headBeta
            let some i ← synthInstance? (mkApp (mkConst ``Decidable) p) | return none
            let v ← mkLambdaFVars xs i
            return if ← isDefEq (← inferType v) ty then some v else none
        catch _ => pure none
    return i?.toArray ++ ms
  -- Hand-made models are more interesting than the generic functions, so they go first there.
  if ty.isForall then return ms ++ (← valuesForBase ty mined)
  let base ← valuesForBase ty mined
  -- v12 bench: library types without built-in values: constructors, then notation values.
  let base ← if !base.isEmpty || ty.hasFVar then pure base else do
    let iv ← valuesForInd ty mined depth
    if !iv.isEmpty then pure iv else notationValues ty
  return base ++ ms
where
  valuesForInd (ty : Expr) (mined : Array Int) (depth : Nat) : MetaM (Array Expr) := do
    if depth ≥ 3 then return #[]
    let ty ← whnfR ty
    let some ii ← plainInductive? ty | return #[]
    let .const I us := ty.getAppFn | return #[]
    let env ← getEnv
    let params := ty.getAppArgs
    let mut perCtor : Array (Array Expr) := #[]
    for ctor in ii.ctors do
      let some (.ctorInfo ci) := env.find? ctor | continue
      let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams us) params
      let mut fs := #[]
      let mut ok := true
      let mut t := cty
      let mut recursive := false
      for _ in [:ci.numFields] do
        let .forallE _ d b _ := t | ok := false; break
        if b.hasLooseBVars || (← isProp d) then ok := false; break
        if (d.find? (·.isConstOf I)).isSome then
          -- only direct recursion (`Term → Term`), not through other type formers (`List Term`)
          if !d.getAppFn.isConstOf I then ok := false; break
          recursive := true
        fs := fs.push d
        t := b
      unless ok do continue
      if recursive && depth ≥ 2 then continue
      let k := if recursive then 2 else 3
      let mut cands := #[]
      for f in fs do
        cands := cands.push ((← valuesFor f (mined := mined) (models := models) (depth := depth + 1)).extract 0 k)
      if cands.any (·.isEmpty) then continue
      let tuples := cands.foldl (fun acc c => acc.flatMap fun t => (List.range c.size).map (t ++ [·])) [[]]
      let tuples := (tuples.toArray.qsort fun a b => a.sum < b.sum).extract 0 6
      perCtor := perCtor.push (tuples.map fun tp =>
        mkAppN (mkAppN (mkConst ctor us) params) ((tp.toArray.zip cands).map fun (i, c) => c[i]!))
    let mut out := #[]
    for i in [:6] do
      for vs in perCtor do
        if let some v := vs[i]? then out := out.push v
    return out.extract 0 16
  valuesForBase (ty : Expr) (mined : Array Int) : MetaM (Array Expr) := do
    let ty ← whnfR ty
    -- Std maps and sets (v10): `S.ofList` of small lists (instance arguments that the type does not
    -- fix are synthesized), and for tree maps also trees built from the constructors, among them
    -- unordered ones and ones with a wrong size field, which violate `WF`.
    if let .const S _ := ty.getAppFn then
      if S.getRoot == `Std && (← getEnv).contains (S ++ `ofList) then
        let mut out := #[]
        try
          let fn ← mkConstWithFreshMVarLevels (S ++ `ofList)
          let (xs, bis, r) ← forallMetaTelescopeReducing (← inferType fn)
          if ← isDefEq r ty then
            for h : k in [:xs.size] do
              if bis[k]! == .instImplicit && !(← xs[k].mvarId!.isAssigned) then
                let some i ← synthInstance? (← instantiateMVars (← inferType xs[k])) | pure ()
                discard <| isDefEq xs[k] i
            if let some j ← (List.range xs.size).findM? fun k => do
                return bis[k]! == .default && (← instantiateMVars (← inferType xs[k]!)).isAppOfArity ``List 1 then
              let lty ← instantiateMVars (← inferType xs[j]!)
              for l in (← valuesFor lty (mined := mined) (models := models)).extract 0 7 do
                let e ← instantiateMVars (mkAppN fn (xs.set! j l))
                unless e.hasMVar do out := out.push e
        catch _ => pure ()
        let treeLike := S == ``Std.DTreeMap.Raw || S == ``Std.TreeMap.Raw || S == ``Std.TreeSet.Raw
        if treeLike then
          if let some (mk, #[f]) ← structFields? ty then
            let good := out
            let mks := ((← valuesFor f (mined := mined) (models := models)).extract 0 10).map (mkApp mk ·)
            out := #[]
            for k in [:max good.size mks.size] do
              if let some g := good[k]? then out := out.push g
              if let some b := mks[k]? then out := out.push b
        if S == ``Std.DTreeMap.Internal.Impl && ty.getAppNumArgs == 2 then
          let α := ty.appFn!.appArg!
          let β := ty.appArg!
          let us := ty.getAppFn.constLevels!
          let leaf := mkApp2 (mkConst ``Std.DTreeMap.Internal.Impl.leaf us) α β
          let ks := (← valuesFor α (mined := mined) (models := models)).extract 0 2
          if h : ks.size = 2 then
            let val (k : Expr) : MetaM (Option Expr) := do
              return (← valuesFor (mkApp β k).headBeta (mined := mined) (models := models))[0]?
            if let (some v0, some v1) := (← val ks[0], ← val ks[1]) then
              let node (sz : Nat) (k v l r : Expr) :=
                mkAppN (mkConst ``Std.DTreeMap.Internal.Impl.inner us) #[α, β, mkNatLit sz, k, v, l, r]
              let n0 := node 1 ks[0] v0 leaf leaf
              let n1 := node 1 ks[1] v1 leaf leaf
              -- Interleaved with the `ofList` trees (v10.1): the malformed ones are the only
              -- counterexamples for a dropped `WF`, and appended last the search never reached them.
              let bad := #[node 2 ks[0] v0 n1 leaf, node 2 ks[1] v1 leaf n0, node 2 ks[0] v0 leaf leaf,
                node 3 ks[0] v0 n1 n1, node 2 ks[1] v1 n0 leaf, leaf]
              let good := out
              out := #[]
              for k in [:max good.size bad.size] do
                if let some g := good[k]? then out := out.push g
                if let some b := bad[k]? then out := out.push b
        unless out.isEmpty do return out
    if let .sort l := ty then
      let l := (← instantiateLevelMVars l).normalize
      if l.isZero then return #[mkConst ``True, mkConst ``False]
      if l == Level.one then return #[mkConst ``Nat, mkConst ``Bool]
      return #[]
    if ty.isConstOf ``Nat then
      return (withMined natVals (mined.filterMap fun i => if i ≥ 0 then some i.toNat else none)).map mkNatLit
    if ty.isConstOf ``Int then return (withMined intVals mined).map toExpr
    if ty.isConstOf ``Bool then return #[toExpr false, toExpr true]
    if ty.isConstOf ``Char then return #['a', '0', ' '].map toExpr
    -- `"é"`, `"aé"`: two-byte characters, so that byte offsets inside a character occur (v8)
    if ty.isConstOf ``String then return #["", "a", "0", "ab", "é", "aé", "a b"].map toExpr
    if ty.isAppOfArity ``BitVec 1 then
      let some w ← evalNat ty.appArg! | return #[]
      let vs := if w ≤ 4 then Array.range (2 ^ w) else
        #[0, 1, 2, 3, 2 ^ (w - 1) - 1, 2 ^ (w - 1), 2 ^ w - 2, 2 ^ w - 1]
      return vs.map fun v => mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit v)
    if ty.isAppOfArity ``Fin 1 then
      let some n ← evalNat ty.appArg! | return #[]
      let vs := (#[0, 1, 2, 3, 4, n - 2, n - 1].filter (· < n)).toList.eraseDups.toArray
      return ← vs.mapM fun v => do
        let lt ← mkDecideProof (← mkLt (mkNatLit v) (mkNatLit n))
        return mkApp3 (mkConst ``Fin.mk) (mkNatLit n) (mkNatLit v) lt
    if ty.isAppOfArity ``List 1 || ty.isAppOfArity ``Array 1 then
      let α := ty.appArg!
      let es := (← valuesFor α (mined := mined) (models := models)).extract 0 3
      let shapes := listShapes.filter (·.all (· < es.size))
      return ← shapes.toArray.mapM fun s =>
        if ty.isAppOfArity ``List 1 then mkListLit α (s.map (es[·]!)) else mkArrayLit α (s.map (es[·]!))
    -- Functions built from values of the codomain: constants, and `if a = a₀ then b₀ else b₁`.
    if let .forallE n a b _ := ty then
      if b.hasLooseBVars then return #[]
      -- Type families `α → Type`: constant families `fun _ => Nat`, `fun _ => Bool` (v10).
      if let .sort l := (← whnfR b) then
        if (← instantiateLevelMVars l).normalize.isZero then return #[]
        let bs := (← valuesFor b (mined := mined) (models := models)).extract 0 2
        return ← bs.mapM fun v => withLocalDeclD n a fun x => mkLambdaFVars #[x] v
      let bs := (← valuesFor b (mined := mined) (models := models)).extract 0 3
      let consts ← bs.mapM fun v => withLocalDeclD n a fun x => mkLambdaFVars #[x] v
      let as := (← valuesFor a (mined := mined) (models := models)).extract 0 2
      if bs.size < 2 || as.isEmpty then return consts
      let steps ← withLocalDeclD n a fun x => do
        let mut r := #[]
        for a₀ in as do
          for (b₀, b₁) in [(bs[0]!, bs[1]!), (bs[1]!, bs[0]!)] do
            try
              let c ← mkEq x a₀
              let some dec ← synthInstance? (mkApp (mkConst ``Decidable) c) | continue
              r := r.push (← mkLambdaFVars #[x] (mkApp5 (mkConst ``ite [← getLevel b]) b c dec b₀ b₁))
            catch _ => pure ()
        return r
      return consts ++ steps
    if let some T := uintTypes.find? ty.isConstOf then
      let ns := withMined natVals (mined.filterMap fun i => if i ≥ 0 then some i.toNat else none)
      return ns.map fun n => mkApp (mkConst (T ++ `ofNat)) (mkNatLit n)
    if let some T := sintTypes.find? ty.isConstOf then
      return (withMined intVals mined).map fun i => mkApp (mkConst (T ++ `ofInt)) (toExpr i)
    if ty.isConstOf ``USize then
      return #[0, 1, 2, 3, 4, 5, 8, 16].map fun n => mkApp (mkConst ``USize.ofNat) (mkNatLit n)
    if ty.isConstOf ``ISize then
      return (#[0, 1, -1, 2, -2, 3, -3, 8] : Array Int).map fun i => mkApp (mkConst ``ISize.ofInt) (toExpr i)
    if let some (mk, fs) ← structFields? ty then
      let cands ← fs.mapM fun f => return (← valuesFor f (mined := mined) (models := models)).extract 0 4
      if cands.any (·.isEmpty) then return #[]
      let tuples := cands.foldl (fun acc c => acc.flatMap fun t => (List.range c.size).map (t ++ [·])) [[]]
      let tuples := (tuples.toArray.qsort fun a b => a.sum < b.sum).extract 0 12
      return tuples.map fun t => mkAppN mk ((t.toArray.zip cands).map fun (i, c) => c[i]!)
    -- Data fields from their candidates, Prop fields by `decide` (dropped if false or stuck) (v8).
    if let some (mk, fs) ← propStructFields? ty then
      let k := if fs.size == 1 then 16 else 4
      let cands ← fs.mapM fun f => return (← valuesFor f (mined := mined) (models := models)).extract 0 k
      if cands.any (·.isEmpty) then return #[]
      let tuples := cands.foldl (fun acc c => acc.flatMap fun t => (List.range c.size).map (t ++ [·])) [[]]
      let tuples := (tuples.toArray.qsort fun a b => a.sum < b.sum).extract 0 16
      let mut out := #[]
      for t in tuples do
        let mut e := mkAppN mk ((t.toArray.zip cands).map fun (i, c) => c[i]!)
        let mut ok := true
        repeat
          let .forallE _ p _ _ ← whnfR (← inferType e) | break
          let some inst ← (try synthInstance? (mkApp (mkConst ``Decidable) p) catch _ => pure none)
            | ok := false; break
          let r ← (try withAtLeastTransparency .default <| whnf (mkApp2 (mkConst ``Decidable.decide) p inst)
            catch _ => pure (mkConst ``Bool.false))
          unless r.isConstOf ``Bool.true do ok := false; break
          e := mkApp e (← mkDecideProof p)
        if ok then out := out.push e
      return out
    if ty.isAppOfArity ``Vector 2 then
      let α := ty.appFn!.appArg!
      let some n ← evalNat ty.appArg! | return #[]
      if n > 3 then return #[]
      let es := (← valuesFor α (mined := mined) (models := models)).extract 0 3
      -- All index tuples of length `n`, by increasing index sum.
      let tuples := (List.range n).foldl (fun acc _ => acc.flatMap fun t => (List.range es.size).map (t ++ [·])) [[]]
      let tuples := (tuples.toArray.qsort fun a b => a.sum < b.sum).extract 0 10
      return ← tuples.mapM fun t => do
        let arr ← mkArrayLit α (t.map (es[·]!))
        mkAppOptM ``Vector.mk #[α, mkNatLit n, arr, ← mkEqRefl (mkNatLit n)]
    if ty.isAppOfArity ``Option 1 then
      let α := ty.appArg!
      let es := (← valuesFor α (models := models)).extract 0 3
      return #[← mkAppOptM ``Option.none #[α]] ++ (← es.mapM fun e => mkAppM ``Option.some #[e])
    -- Dependent pairs `⟨a, b⟩` with `b : β a` (v10), e.g. the entries of a `DTreeMap`.
    if ty.isAppOfArity ``Sigma 2 || ty.isAppOfArity ``PSigma 2 then
      let α := ty.appFn!.appArg!
      let β := ty.appArg!
      let as := (← valuesFor α (mined := mined) (models := models)).extract 0 3
      let mut out : Array (Nat × Expr) := #[]
      for h : i in [:as.size] do
        let a := as[i]
        let bs := (← valuesFor (mkApp β a).headBeta (mined := mined) (models := models)).extract 0 2
        for h' : j in [:bs.size] do
          let mk := if ty.isAppOfArity ``Sigma 2 then ``Sigma.mk else ``PSigma.mk
          try
            let e ← mkAppOptM mk #[α, β, a, bs[j]]
            out := out.push (i + 2 * j, e)
          catch _ => pure ()
      return (out.qsort (·.1 < ·.1)).map (·.2)
    return #[]

/-- Splits a recorded witness `x := v, y := w, …` into the value texts, at top-level `, ` only
(brackets, `«»` model quotes and string literals nest). Model quotes are removed. -/
def splitWitness (w : String) : Array String := Id.run do
  let mut parts : Array String := #[]
  let mut cur := ""
  let mut depth : Int := 0
  let mut inStr := false
  let cs := w.toList.toArray
  let mut k := 0
  while k < cs.size do
    let c := cs[k]!
    if inStr then
      cur := cur.push c
      if c == '\\' && k + 1 < cs.size then cur := cur.push cs[k+1]!; k := k + 1
      else if c == '"' then inStr := false
    else if c == '"' then inStr := true; cur := cur.push c
    else if "([{⟨«".contains c then depth := depth + 1; cur := cur.push c
    else if ")]}⟩»".contains c then depth := depth - 1; cur := cur.push c
    else if c == ',' && depth == 0 && k + 1 < cs.size && cs[k+1]! == ' ' then
      parts := parts.push cur; cur := ""; k := k + 1
    else cur := cur.push c
    k := k + 1
  parts := parts.push cur
  return parts.map fun p =>
    let v := match p.splitOn " := " with
      | _ :: rest@(_ :: _) => " := ".intercalate rest
      | _ => p
    let v := v.trimAscii.toString
    if v.startsWith "«" && v.endsWith "»" then ((v.drop 1).dropEnd 1).toString else v

/-- Elaborates the recorded witness values against the binder types, in order (`v7 --redo`).
A value that does not parse or typecheck (e.g. printed with `⋯`) gives `none`, and so does every
later variable whose type depends on a variable without a value. -/
def elabSeeds (data : Array Expr) (w : String) : TermElabM (Array (Option Expr)) := do
  let texts := splitWitness w
  if texts.size != data.size then return data.map fun _ => none
  let mut vals : Array (Option Expr) := #[]
  for j in [:data.size] do
    let ty0 ← inferType data[j]!
    if (List.range j).any fun k => vals[k]!.isNone && ty0.containsFVar data[k]!.fvarId! then
      vals := vals.push none; continue
    let known := (List.range j).filter (vals[·]!.isSome)
    let ty ← instantiateMVars (ty0.replaceFVars (known.toArray.map (data[·]!)) (known.toArray.map (vals[·]!.get!)))
    let v? ← try
        let env ← getEnv
        let stx ← ofExcept <| Parser.runParserCategory env `term texts[j]!
        Term.withoutErrToSorry do
          let v ← Term.elabTermEnsuringType stx ty
          Term.synthesizeSyntheticMVarsNoPostponing
          let v ← instantiateMVars v
          pure (if v.hasMVar || v.hasSorry then none else some v)
      catch _ => pure none
    vals := vals.push v?
  return vals

/-- Carrier types for a type variable `data[j] : Type` (v12 bench). Constraints are the instance binders (data or
Prop) that mention only this variable. Pool: `Nat`, `Bool`, `Int`, `Fin 2`, `Fin 3`, `Unit`, `Rat`, `Prop`, plus the
types harvested from the instance index for each data constraint. Kept: every data constraint synthesizes; order:
most Prop constraints satisfied first, then pool order. `none` (old behaviour: `Nat`, `Bool`) without constraints. -/
def carrierCands (data hyps : Array Expr) (j : Nat) : MetaM (Option (Array Expr)) := do
  let some x := data[j]? | return none
  let ty ← whnfR (← instantiateMVars (← inferType x))
  let .sort l := ty | return none
  unless (← instantiateLevelMVars l).normalize == Level.one do return none
  let all := data ++ hyps
  let mut cons : Array (Expr × Bool) := #[]
  for y in all do
    let d ← y.fvarId!.getDecl
    let t ← instantiateMVars d.type
    let isInst := d.binderInfo.isInstImplicit || (← isClass? t).isSome
    if !isInst || !t.containsFVar x.fvarId! then continue
    if t.hasAnyFVar (fun f => f != x.fvarId! && all.any (·.fvarId! == f)) then continue
    cons := cons.push (t, ← isProp t)
  if cons.isEmpty then return none
  -- If `Nat` meets every constraint, keep the old behaviour (`Nat`, `Bool`): extra carriers only slow down a
  -- search that already has a fitting type (seen on core tree-map rows found close to the time limit).
  let natOk ← cons.allM fun (t, _) => do
    return (← try synthInstance? (t.replaceFVar x (mkConst ``Nat)) catch _ => pure none).isSome
  if natOk then return none
  let mut pool : Array Expr := #[mkConst ``Nat, mkConst ``Bool, mkConst ``Int,
    mkApp (mkConst ``Fin) (mkNatLit 2), mkApp (mkConst ``Fin) (mkNatLit 3), mkConst ``Unit]
  if (← getEnv).contains ``Rat then pool := pool.push (mkConst ``Rat)
  pool := pool.push (mkSort levelZero)
  for (t, isP) in cons do
    unless isP do
      for T in ← harvestCarriers t x do
        unless pool.contains T do pool := pool.push T
  let mut scored : Array (Expr × Nat × Nat) := #[]
  for h : k in [:pool.size] do
    let T := pool[k]
    let mut ok := true
    let mut score := 0
    for (t, isP) in cons do
      let r ← try synthInstance? (t.replaceFVar x T) catch _ => pure none
      if isP then
        if r.isSome then score := score + 1
      else if r.isNone then
        ok := false
        break
    if ok then scored := scored.push (T, score, k)
  let sorted := scored.qsort fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)
  return some ((sorted.extract 0 6).map (·.1))

/-- All assignments to `data[j:]` whose candidate indices sum to exactly `s`. -/
partial def assignmentsWithSum (data : Array Expr) (s j : Nat) (vals : Array Expr)
    (mined : Array Int := #[]) (models : Models := #[]) (relevant : Array Bool := #[])
    (defined : Array Bool := #[]) (seeds : Array (Option Expr) := #[])
    (carriers : Array (Option (Array Expr)) := #[]) : MetaM (Array (Array Expr)) := do
  if h : j < data.size then
    let ty := (← inferType data[j]).replaceFVars (data.extract 0 j) vals
    -- Class-typed binders that are not instance-implicit (e.g. `{inst : Semiring R}` of structure
    -- projections) are treated as instances too (v9).
    let inst := (← data[j].fvarId!.getDecl).binderInfo.isInstImplicit ||
      (← isClass? (← data[j].fvarId!.getType)).isSome
    -- A variable fixed by an equation hypothesis gets its value after the others (placeholder).
    let cands ← if defined.getD j false then pure #[mkConst ``True] else
      match carriers[j]? with
      | some (some cs) => pure (cs ++ (← modelsFor models ty))
      | _ => valuesFor ty inst mined models
    -- The recorded witness value comes first, if it fits the type after the earlier choices.
    let cands ← match seeds[j]? with
      | some (some sv) =>
        if ← (try isDefEq (← inferType sv) ty catch _ => pure false) then
          pure (#[sv] ++ cands.filter (· != sv))
        else pure cands
      | _ => pure cands
    -- A variable the statement does not mention only needs some value.
    let cands := if relevant.getD j true then cands else cands.extract 0 1
    let mut res := #[]
    for i in [:min (s + 1) cands.size] do
      res := res ++ (← assignmentsWithSum data (s - i) (j + 1) (vals.push cands[i]!) mined models relevant defined seeds carriers)
    return res
  else
    return if s == 0 then #[vals] else #[]

/-- Evaluates a closed proposition through its `Decidable` instance, within `hb` heartbeats.
`none` if there is no instance or the reduction gets stuck (e.g. on well-founded recursion). -/
def quickDecide (p : Expr) (hb : Nat) : MetaM (Option Bool) :=
  withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
    tryCatchRuntimeEx (do
      let some inst ← synthInstance? (mkApp (mkConst ``Decidable) p) | return none
      let d := mkApp2 (mkConst ``Decidable.decide) p inst
      let r ← withAtLeastTransparency .default <| whnf d
      let r ← if r.isConstOf ``Bool.true || r.isConstOf ``Bool.false then pure r else
        -- The kernel unfolds well-founded definitions and has GMP `Nat.gcd`, so e.g. `Rat`
        -- arithmetic evaluates there but not in `whnf` (v9).
        let d ← instantiateMVars d
        if d.hasMVar then pure r else
        match Kernel.whnf (← getEnv) (← getLCtx) d with
        | .ok r' => pure r'
        | .error _ => pure r
      return if r.isConstOf ``Bool.true then some true
        else if r.isConstOf ``Bool.false then some false else none)
      (fun _ => return none)

/-- `of_decide_eq_true rfl : p` without the elaborator's check, for propositions that `quickDecide`
evaluated to true only in the kernel or whose model terms make `decide` exceed its heartbeats; the
caller has the kernel check the proof (v9). -/
def kernelDecideProof? (p : Expr) : MetaM (Option Expr) := do
  let some inst ← (try synthInstance? (mkApp (mkConst ``Decidable) p) catch _ => pure none) | return none
  let rfl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let pf := mkApp3 (mkConst ``of_decide_eq_true) p inst rfl
  -- `quickDecide` may evaluate well-founded definitions that the kernel does not unfold (v10.1);
  -- then the caller falls back to its tactics.
  if p.hasFVar || p.hasMVar then return some pf
  return if ← kernelAccepts [] p pf then some pf else none

/-- Proves a Prop-valued class instance such as `@EquivBEq Bool ⟨fun _ _ => true⟩` for a model by
applying the structure constructor and proving each field (recursively for parent classes).
Also returns the proof as source: `@Ctor _ … field…` with tactic blocks for the fields. -/
partial def proveLaws (goal : Expr) (tacs : Array (String × TSyntax `tactic)) (hb : Nat)
    (depth : Nat := 0) : TermElabM (Option (Expr × String)) := do
  if depth > 4 then return none
  let goal ← whnfR (← instantiateMVars goal)
  let .const S us := goal.getAppFn | return none
  let env ← getEnv
  unless isStructure env S do return none
  let ctor := getStructureCtor env S
  let params := goal.getAppArgs
  unless params.size == ctor.numParams do return none
  let mut ty ← instantiateForall (ctor.type.instantiateLevelParams ctor.levelParams us) params
  let mut args := #[]
  let mut srcs := #[]
  for _ in [:ctor.numFields] do
    let .forallE _ d b _ := ty | return none
    let d ← unfoldModelProjs d
    let p? ← if (← isClass? d).isSome then
        match ← (try synthInstance? d catch _ => pure none) with
        | some i => pure (some (i, "inferInstance"))
        | none => proveLaws d tacs hb (depth + 1)
      else match ← firstProof d tacs hb with
        | some (n, p) => pure (some (p, s!"(by (try dsimp only); {(← tacText tacs n).drop 3})"))
        | none => pure none
    let some (p, src) := p? | return none
    args := args.push p
    srcs := srcs.push src
    ty := b.instantiate1 p
  -- The parameters are printed (explicitly), not left as `_`: a `_` in an instance position would
  -- be filled by instance search, which finds the lawful instance instead of the model (v7).
  let ps ← withOptions (·.setBool `hypcheck.explicit true) <| params.mapM fun p => return s!" ({← ppSrc p})"
  return some (mkAppN (mkConst ctor.name us) (params ++ args),
    s!"(@{ctor.name}{String.join ps.toList} {" ".intercalate srcs.toList})")

structure Verdict where
  status : String
  dependent : Bool := false
  derivable : Option Bool := none
  tactic : Option String := none
  witness : Option String := none
  reason : Option String := none
  note : Option String := none
  proof? : Option ProofBlock := none

/-- Refutes a closed Prop-valued class instance `c` (e.g. `IsPartialOrder Int` for a model `LE Int`,
or `IsCharP (Fin 2) 0`), which has no `Decidable` instance: finds a field, through parent
projections, that evaluates to false at small values, and returns it as `exact` tactics in a readable
and an explicit rendering, e.g. `exact fun hc_c => absurd (hc_c.toIsPreorder.le_refl (0 : Int)) (by …)`
(v9). Implicit binders are passed by name, premises by `decide +kernel`. -/
partial def classRefuteTacs (c : Expr) (models : Models) (mined : Array Int) (hb : Nat) :
    MetaM (Array (String × TSyntax `tactic)) := do
  let c ← instantiateMVars c
  if c.hasFVar || c.hasMVar then return #[]
  unless (← isClass? c).isSome && (← isProp c) do return #[]
  let budget ← IO.mkRef (60 : Nat)
  let some (path, args) ← withLocalDeclD `hc_c c fun h => search budget h c "hc_c" 0 | return #[]
  let mut out := #[]
  for explicit in [false, true] do
    let strs ← withOptions (·.setBool `hypcheck.explicit explicit) <| args.mapM fun (n?, v?) => do
      let s ← match v? with
        | none => pure kt
        | some v => match models.find? (·.2.1 == v) with
          | some (_, mv, src) => pure s!"({src} : {← ppSrc (← inferType mv)})"
          | none => pure s!"({← ppSrc v} : {← ppSrc (← inferType v)})"
      return match n? with | some n => s!"({n} := {s})" | none => s
    let txt := s!"exact fun hc_c => absurd ({path} {" ".intercalate strs.toList}) {kt}"
    if let .ok stx := Parser.runParserCategory (← getEnv) `tactic txt then
      out := out.push (if explicit then "class-refute explicit" else "class-refute", ⟨stx⟩)
  return out
where
  kt : String := "(by first | decide +kernel | (dsimp only <;> decide +kernel))"
  /-- Fields of the class `ty`, whose instance `e` prints as `path`. -/
  search (budget : IO.Ref Nat) (e ty : Expr) (path : String) (depth : Nat) :
      MetaM (Option (String × Array (Option Name × Option Expr))) := do
    if depth > 4 then return none
    let ty ← whnfR ty
    let .const S us := ty.getAppFn | return none
    let env ← getEnv
    unless isStructure env S do return none
    for f in getStructureFields env S do
      let some proj := getProjFnForField? env S f | continue
      let pe := mkAppN (mkConst proj us) (ty.getAppArgs.push e)
      let some fty ← (try some <$> (instantiateMVars (← inferType pe)) catch _ => pure none) | continue
      let fpath := s!"{path}.{f}"
      if (← isClass? fty).isSome && !fty.isForall then
        if let some r ← search budget pe fty fpath (depth + 1) then return some r
      else if let some args ← refute budget fty then return some (fpath, args)
    return none
  /-- Values for the binders of the field type `t` under which its body evaluates to false. -/
  refute (budget : IO.Ref Nat) (t : Expr) : MetaM (Option (Array (Option Name × Option Expr))) := do
    if (← budget.get) == 0 then return none
    match t with
    | .forallE n d b bi =>
      let name? : Option (Option Name) :=
        if bi.isExplicit then some none
        else if n.hasMacroScopes || n.isAnonymous then none else some (some n)
      if ← isProp d then
        if b.hasLooseBVars then return none
        let some nm := name? | return none
        if (← quickDecide (← unfoldModelProjs d) hb) != some true then return none
        let some rest ← refute budget b | return none
        return some (#[(nm, none)] ++ rest)
      if bi.isInstImplicit then
        let some i ← (try synthInstance? d catch _ => pure none) | return none
        return ← refute budget (b.instantiate1 i)
      let some nm := name? | return none
      for v in (← valuesFor d (mined := mined) (models := models)).extract 0 5 do
        if let some rest ← refute budget (b.instantiate1 v) then return some (#[(nm, some v)] ++ rest)
      return none
    | _ =>
      budget.modify (· - 1)
      return if (← quickDecide (← unfoldModelProjs (mkNot t)) hb) == some true then some #[] else none

/-- `letI` lines providing `DecidableRel` for the `LT`/`LE` models among the values (v8.1): instance
search cannot find decidability for a relation given by a model structure, so `decide` would be stuck
on e.g. `xs < ys` for lists or vectors over the model. The instance is synthesized for the unfolded
relation (e.g. `Nat.decLe a b`) and printed explicitly. -/
def modelDecLets (vals : Array Expr) (models : Models) : MetaM (Array String) := do
  let mut out := #[]
  let mut seen : Array Expr := #[]
  for v in vals do
    unless models.any (·.2.1 == v) do continue
    if seen.contains v then continue
    let ty ← whnfR (← inferType v)
    let some (cls, fld) := if ty.isAppOfArity ``LT 1 then some (``LT, ``LT.lt)
      else if ty.isAppOfArity ``LE 1 then some (``LE, ``LE.le) else none | continue
    let _ := cls
    let T := ty.appArg!
    try
      let r ← mkAppOptM fld #[T, v]
      let declTy ← mkAppM ``DecidableRel #[r]
      let val ← withLocalDeclD `a T fun a => withLocalDeclD `b T fun b => do
        let p := (← unfoldModelProjs (mkApp2 r a b)).headBeta
        let i ← synthInstance (mkApp (mkConst ``Decidable) p)
        mkLambdaFVars #[a, b] i
      unless ← isDefEq (← inferType val) declTy do continue
      let txt ← withOptions (·.setBool `hypcheck.explicit true) do
        return s!"letI _hcd{out.size} : {← ppSrc declTy} := {← ppSrc val}"
      out := out.push txt
      seen := seen.push v
    catch _ => pure ()
  return out

/-- The `decide` variants under the `letI` lines of `modelDecLets`, as parsed tactics. -/
def decTacsWith (lets : Array String) : MetaM (Array (String × TSyntax `tactic)) := do
  if lets.isEmpty then return #[]
  let pre := "; ".intercalate lets.toList
  let mut out := #[]
  for (n, t) in [("decide-models", "decide"), ("decide-models +kernel", "decide +kernel"),
      ("decide-models simp", "simp <;> decide")] do
    match Parser.runParserCategory (← getEnv) `tactic s!"({pre}; {t})" with
    | .ok stx => out := out.push (n, ⟨stx⟩)
    | .error _ => pure ()
  return out

/-- grind's recursive predicates (`def`s by pattern matching or `rec`) that have no `Decidable`
instance; `grindPredTacs` unfolds them before `decide` (v9.1). -/
def grindPredNames : Array Name := #[`Lean.Grind.CommRing.PPoly.NonNeg, `Lean.Grind.CommRing.PPoly.Deg,
  `Lean.Grind.CommRing.PPoly.DegList, `Lean.Grind.CommRing.KList.AllZero,
  `Lean.Grind.CommRing.MList.AllZero, `Lean.Grind.CommRing.InvAtoms.ok, `Lean.Grind.CommRing.InvVars.ok,
  `Lean.Grind.CommRing.Poly.NonnegCoeffs]

/-- Tactics for propositions about `grindPredNames` at concrete values (v9.1): unfold and `decide`,
or build `Poly.NonnegCoeffs` (an inductive predicate) from its constructors. -/
def grindPredTacs : TermElabM (Array (String × TSyntax `tactic)) := do
  -- CSLib port: these predicates are from lean4 4.37-pre; v4.36.0-rc2 has none, so skip the tactics.
  unless (← getEnv).contains `Lean.Grind.CommRing.PPoly.NonNeg do return #[]
  return #[
    ("grind-preds", ← `(tactic| (simp only [Lean.Grind.CommRing.PPoly.NonNeg,
      Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList, Lean.Grind.CommRing.KList.AllZero,
      Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok, Lean.Grind.CommRing.InvVars.ok,
      Lean.Grind.CommRing.InvVars.denoteVars, Lean.Grind.CommRing.InvVars.denoteInvs] <;> decide +kernel))),
    ("nonneg-coeffs", ← `(tactic| (repeat (first | decide | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num |
      apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add))))]

/-- Namespaces of the Std map and set implementations (v10). -/
def stdMapNs : List Name := [`Std.DTreeMap, `Std.TreeMap, `Std.TreeSet, `Std.ExtDTreeMap,
  `Std.ExtTreeMap, `Std.ExtTreeSet, `Std.Internal.List]

/-- Definitions of the Std map namespaces that `c` uses, directly or through other such definitions
(depth 3): wrappers like `TreeMap.Raw.minKey?` and the well-founded `Impl.minKey?` behind them,
which neither `decide` nor the kernel unfolds. Construction functions (`ofList`, `insertMany`) are
left to `simp`'s ground evaluation (v10). -/
def stdMapDefs (c : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let inNs (n : Name) := stdMapNs.any (·.isPrefixOf n)
  let mut out := #[]
  let mut seen : NameSet := {}
  let mut todo : List (Name × Nat) := c.getUsedConstants.toList.map (·, 0)
  while true do
    let some (n, d) := todo.head? | break
    todo := todo.tail
    if seen.contains n || !inNs n then continue
    seen := seen.insert n
    let some (.defnInfo di) := env.find? n | continue
    let last := match n with | .str _ s => s | _ => ""
    if n.isInternal || last.startsWith "match_" || last.startsWith "proof_" || last.startsWith "eq_" ||
        ["ofList", "insertMany", "unitOfList", "ofArray"].any (last == ·) then continue
    out := out.push n
    if out.size ≥ 40 then break
    if d < 3 then todo := todo ++ di.value.getUsedConstants.toList.map (·, d + 1)
  return out

/-- `simp` with the Std map definitions of `c` and ground evaluation (v10). -/
def stdMapTacs (c : Expr) : TermElabM (Array (String × TSyntax `tactic)) := do
  let ns ← stdMapDefs c
  if ns.isEmpty then return #[]
  let lemmas ← ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  return #[("std-eval", ← `(tactic| simp +ground +decide [$lemmas,*])),
    ("std-eval-all", ← `(tactic| simp_all +ground +decide [$lemmas,*]))]

/-- Filter statements at concrete filters (`⊤`, `⊥`, `pure a`, `𝓟 s`) and sets (Mathlib.Order probe): unfold
eventually/frequently, `=ᶠ`/`≤ᶠ`, `Tendsto` and `NeBot` to membership, then decide over a finite carrier. Only
for statements that mention a `Filter.*` constant; the lemma names parse but fail harmlessly without Mathlib. -/
def filterLemmaNames : List Name := [`Filter.EventuallyEq, `Filter.EventuallyLE, `Filter.EventuallyEqSet,
  `Filter.EventuallySubset, `Filter.eventually_top, `Filter.eventually_bot, `Filter.eventually_pure,
  `Filter.eventually_principal, `Filter.frequently_top, `Filter.frequently_bot, `Filter.frequently_pure,
  `Filter.frequently_principal, `Filter.tendsto_pure, `Filter.tendsto_top, `Filter.tendsto_bot,
  `Filter.tendsto_principal, `Filter.tendsto_principal_principal, `Filter.tendsto_pure_pure,
  `Filter.principal_neBot_iff, `Filter.not_neBot, `Filter.mem_principal, `Filter.mem_top, `Filter.mem_pure,
  `Filter.mem_bot, `Filter.principal_eq_bot_iff, `Filter.pure_ne_bot, `Filter.top_ne_bot, `Set.ext_iff,
  `Set.subset_def, `Set.le_eq_subset, `Set.mem_setOf_eq, `Set.nonempty_def]

def filterTacs (c : Expr) : TermElabM (Array (String × TSyntax `tactic)) := do
  unless (c.find? fun s => s.isConst && s.constName!.getRoot == `Filter).isSome do return #[]
  let env ← getEnv
  let ns := filterLemmaNames.filter env.contains
  if ns.isEmpty then return #[]
  let lemmas ← ns.toArray.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  return #[("filter-eval", ← `(tactic| (simp +decide [$lemmas,*]; done))),
    ("filter-eval-decide", ← `(tactic| (simp [$lemmas,*] <;> decide))),
    ("filter-eval-all", ← `(tactic| (intros; simp_all +decide [$lemmas,*]; done)))]

def mentionsGrindPreds (e : Expr) : Bool :=
  (e.find? fun s => s.isConst && grindPredNames.contains s.constName!).isSome

/-- The sides of a hypothesis that can define a variable: `a = b`, or `(a == b) = true` (v9; the
latter is discharged by `beq_self_eq_true`, so the `BEq` must be reflexive). -/
def defSides? (ty : Expr) : Option (Expr × Expr) :=
  match ty.eq? with
  | some (_, l, r) =>
    if r.isConstOf ``Bool.true && l.isAppOfArity ``BEq.beq 4 then some (l.getArg! 2, l.getArg! 3)
    else some (l, r)
  | none => none

/-- Tries to prove `¬T'` for `T' = tp = ∀ rest, body` with `nRest` leading binders.
Universe parameters are fixed so that type variables can be `Nat`/`Bool`; a counterexample at one
universe level still shows that `T'` cannot be a (universe-polymorphic) theorem. -/
unsafe def findCounterexample (o : Opts) (decl : Name) (lps : List Name) (tp : Expr) (nRest : Nat)
    (cexTacs premTacs directTacs : Array (String × TSyntax `tactic)) (mined : Array Int)
    (models : Models := #[]) (lawTacs : Array (String × TSyntax `tactic) := #[])
    (seed : Option String := none) :
    TermElabM (Except String (String × String × ProofBlock)) := do
  let us ← lps.mapM fun _ => mkFreshLevelMVar
  let tpL := tp.instantiateLevelParams lps us
  forallBoundedTelescope tpL nRest fun rest body => do
    let mut data := #[]
    let mut hyps := #[]
    for x in rest do
      if ← isProp (← inferType x) then hyps := hyps.push x else data := data.push x
    -- Equation hypotheses `x = t` (or `t = x`) with a data variable `x` that `t`, the other data
    -- types and earlier definitions don't mention: `x` is set to `t` instead of being enumerated (v7).
    let mut defs : Array (Nat × Expr × Expr) := #[]  -- (index of `x` in `data`, `t`, hypothesis)
    for hyp in hyps do
      if (← hyp.fvarId!.getDecl).binderInfo.isInstImplicit then continue
      let some (a, b) := defSides? (← instantiateMVars (← inferType hyp)) | continue
      for (x, t) in [(a, b), (b, a)] do
        let some j := data.idxOf? x | continue
        if t.containsFVar x.fvarId! || t.hasAnyFVar (hyps.map (·.fvarId!)).contains then continue
        if defs.any (·.1 == j) then continue
        if ← data.anyM fun y => return (← inferType y).containsFVar x.fvarId! then continue
        if defs.any fun (k, t', _) => t'.containsFVar x.fvarId! || t.containsFVar data[k]!.fvarId! then continue
        defs := defs.push (j, t, hyp)
        break
    let defined := (List.range data.size).toArray.map fun j => defs.any (·.1 == j)
    let defHyps := defs.map (·.2.2)
    let mut bad := #[]
    for x in data do
      let ty ← whnfR (← inferType x)
      let ok ← if (← x.fvarId!.getDecl).binderInfo.isInstImplicit ||
          (← isClass? (← inferType x)).isSome then pure true
        else if defs.any (data[·.1]! == x) then pure true
        else if let .sort l := ty then
          pure (l.isZero || (← isLevelDefEq l Level.one))
        else isEnumerable data ty models
      unless ok do
        bad := bad.push s!"{(← x.fvarId!.getDecl).userName.eraseMacroScopes} : {← ppExpr (← inferType x)}"
    if !bad.isEmpty then
      let notTp := mkNot tp
      if let some (t, p) ← firstProof notTp directTacs o.cexHb then
        if ← kernelAccepts lps notTp p then
          let tt ← tacText directTacs t
          let srcs ← bothSrc (thmSrc decl lps notTp tt o.cexHb)
          return .ok (t, "direct", { decl, srcs, expect := #[(decl, notTp)] })
      return .error s!"non-enumerable data variables: {", ".intercalate bad.toList}"
    for u in us do
      if (← instantiateLevelMVars u).hasMVar then discard <| isLevelDefEq u Level.zero
    let notTpL ← instantiateMVars (mkNot tpL)
    -- v12 bench: carrier types for type variables with class constraints.
    let mut carriers : Array (Option (Array Expr)) := #[]
    for j in [:data.size] do
      let c ← withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := o.hb * 1000 }) <|
        tryCatchRuntimeEx (carrierCands data hyps j) (fun _ => pure none)
      carriers := carriers.push c
    -- Variables mentioned by the conclusion or the remaining hypotheses, closed under dependencies.
    let mut relSet : Array FVarId := #[]
    for e in #[body] ++ (← hyps.mapM fun x => inferType x) do
      relSet := relSet ++ data.filterMap fun x => if e.containsFVar x.fvarId! then some x.fvarId! else none
    for x in data.reverse do
      if relSet.contains x.fvarId! then
        let t ← inferType x
        relSet := relSet ++ data.filterMap fun y => if t.containsFVar y.fvarId! then some y.fvarId! else none
    let relevant := data.map (relSet.contains ·.fvarId!)
    let seeds ← match seed with
      | some w => elabSeeds data w
      | none => pure #[]
    let start ← IO.monoMsNow
    withLocalDeclD `h tpL fun h => do
      let mut tried := 0
      let mut s := 0
      let mut emptyRun := 0
      -- Instantiations whose statement evaluated to `true`/`false`. If none of the first ones does,
      -- evaluation is stuck (e.g. on `toList` of ranges) and more values will not help.
      let mut decided := 0
      let mut stuck := false
      while tried < o.cexCap && !stuck && (← IO.monoMsNow) - start < o.cexTimeMs do
        -- Generating the candidates (instance synthesis, model matching) gets its own budget: with
        -- many candidates per variable a single sum level can be huge.
        let some vs ← withCurrHeartbeats <|
            withTheReader Core.Context (fun c => { c with maxHeartbeats := o.hb * 1000 }) <|
              tryCatchRuntimeEx (some <$> assignmentsWithSum data s 0 #[] mined models relevant defined seeds carriers)
                (fun _ => pure none)
          | break
        -- A level can be empty while later ones are not, e.g. `n := 0` makes `Fin n` uninhabited.
        if vs.isEmpty then
          emptyRun := emptyRun + 1
          if emptyRun ≥ 6 then break
        else
          emptyRun := 0
        for v in vs.extract 0 (o.cexCap - tried) do
          if (← IO.monoMsNow) - start ≥ o.cexTimeMs then break
          if tried ≥ 40 && decided == 0 then stuck := true; break
          tried := tried + 1
          let v ← (defs.foldl (fun acc (j, t, _) => acc.set! j (t.replaceFVars data acc)) v).mapM instantiateMVars
          -- Discharge Prop-valued instance hypotheses such as `[LawfulBEq α]` by synthesis, since
          -- `decide` cannot handle them as premises.
          let mut kept := #[]
          let mut instFVars := #[]
          let mut instVals := #[]
          -- Source for each discharged instance: `_` (synthesized) or the `proveLaws` term.
          let mut instSrcs := #[]
          for hyp in hyps do
            let d ← hyp.fvarId!.getDecl
            if defHyps.contains hyp then
              let dty ← instantiateMVars (d.type.replaceFVars data v)
              let some (a, _) := defSides? dty | kept := kept.push hyp; continue
              if dty.isEq && (dty.getArg! 1).isAppOfArity ``BEq.beq 4 then
                let l := dty.getArg! 1
                let pf? ← try
                    some <$> mkAppOptM ``beq_self_eq_true #[l.getArg! 0, l.getArg! 1, none, a]
                  catch _ => pure none
                let some pf := pf? | kept := kept.push hyp; continue
                instFVars := instFVars.push hyp
                instVals := instVals.push pf
                instSrcs := instSrcs.push "(beq_self_eq_true _)"
              else
                instFVars := instFVars.push hyp
                instVals := instVals.push (← mkEqRefl a)
                instSrcs := instSrcs.push "rfl"
              continue
            if d.binderInfo.isInstImplicit then
              let ty ← instantiateMVars ((d.type.replaceFVars data v).replaceFVars instFVars instVals)
              if let some i ← (try synthInstance? ty catch _ => pure none) then
                instFVars := instFVars.push hyp
                instVals := instVals.push i
                instSrcs := instSrcs.push "_"
                continue
              -- A model instance (e.g. a non-lawful `BEq`) may still satisfy weaker laws.
              if !models.isEmpty && !ty.hasFVar then
                if let some (i, src) ← proveLaws ty lawTacs o.cexHb then
                  instFVars := instFVars.push hyp
                  instVals := instVals.push i
                  instSrcs := instSrcs.push src
                  continue
            kept := kept.push hyp
          let subst := data ++ instFVars
          let vals := v ++ instVals
          let hv ← unfoldModelProjs (← instantiateMVars <| (← mkForallFVars kept body).replaceFVars subst vals)
          -- Split mode: refute the conclusion and prove the remaining hypotheses separately, so that
          -- a hypothesis without a `Decidable` instance does not block evaluating the conclusion.
          let split ← do
            if body.hasAnyFVar (kept.map (·.fvarId!)).contains then pure false
            else kept.allM fun k => return !(← inferType k).hasAnyFVar (kept.map (·.fvarId!)).contains
          let c ← if split then unfoldModelProjs (← instantiateMVars (body.replaceFVars subst vals))
            else pure hv
          let probe ← quickDecide (mkNot c) o.cexHb
          -- Model relations: decide under `DecidableRel` instances for the models (v8.1).
          let dynTacs ← decTacsWith (← modelDecLets v models)
          let probe ← if probe.isNone && !dynTacs.isEmpty then do
              if (← firstProof (mkNot c) dynTacs o.cexHb).isSome then pure (some true)
              else if (← firstProof c dynTacs o.cexHb).isSome then pure (some false)
              else pure none
            else pure probe
          let probe ← if probe.isNone && mentionsGrindPreds c then do
              let pt ← grindPredTacs
              if (← firstProof (mkNot c) pt o.cexHb).isSome then pure (some true)
              else if (← firstProof c pt o.cexHb).isSome then pure (some false)
              else pure none
            else pure probe
          -- Std maps (v10): `simp` with the map definitions and ground evaluation.
          let mapTacs ← stdMapTacs c
          let probe ← if probe.isNone && !mapTacs.isEmpty then do
              if (← firstProof (mkNot c) mapTacs o.cexHb).isSome then pure (some true)
              else if (← firstProof c mapTacs o.cexHb).isSome then pure (some false)
              else pure none
            else pure probe
          -- Filters (Mathlib): unfold to membership and decide.
          let filtTacs ← filterTacs c
          let probe ← if probe.isNone && !filtTacs.isEmpty then do
              if (← firstProof (mkNot c) filtTacs o.cexHb).isSome then pure (some true)
              else if (← firstProof c filtTacs o.cexHb).isSome then pure (some false)
              else pure none
            else pure probe
          let dynTacs := dynTacs ++ mapTacs ++ filtTacs
          let clsTacs ← if probe.isNone then classRefuteTacs c models mined o.cexHb else pure #[]
          let probe := if probe.isNone && !clsTacs.isEmpty then some true else probe
          let cexTacs := clsTacs ++ cexTacs ++ dynTacs
          let premTacs := premTacs ++ dynTacs
          if probe.isSome then decided := decided + 1
          if (← IO.getEnv "HYPCHECK_DEBUG").isSome then
            IO.eprintln s!"try {← v.mapM fun e => ppExpr e}: {← ppExpr c} quick={probe}"
          if probe == some false then s := s; continue
          let instDecl := decl.str "inst"
          -- With the source and statements of the premise declarations (split mode).
          let found? : Option (String × Expr × Array (Name × Expr × String)) ← if split then do
              let kq? ← if probe == some true then kernelDecideProof? (mkNot c) else pure none
              let some (tac, q) ← (match kq? with
                | some q => pure (some ("decide +kernel", q))
                | none => firstProof (mkNot c) cexTacs o.cexHb) | pure none
              let mut premParts := #[]
              let mut prems := #[]
              for k in kept do
                let pk ← unfoldModelProjs (← instantiateMVars ((← inferType k).replaceFVars subst vals))
                let pDecl := decl.str s!"prem{prems.size}"
                let pp? ← match ← firstProof pk premTacs o.cexHb with
                  | some (n, pp) => pure (some (pp, ← tacText premTacs n))
                  | none => if models.isEmpty then pure none else proveLaws pk lawTacs o.cexHb
                let some (pp, pSrc) := pp? | break
                premParts := premParts.push (pDecl, pk, pSrc)
                prems := prems.push pp
              if prems.size < kept.size then pure none else
              let pr ← withLocalDeclD `hh hv fun hh => mkLambdaFVars #[hh] (mkApp q (mkAppN hh prems))
              pure (some (tac, pr, premParts))
            else do
              let kq? ← if probe == some true then kernelDecideProof? (mkNot hv) else pure none
              match kq? with
              | some q => pure (some ("decide +kernel", q, #[]))
              | none => pure ((← firstProof (mkNot hv) cexTacs o.cexHb).map fun (t, p) => (t, p, #[]))
          if (← IO.getEnv "HYPCHECK_DEBUG").isSome && probe == some true then
            IO.eprintln s!"  found={found?.map (·.1)} split={split} kept={kept.size}"
          if let some (tac, p, premParts) := found? then
            let lam := (← mkLambdaFVars kept (mkAppN h rest)).replaceFVars subst vals
            let proof ← instantiateMVars (← mkLambdaFVars #[h] (mkApp p lam))
            let ok ← kernelAccepts [] notTpL proof
            if (← IO.getEnv "HYPCHECK_DEBUG").isSome then
              IO.eprintln s!"  kernel={ok}"
              unless ok do
                try withoutModifyingEnv <| addDecl <| .thmDecl { name := `_hypCheck_tmp, levelParams := [], type := notTpL, value := proof }
                catch e => IO.eprintln s!"  kernel error: {(← e.toMessageData.toString).take 1500}"
            if ok then
              let names ← data.mapM fun x => return (← x.fvarId!.getDecl).userName.eraseMacroScopes
              let w ← (names.zip v).toList.mapM fun (n, e) => do
                match models.find? (·.2.1 == e) with
                | some (_, _, src) => return s!"{n} := «{src}»"
                | none => return s!"{n} := {← ppExpr e}"
              -- `D.inst` refutes the instance, `D` applies `h : T'` to the witness.
              let instStmt := mkNot (if split then c else hv)
              let tt ← tacText cexTacs tac
              -- First rendering (v7.1): `absurd (@hc_h …) (by tac)`, with the premises proved inline.
              -- No instantiated statement is printed, so nothing has to re-elaborate except the
              -- witness values (printed statements lose model instances and index proofs).
              let absurdSrcs ← bothSrc do
                let mut args := #[]
                for x in rest do
                  if let some j := data.idxOf? x then
                    -- A variable set by a discharged equation premise is inferred from its `rfl`
                    -- (v9): printed, it can lose a model instance (`ofRat v` in a model field).
                    if defs.any fun (k, _, hy) => k == j && instFVars.contains hy then
                      args := args.push "_"; continue
                    -- Model values from their source text: printed elaborated instances (default
                    -- methods, implicit lambdas) often do not parse back.
                    match models.find? (·.2.1 == v[j]!) with
                    | some (_, mv, src) => args := args.push s!"({src} : {← ppSrc (← inferType mv)})"
                    | none => args := args.push s!"({← ppSrc v[j]!})"
                  else if let some j := instFVars.idxOf? x then args := args.push instSrcs[j]!
                  else if let some j := kept.idxOf? x then
                    args := args.push (if split then s!"({premParts[j]!.2.2})" else s!"hc_k{j}")
                let app := s!"@hc_h {" ".intercalate args.toList}"
                let arg := if split || kept.isEmpty then s!"({app})" else
                  s!"(fun {" ".intercalate ((List.range kept.size).map (s!"hc_k{·}"))} => {app})"
                thmSrc decl [] notTpL s!"fun hc_h => absurd {arg} ({tt})" (some (o.cexHb * 20))
              let srcs ← bothSrc do
                let mut args := #[]
                for x in rest do
                  if let some j := data.idxOf? x then args := args.push s!"({← ppSrc v[j]!})"
                  else if let some j := instFVars.idxOf? x then args := args.push instSrcs[j]!
                  else if let some j := kept.idxOf? x then
                    args := args.push (if split then toString (decl.str s!"prem{j}") else s!"hc_k{j}")
                let app := s!"@hc_h {" ".intercalate args.toList}"
                let arg := if split || kept.isEmpty then s!"({app})" else
                  s!"(fun {" ".intercalate ((List.range kept.size).map (s!"hc_k{·}"))} => {app})"
                let mut premSrc := ""
                for (pd, pk, pt) in premParts do premSrc := premSrc ++ (← thmSrc pd [] pk pt o.cexHb)
                return (← thmSrc instDecl [] instStmt tt o.cexHb) ++ premSrc ++
                  (← thmSrc decl [] notTpL s!"fun hc_h => {instDecl} {arg}")
              let expect := #[(instDecl, instStmt)] ++ premParts.map (fun (pd, pk, _) => (pd, pk)) ++
                #[(decl, notTpL)]
              return .ok (tac, ", ".intercalate w, { decl, srcs := absurdSrcs ++ srcs, expect })
        s := s + 1
      if stuck then return .error s!"evaluation stuck: none of the first {tried} instantiations could be evaluated"
      -- No candidate at all (e.g. `USize`, whose width `System.Platform.numBits` doesn't evaluate):
      -- try the direct tactics, as for non-enumerable variables.
      if tried == 0 then
        let notTp := mkNot tp
        if let some (t, p) ← firstProof notTp directTacs o.cexHb then
          if ← kernelAccepts lps notTp p then
            let tt ← tacText directTacs t
            let srcs ← bothSrc (thmSrc decl lps notTp tt o.cexHb)
            return .ok (t, "direct", { decl, srcs, expect := #[(decl, notTp)] })
      return .error s!"no counterexample among {tried} small instantiations"


/-- Builds `∀ rest', body` with `x := mkAppN pder indep` from the telescope `order` (which starts
with `indep`, so the substituted proof only mentions variables already in scope), together with its
proof from `tConst`. -/
partial def restateGo (tConst x s body : Expr) (xs order : Array Expr) (k : Nat)
    (newVars : Array Expr) : MetaM (Expr × Expr) := do
  let olds := order.extract 0 k
  let sub (e : Expr) := (e.replaceFVar x s).replaceFVars olds newVars
  if h : k < order.size then
    let d ← order[k].fvarId!.getDecl
    withLocalDecl d.userName d.binderInfo (sub d.type) fun v =>
      restateGo tConst x s body xs order (k + 1) (newVars.push v)
  else
    return (← mkForallFVars newVars (sub body), ← mkLambdaFVars newVars (mkAppN tConst (xs.map sub)))

/-- `T` without the dependent hypothesis `xs[i]`, which is replaced by `pder : ∀ indep, Hᵢ`. -/
def restateDependent (tConst : Expr) (xs : Array Expr) (i : Nat) (indep : Array Expr)
    (body pder : Expr) : MetaM (Expr × Expr) := do
  let x := xs[i]!
  let order := indep ++ xs.filter fun y => y != x && !indep.contains y
  restateGo tConst x (mkAppN pder indep) body xs order 0 #[]

/-- Proof repair of a non-dependent row (v12): the library proof of `T` without binder `i`, kernel-checked against
`T'`. Returns success and diagnostics. -/
def tryRepair (ci : TheoremVal) (xs : Array Expr) (i : Nat) (body : Expr) (hb holes timeMs depth : Nat)
    (holeTacs : Array (String × TSyntax `tactic)) : TermElabM (Bool × Json) := do
  let some x := xs[i]? | return (false, Json.null)
  let m0 ← IO.monoMsNow
  let rest := xs.eraseIdxIfInBounds i
  let tp ← mkForallFVars rest body
  let pf := (mkAppN ci.value xs).headBeta
  if !pf.containsFVar x.fvarId! then
    return (← kernelAccepts ci.levelParams tp (← mkLambdaFVars rest pf), Json.mkObj [("unused", toJson true)])
  let (r?, st) ← (repairE #[x.fvarId!] (rest.map (·.fvarId!)) holeTacs hb holes true pf 0 depth).run
    { deadline := m0 + timeMs }
  let ok ← match r? with
    | none => pure false
    | some v => if v.containsFVar x.fvarId! then pure false else
        kernelAccepts ci.levelParams tp (← mkLambdaFVars rest v)
  return (ok, Json.mkObj [("holes", toJson st.tried), ("closed", toJson st.closed), ("unfolded", toJson st.unfolded),
    ("surgeries", toJson st.surgeries)])

/-- Tactics parsed at run time from source (v11, CSLib port): Mathlib/Aesop syntax is not known when
this file is compiled (it imports only `Lean`), so quotations can't be used. A tactic that does not parse
in the analysed environment (e.g. without Mathlib) is skipped. -/
def parsedTacs (srcs : List (String × String)) : TermElabM (Array (String × TSyntax `tactic)) := do
  let mut out := #[]
  for (n, src) in srcs do
    match Parser.runParserCategory (← getEnv) `tactic src with
    | .ok stx => out := out.push (n, ⟨stx⟩)
    | .error _ => pure ()
  return out

/-- The `--extra-tacs` lines of one kind (`remove`, `cex` or `prem`); unparsable tactics are reported once. -/
def extraTacsOf (o : Opts) (kind : String) : TermElabM (Array (String × TSyntax `tactic)) := do
  let some f := o.extraTacs? | return #[]
  let mut out := #[]
  for l in (← IO.FS.lines f) do
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    let some (k, rest) := (match l.splitOn " " with | k :: r => some (k, " ".intercalate r) | [] => none) | continue
    unless k == kind do continue
    match rest.splitOn " := " with
    | n :: src@(_ :: _) =>
      match Parser.runParserCategory (← getEnv) `tactic (" := ".intercalate src) with
      | .ok stx => out := out.push (n.trimAscii.toString, ⟨stx⟩)
      | .error e => IO.eprintln s!"--extra-tacs: cannot parse {n}: {e}"
    | _ => IO.eprintln s!"--extra-tacs: bad line {l}"
  return out

unsafe def checkTheorem (o : Opts) (ci : TheoremVal) (only? : Option (Array Nat) := none)
    (models : Models := #[]) (witnesses : Std.HashMap Nat String := {}) :
    TermElabM (Array (Json × Option ProofBlock)) := do
  let lawTacs := #[
    ("decide", ← `(tactic| decide)),
    ("omega", ← `(tactic| (intros; omega))),
    ("simp_all", ← `(tactic| (intros; simp_all; done))),
    ("simp_all <;> omega", ← `(tactic| (intros; simp_all <;> omega))),
    ("grind", ← `(tactic| grind)),
    -- range models: unfold `UpwardEnumerable.LT`/`LE` and the class projections (v8.1)
    ("range-unfold", ← `(tactic| (intros; simp_all [Std.PRange.UpwardEnumerable.LT,
      Std.PRange.UpwardEnumerable.LE, Std.PRange.succMany?, Std.PRange.succ?] <;> omega))),
    ("range-unfold-split", ← `(tactic| (intros; simp_all [Std.PRange.UpwardEnumerable.LT,
      Std.PRange.UpwardEnumerable.LE, Std.PRange.succMany?, Std.PRange.succ?] <;>
      (repeat' split) <;> simp_all <;> omega)))]
  -- v12 removal pool (from a benchmark): cheapest first, stop at the
  -- first success. `lia` replaces `omega` where it exists (it finds a superset); `aesop` is dropped (expensive,
  -- nothing unique); Mathlib closers parse only where Mathlib is imported. Level search adds `exact?`.
  let liaT ← parsedTacs [("lia", "(intros; lia)"), ("simp_all <;> lia", "(intros; simp_all <;> lia)")]
  let arith ← if liaT.size == 2 then pure liaT else pure #[
    ("omega", ← `(tactic| (intros; omega))), ("simp_all <;> omega", ← `(tactic| (intros; simp_all <;> omega)))]
  let removeTacs := (← parsedTacs [("assumption", "(intros; assumption)"), ("trivial", "(intros; trivial)"),
      ("infer_instance", "(intros; infer_instance)"), ("rfl", "(intros; rfl)")]) ++ #[
    ("contradiction", ← `(tactic| (intros; contradiction)))] ++ (← parsedTacs [
      ("decide", "(intros; decide)"), ("solve_by_elim", "(intros; solve_by_elim)"), ("simp", "(intros; simp; done)")]) ++
    arith.extract 0 1 ++ #[("simp_all", ← `(tactic| (intros; simp_all; done)))] ++ arith.extract 1 2 ++ #[
    ("grind", ← `(tactic| (intros; grind))),
    ("simp_all <;> grind", ← `(tactic| (intros; simp_all <;> grind)))] ++ (← parsedTacs [
    ("tauto", "(intros; tauto)"),
    ("linarith", "(intros; linarith)"),
    ("positivity", "(intros; positivity)"),
    ("norm_num", "(intros; norm_num at *; done)")]) ++
    (← extraTacsOf o "remove") ++
    (← if o.level ≥ 1 && !o.noExact then parsedTacs [("exact?", "(intros; exact?)")] else pure #[])
  let removeTacs ← match o.tacs? with
    | none => pure removeTacs
    | some f => do
      let lines := (← IO.FS.lines f).filter fun l => !l.trimAscii.isEmpty && !l.startsWith "#"
      let mut out := #[]
      for l in lines do
        match l.splitOn " := " with
        | n :: rest =>
          let src := " := ".intercalate rest
          match Parser.runParserCategory (← getEnv) `tactic src with
          | .ok stx => out := out.push (n.trimAscii.toString, ⟨stx⟩)
          | .error e => IO.eprintln s!"--tacs: cannot parse {n}: {e}"
        | [] => pure ()
      pure out
  let cexTacs := #[
    ("decide", ← `(tactic| decide)),
    ("decide +kernel", ← `(tactic| decide +kernel))] ++ (← grindPredTacs) ++ #[
    ("simp", ← `(tactic| simp)),
    ("omega", ← `(tactic| omega)),
    ("simp <;> omega", ← `(tactic| (simp <;> omega))),
    ("simp <;> decide", ← `(tactic| (simp <;> decide))),
    -- Equality of types that derive `BEq`/`LawfulBEq` but not `DecidableEq` (e.g. grind's `Poly`).
    ("decide-beq", ← `(tactic| (have _i : ∀ (α : Type) [BEq α] [LawfulBEq α], DecidableEq α :=
      @instDecidableEqOfLawfulBEq; decide))),
    ("to-decidable", ← `(tactic| (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))),
    -- `USize`/`ISize`: `decide` is stuck on `System.Platform.numBits`; split on its two values (v8).
    ("numBits", ← `(tactic| (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
      simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj,
        USize.toBitVec_ofNat, ← BitVec.toNat_inj, BitVec.toNat_ofNat, USize.toNat_toBitVec,
        ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add, USize.toNat_mul, USize.toNat_sub,
        USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
        ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first | done | omega | decide)))] ++ (← parsedTacs [
    -- v11 (CSLib): `nofun` refutes instances of inductive predicates with no matching constructor
    -- (e.g. `(bvar 0).LC`), `norm_num` evaluates Mathlib numerals/sets.
    ("norm_num", "norm_num"),
    ("nofun", "nofun"),
    ("simp-sets", "simp [Set.ext_iff, Set.mem_def] <;> decide")]) ++ (← extraTacsOf o "cex")
  let premTacs := #[
    ("to-decidable", ← `(tactic| (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))),
    ("decide", ← `(tactic| decide)),
    ("decide +kernel", ← `(tactic| decide +kernel)),
    ("rfl", ← `(tactic| rfl)),
    -- `WF` of tree maps built by `ofList`, for any comparison (v10): the library's `WF.ofList` needs
    -- `TransCmp`, but `Impl.WF` holds by construction; instances passed as `id _` so that they
    -- are unified, not synthesized (`instOrdNat` would be found instead of the model's `Ord`).
    ("tree-wf", ← `(tactic| ((repeat (first | apply Std.TreeSet.Raw.WF.mk | apply Std.TreeMap.Raw.WF.mk | apply Std.DTreeMap.Raw.WF.mk)); (first | exact @Std.DTreeMap.Internal.Impl.WF.insertMany _ _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact @Std.DTreeMap.Internal.Impl.WF.constInsertMany _ (id _) _ _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact @Std.DTreeMap.Internal.Impl.WF.constInsertManyIfNewUnit _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _)))))] ++ (← grindPredTacs) ++ #[
    ("decide-beq", ← `(tactic| (have _i : ∀ (α : Type) [BEq α] [LawfulBEq α], DecidableEq α :=
      @instDecidableEqOfLawfulBEq; decide))),
    ("simp", ← `(tactic| simp)),
    ("omega", ← `(tactic| omega)),
    ("grind", ← `(tactic| grind))] ++ (← parsedTacs [
    -- v11 (CSLib): premises of inductive predicates on literal terms (`(fvar 0).LC`), Mathlib numerals.
    ("constructor", "(repeat' constructor) <;> done"),
    ("aesop", "aesop"),
    ("norm_num", "norm_num")]) ++ (← extraTacsOf o "prem")
  let directTacs := #[
    ("simp_all", ← `(tactic| (simp_all; done))),
    ("grind", ← `(tactic| grind))]
  let tConst := mkConst ci.name (ci.levelParams.map mkLevelParam)
  -- From the whole statement: the dropped hypothesis is often the one mentioning the boundary.
  let mined ← mineValues ci.type
  forallTelescope ci.type fun xs body => do
    let mut out := #[]
    for h : i in [:xs.size] do
      let x := xs[i]
      let d ← x.fvarId!.getDecl
      unless ← isProp d.type do continue
      if let some only := only? then unless only.contains i do continue
      let hi := (← instantiateMVars d.type).consumeTypeAnnotations
      let laterDep ← (xs.extract (i+1) xs.size).anyM fun y => return (← inferType y).containsFVar x.fvarId!
      let rest := xs.eraseIdx i
      let isDep := laterDep || body.containsFVar x.fvarId!
      if o.onlyDependent && !isDep then continue
      let decl := proofDecl ci.name i
      let lps := ci.levelParams
      if o.matrix then
        -- bench matrix mode: every removal tactic independently (kernel-checked), then the
        -- counterexample search only if none succeeded; no proof printing.
        let mut dset := #[x.fvarId!]
        for y in xs.extract (i+1) xs.size do
          if (← inferType y).hasAnyFVar dset.contains then dset := dset.push y.fvarId!
        let indep := xs.filter fun y => !dset.contains y.fvarId!
        let goal ← if isDep then mkForallFVars indep hi else
          withLocalDeclD `hn (mkNot hi) fun hn => mkForallFVars (xs.set i hn) body
        let mut mx : Array Json := #[]
        let mut anyOk := false
        let mut firstOk : Option String := none
        let r0 ← IO.monoMsNow
        for (n, t) in removeTacs do
          if o.first && anyOk then break
          let h0 ← IO.getNumHeartbeats
          let m0 ← IO.monoMsNow
          let p? ← proveWith goal t o.hb
          let ok ← match p? with
            | none => pure false
            | some p => kernelAccepts lps goal p
          let h1 ← IO.getNumHeartbeats
          let m1 ← IO.monoMsNow
          if ok then
            anyOk := true
            if firstOk.isNone then firstOk := some n
          -- reuse test: constants of helper modules (`RU_*`, agents' hand files) the proof uses
          let uses : Array String ← match ok, p? with
            | true, some p => do
              let env ← getEnv
              pure <| p.getUsedConstants.filterMap fun c => do
                let i ← env.getModuleIdxFor? c
                let m ← env.header.moduleNames[i.toNat]?
                if m.toString.startsWith "RU_" then some s!"{m}:{c}" else none
            | _, _ => pure #[]
          mx := mx.push (Json.mkObj ([("t", toJson n), ("ok", toJson ok), ("ms", toJson (m1 - m0)),
            ("hb", toJson ((h1 - h0) / 1000))] ++ (if uses.isEmpty then [] else [("uses", toJson uses)])))
        if o.repair && !(o.first && anyOk) then
          let m0 ← IO.monoMsNow
          let (ok, info) ← if isDep then pure (false, Json.mkObj [("skip", toJson "dependent")]) else do
            let pf := (mkAppN ci.value xs).headBeta
            if !pf.containsFVar x.fvarId! then
              pure (true, Json.mkObj [("unused", toJson true)])
            else
            let holeTacs ← parsedTacs [("infer_instance", "(intros; infer_instance)"), ("assumption", "assumption"), ("trivial", "(intros; trivial)"),
              ("omega", "(intros; omega)"), ("simp_all", "(intros; simp_all; done)"),
              ("solve_by_elim", "(intros; solve_by_elim)"), ("grind", "(intros; grind)")]
            let rest := xs.eraseIdx i
            let (r?, st) ← (repairE #[x.fvarId!] (rest.map (·.fvarId!)) holeTacs o.repairHb o.repairHoles true pf 0 o.repairDepth).run
              { deadline := m0 + o.repairTimeMs }
            let ok ← match r? with
              | none => pure false
              | some v =>
                if v.containsFVar x.fvarId! then pure false else
                kernelAccepts lps (← mkForallFVars rest body) (← mkLambdaFVars rest v)
            let blocks := st.blocks.toArray.qsort (fun a b => a.2 > b.2) |>.extract 0 6
            pure (ok, Json.mkObj [("holes", toJson st.tried), ("closed", toJson st.closed),
              ("inlined", toJson st.inlined), ("unfolded", toJson st.unfolded), ("surgeries", toJson st.surgeries), ("result", toJson r?.isSome),
              ("blocks", Json.arr (blocks.map fun (k, n) => Json.arr #[toJson k, toJson n])),
              ("timeout", toJson (decide ((← IO.monoMsNow) > m0 + o.repairTimeMs)))])
          let m1 ← IO.monoMsNow
          mx := mx.push (Json.mkObj [("t", toJson "repair"), ("ok", toJson ok), ("ms", toJson (m1 - m0)),
            ("hb", toJson 0), ("info", info)])
          if ok then
            anyOk := true
            if firstOk.isNone then firstOk := some "repair"
        let remMs := (← IO.monoMsNow) - r0
        let mut fields : List (String × Json) := [
          ("theorem", toString ci.name), ("idx", i), ("name", toString d.userName.eraseMacroScopes),
          ("binder", binderStr d.binderInfo), ("type", toString (← ppExpr d.type)),
          ("dependent", toJson isDep), ("mx", Json.arr mx), ("rem_ms", toJson remMs)]
        if anyOk then
          fields := fields ++ [("status", toJson "removable"), ("tactic", toJson firstOk)]
        else if o.noCex then
          fields := fields ++ [("status", toJson "unresolved"), ("reason", toJson "no-cex")]
        else
          let c0 ← IO.monoMsNow
          let tp ← if isDep then pure goal else mkForallFVars rest body
          let nRest := if isDep then indep.size else rest.size
          let res ← findCounterexample o decl ci.levelParams tp nRest cexTacs premTacs directTacs mined models lawTacs none
          let cexMs := (← IO.monoMsNow) - c0
          match res with
          | .ok (tac, w, _) => fields := fields ++ [("status", toJson "necessary"), ("tactic", toJson tac),
              ("witness", toJson w), ("cex_ms", toJson cexMs)]
          | .error r => fields := fields ++ [("status", toJson "unresolved"), ("reason", toJson r),
              ("cex_ms", toJson cexMs)]
        out := out.push (Json.mkObj fields, none)
        continue
      let verdict ← do
        if isDep then
          -- `x` together with every later binder that (transitively) depends on it.
          let mut dset := #[x.fvarId!]
          for y in xs.extract (i+1) xs.size do
            if (← inferType y).hasAnyFVar dset.contains then dset := dset.push y.fvarId!
          let indep := xs.filter fun y => !dset.contains y.fvarId!
          let gder ← mkForallFVars indep hi
          if let some (tac, pder) ← (if only?.isSome && !o.redo then pure none else firstProof gder removeTacs o.hb) then
            let (ty, pf) ← restateDependent tConst xs i indep body pder
            if ← kernelAccepts ci.levelParams ty pf then
              -- `D.der : ∀ indep, Hᵢ`; `D` is the restated theorem, proved from `T` and `D.der`.
              let derDecl := decl.str "der"
              let (ty', _) ← restateDependent tConst xs i indep body (mkConst derDecl (usedLevels lps gder))
              let order := indep ++ xs.filter fun y => y != x && !indep.contains y
              let nm (y : Expr) := s!"hc_x{order.idxOf y}"
              let args := (List.range xs.size).map fun j =>
                if j == i then s!"(@{derDecl} {" ".intercalate (indep.toList.map nm)})" else nm xs[j]!
              let intro := if order.isEmpty then "" else s!"intro {" ".intercalate (order.toList.map nm)}\n  "
              let tt ← tacText removeTacs tac
              -- `D.der` must exist while printing, so that its implicit arguments get an `@`.
              let derLps := lps.filter (collectLevelParams {} gder).params.contains
              let srcs ← withoutModifyingEnv do
                try addDecl (.thmDecl { name := derDecl, levelParams := derLps, type := gder, value := pder })
                catch _ => pure ()
                bothSrc do
                  return (← thmSrc derDecl lps gder tt o.hb) ++
                    (← thmSrc decl lps ty' s!"by\n  {intro}exact @{privateToUserName ci.name} {" ".intercalate args}")
              -- Fallback (v7.1): `D : ∀ indep, Hᵢ` alone, for restated theorems whose statement does
              -- not print back (proof terms, `▸` casts). This is the verdict itself.
              let fb ← thmSrc decl lps gder tt o.hb
              pure { status := "removable", dependent := true, derivable := true, tactic := tac,
                     proof? := some { decl, srcs, expect := #[(derDecl, gder), (decl, ty')],
                                      fallbacks := #[(fb, #[(decl, gder)])] } : Verdict }
            else
              pure { status := "unresolved", dependent := true,
                     reason := "derived, but the restated theorem was rejected by the kernel" }
          else if o.noCex then
            pure { status := "unresolved", dependent := true, reason := "goal=removable (no counterexample search)" }
          else
            match ← findCounterexample o decl ci.levelParams gder indep.size cexTacs premTacs directTacs mined models lawTacs (witnesses.get? i) with
            | .ok (tac, w, pb) => pure { status := "necessary", dependent := true, tactic := tac, witness := w, proof? := some pb }
            | .error r => pure { status := "unresolved", dependent := true, reason := r }
        else
          let tp ← mkForallFVars rest body
          let removable ← if only?.isSome && !o.redo then pure none else withLocalDeclD `hn (mkNot hi) fun hn => do
            let gneg ← mkForallFVars (xs.set i hn) body
            let some (tac, pneg) ← firstProof gneg removeTacs o.hb | return none
            let f ← mkLambdaFVars #[x] (mkAppN tConst xs)
            let g ← mkLambdaFVars #[hn] (mkAppN pneg (xs.set i hn))
            let val ← mkLambdaFVars rest (mkApp4 (mkConst ``Classical.byCases) hi body f g)
            if ← kernelAccepts ci.levelParams tp val then return some (tac, gneg) else return none
          if let some (tac, gneg) := removable then
            let gder ← mkForallFVars rest hi
            let der? ← firstProof gder removeTacs o.hb
            -- `D.gneg : ∀ rest, ¬Hᵢ → C` by the tactic; `D : T'` by cases on `Hᵢ`.
            let gnegDecl := decl.str "gneg"
            let nm (j : Nat) := if j == i then "hc_h" else s!"hc_x{j}"
            let others := (List.range xs.size).filter (· != i)
            let intro := if others.isEmpty then "" else
              s!"intro {" ".intercalate (others.map nm)}\n  "
            let argsWith (h : String) := " ".intercalate ((List.range xs.size).map fun j => if j == i then h else nm j)
            let tt ← tacText removeTacs tac
            let dtt? ← der?.mapM fun (dtac, _) => tacText removeTacs dtac
            let srcs ← bothSrc do
              let src := (← thmSrc gnegDecl lps gneg tt o.hb) ++
                (← thmSrc decl lps tp (s!"by\n  {intro}exact Classical.byCases (fun hc_h => @{privateToUserName ci.name} {argsWith "hc_h"})" ++
                  s!" (fun hc_hn => @{gnegDecl} {argsWith "hc_hn"})"))
              match dtt? with
              | some dtt => return src ++ (← thmSrc (decl.str "derivable") lps gder dtt o.hb)
              | none => return src
            let expect := #[(gnegDecl, gneg), (decl, tp)] ++
              (if der?.isSome then #[(decl.str "derivable", gder)] else #[])
            pure { status := "removable", derivable := der?.isSome, tactic := tac,
                   proof? := some { decl, srcs, expect } }
          else
            -- v12: proof repair (level search/thorough). Its proof is stored by `scripts/repair_proofs.sh`
            -- (`hc_repair% T i`), not here, so the row has no `proof_ok` and `merge_tool.py` skips it.
            let repaired ← if o.level == 0 || o.noProofs || (only?.isSome && !o.redo) then pure false else do
              let holeTacs ← parsedTacs [("infer_instance", "(intros; infer_instance)"), ("assumption", "assumption"), ("trivial", "(intros; trivial)"),
                ("omega", "(intros; omega)"), ("simp_all", "(intros; simp_all; done)"),
                ("solve_by_elim", "(intros; solve_by_elim)"), ("grind", "(intros; grind)")]
              let (ok, _) ← if o.level ≥ 2 then tryRepair ci xs i body 600 120 30000 3 holeTacs
                else tryRepair ci xs i body 300 60 15000 2 holeTacs
              pure ok
            if repaired then
              pure { status := "removable", tactic := "repair",
                     note := "proof repair (kernel-checked); stored proof: scripts/repair_proofs.sh" }
            else if o.noCex then
              pure { status := "unresolved", reason := "goal=removable (no counterexample search)" }
            else
            match ← findCounterexample o decl ci.levelParams tp rest.size cexTacs premTacs directTacs mined models lawTacs (witnesses.get? i) with
            | .ok (tac, w, pb) => pure { status := "necessary", tactic := tac, witness := w, proof? := some pb }
            | .error r => pure { status := "unresolved", reason := r }
      let mut fields : List (String × Json) := [
        ("theorem", toString ci.name), ("idx", i), ("name", toString d.userName.eraseMacroScopes),
        ("binder", binderStr d.binderInfo), ("type", toString (← ppExpr d.type)),
        ("status", verdict.status)]
      if verdict.dependent then fields := fields ++ [("dependent", toJson true)]
      if let some b := verdict.derivable then fields := fields ++ [("derivable", toJson b)]
      if let some t := verdict.tactic then fields := fields ++ [("tactic", toJson t)]
      if let some w := verdict.witness then fields := fields ++ [("witness", toJson w)]
      if let some r := verdict.reason then fields := fields ++ [("reason", toJson r)]
      if let some n := verdict.note then fields := fields ++ [("note", toJson n)]
      out := out.push (Json.mkObj fields, verdict.proof?)
    return out

/-- `Decidable` instances for grind's recursive predicates (v9.2), by recursion on the data, so that
`decide +kernel` and the kernel probe evaluate statements such as `(p.append q).NonNeg` or
`(Poly.combine p q).NonnegCoeffs`. Added to the environment at startup when `Init.Grind` is loaded,
and written after the imports of every proofs file. -/
def grindDecSrc : String := r#"
noncomputable instance HypCheckDec.ppolyNonNeg (p : Lean.Grind.CommRing.PPoly) : Decidable p.NonNeg :=
  Lean.Grind.CommRing.PPoly.rec (motive := fun p => Decidable p.NonNeg)
    (fun k => (inferInstance : Decidable (0 ≤ k)))
    (fun k _ _ _ ih => @instDecidableAnd (0 ≤ k) _ inferInstance ih) p
noncomputable instance HypCheckDec.ppolyDeg (B D : Nat) (p : Lean.Grind.CommRing.PPoly) : Decidable (p.Deg B D) :=
  Lean.Grind.CommRing.PPoly.rec (motive := fun p => Decidable (p.Deg B D))
    (fun _ => isTrue trivial)
    (fun _ _ v _ ih => @instDecidableAnd (Lean.Grind.CommRing.PPoly.dsum B v ≤ D) _ (Nat.decLe _ _) ih) p
noncomputable instance HypCheckDec.polyNonnegCoeffs (p : Lean.Grind.CommRing.Poly) : Decidable p.NonnegCoeffs :=
  Lean.Grind.CommRing.Poly.rec (motive := fun p => Decidable p.NonnegCoeffs)
    (fun c => if h : c ≥ 0 then isTrue (.num c h) else isFalse (fun hc => by cases hc; contradiction))
    (fun a m p ih => if h : a ≥ 0 then
        (match ih with
         | isTrue hp => isTrue (.add a m p h hp)
         | isFalse hp => isFalse (fun hc => by cases hc; contradiction))
      else isFalse (fun hc => by cases hc; contradiction)) p
noncomputable instance HypCheckDec.polyNonnegList (ps : List Lean.Grind.CommRing.Poly) : Decidable (Lean.Grind.CommRing.Poly.NonnegList ps) :=
  List.rec (motive := fun ps => Decidable (Lean.Grind.CommRing.Poly.NonnegList ps)) (isTrue trivial)
    (fun p _ ih => @instDecidableAnd p.NonnegCoeffs _ inferInstance ih) ps
noncomputable instance HypCheckDec.klistAllZero {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (ls : Lean.Grind.CommRing.KList) : Decidable (ls.AllZero ctx) :=
  Lean.Grind.CommRing.KList.rec (motive := fun ls => Decidable (ls.AllZero ctx)) (isTrue trivial)
    (fun _ _ q _ ih => @instDecidableAnd (q.denote ctx = 0) _ inferInstance ih) ls
noncomputable instance HypCheckDec.mlistAllZero {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (ls : Lean.Grind.CommRing.MList) : Decidable (ls.AllZero ctx) :=
  Lean.Grind.CommRing.MList.rec (motive := fun ls => Decidable (ls.AllZero ctx)) (isTrue trivial)
    (fun _ q _ ih => @instDecidableAnd (q.denote ctx = 0) _ inferInstance ih) ls
noncomputable instance HypCheckDec.invAtomsOk {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (l : Lean.Grind.CommRing.InvAtoms) : Decidable (Lean.Grind.CommRing.InvAtoms.ok ctx l) :=
  List.rec (motive := fun l => Decidable (Lean.Grind.CommRing.InvAtoms.ok ctx l)) (isTrue trivial)
    (fun yx _ ih => @instDecidableAnd (yx.2.denote ctx * yx.1.denote ctx = 1) _ inferInstance ih) l
noncomputable instance HypCheckDec.invVarsOk {α : Type} [Lean.Grind.Field α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (invs : Lean.Grind.CommRing.InvVars) : Decidable (invs.ok ctx) :=
  (inferInstance : Decidable (invs.denoteVars ctx = invs.denoteInvs))
noncomputable instance HypCheckDec.ppolyDegList (B D : Nat) (ps : List Lean.Grind.CommRing.PPoly) : Decidable (Lean.Grind.CommRing.PPoly.DegList B D ps) :=
  (inferInstance : Decidable (∀ p ∈ ps, p.Deg B D))
"#

/-- Elaborates `pb.src` on top of `env` and checks that every declaration in `pb.expect` was added
without `sorry` and has the expected statement (up to definitional equality). `none` if so. -/
unsafe def verifyBlock (env : Environment) (ctx : Core.Context) (pb : ProofBlock) (src : String)
    (expect : Array (Name × Expr) := pb.expect) : IO (Option String) := do
  -- `Elab.process` collects the messages of all snapshots, including asynchronous proofs.
  let (env', msgs) ← Elab.process src env ctx.options "<proof>"
  for m in msgs.toList do
    let t ← m.data.toString
    if m.severity == .error || t.contains "sorry" then
      return some s!"{m.pos.line}:{m.pos.column}: {t.take 500}"
  let check : MetaM (Option String) := do
    for (n, ty) in expect do
      -- Helper declarations are optional (renderings differ in which ones they use); the main one
      -- is required.
      -- Under `--olean-level server` the environment counts as a `module`, where declarations are private
      -- by default: look the name up in its private form too.
      let some ci := (env'.find? n).orElse (fun _ => env'.find? (mkPrivateName env' n))
        | if n == pb.decl then return some s!"{n} was not added" else continue
      if ci.value?.any (·.hasSorry) then return some s!"{n} uses sorry"
      unless ci.type == ty || (← isDefEq ci.type ty) do
        return some s!"{n}: statement differs, elaborated as {← ppExpr ci.type}"
    return none
  let (r, _) ← (check.run' {}).toIO ctx { env := env' }
  return r

unsafe def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs {} args with
    | .ok o => pure o
    | .error e => IO.eprintln e; return (1 : UInt32)
  let modules := if o.modules.isEmpty then #[`Init.Data.Nat] else o.modules
  enableInitializersExecution
  -- Search path = LEAN_PATH (library + dependency oleans, set by `scripts/hcrun` / `lake env`)
  -- plus the running toolchain's own library.
  if (← IO.getEnv "LEAN_PATH").isNone then
    throw <| IO.userError "LEAN_PATH unset: run through scripts/hcrun or scripts/hclean (or `lake env` in the library)"
  initSearchPath (← getBuildDir)
  let imports := if o.imports.isEmpty then (modules.map (·.getRoot)).toList.eraseDups.toArray
    else o.imports
  -- `--olean-level server` imports like a `module` file with `public import`s: module-system libraries load
  -- without proofs (and without private constants' bodies), which needs far less memory; no proof repair then.
  let lvl := o.oleanLevel
  let env ← importModules (imports.map ({ module := · })) {} (loadExts := true) (level := lvl)
  let o := { o with noProofs := lvl != OLeanLevel.private }
  let withGrindDec := env.contains `Lean.Grind.CommRing.PPoly.NonNeg
  let env ← if withGrindDec then do
      let (env', msgs) ← Elab.process grindDecSrc env {} "<grindDec>"
      for m in msgs.toList do
        if m.severity == .error then
          throw <| IO.userError s!"grindDecSrc: {m.pos.line}:{m.pos.column}: {← m.data.toString}"
      pure env'
    else pure env
  let out ← match o.out? with
    | some f => pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk f .write))
    | none => IO.getStdout
  let ctx : Core.Context := {
    fileName := "<HypCheck>", fileMap := default, maxHeartbeats := 0
    options := ({} : Options).setBool `Elab.async false }
  let select : MetaM (Array (Name × TheoremVal)) := do
    let mut thms := #[]
    for mod in env.header.moduleNames, data in env.header.moduleData do
      unless modules.any (·.isPrefixOf mod) do continue
      for n in data.constNames do
        -- Below `.private`, module-system theorems are imported as axioms (statement only).
        let some ci := (match env.find? n with
          | some (.thmInfo ci) => some ci
          | some (.axiomInfo ai) => if lvl != OLeanLevel.private then
              some ({ name := ai.name, levelParams := ai.levelParams, type := ai.type,
                      value := mkConst ai.name (ai.levelParams.map mkLevelParam), all := [ai.name] } : TheoremVal)
            else none
          | _ => none) | continue
        -- Private names count as internal details themselves, so check the user-facing part.
        if ((privateToUserName n).isInternalDetail && !o.includeInternal) ||
            (isPrivateName n && !o.includePrivate) then continue
        if o.onlyPrivate && !isPrivateName n then continue
        unless o.namespaces.isEmpty || o.namespaces.any (·.isPrefixOf n) do continue
        if (← findDeclarationRanges? n).isNone then continue
        let hasProp ← forallTelescope ci.type fun xs _ => xs.anyM fun x => do isProp (← inferType x)
        if hasProp then thms := thms.push (mod, ci)
    return thms
  let (thms, _) ← (select.run' {}).toIO ctx { env }
  let thms := (Array.range thms.size).filterMap fun j =>
    if j % o.shards == o.shard then some thms[j]! else none
  -- Expensive theorems first, so that none of them is left running alone at the end.
  let cost (ci : TheoremVal) : MetaM Nat := forallTelescope ci.type fun xs _ => do
    let props ← xs.filterM fun x => do isProp (← inferType x)
    return props.size * (xs.size - props.size + 1)
  let (costs, _) ← ((thms.mapM fun (p : Name × TheoremVal) => cost p.2).run' {}).toIO ctx { env }
  let thms : Array (Name × TheoremVal) :=
    ((thms.zip costs).qsort (fun a b => a.2 > b.2)).map (·.1)
  let skip : Std.HashSet String ← match o.skip? with
    | none => pure {}
    | some f => do
      let lines := (← IO.FS.lines f).filter (!·.isEmpty)
      pure <| lines.foldl (init := {}) fun acc l =>
        match Json.parse l >>= (·.getObjValAs? String "theorem") with
        | .ok n => acc.insert n
        | .error _ => acc
  let recheck : Std.HashMap String (Array Nat) ← match o.recheck? with
    | none => pure {}
    | some f => do
      let lines := (← IO.FS.lines f).filter (!·.isEmpty)
      pure <| lines.foldl (init := {}) fun acc l =>
        match Json.parse l with
        | .ok j => match j.getObjValAs? String "theorem", j.getObjValAs? Nat "idx" with
          | .ok n, .ok i => acc.insert n ((acc.getD n #[]).push i)
          | _, _ => acc
        | .error _ => acc
  let witnesses : Std.HashMap String (Std.HashMap Nat String) ← match o.recheck?, o.redo with
    | some f, true => do
      let lines := (← IO.FS.lines f).filter (!·.isEmpty)
      pure <| lines.foldl (init := {}) fun acc l =>
        match Json.parse l with
        | .ok j => match j.getObjValAs? String "theorem", j.getObjValAs? Nat "idx", j.getObjValAs? String "witness" with
          | .ok n, .ok i, .ok w => acc.insert n ((acc.getD n {}).insert i w)
          | _, _, _ => acc
        | .error _ => acc
    | _, _ => pure {}
  let thms := if o.recheck?.isSome then thms.filter (recheck.contains <| toString ·.2.name) else thms
  let models : Models ← match o.models? with
    | none => pure #[]
    | some f => do
      let lines ← IO.FS.lines f
      let (ms, _) ← ((Term.TermElabM.run' (elabModels lines)).run' {}).toIO ctx { env }
      IO.eprintln s!"{ms.size} models loaded"
      pure ms
  let proofsOut? ← o.proofs?.mapM fun f => do
    let h ← IO.FS.Handle.mk f .write
    if lvl != OLeanLevel.private then h.putStrLn "module"
    for i in imports do h.putStrLn (if lvl != OLeanLevel.private then s!"public import {i}" else s!"import {i}")
    if withGrindDec then h.putStrLn grindDecSrc
    h.putStrLn s!"\n/-! Proofs emitted by HypCheck.lean (Lean {Lean.versionString}). -/\n"
    h.flush
    pure h
  IO.eprintln s!"{thms.size} theorems selected, {skip.size} to skip"
  -- With `--claim-dir`, several worker processes share this (deterministic) list: a worker checks
  -- theorem `j` only if it is the one that creates the file `j` there (fails if it exists).
  let claim (j : Nat) : IO Bool := do
    let some dir := o.claimDir? | return true
    try discard <| IO.FS.Handle.mk (dir / toString j) .writeNew; return true
    catch _ => return false
  for h : j in [:thms.size] do
    let (mod, ci) := thms[j]
    if skip.contains (toString ci.name) then continue
    unless ← claim j do continue
    let start ← IO.monoMsNow
    -- A fresh Core/Meta state per theorem: caches and auxiliary declarations created by tactics
    -- would otherwise accumulate and let the worker grow by gigabytes over a long run.
    let check : MetaM (Nat × Array (Json × Option ProofBlock)) := do
      let line := (← findDeclarationRanges? ci.name).map (·.selectionRange.pos.line) |>.getD 0
      return (line, ← Term.TermElabM.run' (checkTheorem o ci (recheck.get? (toString ci.name)) models (witnesses.getD (toString ci.name) {})))
    -- v10.2: a private theorem is checked as if inside its own module, so its private constants
    -- print and parse by their plain names (stored proofs are compiled under that module name).
    let envT := if isPrivateName ci.name then env.setMainModule mod else env
    -- v12.2: an exception while checking one theorem (a tool bug, e.g. "unexpected bound variable" on
    -- `Relation.Iterate.head_induction_on` in iris-lean) used to kill the worker, so the theorem got no rows.
    -- Now its Prop hypotheses are reported unresolved with the error as `reason`, and the worker goes on.
    let res ← try pure (Except.ok (← (check.run' {}).toIO ctx { env := envT })) catch e => pure (Except.error e)
    match res with
    | .error e =>
      let msg := ((toString e).replace "\n" " ").take 300
      let props : MetaM (Array (Nat × String)) := forallTelescope ci.type fun xs _ => do
        let mut ps := #[]
        for hx : i in [:xs.size] do
          let d ← xs[i].fvarId!.getDecl
          if ← isProp d.type then ps := ps.push (i, toString d.userName.eraseMacroScopes)
        return ps
      let ps ← try pure (← (props.run' {}).toIO ctx { env := envT }).1 catch _ => pure #[]
      for (i, n) in ps do
        out.putStrLn (Json.mkObj [("theorem", toJson (toString ci.name)), ("idx", toJson i), ("name", toJson n),
          ("module", toJson (toString mod)), ("status", toJson "unresolved"),
          ("reason", toJson s!"tool error: {msg}")]).compress
      out.flush
      IO.eprintln s!"[{j + 1}/{thms.size}] {ci.name} ERROR {msg} ({(← IO.monoMsNow) - start} ms)"
      continue
    | .ok _ => pure ()
    let .ok ((line, rs), _) := res | continue
    let mut rs' := #[]
    for (r, pb?) in rs do
      let mut extra : List (String × Json) := [("module", toString mod), ("line", line)]
      if let (some h, some pb) := (proofsOut?, pb?) then
        let idx := (r.getObjValAs? Nat "idx").toOption.getD 0
        -- The first rendering that passes is kept.
        let mut errs := #[]
        let mut ok? := none
        for (src, exp) in pb.srcs.map (·, pb.expect) ++ pb.fallbacks do
          match ← (try verifyBlock envT ctx pb src exp catch e => pure (some s!"exception: {e}")) with
          | none => ok? := some src; break
          | some err => errs := errs.push err
        extra := extra ++ [("proof", toJson (toString pb.decl)), ("proof_ok", toJson ok?.isSome)]
        h.putStrLn s!"-- {ci.name}, hypothesis {idx}: {(r.getObjValAs? String "status").toOption.getD "?"}"
        match ok? with
        | some src =>
          -- `proof_rendering`: index of the passing rendering when it is not the first one; the
          -- `fallbacks` (derivability alone) come after the `srcs`.
          if errs.size > 0 then extra := extra ++ [("proof_rendering", toJson errs.size)]
          if errs.size ≥ pb.srcs.size then extra := extra ++ [("proof_derivability_only", toJson true)]
          h.putStrLn src
        | none =>
          let err := " | ".intercalate errs.toList
          extra := extra ++ [("proof_error", toJson err)]
          let src := (pb.srcs[0]?.getD "").replace "-/" "- /"
          h.putStrLn s!"/- FAILED: {err.replace "-/" "- /"}\n{src}-/\n"
        h.flush
      let r := r.mergeObj (Json.mkObj extra)
      rs' := rs'.push r
      out.putStrLn r.compress
    out.flush
    let rs := rs'
    let st := rs.map fun r => (r.getObjValAs? String "status").toOption.getD "?"
    IO.eprintln s!"[{j + 1}/{thms.size}] {ci.name} {st} ({(← IO.monoMsNow) - start} ms)"
  return 0
