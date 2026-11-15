import Lean
open Lean

/-!
Dumps every theorem declared in a `Cslib.*` module, one JSON object per line: name, module, source line (as in the
results rows), universe parameters and the raw statement (`Expr` debug string: binder names and infos, universe
names, fully qualified constants). Two dumps of different CSLib commits show which theorems kept their statement
exactly (`scripts/stmt_diff.py`; `../../Methods.md`, "Updating to a new library version").

Usage: `scripts/csrun stmts OUT.jsonl` (native executable from `tools/`; LEAN_PATH of the CSLib checkout in
CSLIB_DIR).
-/

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Cslib}] {} (trustLevel := 1024)
  let out ← IO.FS.Handle.mk args[0]! .write
  for mod in env.header.moduleNames, md in env.header.moduleData do
    unless (`Cslib).isPrefixOf mod do continue
    for ci in md.constants do
      let n := ci.name
      let .thmInfo ti := ci | continue
      let line := match declRangeExt.find? env n with
        | some r => r.selectionRange.pos.line
        | none => 0
      let j := Json.mkObj [("name", toJson n), ("module", toJson mod), ("line", toJson line),
        ("lparams", toJson ti.levelParams), ("type", toJson s!"{ti.type}")]
      out.putStrLn j.compress
