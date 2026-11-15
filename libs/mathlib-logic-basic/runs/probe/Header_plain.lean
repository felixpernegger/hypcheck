import HCHeaderM
-- hypkit toolkit header (mathlib-logic-basic, from mathlib-data): imports all Mathlib.Data, Mathlib.Logic, Mathlib.Basic modules plus
-- Mathlib.Analysis.Real.Cardinality and Mathlib.Topology.Sets.Closeds, and provides
-- drop%/indep%/drop0%/indep0%/drop1%/priv% (source: runs/hcimports/HCHeaderM.lean, HCImportsM.lean;
-- built into tools/hcrepair). Agents copy this file unchanged as the start of their output file
-- (scripts/verify.sh checks it). `drop1%` = universes set to 1, for Sort-polymorphic refutations.
-- Need a module outside Mathlib.Data? Log the row as gave_up with obstruction "needs import <Module>".

set_option linter.unusedVariables false

open Lean Meta Elab Term
