# Library defects found along the way

Concrete mistakes in the Lean library that the hypothesis analysis turned up, worth fixing upstream. This is not the list of removable hypotheses (see `Results.md`); only entries where the source is clearly not what the author meant.

## `omega` as an auto-bound hypothesis in `Std.Sat.AIG.CNF`

`src/Std/Sat/AIG/CNF.lean` lines 217–218 and 547–549 (lean4 at `a2ec825100`):

```lean
theorem Cache.IsExtensionBy_rfl (cache : Cache aig cnf) {h} (hmarked : cache.marks[idx]'h = true) :
    Cache.IsExtensionBy cache cache idx (have := cache.hmarks; omega) := by
theorem State.IsExtensionBy_rfl (state : State aig) {h}
    (hmarked : state.cache.marks[idx]'h = true) :
    State.IsExtensionBy state state idx (have := state.cache.hmarks; omega) := by
```

The bound argument is written as a term without `by`, so `omega` is not the tactic: it is an auto-bound implicit variable `omega : idx < aig.decls.size`, i.e. an extra hypothesis of both theorems. Intended: `(by have := cache.hmarks; omega)` (resp. `state.cache.hmarks`). Both lemmas are private and only used inside the file (e.g. line 788), so the fix is local.

Verdicts: `Cache.IsExtensionBy_rfl` idx 6 (`omega`) and `State.IsExtensionBy_rfl` idx 5 (`omega`) removable/derivable; with `omega` present, the implicit `h` (idx 8 resp. 7) is derivable from it too. Proofs in `checks/SatBVHand.lean`; rows in `results/private/private_all.jsonl`.
