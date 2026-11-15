# Results: Batteries

Which Prop-valued hypotheses of the theorems in [Batteries](https://github.com/leanprover-community/batteries) are
needed? How verdicts are defined, found and checked: `../../Methods.md`.

- **Library version:** commit `4af7237` (`main`, 2026-11-07).
- **Toolchain:** `leanprover/lean4:v4.36.0-rc2` (Batteries' `lean-toolchain`).
- **Patch:** `removals.patch` applies all 66 removals to `4af7237` (17 files; `git apply removals.patch` in a
  Batteries checkout at that commit). Not proposed upstream yet.

## Summary

**All 1,326 Prop-valued hypotheses of the 888 Batteries theorems in scope are decided: 1,259 necessary, 66 removable, 1 independent, 0 unresolved.** Public: 1,079 / 60 / 1 (`results/public.jsonl`); private: 180 / 6 / 0 (`results/private.jsonl`). Every necessary and removable verdict has a stored, kernel-checked Lean proof (`¬T'`, `T'` or `∀ indep, Hᵢ`) that passed `check_hand.py` (statement is exactly `T'`/`¬T'`) with only `propext`/`Classical.choice`/`Quot.sound`; removable proofs keep the theorem's universe parameters.

Scope: every module under `Batteries/` (186 modules, all reachable from `import Batteries`); 433 compiler-generated rows without source position (`.inj`, `congr_simp`, `hcongr_*`, `eq_def`, …) excluded. Coverage check (`scripts/Scope.lean`): over every constant of every `Batteries.*` module, the only Prop-valued declarations with Prop parameters outside the inventory are compiler-generated: the 433 position-less lemmas (`.inj`, `injEq`, `congr_simp`, `hcongr_*`, `eq_def`, `fun_cases_unfolding`, `induct_unfolding`, `sizeOf_spec`, …), about 3,400 Prop parameters of internal auxiliaries (`_proof_N`, `match_N`, `.eq_N`, `_flat_ctor`, `_sparseCasesOn`; none has a source position), and 38 Prop parameters of the 12 positioned recursors `recOn`/`casesOn` of inductive Props (`List.IsChain`, `List.Forall₂`, private `BinaryHeap.InSubtree`). No axioms, no opaque Prop constants. So every hand-written theorem, public or private, is in scope. Only Prop-valued parameters are analysed (not data or non-Prop instance arguments such as `[BEq α]`). Deprecated: 6 rows in 5 theorems, all aliases of core theorems (`List.isChain_of_isChain_cons_cons`, `List.isChain_cons_of_isChain_cons_cons`, `List.IsChain.cons_of_imp_of_cons` ×2, `heq_eqRec_iff_heq`, `eqRec_heq_iff_heq`), all necessary.

| Folder | Hypotheses (private) | Necessary | Removable | Independent |
|---|---|---|---|---|
| Data/List | 344 (1) | 336 | 8 | 0 |
| Data/BinaryHeap | 177 (142) | 173 | 4 | 0 |
| Data/OrderedAssocList | 160 (8) | 141 | 19 | 0 |
| Data/String | 132 (3) | 125 | 7 | 0 |
| Classes | 85 (0) | 85 | 0 | 0 |
| Control | 72 (0) | 68 | 4 | 0 |
| Data/Nat | 57 (5) | 54 | 3 | 0 |
| Data/Fin | 52 (0) | 50 | 2 | 0 |
| Data/Vector | 38 (10) | 31 | 7 | 0 |
| Data/UnionFind | 37 (4) | 37 | 0 | 0 |
| Data/Array | 30 (4) | 23 | 6 | 1 |
| Data/BinomialHeap | 28 (5) | 28 | 0 | 0 |
| Logic | 28 (0) | 28 | 0 | 0 |
| Data/Char | 22 (4) | 22 | 0 | 0 |
| Data/PairingHeap | 21 (0) | 21 | 0 | 0 |
| Data/ByteArray | 13 (0) | 11 | 2 | 0 |
| Data/UInt | 8 (0) | 8 | 0 | 0 |
| Data/Float | 8 (0) | 5 | 3 | 0 |
| Data/BitVec | 4 (0) | 4 | 0 | 0 |
| Data/AssocList | 3 (0) | 3 | 0 | 0 |
| Data/Int | 2 (0) | 2 | 0 | 0 |
| Data/DList | 1 (0) | 1 | 0 | 0 |
| Data/Except | 1 (0) | 1 | 0 | 0 |
| Data/Range | 1 (0) | 1 | 0 | 0 |
| Lean | 1 (0) | 1 | 0 | 0 |
| Util | 1 (0) | 0 | 1 | 0 |
| **total** | **1326** (186) | **1259** | **66** | **1** |

## Where the verdicts come from

| Source | Necessary | Removable | Proof files |
|---|---|---|---|
| HypCheck tool (native build; models + `Decidable` source) | 872 | 4 | `proofs/tool/full/public/part_*.lean`, `proofs/tool/full/private/bymod/` |
| Instance derivable (`InstDerivable.lean`) | | 3 | `checks/InstDerivBat.lean` |
| Agent wave W1 (4 Opus clusters) | 386 | 59 | `checks/{Heap,Ordered,Control,Rest}Hand.lean` |
| Main-session re-check of an agent's independence claim | 1 | | `checks/IndepFixHand.lean` |
| Unused / transitively unused / twins / flow | 0 | 0 | (nothing to find, see below) |

**Agent wave** (four clusters; every file re-verified by the main session before merging):

| Cluster | Rows | Necessary | Removable | Independent | Minutes | Tokens |
|---|---|---|---|---|---|---|
| Heap (BinaryHeap, 113 private) | 132 | 128 | 4 | 0 | 13 | 193 k |
| Ordered (OrderedAssocList, Binomial/Pairing heaps) | 81 | 62 | 19 | 0 | 12 | 200 k |
| Control (monad laws, Logic, Classes) | 88 | 86 | 2 | 0 | 13 | 165 k |
| Rest (List, String, UnionFind, Fin, Array, Vector, Float, Nat, Char) | 146 | 110 | 34 | 2 | 23 | 296 k |
| **total** | **447** | **386** | **59** | **2** | **61 agent-min (0.14/row)** | **854 k (1.9 k/row)** |

Nothing was given up or left untouched. The Rest agent's 2 independent rows were re-checked by the main session: one of them (`Vector.toList_scanlM`) turned out necessary (below).

**Mechanical detectors found nothing:** no hypothesis is unused or only passed on to unused positions (positive control: 20/20 known core cases found by the ported detectors), twins are consistent but add no verdicts, flow reached 2 private candidates (decided by the Heap agent). Batteries' `unusedSectionVars` linter and review keep the proofs free of unused hypotheses, so every removable hypothesis here needed a new argument.

## Independent (1; argument only)

`Array.toList_scanlM` idx 5, `[LawfulMonad m]` (statement `toList <$> as.scanlM f init = as.toList.scanlM f init`, kind `type-identity`). Both sides run bind chains of the same length (one bind per element) and then one `map`: `toList` at `Array β → List β` on the left, `List.reverse` at `List β → List β` on the right.
- **¬T′ is consistent:** if `Array Bool ≠ List Bool`, the counter monad of `checks/IndepFixHand.lean` refutes it. Its `map` adds 1 exactly when source and target type are equal (a classical test), so the left side counts 0 and the right side counts 1.
- **T′ is consistent:** interpret `Array β` as `List β` with `Array.mk := List.reverse`. Then both bind chains and both maps are literally the same terms, so the equation holds for every monad.
- **Neither is provable:** Lean proves neither `Array Bool = List Bool` nor its negation, because the two types are in bijection.

Evidence: argument only, no Lean proof of either half.

**Corrected by re-check:** `Vector.toList_scanlM` idx 6 was reported independent by the agent with the same argument, but is **necessary**. Its left `map` runs at `Vector Bool 1 → List Bool`, and `Vector Bool 1 ≠ List Bool` is provable (2 elements against at least 3), so the counter monad refutes it. Proof: `checks/IndepFixHand.lean` (`check_hand.py` 1/1, standard axioms).

## Removable hypotheses (66) — for review

Groups: **A** = the theorem holds without it, a genuine candidate for removal (46); **C** = instance found from another binder (3); **D** = dependent hypotheses that follow from the others (including two `optParam` bounds that already have default proofs, and `True`-by-definition `KeysOrdered cmp nil`), and private helpers (17). Joint removal of several hypotheses of one theorem is **not** checked (e.g. `filterMapVal_filterMapVal` 5, 6 and 10 are each removable on their own).

### A. Hypotheses the statement does not need (substantive; candidates for removal) (46)

| Theorem | idx | Hypothesis | Why removable | Proof |
|---|---|---|---|---|
| `seq_failure` | 5 | `LawfulMonad m` | LawfulMonad not needed: write failure = PEmpty.elim <$> failure (map_failure), then x <*> failure and x *> failure both equal (fun _ => PEmpty.elim) <$> x <*> failure by the LawfulApplicative laws | checks/ControlHand.lean |
| `Array.scanlM_extract` | 7 | `LawfulMonad m` | loop on extract shifted by start equals the loop on as, induction, no monad laws | checks/RestHand.lean |
| `Array.scanlM_map` | 6 | `LawfulMonad m` | same for the Array loop (size_map) | checks/RestHand.lean |
| `Array.scanrM_extract` | 7 | `LawfulMonad m` | shifted loop induction for scanrM | checks/RestHand.lean |
| `Array.scanrM_map` | 6 | `LawfulMonad m` | same for the Array scanrM loop | checks/RestHand.lean |
| `Subarray.scanlM_eq_scanlM_extract` | 5 | `LawfulMonad m` | Subarray.scanlM unfolds to the law-free Array.scanlM_extract | checks/RestHand.lean |
| `Subarray.scanrM_eq_scanrM_extract` | 5 | `LawfulMonad m` | Subarray.scanrM unfolds to the law-free Array.scanrM_extract | checks/RestHand.lean |
| `Fin.dfoldrM_eq_foldrM` | 4 | `LawfulMonad m` | dfoldrM.loop and foldrM.loop have the same bind shape; induction with the private foldrM_loop_zero/succ equations, no monad laws | checks/RestHand.lean |
| `Float.Model.UnpackedFloat.unpack_beq_unpack_iff` | 3 | `spec.Valid b` | invalid b unpacks to NaN so beq is false; RHS false since b is neither b' (valid) nor a zero | checks/RestHand.lean |
| `Float.Model.UnpackedFloat.unpack_beq_unpack_iff` | 4 | `spec.Valid b'` | symmetric to hb | checks/RestHand.lean |
| `Float.Model.UnpackedFloat.unpack_eq_zero_iff_of_valid` | 3 | `spec.Valid b` | an invalid b is a NaN pattern: unpack is NaN (not zero) and b is no packedZero | checks/RestHand.lean |
| `List.Sublist.erase_diff_erase_sublist` | 6 | `l₁.Sublist l₂` | holds for all l1 l2 (lawful BEq): if a in l1 both sides are equal (perm_cons_erase, diff_cons), else LHS = (l2.diff l1).erase a | checks/RestHand.lean |
| `List.diff_append` | 2 | `LawfulBEq α` | diff recurses on its second list, so the append law holds by induction for every BEq | checks/RestHand.lean |
| `List.diff_sublist` | 2 | `LawfulBEq α` | diff only erases (erase_sublist), so it is a sublist for every BEq | checks/RestHand.lean |
| `List.diff_subset` | 2 | `LawfulBEq α` | follows from the BEq-free diff_sublist | checks/RestHand.lean |
| `List.nil_diff` | 2 | `LawfulBEq α` | induction on l with the definition of diff; holds for every BEq | checks/RestHand.lean |
| `List.Perm.inter` | 2 | `LawfulBEq α` | Perm.filter plus the BEq-free inter_left | checks/RestHand.lean |
| `List.Perm.inter_left` | 4 | `LawfulBEq α` | elem is invariant under permutation for every BEq, so the filters agree | checks/RestHand.lean |
| `List.Perm.union_left` | 4 | `LawfulBEq α` | insert tests elem, invariant under permutation for every BEq; induction on l | checks/RestHand.lean |
| `Nat.toFinDigits_ofFinDigits` | 1 | `2 ≤ base` | for base < 2 the head condition forces l = [] and toFinDigits 0 = [] | checks/RestHand.lean |
| `Batteries.AssocList.KeysOrdered.orderedMerge` | 8 | `Std.LawfulEqCmp cmp` | eq case: cmp a1 a2 = eq transfers LTHeadKey via ltHeadKey_of_le (TransCmp), no key equality needed | checks/OrderedHand.lean |
| `Batteries.AssocList.filterMapVal_filterMapVal` | 5 | `Std.LawfulEqCmp cmp` | composition of filterMapVal holds for any list and any cmp (induction on l) | checks/OrderedHand.lean |
| `Batteries.AssocList.filterMapVal_filterMapVal` | 6 | `Std.TransCmp cmp` | composition of filterMapVal holds for any list and any cmp (induction on l) | checks/OrderedHand.lean |
| `Batteries.AssocList.filterMapVal_filterMapVal` | 10 | `Batteries.AssocList.KeysOrdered cmp l` | composition of filterMapVal holds for any list, ordered or not (induction on l) | checks/OrderedHand.lean |
| `Batteries.AssocList.orderedFind?_orderedInsert` | 4 | `Std.LawfulEqCmp cmp` | holds for any TransCmp and any list: equal keys are interchangeable under a transitive cmp | checks/OrderedHand.lean |
| `Batteries.AssocList.orderedFind?_orderedInsert` | 7 | `Batteries.AssocList.KeysOrdered cmp l` | holds for any list with TransCmp: insert and find agree on the prefix of smaller keys | checks/OrderedHand.lean |
| `Batteries.AssocList.orderedFind?_orderedInsert_self` | 3 | `Std.LawfulEqCmp cmp` | holds for every ReflCmp and every list (TransCmp gives ReflCmp) | checks/OrderedHand.lean |
| `Batteries.AssocList.orderedFind?_orderedInsert_self` | 4 | `Std.TransCmp cmp` | holds for every ReflCmp and every list (LawfulEqCmp gives ReflCmp) | checks/OrderedHand.lean |
| `Batteries.AssocList.orderedFind?_orderedInsert_self` | 6 | `Batteries.AssocList.KeysOrdered cmp l` | holds for every ReflCmp and every list: insert and find walk the same prefix | checks/OrderedHand.lean |
| `Batteries.AssocList.toList_orderedInsert` | 3 | `Std.LawfulEqCmp cmp` | eq case: TransCmp.lt_of_eq_of_lt gives cmp a p.1 = lt for the tail, no key equality needed | checks/OrderedHand.lean |
| `Batteries.OrderedAssocList.filterMapVal_filterMapVal` | 6 | `Std.LawfulEqCmp cmp` | same list-level composition lemma, no LawfulEqCmp needed | checks/OrderedHand.lean |
| `Batteries.OrderedAssocList.merge_assoc` | 15 | `∀ (a : α), f₂ a none none = none` | derivable: w a none none none with hf1, hg1, hg2 gives f2 a none none = none | checks/OrderedHand.lean |
| `Batteries.OrderedAssocList.merge_assoc` | 17 | `∀ (a : α), g₂ a none none = none` | derivable: w a none none none with hf1, hf2, hg1 gives g2 a none none = none | checks/OrderedHand.lean |
| `Batteries.OrderedAssocList.merge_comm` | 9 | `∀ (a : α), g a none none = none` | orderedMerge never evaluates g a none none: replace g by g' (none there) via om_congr, then apply merge_comm | checks/OrderedHand.lean |
| `String.Legacy.Iterator.Valid.remainingBytes_le` | 1 | `it.Valid` | remainingBytes is a truncated difference endPos - pos, always at most the byte size | checks/RestHand.lean |
| `String.Legacy.Iterator.ValidFor.prevn` | 5 | `n ≤ l.length` | past the start prevn stays at 0 and prev_nil keeps ValidFor; induction works for every n | checks/RestHand.lean |
| `Substring.Raw.Valid.front` | 3 | `s.Valid` | front = get 0, follows from the Valid-free get | checks/RestHand.lean |
| `Substring.Raw.Valid.get` | 4 | `s.Valid` | toString nonempty forces a char-boundary start (extract.go1 characterisation, helper hcV); get ignores the stop | checks/RestHand.lean |
| `Substring.Raw.Valid.next` | 4 | `s.Valid` | positions inside toString never equal the stop (extract.go2 stops there), so next agrees with the canonical valid substring | checks/RestHand.lean |
| `Substring.Raw.Valid.prev` | 4 | `s.Valid` | prev ignores the stop; same characterisation as get | checks/RestHand.lean |
| `Substring.Raw.Valid.prevn` | 3 | `s.Valid` | prevn ignores the stop; empty toString case gives 0 = 0 | checks/RestHand.lean |
| `Vector.scanlM_empty` | 5 | `LawfulMonad m` | n = 0: the loop returns pure #v[init] by definition | checks/RestHand.lean |
| `Vector.scanlM_map` | 7 | `LawfulMonad m` | loop on as.map f equals loop with composed function, induction, no monad laws | checks/RestHand.lean |
| `Vector.scanrM_empty` | 5 | `LawfulMonad m` | n = 0: the loop returns pure #v[init] by definition | checks/RestHand.lean |
| `Vector.scanrM_map` | 7 | `LawfulMonad m` | same, scanrM loop | checks/RestHand.lean |
| `Batteries.Tactic.instNonemptyDeclCache` | 1 | `Nonempty α✝` | DeclCache α is always nonempty: Cache α is an IO.Ref of a nonempty sum (MetaM α via throwError), and both functions can be fun _ _ a => pure a | checks/ControlHand.lean |

### C. Instance hypotheses derivable from another binder (instance resolution) (3)

| Theorem | idx | Hypothesis | Why removable | Proof |
|---|---|---|---|---|
| `LawfulMonadStateOf.instReaderTOfLawfulMonad` | 4 | `LawfulMonad m` | found by type class resolution from the other binders | checks/InstDerivBat.lean |
| `LawfulMonadStateOf.instStateRefT'OfLawfulMonad` | 4 | `LawfulMonad m` | found by type class resolution from the other binders | checks/InstDerivBat.lean |
| `OptionT.instLawfulMonadStateOfOfLawfulMonad` | 3 | `LawfulMonad m` | found by type class resolution from the other binders | checks/InstDerivBat.lean |

### D. Dependent hypotheses derivable from the other binders, and private helpers (17)

| Theorem | idx | Hypothesis | Why removable | Proof |
|---|---|---|---|---|
| `Batteries.BinaryHeap.max_ge_all` | 7 | `heap.size > 0` | derivable from h_in: y ∈ heap makes the underlying array nonempty | checks/HeapHand.lean |
| `Batteries.BinaryHeap.maxChild_ge_left` (private) | 8 | `2 * ↑i + 1 < sz` | derivable from hmc: maxChild only returns a child index (2i+1 or 2i+2) below sz | checks/HeapHand.lean |
| `Batteries.BinaryHeap.WF.TopDown.root_ge_all` (private) | 6 | `0 < sz` | derivable from the binder k : Fin sz, which forces 0 < sz | checks/HeapHand.lean |
| `Batteries.BinaryHeap.WF.parent_ge_subtree` (private) | 8 | `j < sz` | derivable from hk and hsub: InSubtree j k gives j ≤ k < sz | checks/HeapHand.lean |
| `ByteArray.get_append_left` | 4 | `optParam (i < (a ++ b).size) ⋯` | derivable by grind | `proofs/tool/full/public` `HypCheckProof.ByteArray.get_append_left.h4` |
| `ByteArray.get_append_right` | 5 | `optParam (i - a.size < b.size) ⋯` | derivable by grind | `proofs/tool/full/public` `HypCheckProof.ByteArray.get_append_right.h5` |
| `Fin.dfoldrM_loop_zero` | 3 | `0 < n + 1` | derivable by omega | `proofs/tool/full/public` `HypCheckProof.Fin.dfoldrM_loop_zero.h3` |
| `Nat.toFinDigits_eq_append` | 4 | `NeZero base` | NeZero base follows from 2 <= base | checks/RestHand.lean |
| `Nat.toFinDigits_of_ne_zero` | 3 | `NeZero base` | NeZero base follows from 2 <= base | checks/RestHand.lean |
| `Batteries.OrderedAssocList.getElem?_mk_nil` | 3 | `Batteries.AssocList.KeysOrdered cmp Batteries.AssocList.nil` | KeysOrdered cmp nil is True by definition | checks/OrderedHand.lean |
| `Batteries.OrderedAssocList.insert_mk_nil` | 5 | `Batteries.AssocList.KeysOrdered cmp Batteries.AssocList.nil` | KeysOrdered cmp nil is True by definition | checks/OrderedHand.lean |
| `Batteries.OrderedAssocList.merge_mk_cons_mk_nil` | 11 | `Batteries.AssocList.KeysOrdered cmp Batteries.AssocList.nil` | KeysOrdered cmp nil is True by definition | checks/OrderedHand.lean |
| `Batteries.OrderedAssocList.merge_mk_nil_mk_cons` | 7 | `Batteries.AssocList.KeysOrdered cmp Batteries.AssocList.nil` | KeysOrdered cmp nil is True by definition | checks/OrderedHand.lean |
| `Batteries.OrderedAssocList.toAssocList_tail_mk_nil` | 3 | `Batteries.AssocList.KeysOrdered cmp Batteries.AssocList.nil` | KeysOrdered cmp nil is True by definition | checks/OrderedHand.lean |
| `Vector.USize.succ_toNat_of_lt` (private) | 4 | `stop.toNat ≤ n` | start < stop and stop.toNat < size already rule out overflow | checks/RestHand.lean |
| `Vector.USize.succ_toNat_of_lt` (private) | 5 | `n < USize.size` | start < stop <= max already rule out overflow | checks/RestHand.lean |
| `Vector.scanlM.loop_toArray` (private) | 8 | `n ≤ as.toArray.size` | derivable by simp_all | `proofs/tool/full/private` `HypCheckProof.Vector.scanlM.loop_toArray.h8` |

## Caveats

- Each hypothesis is checked on its own; joint removability is open.
- Removing a hypothesis from a public lemma breaks callers that pass it explicitly; upstream changes need a deprecation strategy.
- Group D rows are mostly by design (the hypothesis is there to state the lemma, e.g. `optParam` bounds, `⟨[], trivial⟩`); listed for completeness.
- The one independent row rests on an argument, not on a Lean proof of either half.

## Library-specific method notes

- **Native tools.** With a Batteries import, `lean --run HypCheck.lean` was OOM-killed at 1.3 GB (the script's own
  environment next to the analysed one), so `HypCheck.lean` and the detectors are built as native executables in
  `tools/` (wrappers `scripts/hc`, `scripts/hx NAME`); a worker then needs ≤ 0.31 GB plus shared `.olean` pages.
- **HypCheck additions** after classifying the first pilot's failures (48% no values, 26% models, 16% `Decidable`):
  constructor terms up to depth 3 for plain inductive types (`AssocList`, the heap types), more `Char` values,
  `evalNat` after full reduction (`Fin a.size` over literal arrays), and `--dec-src FILE`: `Decidable` instances
  (`scripts/batdec.src`, e.g. `KeysOrdered`, `BinaryHeap.WF`, `Substring.Raw.ValidFor`) elaborated after the imports
  and written into every proofs file. Same pilot rows: 51% → 69% necessary.
- **Models** `scripts/models_bat.txt` (with the kit `models.txt`): union-find states, `EStateM` values, a cyclic
  comparison, `Zero`/`One`/`Add`/`Mul` models that break identity or associativity.
- **Universe 1 refutations:** some statements with a `Sort`-valued motive hold by proof irrelevance at universe 0,
  so two agents added `drop1%`/`indep1%` (all universes set to 1).
- **Private theorems:** tool proofs compile per module (`scripts/priv/compile_priv.py`); `check_hand.py` takes
  `HANDCHECK_MODULE=M` to compile a hand file as module `M`.
