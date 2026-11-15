# Findings: Batteries

Issues found while deciding the Batteries hypotheses. This list is separate from the removable list in `Results.md`, which covers every removable row. Each item below has a kernel-checked proof in the file named.

1. **The `LawfulBEq` requirement on the `List.diff` family is unnecessary.**
   - `diff` only erases, and `elem` is invariant under permutation for every `BEq`.
   - So `List.nil_diff`, `diff_append`, `diff_sublist`, `diff_subset`, `Perm.inter_left`, `Perm.inter` and `Perm.union_left` hold for every `BEq`.
   - These lemmas probably sit in a section with `[LawfulBEq α]`. Proofs: `checks/RestHand.lean`.
2. **`LawfulMonad` on the scan lemmas is unnecessary.**
   - The two sides have the same bind shape, so induction proves them without monad laws.
   - Affected: `Array.scanlM_map`/`scanrM_map`/`scanlM_extract`/`scanrM_extract`, `Subarray.scanlM_eq_scanlM_extract`/`scanrM_eq_scanrM_extract`, `Vector.scanlM_map`/`scanrM_map`/`scanlM_empty`/`scanrM_empty`, `Fin.dfoldrM_eq_foldrM`.
   - Also `seq_failure`: `LawfulAlternative` suffices. Proofs: `checks/RestHand.lean`, `checks/ControlHand.lean`.
3. **The AssocList order lemmas don't need their order hypotheses.**
   - `Batteries.AssocList.filterMapVal_filterMapVal` holds for any `cmp` and any list, so it needs neither `LawfulEqCmp`, `TransCmp` nor `KeysOrdered`. The same goes for `OrderedAssocList.filterMapVal_filterMapVal` (`LawfulEqCmp`).
   - `orderedFind?_orderedInsert_self` needs only `ReflCmp`.
   - `orderedFind?_orderedInsert` needs only `TransCmp`, on any list.
   - `KeysOrdered.orderedMerge` and `toList_orderedInsert` don't need `LawfulEqCmp`.
   - Proofs: `checks/OrderedHand.lean`.
4. **`OrderedAssocList.merge_comm` and `merge_assoc` carry unneeded function hypotheses.**
   - `merge_comm`'s `hg` is never needed, because `orderedMerge` never evaluates `g a none none`.
   - In `merge_assoc`, `hf₂` and `hg₂` each follow from the remaining hypotheses.
   - Proofs: `checks/OrderedHand.lean`.
5. **The `Substring.Raw.Valid` premise is unnecessary for `get`, `front`, `prev`, `next` and `prevn`.**
   - A nonempty `toString` already forces a valid start.
   - `String.Legacy.Iterator.ValidFor.prevn` doesn't need `n ≤ l.length`, and `Iterator.Valid.remainingBytes_le` doesn't need `Valid`.
   - Proofs: `checks/RestHand.lean`.
6. **`Float.Model.UnpackedFloat.unpack_beq_unpack_iff` and `unpack_eq_zero_iff_of_valid` don't need `spec.Valid`:** invalid bit patterns unpack to NaN. Proof: `checks/RestHand.lean`.
7. **Instance hypotheses that are derivable or unneeded.**
   - `Batteries.Tactic.instNonemptyDeclCache` doesn't need `[Nonempty α]`: `DeclCache α` is always nonempty.
   - Three `[LawfulMonad m]` instance arguments are implied by another binder: `LawfulMonadStateOf.instReaderTOfLawfulMonad`, `LawfulMonadStateOf.instStateRefT'OfLawfulMonad` and `OptionT.instLawfulMonadStateOfOfLawfulMonad`.
   - Proofs: `checks/ControlHand.lean`, `checks/InstDerivBat.lean`.
8. **`Nat.toFinDigits_ofFinDigits` doesn't need `2 ≤ base`**, and the `NeZero base` premises of `toFinDigits_of_ne_zero` and `toFinDigits_eq_append` follow from `2 ≤ base`. Proofs: `checks/RestHand.lean`.
9. **`List.Sublist.erase_diff_erase_sublist`'s `l₁ <+ l₂` premise is unneeded:** the statement holds for all lists. Proof: `checks/RestHand.lean`.

All of these removals are in `removals.patch` (a diff against `4af7237`); none has been proposed upstream yet.
