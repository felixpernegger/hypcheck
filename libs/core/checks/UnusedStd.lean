import Std
import Lean
/-!
Removable hypotheses that the library's own proof does not use (`scripts/Unused.lean`). Generated
by `scripts/unused_proofs.py`; do not edit by hand.

`drop_unused% T i` is the proof term of `T` with binder `i` dropped. It fails unless binder `i`
does not occur in the proof, nothing in the statement depends on it, and the result has exactly the
stated type `T'` (checked with `isDefEq`); the kernel then checks the declaration as usual.
-/

open Lean Elab Term Meta in
/-- `T'`: the statement of `T` without binder `i`. Used as the statement where the printed one does
not elaborate back. -/
elab "drop_type% " id:ident i:num : term => do
  let ci ← getConstInfo id.getId
  forallTelescope ci.type fun xs body => mkForallFVars (xs.eraseIdxIfInBounds i.getNat) body

open Lean Elab Term Meta in
elab "drop_unused% " id:ident i:num : term <= expectedType => do
  let n := id.getId
  let i := i.getNat
  let ci ← getConstInfo n
  let some v := ci.value? (allowOpaque := true) | throwError "{n} has no proof term"
  forallTelescope ci.type fun xs body => lambdaBoundedTelescope v xs.size fun ys b => do
    unless ys.size == xs.size do throwError "the proof of {n} has fewer binders than its statement"
    let some x := ys[i]? | throwError "{n} has no binder {i}"
    if b.containsFVar x.fvarId! then throwError "binder {i} of {n} is used in its proof"
    let rest := ys.eraseIdxIfInBounds i
    let ty ← mkForallFVars rest (body.replaceFVars xs ys)
    unless ← isDefEq ty expectedType do
      throwError "{n} without binder {i} is{indentExpr ty}\nnot the stated{indentExpr expectedType}"
    -- universe parameters that only the proof uses (not `T'`) are set to 0
    let pf ← mkLambdaFVars rest b
    let inTy := (collectLevelParams {} ty).params
    let extra := ci.levelParams.filter (!inTy.contains ·)
    return pf.instantiateLevelParams extra (extra.map fun _ => Level.zero)

-- `Std.TreeMap.Raw.Equiv.mergeWith` idx 8: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.Raw.Equiv.mergeWith.h8.{u, v} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t₁ t₂ t₃ t₄ : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp],
      t₁.WF →
        t₂.WF →
          t₃.WF →
            t₄.WF →
              ∀ (f : α → β → β → β),
                t₁.Equiv t₂ → t₃.Equiv t₄ → (Std.TreeMap.Raw.mergeWith f t₁ t₃).Equiv (Std.TreeMap.Raw.mergeWith f t₂ t₄) :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.Raw.Equiv.mergeWith 8)

-- `Std.DTreeMap.Raw.get?_insertMany_list_of_mem` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.get?_insertMany_list_of_mem.h7.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Std.LawfulEqCmp cmp] [inst_1 : BEq α],
      t.WF →
        ∀ {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l →
              (t.insertMany l).get? k' = Option.some (cast (Std.DTreeMap.Raw.get?_insertMany_list_of_mem._proof_1 k_eq) v) :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.get?_insertMany_list_of_mem 7)

-- `Std.TreeMap.Raw.getElem?_insertMany_list_of_mem` idx 6: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.Raw.getElem?_insertMany_list_of_mem.h6.{u, v} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : BEq α],
      t.WF →
        ∀ {l : List (α × β)} {k k' : α},
          cmp k k' = Ordering.eq →
            ∀ {v : β},
              List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
                (k, v) ∈ l → (t.insertMany l)[k']? = Option.some v :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.Raw.getElem?_insertMany_list_of_mem 6)

-- `Std.DHashMap.Internal.toListModel_updateBucket` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.toListModel_updateBucket.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulHashable α]
      {m : Std.DHashMap.Internal.Raw₀ α β},
      Std.DHashMap.Internal.Raw.WFImp m.val →
        ∀ {a : α} {f : Std.DHashMap.Internal.AssocList α β → Std.DHashMap.Internal.AssocList α β}
          {g : List ((a : α) × β a) → List ((a : α) × β a)},
          (∀ {l : Std.DHashMap.Internal.AssocList α β}, (f l).toList.Perm (g l.toList)) →
            (∀ {l l' : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → l.Perm l' → (g l).Perm (g l')) →
              (∀ {l l' : List ((a : α) × β a)}, Std.Internal.List.containsKey a l' = Bool.false → g (l ++ l') = g l ++ l') →
                (Std.DHashMap.Internal.toListModel (Std.DHashMap.Internal.updateBucket m.val.buckets m.property a f)).Perm
                  (g (Std.DHashMap.Internal.toListModel m.val.buckets)) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.toListModel_updateBucket 4)

-- `Std.DHashMap.Internal.Raw₀.Const.wf_insertMany₀` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.wf_insertMany₀.h4.{u, v, w} :
    ∀ {α : Type u} {β : Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulHashable α] {ρ : Type w}
      [inst_3 : ForIn Id ρ (α × β)] {m : Std.DHashMap.Raw α fun (x : α) => β} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.Const.insertMany
                (⟨m, h⟩ : { m : Std.DHashMap.Raw α fun (x : α) => β // 0 < m.buckets.size }) l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.Const.wf_insertMany₀ 4)

-- `Std.DHashMap.Internal.Raw₀.Const.wf_insertMany₀` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.wf_insertMany₀.h5.{u, v, w} :
    ∀ {α : Type u} {β : Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] {ρ : Type w}
      [inst_3 : ForIn Id ρ (α × β)] {m : Std.DHashMap.Raw α fun (x : α) => β} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.Const.insertMany
                (⟨m, h⟩ : { m : Std.DHashMap.Raw α fun (x : α) => β // 0 < m.buckets.size }) l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.Const.wf_insertMany₀ 5)

-- `Std.Iter.Equiv.fold_eq` idx 12: unused in the library's proof
theorem HypCheckProof.Std.Iter.Equiv.fold_eq.h12.{w, w'} :
    ∀ {α₁ α₂ β γ : Type w} {m : Type w → Type w'} [inst : Std.Iterator α₁ Id β] [inst : Std.Iterator α₂ Id β]
      [inst : Std.Iterator α₁ Id β] [inst_1 : Std.Iterator α₂ Id β] [inst_2 : @Std.Iterators.Finite α₁ Id β inst]
      [inst_3 : @Std.Iterators.Finite α₂ Id β inst_1] [inst_4 : Monad m] [inst_5 : @Std.IteratorLoop α₁ Id β inst Id]
      [inst_6 : @Std.LawfulIteratorLoop β α₁ Id Id Id.instMonad Id.instMonad inst inst_5]
      [inst_7 : @Std.IteratorLoop α₂ Id β inst_1 Id]
      [inst_8 : @Std.LawfulIteratorLoop β α₂ Id Id Id.instMonad Id.instMonad inst_1 inst_7] {init : γ} {f : γ → β → γ}
      {ita : @Std.Iter α₁ β} {itb : @Std.Iter α₂ β},
      @Std.Iter.Equiv α₁ α₂ β inst inst_1 ita itb →
        @Eq γ (@Std.Iter.fold α₁ β γ inst inst_5 f init ita) (@Std.Iter.fold α₂ β γ inst_1 inst_7 f init itb) :=
  no_implicit_lambda% (drop_unused% Std.Iter.Equiv.fold_eq 12)

-- `Std.DTreeMap.get?_insertMany_list_of_mem` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.get?_insertMany_list_of_mem.h7.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst : Std.LawfulEqCmp cmp] [inst_1 : BEq α] {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq)
      {v : β k},
      List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
        (⟨k, v⟩ : (a : α) × β a) ∈ l →
          (t.insertMany l).get? k' = Option.some (cast (Std.DTreeMap.get?_insertMany_list_of_mem._proof_1 k_eq) v) :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.get?_insertMany_list_of_mem 7)

-- `Std.TreeMap.getElem?_insertMany_list_of_mem` idx 6: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h6.{u, v} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
      {l : List (α × β)} {k k' : α},
      cmp k k' = Ordering.eq →
        ∀ {v : β},
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
            (k, v) ∈ l → (t.insertMany l)[k']? = Option.some v :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.getElem?_insertMany_list_of_mem 6)

-- `Std.ExtTreeMap.getElem?_insertMany_list_of_mem` idx 6: unused in the library's proof
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h6.{u, v} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : BEq α] {l : List (α × β)} {k k' : α},
      cmp k k' = Ordering.eq →
        ∀ {v : β},
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
            (k, v) ∈ l → (t.insertMany l)[k']? = Option.some v :=
  no_implicit_lambda% (drop_unused% Std.ExtTreeMap.getElem?_insertMany_list_of_mem 6)

-- `Std.DTreeMap.Internal.Impl.head?_keys` idx 8: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.head?_keys.h8.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β} [inst : Std.TransOrd α]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderOrd α] [inst : Std.LawfulOrderLeftLeaningMin α]
      [inst : Std.LawfulEqOrd α], t.WF → t.keys.head? = t.minKey? :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.head?_keys 8)

-- `Std.DTreeMap.Internal.Impl.toListModel_filter_lt_of_lt` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.toListModel_filter_lt_of_lt.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] {k : α → Ordering} [inst_1 : Std.Internal.IsCut Ord.compare k] {sz : Nat}
      {k' : α} {v' : β k'} {l r : Std.DTreeMap.Internal.Impl α β},
      k k' = Ordering.lt →
        (Std.DTreeMap.Internal.Impl.inner sz k' v' l r).Ordered →
          List.filter (fun (x : (a : α) × β a) => k x.fst == Ordering.lt)
              (Std.DTreeMap.Internal.Impl.inner sz k' v' l r).toListModel =
            List.filter (fun (x : (a : α) × β a) => k x.fst == Ordering.lt) l.toListModel ++
              (⟨k', v'⟩ : (a : α) × β a) :: r.toListModel :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.toListModel_filter_lt_of_lt 3)

-- `Std.TreeMap.Equiv.mergeWith` idx 8: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.Equiv.mergeWith.h8.{u, v} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t₁ t₂ t₃ t₄ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
      (f : α → β → β → β), t₁.Equiv t₂ → t₃.Equiv t₄ → (Std.TreeMap.mergeWith f t₁ t₃).Equiv (Std.TreeMap.mergeWith f t₂ t₄) :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.Equiv.mergeWith 8)

-- `Std.DTreeMap.Internal.Impl.Ordered.compare_right_not_beq_gt` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.Ordered.compare_right_not_beq_gt.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] {k : α → Ordering} [inst_1 : Std.Internal.IsStrictCut Ord.compare k]
      {sz : Nat} {k' : α} {v' : β k'} {l r : Std.DTreeMap.Internal.Impl α β},
      (Std.DTreeMap.Internal.Impl.inner sz k' v' l r).Ordered →
        (k k').isLE = Bool.true → ∀ (p : (a : α) × β a), p ∈ r.toListModel → ¬(k p.fst == Ordering.gt) = Bool.true :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.Ordered.compare_right_not_beq_gt 3)

-- `Std.DHashMap.Internal.Raw₀.wf_insertMany₀` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.wf_insertMany₀.h4.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulHashable α] {ρ : Type w}
      [inst_3 : ForIn Id ρ ((a : α) × β a)] {m : Std.DHashMap.Raw α β} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.insertMany (⟨m, h⟩ : { m : Std.DHashMap.Raw α β // 0 < m.buckets.size }) l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.wf_insertMany₀ 4)

-- `Std.DHashMap.Internal.Raw₀.wf_insertMany₀` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.wf_insertMany₀.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] {ρ : Type w}
      [inst_3 : ForIn Id ρ ((a : α) × β a)] {m : Std.DHashMap.Raw α β} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.insertMany (⟨m, h⟩ : { m : Std.DHashMap.Raw α β // 0 < m.buckets.size }) l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.wf_insertMany₀ 5)

-- `Std.DTreeMap.Internal.Impl.min?_keys` idx 8: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.min?_keys.h8.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β} [inst : Std.TransOrd α]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderOrd α] [inst_3 : Std.LawfulOrderLeftLeaningMin α]
      [inst_4 : Std.LawfulEqOrd α], t.WF → t.keys.min? = t.minKey? :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.min?_keys 8)

-- `Std.DTreeMap.Internal.Impl.toListModel_find?_of_lt` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.toListModel_find?_of_lt.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] {k : α → Ordering} [inst_1 : Std.Internal.IsCut Ord.compare k] {sz : Nat}
      {k' : α} {v' : β k'} {l r : Std.DTreeMap.Internal.Impl α β},
      k k' = Ordering.lt →
        (Std.DTreeMap.Internal.Impl.inner sz k' v' l r).Ordered →
          List.find? (fun (x : (a : α) × β a) => k x.fst == Ordering.eq)
              (Std.DTreeMap.Internal.Impl.inner sz k' v' l r).toListModel =
            List.find? (fun (x : (a : α) × β a) => k x.fst == Ordering.eq) l.toListModel :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.toListModel_find?_of_lt 3)

-- `Std.DTreeMap.Raw.Const.get_insertMany_list` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.Const.get_insertMany_list.h6.{u, v} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {β : Type v} {t : Std.DTreeMap.Raw α (fun (x : α) => β) cmp}
      [inst : Std.TransCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] (h : t.WF) {l : List (α × β)} {k : α}
      {h' : k ∈ Std.DTreeMap.Raw.Const.insertMany t l},
      Std.DTreeMap.Raw.Const.get (Std.DTreeMap.Raw.Const.insertMany t l) k h' =
        match w :
          List.findSomeRev?
            (fun (x : α × β) =>
              match x with
              | (a, b) => if cmp a k = Ordering.eq then Option.some b else Option.none)
            l with
        | Option.some v => v
        | Option.none =>
          Std.DTreeMap.Raw.Const.get t k (Std.DTreeMap.Raw.Const.contains_of_contains_insertMany_list' h h' w) :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.Const.get_insertMany_list 6)

-- `Std.DHashMap.Internal.IsHashSelf.updateBucket` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.IsHashSelf.updateBucket.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulHashable α]
      {m : Array (Std.DHashMap.Internal.AssocList α β)} {h : 0 < m.size} {a : α}
      {f : Std.DHashMap.Internal.AssocList α β → Std.DHashMap.Internal.AssocList α β},
      (∀ (l : Std.DHashMap.Internal.AssocList α β) (p : (a : α) × β a),
          p ∈ (f l).toList →
            Std.Internal.List.containsKey p.fst l.toList = Bool.true ∨ Hashable.hash p.fst = Hashable.hash a) →
        Std.DHashMap.Internal.IsHashSelf m → Std.DHashMap.Internal.IsHashSelf (Std.DHashMap.Internal.updateBucket m h a f) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.IsHashSelf.updateBucket 4)

-- `Std.DHashMap.Internal.Raw₀.wf_insertManyIfNew₀` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.wf_insertManyIfNew₀.h4.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulHashable α] {ρ : Type w}
      [inst_3 : ForIn Id ρ ((a : α) × β a)] {m : Std.DHashMap.Raw α β} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.insertManyIfNew (⟨m, h⟩ : { m : Std.DHashMap.Raw α β // 0 < m.buckets.size })
                l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.wf_insertManyIfNew₀ 4)

-- `Std.DHashMap.Internal.Raw₀.wf_insertManyIfNew₀` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.wf_insertManyIfNew₀.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] {ρ : Type w}
      [inst_3 : ForIn Id ρ ((a : α) × β a)] {m : Std.DHashMap.Raw α β} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.insertManyIfNew (⟨m, h⟩ : { m : Std.DHashMap.Raw α β // 0 < m.buckets.size })
                l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.wf_insertManyIfNew₀ 5)

-- `Std.DHashMap.Internal.Raw₀.wf_eraseMany₀` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.wf_eraseMany₀.h4.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulHashable α] {ρ : Type w}
      [inst_3 : ForIn Id ρ ((a : α) × β a)] {m : Std.DHashMap.Raw α β} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.eraseManyEntries (⟨m, h⟩ : { m : Std.DHashMap.Raw α β // 0 < m.buckets.size })
                l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.wf_eraseMany₀ 4)

-- `Std.DHashMap.Internal.Raw₀.wf_eraseMany₀` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.wf_eraseMany₀.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] {ρ : Type w}
      [inst_3 : ForIn Id ρ ((a : α) × β a)] {m : Std.DHashMap.Raw α β} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.eraseManyEntries (⟨m, h⟩ : { m : Std.DHashMap.Raw α β // 0 < m.buckets.size })
                l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.wf_eraseMany₀ 5)

-- `Std.WP.Triple.seq` idx 12: unused in the library's proof
theorem HypCheckProof.Std.WP.Triple.seq.h12.{u, v, w, w'} :
    ∀ {Pred : Type w} {EPosts : Type w'} {m : Type v → Type u} [inst : Monad m] [inst_1 : Std.WP.Assertion Pred]
      [inst_2 : Std.WP.Assertion EPosts] [inst_3 : @Std.WP.WPMonad m Pred EPosts inst inst_1 inst_2] {α β : Type v}
      {pre : Pred} {post : β → Pred} {eposts : EPosts} (x : m (α → β)) (y : m α),
      @Std.WP.Triple Pred EPosts (m (α → β)) (α → β) inst_1 inst_2 x
          (@Std.WP.instWPOfWPMonad m Pred EPosts (α → β) inst inst_1 inst_2 inst_3) pre
          (fun (f : α → β) =>
            @Std.WP.WP.wp (m α) α Pred EPosts inst_1 inst_2
              (@Std.WP.instWPOfWPMonad m Pred EPosts α inst inst_1 inst_2 inst_3) y (fun (a : α) => post (f a)) eposts)
          eposts →
        @Std.WP.Triple Pred EPosts (m β) β inst_1 inst_2
          (@Seq.seq m (@Applicative.toSeq m (@Monad.toApplicative m inst)) α β x fun (x : Unit) => y)
          (@Std.WP.instWPOfWPMonad m Pred EPosts β inst inst_1 inst_2 inst_3) pre post eposts :=
  no_implicit_lambda% (drop_unused% Std.WP.Triple.seq 12)

-- `Std.DHashMap.Raw.insertMany_cons` idx 8: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.insertMany_cons.h8.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α]
      {l : List ((a : α) × β a)} {k : α} {v : β k} [inst_2 : LawfulHashable α],
      m.WF → m.insertMany ((⟨k, v⟩ : (a : α) × β a) :: l) = (m.insert k v).insertMany l :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.insertMany_cons 8)

-- `Std.DHashMap.Raw.insertMany_cons` idx 9: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.insertMany_cons.h9.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α]
      {l : List ((a : α) × β a)} {k : α} {v : β k} [inst_2 : EquivBEq α],
      m.WF → m.insertMany ((⟨k, v⟩ : (a : α) × β a) :: l) = (m.insert k v).insertMany l :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.insertMany_cons 9)

-- `Std.Ric.toArray_iter_eq_toArray` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Ric.toArray_iter_eq_toArray.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : DecidableLE α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxc.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Ric α}, r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Ric.toArray_iter_eq_toArray 5)

-- `Std.Ric.toList_iter_eq_toList` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Ric.toList_iter_eq_toList.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : DecidableLE α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxc.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Ric α}, r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Ric.toList_iter_eq_toList 5)

-- `Std.Internal.List.beq_of_getEntry_eq` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.beq_of_getEntry_eq.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l : List ((a : α) × β a)} {p : (a : α) × β a} {k : α}
      {h₁ : Std.Internal.List.containsKey k l = Bool.true}, Std.Internal.List.getEntry k l h₁ = p → (p.fst == k) = Bool.true :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.beq_of_getEntry_eq 3)

-- `Std.Do.OptionT.ensures_of_wp_run` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Do.OptionT.ensures_of_wp_run.h2.{u, u_1} :
    ∀ {m : Type u → Type u_1} [inst : Monad m] [inst_1 : Std.Do.WP m Std.Do.PostShape.pure]
      [inst_2 : @Std.Do.WPSound m Std.Do.PostShape.pure inst inst_1] {α : Type u} {prog : OptionT m α}
      (P : Option α → Prop),
      @Std.Do.SPred.entails (Std.Do.PostShape.except PUnit Std.Do.PostShape.pure).args
          (@Std.Do.SPred.pure (Std.Do.PostShape.except PUnit Std.Do.PostShape.pure).args True)
          (@Std.Do.PredTrans.apply (Std.Do.PostShape.except PUnit Std.Do.PostShape.pure) α
            (@Std.Do.WP.wp (OptionT m) (Std.Do.PostShape.except PUnit Std.Do.PostShape.pure)
              (@Std.Do.OptionT.instWP m Std.Do.PostShape.pure inst_1) α prog)
            (@Prod.mk (α → Std.Do.Assertion (Std.Do.PostShape.except PUnit Std.Do.PostShape.pure))
              (Std.Do.ExceptConds (Std.Do.PostShape.except PUnit Std.Do.PostShape.pure))
              (fun (a : α) =>
                @Std.Do.SPred.pure (Std.Do.PostShape.except PUnit Std.Do.PostShape.pure).args (P (@Option.some α a)))
              (@Prod.mk (PUnit → Std.Do.Assertion Std.Do.PostShape.pure) (Std.Do.ExceptConds Std.Do.PostShape.pure)
                (fun (x : PUnit) => @Std.Do.SPred.pure Std.Do.PostShape.pure.args (P (@Option.none α))) PUnit.unit))) →
        @Std.Do.Internal.Ensures m (@Monad.toBind m inst) (Option α) P (@OptionT.run m α prog) :=
  no_implicit_lambda% (drop_unused% Std.Do.OptionT.ensures_of_wp_run 2)

-- `Std.DTreeMap.Internal.Impl.Const.WF.getThenInsertIfNew?!` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.Const.WF.getThenInsertIfNew?!.h4.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] {k : α} {v : β}
      {t : Std.DTreeMap.Internal.Impl α fun (x : α) => β},
      t.WF → (Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew?! t k v).snd.WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.Const.WF.getThenInsertIfNew?! 4)

-- `Std.DTreeMap.Internal.Impl.minKey!_eq_minKey!` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.minKey!_eq_minKey!.h6.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : Inhabited α] [inst_3 : BEq α]
      {l : Std.DTreeMap.Internal.Impl α β}, l.Ordered → l.minKey! = Std.Internal.List.minKey! l.toListModel :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.minKey!_eq_minKey! 6)

-- `Std.Roo.toArray_iter_eq_toArray` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Roo.toArray_iter_eq_toArray.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Roo α},
      r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Roo.toArray_iter_eq_toArray 4)

-- `Std.Roc.toList_iter` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Roc.toList_iter.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Roc α},
      r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Roc.toList_iter 4)

-- `Std.Roo.toList_iter_eq_toList` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Roo.toList_iter_eq_toList.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Roo α},
      r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Roo.toList_iter_eq_toList 4)

-- `Std.Roc.toArray_iter` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Roc.toArray_iter.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Roc α},
      r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Roc.toArray_iter 4)

-- `Std.Internal.List.minKey?_eq_head?_keys` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKey?_eq_head?_keys.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α]
      {l : List ((a : α) × β a)},
      List.Pairwise (fun (a b : (a : α) × β a) => Ord.compare a.fst b.fst = Ordering.lt) l →
        Std.Internal.List.minKey? l = (Std.Internal.List.keys l).head? :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKey?_eq_head?_keys 3)

-- `Std.Internal.List.minKey?_eq_head?_keys` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKey?_eq_head?_keys.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((a : α) × β a)},
      List.Pairwise (fun (a b : (a : α) × β a) => Ord.compare a.fst b.fst = Ordering.lt) l →
        Std.Internal.List.minKey? l = (Std.Internal.List.keys l).head? :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKey?_eq_head?_keys 5)

-- `Std.DTreeMap.Internal.Impl.contains_of_isEmpty` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.contains_of_isEmpty.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β},
      t.WF → ∀ {a : α}, t.isEmpty = Bool.true → Std.DTreeMap.Internal.Impl.contains a t = Bool.false :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.contains_of_isEmpty 4)

-- `Std.Internal.List.Const.isSome_minKey?_modifyKey_eq_isSome` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.Const.isSome_minKey?_modifyKey_eq_isSome.h3.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {f : β → β}
      {l : List ((_ : α) × β)},
      (Std.Internal.List.minKey? (Std.Internal.List.Const.modifyKey k f l)).isSome = (Std.Internal.List.minKey? l).isSome :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.Const.isSome_minKey?_modifyKey_eq_isSome 3)

-- `Std.Internal.List.Const.isSome_minKey?_modifyKey_eq_isSome` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.Const.isSome_minKey?_modifyKey_eq_isSome.h5.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {f : β → β}
      {l : List ((_ : α) × β)},
      (Std.Internal.List.minKey? (Std.Internal.List.Const.modifyKey k f l)).isSome = (Std.Internal.List.minKey? l).isSome :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.Const.isSome_minKey?_modifyKey_eq_isSome 5)

-- `Std.DHashMap.Raw.Const.equiv_iff_toList_perm` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.Const.equiv_iff_toList_perm.h6.{u, v} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {β : Type v} {m₁ m₂ : Std.DHashMap.Raw α fun (x : α) => β}
      [inst : LawfulHashable α], m₁.Equiv m₂ ↔ (Std.DHashMap.Raw.Const.toList m₁).Perm (Std.DHashMap.Raw.Const.toList m₂) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.Const.equiv_iff_toList_perm 6)

-- `Std.DHashMap.Raw.Const.equiv_iff_toList_perm` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.Const.equiv_iff_toList_perm.h7.{u, v} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {β : Type v} {m₁ m₂ : Std.DHashMap.Raw α fun (x : α) => β}
      [inst : EquivBEq α], m₁.Equiv m₂ ↔ (Std.DHashMap.Raw.Const.toList m₁).Perm (Std.DHashMap.Raw.Const.toList m₂) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.Const.equiv_iff_toList_perm 7)

-- `Std.Internal.List.eq_getKey_getValue_of_getEntry?_eq_some` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.eq_getKey_getValue_of_getEntry?_eq_some.h2.{u, v} :
    ∀ {α : Type u} [inst : BEq α] {β : Type v} {l : List ((_ : α) × β)} {k : α} {y : (_ : α) × β}
      (h : Std.Internal.List.getEntry? k l = Option.some y),
      y =
        (⟨Std.Internal.List.getKey k l
              (Eq.trans Std.Internal.List.containsKey_eq_isSome_getEntry? (Option.isSome_of_eq_some h)),
            Std.Internal.List.getValue k l
              (Eq.trans Std.Internal.List.containsKey_eq_isSome_getEntry? (Option.isSome_of_eq_some h))⟩ :
          (_ : α) × β) :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.eq_getKey_getValue_of_getEntry?_eq_some 2)

-- `Std.Internal.List.minKeyD_eq_getD_minKey?` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKeyD_eq_getD_minKey?.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {l : List ((a : α) × β a)}
      {fallback : α}, Std.Internal.List.minKeyD l fallback = (Std.Internal.List.minKey? l).getD fallback :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKeyD_eq_getD_minKey? 3)

-- `Std.Internal.List.minKeyD_eq_getD_minKey?` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKeyD_eq_getD_minKey?.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((a : α) × β a)}
      {fallback : α}, Std.Internal.List.minKeyD l fallback = (Std.Internal.List.minKey? l).getD fallback :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKeyD_eq_getD_minKey? 5)

-- `Std.Internal.List.getKeyD_eq_fallback` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.getKeyD_eq_fallback.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l : List ((a : α) × β a)} {a fallback : α},
      Std.Internal.List.containsKey a l = Bool.false → Std.Internal.List.getKeyD a l fallback = fallback :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.getKeyD_eq_fallback 3)

-- `Std.Internal.List.containsKey_of_getValue_eq_some` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.containsKey_of_getValue_eq_some.h2.{u, v} :
    ∀ {α : Type u} [inst : BEq α] {β : Type v} {l : List ((_ : α) × β)} {a : α} {b : β},
      Std.Internal.List.getValue? a l = Option.some b → Std.Internal.List.containsKey a l = Bool.true :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.containsKey_of_getValue_eq_some 2)

-- `Std.DTreeMap.Internal.Impl.Const.modify_eq_alter` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.Const.modify_eq_alter.h3.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : Ord α] {t : Std.DTreeMap.Internal.Impl α fun (x : α) => β} {a : α} {f : β → β}
      (htb : t.Balanced),
      Std.DTreeMap.Internal.Impl.Const.modify a f t =
        (Std.DTreeMap.Internal.Impl.Const.alter a (fun (x : Option β) => Option.map f x) t htb).impl :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.Const.modify_eq_alter 3)

-- `Std.DHashMap.Internal.Raw₀.map_fst_toList_eq_keys` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.map_fst_toList_eq_keys.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} (m : Std.DHashMap.Internal.Raw₀ α β) [inst : BEq α] [inst_1 : Hashable α]
      [inst : LawfulHashable α], List.map Sigma.fst m.val.toList = m.val.keys :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.map_fst_toList_eq_keys 5)

-- `Std.DHashMap.Internal.Raw₀.map_fst_toList_eq_keys` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.map_fst_toList_eq_keys.h6.{u, v} :
    ∀ {α : Type u} {β : α → Type v} (m : Std.DHashMap.Internal.Raw₀ α β) [inst : BEq α] [inst_1 : Hashable α]
      [inst : EquivBEq α], List.map Sigma.fst m.val.toList = m.val.keys :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.map_fst_toList_eq_keys 6)

-- `Std.BundledIterM.stepOnQuotient_mk` idx 2: unused in the library's proof
theorem HypCheckProof.Std.BundledIterM.stepOnQuotient_mk.h2.{w, w'} :
    ∀ {m : Type w → Type w'} [inst : Monad m] {β : Type w} [inst : Monad m] [inst_1 : LawfulMonad m]
      {bit : Std.BundledIterM m β},
      Std.BundledIterM.stepOnQuotient (Quot.mk (Std.BundledIterM.Equiv m β) bit) =
        Std.IterStep.mapIterator (Quot.mk (Std.BundledIterM.Equiv m β)) <$> bit.step :=
  no_implicit_lambda% (drop_unused% Std.BundledIterM.stepOnQuotient_mk 2)

-- `Std.DHashMap.Raw.Const.equiv_iff_keys_unit_perm` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.Const.equiv_iff_keys_unit_perm.h3.{u} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] [inst : LawfulHashable α]
      {m₁ m₂ : Std.DHashMap.Raw α fun (x : α) => Unit}, m₁.Equiv m₂ ↔ m₁.keys.Perm m₂.keys :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.Const.equiv_iff_keys_unit_perm 3)

-- `Std.DHashMap.Raw.Const.equiv_iff_keys_unit_perm` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.Const.equiv_iff_keys_unit_perm.h4.{u} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] [inst : EquivBEq α]
      {m₁ m₂ : Std.DHashMap.Raw α fun (x : α) => Unit}, m₁.Equiv m₂ ↔ m₁.keys.Perm m₂.keys :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.Const.equiv_iff_keys_unit_perm 4)

-- `Std.DTreeMap.Internal.Impl.WF.erase!` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.WF.erase!.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {x : Ord α} {k : α} {l : Std.DTreeMap.Internal.Impl α β},
      l.WF → (Std.DTreeMap.Internal.Impl.erase! k l).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.WF.erase! 3)

-- `Std.HashMap.Raw.equiv_iff_keys_unit_perm` idx 3: unused in the library's proof
theorem HypCheckProof.Std.HashMap.Raw.equiv_iff_keys_unit_perm.h3.{u} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] [inst : LawfulHashable α] {m₁ m₂ : Std.HashMap.Raw α Unit},
      m₁.Equiv m₂ ↔ m₁.keys.Perm m₂.keys :=
  no_implicit_lambda% (drop_unused% Std.HashMap.Raw.equiv_iff_keys_unit_perm 3)

-- `Std.HashMap.Raw.equiv_iff_keys_unit_perm` idx 4: unused in the library's proof
theorem HypCheckProof.Std.HashMap.Raw.equiv_iff_keys_unit_perm.h4.{u} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] [inst : EquivBEq α] {m₁ m₂ : Std.HashMap.Raw α Unit},
      m₁.Equiv m₂ ↔ m₁.keys.Perm m₂.keys :=
  no_implicit_lambda% (drop_unused% Std.HashMap.Raw.equiv_iff_keys_unit_perm 4)

-- `Lean.Order.le_himp_of_meet_le_comm` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Order.le_himp_of_meet_le_comm.h5.{u} :
    ∀ {l : Type u} [inst : Lean.Order.CompleteLattice l] {P Q R : l},
      Lean.Order.PartialOrder.rel (Lean.Order.meet Q P) R → Lean.Order.PartialOrder.rel P (Lean.Order.himp Q R) :=
  no_implicit_lambda% (drop_unused% Lean.Order.le_himp_of_meet_le_comm 5)

-- `Lean.Order.le_himp` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Order.le_himp.h5.{u} :
    ∀ {l : Type u} [inst : Lean.Order.CompleteLattice l] {P Q R : l},
      Lean.Order.PartialOrder.rel (Lean.Order.meet P Q) R → Lean.Order.PartialOrder.rel P (Lean.Order.himp Q R) :=
  no_implicit_lambda% (drop_unused% Lean.Order.le_himp 5)

-- `Std.Internal.List.getValue_eq_getEntry_snd` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.getValue_eq_getEntry_snd.h3.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : BEq α] {l : List ((_ : α) × β)} {k : α}
      {h' : Std.Internal.List.containsKey k l = Bool.true},
      Std.Internal.List.getValue k l h' = (Std.Internal.List.getEntry k l h').snd :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.getValue_eq_getEntry_snd 3)

-- `Std.HashMap.forIn_eq_forIn` idx 8: unused in the library's proof
theorem HypCheckProof.Std.HashMap.forIn_eq_forIn.h8.{u, v, w, w'} :
    ∀ {α : Type u} {β : Type v} {x : BEq α} {x_1 : Hashable α} {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'}
      [inst : Monad m'] {f : α → β → δ → m' (ForInStep δ)} {init : δ},
      Std.HashMap.forIn f init m = ForIn.forIn m init fun (a : α × β) (d : δ) => f a.fst a.snd d :=
  no_implicit_lambda% (drop_unused% Std.HashMap.forIn_eq_forIn 8)

-- `Std.DTreeMap.Raw.forIn_eq_forIn` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.forIn_eq_forIn.h7.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} {δ : Type w}
      {m : Type w → Type w'} [inst : Monad m] {f : (a : α) → β a → δ → m (ForInStep δ)} {init : δ},
      Std.DTreeMap.Raw.forIn f init t = ForIn.forIn t init fun (a : (a : α) × β a) (b : δ) => f a.fst a.snd b :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.forIn_eq_forIn 7)

-- `Std.IterM.step_intermediateDropWhileM` idx 5: unused in the library's proof
theorem HypCheckProof.Std.IterM.step_intermediateDropWhileM.h5.{u_1, u_2} :
    ∀ {α : Type u_1} {m : Type u_1 → Type u_2} {β : Type u_1} [inst : Monad m] [inst_1 : MonadAttach m]
      [inst_2 : Std.Iterator α m β] {it : @Std.IterM α m β} {P : β → m (ULift Bool)} {dropping : Bool},
      @Eq
        (m
          (Std.Shrink
            (@Std.IterM.Step
              (Std.Iterators.Types.DropWhile α m β
                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
              m β
              (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
              (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))))
        (@Std.IterM.step
          (Std.Iterators.Types.DropWhile α m β
            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
          m β
          (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
          (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
        (@Bind.bind m (@Monad.toBind m inst) (Std.Shrink (@Std.IterM.Step α m β inst_2 it))
          (Std.Shrink
            (@Std.IterM.Step
              (Std.Iterators.Types.DropWhile α m β
                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
              m β
              (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
              (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
          (@Std.IterM.step α m β inst_2 it) fun (__do_lift : Std.Shrink (@Std.IterM.Step α m β inst_2 it)) =>
          @Std.IterM.step_intermediateDropWhileWithPostcondition.match_3 α m β inst_2 it
            (fun (x : @Std.IterM.Step α m β inst_2 it) =>
              m
                (Std.Shrink
                  (@Std.IterM.Step
                    (Std.Iterators.Types.DropWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β
                    (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))))
            (@Std.Shrink.inflate (@Std.IterM.Step α m β inst_2 it) __do_lift)
            (fun (it' : @Std.IterM α m β) (out : β)
                (h : @Std.IterM.IsPlausibleStep α m β inst_2 it (@Std.IterStep.yield (@Std.IterM α m β) β it' out)) =>
              @dite
                (m
                  (Std.Shrink
                    (@Std.IterM.Step
                      (Std.Iterators.Types.DropWhile α m β
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      m β
                      (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))))
                (@Eq Bool dropping Bool.true) (instDecidableEqBool dropping Bool.true)
                (fun (h' : @Eq Bool dropping Bool.true) =>
                  @Bind.bind m (@Monad.toBind m inst)
                    (@Subtype (ULift Bool) (@MonadAttach.CanReturn m inst_1 (ULift Bool) (P out)))
                    (Std.Shrink
                      (@Std.IterM.Step
                        (Std.Iterators.Types.DropWhile α m β
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                        m β
                        (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                        (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
                    (@MonadAttach.attach m inst_1 (ULift Bool) (P out))
                    fun (__do_lift : @Subtype (ULift Bool) (@MonadAttach.CanReturn m inst_1 (ULift Bool) (P out))) =>
                    @Std.IterM.step_intermediateDropWhileM.match_1 m β inst_1 P out
                      (fun (__do_lift : @Subtype (ULift Bool) (@MonadAttach.CanReturn m inst_1 (ULift Bool) (P out))) =>
                        m
                          (Std.Shrink
                            (@Std.IterM.Step
                              (Std.Iterators.Types.DropWhile α m β
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                              m β
                              (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                              (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))))
                      __do_lift
                      (fun (hP : @MonadAttach.CanReturn m inst_1 (ULift Bool) (P out) (@ULift.up Bool Bool.true)) =>
                        @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                          (Std.Shrink
                            (@Std.IterM.Step
                              (Std.Iterators.Types.DropWhile α m β
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                              m β
                              (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                              (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
                          (@Std.Shrink.deflate
                            (@Std.IterM.Step
                              (Std.Iterators.Types.DropWhile α m β
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                              m β
                              (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                              (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                            (@Std.PlausibleIterStep.skip
                              (@Std.IterM
                                (Std.Iterators.Types.DropWhile α m β
                                  (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                    (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                                m β)
                              β
                              (@Std.IterM.IsPlausibleStep
                                (Std.Iterators.Types.DropWhile α m β
                                  (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                    (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                                m β
                                (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                                  (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                    (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                                (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                              (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P Bool.true it')
                              (@Std.Iterators.Types.DropWhile.PlausibleStep.dropped α m β inst_2
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                                (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it) it' out h h' hP))))
                      fun (hP : @MonadAttach.CanReturn m inst_1 (ULift Bool) (P out) (@ULift.up Bool Bool.false)) =>
                      @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                        (Std.Shrink
                          (@Std.IterM.Step
                            (Std.Iterators.Types.DropWhile α m β
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                            m β
                            (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                            (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
                        (@Std.Shrink.deflate
                          (@Std.IterM.Step
                            (Std.Iterators.Types.DropWhile α m β
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                            m β
                            (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                            (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                          (@Std.PlausibleIterStep.yield
                            (@Std.IterM
                              (Std.Iterators.Types.DropWhile α m β
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                              m β)
                            β
                            (@Std.IterM.IsPlausibleStep
                              (Std.Iterators.Types.DropWhile α m β
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                              m β
                              (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                              (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                            (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P Bool.false it') out
                            (@Std.Iterators.Types.DropWhile.PlausibleStep.start α m β inst_2
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                              (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it) it' out h h' hP))))
                fun (h' : Not (@Eq Bool dropping Bool.true)) =>
                @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                  (Std.Shrink
                    (@Std.IterM.Step
                      (Std.Iterators.Types.DropWhile α m β
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      m β
                      (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
                  (@Std.Shrink.deflate
                    (@Std.IterM.Step
                      (Std.Iterators.Types.DropWhile α m β
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      m β
                      (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                    (@Std.PlausibleIterStep.yield
                      (@Std.IterM
                        (Std.Iterators.Types.DropWhile α m β
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                        m β)
                      β
                      (@Std.IterM.IsPlausibleStep
                        (Std.Iterators.Types.DropWhile α m β
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                        m β
                        (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                        (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                      (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P Bool.false it') out
                      (@Std.Iterators.Types.DropWhile.PlausibleStep.yield α m β inst_2
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                        (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it) it' out h
                        (@Eq.rec Prop
                          (Not
                            (@Eq Bool
                              (@Std.Iterators.Types.DropWhile.dropping α m β
                                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                                (@Std.IterM.internalState
                                  (Std.Iterators.Types.DropWhile α m β
                                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                                  m β (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
                              Bool.true))
                          (fun (x : Prop)
                              (h :
                                @Eq Prop
                                  (Not
                                    (@Eq Bool
                                      (@Std.Iterators.Types.DropWhile.dropping α m β
                                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                                        (@Std.IterM.internalState
                                          (Std.Iterators.Types.DropWhile α m β
                                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                                          m β (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
                                      Bool.true))
                                  x) =>
                            x)
                          h'
                          (@Eq Bool
                            (@Std.Iterators.Types.DropWhile.dropping α m β
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                              (@Std.IterM.internalState
                                (Std.Iterators.Types.DropWhile α m β
                                  (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                    (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                                m β (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
                            Bool.false)
                          (Bool.not_eq_true
                            (@Std.Iterators.Types.DropWhile.dropping α m β
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                              (@Std.IterM.internalState
                                (Std.Iterators.Types.DropWhile α m β
                                  (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                    (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                                m β (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))))))))
            (fun (it' : @Std.IterM α m β)
                (h : @Std.IterM.IsPlausibleStep α m β inst_2 it (@Std.IterStep.skip (@Std.IterM α m β) β it')) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                (Std.Shrink
                  (@Std.IterM.Step
                    (Std.Iterators.Types.DropWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β
                    (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
                (@Std.Shrink.deflate
                  (@Std.IterM.Step
                    (Std.Iterators.Types.DropWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β
                    (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                  (@Std.PlausibleIterStep.skip
                    (@Std.IterM
                      (Std.Iterators.Types.DropWhile α m β
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      m β)
                    β
                    (@Std.IterM.IsPlausibleStep
                      (Std.Iterators.Types.DropWhile α m β
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      m β
                      (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                    (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it')
                    (@Std.Iterators.Types.DropWhile.PlausibleStep.skip α m β inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                      (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it) it' h))))
            fun (h : @Std.IterM.IsPlausibleStep α m β inst_2 it (@Std.IterStep.done (@Std.IterM α m β) β)) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
              (Std.Shrink
                (@Std.IterM.Step
                  (Std.Iterators.Types.DropWhile α m β
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                  m β
                  (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                  (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it)))
              (@Std.Shrink.deflate
                (@Std.IterM.Step
                  (Std.Iterators.Types.DropWhile α m β
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                  m β
                  (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                  (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                (@Std.PlausibleIterStep.done
                  (@Std.IterM
                    (Std.Iterators.Types.DropWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β)
                  β
                  (@Std.IterM.IsPlausibleStep
                    (Std.Iterators.Types.DropWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β
                    (@Std.Iterators.Types.DropWhile.instIterator α m β inst inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it))
                  (@Std.Iterators.Types.DropWhile.PlausibleStep.done α m β inst_2
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                    (@Std.IterM.Intermediate.dropWhileM α m β inst inst_1 P dropping it) h)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.step_intermediateDropWhileM 5)

-- `Std.DTreeMap.Internal.Impl.length_toList` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.length_toList.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β}, t.WF → t.toList.length = t.size :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.length_toList 4)

-- `Std.DTreeMap.Internal.Impl.length_keys` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.length_keys.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β}, t.WF → t.keys.length = t.size :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.length_keys 4)

-- `Std.DTreeMap.Internal.Cell.getEntry?_empty` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Cell.getEntry?_empty.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : @Std.LawfulEqOrd α inst] {k : α},
      @Eq (Option (@Sigma α fun (a : α) => β a))
        (@Std.DTreeMap.Internal.Cell.getEntry? α β inst k
          (@Std.DTreeMap.Internal.Cell.empty α β inst (@Ord.compare α inst k)))
        (@Option.none (@Sigma α fun (a : α) => β a)) :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Cell.getEntry?_empty 3)

-- `Std.DTreeMap.Internal.Cell.getEntry?_empty` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Cell.getEntry?_empty.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : @Std.OrientedOrd α inst] {k : α},
      @Eq (Option (@Sigma α fun (a : α) => β a))
        (@Std.DTreeMap.Internal.Cell.getEntry? α β inst k
          (@Std.DTreeMap.Internal.Cell.empty α β inst (@Ord.compare α inst k)))
        (@Option.none (@Sigma α fun (a : α) => β a)) :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Cell.getEntry?_empty 4)

-- `Std.ExtDHashMap.Const.ofList_nil` idx 4: unused in the library's proof
theorem HypCheckProof.Std.ExtDHashMap.Const.ofList_nil.h4.{u, v} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : Type v} [inst : @LawfulHashable α x x_1],
      @Eq (@Std.ExtDHashMap α (fun (x : α) => β) x x_1) (@Std.ExtDHashMap.Const.ofList α β x x_1 (@List.nil (Prod α β)))
        (@EmptyCollection.emptyCollection (@Std.ExtDHashMap α (fun (x : α) => β) x x_1)
          (@Std.ExtDHashMap.instEmptyCollection α (fun (x : α) => β) x x_1)) :=
  no_implicit_lambda% (drop_unused% Std.ExtDHashMap.Const.ofList_nil 4)

-- `Std.ExtDHashMap.Const.ofList_nil` idx 5: unused in the library's proof
theorem HypCheckProof.Std.ExtDHashMap.Const.ofList_nil.h5.{u, v} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : Type v} [inst : @EquivBEq α x],
      @Eq (@Std.ExtDHashMap α (fun (x : α) => β) x x_1) (@Std.ExtDHashMap.Const.ofList α β x x_1 (@List.nil (Prod α β)))
        (@EmptyCollection.emptyCollection (@Std.ExtDHashMap α (fun (x : α) => β) x x_1)
          (@Std.ExtDHashMap.instEmptyCollection α (fun (x : α) => β) x x_1)) :=
  no_implicit_lambda% (drop_unused% Std.ExtDHashMap.Const.ofList_nil 5)

-- `Std.HashMap.Raw.forM_eq_forM` idx 5: unused in the library's proof
theorem HypCheckProof.Std.HashMap.Raw.forM_eq_forM.h5.{u, v, w, w'} :
    ∀ {α : Type u} {β : Type v} {m : Std.HashMap.Raw α β} {m' : Type w → Type w'} [inst : Monad m'] {f : α → β → m' PUnit},
      Std.HashMap.Raw.forM f m = ForM.forM m fun (a : α × β) => f a.fst a.snd :=
  no_implicit_lambda% (drop_unused% Std.HashMap.Raw.forM_eq_forM 5)

-- `Std.Internal.List.getKey?_eq_some_iff'` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.getKey?_eq_some_iff'.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l : List ((a : α) × β a)} {k k' : α},
      Std.Internal.List.getKey? k l = Option.some k' ↔
        ∃ (h : Std.Internal.List.containsKey k l = Bool.true), Std.Internal.List.getKey k l h = k' :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.getKey?_eq_some_iff' 3)

-- `Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew?!_fst` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew?!_fst.h4.{u, v} :
    ∀ {α : Type u} {instOrd : Ord α} {β : Type v} {t : Std.DTreeMap.Internal.Impl α fun (x : α) => β} {k : α} {v : β},
      (Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew?! t k v).fst = Std.DTreeMap.Internal.Impl.Const.get? t k :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew?!_fst 4)

-- `Std.Iterators.HetT.property_bind` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iterators.HetT.property_bind.h4.{w, w', u, v} :
    ∀ {m : Type w → Type w'} {α : Type u} {β : Type v} [inst : Monad m] {x : Std.Iterators.HetT m α}
      {f : α → Std.Iterators.HetT m β}, (x.bind f).Property = fun (b : β) => ∃ (a : α), x.Property a ∧ (f a).Property b :=
  no_implicit_lambda% (drop_unused% Std.Iterators.HetT.property_bind 4)

-- `Std.Equivalence.property_step` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Equivalence.property_step.h5.{u_1, u_2} :
    ∀ {α : Type u_1} {m : Type u_1 → Type u_2} {β : Type u_1} [inst : Std.Iterator α m β] [inst_1 : Monad m]
      {it : @Std.IterM α m β},
      @Eq (Std.IterStep (@Std.IterM α m β) β → Prop)
        (@Std.Iterators.HetT.Property m (Std.IterStep (@Std.IterM α m β) β) (@Std.IterM.stepAsHetT α m β inst inst_1 it))
        (@Std.IterM.IsPlausibleStep α m β inst it) :=
  no_implicit_lambda% (drop_unused% Std.Equivalence.property_step 5)

-- `Std.Internal.List.getKey!_eq_getKeyD_default` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.getKey!_eq_getKeyD_default.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Inhabited α] {l : List ((a : α) × β a)} {a : α},
      Std.Internal.List.getKey! a l = Std.Internal.List.getKeyD a l Inhabited.default :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.getKey!_eq_getKeyD_default 3)

-- `Std.DTreeMap.Raw.isEmpty_map` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.isEmpty_map.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} {γ : α → Type w}
      {f : (a : α) → β a → γ a}, (Std.DTreeMap.Raw.map f t).isEmpty = t.isEmpty :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.isEmpty_map 5)

-- `Std.DTreeMap.Raw.size_map` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.size_map.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} {γ : α → Type w}
      {f : (a : α) → β a → γ a}, (Std.DTreeMap.Raw.map f t).size = t.size :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.size_map 5)

-- `Std.Internal.List.length_left_le_length_insertListIfNew` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.length_left_le_length_insertListIfNew.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l toInsert : List ((a : α) × β a)},
      l.length ≤ (Std.Internal.List.insertListIfNew l toInsert).length :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.length_left_le_length_insertListIfNew 3)

-- `Std.Internal.List.length_insertListIfNewUnit_le` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.length_insertListIfNewUnit_le.h2.{u} :
    ∀ {α : Type u} [inst : BEq α] {l : List ((_ : α) × Unit)} {toInsert : List α},
      (Std.Internal.List.insertListIfNewUnit l toInsert).length ≤ l.length + toInsert.length :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.length_insertListIfNewUnit_le 2)

-- `Std.DTreeMap.Raw.WF.unitOfArray` idx 2: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.WF.unitOfArray.h2.{u} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {a : Array α}, (Std.DTreeMap.Raw.Const.unitOfArray a cmp).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.WF.unitOfArray 2)

-- `Std.DHashMap.Raw.insertMany_list_singleton` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.insertMany_list_singleton.h7.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α] {k : α} {v : β k}
      [inst_2 : LawfulHashable α], m.WF → m.insertMany [(⟨k, v⟩ : (a : α) × β a)] = m.insert k v :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.insertMany_list_singleton 7)

-- `Std.DHashMap.Raw.insertMany_list_singleton` idx 8: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.insertMany_list_singleton.h8.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α] {k : α} {v : β k}
      [inst_2 : EquivBEq α], m.WF → m.insertMany [(⟨k, v⟩ : (a : α) × β a)] = m.insert k v :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.insertMany_list_singleton 8)

-- `Std.Internal.List.minKey!_eq_default` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKey!_eq_default.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] [inst_3 : Inhabited α]
      {l : List ((a : α) × β a)}, l.isEmpty = Bool.true → Std.Internal.List.minKey! l = Inhabited.default :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKey!_eq_default 3)

-- `Std.Internal.List.minKey!_eq_default` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKey!_eq_default.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Inhabited α]
      {l : List ((a : α) × β a)}, l.isEmpty = Bool.true → Std.Internal.List.minKey! l = Inhabited.default :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKey!_eq_default 5)

-- `Std.DTreeMap.Internal.Impl.getThenInsertIfNew?_fst` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.getThenInsertIfNew?_fst.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β} [inst : Std.LawfulEqOrd α]
      (h : t.WF) {k : α} {v : β k}, (t.getThenInsertIfNew? k v (Std.DTreeMap.Internal.Impl.WF.balanced h)).fst = t.get? k :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.getThenInsertIfNew?_fst 4)

-- `Std.Ric.toList_iter` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Ric.toList_iter.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : DecidableLE α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxc.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Ric α}, r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Ric.toList_iter 5)

-- `Std.Ric.toArray_iter` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Ric.toArray_iter.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : DecidableLE α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxc.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Ric α}, r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Ric.toArray_iter 5)

-- `Std.Internal.List.isSome_minKey?_of_isSome_minKey?_eraseKey` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.isSome_minKey?_of_isSome_minKey?_eraseKey.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α}
      {l : List ((a : α) × β a)},
      (Std.Internal.List.minKey? (Std.Internal.List.eraseKey k l)).isSome = Bool.true →
        (Std.Internal.List.minKey? l).isSome = Bool.true :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.isSome_minKey?_of_isSome_minKey?_eraseKey 3)

-- `Std.Internal.List.isSome_minKey?_of_isSome_minKey?_eraseKey` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.isSome_minKey?_of_isSome_minKey?_eraseKey.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α}
      {l : List ((a : α) × β a)},
      (Std.Internal.List.minKey? (Std.Internal.List.eraseKey k l)).isSome = Bool.true →
        (Std.Internal.List.minKey? l).isSome = Bool.true :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.isSome_minKey?_of_isSome_minKey?_eraseKey 5)

-- `Std.Internal.List.minKeyD_eq_fallback` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKeyD_eq_fallback.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {l : List ((a : α) × β a)}
      {fallback : α}, l.isEmpty = Bool.true → Std.Internal.List.minKeyD l fallback = fallback :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKeyD_eq_fallback 3)

-- `Std.Internal.List.minKeyD_eq_fallback` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKeyD_eq_fallback.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((a : α) × β a)}
      {fallback : α}, l.isEmpty = Bool.true → Std.Internal.List.minKeyD l fallback = fallback :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKeyD_eq_fallback 5)

-- `Std.DTreeMap.Raw.getThenInsertIfNew?_fst` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.getThenInsertIfNew?_fst.h6.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Std.LawfulEqCmp cmp] {k : α} {v : β k}, (t.getThenInsertIfNew? k v).fst = t.get? k :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.getThenInsertIfNew?_fst 6)

-- `Std.DTreeMap.Internal.Impl.not_mem_of_isEmpty` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.not_mem_of_isEmpty.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β},
      t.WF → ∀ {a : α}, t.isEmpty = Bool.true → ¬a ∈ t :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.not_mem_of_isEmpty 4)

-- `Std.Rco.toList_iter` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Rco.toList_iter.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rco α},
      r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Rco.toList_iter 4)

-- `Std.Rco.toArray_iter_eq_toArray` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Rco.toArray_iter_eq_toArray.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rco α},
      r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Rco.toArray_iter_eq_toArray 4)

-- `Std.Roc.toArray_iter_eq_toArray` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Roc.toArray_iter_eq_toArray.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Roc α},
      r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Roc.toArray_iter_eq_toArray 4)

-- `Std.Rco.toList_iter_eq_toList` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Rco.toList_iter_eq_toList.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rco α},
      r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Rco.toList_iter_eq_toList 4)

-- `Std.Rcc.toList_iter_eq_toList` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Rcc.toList_iter_eq_toList.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rcc α},
      r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Rcc.toList_iter_eq_toList 4)

-- `Std.DHashMap.Raw.ofList_cons` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.ofList_cons.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : @LawfulHashable α inst inst_1] {k : α}
      {v : β k} {tl : List (@Sigma α fun (a : α) => β a)},
      @Eq (Std.DHashMap.Raw α β)
        (@Std.DHashMap.Raw.ofList α β inst inst_1
          (@List.cons (@Sigma α fun (a : α) => β a) (@Sigma.mk α (fun (a : α) => β a) k v) tl))
        (@Std.DHashMap.Raw.insertMany α β inst inst_1 (List (@Sigma α fun (a : α) => β a))
          (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
            (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
              (@List.instMembership (@Sigma α fun (a : α) => β a)))
            (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
          (@Std.DHashMap.Raw.insert α β inst inst_1
            (@EmptyCollection.emptyCollection (Std.DHashMap.Raw α β) (@Std.DHashMap.Raw.instEmptyCollection α β)) k v)
          tl) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.ofList_cons 4)

-- `Std.DHashMap.Raw.ofList_cons` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.ofList_cons.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : @EquivBEq α inst] {k : α} {v : β k}
      {tl : List (@Sigma α fun (a : α) => β a)},
      @Eq (Std.DHashMap.Raw α β)
        (@Std.DHashMap.Raw.ofList α β inst inst_1
          (@List.cons (@Sigma α fun (a : α) => β a) (@Sigma.mk α (fun (a : α) => β a) k v) tl))
        (@Std.DHashMap.Raw.insertMany α β inst inst_1 (List (@Sigma α fun (a : α) => β a))
          (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
            (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
              (@List.instMembership (@Sigma α fun (a : α) => β a)))
            (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
          (@Std.DHashMap.Raw.insert α β inst inst_1
            (@EmptyCollection.emptyCollection (Std.DHashMap.Raw α β) (@Std.DHashMap.Raw.instEmptyCollection α β)) k v)
          tl) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.ofList_cons 5)

-- `Std.DHashMap.equiv_iff_toList_perm` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.equiv_iff_toList_perm.h6.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} {m₁ m₂ : Std.DHashMap α β} [inst : LawfulHashable α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.equiv_iff_toList_perm 6)

-- `Std.DHashMap.equiv_iff_toList_perm` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.equiv_iff_toList_perm.h7.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} {m₁ m₂ : Std.DHashMap α β} [inst : EquivBEq α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.equiv_iff_toList_perm 7)

-- `Std.DHashMap.Const.equiv_iff_toList_perm` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Const.equiv_iff_toList_perm.h6.{u, v} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : Type v} {m₁ m₂ : Std.DHashMap α fun (x : α) => β}
      [inst : LawfulHashable α], m₁.Equiv m₂ ↔ (Std.DHashMap.Const.toList m₁).Perm (Std.DHashMap.Const.toList m₂) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Const.equiv_iff_toList_perm 6)

-- `Std.DHashMap.Const.equiv_iff_toList_perm` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Const.equiv_iff_toList_perm.h7.{u, v} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : Type v} {m₁ m₂ : Std.DHashMap α fun (x : α) => β}
      [inst : EquivBEq α], m₁.Equiv m₂ ↔ (Std.DHashMap.Const.toList m₁).Perm (Std.DHashMap.Const.toList m₂) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Const.equiv_iff_toList_perm 7)

-- `Std.DTreeMap.Internal.Impl.size_filterMap_le_size` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.size_filterMap_le_size.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β} {γ : α → Type w}
      {f : (a : α) → β a → Option (γ a)} (h : t.WF),
      (Std.DTreeMap.Internal.Impl.filterMap f t (Std.DTreeMap.Internal.Impl.WF.balanced h)).impl.size ≤ t.size :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.size_filterMap_le_size 5)

-- `Std.HashMap.Raw.equiv_iff_toList_perm` idx 6: unused in the library's proof
theorem HypCheckProof.Std.HashMap.Raw.equiv_iff_toList_perm.h6.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : BEq α] [inst_1 : Hashable α] {m₁ m₂ : Std.HashMap.Raw α β}
      [inst : LawfulHashable α], m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.HashMap.Raw.equiv_iff_toList_perm 6)

-- `Std.HashMap.Raw.equiv_iff_toList_perm` idx 7: unused in the library's proof
theorem HypCheckProof.Std.HashMap.Raw.equiv_iff_toList_perm.h7.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : BEq α] [inst_1 : Hashable α] {m₁ m₂ : Std.HashMap.Raw α β} [inst : EquivBEq α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.HashMap.Raw.equiv_iff_toList_perm 7)

-- `Std.DTreeMap.Internal.Impl.containsThenInsertIfNew_fst_eq_containsₘ` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.containsThenInsertIfNew_fst_eq_containsₘ.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] (t : Std.DTreeMap.Internal.Impl α β) (htb : t.Balanced) (a : α)
      (b : β a), (Std.DTreeMap.Internal.Impl.containsThenInsertIfNew a b t htb).fst = t.containsₘ a :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.containsThenInsertIfNew_fst_eq_containsₘ 3)

-- `Std.Internal.List.getKey?_append_of_containsKey_eq_false` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.getKey?_append_of_containsKey_eq_false.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l l' : List ((a : α) × β a)} {a : α},
      Std.Internal.List.containsKey a l' = Bool.false →
        Std.Internal.List.getKey? a (l ++ l') = Std.Internal.List.getKey? a l :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.getKey?_append_of_containsKey_eq_false 3)

-- `Std.Internal.List.Const.getKey_getValue_mem` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.Const.getKey_getValue_mem.h2.{u, v} :
    ∀ {α : Type u} [inst : BEq α] {β : Type v} {l : List ((_ : α) × β)} {k : α}
      {h : Std.Internal.List.containsKey k l = Bool.true},
      (⟨Std.Internal.List.getKey k l h, Std.Internal.List.getValue k l h⟩ : (_ : α) × β) ∈ l :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.Const.getKey_getValue_mem 2)

-- `Std.HashSet.equiv_iff_toList_perm` idx 5: unused in the library's proof
theorem HypCheckProof.Std.HashSet.equiv_iff_toList_perm.h5.{u} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m₁ m₂ : Std.HashSet α} [inst : LawfulHashable α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.HashSet.equiv_iff_toList_perm 5)

-- `Std.HashSet.equiv_iff_toList_perm` idx 6: unused in the library's proof
theorem HypCheckProof.Std.HashSet.equiv_iff_toList_perm.h6.{u} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m₁ m₂ : Std.HashSet α} [inst : EquivBEq α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.HashSet.equiv_iff_toList_perm 6)

-- `Std.HashSet.Raw.equiv_iff_toList_perm` idx 5: unused in the library's proof
theorem HypCheckProof.Std.HashSet.Raw.equiv_iff_toList_perm.h5.{u} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {m₁ m₂ : Std.HashSet.Raw α} [inst : LawfulHashable α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.HashSet.Raw.equiv_iff_toList_perm 5)

-- `Std.HashSet.Raw.equiv_iff_toList_perm` idx 6: unused in the library's proof
theorem HypCheckProof.Std.HashSet.Raw.equiv_iff_toList_perm.h6.{u} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {m₁ m₂ : Std.HashSet.Raw α} [inst : EquivBEq α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.HashSet.Raw.equiv_iff_toList_perm 6)

-- `Std.DTreeMap.Internal.Impl.size_filter_le_size` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.size_filter_le_size.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β} {f : (a : α) → β a → Bool}
      (h : t.WF), (Std.DTreeMap.Internal.Impl.filter f t (Std.DTreeMap.Internal.Impl.WF.balanced h)).impl.size ≤ t.size :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.size_filter_le_size 4)

-- `Std.DHashMap.Const.equiv_iff_keys_unit_perm` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Const.equiv_iff_keys_unit_perm.h3.{u} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} [inst : LawfulHashable α] {m₁ m₂ : Std.DHashMap α fun (x : α) => Unit},
      m₁.Equiv m₂ ↔ m₁.keys.Perm m₂.keys :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Const.equiv_iff_keys_unit_perm 3)

-- `Std.DHashMap.Const.equiv_iff_keys_unit_perm` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Const.equiv_iff_keys_unit_perm.h4.{u} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} [inst : EquivBEq α] {m₁ m₂ : Std.DHashMap α fun (x : α) => Unit},
      m₁.Equiv m₂ ↔ m₁.keys.Perm m₂.keys :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Const.equiv_iff_keys_unit_perm 4)

-- `Std.DTreeMap.Raw.WF.filterMap` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.WF.filterMap.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp}
      {f : (a : α) → β a → Option (β a)}, t.WF → (Std.DTreeMap.Raw.filterMap f t).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.WF.filterMap 4)

-- `Std.DHashMap.Internal.Raw₀.Const.map_fst_toList_eq_keys` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.map_fst_toList_eq_keys.h5.{u, v} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {β : Type v} (m : Std.DHashMap.Internal.Raw₀ α fun (x : α) => β)
      [inst : LawfulHashable α], List.map Prod.fst (Std.DHashMap.Raw.Const.toList m.val) = m.val.keys :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.Const.map_fst_toList_eq_keys 5)

-- `Std.DHashMap.Internal.Raw₀.Const.map_fst_toList_eq_keys` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.map_fst_toList_eq_keys.h6.{u, v} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {β : Type v} (m : Std.DHashMap.Internal.Raw₀ α fun (x : α) => β)
      [inst : EquivBEq α], List.map Prod.fst (Std.DHashMap.Raw.Const.toList m.val) = m.val.keys :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.Const.map_fst_toList_eq_keys 6)

-- `Std.DTreeMap.Internal.Impl.Const.size_filter_le_size` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.Const.size_filter_le_size.h4.{u, v} :
    ∀ {α : Type u} {instOrd : Ord α} {β : Type v} {t : Std.DTreeMap.Internal.Impl α fun (x : α) => β} {f : α → β → Bool}
      (h : t.WF), (Std.DTreeMap.Internal.Impl.filter f t (Std.DTreeMap.Internal.Impl.WF.balanced h)).impl.size ≤ t.size :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.Const.size_filter_le_size 4)

-- `Std.DTreeMap.forIn_eq_forIn` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.forIn_eq_forIn.h7.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {δ : Type w} {m : Type w → Type w'}
      [inst : Monad m] {f : (a : α) → β a → δ → m (ForInStep δ)} {init : δ},
      Std.DTreeMap.forIn f init t = ForIn.forIn t init fun (a : (a : α) × β a) (b : δ) => f a.fst a.snd b :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.forIn_eq_forIn 7)

-- `Std.Internal.List.DistinctKeys_impl_Pairwise_distinct` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.DistinctKeys_impl_Pairwise_distinct.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l : List ((a : α) × β a)},
      Std.Internal.List.DistinctKeys l → List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.DistinctKeys_impl_Pairwise_distinct 3)

-- `Std.Internal.List.minKey?_of_isEmpty` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKey?_of_isEmpty.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → Std.Internal.List.minKey? l = Option.none :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKey?_of_isEmpty 3)

-- `Std.TreeMap.Raw.forIn_eq_forIn` idx 7: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.Raw.forIn_eq_forIn.h7.{u, v, w, w'} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} {δ : Type w} {m : Type w → Type w'}
      [inst : Monad m] {f : α → β → δ → m (ForInStep δ)} {init : δ},
      Std.TreeMap.Raw.forIn f init t = ForIn.forIn t init fun (a : α × β) (d : δ) => f a.fst a.snd d :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.Raw.forIn_eq_forIn 7)

-- `Std.ExtDHashMap.ofList_nil` idx 4: unused in the library's proof
theorem HypCheckProof.Std.ExtDHashMap.ofList_nil.h4.{u, v} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} [inst : @LawfulHashable α x x_1],
      @Eq (@Std.ExtDHashMap α β x x_1) (@Std.ExtDHashMap.ofList α β x x_1 (@List.nil (@Sigma α fun (a : α) => β a)))
        (@EmptyCollection.emptyCollection (@Std.ExtDHashMap α β x x_1) (@Std.ExtDHashMap.instEmptyCollection α β x x_1)) :=
  no_implicit_lambda% (drop_unused% Std.ExtDHashMap.ofList_nil 4)

-- `Std.ExtDHashMap.ofList_nil` idx 5: unused in the library's proof
theorem HypCheckProof.Std.ExtDHashMap.ofList_nil.h5.{u, v} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} [inst : @EquivBEq α x],
      @Eq (@Std.ExtDHashMap α β x x_1) (@Std.ExtDHashMap.ofList α β x x_1 (@List.nil (@Sigma α fun (a : α) => β a)))
        (@EmptyCollection.emptyCollection (@Std.ExtDHashMap α β x x_1) (@Std.ExtDHashMap.instEmptyCollection α β x x_1)) :=
  no_implicit_lambda% (drop_unused% Std.ExtDHashMap.ofList_nil 5)

-- `Std.DHashMap.forM_eq_forM` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.forM_eq_forM.h7.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} {m : Std.DHashMap α β} {m' : Type w → Type w'}
      [inst : Monad m'] {f : (a : α) → β a → m' PUnit},
      Std.DHashMap.forM f m = ForM.forM m fun (a : (a : α) × β a) => f a.fst a.snd :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.forM_eq_forM 7)

-- `Std.Internal.List.foldlM_eq_foldlM_keys` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.foldlM_eq_foldlM_keys.h5.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {δ : Type w} {m' : Type w → Type w'} [inst : Monad m'] {l : List ((a : α) × β a)}
      {f : δ → α → m' δ} {init : δ},
      List.foldlM (fun (a : δ) (b : (a : α) × β a) => f a b.fst) init l = List.foldlM f init (Std.Internal.List.keys l) :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.foldlM_eq_foldlM_keys 5)

-- `Std.DHashMap.Const.forM_eq_forMUncurried` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Const.forM_eq_forMUncurried.h7.{u, v, w, w'} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m' : Type w → Type w'} {β : Type v} {m : Std.DHashMap α fun (x : α) => β}
      [inst : Monad m'] {f : α → β → m' PUnit},
      Std.DHashMap.forM f m = Std.DHashMap.Const.forMUncurried (fun (a : α × β) => f a.fst a.snd) m :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Const.forM_eq_forMUncurried 7)

-- `Std.HashMap.forM_eq_forM` idx 7: unused in the library's proof
theorem HypCheckProof.Std.HashMap.forM_eq_forM.h7.{u, v, w, w'} :
    ∀ {α : Type u} {β : Type v} {x : BEq α} {x_1 : Hashable α} {m : Std.HashMap α β} {m' : Type w → Type w'}
      [inst : Monad m'] {f : α → β → m' PUnit}, Std.HashMap.forM f m = ForM.forM m fun (a : α × β) => f a.fst a.snd :=
  no_implicit_lambda% (drop_unused% Std.HashMap.forM_eq_forM 7)

-- `Std.DHashMap.Raw.forIn_eq_forIn` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.forIn_eq_forIn.h6.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} {δ : Type w} {m' : Type w → Type w'} [inst : Monad m']
      {f : (a : α) → β a → δ → m' (ForInStep δ)} {init : δ},
      Std.DHashMap.Raw.forIn f init m = ForIn.forIn m init fun (a : (a : α) × β a) (b : δ) => f a.fst a.snd b :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.forIn_eq_forIn 6)

-- `Std.ExtDHashMap.Const.unitOfList_nil` idx 3: unused in the library's proof
theorem HypCheckProof.Std.ExtDHashMap.Const.unitOfList_nil.h3.{u} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} [inst : @LawfulHashable α x x_1],
      @Eq (@Std.ExtDHashMap α (fun (x : α) => Unit) x x_1) (@Std.ExtDHashMap.Const.unitOfList α x x_1 (@List.nil α))
        (@EmptyCollection.emptyCollection (@Std.ExtDHashMap α (fun (x : α) => Unit) x x_1)
          (@Std.ExtDHashMap.instEmptyCollection α (fun (x : α) => Unit) x x_1)) :=
  no_implicit_lambda% (drop_unused% Std.ExtDHashMap.Const.unitOfList_nil 3)

-- `Std.ExtDHashMap.Const.unitOfList_nil` idx 4: unused in the library's proof
theorem HypCheckProof.Std.ExtDHashMap.Const.unitOfList_nil.h4.{u} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} [inst : @EquivBEq α x],
      @Eq (@Std.ExtDHashMap α (fun (x : α) => Unit) x x_1) (@Std.ExtDHashMap.Const.unitOfList α x x_1 (@List.nil α))
        (@EmptyCollection.emptyCollection (@Std.ExtDHashMap α (fun (x : α) => Unit) x x_1)
          (@Std.ExtDHashMap.instEmptyCollection α (fun (x : α) => Unit) x x_1)) :=
  no_implicit_lambda% (drop_unused% Std.ExtDHashMap.Const.unitOfList_nil 4)

-- `Std.DTreeMap.forM_eq_forM` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.forM_eq_forM.h6.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {m : Type w → Type w'}
      [inst : Monad m] {f : (a : α) → β a → m PUnit},
      Std.DTreeMap.forM f t = ForM.forM t fun (a : (a : α) × β a) => f a.fst a.snd :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.forM_eq_forM 6)

-- `Std.DHashMap.Internal.Raw₀.toListModel_reinsertAux` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.toListModel_reinsertAux.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst : Hashable α]
      (data : { d : Array (Std.DHashMap.Internal.AssocList α β) // 0 < d.size }) (a : α) (b : β a),
      (Std.DHashMap.Internal.toListModel (Std.DHashMap.Internal.Raw₀.reinsertAux Hashable.hash data a b).val).Perm
        ((⟨a, b⟩ : (a : α) × β a) :: Std.DHashMap.Internal.toListModel data.val) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.toListModel_reinsertAux 4)

-- `Std.DTreeMap.Raw.Const.forM_eq_forMUncurried` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.Const.forM_eq_forMUncurried.h6.{u, v, w, w'} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {m : Type w → Type w'} {β : Type v}
      {t : Std.DTreeMap.Raw α (fun (x : α) => β) cmp} [inst : Monad m] {f : α → β → m PUnit},
      Std.DTreeMap.Raw.forM f t = Std.DTreeMap.Raw.Const.forMUncurried (fun (a : α × β) => f a.fst a.snd) t :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.Const.forM_eq_forMUncurried 6)

-- `Std.TreeMap.Raw.forM_eq_forM` idx 6: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.Raw.forM_eq_forM.h6.{u, v, w, w'} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} {m : Type w → Type w'}
      [inst : Monad m] {f : α → β → m PUnit}, Std.TreeMap.Raw.forM f t = ForM.forM t fun (a : α × β) => f a.fst a.snd :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.Raw.forM_eq_forM 6)

-- `Std.DTreeMap.size_map` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.size_map.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {γ : α → Type w}
      {f : (a : α) → β a → γ a}, (Std.DTreeMap.map f t).size = t.size :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.size_map 5)

-- `Std.Iterators.HetT.property_pbind` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iterators.HetT.property_pbind.h4.{w, w', u, v} :
    ∀ {m : Type w → Type w'} {α : Type u} {β : Type v} [inst : Monad m] {x : Std.Iterators.HetT m α}
      {f : (a : α) → x.Property a → Std.Iterators.HetT m β},
      (x.pbind f).Property = fun (b : β) => ∃ (a : α), ∃ (h : x.Property a), (f a h).Property b :=
  no_implicit_lambda% (drop_unused% Std.Iterators.HetT.property_pbind 4)

-- `Std.DHashMap.Raw.forM_eq_forM` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.forM_eq_forM.h5.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} {m' : Type w → Type w'} [inst : Monad m']
      {f : (a : α) → β a → m' PUnit}, Std.DHashMap.Raw.forM f m = ForM.forM m fun (a : (a : α) × β a) => f a.fst a.snd :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.forM_eq_forM 5)

-- `Std.DTreeMap.filterMap_equiv_map` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.filterMap_equiv_map.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {γ : α → Type w}
      {f : (a : α) → β a → γ a},
      (Std.DTreeMap.filterMap (fun (k : α) (v : β k) => Option.some (f k v)) t).Equiv (Std.DTreeMap.map f t) :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.filterMap_equiv_map 5)

-- `Std.DTreeMap.Raw.WF.ofArray` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.WF.ofArray.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {a : Array ((a : α) × β a)},
      (Std.DTreeMap.Raw.ofArray a cmp).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.WF.ofArray 3)

-- `Std.DTreeMap.Raw.WF.constOfList` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.WF.constOfList.h3.{u, v} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {β : Type v} {l : List (α × β)}, (Std.DTreeMap.Raw.Const.ofList l cmp).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.WF.constOfList 3)

-- `Std.DTreeMap.Raw.WF.ofList` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.WF.ofList.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {l : List ((a : α) × β a)}, (Std.DTreeMap.Raw.ofList l cmp).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.WF.ofList 3)

-- `Std.DTreeMap.Raw.WF.constOfArray` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.WF.constOfArray.h3.{u, v} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {β : Type v} {a : Array (α × β)}, (Std.DTreeMap.Raw.Const.ofArray a cmp).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.WF.constOfArray 3)

-- `Std.DTreeMap.Raw.WF.unitOfList` idx 2: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.WF.unitOfList.h2.{u} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {l : List α}, (Std.DTreeMap.Raw.Const.unitOfList l cmp).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.WF.unitOfList 2)

-- `Std.Internal.List.isSome_minEntry?_of_containsKey` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.isSome_minEntry?_of_containsKey.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α}
      {l : List ((a : α) × β a)},
      Std.Internal.List.containsKey k l = Bool.true → (Std.Internal.List.minEntry? l).isSome = Bool.true :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.isSome_minEntry?_of_containsKey 3)

-- `Std.Internal.List.isSome_minEntry?_of_containsKey` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.isSome_minEntry?_of_containsKey.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α}
      {l : List ((a : α) × β a)},
      Std.Internal.List.containsKey k l = Bool.true → (Std.Internal.List.minEntry? l).isSome = Bool.true :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.isSome_minEntry?_of_containsKey 5)

-- `Std.Roo.toList_iter` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Roo.toList_iter.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Roo α},
      r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Roo.toList_iter 4)

-- `Std.Roc.toList_iter_eq_toList` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Roc.toList_iter_eq_toList.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Roc α},
      r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Roc.toList_iter_eq_toList 4)

-- `Std.Rcc.toArray_iter_eq_toArray` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Rcc.toArray_iter_eq_toArray.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rcc α},
      r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Rcc.toArray_iter_eq_toArray 4)

-- `Std.DHashMap.Raw.insertMany_nil` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.insertMany_nil.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α]
      [inst_2 : LawfulHashable α], m.WF → m.insertMany [] = m :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.insertMany_nil 5)

-- `Std.DHashMap.Raw.insertMany_nil` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.insertMany_nil.h6.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α],
      m.WF → m.insertMany [] = m :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.insertMany_nil 6)

-- `Std.Internal.List.minKey_eq_get_minKey?` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKey_eq_get_minKey?.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : @Std.LawfulBEqOrd α inst_1 inst]
      {l : List (@Sigma α fun (a : α) => β a)} {he : @Eq Bool (@List.isEmpty (@Sigma α fun (a : α) => β a) l) Bool.false},
      @Eq α (@Std.Internal.List.minKey α β inst l he)
        (@Option.get α (@Std.Internal.List.minKey? α β inst l)
          (@Std.Internal.List.minKey_eq_get_minKey?._proof_1 α β inst l he)) :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKey_eq_get_minKey? 3)

-- `Std.Internal.List.minKey_eq_get_minKey?` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKey_eq_get_minKey?.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : @Std.TransOrd α inst] [inst_2 : BEq α]
      {l : List (@Sigma α fun (a : α) => β a)} {he : @Eq Bool (@List.isEmpty (@Sigma α fun (a : α) => β a) l) Bool.false},
      @Eq α (@Std.Internal.List.minKey α β inst l he)
        (@Option.get α (@Std.Internal.List.minKey? α β inst l)
          (@Std.Internal.List.minKey_eq_get_minKey?._proof_1 α β inst l he)) :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKey_eq_get_minKey? 5)

-- `Std.Internal.List.maxKey_eq_get_maxKey?` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.maxKey_eq_get_maxKey?.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : @Std.LawfulBEqOrd α inst_1 inst]
      {l : List (@Sigma α fun (a : α) => β a)} {he : @Eq Bool (@List.isEmpty (@Sigma α fun (a : α) => β a) l) Bool.false},
      @Eq α (@Std.Internal.List.maxKey α β inst l he)
        (@Option.get α (@Std.Internal.List.maxKey? α β inst l)
          (@Std.Internal.List.maxKey_eq_get_maxKey?._proof_1 α β inst l he)) :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.maxKey_eq_get_maxKey? 3)

-- `Std.Internal.List.maxKey_eq_get_maxKey?` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.maxKey_eq_get_maxKey?.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : @Std.TransOrd α inst] [inst_2 : BEq α]
      {l : List (@Sigma α fun (a : α) => β a)} {he : @Eq Bool (@List.isEmpty (@Sigma α fun (a : α) => β a) l) Bool.false},
      @Eq α (@Std.Internal.List.maxKey α β inst l he)
        (@Option.get α (@Std.Internal.List.maxKey? α β inst l)
          (@Std.Internal.List.maxKey_eq_get_maxKey?._proof_1 α β inst l he)) :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.maxKey_eq_get_maxKey? 5)

-- `Std.DTreeMap.Internal.Impl.get_eq_get?` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.get_eq_get?.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.LawfulEqOrd α] (k : α) (l : Std.DTreeMap.Internal.Impl α β)
      {h : k ∈ l}, Option.some (l.get k h) = l.get? k :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.get_eq_get? 3)

-- `Std.Iterators.HetT.pmap_congr` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iterators.HetT.pmap_congr.h4.{w, w', u, v} :
    ∀ {m : Type w → Type w'} {α : Type u} {β : Type v} [inst : Monad m] {x y : Std.Iterators.HetT m α}
      {f : (a : α) → x.Property a → β} (h : x = y),
      x.pmap f = y.pmap fun (a : α) (ha : y.Property a) => f a (Eq.symm h ▸ ha) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.HetT.pmap_congr 4)

-- `Std.DTreeMap.Internal.Impl.WF.interSmallerFn` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.WF.interSmallerFn.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {x : Ord α} [inst : BEq α] (m₁ m₂ : Std.DTreeMap.Internal.Impl α β) (hm₂ : m₂.WF)
      (k : α),
      (m₁.interSmallerFn
            (⟨m₂, Std.DTreeMap.Internal.Impl.WF.balanced hm₂⟩ : { t : Std.DTreeMap.Internal.Impl α β // t.Balanced })
            k).val.WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.WF.interSmallerFn 3)

-- `Std.Internal.List.minKey!_eq_get!_minKey?` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKey!_eq_get!_minKey?.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] [inst_3 : Inhabited α]
      {l : List ((a : α) × β a)}, Std.Internal.List.minKey! l = (Std.Internal.List.minKey? l).get! :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKey!_eq_get!_minKey? 3)

-- `Std.Internal.List.minKey!_eq_get!_minKey?` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.minKey!_eq_get!_minKey?.h5.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Inhabited α]
      {l : List ((a : α) × β a)}, Std.Internal.List.minKey! l = (Std.Internal.List.minKey? l).get! :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.minKey!_eq_get!_minKey? 5)

-- `Std.HashMap.equiv_iff_toList_perm` idx 6: unused in the library's proof
theorem HypCheckProof.Std.HashMap.equiv_iff_toList_perm.h6.{u, v} :
    ∀ {α : Type u} {β : Type v} {x : BEq α} {x_1 : Hashable α} {m₁ m₂ : Std.HashMap α β} [inst : LawfulHashable α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.HashMap.equiv_iff_toList_perm 6)

-- `Std.HashMap.equiv_iff_toList_perm` idx 7: unused in the library's proof
theorem HypCheckProof.Std.HashMap.equiv_iff_toList_perm.h7.{u, v} :
    ∀ {α : Type u} {β : Type v} {x : BEq α} {x_1 : Hashable α} {m₁ m₂ : Std.HashMap α β} [inst : EquivBEq α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.HashMap.equiv_iff_toList_perm 7)

-- `Std.DTreeMap.Raw.filterMap_equiv_map` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.filterMap_equiv_map.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} {γ : α → Type w}
      {f : (a : α) → β a → γ a},
      t.WF → (Std.DTreeMap.Raw.filterMap (fun (k : α) (v : β k) => Option.some (f k v)) t).Equiv (Std.DTreeMap.Raw.map f t) :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.filterMap_equiv_map 5)

-- `Std.DTreeMap.Internal.Impl.getThenInsertIfNew?!_fst` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.getThenInsertIfNew?!_fst.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β} [inst : Std.LawfulEqOrd α]
      {k : α} {v : β k}, (t.getThenInsertIfNew?! k v).fst = t.get? k :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.getThenInsertIfNew?!_fst 4)

-- `Std.DTreeMap.Internal.Impl.containsThenInsertIfNew_snd` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.containsThenInsertIfNew_snd.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β} (h : t.WF) {k : α} {v : β k},
      (Std.DTreeMap.Internal.Impl.containsThenInsertIfNew k v t (Std.DTreeMap.Internal.Impl.WF.balanced h)).snd.impl =
        (Std.DTreeMap.Internal.Impl.insertIfNew k v t (Std.DTreeMap.Internal.Impl.WF.balanced h)).impl :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.containsThenInsertIfNew_snd 4)

-- `Std.DTreeMap.Raw.Const.getThenInsertIfNew?_fst` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.Const.getThenInsertIfNew?_fst.h5.{u, v} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {β : Type v} {t : Std.DTreeMap.Raw α (fun (x : α) => β) cmp}
      [inst : Std.TransCmp cmp] {k : α} {v : β},
      (Std.DTreeMap.Raw.Const.getThenInsertIfNew? t k v).fst = Std.DTreeMap.Raw.Const.get? t k :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.Const.getThenInsertIfNew?_fst 5)

-- `Std.Internal.List.getKey_eq_getKeyD` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.getKey_eq_getKeyD.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l : List ((a : α) × β a)} {a fallback : α}
      (h : Std.Internal.List.containsKey a l = Bool.true),
      Std.Internal.List.getKey a l h = Std.Internal.List.getKeyD a l fallback :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.getKey_eq_getKeyD 3)

-- `Std.DTreeMap.Internal.Impl.WF.insert!` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.WF.insert!.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {x : Ord α} {k : α} {v : β k} {l : Std.DTreeMap.Internal.Impl α β},
      l.WF → (Std.DTreeMap.Internal.Impl.insert! k v l).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.WF.insert! 3)

-- `Std.DTreeMap.Internal.Impl.WF.containsThenInsert!` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.WF.containsThenInsert!.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {x : Ord α} {k : α} {v : β k} {t : Std.DTreeMap.Internal.Impl α β},
      t.WF → (Std.DTreeMap.Internal.Impl.containsThenInsert! k v t).snd.WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.WF.containsThenInsert! 3)

-- `Std.Internal.List.mem_replaceEntry_of_true` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.mem_replaceEntry_of_true.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k},
      Std.Internal.List.containsKey k l = Bool.true → (⟨k, v⟩ : (a : α) × β a) ∈ Std.Internal.List.replaceEntry k v l :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.mem_replaceEntry_of_true 3)

-- `Std.DTreeMap.Internal.Impl.WF.insertIfNew!` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.WF.insertIfNew!.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {x : Ord α} {k : α} {v : β k} {l : Std.DTreeMap.Internal.Impl α β},
      l.WF → (Std.DTreeMap.Internal.Impl.insertIfNew! k v l).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.WF.insertIfNew! 3)

-- `Std.DTreeMap.Raw.WF.filter` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.WF.filter.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} {f : (a : α) → β a → Bool},
      t.WF → (Std.DTreeMap.Raw.filter f t).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.WF.filter 4)

-- `Std.DTreeMap.Internal.Impl.getD_empty` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.getD_empty.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} [inst : Std.LawfulEqOrd α] {a : α} {fallback : β a},
      Std.DTreeMap.Internal.Impl.empty.getD a fallback = fallback :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.getD_empty 3)

-- `Std.HashMap.equiv_iff_keys_unit_perm` idx 5: unused in the library's proof
theorem HypCheckProof.Std.HashMap.equiv_iff_keys_unit_perm.h5.{u} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m₁ m₂ : Std.HashMap α Unit} [inst : LawfulHashable α],
      m₁.Equiv m₂ ↔ m₁.keys.Perm m₂.keys :=
  no_implicit_lambda% (drop_unused% Std.HashMap.equiv_iff_keys_unit_perm 5)

-- `Std.HashMap.equiv_iff_keys_unit_perm` idx 6: unused in the library's proof
theorem HypCheckProof.Std.HashMap.equiv_iff_keys_unit_perm.h6.{u} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m₁ m₂ : Std.HashMap α Unit} [inst : EquivBEq α],
      m₁.Equiv m₂ ↔ m₁.keys.Perm m₂.keys :=
  no_implicit_lambda% (drop_unused% Std.HashMap.equiv_iff_keys_unit_perm 6)

-- `Std.DTreeMap.Internal.Impl.WF.inter!` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.WF.inter!.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {x : Ord α} {m₁ m₂ : Std.DTreeMap.Internal.Impl α β}, m₁.WF → (m₁.inter! m₂).WF :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.WF.inter! 3)

-- `Std.DHashMap.forIn_eq_forIn` idx 8: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.forIn_eq_forIn.h8.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} {m : Std.DHashMap α β} {δ : Type w}
      {m' : Type w → Type w'} [inst : Monad m'] {f : (a : α) → β a → δ → m' (ForInStep δ)} {init : δ},
      Std.DHashMap.forIn f init m = ForIn.forIn m init fun (a : (a : α) × β a) (b : δ) => f a.fst a.snd b :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.forIn_eq_forIn 8)

-- `Std.DHashMap.Const.forIn_eq_forInUncurried` idx 8: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Const.forIn_eq_forInUncurried.h8.{u, v, w, w'} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {δ : Type w} {m' : Type w → Type w'} {β : Type v}
      {m : Std.DHashMap α fun (x : α) => β} [inst : Monad m'] {f : α → β → δ → m' (ForInStep δ)} {init : δ},
      Std.DHashMap.forIn f init m = Std.DHashMap.Const.forInUncurried (fun (a : α × β) (b : δ) => f a.fst a.snd b) init m :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Const.forIn_eq_forInUncurried 8)

-- `Std.DTreeMap.Raw.Const.forIn_eq_forInUncurried` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.Const.forIn_eq_forInUncurried.h7.{u, v, w, w'} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {δ : Type w} {m : Type w → Type w'} {β : Type v}
      {t : Std.DTreeMap.Raw α (fun (x : α) => β) cmp} [inst : Monad m] {f : α → β → δ → m (ForInStep δ)} {init : δ},
      Std.DTreeMap.Raw.forIn f init t =
        Std.DTreeMap.Raw.Const.forInUncurried (fun (a : α × β) (b : δ) => f a.fst a.snd b) init t :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.Const.forIn_eq_forInUncurried 7)

-- `Std.TreeMap.forIn_eq_forIn` idx 7: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.forIn_eq_forIn.h7.{u, v, w, w'} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type w} {m : Type w → Type w'}
      [inst : Monad m] {f : α → β → δ → m (ForInStep δ)} {init : δ},
      Std.TreeMap.forIn f init t = ForIn.forIn t init fun (a : α × β) (d : δ) => f a.fst a.snd d :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.forIn_eq_forIn 7)

-- `Std.DTreeMap.Const.forIn_eq_forInUncurried` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Const.forIn_eq_forInUncurried.h7.{u, v, w, w'} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {δ : Type w} {m : Type w → Type w'} {β : Type v}
      {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Monad m] {f : α → β → δ → m (ForInStep δ)} {init : δ},
      Std.DTreeMap.forIn f init t = Std.DTreeMap.Const.forInUncurried (fun (a : α × β) (b : δ) => f a.fst a.snd b) init t :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Const.forIn_eq_forInUncurried 7)

-- `Std.TreeSet.forIn_eq_forIn` idx 6: unused in the library's proof
theorem HypCheckProof.Std.TreeSet.forIn_eq_forIn.h6.{u, w, w'} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {δ : Type w} {m : Type w → Type w'} [inst : Monad m]
      {f : α → δ → m (ForInStep δ)} {init : δ}, Std.TreeSet.forIn f init t = ForIn.forIn t init f :=
  no_implicit_lambda% (drop_unused% Std.TreeSet.forIn_eq_forIn 6)

-- `Std.IterM.step_takeWhileM` idx 5: unused in the library's proof
theorem HypCheckProof.Std.IterM.step_takeWhileM.h5.{u_1, u_2} :
    ∀ {α : Type u_1} {m : Type u_1 → Type u_2} {β : Type u_1} [inst : Monad m] [inst_1 : MonadAttach m]
      [inst_2 : Std.Iterator α m β] {it : @Std.IterM α m β} {P : β → m (ULift Bool)},
      @Eq
        (m
          (Std.Shrink
            (@Std.IterM.Step
              (Std.Iterators.Types.TakeWhile α m β
                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
              m β
              (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
              (@Std.IterM.takeWhileM α m β inst inst_1 P it))))
        (@Std.IterM.step
          (Std.Iterators.Types.TakeWhile α m β
            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
          m β
          (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
          (@Std.IterM.takeWhileM α m β inst inst_1 P it))
        (@Bind.bind m (@Monad.toBind m inst) (Std.Shrink (@Std.IterM.Step α m β inst_2 it))
          (Std.Shrink
            (@Std.IterM.Step
              (Std.Iterators.Types.TakeWhile α m β
                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
              m β
              (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                  (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
              (@Std.IterM.takeWhileM α m β inst inst_1 P it)))
          (@Std.IterM.step α m β inst_2 it) fun (__do_lift : Std.Shrink (@Std.IterM.Step α m β inst_2 it)) =>
          @Std.IterM.step_takeWhileWithPostcondition.match_3 α m β inst_2 it
            (fun (x : @Std.IterM.Step α m β inst_2 it) =>
              m
                (Std.Shrink
                  (@Std.IterM.Step
                    (Std.Iterators.Types.TakeWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β
                    (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    (@Std.IterM.takeWhileM α m β inst inst_1 P it))))
            (@Std.Shrink.inflate (@Std.IterM.Step α m β inst_2 it) __do_lift)
            (fun (it' : @Std.IterM α m β) (out : β)
                (h : @Std.IterM.IsPlausibleStep α m β inst_2 it (@Std.IterStep.yield (@Std.IterM α m β) β it' out)) =>
              @Bind.bind m (@Monad.toBind m inst)
                (@Subtype (ULift Bool) (@MonadAttach.CanReturn m inst_1 (ULift Bool) (P out)))
                (Std.Shrink
                  (@Std.IterM.Step
                    (Std.Iterators.Types.TakeWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β
                    (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    (@Std.IterM.takeWhileM α m β inst inst_1 P it)))
                (@MonadAttach.attach m inst_1 (ULift Bool) (P out))
                fun (__do_lift : @Subtype (ULift Bool) (@MonadAttach.CanReturn m inst_1 (ULift Bool) (P out))) =>
                @Std.IterM.step_takeWhileM.match_1 m β inst_1 P out
                  (fun (__do_lift : @Subtype (ULift Bool) (@MonadAttach.CanReturn m inst_1 (ULift Bool) (P out))) =>
                    m
                      (Std.Shrink
                        (@Std.IterM.Step
                          (Std.Iterators.Types.TakeWhile α m β
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                          m β
                          (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                          (@Std.IterM.takeWhileM α m β inst inst_1 P it))))
                  __do_lift
                  (fun (hP : @MonadAttach.CanReturn m inst_1 (ULift Bool) (P out) (@ULift.up Bool Bool.true)) =>
                    @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                      (Std.Shrink
                        (@Std.IterM.Step
                          (Std.Iterators.Types.TakeWhile α m β
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                          m β
                          (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                          (@Std.IterM.takeWhileM α m β inst inst_1 P it)))
                      (@Std.Shrink.deflate
                        (@Std.IterM.Step
                          (Std.Iterators.Types.TakeWhile α m β
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                          m β
                          (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                          (@Std.IterM.takeWhileM α m β inst inst_1 P it))
                        (@Std.PlausibleIterStep.yield
                          (@Std.IterM
                            (Std.Iterators.Types.TakeWhile α m β
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                            m β)
                          β
                          (@Std.IterM.IsPlausibleStep
                            (Std.Iterators.Types.TakeWhile α m β
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                            m β
                            (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                              (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                            (@Std.IterM.takeWhileM α m β inst inst_1 P it))
                          (@Std.IterM.takeWhileM α m β inst inst_1 P it') out
                          (@Std.Iterators.Types.TakeWhile.PlausibleStep.yield α m β inst_2
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                            (@Std.IterM.takeWhileM α m β inst inst_1 P it) it' out h hP))))
                  fun (hP : @MonadAttach.CanReturn m inst_1 (ULift Bool) (P out) (@ULift.up Bool Bool.false)) =>
                  @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                    (Std.Shrink
                      (@Std.IterM.Step
                        (Std.Iterators.Types.TakeWhile α m β
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                        m β
                        (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                        (@Std.IterM.takeWhileM α m β inst inst_1 P it)))
                    (@Std.Shrink.deflate
                      (@Std.IterM.Step
                        (Std.Iterators.Types.TakeWhile α m β
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                        m β
                        (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                        (@Std.IterM.takeWhileM α m β inst inst_1 P it))
                      (@Std.PlausibleIterStep.done
                        (@Std.IterM
                          (Std.Iterators.Types.TakeWhile α m β
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                          m β)
                        β
                        (@Std.IterM.IsPlausibleStep
                          (Std.Iterators.Types.TakeWhile α m β
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                          m β
                          (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                            (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                          (@Std.IterM.takeWhileM α m β inst inst_1 P it))
                        (@Std.Iterators.Types.TakeWhile.PlausibleStep.rejected α m β inst_2
                          (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                            (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                          (@Std.IterM.takeWhileM α m β inst inst_1 P it) it' out h hP))))
            (fun (it' : @Std.IterM α m β)
                (h : @Std.IterM.IsPlausibleStep α m β inst_2 it (@Std.IterStep.skip (@Std.IterM α m β) β it')) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                (Std.Shrink
                  (@Std.IterM.Step
                    (Std.Iterators.Types.TakeWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β
                    (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    (@Std.IterM.takeWhileM α m β inst inst_1 P it)))
                (@Std.Shrink.deflate
                  (@Std.IterM.Step
                    (Std.Iterators.Types.TakeWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β
                    (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    (@Std.IterM.takeWhileM α m β inst inst_1 P it))
                  (@Std.PlausibleIterStep.skip
                    (@Std.IterM
                      (Std.Iterators.Types.TakeWhile α m β
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      m β)
                    β
                    (@Std.IterM.IsPlausibleStep
                      (Std.Iterators.Types.TakeWhile α m β
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      m β
                      (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                        (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                          (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                      (@Std.IterM.takeWhileM α m β inst inst_1 P it))
                    (@Std.IterM.takeWhileM α m β inst inst_1 P it')
                    (@Std.Iterators.Types.TakeWhile.PlausibleStep.skip α m β inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                      (@Std.IterM.takeWhileM α m β inst inst_1 P it) it' h))))
            fun (h : @Std.IterM.IsPlausibleStep α m β inst_2 it (@Std.IterStep.done (@Std.IterM α m β) β)) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
              (Std.Shrink
                (@Std.IterM.Step
                  (Std.Iterators.Types.TakeWhile α m β
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                  m β
                  (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                  (@Std.IterM.takeWhileM α m β inst inst_1 P it)))
              (@Std.Shrink.deflate
                (@Std.IterM.Step
                  (Std.Iterators.Types.TakeWhile α m β
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                  m β
                  (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                  (@Std.IterM.takeWhileM α m β inst inst_1 P it))
                (@Std.PlausibleIterStep.done
                  (@Std.IterM
                    (Std.Iterators.Types.TakeWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β)
                  β
                  (@Std.IterM.IsPlausibleStep
                    (Std.Iterators.Types.TakeWhile α m β
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    m β
                    (@Std.Iterators.Types.TakeWhile.instIterator α m β inst inst_2
                      (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                        (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P))
                    (@Std.IterM.takeWhileM α m β inst inst_1 P it))
                  (@Std.Iterators.Types.TakeWhile.PlausibleStep.done α m β inst_2
                    (@Function.comp β (m (ULift Bool)) (Std.Iterators.PostconditionT m (ULift Bool))
                      (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_1) P)
                    (@Std.IterM.takeWhileM α m β inst inst_1 P it) h)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.step_takeWhileM 5)

-- `Std.Internal.List.foldlM_eq_foldlM_toProd` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.foldlM_eq_foldlM_toProd.h5.{u, v, w, w'} :
    ∀ {α : Type u} {β : Type v} {δ : Type w} {m' : Type w → Type w'} [inst : Monad m'] {l : List ((_ : α) × β)}
      {f : δ → α → β → m' δ} {init : δ},
      List.foldlM (fun (a : δ) (b : (_ : α) × β) => f a b.fst b.snd) init l =
        List.foldlM (fun (a : δ) (b : α × β) => f a b.fst b.snd) init (List.map (fun (x : (_ : α) × β) => (x.fst, x.snd)) l) :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.foldlM_eq_foldlM_toProd 5)

-- `Std.DHashMap.Raw.Const.forIn_eq_forInUncurried` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.Const.forIn_eq_forInUncurried.h6.{u, v, w, w'} :
    ∀ {α : Type u} {δ : Type w} {m' : Type w → Type w'} {β : Type v} {m : Std.DHashMap.Raw α fun (x : α) => β}
      [inst : Monad m'] {f : α → β → δ → m' (ForInStep δ)} {init : δ},
      Std.DHashMap.Raw.forIn f init m =
        Std.DHashMap.Raw.Const.forInUncurried (fun (a : α × β) (b : δ) => f a.fst a.snd b) init m :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.Const.forIn_eq_forInUncurried 6)

-- `Std.HashMap.Raw.forIn_eq_forIn` idx 6: unused in the library's proof
theorem HypCheckProof.Std.HashMap.Raw.forIn_eq_forIn.h6.{u, v, w, w'} :
    ∀ {α : Type u} {β : Type v} {m : Std.HashMap.Raw α β} {δ : Type w} {m' : Type w → Type w'} [inst : Monad m']
      {f : α → β → δ → m' (ForInStep δ)} {init : δ},
      Std.HashMap.Raw.forIn f init m = ForIn.forIn m init fun (a : α × β) (d : δ) => f a.fst a.snd d :=
  no_implicit_lambda% (drop_unused% Std.HashMap.Raw.forIn_eq_forIn 6)

-- `Std.HashSet.Raw.forIn_eq_forIn` idx 5: unused in the library's proof
theorem HypCheckProof.Std.HashSet.Raw.forIn_eq_forIn.h5.{u, v, w} :
    ∀ {α : Type u} {m : Std.HashSet.Raw α} {δ : Type v} {m' : Type v → Type w} [inst : Monad m']
      {f : α → δ → m' (ForInStep δ)} {init : δ}, Std.HashSet.Raw.forIn f init m = ForIn.forIn m init f :=
  no_implicit_lambda% (drop_unused% Std.HashSet.Raw.forIn_eq_forIn 5)

-- `Std.HashSet.forM_eq_forM` idx 6: unused in the library's proof
theorem HypCheckProof.Std.HashSet.forM_eq_forM.h6.{u, v, w} :
    ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.HashSet α} {m' : Type v → Type w} [inst : Monad m']
      {f : α → m' PUnit}, Std.HashSet.forM f m = ForM.forM m f :=
  no_implicit_lambda% (drop_unused% Std.HashSet.forM_eq_forM 6)

-- `Std.Internal.List.find?_map_toProd_eq_some_iff_getKey?_eq_some_and_getValue?_eq_some` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.find?_map_toProd_eq_some_iff_getKey?_eq_some_and_getValue?_eq_some.h2.{u, v} :
    ∀ {α : Type u} [inst : BEq α] {β : Type v} {k k' : α} {v : β} {l : List ((_ : α) × β)},
      List.find? (fun (a : α × β) => a.fst == k) (List.map (fun (x : (_ : α) × β) => (x.fst, x.snd)) l) =
          Option.some (k', v) ↔
        Std.Internal.List.getKey? k l = Option.some k' ∧ Std.Internal.List.getValue? k l = Option.some v :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.find?_map_toProd_eq_some_iff_getKey?_eq_some_and_getValue?_eq_some 2)

-- `Std.DTreeMap.Const.forM_eq_forMUncurried` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Const.forM_eq_forMUncurried.h6.{u, v, w, w'} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {m : Type w → Type w'} {β : Type v} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
      [inst : Monad m] {f : α → β → m PUnit},
      Std.DTreeMap.forM f t = Std.DTreeMap.Const.forMUncurried (fun (a : α × β) => f a.fst a.snd) t :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Const.forM_eq_forMUncurried 6)

-- `Std.DHashMap.Internal.Raw₀.Const.alter_eq_alterₘ` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.alter_eq_alterₘ.h4.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : BEq α] [inst_1 : Hashable α] (m : Std.DHashMap.Internal.Raw₀ α fun (x : α) => β)
      (a : α) (f : Option β → Option β),
      Std.DHashMap.Internal.Raw₀.Const.alter m a f = Std.DHashMap.Internal.Raw₀.Const.alterₘ m a f :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.Const.alter_eq_alterₘ 4)

-- `Std.TreeSet.forM_eq_forM` idx 5: unused in the library's proof
theorem HypCheckProof.Std.TreeSet.forM_eq_forM.h5.{u, w, w'} :
    ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {m : Type w → Type w'} [inst : Monad m]
      {f : α → m PUnit}, Std.TreeSet.forM f t = ForM.forM t f :=
  no_implicit_lambda% (drop_unused% Std.TreeSet.forM_eq_forM 5)

-- `Std.DHashMap.Raw.Const.forM_eq_forMUncurried` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.Const.forM_eq_forMUncurried.h5.{u, v, w, w'} :
    ∀ {α : Type u} {m' : Type w → Type w'} {β : Type v} {m : Std.DHashMap.Raw α fun (x : α) => β} [inst : Monad m']
      {f : α → β → m' PUnit},
      Std.DHashMap.Raw.forM f m = Std.DHashMap.Raw.Const.forMUncurried (fun (a : α × β) => f a.fst a.snd) m :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.Const.forM_eq_forMUncurried 5)

-- `Std.DTreeMap.isEmpty_map` idx 5: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.isEmpty_map.h5.{u, v, w} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {γ : α → Type w}
      {f : (a : α) → β a → γ a}, (Std.DTreeMap.map f t).isEmpty = t.isEmpty :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.isEmpty_map 5)

-- `Std.DHashMap.Internal.AssocList.Const.toList_alter` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.AssocList.Const.toList_alter.h3.{v, u} :
    ∀ {α : Type u} {β : Type v} [inst : BEq α] {a : α} {f : Option β → Option β}
      {l : Std.DHashMap.Internal.AssocList α fun (x : α) => β},
      (Std.DHashMap.Internal.AssocList.Const.alter a f l).toList.Perm (Std.Internal.List.Const.alterKey a f l.toList) :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.AssocList.Const.toList_alter 3)

-- `Std.DHashMap.Internal.AssocList.Const.modify_eq_alter` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.AssocList.Const.modify_eq_alter.h3.{v, u} :
    ∀ {α : Type u} {β : Type v} [inst : BEq α] {a : α} {f : β → β} {l : Std.DHashMap.Internal.AssocList α fun (x : α) => β},
      Std.DHashMap.Internal.AssocList.Const.modify a f l =
        Std.DHashMap.Internal.AssocList.Const.alter a (fun (x : Option β) => Option.map f x) l :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.AssocList.Const.modify_eq_alter 3)

-- `Std.Internal.List.keys_insertEntryIfNew_perm` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.keys_insertEntryIfNew_perm.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] (k : α) (v : β k) {l : List ((a : α) × β a)},
      (Std.Internal.List.keys (Std.Internal.List.insertEntryIfNew k v l)).Perm
        (if Std.Internal.List.containsKey k l = Bool.true then Std.Internal.List.keys l else k :: Std.Internal.List.keys l) :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.keys_insertEntryIfNew_perm 3)

-- `Std.HashSet.Raw.forM_eq_forM` idx 4: unused in the library's proof
theorem HypCheckProof.Std.HashSet.Raw.forM_eq_forM.h4.{u, v, w} :
    ∀ {α : Type u} {m : Std.HashSet.Raw α} {m' : Type v → Type w} [inst : Monad m'] {f : α → m' PUnit},
      Std.HashSet.Raw.forM f m = ForM.forM m f :=
  no_implicit_lambda% (drop_unused% Std.HashSet.Raw.forM_eq_forM 4)

-- `Std.ExtDTreeMap.isEmpty_iff` idx 4: unused in the library's proof
theorem HypCheckProof.Std.ExtDTreeMap.isEmpty_iff.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp}, t.isEmpty = Bool.true ↔ t = ∅ :=
  no_implicit_lambda% (drop_unused% Std.ExtDTreeMap.isEmpty_iff 4)

-- `Std.DHashMap.Internal.Raw₀.Const.wf_insertManyIfNewUnit₀` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.wf_insertManyIfNewUnit₀.h3.{u, w} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulHashable α] {ρ : Type w} [inst_3 : ForIn Id ρ α]
      {m : Std.DHashMap.Raw α fun (x : α) => Unit} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.Const.insertManyIfNewUnit
                (⟨m, h⟩ : { m : Std.DHashMap.Raw α fun (x : α) => Unit // 0 < m.buckets.size }) l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.Const.wf_insertManyIfNewUnit₀ 3)

-- `Std.DHashMap.Internal.Raw₀.Const.wf_insertManyIfNewUnit₀` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.wf_insertManyIfNewUnit₀.h4.{u, w} :
    ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] {ρ : Type w} [inst_3 : ForIn Id ρ α]
      {m : Std.DHashMap.Raw α fun (x : α) => Unit} {h : 0 < m.buckets.size} {l : ρ},
      m.WF →
        (Std.DHashMap.Internal.Raw₀.Const.insertManyIfNewUnit
                (⟨m, h⟩ : { m : Std.DHashMap.Raw α fun (x : α) => Unit // 0 < m.buckets.size }) l).val.val.WF :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Internal.Raw₀.Const.wf_insertManyIfNewUnit₀ 4)

-- `Std.IterM.forIn_empty` idx 5: unused in the library's proof
theorem HypCheckProof.Std.IterM.forIn_empty.h5.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {n : Type u_1 → Type u_3} {β γ : Type u_1} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : LawfulMonad n] [inst_3 : MonadLiftT m n] [inst_4 : LawfulMonadLiftT m n] {init : γ}
      {f : β → γ → n (ForInStep γ)}, ForIn.forIn (Std.IterM.empty m β) init f = Pure.pure init :=
  no_implicit_lambda% (drop_unused% Std.IterM.forIn_empty 5)

-- `Std.WP.Triple.map` idx 12: unused in the library's proof
theorem HypCheckProof.Std.WP.Triple.map.h12.{u, v, w, w'} :
    ∀ {Pred : Type w} {EPosts : Type w'} {m : Type v → Type u} [inst : Monad m] [inst_1 : Std.WP.Assertion Pred]
      [inst_2 : Std.WP.Assertion EPosts] [inst_3 : @Std.WP.WPMonad m Pred EPosts inst inst_1 inst_2] {α β : Type v}
      {pre : Pred} {post : β → Pred} {eposts : EPosts} (f : α → β) (x : m α),
      @Std.WP.Triple Pred EPosts (m α) α inst_1 inst_2 x (@Std.WP.instWPOfWPMonad m Pred EPosts α inst inst_1 inst_2 inst_3)
          pre (fun (a : α) => post (f a)) eposts →
        @Std.WP.Triple Pred EPosts (m β) β inst_1 inst_2
          (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) α β f x)
          (@Std.WP.instWPOfWPMonad m Pred EPosts β inst inst_1 inst_2 inst_3) pre post eposts :=
  no_implicit_lambda% (drop_unused% Std.WP.Triple.map 12)

-- `Std.TreeMap.Equiv.modify` idx 6: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.Equiv.modify.h6.{u, v} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
      t₁.Equiv t₂ → ∀ (k : α) (f : β → β), (t₁.modify k f).Equiv (t₂.modify k f) :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.Equiv.modify 6)

-- `Std.TreeMap.Equiv.alter` idx 6: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.Equiv.alter.h6.{u, v} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
      t₁.Equiv t₂ → ∀ (k : α) (f : Option β → Option β), (t₁.alter k f).Equiv (t₂.alter k f) :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.Equiv.alter 6)

-- `Std.Do.ExceptT.ensures_of_wp_run` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Do.ExceptT.ensures_of_wp_run.h2.{u, u_1} :
    ∀ {m : Type u → Type u_1} [inst : Monad m] [inst_1 : Std.Do.WP m Std.Do.PostShape.pure]
      [inst_2 : @Std.Do.WPSound m Std.Do.PostShape.pure inst inst_1] {ε α : Type u} {prog : ExceptT ε m α}
      (P : Except ε α → Prop),
      @Std.Do.SPred.entails (Std.Do.PostShape.except ε Std.Do.PostShape.pure).args
          (@Std.Do.SPred.pure (Std.Do.PostShape.except ε Std.Do.PostShape.pure).args True)
          (@Std.Do.PredTrans.apply (Std.Do.PostShape.except ε Std.Do.PostShape.pure) α
            (@Std.Do.WP.wp (ExceptT ε m) (Std.Do.PostShape.except ε Std.Do.PostShape.pure)
              (@Std.Do.ExceptT.instWP m Std.Do.PostShape.pure ε inst_1) α prog)
            (@Prod.mk (α → Std.Do.Assertion (Std.Do.PostShape.except ε Std.Do.PostShape.pure))
              (Std.Do.ExceptConds (Std.Do.PostShape.except ε Std.Do.PostShape.pure))
              (fun (a : α) =>
                @Std.Do.SPred.pure (Std.Do.PostShape.except ε Std.Do.PostShape.pure).args (P (@Except.ok ε α a)))
              (@Prod.mk (ε → Std.Do.Assertion Std.Do.PostShape.pure) (Std.Do.ExceptConds Std.Do.PostShape.pure)
                (fun (e : ε) => @Std.Do.SPred.pure Std.Do.PostShape.pure.args (P (@Except.error ε α e))) PUnit.unit))) →
        @Std.Do.Internal.Ensures m (@Monad.toBind m inst) (Except ε α) P (@ExceptT.run ε m α prog) :=
  no_implicit_lambda% (drop_unused% Std.Do.ExceptT.ensures_of_wp_run 2)

-- `Std.Rio.toList_iter_eq_toList` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rio.toList_iter_eq_toList.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : DecidableLT α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rio α}, r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Rio.toList_iter_eq_toList 5)

-- `Std.Rio.toArray_iter` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rio.toArray_iter.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : DecidableLT α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rio α}, r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Rio.toArray_iter 5)

-- `Std.Rio.toList_iter` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rio.toList_iter.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : DecidableLT α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rio α}, r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Rio.toList_iter 5)

-- `Std.Rio.toArray_iter_eq_toArray` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rio.toArray_iter_eq_toArray.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : DecidableLT α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rio α}, r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Rio.toArray_iter_eq_toArray 5)

-- `Std.Rcc.toList_iter` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Rcc.toList_iter.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rcc α},
      r.iter.toList = r.toList :=
  no_implicit_lambda% (drop_unused% Std.Rcc.toList_iter 4)

-- `Std.Rcc.toArray_iter` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Rcc.toArray_iter.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rcc α},
      r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Rcc.toArray_iter 4)

-- `Std.Roo.toArray_iter` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Roo.toArray_iter.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Roo α},
      r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Roo.toArray_iter 4)

-- `Std.Rco.toArray_iter` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Rco.toArray_iter.h4.{u_1} :
    ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.IsAlwaysFinite α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {r : Std.Rco α},
      r.iter.toArray = r.toArray :=
  no_implicit_lambda% (drop_unused% Std.Rco.toArray_iter 4)

-- `Std.Internal.List.Const.isSome_minKey?_modifyKey` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.Const.isSome_minKey?_modifyKey.h3.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {f : β → β}
      {l : List ((_ : α) × β)}, (Std.Internal.List.minKey? (Std.Internal.List.Const.modifyKey k f l)).isSome = !l.isEmpty :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.Const.isSome_minKey?_modifyKey 3)

-- `Std.Internal.List.Const.isSome_minKey?_modifyKey` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.Const.isSome_minKey?_modifyKey.h5.{u, v} :
    ∀ {α : Type u} {β : Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {f : β → β}
      {l : List ((_ : α) × β)}, (Std.Internal.List.minKey? (Std.Internal.List.Const.modifyKey k f l)).isSome = !l.isEmpty :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.Const.isSome_minKey?_modifyKey 5)

-- `Std.Iterators.HetT.prun_congr` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iterators.HetT.prun_congr.h4.{w, w', u} :
    ∀ {m : Type w → Type w'} {α : Type u} {β : Type w} [inst : Monad m] {x y : Std.Iterators.HetT m α}
      {f : (a : α) → x.Property a → m β} (h : x = y),
      x.prun f = y.prun fun (a : α) (ha : y.Property a) => f a (Eq.symm h ▸ ha) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.HetT.prun_congr 4)

-- `Std.DHashMap.Raw.equiv_iff_toList_perm` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.equiv_iff_toList_perm.h6.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] {m₁ m₂ : Std.DHashMap.Raw α β}
      [inst : LawfulHashable α], m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.equiv_iff_toList_perm 6)

-- `Std.DHashMap.Raw.equiv_iff_toList_perm` idx 7: unused in the library's proof
theorem HypCheckProof.Std.DHashMap.Raw.equiv_iff_toList_perm.h7.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] {m₁ m₂ : Std.DHashMap.Raw α β} [inst : EquivBEq α],
      m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList :=
  no_implicit_lambda% (drop_unused% Std.DHashMap.Raw.equiv_iff_toList_perm 7)

-- `Std.DTreeMap.Internal.Impl.containsThenInsert_snd` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.containsThenInsert_snd.h4.{u, v} :
    ∀ {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Std.DTreeMap.Internal.Impl α β} (h : t.WF) {k : α} {v : β k},
      (Std.DTreeMap.Internal.Impl.containsThenInsert k v t (Std.DTreeMap.Internal.Impl.WF.balanced h)).snd.impl =
        (Std.DTreeMap.Internal.Impl.insert k v t (Std.DTreeMap.Internal.Impl.WF.balanced h)).impl :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.containsThenInsert_snd 4)

-- `Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew?_fst` idx 4: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew?_fst.h4.{u, v} :
    ∀ {α : Type u} {instOrd : Ord α} {β : Type v} {t : Std.DTreeMap.Internal.Impl α fun (x : α) => β} (h : t.WF) {k : α}
      {v : β},
      (Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew? t k v (Std.DTreeMap.Internal.Impl.WF.balanced h)).fst =
        Std.DTreeMap.Internal.Impl.Const.get? t k :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew?_fst 4)

-- `Std.Internal.List.containsKey_of_perm` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.containsKey_of_perm.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l l' : List ((a : α) × β a)} {k : α},
      l.Perm l' → Std.Internal.List.containsKey k l = Std.Internal.List.containsKey k l' :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.containsKey_of_perm 3)

-- `Std.Internal.List.getKey?_eq_none` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.getKey?_eq_none.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l : List ((a : α) × β a)} {a : α},
      Std.Internal.List.containsKey a l = Bool.false → Std.Internal.List.getKey? a l = Option.none :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.getKey?_eq_none 3)

-- `Std.Internal.List.fst_mem_keys_of_mem` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.fst_mem_keys_of_mem.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {a : (a : α) × β a} {l : List ((a : α) × β a)},
      a ∈ l → a.fst ∈ Std.Internal.List.keys l :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.fst_mem_keys_of_mem 3)

-- `Std.Internal.List.forIn_eq_forIn_keys` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.forIn_eq_forIn_keys.h5.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {δ : Type w} {m' : Type w → Type w'} [inst : Monad m'] {f : α → δ → m' (ForInStep δ)}
      {init : δ} {l : List ((a : α) × β a)},
      (ForIn.forIn l init fun (a : (a : α) × β a) (d : δ) => f a.fst d) = ForIn.forIn (Std.Internal.List.keys l) init f :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.forIn_eq_forIn_keys 5)

-- `Std.TreeMap.forM_eq_forM` idx 6: unused in the library's proof
theorem HypCheckProof.Std.TreeMap.forM_eq_forM.h6.{u, v, w, w'} :
    ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {m : Type w → Type w'} [inst : Monad m]
      {f : α → β → m PUnit}, Std.TreeMap.forM f t = ForM.forM t fun (a : α × β) => f a.fst a.snd :=
  no_implicit_lambda% (drop_unused% Std.TreeMap.forM_eq_forM 6)

-- `Std.Internal.List.getEntry?_insertEntryIfNew` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.getEntry?_insertEntryIfNew.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k},
      Std.Internal.List.getEntry? a (Std.Internal.List.insertEntryIfNew k v l) =
        if (k == a && !Std.Internal.List.containsKey k l) = Bool.true then Option.some (⟨k, v⟩ : (a : α) × β a)
        else Std.Internal.List.getEntry? a l :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.getEntry?_insertEntryIfNew 3)

-- `Std.Sat.AIG.denote_mkGate_cached` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Sat.AIG.denote_mkGate_cached.h7 :
    ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {assign : α → Bool} {aig : @Std.Sat.AIG α inst_1 inst}
      {input : @Std.Sat.AIG.BinaryInput α inst inst_1 aig}
      {hit :
        @Std.Sat.AIG.CacheHit α (@Std.Sat.AIG.decls α inst_1 inst aig)
          (@Std.Sat.AIG.Decl.gate α
            (Std.Sat.AIG.Fanin.mk
              (@Std.Sat.AIG.Ref.gate α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig input))
              (@Std.Sat.AIG.Ref.invert α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig input)))
            (Std.Sat.AIG.Fanin.mk
              (@Std.Sat.AIG.Ref.gate α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig input))
              (@Std.Sat.AIG.Ref.invert α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig input))))},
      @Eq Bool
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig
            (@Std.Sat.AIG.Ref.mk α inst inst_1 aig
              (@Std.Sat.AIG.CacheHit.idx α (@Std.Sat.AIG.decls α inst_1 inst aig)
                (@Std.Sat.AIG.Decl.gate α
                  (Std.Sat.AIG.Fanin.mk
                    (@Std.Sat.AIG.Ref.gate α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig input))
                    (@Std.Sat.AIG.Ref.invert α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig input)))
                  (Std.Sat.AIG.Fanin.mk
                    (@Std.Sat.AIG.Ref.gate α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig input))
                    (@Std.Sat.AIG.Ref.invert α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig input))))
                hit)
              Bool.false
              (@Std.Sat.AIG.CacheHit.hbound α (@Std.Sat.AIG.decls α inst_1 inst aig)
                (@Std.Sat.AIG.Decl.gate α
                  (Std.Sat.AIG.Fanin.mk
                    (@Std.Sat.AIG.Ref.gate α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig input))
                    (@Std.Sat.AIG.Ref.invert α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig input)))
                  (Std.Sat.AIG.Fanin.mk
                    (@Std.Sat.AIG.Ref.gate α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig input))
                    (@Std.Sat.AIG.Ref.invert α inst inst_1 aig (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig input))))
                hit))))
        ((@Std.Sat.AIG.denote α inst inst_1 assign
              (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig input))).and
          (@Std.Sat.AIG.denote α inst inst_1 assign
            (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig input)))) :=
  no_implicit_lambda% (drop_unused% Std.Sat.AIG.denote_mkGate_cached 7)

-- `Std.DTreeMap.Raw.forM_eq_forM` idx 6: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Raw.forM_eq_forM.h6.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} {m : Type w → Type w'}
      [inst : Monad m] {f : (a : α) → β a → m PUnit},
      Std.DTreeMap.Raw.forM f t = ForM.forM t fun (a : (a : α) × β a) => f a.fst a.snd :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Raw.forM_eq_forM 6)

-- `Std.Internal.List.getKey?_insertEntryIfNew` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.getKey?_insertEntryIfNew.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k},
      Std.Internal.List.getKey? a (Std.Internal.List.insertEntryIfNew k v l) =
        if (k == a) = Bool.true ∧ Std.Internal.List.containsKey k l = Bool.false then Option.some k
        else Std.Internal.List.getKey? a l :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.getKey?_insertEntryIfNew 3)

-- `Std.DTreeMap.Internal.Impl.containsThenInsertIfNew!_fst_eq_containsₘ` idx 3: unused in the library's proof
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.containsThenInsertIfNew!_fst_eq_containsₘ.h3.{u, v} :
    ∀ {α : Type u} {β : α → Type v} [inst : Ord α] (t : Std.DTreeMap.Internal.Impl α β) (a : α) (b : β a),
      (Std.DTreeMap.Internal.Impl.containsThenInsertIfNew! a b t).fst = t.containsₘ a :=
  no_implicit_lambda% (drop_unused% Std.DTreeMap.Internal.Impl.containsThenInsertIfNew!_fst_eq_containsₘ 3)

-- `Std.Iterators.HetT.property_pmap` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iterators.HetT.property_pmap.h4.{w, w', u, v} :
    ∀ {m : Type w → Type w'} {α : Type u} {β : Type v} [inst : Monad m] {x : Std.Iterators.HetT m α}
      {f : (a : α) → x.Property a → β}, (x.pmap f).Property = fun (b : β) => ∃ (a : α), ∃ (h : x.Property a), f a h = b :=
  no_implicit_lambda% (drop_unused% Std.Iterators.HetT.property_pmap 4)

-- `Std.Internal.List.forM_eq_forM_keys` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.forM_eq_forM_keys.h4.{u, v, w, w'} :
    ∀ {α : Type u} {β : α → Type v} {m' : Type w → Type w'} [inst : Monad m'] {l : List ((a : α) × β a)} {f : α → m' PUnit},
      (l.forM fun (a : (a : α) × β a) => f a.fst) = (Std.Internal.List.keys l).forM f :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.forM_eq_forM_keys 4)

-- `Std.Internal.List.length_le_length_insertListIfNewUnit` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Internal.List.length_le_length_insertListIfNewUnit.h2.{u} :
    ∀ {α : Type u} [inst : BEq α] {l : List ((_ : α) × Unit)} {toInsert : List α},
      l.length ≤ (Std.Internal.List.insertListIfNewUnit l toInsert).length :=
  no_implicit_lambda% (drop_unused% Std.Internal.List.length_le_length_insertListIfNewUnit 2)

-- `Std.Iterators.HetT.property_pure` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Iterators.HetT.property_pure.h3.{w, w', u} :
    ∀ {m : Type w → Type w'} {α : Type u} [inst : Monad m] {x : α},
      @Eq (α → Prop)
        (@Std.Iterators.HetT.Property m α
          (@Std.Iterators.HetT.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) α x))
        fun (x_1 : α) => @Eq α x x_1 :=
  no_implicit_lambda% (drop_unused% Std.Iterators.HetT.property_pure 3)

