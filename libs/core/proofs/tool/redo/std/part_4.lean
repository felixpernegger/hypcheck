import Std

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Std.ExtDHashMap.get_insertMany_list_of_mem, hypothesis 13: removable
/- FAILED: 16:50: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 53:12: Application type mismatch: The argument
  α
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {x} {β} [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDHashMap.get_insertMany_list_of_mem.h13.der.{u, v} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} {m : Std.ExtDHashMap α β} [inst : LawfulBEq α]
      {l : List ((a : α) × β a)} {k k' : α},
      (k == k') = Bool.true →
        ∀ {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ m.insertMany l := by
  (intros; grind)
theorem HypCheckProof.Std.ExtDHashMap.get_insertMany_list_of_mem.h13.{u, v} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} {m : Std.ExtDHashMap α β} [inst : LawfulBEq α]
      {l : List ((a : α) × β a)} {k k' : α} (k_beq : (k == k') = Bool.true) {v : β k}
      (distinct : List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l)
      (mem : (⟨k, v⟩ : (a : α) × β a) ∈ l),
      (m.insertMany l).get k' (HypCheckProof.Std.ExtDHashMap.get_insertMany_list_of_mem.h13.der k_beq distinct mem) =
        cast
          ((fun {α : Type u} {x : BEq α} {β : α → Type v} [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
              (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
            k_beq)
          v := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.ExtDHashMap.get_insertMany_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 (@HypCheckProof.Std.ExtDHashMap.get_insertMany_list_of_mem.h13.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12)
-/

-- Std.DHashMap.Raw.get_ofList_of_mem, hypothesis 12: removable
/- FAILED: 16:50: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 37:12: Application type mismatch: The argument
  α
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.Raw.get_ofList_of_mem.h12.der.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulBEq α] {l : List ((a : α) × β a)}
      {k k' : α},
      (k == k') = Bool.true →
        ∀ {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ Std.DHashMap.Raw.ofList l := by
  (intros; grind)
theorem HypCheckProof.Std.DHashMap.Raw.get_ofList_of_mem.h12.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulBEq α] {l : List ((a : α) × β a)}
      {k k' : α} (k_beq : (k == k') = Bool.true) {v : β k}
      (distinct : List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l)
      (mem : (⟨k, v⟩ : (a : α) × β a) ∈ l),
      (Std.DHashMap.Raw.ofList l).get k' (HypCheckProof.Std.DHashMap.Raw.get_ofList_of_mem.h12.der k_beq distinct mem) =
        cast
          ((fun {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
              (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
            k_beq)
          v := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Std.DHashMap.Raw.get_ofList_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 (@HypCheckProof.Std.DHashMap.Raw.get_ofList_of_mem.h12.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11)
-/

-- Std.HashMap.Raw.getKey!_unitOfList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getKey!_unitOfList_of_mem.h11.inst : ¬(Std.HashMap.Raw.unitOfList []).getKey! 1 = 1 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getKey!_unitOfList_of_mem.h11.prem0 : (1 == 1) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getKey!_unitOfList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.HashMap.Raw.getKey!_unitOfList_of_mem.h11 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α]
        [inst_4 : Inhabited α] {l : List α} {k k' : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l → (Std.HashMap.Raw.unitOfList l).getKey! k' = k := fun hc_h => HypCheckProof.Std.HashMap.Raw.getKey!_unitOfList_of_mem.h11.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ (instInhabitedNat) ([]) (1) (1) HypCheckProof.Std.HashMap.Raw.getKey!_unitOfList_of_mem.h11.prem0 HypCheckProof.Std.HashMap.Raw.getKey!_unitOfList_of_mem.h11.prem1)

-- Std.HashSet.Raw.getD_ofList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashSet.Raw.getD_ofList_of_mem.h11.inst : ¬(Std.HashSet.Raw.ofList []).getD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashSet.Raw.getD_ofList_of_mem.h11.prem0 : (0 == 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashSet.Raw.getD_ofList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.HashSet.Raw.getD_ofList_of_mem.h11 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α] {l : List α}
        {k k' fallback : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l → (Std.HashSet.Raw.ofList l).getD k' fallback = k := fun hc_h => HypCheckProof.Std.HashSet.Raw.getD_ofList_of_mem.h11.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ ([]) (0) (0) (1) HypCheckProof.Std.HashSet.Raw.getD_ofList_of_mem.h11.prem0 HypCheckProof.Std.HashSet.Raw.getD_ofList_of_mem.h11.prem1)

-- Std.Internal.List.minKeyD_insertEntry_of_isEmpty, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntry_of_isEmpty.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      ¬Std.Internal.List.DistinctKeys l →
        l.isEmpty = Bool.true →
          ∀ {fallback : α}, Std.Internal.List.minKeyD (Std.Internal.List.insertEntry k v l) fallback = k := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntry_of_isEmpty.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → ∀ {fallback : α}, Std.Internal.List.minKeyD (Std.Internal.List.insertEntry k v l) fallback = k := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @Std.Internal.List.minKeyD_insertEntry_of_isEmpty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.Std.Internal.List.minKeyD_insertEntry_of_isEmpty.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10 hc_x11)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntry_of_isEmpty.h9.derivable.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → ∀ {fallback : α}, Std.Internal.List.DistinctKeys l := by
  (intros; simp_all; done)

-- Std.TreeSet.Raw.head?_toList, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.Raw.head?_toList.h6.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α],
      ¬Std.LawfulOrderCmp cmp →
        ∀ [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
          t.WF → t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.Raw.head?_toList.h6.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
      t.WF → t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x7 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.TreeSet.Raw.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h hc_x7 hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.TreeSet.Raw.head?_toList.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn hc_x7 hc_x8 hc_x9 hc_x10)

-- Std.TreeSet.Raw.head?_toList, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.Raw.head?_toList.h7.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp],
      ¬Std.LawfulOrderMin α →
        ∀ [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp], t.WF → t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.Raw.head?_toList.h7.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderLeftLeaningMin α]
      [inst : Std.LawfulEqCmp cmp], t.WF → t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.TreeSet.Raw.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.TreeSet.Raw.head?_toList.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9 hc_x10)

-- Std.TreeSet.Raw.head?_toList, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.Raw.head?_toList.h8.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α],
      ¬Std.LawfulOrderLeftLeaningMin α → ∀ [inst : Std.LawfulEqCmp cmp], t.WF → t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.Raw.head?_toList.h8.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderMin α] [inst : Std.LawfulEqCmp cmp],
      t.WF → t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.TreeSet.Raw.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.TreeSet.Raw.head?_toList.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9 hc_x10)

-- Std.TreeSet.Raw.head?_toList, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.Raw.head?_toList.h9.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], ¬Std.LawfulEqCmp cmp → t.WF → t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.Raw.head?_toList.h9.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], t.WF → t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @Std.TreeSet.Raw.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.Std.TreeSet.Raw.head?_toList.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)

-- Std.HashSet.Raw.get_insertMany_list_of_mem, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.HashSet.Raw.get_insertMany_list_of_mem.h10.der.{u} : ∀ {α : Type u} {m : Std.HashSet.Raw α} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α]
      [inst_3 : LawfulHashable α], m.WF → ∀ {l : List α} {k : α}, k ∈ m → k ∈ m.insertMany l := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.HashSet.Raw.get_insertMany_list_of_mem.h10.{u} : ∀ {α : Type u} {m : Std.HashSet.Raw α} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α]
      [inst_3 : LawfulHashable α] (h : m.WF) {l : List α} {k : α} (mem : k ∈ m),
      (m.insertMany l).get k (HypCheckProof.Std.HashSet.Raw.get_insertMany_list_of_mem.h10.der h mem) = m.get k mem := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact @Std.HashSet.Raw.get_insertMany_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 (@HypCheckProof.Std.HashSet.Raw.get_insertMany_list_of_mem.h10.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9)

-- Std.ExtTreeMap.head?_keys, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeMap.head?_keys.h7.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α],
      ¬Std.LawfulOrderCmp cmp →
        ∀ [inst_3 : Std.LawfulOrderMin α] [inst_4 : Std.LawfulOrderLeftLeaningMin α] [inst_5 : Std.LawfulEqCmp cmp],
          t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeMap.head?_keys.h7.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderMin α] [inst_4 : Std.LawfulOrderLeftLeaningMin α]
      [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.ExtTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.ExtTreeMap.head?_keys.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9 hc_x10)

-- Std.ExtTreeMap.head?_keys, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeMap.head?_keys.h8.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp],
      ¬Std.LawfulOrderMin α →
        ∀ [inst_4 : Std.LawfulOrderLeftLeaningMin α] [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeMap.head?_keys.h8.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderLeftLeaningMin α]
      [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.ExtTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.ExtTreeMap.head?_keys.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9 hc_x10)

-- Std.ExtTreeMap.head?_keys, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeMap.head?_keys.h9.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α],
      ¬Std.LawfulOrderLeftLeaningMin α → ∀ [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeMap.head?_keys.h9.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α]
      [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @Std.ExtTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.Std.ExtTreeMap.head?_keys.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)

-- Std.ExtTreeMap.head?_keys, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeMap.head?_keys.h10.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α]
      [inst_5 : Std.LawfulOrderLeftLeaningMin α], ¬Std.LawfulEqCmp cmp → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeMap.head?_keys.h10.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α]
      [inst_5 : Std.LawfulOrderLeftLeaningMin α], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.ExtTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h) (fun hc_hn => @HypCheckProof.Std.ExtTreeMap.head?_keys.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn)

-- Std.DTreeMap.head?_keys, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.head?_keys.h7.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α],
      ¬Std.LawfulOrderCmp cmp →
        ∀ [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
          t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.head?_keys.h7.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α]
      [inst : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.DTreeMap.head?_keys.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9 hc_x10)

-- Std.DTreeMap.head?_keys, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.head?_keys.h8.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp],
      ¬Std.LawfulOrderMin α →
        ∀ [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.head?_keys.h8.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderLeftLeaningMin α]
      [inst : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.DTreeMap.head?_keys.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9 hc_x10)

-- Std.DTreeMap.head?_keys, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.head?_keys.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α],
      ¬Std.LawfulOrderLeftLeaningMin α → ∀ [inst : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.head?_keys.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderMin α]
      [inst : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.Std.DTreeMap.head?_keys.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)

-- Std.DTreeMap.head?_keys, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.head?_keys.h10.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], ¬Std.LawfulEqCmp cmp → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.head?_keys.h10.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h) (fun hc_hn => @HypCheckProof.Std.DTreeMap.head?_keys.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn)

-- Std.DHashMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_mem, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.der.{u} : ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {m : Std.DHashMap.Raw α fun (x : α) => Unit} [inst_2 : EquivBEq α]
      [inst_3 : LawfulHashable α], m.WF → ∀ {l : List α} {k : α}, k ∈ m → k ∈ Std.DHashMap.Raw.Const.insertManyIfNewUnit m l := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.{u} : ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {m : Std.DHashMap.Raw α fun (x : α) => Unit} [inst_2 : EquivBEq α]
      [inst_3 : LawfulHashable α] (h : m.WF) {l : List α} {k : α} (mem : k ∈ m),
      (Std.DHashMap.Raw.Const.insertManyIfNewUnit m l).getKey k
          (HypCheckProof.Std.DHashMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.der h mem) =
        m.getKey k mem := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact @Std.DHashMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.DHashMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9) hc_x9

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get, hypothesis 8: removable
/- FAILED: 20:96: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.122 = true) = true
in the application
  id (Eq.refl true) | 6:104: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get.h8.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (curr : Nat) (s : aig.RefVec curr) (idx : Nat), idx < w → curr ≤ idx → curr ≤ w := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get.h8 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (curr : Nat) (s : aig.RefVec curr) (idx : Nat) (hidx1 : idx < w) (a : curr ≤ idx),
      (Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go input distance curr
              (HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get.h8.der aig distance input curr s idx
                hidx1 a)
              s).get
          idx hidx1 =
        if hidx3 : idx < distance % w then
          input.get (w - distance % w + idx)
            ((fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) (hidx3 : idx < distance % w) =>
                Decidable.byContradiction fun (a : ¬w - distance % w + idx < w) =>
                  (fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) (hidx3 : idx < distance % w)
                        (a : ¬w - distance % w + idx < w) =>
                      Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                        (fun (h₁ : distance % w ≤ w ∧ ↑(w - distance % w) = ↑w - ↑(distance % w)) =>
                          Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                            (Lean.Omega.tidy_sat
                              (Lean.Omega.combo_sat'
                                { lowerBound := Option.some 0, upperBound := Option.none : Lean.Omega.Constraint }
                                { lowerBound := Option.none, upperBound := Option.some (-1) : Lean.Omega.Constraint } 1
                                [0, 0, 1, -1, 0] (-1) [0, 0, 1, -1]
                                (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.combo_sat'
                                    { lowerBound := Option.some 0, upperBound := Option.some 0 : Lean.Omega.Constraint }
                                    { lowerBound := Option.none, upperBound := Option.some 0 : Lean.Omega.Constraint } (-1)
                                    [1, 0, 0, -1, -1] 1 [1, 0, -1, 0, -1]
                                    (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])
                                    (Lean.Omega.tidy_sat
                                      (Lean.Omega.Constraint.addEquality_sat
                                        (Eq.trans
                                          (Eq.symm
                                            (Eq.trans
                                              (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)
                                                (Eq.trans
                                                  (Lean.Omega.Int.sub_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                                    (Eq.trans (Int.natCast_emod distance w)
                                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.sub_eval
                                                      { coeffs := [1] : Lean.Omega.LinearCombo }
                                                      { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList
                                                        [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])))))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.sub_eval
                                                  { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                  { coeffs := [1, 0, 0, -1] : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList
                                                    [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])))))
                                          (Int.sub_eq_zero_of_eq h₁.right))))
                                    (Lean.Omega.tidy_sat
                                      (Lean.Omega.Constraint.addInequality_sat
                                        (le_of_le_of_eq
                                          (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt a)))
                                          (Eq.trans
                                            (Lean.Omega.Int.sub_congr
                                              (Eq.trans (Int.natCast_add (w - distance % w) idx)
                                                (Eq.trans
                                                  (Lean.Omega.Int.add_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.add_eval
                                                      { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                      { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList
                                                        [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])))))
                                              (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.sub_eval
                                                { coeffs := [0, 0, 1, 0, 1] : Lean.Omega.LinearCombo }
                                                { coeffs := [1] : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList
                                                  [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])))))))))
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq
                                      (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt hidx3)))
                                      (Eq.trans
                                        (Lean.Omega.Int.sub_congr
                                          (Eq.trans (Int.natCast_emod distance w)
                                            (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3))
                                          (Eq.trans
                                            (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                              (id (Eq.refl 1)))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.add_eval
                                                { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                { const := 1 : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList
                                                  [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])))))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.sub_eval
                                            { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                            { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList
                                              [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)]))))))))))
                        fun (h₂ : w < distance % w ∧ ↑(w - distance % w) = 0) =>
                        Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                          (Lean.Omega.tidy_sat
                            (Lean.Omega.combo_sat'
                              { lowerBound := Option.none, upperBound := Option.some 0 : Lean.Omega.Constraint }
                              { lowerBound := Option.some 1, upperBound := Option.none : Lean.Omega.Constraint } (-1)
                              [1, 0, -1, 0, 0] 1 [1, 0, -1]
                              (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])
                              (Lean.Omega.combo_sat'
                                { lowerBound := Option.some 0, upperBound := Option.some 0 : Lean.Omega.Constraint }
                                { lowerBound := Option.none, upperBound := Option.some 0 : Lean.Omega.Constraint } 1
                                [0, 0, 0, 0, 1] 1 [1, 0, -1, 0, -1]
                                (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])
                                (Lean.Omega.Constraint.addEquality_sat
                                  (Eq.trans (Eq.symm (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)) h₂.right))
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq
                                      (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt a)))
                                      (Eq.trans
                                        (Lean.Omega.Int.sub_congr
                                          (Eq.trans (Int.natCast_add (w - distance % w) idx)
                                            (Eq.trans
                                              (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)
                                                (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.add_eval
                                                  { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                  { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList
                                                    [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])))))
                                          (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.sub_eval
                                            { coeffs := [0, 0, 1, 0, 1] : Lean.Omega.LinearCombo }
                                            { coeffs := [1] : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList
                                              [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)]))))))))
                              (Lean.Omega.Constraint.addInequality_sat
                                (le_of_le_of_eq
                                  (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt hidx1)))
                                  (Eq.trans
                                    (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                      (Eq.trans
                                        (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                          (id (Eq.refl 1)))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.add_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                            { const := 1 : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList
                                              [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])))))
                                    (Eq.symm
                                      (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                        { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList
                                          [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(w - distance % w)])))))))))
                    distance curr idx hidx1 hidx3 a)
              distance curr idx hidx1 hidx3)
        else
          input.get (idx - distance % w)
            ((fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) (hidx3 : ¬idx < distance % w) =>
                Decidable.byContradiction fun (a : ¬idx - distance % w < w) =>
                  (fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) (hidx3 : ¬idx < distance % w)
                        (a : ¬idx - distance % w < w) =>
                      Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                        (fun (h₁ : distance % w ≤ idx ∧ ↑(idx - distance % w) = ↑idx - ↑(distance % w)) =>
                          Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                            (Lean.Omega.Constraint.combine_sat'
                              (Lean.Omega.tidy_sat
                                (Lean.Omega.combo_sat'
                                  { lowerBound := Option.some 0, upperBound := Option.none : Lean.Omega.Constraint }
                                  { lowerBound := Option.some 1, upperBound := Option.none : Lean.Omega.Constraint } (-1)
                                  [0, 0, 0, 1] (-1) [1, 0, 0, -1, -1]
                                  (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)])
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq Lean.Omega.Int.emod_ofNat_nonneg
                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)))
                                  (Lean.Omega.combo_sat'
                                    { lowerBound := Option.some 0, upperBound := Option.some 0 : Lean.Omega.Constraint }
                                    { lowerBound := Option.some 1, upperBound := Option.none : Lean.Omega.Constraint } 1
                                    [0, 0, 1, -1, -1] 1 [1, 0, -1]
                                    (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)])
                                    (Lean.Omega.tidy_sat
                                      (Lean.Omega.Constraint.addEquality_sat
                                        (Eq.trans
                                          (Eq.symm
                                            (Eq.trans
                                              (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)
                                                (Eq.trans
                                                  (Lean.Omega.Int.sub_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                                    (Eq.trans (Int.natCast_emod distance w)
                                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.sub_eval
                                                      { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                      { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList
                                                        [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)])))))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.sub_eval
                                                  { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                  { coeffs := [0, 0, 1, -1] : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList
                                                    [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)])))))
                                          (Int.sub_eq_zero_of_eq h₁.right))))
                                    (Lean.Omega.Constraint.addInequality_sat
                                      (le_of_le_of_eq
                                        (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt hidx1)))
                                        (Eq.trans
                                          (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                            (Eq.trans
                                              (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                                (id (Eq.refl 1)))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.add_eval
                                                  { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                  { const := 1 : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList
                                                    [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)])))))
                                          (Eq.symm
                                            (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                              { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                              (Lean.Omega.Coeffs.ofList
                                                [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)])))))))))
                              (Lean.Omega.tidy_sat
                                (Lean.Omega.Constraint.addInequality_sat
                                  (le_of_le_of_eq
                                    (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt a)))
                                    (Eq.trans
                                      (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)
                                        (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0))
                                      (Eq.symm
                                        (Lean.Omega.LinearCombo.sub_eval
                                          { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                          { coeffs := [1] : Lean.Omega.LinearCombo }
                                          (Lean.Omega.Coeffs.ofList
                                            [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)])))))))))
                        fun (h₂ : idx < distance % w ∧ ↑(idx - distance % w) = 0) =>
                        Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                          (Lean.Omega.Constraint.combine_sat'
                            (Lean.Omega.tidy_sat
                              (Lean.Omega.Constraint.addInequality_sat
                                (le_of_le_of_eq
                                  (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂.left)))
                                  (Eq.trans
                                    (Lean.Omega.Int.sub_congr
                                      (Eq.trans (Int.natCast_emod distance w)
                                        (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3))
                                      (Eq.trans
                                        (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                          (id (Eq.refl 1)))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.add_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                            { const := 1 : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList
                                              [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)])))))
                                    (Eq.symm
                                      (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                        { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList
                                          [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)])))))))
                            (Lean.Omega.Constraint.addInequality_sat
                              (le_of_le_of_eq
                                (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt hidx3)))
                                (Eq.trans
                                  (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                    (Eq.trans (Int.natCast_emod distance w)
                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)))
                                  (Eq.symm
                                    (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                      { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                      (Lean.Omega.Coeffs.ofList
                                        [↑w, ↑curr, ↑idx, ↑distance % ↑w, ↑(idx - distance % w)]))))))))
                    distance curr idx hidx1 hidx3 a)
              distance curr idx hidx1 hidx3) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get.h8.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11) hc_x8 hc_x9 hc_x10 hc_x11
-/

