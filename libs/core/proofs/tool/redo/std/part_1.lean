import Std

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Std.DHashMap.get_insertMany_list_of_mem, hypothesis 13: removable
/- FAILED: 16:50: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 48:12: Application type mismatch: The argument
  α
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} {x} [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.get_insertMany_list_of_mem.h13.der.{u, v} : ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} {m : Std.DHashMap α β} [inst : LawfulBEq α]
      {l : List ((a : α) × β a)} {k k' : α},
      (k == k') = Bool.true →
        ∀ {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ m.insertMany l := by
  (intros; grind)
theorem HypCheckProof.Std.DHashMap.get_insertMany_list_of_mem.h13.{u, v} : ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} {m : Std.DHashMap α β} [inst : LawfulBEq α]
      {l : List ((a : α) × β a)} {k k' : α} (k_beq : (k == k') = Bool.true) {v : β k}
      (distinct : List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l)
      (mem : (⟨k, v⟩ : (a : α) × β a) ∈ l),
      (m.insertMany l).get k' (HypCheckProof.Std.DHashMap.get_insertMany_list_of_mem.h13.der k_beq distinct mem) =
        cast
          ((fun {α : Type u} {β : α → Type v} {x : BEq α} [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
              (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
            k_beq)
          v := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.DHashMap.get_insertMany_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 (@HypCheckProof.Std.DHashMap.get_insertMany_list_of_mem.h13.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12)
-/

-- Std.DHashMap.get_ofList_of_mem, hypothesis 12: removable
/- FAILED: 16:50: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 36:12: Application type mismatch: The argument
  α
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} {x} [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.get_ofList_of_mem.h12.der.{u, v} : ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} [inst : LawfulBEq α] {l : List ((a : α) × β a)}
      {k k' : α},
      (k == k') = Bool.true →
        ∀ {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ Std.DHashMap.ofList l := by
  (intros; grind)
theorem HypCheckProof.Std.DHashMap.get_ofList_of_mem.h12.{u, v} : ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} [inst : LawfulBEq α] {l : List ((a : α) × β a)}
      {k k' : α} (k_beq : (k == k') = Bool.true) {v : β k}
      (distinct : List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l)
      (mem : (⟨k, v⟩ : (a : α) × β a) ∈ l),
      (Std.DHashMap.ofList l).get k' (HypCheckProof.Std.DHashMap.get_ofList_of_mem.h12.der k_beq distinct mem) =
        cast
          ((fun {α : Type u} {β : α → Type v} {x : BEq α} [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
              (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
            k_beq)
          v := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Std.DHashMap.get_ofList_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 (@HypCheckProof.Std.DHashMap.get_ofList_of_mem.h12.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11)
-/

-- Std.DTreeMap.Raw.head?_keys, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.Raw.head?_keys.h7.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α],
      ¬Std.LawfulOrderCmp cmp →
        ∀ [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
          t.WF → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.Raw.head?_keys.h7.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α]
      [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.Raw.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9 hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.Std.DTreeMap.Raw.head?_keys.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9 hc_x10 hc_x11)

-- Std.DTreeMap.Raw.head?_keys, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.Raw.head?_keys.h8.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp],
      ¬Std.LawfulOrderMin α →
        ∀ [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.Raw.head?_keys.h8.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderLeftLeaningMin α]
      [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.Raw.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9 hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.Std.DTreeMap.Raw.head?_keys.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9 hc_x10 hc_x11)

-- Std.DTreeMap.Raw.head?_keys, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.Raw.head?_keys.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α],
      ¬Std.LawfulOrderLeftLeaningMin α → ∀ [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.Raw.head?_keys.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderMin α]
      [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.Raw.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.Std.DTreeMap.Raw.head?_keys.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10 hc_x11)

-- Std.DTreeMap.Raw.head?_keys, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.Raw.head?_keys.h10.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], ¬Std.LawfulEqCmp cmp → t.WF → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.Raw.head?_keys.h10.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], t.WF → t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x11
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.Raw.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h hc_x11) (fun hc_hn => @HypCheckProof.Std.DTreeMap.Raw.head?_keys.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn hc_x11)

-- Std.DHashMap.Raw.Const.getKeyD_unitOfList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKeyD_unitOfList_of_mem.h11.inst : ¬(Std.DHashMap.Raw.Const.unitOfList []).getKeyD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKeyD_unitOfList_of_mem.h11.prem0 : (0 == 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKeyD_unitOfList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKeyD_unitOfList_of_mem.h11 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α] {l : List α}
        {k k' fallback : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l →
            (Std.DHashMap.Raw.Const.unitOfList l).getKeyD k' fallback = k := fun hc_h => HypCheckProof.Std.DHashMap.Raw.Const.getKeyD_unitOfList_of_mem.h11.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ ([]) (0) (0) (1) HypCheckProof.Std.DHashMap.Raw.Const.getKeyD_unitOfList_of_mem.h11.prem0 HypCheckProof.Std.DHashMap.Raw.Const.getKeyD_unitOfList_of_mem.h11.prem1)

-- Std.Sat.AIG.RefVec.ite.denote_go, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.RefVec.ite.denote_go.h7.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {assign : α → Bool} {w : Nat}
      (aig : @Std.Sat.AIG α inst_1 inst) (curr : Nat) (discr : @Std.Sat.AIG.Ref α inst inst_1 aig)
      (lhs rhs : @Std.Sat.AIG.RefVec α inst inst_1 aig w) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr) (idx : Nat),
      @LT.lt Nat instLTNat idx w → @LE.le Nat instLENat curr idx → @LE.le Nat instLENat curr w := by
  (intros; omega)
theorem HypCheckProof.Std.Sat.AIG.RefVec.ite.denote_go.h7 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {assign : α → Bool} {w : Nat}
      (aig : @Std.Sat.AIG α inst_1 inst) (curr : Nat) (discr : @Std.Sat.AIG.Ref α inst inst_1 aig)
      (lhs rhs : @Std.Sat.AIG.RefVec α inst inst_1 aig w) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr) (idx : Nat)
      (hidx1 : @LT.lt Nat instLTNat idx w) (a : @LE.le Nat instLENat curr idx),
      @Eq Bool
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst
            (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 w
              (@Std.Sat.AIG.RefVec.ite.go α inst inst_1 w aig curr
                (@HypCheckProof.Std.Sat.AIG.RefVec.ite.denote_go.h7.der α inst inst_1 assign w aig curr discr lhs rhs s idx
                  hidx1 a)
                discr lhs rhs s))
            (@Std.Sat.AIG.RefVec.get α inst inst_1
              (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 w
                (@Std.Sat.AIG.RefVec.ite.go α inst inst_1 w aig curr
                  (@HypCheckProof.Std.Sat.AIG.RefVec.ite.denote_go.h7.der α inst inst_1 assign w aig curr discr lhs rhs s
                    idx hidx1 a)
                  discr lhs rhs s))
              w
              (@Std.Sat.AIG.RefVecEntry.vec α inst_1 inst inst_1 w
                (@Std.Sat.AIG.RefVec.ite.go α inst inst_1 w aig curr
                  (@HypCheckProof.Std.Sat.AIG.RefVec.ite.denote_go.h7.der α inst inst_1 assign w aig curr discr lhs rhs s
                    idx hidx1 a)
                  discr lhs rhs s))
              idx hidx1)))
        (@ite Bool
          (@Eq Bool (@Std.Sat.AIG.denote α inst inst_1 assign (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig discr))
            Bool.true)
          (instDecidableEqBool
            (@Std.Sat.AIG.denote α inst inst_1 assign (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig discr)) Bool.true)
          (@Std.Sat.AIG.denote α inst inst_1 assign
            (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w lhs idx hidx1)))
          (@Std.Sat.AIG.denote α inst inst_1 assign
            (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w rhs idx hidx1)))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13
  exact @Std.Sat.AIG.RefVec.ite.denote_go hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Std.Sat.AIG.RefVec.ite.denote_go.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13) hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq.h9.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : @Std.Sat.AIG α inst_1 inst) (distance : Nat)
      (input : @Std.Sat.AIG.RefVec α inst inst_1 aig w) (assign : α → Bool) (curr : Nat)
      (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr) (idx : Nat),
      @LT.lt Nat instLTNat idx w → @LE.le Nat instLENat curr idx → @LE.le Nat instLENat curr w := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq.h9 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : @Std.Sat.AIG α inst_1 inst) (distance : Nat)
      (input : @Std.Sat.AIG.RefVec α inst inst_1 aig w) (assign : α → Bool) (curr : Nat)
      (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr) (idx : Nat) (hidx1 : @LT.lt Nat instLTNat idx w)
      (a : @LE.le Nat instLENat curr idx),
      @Eq Bool
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst
            (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 w
              (@Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go α inst inst_1 w aig input distance curr
                (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq.h9.der α inst inst_1 w
                  aig distance input assign curr s idx hidx1 a)
                s))
            (@Std.Sat.AIG.RefVec.get α inst inst_1
              (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 w
                (@Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go α inst inst_1 w aig input distance curr
                  (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq.h9.der α inst inst_1
                    w aig distance input assign curr s idx hidx1 a)
                  s))
              w
              (@Std.Sat.AIG.RefVecEntry.vec α inst_1 inst inst_1 w
                (@Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go α inst inst_1 w aig input distance curr
                  (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq.h9.der α inst inst_1
                    w aig distance input assign curr s idx hidx1 a)
                  s))
              idx hidx1)))
        (@dite Bool (@LT.lt Nat instLTNat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) distance idx) w)
          ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) distance idx).decLt w)
          (fun (hidx : @LT.lt Nat instLTNat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) distance idx) w) =>
            @Std.Sat.AIG.denote α inst inst_1 assign
              (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig
                (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w input
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) distance idx) hidx)))
          fun (hidx : Not (@LT.lt Nat instLTNat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) distance idx) w)) =>
          Bool.false) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12) hc_x9 hc_x10 hc_x11 hc_x12

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq.h8.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] (aig : @Std.Sat.AIG α inst_1 inst) (w : Nat)
      (input : @Std.Sat.AIG.RefVec α inst inst_1 aig w) (newWidth curr : Nat)
      (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr) (assign : α → Bool) (idx : Nat),
      @LT.lt Nat instLTNat idx newWidth → @LE.le Nat instLENat curr idx → @LE.le Nat instLENat curr newWidth := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq.h8 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] (aig : @Std.Sat.AIG α inst_1 inst) (w : Nat)
      (input : @Std.Sat.AIG.RefVec α inst inst_1 aig w) (newWidth curr : Nat)
      (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr) (assign : α → Bool) (idx : Nat)
      (hidx1 : @LT.lt Nat instLTNat idx newWidth) (a : @LE.le Nat instLENat curr idx),
      @Eq Bool
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst
            (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 newWidth
              (@Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go α inst inst_1 aig w input newWidth curr
                (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq.h8.der α inst inst_1 aig w
                  input newWidth curr s assign idx hidx1 a)
                s))
            (@Std.Sat.AIG.RefVec.get α inst inst_1
              (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 newWidth
                (@Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go α inst inst_1 aig w input newWidth curr
                  (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq.h8.der α inst inst_1 aig
                    w input newWidth curr s assign idx hidx1 a)
                  s))
              newWidth
              (@Std.Sat.AIG.RefVecEntry.vec α inst_1 inst inst_1 newWidth
                (@Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go α inst inst_1 aig w input newWidth curr
                  (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq.h8.der α inst inst_1 aig
                    w input newWidth curr s assign idx hidx1 a)
                  s))
              idx hidx1)))
        (@dite Bool (@LT.lt Nat instLTNat idx w) (idx.decLt w)
          (fun (hidx : @LT.lt Nat instLTNat idx w) =>
            @Std.Sat.AIG.denote α inst inst_1 assign
              (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w input idx hidx)))
          fun (hidx : Not (@LT.lt Nat instLTNat idx w)) => Bool.false) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq.h8.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12) hc_x8 hc_x9 hc_x10 hc_x11 hc_x12

-- Std.DHashMap.Internal.Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem.h10.inst : ¬(Std.DHashMap.Internal.Raw₀.Const.insertManyIfNewUnit Std.DHashMap.Internal.Raw₀.emptyWithCapacity []).val.getKey? 0 =
        Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem.h10.prem0 : (0 == 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem.h10.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem.h10 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α] {l : List α}
        {k k' : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l →
            (Std.DHashMap.Internal.Raw₀.Const.insertManyIfNewUnit Std.DHashMap.Internal.Raw₀.emptyWithCapacity
                      l).val.getKey?
                k' =
              Option.some k := fun hc_h => HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem.h10.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ ([]) (0) (0) HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem.h10.prem0 HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem.h10.prem1)

-- Std.HashSet.Raw.get?_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashSet.Raw.get?_ofList_of_mem.h10.inst : ¬(Std.HashSet.Raw.ofList []).get? 0 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashSet.Raw.get?_ofList_of_mem.h10.prem0 : (0 == 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashSet.Raw.get?_ofList_of_mem.h10.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.HashSet.Raw.get?_ofList_of_mem.h10 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α] {l : List α}
        {k k' : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l → (Std.HashSet.Raw.ofList l).get? k' = Option.some k := fun hc_h => HypCheckProof.Std.HashSet.Raw.get?_ofList_of_mem.h10.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ ([]) (0) (0) HypCheckProof.Std.HashSet.Raw.get?_ofList_of_mem.h10.prem0 HypCheckProof.Std.HashSet.Raw.get?_ofList_of_mem.h10.prem1)

-- Std.TreeMap.head?_keys, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.head?_keys.h7.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α],
      ¬Std.LawfulOrderCmp cmp →
        ∀ [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
          t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.head?_keys.h7.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
      t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.TreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.TreeMap.head?_keys.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9 hc_x10)

-- Std.TreeMap.head?_keys, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.head?_keys.h8.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp],
      ¬Std.LawfulOrderMin α →
        ∀ [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.head?_keys.h8.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderLeftLeaningMin α]
      [inst : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.TreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.TreeMap.head?_keys.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9 hc_x10)

-- Std.TreeMap.head?_keys, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.head?_keys.h9.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α],
      ¬Std.LawfulOrderLeftLeaningMin α → ∀ [inst : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.head?_keys.h9.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderMin α] [inst : Std.LawfulEqCmp cmp],
      t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @Std.TreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.Std.TreeMap.head?_keys.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)

-- Std.TreeMap.head?_keys, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.head?_keys.h10.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], ¬Std.LawfulEqCmp cmp → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.head?_keys.h10.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.TreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h) (fun hc_hn => @HypCheckProof.Std.TreeMap.head?_keys.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn)

-- Std.DHashMap.Internal.Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains.h9.der.{u} : ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] (m : Std.DHashMap.Internal.Raw₀ α fun (x : α) => Unit)
      [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α],
      m.val.WF →
        ∀ {l : List α} {k : α},
          m.contains k = Bool.true → (Std.DHashMap.Internal.Raw₀.Const.insertManyIfNewUnit m l).val.contains k = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains.h9.{u} : ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] (m : Std.DHashMap.Internal.Raw₀ α fun (x : α) => Unit)
      [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α] (h : m.val.WF) {l : List α} {k : α}
      (contains : m.contains k = Bool.true),
      (Std.DHashMap.Internal.Raw₀.Const.insertManyIfNewUnit m l).val.getKey k
          (HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains.h9.der m h contains) =
        m.getKey k contains := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact @Std.DHashMap.Internal.Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9) hc_x9

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_denote_eq, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_denote_eq.h8.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : @Std.Sat.AIG α inst_1 inst) (c : BitVec w)
      (assign : α → Bool) (curr : Nat) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr) (idx : Nat),
      @LT.lt Nat instLTNat idx w → @LE.le Nat instLENat curr idx → @LE.le Nat instLENat curr w := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_denote_eq.h8 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : @Std.Sat.AIG α inst_1 inst) (c : BitVec w)
      (assign : α → Bool) (curr : Nat) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr) (idx : Nat)
      (hidx1 : @LT.lt Nat instLTNat idx w) (a : @LE.le Nat instLENat curr idx),
      @Eq Bool
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig
            (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w
              (@Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go α inst inst_1 w aig c curr s
                (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_denote_eq.h8.der α inst inst_1 w aig c
                  assign curr s idx hidx1 a))
              idx hidx1)))
        (@BitVec.getLsbD w c idx) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_denote_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_denote_eq.h8.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11) hc_x8 hc_x9 hc_x10 hc_x11

-- Std.Internal.List.minKey?_insertEntryIfNew_of_isEmpty, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_of_isEmpty.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      ¬Std.Internal.List.DistinctKeys l →
        l.isEmpty = Bool.true → Std.Internal.List.minKey? (Std.Internal.List.insertEntryIfNew k v l) = Option.some k := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_of_isEmpty.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → Std.Internal.List.minKey? (Std.Internal.List.insertEntryIfNew k v l) = Option.some k := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @Std.Internal.List.minKey?_insertEntryIfNew_of_isEmpty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_of_isEmpty.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_of_isEmpty.h9.derivable.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)}, l.isEmpty = Bool.true → Std.Internal.List.DistinctKeys l := by
  (intros; simp_all; done)

-- Std.Internal.List.minKey_insertEntry_of_isEmpty, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey_insertEntry_of_isEmpty.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      ¬Std.Internal.List.DistinctKeys l →
        l.isEmpty = Bool.true →
          Std.Internal.List.minKey (Std.Internal.List.insertEntry k v l) Std.Internal.List.isEmpty_insertEntry = k := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.minKey_insertEntry_of_isEmpty.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true →
        Std.Internal.List.minKey (Std.Internal.List.insertEntry k v l) Std.Internal.List.isEmpty_insertEntry = k := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @Std.Internal.List.minKey_insertEntry_of_isEmpty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.Std.Internal.List.minKey_insertEntry_of_isEmpty.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey_insertEntry_of_isEmpty.h9.derivable.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)}, l.isEmpty = Bool.true → Std.Internal.List.DistinctKeys l := by
  (intros; simp_all; done)

-- Std.Ric.length_iter, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Ric.length_iter.h6.gneg.{u_1} : ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : DecidableLE α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α],
      ¬Std.Rxc.IsAlwaysFinite α →
        ∀ [inst_5 : Std.PRange.LawfulUpwardEnumerable α] [inst_6 : Std.Rxc.HasSize α] [inst_7 : Std.Rxc.LawfulHasSize α]
          {r : Std.Ric α}, r.iter.length = r.size := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Ric.length_iter.h6.{u_1} : ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : DecidableLE α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] [inst_6 : Std.Rxc.HasSize α] [inst_7 : Std.Rxc.LawfulHasSize α]
      {r : Std.Ric α}, r.iter.length = r.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x7 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.Ric.length_iter hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h hc_x7 hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.Ric.length_iter.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn hc_x7 hc_x8 hc_x9 hc_x10)

-- Std.Internal.List.congr_filter_not_contains_map_fst_of_perm, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.congr_filter_not_contains_map_fst_of_perm.h7.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {l₁ l₂ l₃ l₄ : List ((a : α) × β a)} [inst : BEq α],
      ¬EquivBEq α →
        l₁.Perm l₃ →
          l₂.Perm l₄ →
            Std.Internal.List.DistinctKeys l₃ →
              (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₂).contains p.fst) l₁).Perm
                (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₄).contains p.fst) l₃) := by
  (intros; grind)
theorem HypCheckProof.Std.Internal.List.congr_filter_not_contains_map_fst_of_perm.h7.{u, v} : ∀ {α : Type u} {β : α → Type v} {l₁ l₂ l₃ l₄ : List ((a : α) × β a)} [inst : BEq α],
      l₁.Perm l₃ →
        l₂.Perm l₄ →
          Std.Internal.List.DistinctKeys l₃ →
            (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₂).contains p.fst) l₁).Perm
              (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₄).contains p.fst) l₃) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.Internal.List.congr_filter_not_contains_map_fst_of_perm hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.Internal.List.congr_filter_not_contains_map_fst_of_perm.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9 hc_x10)

-- Std.Internal.List.congr_filter_not_contains_map_fst_of_perm, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.congr_filter_not_contains_map_fst_of_perm.h10.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {l₁ l₂ l₃ l₄ : List ((a : α) × β a)} [inst : BEq α] [inst_1 : EquivBEq α],
      l₁.Perm l₃ →
        l₂.Perm l₄ →
          ¬Std.Internal.List.DistinctKeys l₃ →
            (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₂).contains p.fst) l₁).Perm
              (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₄).contains p.fst) l₃) := by
  (intros; grind)
theorem HypCheckProof.Std.Internal.List.congr_filter_not_contains_map_fst_of_perm.h10.{u, v} : ∀ {α : Type u} {β : α → Type v} {l₁ l₂ l₃ l₄ : List ((a : α) × β a)} [inst : BEq α] [inst_1 : EquivBEq α],
      l₁.Perm l₃ →
        l₂.Perm l₄ →
          (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₂).contains p.fst) l₁).Perm
            (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₄).contains p.fst) l₃) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.Internal.List.congr_filter_not_contains_map_fst_of_perm hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h) (fun hc_hn => @HypCheckProof.Std.Internal.List.congr_filter_not_contains_map_fst_of_perm.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn)

-- Std.ExtTreeSet.head?_toList, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeSet.head?_toList.h6.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Min α]
      [inst_2 : LE α],
      ¬Std.LawfulOrderCmp cmp →
        ∀ [inst_3 : Std.LawfulOrderMin α] [inst_4 : Std.LawfulOrderLeftLeaningMin α] [inst_5 : Std.LawfulEqCmp cmp],
          t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeSet.head?_toList.h6.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Min α]
      [inst_2 : LE α] [inst_3 : Std.LawfulOrderMin α] [inst_4 : Std.LawfulOrderLeftLeaningMin α]
      [inst_5 : Std.LawfulEqCmp cmp], t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.ExtTreeSet.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.Std.ExtTreeSet.head?_toList.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn hc_x7 hc_x8 hc_x9)

-- Std.ExtTreeSet.head?_toList, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeSet.head?_toList.h7.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Min α]
      [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp],
      ¬Std.LawfulOrderMin α →
        ∀ [inst_4 : Std.LawfulOrderLeftLeaningMin α] [inst_5 : Std.LawfulEqCmp cmp], t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeSet.head?_toList.h7.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Min α]
      [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderLeftLeaningMin α]
      [inst_5 : Std.LawfulEqCmp cmp], t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.ExtTreeSet.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.Std.ExtTreeSet.head?_toList.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9)

-- Std.ExtTreeSet.head?_toList, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeSet.head?_toList.h8.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Min α]
      [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α],
      ¬Std.LawfulOrderLeftLeaningMin α → ∀ [inst_5 : Std.LawfulEqCmp cmp], t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeSet.head?_toList.h8.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Min α]
      [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α] [inst_5 : Std.LawfulEqCmp cmp],
      t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9
  exact Classical.byCases (fun hc_h => @Std.ExtTreeSet.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9) (fun hc_hn => @HypCheckProof.Std.ExtTreeSet.head?_toList.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9)

-- Std.ExtTreeSet.head?_toList, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeSet.head?_toList.h9.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Min α]
      [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α]
      [inst_5 : Std.LawfulOrderLeftLeaningMin α], ¬Std.LawfulEqCmp cmp → t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeSet.head?_toList.h9.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Min α]
      [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α]
      [inst_5 : Std.LawfulOrderLeftLeaningMin α], t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact Classical.byCases (fun hc_h => @Std.ExtTreeSet.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h) (fun hc_hn => @HypCheckProof.Std.ExtTreeSet.head?_toList.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn)

-- Std.TreeSet.head?_toList, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.head?_toList.h6.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Min α]
      [inst_1 : LE α],
      ¬Std.LawfulOrderCmp cmp →
        ∀ [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
          t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.head?_toList.h6.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Min α] [inst_1 : LE α]
      [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
      t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.TreeSet.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.Std.TreeSet.head?_toList.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn hc_x7 hc_x8 hc_x9)

-- Std.TreeSet.head?_toList, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.head?_toList.h7.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Min α] [inst_1 : LE α]
      [inst_2 : Std.LawfulOrderCmp cmp],
      ¬Std.LawfulOrderMin α →
        ∀ [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp], t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.head?_toList.h7.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Min α] [inst_1 : LE α]
      [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
      t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.TreeSet.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.Std.TreeSet.head?_toList.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9)

-- Std.TreeSet.head?_toList, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.head?_toList.h8.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Min α] [inst_1 : LE α]
      [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α],
      ¬Std.LawfulOrderLeftLeaningMin α → ∀ [inst : Std.LawfulEqCmp cmp], t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.head?_toList.h8.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Min α] [inst_1 : LE α]
      [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderMin α] [inst : Std.LawfulEqCmp cmp], t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9
  exact Classical.byCases (fun hc_h => @Std.TreeSet.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9) (fun hc_hn => @HypCheckProof.Std.TreeSet.head?_toList.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9)

-- Std.TreeSet.head?_toList, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.head?_toList.h9.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Min α] [inst_1 : LE α]
      [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α],
      ¬Std.LawfulEqCmp cmp → t.toList.head? = t.min? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.head?_toList.h9.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Min α] [inst_1 : LE α]
      [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α],
      t.toList.head? = t.min? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact Classical.byCases (fun hc_h => @Std.TreeSet.head?_toList hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h) (fun hc_hn => @HypCheckProof.Std.TreeSet.head?_toList.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn)

-- Std.ExtDHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.der.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.ExtDHashMap α fun (x : α) => Unit} [inst : EquivBEq α]
      [inst_1 : LawfulHashable α] {l : List α} {k : α}, k ∈ m → k ∈ Std.ExtDHashMap.Const.insertManyIfNewUnit m l := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.ExtDHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.ExtDHashMap α fun (x : α) => Unit} [inst : EquivBEq α]
      [inst_1 : LawfulHashable α] {l : List α} {k : α} (mem : k ∈ m),
      (Std.ExtDHashMap.Const.insertManyIfNewUnit m l).getKey k
          (HypCheckProof.Std.ExtDHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.der mem) =
        m.getKey k mem := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact @Std.ExtDHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.ExtDHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8)

-- Std.ExtHashMap.getKey_insertManyIfNewUnit_list_of_mem, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtHashMap.getKey_insertManyIfNewUnit_list_of_mem.h9.der.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.ExtHashMap α Unit} [inst : EquivBEq α]
      [inst_1 : LawfulHashable α] {l : List α} {k : α}, k ∈ m → k ∈ m.insertManyIfNewUnit l := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.ExtHashMap.getKey_insertManyIfNewUnit_list_of_mem.h9.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.ExtHashMap α Unit} [inst : EquivBEq α]
      [inst_1 : LawfulHashable α] {l : List α} {k : α} (mem : k ∈ m),
      (m.insertManyIfNewUnit l).getKey k (HypCheckProof.Std.ExtHashMap.getKey_insertManyIfNewUnit_list_of_mem.h9.der mem) =
        m.getKey k mem := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact @Std.ExtHashMap.getKey_insertManyIfNewUnit_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.ExtHashMap.getKey_insertManyIfNewUnit_list_of_mem.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8)

-- Std.ExtHashSet.get_insertMany_list_of_mem, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtHashSet.get_insertMany_list_of_mem.h9.der.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.ExtHashSet α} [inst : EquivBEq α] [inst_1 : LawfulHashable α]
      {l : List α} {k : α}, k ∈ m → k ∈ m.insertMany l := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.ExtHashSet.get_insertMany_list_of_mem.h9.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.ExtHashSet α} [inst : EquivBEq α] [inst_1 : LawfulHashable α]
      {l : List α} {k : α} (mem : k ∈ m),
      (m.insertMany l).get k (HypCheckProof.Std.ExtHashSet.get_insertMany_list_of_mem.h9.der mem) = m.get k mem := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact @Std.ExtHashSet.get_insertMany_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.ExtHashSet.get_insertMany_list_of_mem.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8)

-- Std.ExtDTreeMap.mem_of_get_eq, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDTreeMap.mem_of_get_eq.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Std.LawfulEqCmp cmp] {k : α} {v : β k} {w : k ∈ t}, ¬t.get k w = v → k ∈ t := by
  (intros; omega)
theorem HypCheckProof.Std.ExtDTreeMap.mem_of_get_eq.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Std.LawfulEqCmp cmp] {k : α} {v : β k} {w : k ∈ t}, k ∈ t := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact Classical.byCases (fun hc_h => @Std.ExtDTreeMap.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h) (fun hc_hn => @HypCheckProof.Std.ExtDTreeMap.mem_of_get_eq.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn)

-- Std.HashMap.getKey_insertManyIfNewUnit_list_of_mem, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.HashMap.getKey_insertManyIfNewUnit_list_of_mem.h9.der.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.HashMap α Unit} [inst : EquivBEq α] [inst : LawfulHashable α]
      {l : List α} {k : α}, k ∈ m → k ∈ m.insertManyIfNewUnit l := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.HashMap.getKey_insertManyIfNewUnit_list_of_mem.h9.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.HashMap α Unit} [inst : EquivBEq α] [inst_1 : LawfulHashable α]
      {l : List α} {k : α} (mem : k ∈ m),
      (m.insertManyIfNewUnit l).getKey k (HypCheckProof.Std.HashMap.getKey_insertManyIfNewUnit_list_of_mem.h9.der mem) =
        m.getKey k mem := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact @Std.HashMap.getKey_insertManyIfNewUnit_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.HashMap.getKey_insertManyIfNewUnit_list_of_mem.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8)

-- Std.HashSet.get_insertMany_list_of_mem, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.HashSet.get_insertMany_list_of_mem.h9.der.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.HashSet α} [inst : EquivBEq α] [inst : LawfulHashable α]
      {l : List α} {k : α}, k ∈ m → k ∈ m.insertMany l := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.HashSet.get_insertMany_list_of_mem.h9.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.HashSet α} [inst : EquivBEq α] [inst_1 : LawfulHashable α]
      {l : List α} {k : α} (mem : k ∈ m),
      (m.insertMany l).get k (HypCheckProof.Std.HashSet.get_insertMany_list_of_mem.h9.der mem) = m.get k mem := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact @Std.HashSet.get_insertMany_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.HashSet.get_insertMany_list_of_mem.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8)

-- Std.Roo.length_iter, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Roo.length_iter.h5.gneg.{u_1} : ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLT α],
      ¬Std.Rxo.IsAlwaysFinite α →
        ∀ [inst_4 : Std.PRange.LawfulUpwardEnumerable α] [inst_5 : Std.Rxo.HasSize α] [inst_6 : Std.Rxo.LawfulHasSize α]
          {r : Std.Roo α}, r.iter.length = r.size := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Roo.length_iter.h5.{u_1} : ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.Rxo.HasSize α] [inst_6 : Std.Rxo.LawfulHasSize α] {r : Std.Roo α}, r.iter.length = r.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.Roo.length_iter hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6 hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.Std.Roo.length_iter.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6 hc_x7 hc_x8 hc_x9)

-- Std.Rco.length_iter, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Rco.length_iter.h5.gneg.{u_1} : ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLT α],
      ¬Std.Rxo.IsAlwaysFinite α →
        ∀ [inst_4 : Std.PRange.LawfulUpwardEnumerable α] [inst_5 : Std.Rxo.HasSize α] [inst_6 : Std.Rxo.LawfulHasSize α]
          {r : Std.Rco α}, r.iter.length = r.size := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Rco.length_iter.h5.{u_1} : ∀ {α : Type u_1} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.Rxo.HasSize α] [inst_6 : Std.Rxo.LawfulHasSize α] {r : Std.Rco α}, r.iter.length = r.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.Rco.length_iter hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6 hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.Std.Rco.length_iter.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6 hc_x7 hc_x8 hc_x9)

-- Std.Rcc.length_iter, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Rcc.length_iter.h5.gneg.{u_1} : ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α],
      ¬Std.Rxc.IsAlwaysFinite α →
        ∀ [inst_4 : Std.PRange.LawfulUpwardEnumerable α] [inst_5 : Std.Rxc.HasSize α] [inst_6 : Std.Rxc.LawfulHasSize α]
          {r : Std.Rcc α}, r.iter.length = r.size := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Rcc.length_iter.h5.{u_1} : ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.Rxc.HasSize α] [inst_6 : Std.Rxc.LawfulHasSize α] {r : Std.Rcc α}, r.iter.length = r.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.Rcc.length_iter hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6 hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.Std.Rcc.length_iter.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6 hc_x7 hc_x8 hc_x9)

-- Std.Roc.length_iter, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Roc.length_iter.h5.gneg.{u_1} : ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α],
      ¬Std.Rxc.IsAlwaysFinite α →
        ∀ [inst_4 : Std.PRange.LawfulUpwardEnumerable α] [inst_5 : Std.Rxc.HasSize α] [inst_6 : Std.Rxc.LawfulHasSize α]
          {r : Std.Roc α}, r.iter.length = r.size := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Roc.length_iter.h5.{u_1} : ∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.Rxc.HasSize α] [inst_6 : Std.Rxc.LawfulHasSize α] {r : Std.Roc α}, r.iter.length = r.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.Roc.length_iter hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6 hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.Std.Roc.length_iter.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6 hc_x7 hc_x8 hc_x9)

-- Std.DHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.der.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.DHashMap α fun (x : α) => Unit} [inst : EquivBEq α]
      [inst : LawfulHashable α] {l : List α} {k : α}, k ∈ m → k ∈ Std.DHashMap.Const.insertManyIfNewUnit m l := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.DHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.DHashMap α fun (x : α) => Unit} [inst : EquivBEq α]
      [inst_1 : LawfulHashable α] {l : List α} {k : α} (mem : k ∈ m),
      (Std.DHashMap.Const.insertManyIfNewUnit m l).getKey k
          (HypCheckProof.Std.DHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.der mem) =
        m.getKey k mem := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact @Std.DHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.DHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8)

-- Std.DHashMap.Raw.mem_of_get_eq, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.Raw.mem_of_get_eq.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulBEq α]
      {k : α} {v : β k} {w : k ∈ m}, ¬m.get k w = v → k ∈ m := by
  (intros; omega)
theorem HypCheckProof.Std.DHashMap.Raw.mem_of_get_eq.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulBEq α]
      {k : α} {v : β k} {w : k ∈ m}, k ∈ m := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact Classical.byCases (fun hc_h => @Std.DHashMap.Raw.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h) (fun hc_hn => @HypCheckProof.Std.DHashMap.Raw.mem_of_get_eq.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn)

-- Std.Internal.List.getKey_modifyKey, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.getKey_modifyKey.h8.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : LawfulBEq α] {k k' : α} {f : β k → β k}
      (l : List ((a : α) × β a)),
      ¬Std.Internal.List.DistinctKeys l →
        ∀ (h : Std.Internal.List.containsKey k' (Std.Internal.List.modifyKey k f l) = Bool.true),
          Std.Internal.List.getKey k' (Std.Internal.List.modifyKey k f l) h =
            if (k == k') = Bool.true then k
            else
              Std.Internal.List.getKey k' l
                ((fun {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] {k k' : α} {f : β k → β k}
                      (l : List ((a : α) × β a))
                      (h : Std.Internal.List.containsKey k' (Std.Internal.List.modifyKey k f l) = Bool.true) =>
                    Eq.mp (congrArg (fun (_a : Bool) => _a = Bool.true) (Std.Internal.List.containsKey_modifyKey k k' f l))
                      h)
                  l h) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.getKey_modifyKey.h8.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : LawfulBEq α] {k k' : α} {f : β k → β k}
      (l : List ((a : α) × β a)) (h : Std.Internal.List.containsKey k' (Std.Internal.List.modifyKey k f l) = Bool.true),
      Std.Internal.List.getKey k' (Std.Internal.List.modifyKey k f l) h =
        if (k == k') = Bool.true then k
        else
          Std.Internal.List.getKey k' l
            ((fun {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] {k k' : α} {f : β k → β k} (l : List ((a : α) × β a))
                  (h : Std.Internal.List.containsKey k' (Std.Internal.List.modifyKey k f l) = Bool.true) =>
                Eq.mp (congrArg (fun (_a : Bool) => _a = Bool.true) (Std.Internal.List.containsKey_modifyKey k k' f l)) h)
              l h) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9
  exact Classical.byCases (fun hc_h => @Std.Internal.List.getKey_modifyKey hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9) (fun hc_hn => @HypCheckProof.Std.Internal.List.getKey_modifyKey.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9)

-- Std.ExtDHashMap.mem_of_get_eq, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDHashMap.mem_of_get_eq.h9.gneg.{u, v} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} {m : Std.ExtDHashMap α β} [inst : LawfulBEq α] {k : α}
      {v : β k} {w : k ∈ m}, ¬m.get k w = v → k ∈ m := by
  (intros; omega)
theorem HypCheckProof.Std.ExtDHashMap.mem_of_get_eq.h9.{u, v} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} {m : Std.ExtDHashMap α β} [inst : LawfulBEq α] {k : α}
      {v : β k} {w : k ∈ m}, k ∈ m := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact Classical.byCases (fun hc_h => @Std.ExtDHashMap.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h) (fun hc_hn => @HypCheckProof.Std.ExtDHashMap.mem_of_get_eq.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn)

-- Std.DHashMap.mem_of_get_eq, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.mem_of_get_eq.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} {m : Std.DHashMap α β} [inst : LawfulBEq α] {k : α}
      {v : β k} {w : k ∈ m}, ¬m.get k w = v → k ∈ m := by
  (intros; omega)
theorem HypCheckProof.Std.DHashMap.mem_of_get_eq.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} {m : Std.DHashMap α β} [inst : LawfulBEq α] {k : α}
      {v : β k} {w : k ∈ m}, k ∈ m := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact Classical.byCases (fun hc_h => @Std.DHashMap.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h) (fun hc_hn => @HypCheckProof.Std.DHashMap.mem_of_get_eq.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn)

-- List.lt_of_range'_eq_append_cons, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h7.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h7.prem0 : 0 < 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h7.prem1 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h7 : ¬∀ {s n : Nat} {step : Nat} {xs : List Nat} {i : Nat} {ys : List Nat} {j : Nat}, 0 < step → j ∈ ys → i < j := fun hc_h => HypCheckProof.List.lt_of_range'_eq_append_cons.h7.inst (@hc_h (0) (0) (1) ([]) (0) ([0]) (0) HypCheckProof.List.lt_of_range'_eq_append_cons.h7.prem0 HypCheckProof.List.lt_of_range'_eq_append_cons.h7.prem1)

-- List.lt_of_range'_eq_append_cons, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h8.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h8.prem0 : List.range' 0 2 0 = [] ++ [0, 0] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h8.prem1 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h8 : ¬∀ {s n step : Nat} {xs : List Nat} {i : Nat} {ys : List Nat} {j : Nat},
        List.range' s n step = xs ++ i :: ys → j ∈ ys → i < j := fun hc_h => HypCheckProof.List.lt_of_range'_eq_append_cons.h8.inst (@hc_h (0) (2) (0) ([]) (0) ([0]) (0) HypCheckProof.List.lt_of_range'_eq_append_cons.h8.prem0 HypCheckProof.List.lt_of_range'_eq_append_cons.h8.prem1)

-- List.lt_of_range'_eq_append_cons, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h9.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h9.prem0 : List.range' 0 1 = [] ++ [0] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h9.prem1 : 0 < 1 := by
  decide
theorem HypCheckProof.List.lt_of_range'_eq_append_cons.h9 : ¬∀ {s n step : Nat} {xs : List Nat} {i : Nat} {ys : List Nat} {j : Nat},
        List.range' s n step = xs ++ i :: ys → 0 < step → i < j := fun hc_h => HypCheckProof.List.lt_of_range'_eq_append_cons.h9.inst (@hc_h (0) (1) (1) ([]) (0) ([]) (0) HypCheckProof.List.lt_of_range'_eq_append_cons.h9.prem0 HypCheckProof.List.lt_of_range'_eq_append_cons.h9.prem1)

-- List.gt_of_range'_eq_append_cons, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h7.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h7.prem0 : 0 < 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h7.prem1 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h7 : ¬∀ {s n : Nat} {step : Nat} {xs : List Nat} {i : Nat} {ys : List Nat} {j : Nat}, 0 < step → j ∈ xs → j < i := fun hc_h => HypCheckProof.List.gt_of_range'_eq_append_cons.h7.inst (@hc_h (0) (0) (1) ([0]) (0) ([]) (0) HypCheckProof.List.gt_of_range'_eq_append_cons.h7.prem0 HypCheckProof.List.gt_of_range'_eq_append_cons.h7.prem1)

-- List.gt_of_range'_eq_append_cons, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h8.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h8.prem0 : List.range' 0 2 0 = [0] ++ [0] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h8.prem1 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h8 : ¬∀ {s n step : Nat} {xs : List Nat} {i : Nat} {ys : List Nat} {j : Nat},
        List.range' s n step = xs ++ i :: ys → j ∈ xs → j < i := fun hc_h => HypCheckProof.List.gt_of_range'_eq_append_cons.h8.inst (@hc_h (0) (2) (0) ([0]) (0) ([]) (0) HypCheckProof.List.gt_of_range'_eq_append_cons.h8.prem0 HypCheckProof.List.gt_of_range'_eq_append_cons.h8.prem1)

-- List.gt_of_range'_eq_append_cons, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h9.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h9.prem0 : List.range' 0 1 = [] ++ [0] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h9.prem1 : 0 < 1 := by
  decide
theorem HypCheckProof.List.gt_of_range'_eq_append_cons.h9 : ¬∀ {s n step : Nat} {xs : List Nat} {i : Nat} {ys : List Nat} {j : Nat},
        List.range' s n step = xs ++ i :: ys → 0 < step → j < i := fun hc_h => HypCheckProof.List.gt_of_range'_eq_append_cons.h9.inst (@hc_h (0) (1) (1) ([]) (0) ([]) (0) HypCheckProof.List.gt_of_range'_eq_append_cons.h9.prem0 HypCheckProof.List.gt_of_range'_eq_append_cons.h9.prem1)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq.h5.der : ∀ {w : Nat}
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (a : Nat) (assign : Std.Tactic.BVDecide.BVExpr.Assignment) (curr : Nat)
      (s :
        @Std.Sat.AIG.RefVec Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instHashableBVBit
          Std.Tactic.BVDecide.instDecidableEqBVBit aig curr)
      (idx : Nat), @LT.lt Nat instLTNat idx w → @LE.le Nat instLENat curr idx → @LE.le Nat instLENat curr w := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq.h5 : ∀ {w : Nat}
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (a : Nat) (assign : Std.Tactic.BVDecide.BVExpr.Assignment) (curr : Nat)
      (s :
        @Std.Sat.AIG.RefVec Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instHashableBVBit
          Std.Tactic.BVDecide.instDecidableEqBVBit aig curr)
      (idx : Nat) (hidx1 : @LT.lt Nat instLTNat idx w) (a_1 : @LE.le Nat instLENat curr idx),
      @Eq Bool
        (@Std.Sat.AIG.denote Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instHashableBVBit
          Std.Tactic.BVDecide.instDecidableEqBVBit assign.toAIGAssignment
          (@Std.Sat.AIG.Entrypoint.mk Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit
            (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w
              (Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go aig w a curr s
                (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq.h5.der w aig a assign curr s idx
                  hidx1 a_1)))
            (@Std.Sat.AIG.RefVec.get Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instHashableBVBit
              Std.Tactic.BVDecide.instDecidableEqBVBit
              (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w
                (Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go aig w a curr s
                  (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq.h5.der w aig a assign curr s idx
                    hidx1 a_1)))
              w
              (@Std.Sat.AIG.RefVecEntry.vec Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w
                (Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go aig w a curr s
                  (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq.h5.der w aig a assign curr s idx
                    hidx1 a_1)))
              idx hidx1)))
        (@BitVec.getLsbD w (@Std.Tactic.BVDecide.BVExpr.eval w assign (@Std.Tactic.BVDecide.BVExpr.var w a)) idx) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8) hc_x5 hc_x6 hc_x7 hc_x8

-- Std.ExtHashSet.mem_of_get_eq, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtHashSet.mem_of_get_eq.h8.gneg.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} [inst : LawfulBEq α] (m : Std.ExtHashSet α) {k v : α} {w : k ∈ m},
      ¬m.get k w = v → k ∈ m := by
  (intros; omega)
theorem HypCheckProof.Std.ExtHashSet.mem_of_get_eq.h8.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} [inst : LawfulBEq α] (m : Std.ExtHashSet α) {k : α} {v : α} {w : k ∈ m},
      k ∈ m := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact Classical.byCases (fun hc_h => @Std.ExtHashSet.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h) (fun hc_hn => @HypCheckProof.Std.ExtHashSet.mem_of_get_eq.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn)

-- Std.DTreeMap.mem_of_get_eq, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_get_eq.h8.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {k : α}
      {v : β k} {w : k ∈ t}, ¬t.get k w = v → k ∈ t := by
  (intros; omega)
theorem HypCheckProof.Std.DTreeMap.mem_of_get_eq.h8.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {k : α}
      {v : β k} {w : k ∈ t}, k ∈ t := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h) (fun hc_hn => @HypCheckProof.Std.DTreeMap.mem_of_get_eq.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn)

-- Std.DTreeMap.Raw.mem_of_get_eq, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.Raw.mem_of_get_eq.h8.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.LawfulEqCmp cmp]
      {k : α} {v : β k} {w : k ∈ t}, ¬t.get k w = v → k ∈ t := by
  (intros; omega)
theorem HypCheckProof.Std.DTreeMap.Raw.mem_of_get_eq.h8.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.LawfulEqCmp cmp]
      {k : α} {v : β k} {w : k ∈ t}, k ∈ t := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact Classical.byCases (fun hc_h => @Std.DTreeMap.Raw.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h) (fun hc_hn => @HypCheckProof.Std.DTreeMap.Raw.mem_of_get_eq.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn)

-- Std.Internal.List.getKey_modifyKey_self, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.getKey_modifyKey_self.h7.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : LawfulBEq α] {k : α} {f : β k → β k}
      (l : List ((a : α) × β a)),
      ¬Std.Internal.List.DistinctKeys l →
        ∀ (h : Std.Internal.List.containsKey k (Std.Internal.List.modifyKey k f l) = Bool.true),
          Std.Internal.List.getKey k (Std.Internal.List.modifyKey k f l) h = k := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.getKey_modifyKey_self.h7.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : LawfulBEq α] {k : α} {f : β k → β k} (l : List ((a : α) × β a))
      (h : Std.Internal.List.containsKey k (Std.Internal.List.modifyKey k f l) = Bool.true),
      Std.Internal.List.getKey k (Std.Internal.List.modifyKey k f l) h = k := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8
  exact Classical.byCases (fun hc_h => @Std.Internal.List.getKey_modifyKey_self hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8) (fun hc_hn => @HypCheckProof.Std.Internal.List.getKey_modifyKey_self.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8)

-- Std.Tactic.BVDecide.Reflect.Bool.cond_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.cond_congr.h6.inst : ¬(bif Bool.true then Bool.false else Bool.true) = bif Bool.false then Bool.false else Bool.true := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.cond_congr.h6 : ¬∀ (discr lhs rhs discr' lhs' rhs' : Bool),
        lhs' = lhs → rhs' = rhs → (bif discr' then lhs' else rhs') = bif discr then lhs else rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.cond_congr.h6.inst (@hc_h (Bool.false) (Bool.false) (Bool.true) (Bool.true) (Bool.false) (Bool.true) rfl rfl)

-- Std.Tactic.BVDecide.Reflect.Bool.cond_congr, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.cond_congr.h7.inst : ¬(bif Bool.true then Bool.true else Bool.false) = bif Bool.true then Bool.false else Bool.false := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.cond_congr.h7 : ¬∀ (discr lhs rhs discr' lhs' rhs' : Bool),
        discr' = discr → rhs' = rhs → (bif discr' then lhs' else rhs') = bif discr then lhs else rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.cond_congr.h7.inst (@hc_h (Bool.true) (Bool.false) (Bool.false) (Bool.true) (Bool.true) (Bool.false) rfl rfl)

-- Std.Tactic.BVDecide.Reflect.Bool.cond_congr, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.cond_congr.h8.inst : ¬(bif Bool.false then Bool.false else Bool.true) = bif Bool.false then Bool.false else Bool.false := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.cond_congr.h8 : ¬∀ (discr lhs rhs discr' lhs' rhs' : Bool),
        discr' = discr → lhs' = lhs → (bif discr' then lhs' else rhs') = bif discr then lhs else rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.cond_congr.h8.inst (@hc_h (Bool.false) (Bool.false) (Bool.false) (Bool.false) (Bool.false) (Bool.true) rfl rfl)

-- Std.ExtTreeSet.mem_of_get_eq, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeSet.mem_of_get_eq.h7.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {k v : α} {w : k ∈ t},
      ¬t.get k w = v → k ∈ t := by
  (intros; omega)
theorem HypCheckProof.Std.ExtTreeSet.mem_of_get_eq.h7.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {v : α}
      {w : k ∈ t}, k ∈ t := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @Std.ExtTreeSet.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h) (fun hc_hn => @HypCheckProof.Std.ExtTreeSet.mem_of_get_eq.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn)

-- Std.Sat.AIG.BinaryInput.each_cast, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.BinaryInput.each_cast.h7.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {aig1 aig2 : Std.Sat.AIG α} (lhs rhs : aig1.Ref),
      aig1.decls.size ≤ aig2.decls.size → aig1.decls.size ≤ aig2.decls.size := by
  (intros; omega)
theorem HypCheckProof.Std.Sat.AIG.BinaryInput.each_cast.h7 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {aig1 aig2 : Std.Sat.AIG α} (lhs rhs : aig1.Ref)
      (h2 : aig1.decls.size ≤ aig2.decls.size),
      { lhs := lhs.cast (HypCheckProof.Std.Sat.AIG.BinaryInput.each_cast.h7.der lhs rhs h2), rhs := rhs.cast h2 :
          aig2.BinaryInput } =
        { lhs := lhs, rhs := rhs : aig1.BinaryInput }.cast h2 := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @Std.Sat.AIG.BinaryInput.each_cast hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Std.Sat.AIG.BinaryInput.each_cast.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7) hc_x7

-- Std.Sat.AIG.BinaryInput.each_cast, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.BinaryInput.each_cast.h8.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {aig1 aig2 : Std.Sat.AIG α} (lhs rhs : aig1.Ref),
      aig1.decls.size ≤ aig2.decls.size → aig1.decls.size ≤ aig2.decls.size := by
  (intros; omega)
theorem HypCheckProof.Std.Sat.AIG.BinaryInput.each_cast.h8 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {aig1 aig2 : Std.Sat.AIG α} (lhs rhs : aig1.Ref)
      (h1 : aig1.decls.size ≤ aig2.decls.size),
      { lhs := lhs.cast h1, rhs := rhs.cast (HypCheckProof.Std.Sat.AIG.BinaryInput.each_cast.h8.der lhs rhs h1) :
          aig2.BinaryInput } =
        { lhs := lhs, rhs := rhs : aig1.BinaryInput }.cast
          (HypCheckProof.Std.Sat.AIG.BinaryInput.each_cast.h8.der lhs rhs h1) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @Std.Sat.AIG.BinaryInput.each_cast hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 (@HypCheckProof.Std.Sat.AIG.BinaryInput.each_cast.h8.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7)

-- Std.Sat.AIG.denote_gate_push, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.denote_gate_push.h7.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {assign : α → Bool} {aig1 aig2 : @Std.Sat.AIG α inst_1 inst}
      {input : @Std.Sat.AIG.BinaryInput α inst inst_1 aig1},
      @Eq (Array (Std.Sat.AIG.Decl α)) (@Std.Sat.AIG.decls α inst_1 inst aig2)
          (@Array.push (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig1)
            (@Std.Sat.AIG.Decl.gate α
              (Std.Sat.AIG.Fanin.mk
                (@Std.Sat.AIG.Ref.gate α inst inst_1 aig1 (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig1 input))
                (@Std.Sat.AIG.Ref.invert α inst inst_1 aig1 (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig1 input)))
              (Std.Sat.AIG.Fanin.mk
                (@Std.Sat.AIG.Ref.gate α inst inst_1 aig1 (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig1 input))
                (@Std.Sat.AIG.Ref.invert α inst inst_1 aig1 (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig1 input))))) →
        @LT.lt Nat instLTNat (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig1))
          (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig2)) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Sat.AIG.denote_gate_push.h7 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {assign : α → Bool} {aig1 aig2 : @Std.Sat.AIG α inst_1 inst}
      {input : @Std.Sat.AIG.BinaryInput α inst inst_1 aig1}
      (h :
        @Eq (Array (Std.Sat.AIG.Decl α)) (@Std.Sat.AIG.decls α inst_1 inst aig2)
          (@Array.push (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig1)
            (@Std.Sat.AIG.Decl.gate α
              (Std.Sat.AIG.Fanin.mk
                (@Std.Sat.AIG.Ref.gate α inst inst_1 aig1 (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig1 input))
                (@Std.Sat.AIG.Ref.invert α inst inst_1 aig1 (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig1 input)))
              (Std.Sat.AIG.Fanin.mk
                (@Std.Sat.AIG.Ref.gate α inst inst_1 aig1 (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig1 input))
                (@Std.Sat.AIG.Ref.invert α inst inst_1 aig1 (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig1 input)))))),
      @Eq Bool
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig2
            (@Std.Sat.AIG.Ref.mk α inst inst_1 aig2
              (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig1)) Bool.false
              (@HypCheckProof.Std.Sat.AIG.denote_gate_push.h7.der α inst inst_1 assign aig1 aig2 input h))))
        ((@Std.Sat.AIG.denote α inst inst_1 assign
              (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig1 (@Std.Sat.AIG.BinaryInput.lhs α inst inst_1 aig1 input))).and
          (@Std.Sat.AIG.denote α inst inst_1 assign
            (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig1 (@Std.Sat.AIG.BinaryInput.rhs α inst inst_1 aig1 input)))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @Std.Sat.AIG.denote_gate_push hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Std.Sat.AIG.denote_gate_push.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7) hc_x7

-- Std.TreeMap.getKey_maxKey, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.getKey_maxKey.h6.der.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t.isEmpty = Bool.false}, t.maxKey he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.getKey_maxKey.h6.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t.isEmpty = Bool.false}, t.getKey (t.maxKey he) HypCheckProof.Std.TreeMap.getKey_maxKey.h6.der = t.maxKey he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.TreeMap.getKey_maxKey hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.TreeMap.getKey_maxKey.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.ExtTreeMap.getKey_maxKey, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_maxKey.h6.der.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t ≠ ∅}, t.maxKey he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeMap.getKey_maxKey.h6.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t ≠ ∅}, t.getKey (t.maxKey he) HypCheckProof.Std.ExtTreeMap.getKey_maxKey.h6.der = t.maxKey he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.ExtTreeMap.getKey_maxKey hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.ExtTreeMap.getKey_maxKey.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.ExtDTreeMap.getKey_maxKey, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_maxKey.h6.der.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t ≠ ∅}, t.maxKey he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.ExtDTreeMap.getKey_maxKey.h6.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t ≠ ∅}, t.getKey (t.maxKey he) HypCheckProof.Std.ExtDTreeMap.getKey_maxKey.h6.der = t.maxKey he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.ExtDTreeMap.getKey_maxKey hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.ExtDTreeMap.getKey_maxKey.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.DTreeMap.getKey_minKey, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.getKey_minKey.h6.der.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t.isEmpty = Bool.false}, t.minKey he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.getKey_minKey.h6.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t.isEmpty = Bool.false}, t.getKey (t.minKey he) HypCheckProof.Std.DTreeMap.getKey_minKey.h6.der = t.minKey he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.DTreeMap.getKey_minKey hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.DTreeMap.getKey_minKey.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.DTreeMap.getKey_maxKey, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DTreeMap.getKey_maxKey.h6.der.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t.isEmpty = Bool.false}, t.maxKey he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.DTreeMap.getKey_maxKey.h6.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t.isEmpty = Bool.false}, t.getKey (t.maxKey he) HypCheckProof.Std.DTreeMap.getKey_maxKey.h6.der = t.maxKey he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.DTreeMap.getKey_maxKey hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.DTreeMap.getKey_maxKey.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.ExtTreeMap.getKey_minKey, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_minKey.h6.der.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t ≠ ∅}, t.minKey he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeMap.getKey_minKey.h6.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t ≠ ∅}, t.getKey (t.minKey he) HypCheckProof.Std.ExtTreeMap.getKey_minKey.h6.der = t.minKey he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.ExtTreeMap.getKey_minKey hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.ExtTreeMap.getKey_minKey.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.ExtDTreeMap.getKey_minKey, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_minKey.h6.der.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t ≠ ∅}, t.minKey he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.ExtDTreeMap.getKey_minKey.h6.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t ≠ ∅}, t.getKey (t.minKey he) HypCheckProof.Std.ExtDTreeMap.getKey_minKey.h6.der = t.minKey he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.ExtDTreeMap.getKey_minKey hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.ExtDTreeMap.getKey_minKey.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.TreeMap.getKey_minKey, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.getKey_minKey.h6.der.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t.isEmpty = Bool.false}, t.minKey he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.getKey_minKey.h6.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
      {he : t.isEmpty = Bool.false}, t.getKey (t.minKey he) HypCheckProof.Std.TreeMap.getKey_minKey.h6.der = t.minKey he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.TreeMap.getKey_minKey hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.TreeMap.getKey_minKey.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.HashSet.Raw.mem_of_get_eq, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.HashSet.Raw.mem_of_get_eq.h7.gneg.{u} : ∀ {α : Type u} {m : Std.HashSet.Raw α} [inst : BEq α] [inst_1 : Hashable α] {k v : α} {w : k ∈ m},
      ¬m.get k w = v → k ∈ m := by
  (intros; omega)
theorem HypCheckProof.Std.HashSet.Raw.mem_of_get_eq.h7.{u} : ∀ {α : Type u} {m : Std.HashSet.Raw α} [inst : BEq α] [inst_1 : Hashable α] {k : α} {v : α} {w : k ∈ m}, k ∈ m := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @Std.HashSet.Raw.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h) (fun hc_hn => @HypCheckProof.Std.HashSet.Raw.mem_of_get_eq.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn)

-- Std.HashSet.mem_of_get_eq, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.HashSet.mem_of_get_eq.h7.gneg.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.HashSet α} {k v : α} {w : k ∈ m}, ¬m.get k w = v → k ∈ m := by
  (intros; omega)
theorem HypCheckProof.Std.HashSet.mem_of_get_eq.h7.{u} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.HashSet α} {k : α} {v : α} {w : k ∈ m}, k ∈ m := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @Std.HashSet.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h) (fun hc_hn => @HypCheckProof.Std.HashSet.mem_of_get_eq.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn)

-- Std.Sat.AIG.relabelNat_unsat_iff, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.relabelNat_unsat_iff.h6.der : ∀ {α : Type} [inst : DecidableEq α] [inst_1 : Hashable α] {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst inst_1}
      {hidx2 : @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst inst_1 aig))},
      @LT.lt Nat instLTNat idx
        (@Array.size (Std.Sat.AIG.Decl Nat)
          (@Std.Sat.AIG.decls Nat instDecidableEqNat instHashableNat (@Std.Sat.AIG.relabelNat α inst inst_1 aig))) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Sat.AIG.relabelNat_unsat_iff.h6 : ∀ {α : Type} [inst : DecidableEq α] [inst_1 : Hashable α] {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst inst_1}
      {hidx2 : @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst inst_1 aig))},
      Iff
        (@Std.Sat.AIG.UnsatAt Nat instHashableNat instDecidableEqNat (@Std.Sat.AIG.relabelNat α inst inst_1 aig) idx invert
          (@HypCheckProof.Std.Sat.AIG.relabelNat_unsat_iff.h6.der α inst inst_1 idx invert aig hidx2))
        (@Std.Sat.AIG.UnsatAt α inst_1 inst aig idx invert hidx2) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Std.Sat.AIG.relabelNat_unsat_iff hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.Sat.AIG.relabelNat_unsat_iff.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x6

-- Std.Sat.AIG.relabelNat_unsat_iff, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.relabelNat_unsat_iff.h7.der : ∀ {α : Type} [inst : DecidableEq α] [inst_1 : Hashable α] {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst inst_1}
      {hidx1 :
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Nat)
            (@Std.Sat.AIG.decls Nat instDecidableEqNat instHashableNat (@Std.Sat.AIG.relabelNat α inst inst_1 aig)))},
      @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst inst_1 aig)) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Sat.AIG.relabelNat_unsat_iff.h7 : ∀ {α : Type} [inst : DecidableEq α] [inst_1 : Hashable α] {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst inst_1}
      {hidx1 :
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Nat)
            (@Std.Sat.AIG.decls Nat instDecidableEqNat instHashableNat (@Std.Sat.AIG.relabelNat α inst inst_1 aig)))},
      Iff
        (@Std.Sat.AIG.UnsatAt Nat instHashableNat instDecidableEqNat (@Std.Sat.AIG.relabelNat α inst inst_1 aig) idx invert
          hidx1)
        (@Std.Sat.AIG.UnsatAt α inst_1 inst aig idx invert
          (@HypCheckProof.Std.Sat.AIG.relabelNat_unsat_iff.h7.der α inst inst_1 idx invert aig hidx1)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Std.Sat.AIG.relabelNat_unsat_iff hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Std.Sat.AIG.relabelNat_unsat_iff.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- Std.Tactic.BVDecide.Reflect.BitVec.append_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.append_congr.h6.inst : ¬1#1 ++ 0#0 = 0#1 ++ 0#0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.append_congr.h6 : ¬∀ (lw rw : Nat) (lhs lhs' : BitVec lw) (rhs rhs' : BitVec rw), rhs' = rhs → lhs' ++ rhs' = lhs ++ rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.append_congr.h6.inst (@hc_h (1) (0) (0#1) (1#1) (0#0) (0#0) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.append_congr, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.append_congr.h7.inst : ¬0#0 ++ 1#1 = 0#0 ++ 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.append_congr.h7 : ¬∀ (lw rw : Nat) (lhs lhs' : BitVec lw) (rhs rhs' : BitVec rw), lhs' = lhs → lhs' ++ rhs' = lhs ++ rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.append_congr.h7.inst (@hc_h (0) (1) (0#0) (0#0) (0#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr.h6.inst : ¬(0#1).sshiftRight' 0#0 = (1#1).sshiftRight' 0#0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr.h6 : ¬∀ (m n : Nat) (lhs : BitVec m) (rhs : BitVec n) (lhs' : BitVec m) (rhs' : BitVec n),
        rhs' = rhs → lhs.sshiftRight' rhs = lhs'.sshiftRight' rhs' := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr.h6.inst (@hc_h (1) (0) (0#1) (0#0) (1#1) (0#0) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr.h7.inst : ¬(1#2).sshiftRight' 0#1 = (1#2).sshiftRight' 1#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr.h7 : ¬∀ (m n : Nat) (lhs : BitVec m) (rhs : BitVec n) (lhs' : BitVec m) (rhs' : BitVec n),
        lhs' = lhs → lhs.sshiftRight' rhs = lhs'.sshiftRight' rhs' := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr.h7.inst (@hc_h (2) (1) (1#2) (0#1) (1#2) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr.h6.inst : ¬0#1 >>> 0#0 = 1#1 >>> 0#0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr.h6 : ¬∀ (m n : Nat) (lhs : BitVec m) (rhs : BitVec n) (lhs' : BitVec m) (rhs' : BitVec n),
        rhs' = rhs → lhs >>> rhs = lhs' >>> rhs' := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr.h6.inst (@hc_h (1) (0) (0#1) (0#0) (1#1) (0#0) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr.h7.inst : ¬1#1 >>> 0#1 = 1#1 >>> 1#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr.h7 : ¬∀ (m n : Nat) (lhs : BitVec m) (rhs : BitVec n) (lhs' : BitVec m) (rhs' : BitVec n),
        lhs' = lhs → lhs >>> rhs = lhs' >>> rhs' := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr.h7.inst (@hc_h (1) (1) (1#1) (0#1) (1#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr.h6.inst : ¬0#1 <<< 0#0 = 1#1 <<< 0#0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr.h6 : ¬∀ (m n : Nat) (lhs : BitVec m) (rhs : BitVec n) (lhs' : BitVec m) (rhs' : BitVec n),
        rhs' = rhs → lhs <<< rhs = lhs' <<< rhs' := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr.h6.inst (@hc_h (1) (0) (0#1) (0#0) (1#1) (0#0) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr.h7.inst : ¬1#1 <<< 0#1 = 1#1 <<< 1#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr.h7 : ¬∀ (m n : Nat) (lhs : BitVec m) (rhs : BitVec n) (lhs' : BitVec m) (rhs' : BitVec n),
        lhs' = lhs → lhs <<< rhs = lhs' <<< rhs' := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr.h7.inst (@hc_h (1) (1) (1#1) (0#1) (1#1) (1#1) rfl)

-- Std.ExtTreeSet.get_min, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeSet.get_min.h5.der.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {he : t ≠ ∅}, t.min he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeSet.get_min.h5.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {he : t ≠ ∅},
      t.get (t.min he) HypCheckProof.Std.ExtTreeSet.get_min.h5.der = t.min he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Std.ExtTreeSet.get_min hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Std.ExtTreeSet.get_min.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Std.ExtTreeSet.get_max, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtTreeSet.get_max.h5.der.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {he : t ≠ ∅}, t.max he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.ExtTreeSet.get_max.h5.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {he : t ≠ ∅},
      t.get (t.max he) HypCheckProof.Std.ExtTreeSet.get_max.h5.der = t.max he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Std.ExtTreeSet.get_max hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Std.ExtTreeSet.get_max.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Std.Internal.List.isEmpty_filter_not_contains_map_fst_left, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.isEmpty_filter_not_contains_map_fst_left.h3.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α],
      ¬EquivBEq α →
        ∀ {l₁ l₂ : List ((a : α) × β a)},
          l₁.isEmpty = Bool.true →
            (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₂).contains p.fst) l₁).isEmpty = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.isEmpty_filter_not_contains_map_fst_left.h3.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l₁ l₂ : List ((a : α) × β a)},
      l₁.isEmpty = Bool.true →
        (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₂).contains p.fst) l₁).isEmpty = Bool.true := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @Std.Internal.List.isEmpty_filter_not_contains_map_fst_left hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.Std.Internal.List.isEmpty_filter_not_contains_map_fst_left.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5 hc_x6)

-- Std.ExtDTreeMap.getKey!_minKey!, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_minKey!.h6.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Inhabited α], ¬t ≠ ∅ → t.getKey! t.minKey! = t.minKey! := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_minKey!.h6.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Inhabited α], t.getKey! t.minKey! = t.minKey! := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact Classical.byCases (fun hc_h => @Std.ExtDTreeMap.getKey!_minKey! hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h) (fun hc_hn => @HypCheckProof.Std.ExtDTreeMap.getKey!_minKey!.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn)

-- Std.TreeSet.get_max, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.get_max.h5.der.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {he : t.isEmpty = Bool.false},
      t.max he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.get_max.h5.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {he : t.isEmpty = Bool.false},
      t.get (t.max he) HypCheckProof.Std.TreeSet.get_max.h5.der = t.max he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Std.TreeSet.get_max hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Std.TreeSet.get_max.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Std.ExtDTreeMap.getKey!_maxKey!, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_maxKey!.h6.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Inhabited α], ¬t ≠ ∅ → t.getKey! t.maxKey! = t.maxKey! := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_maxKey!.h6.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Inhabited α], t.getKey! t.maxKey! = t.maxKey! := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact Classical.byCases (fun hc_h => @Std.ExtDTreeMap.getKey!_maxKey! hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h) (fun hc_hn => @HypCheckProof.Std.ExtDTreeMap.getKey!_maxKey!.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn)

-- Std.TreeSet.Raw.mem_of_get_eq, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.Raw.mem_of_get_eq.h6.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} {k v : α} {w : k ∈ t}, ¬t.get k w = v → k ∈ t := by
  (intros; omega)
theorem HypCheckProof.Std.TreeSet.Raw.mem_of_get_eq.h6.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet.Raw α cmp} {k : α} {v : α} {w : k ∈ t}, k ∈ t := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact Classical.byCases (fun hc_h => @Std.TreeSet.Raw.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h) (fun hc_hn => @HypCheckProof.Std.TreeSet.Raw.mem_of_get_eq.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn)

-- Std.Internal.List.isEmpty_filter_not_contains_left, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.isEmpty_filter_not_contains_left.h3.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α],
      ¬EquivBEq α →
        ∀ {l₁ : List ((a : α) × β a)} {l₂ : List α},
          l₁.isEmpty = Bool.true → (List.filter (fun (p : (a : α) × β a) => !l₂.contains p.fst) l₁).isEmpty = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.isEmpty_filter_not_contains_left.h3.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l₁ : List ((a : α) × β a)} {l₂ : List α},
      l₁.isEmpty = Bool.true → (List.filter (fun (p : (a : α) × β a) => !l₂.contains p.fst) l₁).isEmpty = Bool.true := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @Std.Internal.List.isEmpty_filter_not_contains_left hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.Std.Internal.List.isEmpty_filter_not_contains_left.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5 hc_x6)

-- Std.TreeSet.mem_of_get_eq, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.mem_of_get_eq.h6.gneg.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k v : α} {w : k ∈ t}, ¬t.get k w = v → k ∈ t := by
  (intros; omega)
theorem HypCheckProof.Std.TreeSet.mem_of_get_eq.h6.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α} {v : α} {w : k ∈ t}, k ∈ t := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact Classical.byCases (fun hc_h => @Std.TreeSet.mem_of_get_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h) (fun hc_hn => @HypCheckProof.Std.TreeSet.mem_of_get_eq.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn)

-- Std.TreeSet.get_min, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeSet.get_min.h5.der.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {he : t.isEmpty = Bool.false},
      t.min he ∈ t := by
  (intros; grind)
theorem HypCheckProof.Std.TreeSet.get_min.h5.{u} : ∀ {α : Type u} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {he : t.isEmpty = Bool.false},
      t.get (t.min he) HypCheckProof.Std.TreeSet.get_min.h5.der = t.min he := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Std.TreeSet.get_min hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Std.TreeSet.get_min.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq.h6.der : ∀ {w : Nat}
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (expr : Std.Tactic.BVDecide.BVExpr w) (cache : Std.Tactic.BVDecide.BVExpr.Cache aig) (idx : Nat),
      @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
            (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit aig)) →
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
            (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit
              (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w
                (@Subtype.val
                  (@Std.Sat.AIG.RefVecEntry Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                    Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w)
                  (fun
                      (ref :
                        @Std.Sat.AIG.RefVecEntry Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w) =>
                    @LE.le Nat instLENat
                      (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                        (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit aig))
                      (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                        (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit
                          (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                            Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w ref))))
                  (@Std.Tactic.BVDecide.BVExpr.Return.result aig w
                    (@Std.Tactic.BVDecide.BVExpr.bitblast.go w aig expr cache)))))) := by
  (intros; grind)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq.h6 : ∀ {w : Nat}
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (expr : Std.Tactic.BVDecide.BVExpr w) (cache : Std.Tactic.BVDecide.BVExpr.Cache aig) (idx : Nat)
      (h1 :
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
            (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit aig))),
      @Eq (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
        (@GetElem.getElem (Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) Nat
          (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
          (fun (xs : Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) (i : Nat) =>
            @LT.lt Nat instLTNat i (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit) xs))
          (@Array.instGetElemNatLtSize (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit))
          (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit
            (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w
              (@Subtype.val
                (@Std.Sat.AIG.RefVecEntry Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                  Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w)
                (fun
                    (ref :
                      @Std.Sat.AIG.RefVecEntry Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                        Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w) =>
                  @LE.le Nat instLENat
                    (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                      (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                        Std.Tactic.BVDecide.instHashableBVBit aig))
                    (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                      (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                        Std.Tactic.BVDecide.instHashableBVBit
                        (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w ref))))
                (@Std.Tactic.BVDecide.BVExpr.Return.result aig w
                  (@Std.Tactic.BVDecide.BVExpr.bitblast.go w aig expr cache)))))
          idx (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq.h6.der w aig expr cache idx h1))
        (@GetElem.getElem (Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) Nat
          (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
          (fun (xs : Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) (i : Nat) =>
            @LT.lt Nat instLTNat i (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit) xs))
          (@Array.instGetElemNatLtSize (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit))
          (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit aig)
          idx h1) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq.h6.der : ∀ {w : Nat}
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (expr : Std.Tactic.BVDecide.BVExpr w) (cache : Std.Tactic.BVDecide.BVExpr.Cache aig) (idx : Nat),
      @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
            (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit aig)) →
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
            (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit
              (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w
                (@Subtype.val
                  (@Std.Sat.AIG.RefVecEntry Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                    Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w)
                  (fun
                      (ref :
                        @Std.Sat.AIG.RefVecEntry Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w) =>
                    @LE.le Nat instLENat
                      (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                        (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit aig))
                      (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                        (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit
                          (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                            Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w ref))))
                  (@Std.Tactic.BVDecide.BVExpr.Return.result aig w
                    (@Std.Tactic.BVDecide.BVExpr.bitblast.goCache w aig expr cache)))))) := by
  (intros; grind)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq.h6 : ∀ {w : Nat}
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (expr : Std.Tactic.BVDecide.BVExpr w) (cache : Std.Tactic.BVDecide.BVExpr.Cache aig) (idx : Nat)
      (h1 :
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
            (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit aig))),
      @Eq (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
        (@GetElem.getElem (Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) Nat
          (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
          (fun (xs : Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) (i : Nat) =>
            @LT.lt Nat instLTNat i (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit) xs))
          (@Array.instGetElemNatLtSize (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit))
          (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit
            (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w
              (@Subtype.val
                (@Std.Sat.AIG.RefVecEntry Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                  Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w)
                (fun
                    (ref :
                      @Std.Sat.AIG.RefVecEntry Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                        Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w) =>
                  @LE.le Nat instLENat
                    (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                      (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                        Std.Tactic.BVDecide.instHashableBVBit aig))
                    (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                      (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                        Std.Tactic.BVDecide.instHashableBVBit
                        (@Std.Sat.AIG.RefVecEntry.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit Std.Tactic.BVDecide.instDecidableEqBVBit w ref))))
                (@Std.Tactic.BVDecide.BVExpr.Return.result aig w
                  (@Std.Tactic.BVDecide.BVExpr.bitblast.goCache w aig expr cache)))))
          idx (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq.h6.der w aig expr cache idx h1))
        (@GetElem.getElem (Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) Nat
          (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
          (fun (xs : Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) (i : Nat) =>
            @LT.lt Nat instLTNat i (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit) xs))
          (@Array.instGetElemNatLtSize (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit))
          (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit aig)
          idx h1) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Std.Internal.List.isEmpty_filter_containsKey_right, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.isEmpty_filter_containsKey_right.h3.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α],
      ¬EquivBEq α →
        ∀ {l₁ l₂ : List ((a : α) × β a)},
          l₂.isEmpty = Bool.true →
            (List.filter (fun (p : (a : α) × β a) => Std.Internal.List.containsKey p.fst l₂) l₁).isEmpty = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.isEmpty_filter_containsKey_right.h3.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l₁ l₂ : List ((a : α) × β a)},
      l₂.isEmpty = Bool.true →
        (List.filter (fun (p : (a : α) × β a) => Std.Internal.List.containsKey p.fst l₂) l₁).isEmpty = Bool.true := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @Std.Internal.List.isEmpty_filter_containsKey_right hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.Std.Internal.List.isEmpty_filter_containsKey_right.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5 hc_x6)

-- Std.Tactic.BVDecide.Reflect.BitVec.xor_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.xor_congr.h5.inst : ¬1#1 ^^^ 0#1 = 0#1 ^^^ 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.xor_congr.h5 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), rhs' = rhs → lhs' ^^^ rhs' = lhs ^^^ rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.xor_congr.h5.inst (@hc_h (1) (0#1) (0#1) (1#1) (0#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.xor_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.xor_congr.h6.inst : ¬0#1 ^^^ 1#1 = 0#1 ^^^ 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.xor_congr.h6 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), lhs' = lhs → lhs' ^^^ rhs' = lhs ^^^ rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.xor_congr.h6.inst (@hc_h (1) (0#1) (0#1) (0#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.umod_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.umod_congr.h5.inst : ¬1#1 % 0#1 = 0#1 % 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.umod_congr.h5 : ¬∀ {w : Nat} (lhs rhs lhs' rhs' : BitVec w), rhs' = rhs → lhs' % rhs' = lhs % rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.umod_congr.h5.inst (@hc_h (1) (0#1) (0#1) (1#1) (0#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.umod_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.umod_congr.h6.inst : ¬1#1 % 1#1 = 1#1 % 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.umod_congr.h6 : ¬∀ {w : Nat} (lhs rhs lhs' rhs' : BitVec w), lhs' = lhs → lhs' % rhs' = lhs % rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.umod_congr.h6.inst (@hc_h (1) (1#1) (0#1) (1#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.beq_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.beq_congr.h5.inst : ¬(1#1 == 0#1) = (0#1 == 0#1) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.beq_congr.h5 : ¬∀ {w : Nat} (lhs rhs lhs' rhs' : BitVec w), rhs' = rhs → (lhs' == rhs') = (lhs == rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.beq_congr.h5.inst (@hc_h (1) (0#1) (0#1) (1#1) (0#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.beq_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.beq_congr.h6.inst : ¬(0#1 == 1#1) = (0#1 == 0#1) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.beq_congr.h6 : ¬∀ {w : Nat} (lhs rhs lhs' rhs' : BitVec w), lhs' = lhs → (lhs' == rhs') = (lhs == rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.beq_congr.h6.inst (@hc_h (1) (0#1) (0#1) (0#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.add_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.add_congr.h5.inst : ¬1#1 + 0#1 = 0#1 + 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.add_congr.h5 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), rhs' = rhs → lhs' + rhs' = lhs + rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.add_congr.h5.inst (@hc_h (1) (0#1) (0#1) (1#1) (0#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.add_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.add_congr.h6.inst : ¬0#1 + 1#1 = 0#1 + 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.add_congr.h6 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), lhs' = lhs → lhs' + rhs' = lhs + rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.add_congr.h6.inst (@hc_h (1) (0#1) (0#1) (0#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.ult_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.ult_congr.h5.inst : ¬(1#1).ult 1#1 = (0#1).ult 1#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.ult_congr.h5 : ¬∀ {w : Nat} (lhs rhs lhs' rhs' : BitVec w), rhs' = rhs → lhs'.ult rhs' = lhs.ult rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.ult_congr.h5.inst (@hc_h (1) (0#1) (1#1) (1#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.ult_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.ult_congr.h6.inst : ¬(0#1).ult 1#1 = (0#1).ult 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.ult_congr.h6 : ¬∀ {w : Nat} (lhs rhs lhs' rhs' : BitVec w), lhs' = lhs → lhs'.ult rhs' = lhs.ult rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.ult_congr.h6.inst (@hc_h (1) (0#1) (0#1) (0#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.and_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.and_congr.h5.inst : ¬1#1 &&& 1#1 = 0#1 &&& 1#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.and_congr.h5 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), rhs' = rhs → lhs' &&& rhs' = lhs &&& rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.and_congr.h5.inst (@hc_h (1) (0#1) (1#1) (1#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.and_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.and_congr.h6.inst : ¬1#1 &&& 1#1 = 1#1 &&& 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.and_congr.h6 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), lhs' = lhs → lhs' &&& rhs' = lhs &&& rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.and_congr.h6.inst (@hc_h (1) (1#1) (0#1) (1#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr.h5.inst : ¬1#1 / 1#1 = 0#1 / 1#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr.h5 : ¬∀ {w : Nat} (lhs rhs lhs' rhs' : BitVec w), rhs' = rhs → lhs' / rhs' = lhs / rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr.h5.inst (@hc_h (1) (0#1) (1#1) (1#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr.h6.inst : ¬1#1 / 1#1 = 1#1 / 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr.h6 : ¬∀ {w : Nat} (lhs rhs lhs' rhs' : BitVec w), lhs' = lhs → lhs' / rhs' = lhs / rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr.h6.inst (@hc_h (1) (1#1) (0#1) (1#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.or_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.or_congr.h5.inst : ¬1#1 ||| 0#1 = 0#1 ||| 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.or_congr.h5 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), rhs' = rhs → lhs' ||| rhs' = lhs ||| rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.or_congr.h5.inst (@hc_h (1) (0#1) (0#1) (1#1) (0#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.or_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.or_congr.h6.inst : ¬0#1 ||| 1#1 = 0#1 ||| 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.or_congr.h6 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), lhs' = lhs → lhs' ||| rhs' = lhs ||| rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.or_congr.h6.inst (@hc_h (1) (0#1) (0#1) (0#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.mul_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.mul_congr.h5.inst : ¬1#1 * 1#1 = 0#1 * 1#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.mul_congr.h5 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), rhs' = rhs → lhs' * rhs' = lhs * rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.mul_congr.h5.inst (@hc_h (1) (0#1) (1#1) (1#1) (1#1) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.mul_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.mul_congr.h6.inst : ¬1#1 * 1#1 = 1#1 * 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.mul_congr.h6 : ¬∀ (w : Nat) (lhs rhs lhs' rhs' : BitVec w), lhs' = lhs → lhs' * rhs' = lhs * rhs := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.mul_congr.h6.inst (@hc_h (1) (1#1) (0#1) (1#1) (1#1) rfl)

-- Std.Internal.List.isEmpty_filter_containsKey_left, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.isEmpty_filter_containsKey_left.h3.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α],
      ¬EquivBEq α →
        ∀ {l₁ l₂ : List ((a : α) × β a)},
          l₁.isEmpty = Bool.true →
            (List.filter (fun (p : (a : α) × β a) => Std.Internal.List.containsKey p.fst l₂) l₁).isEmpty = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.isEmpty_filter_containsKey_left.h3.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : BEq α] {l₁ l₂ : List ((a : α) × β a)},
      l₁.isEmpty = Bool.true →
        (List.filter (fun (p : (a : α) × β a) => Std.Internal.List.containsKey p.fst l₂) l₁).isEmpty = Bool.true := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @Std.Internal.List.isEmpty_filter_containsKey_left hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.Std.Internal.List.isEmpty_filter_containsKey_left.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5 hc_x6)

-- Std.HashSet.forIn_eq_forIn, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.HashSet.forIn_eq_forIn.h7.gneg.{u, v, w} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.HashSet α} {δ : Type v} {m' : Type v → Type w} [inst : Monad m'],
      ¬LawfulMonad m' → ∀ {f : α → δ → m' (ForInStep δ)} {init : δ}, ForIn.forIn m init f = ForIn.forIn m init f := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.HashSet.forIn_eq_forIn.h7.{u, v, w} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {m : Std.HashSet α} {δ : Type v} {m' : Type v → Type w} [inst : Monad m']
      {f : α → δ → m' (ForInStep δ)} {init : δ}, ForIn.forIn m init f = ForIn.forIn m init f := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.HashSet.forIn_eq_forIn hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.Std.HashSet.forIn_eq_forIn.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9)

-- Std.TreeMap.Raw.length_keys, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.Raw.length_keys.h4.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp},
      ¬Std.TransCmp cmp → t.WF → t.keys.length = t.size := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.Raw.length_keys.h4.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp}, t.WF → t.keys.length = t.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5
  exact Classical.byCases (fun hc_h => @Std.TreeMap.Raw.length_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5) (fun hc_hn => @HypCheckProof.Std.TreeMap.Raw.length_keys.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5)

-- Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_decl_eq, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_decl_eq.h5.der : ∀
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (expr : Std.Tactic.BVDecide.BVLogicalExpr) (cache : Std.Tactic.BVDecide.BVLogicalExpr.Cache aig) (idx : Nat),
      @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
            (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit aig)) →
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
            (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit
              (@Std.Sat.AIG.Entrypoint.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                Std.Tactic.BVDecide.instHashableBVBit
                (@Subtype.val
                  (@Std.Sat.AIG.Entrypoint Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                    Std.Tactic.BVDecide.instHashableBVBit)
                  (fun
                      (entry :
                        @Std.Sat.AIG.Entrypoint Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit) =>
                    @LE.le Nat instLENat
                      (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                        (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit aig))
                      (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                        (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit
                          (@Std.Sat.AIG.Entrypoint.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                            Std.Tactic.BVDecide.instHashableBVBit entry))))
                  (@Std.Tactic.BVDecide.BVLogicalExpr.Return.result aig
                    (Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache aig expr cache)))))) := by
  (intros; grind)
theorem HypCheckProof.Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_decl_eq.h5 : ∀
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (expr : Std.Tactic.BVDecide.BVLogicalExpr) (cache : Std.Tactic.BVDecide.BVLogicalExpr.Cache aig) (idx : Nat)
      (h1 :
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
            (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit aig))),
      @Eq (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
        (@GetElem.getElem (Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) Nat
          (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
          (fun (xs : Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) (i : Nat) =>
            @LT.lt Nat instLTNat i (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit) xs))
          (@Array.instGetElemNatLtSize (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit))
          (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit
            (@Std.Sat.AIG.Entrypoint.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
              Std.Tactic.BVDecide.instHashableBVBit
              (@Subtype.val
                (@Std.Sat.AIG.Entrypoint Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                  Std.Tactic.BVDecide.instHashableBVBit)
                (fun
                    (entry :
                      @Std.Sat.AIG.Entrypoint Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                        Std.Tactic.BVDecide.instHashableBVBit) =>
                  @LE.le Nat instLENat
                    (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                      (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                        Std.Tactic.BVDecide.instHashableBVBit aig))
                    (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
                      (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                        Std.Tactic.BVDecide.instHashableBVBit
                        (@Std.Sat.AIG.Entrypoint.aig Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
                          Std.Tactic.BVDecide.instHashableBVBit entry))))
                (@Std.Tactic.BVDecide.BVLogicalExpr.Return.result aig
                  (Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache aig expr cache)))))
          idx
          (HypCheckProof.Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_decl_eq.h5.der aig expr cache idx h1))
        (@GetElem.getElem (Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) Nat
          (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
          (fun (xs : Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) (i : Nat) =>
            @LT.lt Nat instLTNat i (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit) xs))
          (@Array.instGetElemNatLtSize (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit))
          (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit aig)
          idx h1) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_decl_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_decl_eq.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt.h4.inst : ¬1#1 / 0#1 = 1#1 >>> 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt.h4.prem0 : 0 < 1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt.h4 : ¬∀ (w : Nat) (x : BitVec w) (n k : Nat), k < w → x / BitVec.ofNat w n = x >>> k := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt.h4.inst (@hc_h (1) (1#1) (0) (0) HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt.h4.prem0)

-- Std.Tactic.BVDecide.Reflect.Bool.and_congr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.and_congr.h4.inst : ¬(Bool.true && Bool.true) = (Bool.false && Bool.true) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.and_congr.h4 : ¬∀ (lhs rhs lhs' rhs' : Bool), rhs' = rhs → (lhs' && rhs') = (lhs && rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.and_congr.h4.inst (@hc_h (Bool.false) (Bool.true) (Bool.true) (Bool.true) rfl)

-- Std.Tactic.BVDecide.Reflect.Bool.and_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.and_congr.h5.inst : ¬(Bool.true && Bool.true) = (Bool.true && Bool.false) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.and_congr.h5 : ¬∀ (lhs rhs lhs' rhs' : Bool), lhs' = lhs → (lhs' && rhs') = (lhs && rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.and_congr.h5.inst (@hc_h (Bool.true) (Bool.false) (Bool.true) (Bool.true) rfl)

-- Lean.Order.le_and, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.le_and.h3.inst : Not (@Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp True (And False True)) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.le_and.h3.prem0 : @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp True True := by
  simp
theorem HypCheckProof.Lean.Order.le_and.h3 : Not
      (∀ (p a b : Prop),
        @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp p b →
          @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp p (And a b)) := fun hc_h => HypCheckProof.Lean.Order.le_and.h3.inst (@hc_h (True) (False) (True) HypCheckProof.Lean.Order.le_and.h3.prem0)

-- Lean.Order.le_and, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.le_and.h4.inst : Not (@Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp True (And True False)) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.le_and.h4.prem0 : @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp True True := by
  simp
theorem HypCheckProof.Lean.Order.le_and.h4 : Not
      (∀ (p a b : Prop),
        @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp p a →
          @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp p (And a b)) := fun hc_h => HypCheckProof.Lean.Order.le_and.h4.inst (@hc_h (True) (True) (False) HypCheckProof.Lean.Order.le_and.h4.prem0)

-- List.eq_of_range'_eq_append_cons, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.eq_of_range'_eq_append_cons.h6.inst : Not
      (@Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@List.length Nat (@List.nil Nat))))) := by
  decide
theorem HypCheckProof.List.eq_of_range'_eq_append_cons.h6 : Not
      (∀ {s : Nat} {n : Nat} {step : Nat} {xs : List Nat} {cur : Nat} {ys : List Nat},
        @Eq Nat cur
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) s
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) step (@List.length Nat xs)))) := fun hc_h => HypCheckProof.List.eq_of_range'_eq_append_cons.h6.inst (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))

-- Std.DHashMap.Raw.Const.get_unitOfList, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.get_unitOfList.h5.inst : Not
      (@Membership.mem Nat (Std.DHashMap.Raw Nat fun (x : Nat) => Unit)
        (@Std.DHashMap.Raw.instMembershipOfBEqOfHashable Nat (fun (x : Nat) => Unit)
          (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat)
        (@Std.DHashMap.Raw.Const.unitOfList Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat
          (@List.nil Nat))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
theorem HypCheckProof.Std.DHashMap.Raw.Const.get_unitOfList.h5 : Not
      (∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] {l : List α} {k : α},
        @Membership.mem α (Std.DHashMap.Raw α fun (x : α) => Unit)
          (@Std.DHashMap.Raw.instMembershipOfBEqOfHashable α (fun (x : α) => Unit) inst inst_1)
          (@Std.DHashMap.Raw.Const.unitOfList α inst inst_1 l) k) := fun hc_h => HypCheckProof.Std.DHashMap.Raw.Const.get_unitOfList.h5.inst (@hc_h (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (instHashableNat) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Std.Tactic.BVDecide.Reflect.BitVec.extract_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.extract_congr.h5.inst : ¬BitVec.extractLsb' 0 1 1#1 = BitVec.extractLsb' 0 1 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.extract_congr.h5 : ¬∀ (start len w : Nat) (x x' : BitVec w), BitVec.extractLsb' start len x' = BitVec.extractLsb' start len x := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.extract_congr.h5.inst (@hc_h (0) (1) (1) (0#1) (1#1))

-- Std.Tactic.BVDecide.Reflect.BitVec.getLsbD_congr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.getLsbD_congr.h4.inst : ¬(1#1).getLsbD 0 = (0#1).getLsbD 0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.getLsbD_congr.h4 : ¬∀ (i w : Nat) (e e' : BitVec w), e'.getLsbD i = e.getLsbD i := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.getLsbD_congr.h4.inst (@hc_h (0) (1) (0#1) (1#1))

-- Std.Tactic.BVDecide.Reflect.BitVec.rotateRight_congr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.rotateRight_congr.h4.inst : ¬(1#1).rotateRight 0 = (0#1).rotateRight 0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.rotateRight_congr.h4 : ¬∀ (n w : Nat) (x x' : BitVec w), x'.rotateRight n = x.rotateRight n := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.rotateRight_congr.h4.inst (@hc_h (0) (1) (0#1) (1#1))

-- Std.TreeMap.length_keys, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.length_keys.h4.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp},
      ¬Std.TransCmp cmp → t.keys.length = t.size := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.length_keys.h4.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp}, t.keys.length = t.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact Classical.byCases (fun hc_h => @Std.TreeMap.length_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_h) (fun hc_hn => @HypCheckProof.Std.TreeMap.length_keys.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn)

-- Std.Internal.List.DistinctKeys.mapUnit, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Internal.List.DistinctKeys.mapUnit.h3.inst : ¬Std.Internal.List.DistinctKeys (List.map (fun (x : Nat) => (⟨x, ()⟩ : (_ : Nat) × Unit)) [0, 0]) := by
  simp
theorem HypCheckProof.Std.Internal.List.DistinctKeys.mapUnit.h3 : ¬∀ {α : Type} [inst : BEq α] {l : List α},
        Std.Internal.List.DistinctKeys (List.map (fun (x : α) => (⟨x, ()⟩ : (_ : α) × Unit)) l) := fun hc_h => HypCheckProof.Std.Internal.List.DistinctKeys.mapUnit.h3.inst (@hc_h (Nat) (instBEqOfDecidableEq) ([0, 0]))

-- Std.Do.SPred.pure_mono, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Do.SPred.pure_mono.h3.inst : Not
      (@Std.Do.SPred.entails (@List.nil Type) (@Std.Do.SPred.pure (@List.nil Type) True)
        (@Std.Do.SPred.pure (@List.nil Type) False)) := by
  simp
theorem HypCheckProof.Std.Do.SPred.pure_mono.h3 : Not (∀ {σs : List Type} {φ₁ φ₂ : Prop}, @Std.Do.SPred.entails σs (@Std.Do.SPred.pure σs φ₁) (@Std.Do.SPred.pure σs φ₂)) := fun hc_h => HypCheckProof.Std.Do.SPred.pure_mono.h3.inst (@hc_h (@List.nil Type) (True) (False))

-- Std.Tactic.BVDecide.Reflect.BitVec.cpop_congr, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.cpop_congr.h3.inst : ¬(1#1).cpop = (0#1).cpop := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.cpop_congr.h3 : ¬∀ (w : Nat) (x x' : BitVec w), x'.cpop = x.cpop := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.cpop_congr.h3.inst (@hc_h (1) (0#1) (1#1))

-- Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false.h1.inst : ¬False := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false.h1 : ¬∀ {x : Bool}, x = Bool.false → False := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false.h1.inst (@hc_h (Bool.false) rfl)

-- Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false.h2.inst : ¬False := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false.h2 : ¬∀ {x : Bool}, x = Bool.true → False := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false.h2.inst (@hc_h (Bool.true) rfl)

-- Std.Tactic.BVDecide.Reflect.BitVec.not_congr, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.not_congr.h3.inst : ¬~~~1#1 = ~~~0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.not_congr.h3 : ¬∀ (w : Nat) (x x' : BitVec w), ~~~x' = ~~~x := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.not_congr.h3.inst (@hc_h (1) (0#1) (1#1))

-- Int.repr_injective, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.repr_injective.h2.inst : Not
      (@Eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) := by
  decide
theorem HypCheckProof.Int.repr_injective.h2 : Not (∀ {a b : Int}, @Eq Int a b) := fun hc_h => HypCheckProof.Int.repr_injective.h2.inst (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Std.Tactic.BVDecide.Reflect.Bool.not_congr, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.not_congr.h2.inst : ¬(!Bool.true) = !Bool.false := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.not_congr.h2 : ¬∀ (x x' : Bool), (!x') = !x := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.not_congr.h2.inst (@hc_h (Bool.false) (Bool.true))

-- Std.Do.SPred.pure_true, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Do.SPred.pure_true.h2.inst : Not
      (@Std.Do.SPred.bientails (@List.nil Type) (@Std.Do.SPred.pure (@List.nil Type) False)
        (@Std.Do.SPred.pure (@List.nil Type) True)) := by
  simp
theorem HypCheckProof.Std.Do.SPred.pure_true.h2 : Not (∀ {σs : List Type} {φ : Prop}, @Std.Do.SPred.bientails σs (@Std.Do.SPred.pure σs φ) (@Std.Do.SPred.pure σs True)) := fun hc_h => HypCheckProof.Std.Do.SPred.pure_true.h2.inst (@hc_h (@List.nil Type) (False))

-- Lean.Order.le_of_right, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.le_of_right.h2.inst : Not (@Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp True False) := by
  simp
theorem HypCheckProof.Lean.Order.le_of_right.h2 : Not (∀ (x y : Prop), @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp x y) := fun hc_h => HypCheckProof.Lean.Order.le_of_right.h2.inst (@hc_h (True) (False))

-- Lean.Order.of_top_le_prop, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.of_top_le_prop.h1.inst : ¬False := by
  decide
theorem HypCheckProof.Lean.Order.of_top_le_prop.h1 : ¬∀ {x : Prop}, x := fun hc_h => HypCheckProof.Lean.Order.of_top_le_prop.h1.inst (@hc_h (False))

-- Std.Do.SPred.down_pure_intro, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Do.SPred.down_pure_intro.h1.inst : Not (@ULift.down Prop (@Std.Do.SPred.pure (@List.nil Type) False)) := by
  simp
theorem HypCheckProof.Std.Do.SPred.down_pure_intro.h1 : Not (∀ {φ : Prop}, @ULift.down Prop (@Std.Do.SPred.pure (@List.nil Type) φ)) := fun hc_h => HypCheckProof.Std.Do.SPred.down_pure_intro.h1.inst (@hc_h (False))

-- Std.Tactic.BVDecide.Normalize.Bool.eq_false_of_not_eq_true, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.Bool.eq_false_of_not_eq_true.h1.inst : ¬Bool.true = Bool.false := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.Bool.eq_false_of_not_eq_true.h1 : ¬∀ {b : Bool}, b = Bool.false := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Normalize.Bool.eq_false_of_not_eq_true.h1.inst (@hc_h (Bool.true))

