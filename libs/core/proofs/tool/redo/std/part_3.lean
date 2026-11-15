import Std

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Std.Sat.AIG.RefVec.zip.denote_go, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.RefVec.zip.denote_go.h7.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {len : Nat} {assign : α → Bool}
      {aig : @Std.Sat.AIG α inst_1 inst} (curr : Nat) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr)
      (lhs rhs : @Std.Sat.AIG.RefVec α inst inst_1 aig len)
      (f :
        (aig : @Std.Sat.AIG α inst_1 inst) →
          @Std.Sat.AIG.BinaryInput α inst inst_1 aig → @Std.Sat.AIG.Entrypoint α inst_1 inst)
      [inst_2 : @Std.Sat.AIG.LawfulOperator α inst inst_1 (@Std.Sat.AIG.BinaryInput α inst inst_1) f]
      [inst : @Std.Sat.AIG.RefVec.LawfulZipOperator α inst inst_1 f inst_2] (idx : Nat),
      @LT.lt Nat instLTNat idx len → @LE.le Nat instLENat curr idx → @LE.le Nat instLENat curr len := by
  (intros; omega)
theorem HypCheckProof.Std.Sat.AIG.RefVec.zip.denote_go.h7 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {len : Nat} {assign : α → Bool}
      {aig : @Std.Sat.AIG α inst_1 inst} (curr : Nat) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr)
      (lhs rhs : @Std.Sat.AIG.RefVec α inst inst_1 aig len)
      (f :
        (aig : @Std.Sat.AIG α inst_1 inst) →
          @Std.Sat.AIG.BinaryInput α inst inst_1 aig → @Std.Sat.AIG.Entrypoint α inst_1 inst)
      [inst_2 : @Std.Sat.AIG.LawfulOperator α inst inst_1 (@Std.Sat.AIG.BinaryInput α inst inst_1) f]
      [inst_3 : @Std.Sat.AIG.RefVec.LawfulZipOperator α inst inst_1 f inst_2] (idx : Nat)
      (hidx1 : @LT.lt Nat instLTNat idx len) (a : @LE.le Nat instLENat curr idx),
      @Eq Bool
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst
            (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 len
              (@Std.Sat.AIG.RefVec.zip.go α inst inst_1 len aig curr s
                (@HypCheckProof.Std.Sat.AIG.RefVec.zip.denote_go.h7.der α inst inst_1 len assign aig curr s lhs rhs f inst_2
                  inst_3 idx hidx1 a)
                lhs rhs f inst_2 inst_3))
            (@Std.Sat.AIG.RefVec.get α inst inst_1
              (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 len
                (@Std.Sat.AIG.RefVec.zip.go α inst inst_1 len aig curr s
                  (@HypCheckProof.Std.Sat.AIG.RefVec.zip.denote_go.h7.der α inst inst_1 len assign aig curr s lhs rhs f
                    inst_2 inst_3 idx hidx1 a)
                  lhs rhs f inst_2 inst_3))
              len
              (@Std.Sat.AIG.RefVecEntry.vec α inst_1 inst inst_1 len
                (@Std.Sat.AIG.RefVec.zip.go α inst inst_1 len aig curr s
                  (@HypCheckProof.Std.Sat.AIG.RefVec.zip.denote_go.h7.der α inst inst_1 len assign aig curr s lhs rhs f
                    inst_2 inst_3 idx hidx1 a)
                  lhs rhs f inst_2 inst_3))
              idx hidx1)))
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (f aig
            (@Std.Sat.AIG.BinaryInput.mk α inst inst_1 aig (@Std.Sat.AIG.RefVec.get α inst inst_1 aig len lhs idx hidx1)
              (@Std.Sat.AIG.RefVec.get α inst inst_1 aig len rhs idx hidx1)))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 hc_x14 hc_x15
  exact @Std.Sat.AIG.RefVec.zip.denote_go hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Std.Sat.AIG.RefVec.zip.denote_go.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 hc_x14 hc_x15) hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 hc_x14 hc_x15

-- Std.Sat.AIG.RefVec.map.denote_go, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.RefVec.map.denote_go.h7.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {len : Nat} {assign : α → Bool}
      {aig : @Std.Sat.AIG α inst_1 inst} (curr : Nat) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr)
      (input : @Std.Sat.AIG.RefVec α inst inst_1 aig len)
      (f : (aig : @Std.Sat.AIG α inst_1 inst) → @Std.Sat.AIG.Ref α inst inst_1 aig → @Std.Sat.AIG.Entrypoint α inst_1 inst)
      [inst_2 : @Std.Sat.AIG.LawfulOperator α inst inst_1 (@Std.Sat.AIG.Ref α inst inst_1) f]
      [inst : @Std.Sat.AIG.RefVec.LawfulMapOperator α inst inst_1 f inst_2] (idx : Nat),
      @LT.lt Nat instLTNat idx len → @LE.le Nat instLENat curr idx → @LE.le Nat instLENat curr len := by
  (intros; omega)
theorem HypCheckProof.Std.Sat.AIG.RefVec.map.denote_go.h7 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {len : Nat} {assign : α → Bool}
      {aig : @Std.Sat.AIG α inst_1 inst} (curr : Nat) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr)
      (input : @Std.Sat.AIG.RefVec α inst inst_1 aig len)
      (f : (aig : @Std.Sat.AIG α inst_1 inst) → @Std.Sat.AIG.Ref α inst inst_1 aig → @Std.Sat.AIG.Entrypoint α inst_1 inst)
      [inst_2 : @Std.Sat.AIG.LawfulOperator α inst inst_1 (@Std.Sat.AIG.Ref α inst inst_1) f]
      [inst_3 : @Std.Sat.AIG.RefVec.LawfulMapOperator α inst inst_1 f inst_2] (idx : Nat)
      (hidx1 : @LT.lt Nat instLTNat idx len) (a : @LE.le Nat instLENat curr idx),
      @Eq Bool
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst
            (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 len
              (@Std.Sat.AIG.RefVec.map.go α inst inst_1 len aig curr
                (@HypCheckProof.Std.Sat.AIG.RefVec.map.denote_go.h7.der α inst inst_1 len assign aig curr s input f inst_2
                  inst_3 idx hidx1 a)
                s input f inst_2 inst_3))
            (@Std.Sat.AIG.RefVec.get α inst inst_1
              (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 len
                (@Std.Sat.AIG.RefVec.map.go α inst inst_1 len aig curr
                  (@HypCheckProof.Std.Sat.AIG.RefVec.map.denote_go.h7.der α inst inst_1 len assign aig curr s input f inst_2
                    inst_3 idx hidx1 a)
                  s input f inst_2 inst_3))
              len
              (@Std.Sat.AIG.RefVecEntry.vec α inst_1 inst inst_1 len
                (@Std.Sat.AIG.RefVec.map.go α inst inst_1 len aig curr
                  (@HypCheckProof.Std.Sat.AIG.RefVec.map.denote_go.h7.der α inst inst_1 len assign aig curr s input f inst_2
                    inst_3 idx hidx1 a)
                  s input f inst_2 inst_3))
              idx hidx1)))
        (@Std.Sat.AIG.denote α inst inst_1 assign (f aig (@Std.Sat.AIG.RefVec.get α inst inst_1 aig len input idx hidx1))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 hc_x14
  exact @Std.Sat.AIG.RefVec.map.denote_go hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Std.Sat.AIG.RefVec.map.denote_go.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 hc_x14) hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 hc_x14

-- Std.DHashMap.Internal.Raw₀.get_insertMany_list_of_mem, hypothesis 14: removable
/- FAILED: 19:50: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 80:12: Application type mismatch: The argument
  α
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.get_insertMany_list_of_mem.h14.der.{u, v} : ∀ {α : Type u} {β : α → Type v} (m : Std.DHashMap.Internal.Raw₀ α β) [inst : BEq α] [inst_1 : Hashable α]
      [inst_2 : LawfulBEq α],
      m.val.WF →
        ∀ {l : List ((a : α) × β a)} {k k' : α},
          (k == k') = Bool.true →
            ∀ {v : β k},
              List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
                (⟨k, v⟩ : (a : α) × β a) ∈ l → (m.insertMany l).val.contains k' = Bool.true := by
  (intros; simp_all <;> grind)
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.get_insertMany_list_of_mem.h14.{u, v} : ∀ {α : Type u} {β : α → Type v} (m : Std.DHashMap.Internal.Raw₀ α β) [inst : BEq α] [inst_1 : Hashable α]
      [inst_2 : LawfulBEq α] (h : m.val.WF) {l : List ((a : α) × β a)} {k k' : α} (k_beq : (k == k') = Bool.true) {v : β k}
      (distinct : List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l)
      (mem : (⟨k, v⟩ : (a : α) × β a) ∈ l),
      (m.insertMany l).val.get k'
          (HypCheckProof.Std.DHashMap.Internal.Raw₀.get_insertMany_list_of_mem.h14.der m h k_beq distinct mem) =
        cast
          ((fun {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
              (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
            k_beq)
          v := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13
  exact @Std.DHashMap.Internal.Raw₀.get_insertMany_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 (@HypCheckProof.Std.DHashMap.Internal.Raw₀.get_insertMany_list_of_mem.h14.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13)
-/

-- Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty, hypothesis 11: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty.h11.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx2 : @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig))},
      Not (Nonempty α) →
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl β)
            (@Std.Sat.AIG.decls β inst_3 inst_2 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj))) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty.h11 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx2 : @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig))}
      (hNonempty : Not (Nonempty α)),
      Iff
        (@Std.Sat.AIG.UnsatAt β inst_2 inst_3 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj) idx invert
          (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty.h11.der α inst inst_1 β inst_2 inst_3 idx invert aig
            r hinj hidx2 hNonempty))
        (@Std.Sat.AIG.UnsatAt α inst inst_1 aig idx invert hidx2) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty.h11.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12) hc_x11 hc_x12

-- Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty, hypothesis 12: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty.h12.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx1 :
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl β)
            (@Std.Sat.AIG.decls β inst_3 inst_2 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj)))},
      Not (Nonempty α) → @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig)) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty.h12 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx1 :
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl β)
            (@Std.Sat.AIG.decls β inst_3 inst_2 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj)))}
      (hNonempty : Not (Nonempty α)),
      Iff
        (@Std.Sat.AIG.UnsatAt β inst_2 inst_3 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj) idx invert
          hidx1)
        (@Std.Sat.AIG.UnsatAt α inst inst_1 aig idx invert
          (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty.h12.der α inst inst_1 β inst_2 inst_3 idx invert aig
            r hinj hidx1 hNonempty)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_not_Nonempty.h12.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12) hc_x12

-- Std.TreeMap.Raw.head?_keys, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.Raw.head?_keys.h7.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α],
      ¬Std.LawfulOrderCmp cmp →
        ∀ [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp],
          t.WF → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.Raw.head?_keys.h7.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderMin α] [inst : Std.LawfulOrderLeftLeaningMin α]
      [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @Std.TreeMap.Raw.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9 hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.Std.TreeMap.Raw.head?_keys.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9 hc_x10 hc_x11)

-- Std.TreeMap.Raw.head?_keys, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.Raw.head?_keys.h8.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp],
      ¬Std.LawfulOrderMin α →
        ∀ [inst : Std.LawfulOrderLeftLeaningMin α] [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.Raw.head?_keys.h8.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderLeftLeaningMin α]
      [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @Std.TreeMap.Raw.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9 hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.Std.TreeMap.Raw.head?_keys.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9 hc_x10 hc_x11)

-- Std.TreeMap.Raw.head?_keys, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.Raw.head?_keys.h9.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α],
      ¬Std.LawfulOrderLeftLeaningMin α → ∀ [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.Raw.head?_keys.h9.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst : Std.LawfulOrderMin α]
      [inst : Std.LawfulEqCmp cmp], t.WF → t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @Std.TreeMap.Raw.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.Std.TreeMap.Raw.head?_keys.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10 hc_x11)

-- Std.TreeMap.Raw.head?_keys, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.Raw.head?_keys.h10.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], ¬Std.LawfulEqCmp cmp → t.WF → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.Raw.head?_keys.h10.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
      [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderCmp cmp] [inst_3 : Std.LawfulOrderMin α]
      [inst : Std.LawfulOrderLeftLeaningMin α], t.WF → t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x11
  exact Classical.byCases (fun hc_h => @Std.TreeMap.Raw.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h hc_x11) (fun hc_hn => @HypCheckProof.Std.TreeMap.Raw.head?_keys.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn hc_x11)

-- Std.DHashMap.Raw.Const.getKey!_unitOfList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey!_unitOfList_of_mem.h11.inst : ¬(Std.DHashMap.Raw.Const.unitOfList []).getKey! 1 = 1 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey!_unitOfList_of_mem.h11.prem0 : (1 == 1) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey!_unitOfList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey!_unitOfList_of_mem.h11 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α]
        [inst_4 : Inhabited α] {l : List α} {k k' : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l → (Std.DHashMap.Raw.Const.unitOfList l).getKey! k' = k := fun hc_h => HypCheckProof.Std.DHashMap.Raw.Const.getKey!_unitOfList_of_mem.h11.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ (instInhabitedNat) ([]) (1) (1) HypCheckProof.Std.DHashMap.Raw.Const.getKey!_unitOfList_of_mem.h11.prem0 HypCheckProof.Std.DHashMap.Raw.Const.getKey!_unitOfList_of_mem.h11.prem1)

-- Std.Internal.List.minKey!_insertEntryIfNew_of_isEmpty, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntryIfNew_of_isEmpty.h10.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      [inst_4 : Inhabited α] {k : α} {v : β k} {l : List ((a : α) × β a)},
      ¬Std.Internal.List.DistinctKeys l →
        l.isEmpty = Bool.true → Std.Internal.List.minKey! (Std.Internal.List.insertEntryIfNew k v l) = k := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntryIfNew_of_isEmpty.h10.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      [inst_4 : Inhabited α] {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → Std.Internal.List.minKey! (Std.Internal.List.insertEntryIfNew k v l) = k := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x11
  exact Classical.byCases (fun hc_h => @Std.Internal.List.minKey!_insertEntryIfNew_of_isEmpty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h hc_x11) (fun hc_hn => @HypCheckProof.Std.Internal.List.minKey!_insertEntryIfNew_of_isEmpty.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn hc_x11)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntryIfNew_of_isEmpty.h10.derivable.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
      [inst : Inhabited α] {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → Std.Internal.List.DistinctKeys l := by
  (intros; simp_all; done)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq, hypothesis 9: removable
/- FAILED: 9:6: expected token | 7:120: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq.h9.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (assign : α → Bool) (curr : Nat) (s : aig.RefVec curr) (idx : Nat),
      idx < w → curr ≤ idx → curr ≤ w := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq.h9 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (assign : α → Bool) (curr : Nat) (s : aig.RefVec curr) (idx : Nat) (hidx1 : idx < w)
      (a : curr ≤ idx),
      ⟦assign,
          { aig := aig,
            ref :=
              (Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go input distance curr
                    (HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq.h9.der aig
                      distance input assign curr s idx hidx1 a)
                    s).get
                idx hidx1 :
            Std.Sat.AIG.Entrypoint α }⟧ =
        if hidx : distance + idx < w then
          ⟦assign, { aig := aig, ref := input.get (distance + idx) hidx : Std.Sat.AIG.Entrypoint α }⟧
        else
          ⟦assign,
            { aig := aig,
              ref :=
                input.get (w - 1)
                  ((fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) =>
                      Decidable.byContradiction fun (a : ¬w - 1 < w) =>
                        (fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) (a : ¬w - 1 < w) =>
                            Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                              (fun (h₁ : 1 ≤ w ∧ ↑(w - 1) = ↑w - ↑1) =>
                                Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                                  (Lean.Omega.Constraint.combine_sat'
                                    (Lean.Omega.tidy_sat
                                      (Lean.Omega.Constraint.addEquality_sat
                                        (Eq.trans
                                          (Eq.symm
                                            (Eq.trans
                                              (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)
                                                (Eq.trans
                                                  (Lean.Omega.Int.sub_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0) (id (Eq.refl ↑1)))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.sub_eval
                                                      { coeffs := [1] : Lean.Omega.LinearCombo }
                                                      { const := 1 : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance, ↑(w - 1)])))))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.sub_eval
                                                  { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                  { const := -1, coeffs := [1] : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance, ↑(w - 1)])))))
                                          (Int.sub_eq_zero_of_eq h₁.right))))
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
                                                (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance, ↑(w - 1)])))))))))
                              fun (h₂ : w < 1 ∧ ↑(w - 1) = 0) =>
                              Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                                (Lean.Omega.Constraint.combine_sat'
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq (Int.natCast_nonneg idx)
                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)))
                                  (Lean.Omega.tidy_sat
                                    (Lean.Omega.combo_sat'
                                      { lowerBound := Option.some 0, upperBound := Option.some 0 : Lean.Omega.Constraint }
                                      { lowerBound := Option.some 1, upperBound := Option.none : Lean.Omega.Constraint }
                                      (-1) [1] 1 [1, 0, -1]
                                      (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance, ↑(w - 1)])
                                      (Lean.Omega.Constraint.combine_sat'
                                        (Lean.Omega.tidy_sat
                                          (Lean.Omega.Constraint.addInequality_sat
                                            (le_of_le_of_eq
                                              (Int.sub_nonneg_of_le
                                                (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂.left)))
                                              (Eq.trans
                                                (Lean.Omega.Int.sub_congr (id (Eq.refl ↑1))
                                                  (Eq.trans
                                                    (Lean.Omega.Int.add_congr
                                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0) (id (Eq.refl 1)))
                                                    (Eq.symm
                                                      (Lean.Omega.LinearCombo.add_eval
                                                        { coeffs := [1] : Lean.Omega.LinearCombo }
                                                        { const := 1 : Lean.Omega.LinearCombo }
                                                        (Lean.Omega.Coeffs.ofList
                                                          [↑w, ↑curr, ↑idx, ↑distance, ↑(w - 1)])))))
                                                (Eq.symm
                                                  (Lean.Omega.LinearCombo.sub_eval { const := 1 : Lean.Omega.LinearCombo }
                                                    { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                                    (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance, ↑(w - 1)])))))))
                                        (Lean.Omega.Constraint.addInequality_sat
                                          (le_of_le_of_eq (Int.natCast_nonneg w)
                                            (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0))))
                                      (Lean.Omega.Constraint.addInequality_sat
                                        (le_of_le_of_eq
                                          (Int.sub_nonneg_of_le
                                            (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt hidx1)))
                                          (Eq.trans
                                            (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                              (Eq.trans
                                                (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                                  (id (Eq.refl 1)))
                                                (Eq.symm
                                                  (Lean.Omega.LinearCombo.add_eval
                                                    { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                    { const := 1 : Lean.Omega.LinearCombo }
                                                    (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance, ↑(w - 1)])))))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                                { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance, ↑(w - 1)]))))))))))
                          distance curr idx hidx1 a)
                    distance curr idx hidx1) :
              Std.Sat.AIG.Entrypoint α }⟧ := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12) hc_x9 hc_x10 hc_x11 hc_x12
-/

-- Std.DHashMap.Raw.Const.getKey?_unitOfList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey?_unitOfList_of_mem.h10.inst : ¬(Std.DHashMap.Raw.Const.unitOfList []).getKey? 0 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey?_unitOfList_of_mem.h10.prem0 : (0 == 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey?_unitOfList_of_mem.h10.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.DHashMap.Raw.Const.getKey?_unitOfList_of_mem.h10 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α] {l : List α}
        {k k' : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l →
            (Std.DHashMap.Raw.Const.unitOfList l).getKey? k' = Option.some k := fun hc_h => HypCheckProof.Std.DHashMap.Raw.Const.getKey?_unitOfList_of_mem.h10.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ ([]) (0) (0) HypCheckProof.Std.DHashMap.Raw.Const.getKey?_unitOfList_of_mem.h10.prem0 HypCheckProof.Std.DHashMap.Raw.Const.getKey?_unitOfList_of_mem.h10.prem1)

-- Std.ExtDTreeMap.head?_keys, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDTreeMap.head?_keys.h7.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α],
      ¬Std.LawfulOrderCmp cmp →
        ∀ [inst_3 : Std.LawfulOrderMin α] [inst_4 : Std.LawfulOrderLeftLeaningMin α] [inst_5 : Std.LawfulEqCmp cmp],
          t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtDTreeMap.head?_keys.h7.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderMin α] [inst_4 : Std.LawfulOrderLeftLeaningMin α]
      [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.ExtDTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.ExtDTreeMap.head?_keys.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8 hc_x9 hc_x10)

-- Std.ExtDTreeMap.head?_keys, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDTreeMap.head?_keys.h8.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp],
      ¬Std.LawfulOrderMin α →
        ∀ [inst_4 : Std.LawfulOrderLeftLeaningMin α] [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtDTreeMap.head?_keys.h8.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderLeftLeaningMin α]
      [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.ExtDTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.ExtDTreeMap.head?_keys.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9 hc_x10)

-- Std.ExtDTreeMap.head?_keys, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDTreeMap.head?_keys.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α],
      ¬Std.LawfulOrderLeftLeaningMin α → ∀ [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtDTreeMap.head?_keys.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α]
      [inst_5 : Std.LawfulEqCmp cmp], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @Std.ExtDTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.Std.ExtDTreeMap.head?_keys.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)

-- Std.ExtDTreeMap.head?_keys, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDTreeMap.head?_keys.h10.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α]
      [inst_5 : Std.LawfulOrderLeftLeaningMin α], ¬Std.LawfulEqCmp cmp → t.keys.head? = t.minKey? := by
  (intros; grind)
theorem HypCheckProof.Std.ExtDTreeMap.head?_keys.h10.{u, v} : ∀ {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
      [inst_1 : Min α] [inst_2 : LE α] [inst_3 : Std.LawfulOrderCmp cmp] [inst_4 : Std.LawfulOrderMin α]
      [inst_5 : Std.LawfulOrderLeftLeaningMin α], t.keys.head? = t.minKey? := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @Std.ExtDTreeMap.head?_keys hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h) (fun hc_hn => @HypCheckProof.Std.ExtDTreeMap.head?_keys.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateRight.go_get, hypothesis 8: removable
/- FAILED: 19:96: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.118 = true) = true
in the application
  id (Eq.refl true) | 6:105: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateRight.go_get.h8.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (curr : Nat) (s : aig.RefVec curr) (idx : Nat), idx < w → curr ≤ idx → curr ≤ w := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateRight.go_get.h8 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (curr : Nat) (s : aig.RefVec curr) (idx : Nat) (hidx1 : idx < w) (a : curr ≤ idx),
      (Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateRight.go input distance curr
              (HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateRight.go_get.h8.der aig distance input curr s
                idx hidx1 a)
              s).get
          idx hidx1 =
        if hidx3 : idx < w - distance % w then
          input.get (distance % w + idx)
            ((fun {w : Nat} (distance curr idx : Nat) (hidx3 : idx < w - distance % w) =>
                Decidable.byContradiction fun (a : ¬distance % w + idx < w) =>
                  (fun {w : Nat} (distance curr idx : Nat) (hidx3 : idx < w - distance % w) (a : ¬distance % w + idx < w) =>
                      Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                        (fun (h₁ : distance % w ≤ w ∧ ↑(w - distance % w) = ↑w - ↑(distance % w)) =>
                          Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                            (Lean.Omega.tidy_sat
                              (Lean.Omega.combo_sat'
                                { lowerBound := Option.some 0, upperBound := Option.none : Lean.Omega.Constraint }
                                { lowerBound := Option.none, upperBound := Option.some (-1) : Lean.Omega.Constraint } 1
                                [0, 0, 1, -1, 0] (-1) [0, 0, 1, -1]
                                (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.combo_sat'
                                    { lowerBound := Option.some 0, upperBound := Option.some 0 : Lean.Omega.Constraint }
                                    { lowerBound := Option.none, upperBound := Option.some 0 : Lean.Omega.Constraint } (-1)
                                    [1, 0, 0, -1, -1] 1 [1, 0, -1, 0, -1]
                                    (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])
                                    (Lean.Omega.tidy_sat
                                      (Lean.Omega.Constraint.addEquality_sat
                                        (Eq.trans
                                          (Eq.symm
                                            (Eq.trans
                                              (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                                (Eq.trans
                                                  (Lean.Omega.Int.sub_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                                    (Eq.trans (Int.natCast_emod distance w)
                                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.sub_eval
                                                      { coeffs := [1] : Lean.Omega.LinearCombo }
                                                      { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList
                                                        [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])))))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.sub_eval
                                                  { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                  { coeffs := [1, 0, 0, 0, -1] : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList
                                                    [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])))))
                                          (Int.sub_eq_zero_of_eq h₁.right))))
                                    (Lean.Omega.tidy_sat
                                      (Lean.Omega.Constraint.addInequality_sat
                                        (le_of_le_of_eq
                                          (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt a)))
                                          (Eq.trans
                                            (Lean.Omega.Int.sub_congr
                                              (Eq.trans (Int.natCast_add (distance % w) idx)
                                                (Eq.trans
                                                  (Lean.Omega.Int.add_congr
                                                    (Eq.trans (Int.natCast_emod distance w)
                                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4))
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.add_eval
                                                      { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                      { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList
                                                        [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])))))
                                              (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.sub_eval
                                                { coeffs := [0, 0, 1, 0, 1] : Lean.Omega.LinearCombo }
                                                { coeffs := [1] : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList
                                                  [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])))))))))
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq
                                      (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt hidx3)))
                                      (Eq.trans
                                        (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                          (Eq.trans
                                            (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                              (id (Eq.refl 1)))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.add_eval
                                                { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                { const := 1 : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList
                                                  [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])))))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.sub_eval
                                            { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                            { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList
                                              [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w]))))))))))
                        fun (h₂ : w < distance % w ∧ ↑(w - distance % w) = 0) =>
                        Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                          (Lean.Omega.tidy_sat
                            (Lean.Omega.combo_sat'
                              { lowerBound := Option.some 0, upperBound := Option.none : Lean.Omega.Constraint }
                              { lowerBound := Option.none, upperBound := Option.some (-1) : Lean.Omega.Constraint } 1
                              [0, 0, 1] (-1) [0, 0, 1, 0]
                              (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])
                              (Lean.Omega.Constraint.addInequality_sat
                                (le_of_le_of_eq (Int.natCast_nonneg idx)
                                  (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)))
                              (Lean.Omega.combo_sat'
                                { lowerBound := Option.some 0, upperBound := Option.some 0 : Lean.Omega.Constraint }
                                { lowerBound := Option.none, upperBound := Option.some (-1) : Lean.Omega.Constraint } 1
                                [0, 0, 0, 1] 1 [0, 0, 1, -1]
                                (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])
                                (Lean.Omega.Constraint.addEquality_sat
                                  (Eq.trans (Eq.symm (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)) h₂.right))
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq
                                      (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt hidx3)))
                                      (Eq.trans
                                        (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                          (Eq.trans
                                            (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                              (id (Eq.refl 1)))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.add_eval
                                                { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                { const := 1 : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList
                                                  [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])))))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.sub_eval
                                            { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                            { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList
                                              [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑distance % ↑w])))))))))))
                    distance curr idx hidx3 a)
              distance curr idx hidx3)
        else
          input.get (idx - (w - distance % w))
            ((fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) (hidx3 : ¬idx < w - distance % w) =>
                Decidable.byContradiction fun (a : ¬idx - (w - distance % w) < w) =>
                  (fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) (hidx3 : ¬idx < w - distance % w)
                        (a : ¬idx - (w - distance % w) < w) =>
                      Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                        (fun (h₁ : w - distance % w ≤ idx ∧ ↑(idx - (w - distance % w)) = ↑idx - ↑(w - distance % w)) =>
                          Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                            (Lean.Omega.Constraint.combine_sat'
                              (Lean.Omega.tidy_sat
                                (Lean.Omega.combo_sat'
                                  { lowerBound := Option.some 0, upperBound := Option.none : Lean.Omega.Constraint }
                                  { lowerBound := Option.some 1, upperBound := Option.none : Lean.Omega.Constraint } (-1)
                                  [0, 0, 0, 1] (-1) [1, 0, 0, -1, -1]
                                  (Lean.Omega.Coeffs.ofList
                                    [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑(idx - (w - distance % w))])
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq (Int.natCast_nonneg (w - distance % w))
                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)))
                                  (Lean.Omega.combo_sat'
                                    { lowerBound := Option.some 0, upperBound := Option.some 0 : Lean.Omega.Constraint }
                                    { lowerBound := Option.some 1, upperBound := Option.none : Lean.Omega.Constraint } 1
                                    [0, 0, 1, -1, -1] 1 [1, 0, -1]
                                    (Lean.Omega.Coeffs.ofList
                                      [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑(idx - (w - distance % w))])
                                    (Lean.Omega.tidy_sat
                                      (Lean.Omega.Constraint.addEquality_sat
                                        (Eq.trans
                                          (Eq.symm
                                            (Eq.trans
                                              (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)
                                                (Eq.trans
                                                  (Lean.Omega.Int.sub_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.sub_eval
                                                      { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                      { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList
                                                        [↑w, ↑curr, ↑idx, ↑(w - distance % w),
                                                          ↑(idx - (w - distance % w))])))))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.sub_eval
                                                  { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                  { coeffs := [0, 0, 1, -1] : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList
                                                    [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑(idx - (w - distance % w))])))))
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
                                                    [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑(idx - (w - distance % w))])))))
                                          (Eq.symm
                                            (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                              { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                              (Lean.Omega.Coeffs.ofList
                                                [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑(idx - (w - distance % w))])))))))))
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
                                            [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑(idx - (w - distance % w))])))))))))
                        fun (h₂ : idx < w - distance % w ∧ ↑(idx - (w - distance % w)) = 0) =>
                        Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                          (Lean.Omega.Constraint.combine_sat'
                            (Lean.Omega.tidy_sat
                              (Lean.Omega.Constraint.addInequality_sat
                                (le_of_le_of_eq
                                  (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂.left)))
                                  (Eq.trans
                                    (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                      (Eq.trans
                                        (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                          (id (Eq.refl 1)))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.add_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                            { const := 1 : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList
                                              [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑(idx - (w - distance % w))])))))
                                    (Eq.symm
                                      (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                        { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList
                                          [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑(idx - (w - distance % w))])))))))
                            (Lean.Omega.Constraint.addInequality_sat
                              (le_of_le_of_eq
                                (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt hidx3)))
                                (Eq.trans
                                  (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3))
                                  (Eq.symm
                                    (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                      { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                      (Lean.Omega.Coeffs.ofList
                                        [↑w, ↑curr, ↑idx, ↑(w - distance % w), ↑(idx - (w - distance % w))]))))))))
                    distance curr idx hidx1 hidx3 a)
              distance curr idx hidx1 hidx3) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateRight.go_get hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateRight.go_get.h8.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11) hc_x8 hc_x9 hc_x10 hc_x11
-/

-- Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_decl_eq, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_decl_eq.h5.der : ∀
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
                    (Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go aig expr cache)))))) := by
  (intros; grind)
theorem HypCheckProof.Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_decl_eq.h5 : ∀
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
                  (Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go aig expr cache)))))
          idx (HypCheckProof.Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_decl_eq.h5.der aig expr cache idx h1))
        (@GetElem.getElem (Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) Nat
          (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
          (fun (xs : Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) (i : Nat) =>
            @LT.lt Nat instLTNat i (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit) xs))
          (@Array.instGetElemNatLtSize (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit))
          (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit aig)
          idx h1) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_decl_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_decl_eq.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Std.Tactic.BVDecide.Reflect.Bool.beq_congr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.beq_congr.h4.inst : ¬(Bool.true == Bool.false) = (Bool.false == Bool.false) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.beq_congr.h4 : ¬∀ (lhs rhs lhs' rhs' : Bool), rhs' = rhs → (lhs' == rhs') = (lhs == rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.beq_congr.h4.inst (@hc_h (Bool.false) (Bool.false) (Bool.true) (Bool.false) rfl)

-- Std.Tactic.BVDecide.Reflect.Bool.beq_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.beq_congr.h5.inst : ¬(Bool.false == Bool.true) = (Bool.false == Bool.false) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.beq_congr.h5 : ¬∀ (lhs rhs lhs' rhs' : Bool), lhs' = lhs → (lhs' == rhs') = (lhs == rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.beq_congr.h5.inst (@hc_h (Bool.false) (Bool.false) (Bool.false) (Bool.true) rfl)

-- Std.Tactic.BVDecide.Reflect.Bool.or_congr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.or_congr.h4.inst : ¬(Bool.true || Bool.false) = (Bool.false || Bool.false) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.or_congr.h4 : ¬∀ (lhs rhs lhs' rhs' : Bool), rhs' = rhs → (lhs' || rhs') = (lhs || rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.or_congr.h4.inst (@hc_h (Bool.false) (Bool.false) (Bool.true) (Bool.false) rfl)

-- Std.Tactic.BVDecide.Reflect.Bool.or_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.or_congr.h5.inst : ¬(Bool.false || Bool.true) = (Bool.false || Bool.false) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.or_congr.h5 : ¬∀ (lhs rhs lhs' rhs' : Bool), lhs' = lhs → (lhs' || rhs') = (lhs || rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.or_congr.h5.inst (@hc_h (Bool.false) (Bool.false) (Bool.false) (Bool.true) rfl)

-- List.length_of_range'_eq_append_cons, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.length_of_range'_eq_append_cons.h6.inst : Not
      (@Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length Nat (@List.nil Nat))
            (@List.length Nat (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.List.length_of_range'_eq_append_cons.h6 : Not
      (∀ {s : Nat} {n : Nat} {step : Nat} {xs : List Nat} {cur : Nat} {ys : List Nat},
        @Eq Nat n
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length Nat xs) (@List.length Nat ys))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => HypCheckProof.List.length_of_range'_eq_append_cons.h6.inst (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))

-- Std.HashMap.Raw.getElem_unitOfList, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getElem_unitOfList.h5.inst : Not
      (@Membership.mem Nat (Std.HashMap.Raw Nat Unit)
        (@Std.HashMap.Raw.instMembershipOfBEqOfHashable Nat Unit (@instBEqOfDecidableEq Nat instDecidableEqNat)
          instHashableNat)
        (@Std.HashMap.Raw.unitOfList Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) instHashableNat (@List.nil Nat))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
theorem HypCheckProof.Std.HashMap.Raw.getElem_unitOfList.h5 : Not
      (∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] {l : List α} {k : α},
        @Membership.mem α (Std.HashMap.Raw α Unit) (@Std.HashMap.Raw.instMembershipOfBEqOfHashable α Unit inst inst_1)
          (@Std.HashMap.Raw.unitOfList α inst inst_1 l) k) := fun hc_h => HypCheckProof.Std.HashMap.Raw.getElem_unitOfList.h5.inst (@hc_h (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (instHashableNat) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Std.DHashMap.Internal.Raw₀.Const.get_insertManyIfNewUnit_emptyWithCapacity_list, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.get_insertManyIfNewUnit_emptyWithCapacity_list.h5.inst : ¬(Std.DHashMap.Internal.Raw₀.Const.insertManyIfNewUnit Std.DHashMap.Internal.Raw₀.emptyWithCapacity []).val.contains 0 =
        Bool.true := by
  decide +kernel
theorem HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.get_insertManyIfNewUnit_emptyWithCapacity_list.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] {l : List α} {k : α},
        (Std.DHashMap.Internal.Raw₀.Const.insertManyIfNewUnit Std.DHashMap.Internal.Raw₀.emptyWithCapacity l).val.contains
            k =
          Bool.true := fun hc_h => HypCheckProof.Std.DHashMap.Internal.Raw₀.Const.get_insertManyIfNewUnit_emptyWithCapacity_list.h5.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) ([]) (0))

-- List.Cursor.pos_mk, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Cursor.pos_mk.h4.inst : ¬[] ++ [0] = [] := by
  decide
theorem HypCheckProof.List.Cursor.pos_mk.h4 : ¬∀ {α : Type} {l pre suff : List α}, pre ++ suff = l := fun hc_h => HypCheckProof.List.Cursor.pos_mk.h4.inst (@hc_h (Nat) ([]) ([]) ([0]))

-- Std.Tactic.BVDecide.BVExpr.eval_replicate, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.eval_replicate.h4.der : ∀ {assign : Std.Tactic.BVDecide.BVExpr.Assignment} {n a : Nat} {expr : Std.Tactic.BVDecide.BVExpr a},
      @Eq Nat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) a n)
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) a n) := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.eval_replicate.h4 : ∀ {assign : Std.Tactic.BVDecide.BVExpr.Assignment} {n a : Nat} {expr : Std.Tactic.BVDecide.BVExpr a},
      @Eq (BitVec (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) a n))
        (@Std.Tactic.BVDecide.BVExpr.eval (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) a n) assign
          (@Std.Tactic.BVDecide.BVExpr.replicate a (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) a n) n expr
            (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.eval_replicate.h4.der assign n a expr)))
        (@BitVec.replicate a n (@Std.Tactic.BVDecide.BVExpr.eval a assign expr)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Std.Tactic.BVDecide.BVExpr.eval_replicate hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.eval_replicate.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRightNat_congr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRightNat_congr.h4.inst : ¬(1#1).sshiftRight 0 = (0#1).sshiftRight 0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRightNat_congr.h4 : ¬∀ (n w : Nat) (x x' : BitVec w), x'.sshiftRight n = x.sshiftRight n := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRightNat_congr.h4.inst (@hc_h (0) (1) (0#1) (1#1))

-- Std.Do.SPred.pure_congr, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Do.SPred.pure_congr.h3.inst : Not
      (@Std.Do.SPred.bientails (@List.nil Type) (@Std.Do.SPred.pure (@List.nil Type) True)
        (@Std.Do.SPred.pure (@List.nil Type) False)) := by
  simp
theorem HypCheckProof.Std.Do.SPred.pure_congr.h3 : Not
      (∀ {σs : List Type} {φ₁ φ₂ : Prop}, @Std.Do.SPred.bientails σs (@Std.Do.SPred.pure σs φ₁) (@Std.Do.SPred.pure σs φ₂)) := fun hc_h => HypCheckProof.Std.Do.SPred.pure_congr.h3.inst (@hc_h (@List.nil Type) (True) (False))

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux2, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux2.h3.inst : ¬0 % 0 < 0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux2.h3 : ¬∀ {a : Nat} {b c : Nat}, b % c < c := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux2.h3.inst (@hc_h (0) (0) (0))

-- Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim.h3.inst : ¬1 ≤ 0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim.h3 : ¬∀ {v : Nat} {x : BitVec v} {w : Nat}, v ≤ w := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim.h3.inst (@hc_h (1) (0#1) (0))

-- Std.Tactic.BVDecide.Reflect.BitVec.clz_congr, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.clz_congr.h3.inst : ¬(1#1).clz = (0#1).clz := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.clz_congr.h3 : ¬∀ (w : Nat) (x x' : BitVec w), x'.clz = x.clz := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.clz_congr.h3.inst (@hc_h (1) (0#1) (1#1))

-- Std.Tactic.BVDecide.Reflect.BitVec.reverse_congr, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.reverse_congr.h3.inst : ¬(1#1).reverse = (0#1).reverse := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.reverse_congr.h3 : ¬∀ (w : Nat) (x x' : BitVec w), x'.reverse = x.reverse := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.reverse_congr.h3.inst (@hc_h (1) (0#1) (1#1))

-- List.Cursor.pos_at, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Cursor.pos_at.h3.inst : Not
      (@Eq Nat
        (@List.Cursor.pos Nat (@List.nil Nat)
          (@List.Cursor.at Nat (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide
theorem HypCheckProof.List.Cursor.pos_at.h3 : Not (∀ {α : Type} {l : List α} {n : Nat}, @Eq Nat (@List.Cursor.pos α l (@List.Cursor.at α l n)) n) := fun hc_h => HypCheckProof.List.Cursor.pos_at.h3.inst (@hc_h (Nat) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

-- Nat.repr_injective, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.repr_injective.h2.inst : ¬0 = 1 := by
  decide
theorem HypCheckProof.Nat.repr_injective.h2 : ¬∀ {m n : Nat}, m = n := fun hc_h => HypCheckProof.Nat.repr_injective.h2.inst (@hc_h (0) (1))

-- Std.Tactic.BVDecide.Normalize.Bool.and_right, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.Bool.and_right.h2.inst : ¬Bool.false = Bool.true := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.Bool.and_right.h2 : ¬∀ (lhs rhs : Bool), rhs = Bool.true := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Normalize.Bool.and_right.h2.inst (@hc_h (Bool.false) (Bool.false))

-- Std.Tactic.BVDecide.Normalize.Bool.and_left, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.Bool.and_left.h2.inst : ¬Bool.false = Bool.true := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.Bool.and_left.h2 : ¬∀ (lhs rhs : Bool), lhs = Bool.true := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Normalize.Bool.and_left.h2.inst (@hc_h (Bool.false) (Bool.false))

-- Std.Tactic.BVDecide.Normalize.BitVec.lt_one_iff, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.lt_one_iff.h2.inst : ¬(0#0).ult 1#0 = (0#0 == 0#0) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.lt_one_iff.h2 : ¬∀ {n : Nat} (a : BitVec n), a.ult 1#n = (a == 0#n) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.lt_one_iff.h2.inst (@hc_h (0) (0#0))

