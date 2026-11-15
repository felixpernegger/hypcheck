import Std

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq.h6.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : @Std.Sat.AIG α inst_1 inst) (curr : Nat)
      (cin : @Std.Sat.AIG.Ref α inst inst_1 aig) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr)
      (lhs rhs : @Std.Sat.AIG.RefVec α inst inst_1 aig w) (assign : α → Bool) (lhsExpr rhsExpr : BitVec w),
      (∀ (idx : Nat) (hidx : @LT.lt Nat instLTNat idx w),
          @Eq Bool
            (@Std.Sat.AIG.denote α inst inst_1 assign
              (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w lhs idx hidx)))
            (@BitVec.getLsbD w lhsExpr idx)) →
        (∀ (idx : Nat) (hidx : @LT.lt Nat instLTNat idx w),
            @Eq Bool
              (@Std.Sat.AIG.denote α inst inst_1 assign
                (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w rhs idx hidx)))
              (@BitVec.getLsbD w rhsExpr idx)) →
          @Eq Bool (@Std.Sat.AIG.denote α inst inst_1 assign (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig cin))
              (@BitVec.carry w curr lhsExpr rhsExpr Bool.false) →
            ∀ (idx : Nat), @LT.lt Nat instLTNat idx w → @LE.le Nat instLENat curr idx → @LE.le Nat instLENat curr w := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq.h6 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : @Std.Sat.AIG α inst_1 inst) (curr : Nat)
      (cin : @Std.Sat.AIG.Ref α inst inst_1 aig) (s : @Std.Sat.AIG.RefVec α inst inst_1 aig curr)
      (lhs rhs : @Std.Sat.AIG.RefVec α inst inst_1 aig w) (assign : α → Bool) (lhsExpr rhsExpr : BitVec w)
      (hleft :
        ∀ (idx : Nat) (hidx : @LT.lt Nat instLTNat idx w),
          @Eq Bool
            (@Std.Sat.AIG.denote α inst inst_1 assign
              (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w lhs idx hidx)))
            (@BitVec.getLsbD w lhsExpr idx))
      (hright :
        ∀ (idx : Nat) (hidx : @LT.lt Nat instLTNat idx w),
          @Eq Bool
            (@Std.Sat.AIG.denote α inst inst_1 assign
              (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w rhs idx hidx)))
            (@BitVec.getLsbD w rhsExpr idx))
      (hcin :
        @Eq Bool (@Std.Sat.AIG.denote α inst inst_1 assign (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig cin))
          (@BitVec.carry w curr lhsExpr rhsExpr Bool.false))
      (idx : Nat) (hidx1 : @LT.lt Nat instLTNat idx w) (a : @LE.le Nat instLENat curr idx),
      @Eq Bool
        (@Std.Sat.AIG.denote α inst inst_1 assign
          (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst
            (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 w
              (@Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go α inst inst_1 w aig lhs rhs curr
                (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq.h6.der α inst inst_1 w aig curr
                  cin s lhs rhs assign lhsExpr rhsExpr hleft hright hcin idx hidx1 a)
                cin s))
            (@Std.Sat.AIG.RefVec.get α inst inst_1
              (@Std.Sat.AIG.RefVecEntry.aig α inst_1 inst inst_1 w
                (@Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go α inst inst_1 w aig lhs rhs curr
                  (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq.h6.der α inst inst_1 w aig curr
                    cin s lhs rhs assign lhsExpr rhsExpr hleft hright hcin idx hidx1 a)
                  cin s))
              w
              (@Std.Sat.AIG.RefVecEntry.vec α inst_1 inst inst_1 w
                (@Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go α inst inst_1 w aig lhs rhs curr
                  (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq.h6.der α inst inst_1 w aig curr
                    cin s lhs rhs assign lhsExpr rhsExpr hleft hright hcin idx hidx1 a)
                  cin s))
              idx hidx1)))
        ((@Std.Sat.AIG.denote α inst inst_1 assign
              (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig
                (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w lhs idx hidx1))).xor
          ((@Std.Sat.AIG.denote α inst inst_1 assign
                (@Std.Sat.AIG.Entrypoint.mk α inst_1 inst aig
                  (@Std.Sat.AIG.RefVec.get α inst inst_1 aig w rhs idx hidx1))).xor
            (@BitVec.carry w idx lhsExpr rhsExpr Bool.false))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 hc_x14 hc_x15 hc_x16 hc_x17 hc_x18
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 hc_x14 hc_x15 hc_x16 hc_x17 hc_x18) hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 hc_x14 hc_x15 hc_x16 hc_x17 hc_x18

-- Std.DHashMap.Raw.get_insertMany_list_of_mem, hypothesis 14: removable
/- FAILED: 17:50: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 54:12: Application type mismatch: The argument
  α
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.Raw.get_insertMany_list_of_mem.h14.der.{u, v} : ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulBEq α],
      m.WF →
        ∀ {l : List ((a : α) × β a)} {k k' : α},
          (k == k') = Bool.true →
            ∀ {v : β k},
              List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
                (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ m.insertMany l := by
  (intros; grind)
theorem HypCheckProof.Std.DHashMap.Raw.get_insertMany_list_of_mem.h14.{u, v} : ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulBEq α]
      (h : m.WF) {l : List ((a : α) × β a)} {k k' : α} (k_beq : (k == k') = Bool.true) {v : β k}
      (distinct : List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l)
      (mem : (⟨k, v⟩ : (a : α) × β a) ∈ l),
      (m.insertMany l).get k' (HypCheckProof.Std.DHashMap.Raw.get_insertMany_list_of_mem.h14.der h k_beq distinct mem) =
        cast
          ((fun {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
              (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
            k_beq)
          v := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13
  exact @Std.DHashMap.Raw.get_insertMany_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13 (@HypCheckProof.Std.DHashMap.Raw.get_insertMany_list_of_mem.h14.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13)
-/

-- Std.ExtDHashMap.get_ofList_of_mem, hypothesis 12: removable
/- FAILED: 16:50: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 38:12: Application type mismatch: The argument
  α
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {x} {β} [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDHashMap.get_ofList_of_mem.h12.der.{u, v} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} [inst : LawfulBEq α] {l : List ((a : α) × β a)}
      {k k' : α},
      (k == k') = Bool.true →
        ∀ {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ Std.ExtDHashMap.ofList l := by
  (intros; grind)
theorem HypCheckProof.Std.ExtDHashMap.get_ofList_of_mem.h12.{u, v} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} [inst : LawfulBEq α] {l : List ((a : α) × β a)}
      {k k' : α} (k_beq : (k == k') = Bool.true) {v : β k}
      (distinct : List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l)
      (mem : (⟨k, v⟩ : (a : α) × β a) ∈ l),
      (Std.ExtDHashMap.ofList l).get k' (HypCheckProof.Std.ExtDHashMap.get_ofList_of_mem.h12.der k_beq distinct mem) =
        cast
          ((fun {α : Type u} {x : BEq α} {β : α → Type v} [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
              (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
            k_beq)
          v := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Std.ExtDHashMap.get_ofList_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 (@HypCheckProof.Std.ExtDHashMap.get_ofList_of_mem.h12.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11)
-/

-- Std.Sat.AIG.relabel_unsat_iff_of_Nonempty, hypothesis 12: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_Nonempty.h12.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} [inst_4 : Nonempty α] {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx2 : @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig))},
      @LT.lt Nat instLTNat idx
        (@Array.size (Std.Sat.AIG.Decl β)
          (@Std.Sat.AIG.decls β inst_3 inst_2 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj))) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_Nonempty.h12 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} [inst_4 : Nonempty α] {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx2 : @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig))},
      Iff
        (@Std.Sat.AIG.UnsatAt β inst_2 inst_3 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj) idx invert
          (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_Nonempty.h12.der α inst inst_1 β inst_2 inst_3 idx invert inst_4
            aig r hinj hidx2))
        (@Std.Sat.AIG.UnsatAt α inst inst_1 aig idx invert hidx2) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.Sat.AIG.relabel_unsat_iff_of_Nonempty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_Nonempty.h12.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12) hc_x12

-- Std.Sat.AIG.relabel_unsat_iff_of_Nonempty, hypothesis 13: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_Nonempty.h13.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} [inst_4 : Nonempty α] {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx1 :
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl β)
            (@Std.Sat.AIG.decls β inst_3 inst_2 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj)))},
      @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig)) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_Nonempty.h13 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} [inst_4 : Nonempty α] {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx1 :
        @LT.lt Nat instLTNat idx
          (@Array.size (Std.Sat.AIG.Decl β)
            (@Std.Sat.AIG.decls β inst_3 inst_2 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj)))},
      Iff
        (@Std.Sat.AIG.UnsatAt β inst_2 inst_3 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj) idx invert
          hidx1)
        (@Std.Sat.AIG.UnsatAt α inst inst_1 aig idx invert
          (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_Nonempty.h13.der α inst inst_1 β inst_2 inst_3 idx invert inst_4
            aig r hinj hidx1)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.Sat.AIG.relabel_unsat_iff_of_Nonempty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff_of_Nonempty.h13.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12)

-- Std.HashSet.Raw.get!_ofList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashSet.Raw.get!_ofList_of_mem.h11.inst : ¬(Std.HashSet.Raw.ofList []).get! 1 = 1 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashSet.Raw.get!_ofList_of_mem.h11.prem0 : (1 == 1) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashSet.Raw.get!_ofList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.HashSet.Raw.get!_ofList_of_mem.h11 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α]
        [inst_4 : Inhabited α] {l : List α} {k k' : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l → (Std.HashSet.Raw.ofList l).get! k' = k := fun hc_h => HypCheckProof.Std.HashSet.Raw.get!_ofList_of_mem.h11.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ (instInhabitedNat) ([]) (1) (1) HypCheckProof.Std.HashSet.Raw.get!_ofList_of_mem.h11.prem0 HypCheckProof.Std.HashSet.Raw.get!_ofList_of_mem.h11.prem1)

-- Std.HashMap.Raw.getKeyD_unitOfList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getKeyD_unitOfList_of_mem.h11.inst : ¬(Std.HashMap.Raw.unitOfList []).getKeyD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getKeyD_unitOfList_of_mem.h11.prem0 : (0 == 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getKeyD_unitOfList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.HashMap.Raw.getKeyD_unitOfList_of_mem.h11 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α] {l : List α}
        {k k' fallback : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l → (Std.HashMap.Raw.unitOfList l).getKeyD k' fallback = k := fun hc_h => HypCheckProof.Std.HashMap.Raw.getKeyD_unitOfList_of_mem.h11.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ ([]) (0) (0) (1) HypCheckProof.Std.HashMap.Raw.getKeyD_unitOfList_of_mem.h11.prem0 HypCheckProof.Std.HashMap.Raw.getKeyD_unitOfList_of_mem.h11.prem1)

-- Std.Internal.List.minKey!_insertEntry_of_isEmpty, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntry_of_isEmpty.h10.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      [inst_4 : Inhabited α] {k : α} {v : β k} {l : List ((a : α) × β a)},
      ¬Std.Internal.List.DistinctKeys l →
        l.isEmpty = Bool.true → Std.Internal.List.minKey! (Std.Internal.List.insertEntry k v l) = k := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntry_of_isEmpty.h10.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      [inst_4 : Inhabited α] {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → Std.Internal.List.minKey! (Std.Internal.List.insertEntry k v l) = k := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x11
  exact Classical.byCases (fun hc_h => @Std.Internal.List.minKey!_insertEntry_of_isEmpty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h hc_x11) (fun hc_hn => @HypCheckProof.Std.Internal.List.minKey!_insertEntry_of_isEmpty.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn hc_x11)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntry_of_isEmpty.h10.derivable.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
      [inst : Inhabited α] {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → Std.Internal.List.DistinctKeys l := by
  (intros; simp_all; done)

-- Std.Internal.List.minKeyD_insertEntryIfNew_of_isEmpty, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntryIfNew_of_isEmpty.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      ¬Std.Internal.List.DistinctKeys l →
        l.isEmpty = Bool.true →
          ∀ {fallback : α}, Std.Internal.List.minKeyD (Std.Internal.List.insertEntryIfNew k v l) fallback = k := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntryIfNew_of_isEmpty.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true →
        ∀ {fallback : α}, Std.Internal.List.minKeyD (Std.Internal.List.insertEntryIfNew k v l) fallback = k := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @Std.Internal.List.minKeyD_insertEntryIfNew_of_isEmpty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.Std.Internal.List.minKeyD_insertEntryIfNew_of_isEmpty.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10 hc_x11)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntryIfNew_of_isEmpty.h9.derivable.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → ∀ {fallback : α}, Std.Internal.List.DistinctKeys l := by
  (intros; simp_all; done)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastExtract.go_get, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastExtract.go_get.h9.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w newWidth : Nat} (aig : Std.Sat.AIG α)
      (input : aig.RefVec w) (lo curr : Nat) (s : aig.RefVec curr) (idx : Nat),
      idx < newWidth → curr ≤ idx → curr ≤ newWidth := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastExtract.go_get.h9 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w newWidth : Nat} (aig : Std.Sat.AIG α)
      (input : aig.RefVec w) (lo curr : Nat) (s : aig.RefVec curr) (idx : Nat) (hidx1 : idx < newWidth) (a : curr ≤ idx),
      (Std.Tactic.BVDecide.BVExpr.bitblast.blastExtract.go input lo curr
              (HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastExtract.go_get.h9.der aig input lo curr s idx hidx1 a)
              s).get
          idx hidx1 =
        input.getD (lo + idx) (aig.mkConstCached Bool.false) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastExtract.go_get hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastExtract.go_get.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12) hc_x9 hc_x10 hc_x11 hc_x12

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq, hypothesis 9: removable
/- FAILED: 9:6: expected token | 7:114: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq.h9.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (assign : α → Bool) (curr : Nat) (s : aig.RefVec curr) (idx : Nat),
      idx < w → curr ≤ idx → curr ≤ w := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq.h9 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (assign : α → Bool) (curr : Nat) (s : aig.RefVec curr) (idx : Nat) (hidx1 : idx < w)
      (a : curr ≤ idx),
      ⟦assign,
          {
            aig :=
              (Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go aig input distance curr
                  (HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq.h9.der aig distance
                    input assign curr s idx hidx1 a)
                  s).aig,
            ref :=
              (Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go aig input distance curr
                      (HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq.h9.der aig
                        distance input assign curr s idx hidx1 a)
                      s).vec.get
                idx hidx1 :
            Std.Sat.AIG.Entrypoint α }⟧ =
        if hidx : idx < distance then Bool.false
        else
          ⟦assign,
            { aig := aig,
              ref :=
                input.get (idx - distance)
                  ((fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) (hidx : ¬idx < distance) =>
                      Decidable.byContradiction fun (a : ¬idx - distance < w) =>
                        (fun {w : Nat} (distance curr idx : Nat) (hidx1 : idx < w) (hidx : ¬idx < distance)
                              (a : ¬idx - distance < w) =>
                            Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                              (fun (h₁ : distance ≤ idx ∧ ↑(idx - distance) = ↑idx - ↑distance) =>
                                Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                                  (Lean.Omega.Constraint.combine_sat'
                                    (Lean.Omega.tidy_sat
                                      (Lean.Omega.combo_sat'
                                        { lowerBound := Option.some 0, upperBound := Option.none : Lean.Omega.Constraint }
                                        { lowerBound := Option.some 1, upperBound := Option.none : Lean.Omega.Constraint }
                                        (-1) [0, 0, 0, 1] (-1) [1, 0, 0, -1, -1]
                                        (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)])
                                        (Lean.Omega.Constraint.addInequality_sat
                                          (le_of_le_of_eq (Int.natCast_nonneg distance)
                                            (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)))
                                        (Lean.Omega.combo_sat'
                                          { lowerBound := Option.some 0, upperBound := Option.some 0 :
                                            Lean.Omega.Constraint }
                                          { lowerBound := Option.some 1, upperBound := Option.none : Lean.Omega.Constraint }
                                          1 [0, 0, 1, -1, -1] 1 [1, 0, -1]
                                          (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)])
                                          (Lean.Omega.tidy_sat
                                            (Lean.Omega.Constraint.addEquality_sat
                                              (Eq.trans
                                                (Eq.symm
                                                  (Eq.trans
                                                    (Lean.Omega.Int.sub_congr
                                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_4)
                                                      (Eq.trans
                                                        (Lean.Omega.Int.sub_congr
                                                          (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                                          (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3))
                                                        (Eq.symm
                                                          (Lean.Omega.LinearCombo.sub_eval
                                                            { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                            { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                            (Lean.Omega.Coeffs.ofList
                                                              [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)])))))
                                                    (Eq.symm
                                                      (Lean.Omega.LinearCombo.sub_eval
                                                        { coeffs := [0, 0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                        { coeffs := [0, 0, 1, -1] : Lean.Omega.LinearCombo }
                                                        (Lean.Omega.Coeffs.ofList
                                                          [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)])))))
                                                (Int.sub_eq_zero_of_eq h₁.right))))
                                          (Lean.Omega.Constraint.addInequality_sat
                                            (le_of_le_of_eq
                                              (Int.sub_nonneg_of_le
                                                (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt hidx1)))
                                              (Eq.trans
                                                (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                                  (Eq.trans
                                                    (Lean.Omega.Int.add_congr
                                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2) (id (Eq.refl 1)))
                                                    (Eq.symm
                                                      (Lean.Omega.LinearCombo.add_eval
                                                        { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                        { const := 1 : Lean.Omega.LinearCombo }
                                                        (Lean.Omega.Coeffs.ofList
                                                          [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)])))))
                                                (Eq.symm
                                                  (Lean.Omega.LinearCombo.sub_eval
                                                    { coeffs := [1] : Lean.Omega.LinearCombo }
                                                    { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                    (Lean.Omega.Coeffs.ofList
                                                      [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)])))))))))
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
                                                  [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)])))))))))
                              fun (h₂ : idx < distance ∧ ↑(idx - distance) = 0) =>
                              Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                                (Lean.Omega.Constraint.combine_sat'
                                  (Lean.Omega.tidy_sat
                                    (Lean.Omega.Constraint.addInequality_sat
                                      (le_of_le_of_eq
                                        (Int.sub_nonneg_of_le
                                          (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂.left)))
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
                                                    [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)])))))
                                          (Eq.symm
                                            (Lean.Omega.LinearCombo.sub_eval
                                              { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                              { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                              (Lean.Omega.Coeffs.ofList
                                                [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)])))))))
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq
                                      (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt hidx)))
                                      (Eq.trans
                                        (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                          (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                            { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList
                                              [↑w, ↑curr, ↑idx, ↑distance, ↑(idx - distance)]))))))))
                          distance curr idx hidx1 hidx a)
                    distance curr idx hidx1 hidx) :
              Std.Sat.AIG.Entrypoint α }⟧ := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12) hc_x9 hc_x10 hc_x11 hc_x12
-/

-- Std.HashMap.Raw.getKey?_unitOfList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getKey?_unitOfList_of_mem.h10.inst : ¬(Std.HashMap.Raw.unitOfList []).getKey? 0 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getKey?_unitOfList_of_mem.h10.prem0 : (0 == 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.HashMap.Raw.getKey?_unitOfList_of_mem.h10.prem1 : List.Pairwise (fun (a b : Nat) => (a == b) = Bool.false) [] := by
  decide
theorem HypCheckProof.Std.HashMap.Raw.getKey?_unitOfList_of_mem.h10 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : EquivBEq α] [inst_3 : LawfulHashable α] {l : List α}
        {k k' : α},
        (k == k') = Bool.true →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) l →
            (Std.HashMap.Raw.unitOfList l).getKey? k' = Option.some k := fun hc_h => HypCheckProof.Std.HashMap.Raw.getKey?_unitOfList_of_mem.h10.inst (@hc_h (Nat) (instBEqOfDecidableEq) (instHashableNat) _ _ ([]) (0) (0) HypCheckProof.Std.HashMap.Raw.getKey?_unitOfList_of_mem.h10.prem0 HypCheckProof.Std.HashMap.Raw.getKey?_unitOfList_of_mem.h10.prem1)

-- Std.HashMap.Raw.getKey_insertManyIfNewUnit_list_of_mem, hypothesis 10: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.HashMap.Raw.getKey_insertManyIfNewUnit_list_of_mem.h10.der.{u} : ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {m : Std.HashMap.Raw α Unit} [inst_2 : EquivBEq α]
      [inst_3 : LawfulHashable α], m.WF → ∀ {l : List α} {k : α}, k ∈ m → k ∈ m.insertManyIfNewUnit l := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.HashMap.Raw.getKey_insertManyIfNewUnit_list_of_mem.h10.{u} : ∀ {α : Type u} [inst : BEq α] [inst_1 : Hashable α] {m : Std.HashMap.Raw α Unit} [inst_2 : EquivBEq α]
      [inst_3 : LawfulHashable α] (h : m.WF) {l : List α} {k : α} (mem : k ∈ m),
      (m.insertManyIfNewUnit l).getKey k
          (HypCheckProof.Std.HashMap.Raw.getKey_insertManyIfNewUnit_list_of_mem.h10.der h mem) =
        m.getKey k mem := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact @Std.HashMap.Raw.getKey_insertManyIfNewUnit_list_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 (@HypCheckProof.Std.HashMap.Raw.getKey_insertManyIfNewUnit_list_of_mem.h10.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9)

-- Std.Sat.AIG.relabel_unsat_iff, hypothesis 11: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff.h11.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx2 : @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig))},
      @LT.lt Nat instLTNat idx
        (@Array.size (Std.Sat.AIG.Decl β)
          (@Std.Sat.AIG.decls β inst_3 inst_2 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj))) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff.h11 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
      {idx : Nat} {invert : Bool} {aig : @Std.Sat.AIG α inst_1 inst} {r : α → β}
      {hinj :
        ∀ (x y : α),
          @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig x →
            @Membership.mem α (@Std.Sat.AIG α inst_1 inst) (@Std.Sat.AIG.instMembership α inst inst_1) aig y →
              @Eq β (r x) (r y) → @Eq α x y}
      {hidx2 : @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig))},
      Iff
        (@Std.Sat.AIG.UnsatAt β inst_2 inst_3 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj) idx invert
          (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff.h11.der α inst inst_1 β inst_2 inst_3 idx invert aig r hinj hidx2))
        (@Std.Sat.AIG.UnsatAt α inst inst_1 aig idx invert hidx2) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Std.Sat.AIG.relabel_unsat_iff hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff.h11.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11) hc_x11

-- Std.Sat.AIG.relabel_unsat_iff, hypothesis 12: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff.h12.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
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
      @LT.lt Nat instLTNat idx (@Array.size (Std.Sat.AIG.Decl α) (@Std.Sat.AIG.decls α inst_1 inst aig)) := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Sat.AIG.relabel_unsat_iff.h12 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {β : Type} [inst_2 : Hashable β] [inst_3 : DecidableEq β]
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
      Iff
        (@Std.Sat.AIG.UnsatAt β inst_2 inst_3 (@Std.Sat.AIG.relabel α inst inst_1 β inst_2 inst_3 r aig hinj) idx invert
          hidx1)
        (@Std.Sat.AIG.UnsatAt α inst inst_1 aig idx invert
          (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff.h12.der α inst inst_1 β inst_2 inst_3 idx invert aig r hinj hidx1)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Std.Sat.AIG.relabel_unsat_iff hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 (@HypCheckProof.Std.Sat.AIG.relabel_unsat_iff.h12.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11)

-- Std.Internal.List.minKey_insertEntryIfNew_of_isEmpty, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey_insertEntryIfNew_of_isEmpty.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      ¬Std.Internal.List.DistinctKeys l →
        l.isEmpty = Bool.true →
          Std.Internal.List.minKey (Std.Internal.List.insertEntryIfNew k v l) Std.Internal.List.isEmpty_insertEntryIfNew = k := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.minKey_insertEntryIfNew_of_isEmpty.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true →
        Std.Internal.List.minKey (Std.Internal.List.insertEntryIfNew k v l) Std.Internal.List.isEmpty_insertEntryIfNew = k := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @Std.Internal.List.minKey_insertEntryIfNew_of_isEmpty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.Std.Internal.List.minKey_insertEntryIfNew_of_isEmpty.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey_insertEntryIfNew_of_isEmpty.h9.derivable.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)}, l.isEmpty = Bool.true → Std.Internal.List.DistinctKeys l := by
  (intros; simp_all; done)

-- Std.Rio.length_iter, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Rio.length_iter.h6.gneg.{u_1} : ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : DecidableLT α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α],
      ¬Std.Rxo.IsAlwaysFinite α →
        ∀ [inst_5 : Std.PRange.LawfulUpwardEnumerable α] [inst_6 : Std.Rxo.HasSize α] [inst_7 : Std.Rxo.LawfulHasSize α]
          {r : Std.Rio α}, r.iter.length = r.size := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Rio.length_iter.h6.{u_1} : ∀ {α : Type u_1} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : DecidableLT α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] [inst_6 : Std.Rxo.HasSize α] [inst_7 : Std.Rxo.LawfulHasSize α]
      {r : Std.Rio α}, r.iter.length = r.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x7 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @Std.Rio.length_iter hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h hc_x7 hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.Std.Rio.length_iter.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn hc_x7 hc_x8 hc_x9 hc_x10)

-- Std.Internal.List.minKey?_insertEntry_of_isEmpty, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_of_isEmpty.h9.gneg.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      ¬Std.Internal.List.DistinctKeys l →
        l.isEmpty = Bool.true → Std.Internal.List.minKey? (Std.Internal.List.insertEntry k v l) = Option.some k := by
  (intros; simp_all; done)
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_of_isEmpty.h9.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)},
      l.isEmpty = Bool.true → Std.Internal.List.minKey? (Std.Internal.List.insertEntry k v l) = Option.some k := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @Std.Internal.List.minKey?_insertEntry_of_isEmpty hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.Std.Internal.List.minKey?_insertEntry_of_isEmpty.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_of_isEmpty.h9.derivable.{u, v} : ∀ {α : Type u} {β : α → Type v} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
      {k : α} {v : β k} {l : List ((a : α) × β a)}, l.isEmpty = Bool.true → Std.Internal.List.DistinctKeys l := by
  (intros; simp_all; done)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux, hypothesis 11: removable
/- FAILED: 13:90: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.37 = true) = true
in the application
  id (Eq.refl true) | 987:18: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  Std.Sat.AIG ?m.41
of sort `Type` in the application
  (fun {α} [Hashable α] [DecidableEq α] {w} aig curr hcurr idx hidx a =>
      Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl true)))
        (Lean.Omega.Constraint.combine_sat'
          (Lean.Omega.tidy_sat
            (Lean.Omega.combo_sat' { lowerBound := some 0, upperBound := none }
              { low
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux.h11.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (c : BitVec w) (curr : Nat),
      curr ≤ w → ∀ (s : aig.RefVec curr) (idx : Nat), idx < curr → aig.decls.size ≤ aig.decls.size := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux.h11 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (c : BitVec w) (curr : Nat)
      (hcurr : curr ≤ w) (s : aig.RefVec curr) (idx : Nat) (hidx : idx < curr),
      (Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go aig c curr s hcurr).get idx
          ((fun {α : Type} [Hashable α] [DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (curr : Nat) (hcurr : curr ≤ w)
                (idx : Nat) (hidx : idx < curr) =>
              Decidable.byContradiction fun (a : ¬idx < w) =>
                (fun {α : Type} [Hashable α] [DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (curr : Nat) (hcurr : curr ≤ w)
                      (idx : Nat) (hidx : idx < curr) (a : ¬idx < w) =>
                    Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                      (Lean.Omega.Constraint.combine_sat'
                        (Lean.Omega.tidy_sat
                          (Lean.Omega.combo_sat'
                            { lowerBound := Option.some 0, upperBound := Option.none : Lean.Omega.Constraint }
                            { lowerBound := Option.none, upperBound := Option.some 0 : Lean.Omega.Constraint } 1 [1, -1]
                            (-1) [1, 0, -1] (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑aig.decls.size])
                            (Lean.Omega.Constraint.addInequality_sat
                              (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le hcurr))
                                (Eq.trans
                                  (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1))
                                  (Eq.symm
                                    (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                      { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                      (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑aig.decls.size]))))))
                            (Lean.Omega.tidy_sat
                              (Lean.Omega.Constraint.addInequality_sat
                                (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt a)))
                                  (Eq.trans
                                    (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0))
                                    (Eq.symm
                                      (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                        { coeffs := [1] : Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑aig.decls.size])))))))))
                        (Lean.Omega.Constraint.addInequality_sat
                          (le_of_le_of_eq (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt hidx)))
                            (Eq.trans
                              (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)
                                (Eq.trans
                                  (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                    (id (Eq.refl 1)))
                                  (Eq.symm
                                    (Lean.Omega.LinearCombo.add_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                      { const := 1 : Lean.Omega.LinearCombo }
                                      (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑aig.decls.size])))))
                              (Eq.symm
                                (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                  { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                  (Lean.Omega.Coeffs.ofList [↑w, ↑curr, ↑idx, ↑aig.decls.size]))))))))
                  aig curr hcurr idx hidx a)
            aig curr hcurr idx hidx) =
        (s.get idx hidx).cast
          (HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux.h11.der aig c curr hcurr s idx hidx) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux.h11.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10)
-/

-- Std.TreeMap.Raw.size_keysArray, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.Raw.size_keysArray.h4.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp},
      ¬Std.TransCmp cmp → t.WF → t.keysArray.size = t.size := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.Raw.size_keysArray.h4.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp}, t.WF → t.keysArray.size = t.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5
  exact Classical.byCases (fun hc_h => @Std.TreeMap.Raw.size_keysArray hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5) (fun hc_hn => @HypCheckProof.Std.TreeMap.Raw.size_keysArray.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5)

-- Std.Tactic.BVDecide.BVExpr.bitblast_decl_eq, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast_decl_eq.h5.der : ∀ {w : Nat}
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (input : Std.Tactic.BVDecide.BVExpr.WithCache (Std.Tactic.BVDecide.BVExpr w) aig) (idx : Nat),
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
                  (@Std.Tactic.BVDecide.BVExpr.Return.result aig w (@Std.Tactic.BVDecide.BVExpr.bitblast w aig input)))))) := by
  (intros; grind)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast_decl_eq.h5 : ∀ {w : Nat}
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (input : Std.Tactic.BVDecide.BVExpr.WithCache (Std.Tactic.BVDecide.BVExpr w) aig) (idx : Nat)
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
                (@Std.Tactic.BVDecide.BVExpr.Return.result aig w (@Std.Tactic.BVDecide.BVExpr.bitblast w aig input)))))
          idx (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast_decl_eq.h5.der w aig input idx h1))
        (@GetElem.getElem (Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) Nat
          (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
          (fun (xs : Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) (i : Nat) =>
            @LT.lt Nat instLTNat i (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit) xs))
          (@Array.instGetElemNatLtSize (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit))
          (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit aig)
          idx h1) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Std.Tactic.BVDecide.BVExpr.bitblast_decl_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast_decl_eq.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h4.inst : ¬0 < 0 * 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h4.prem0 : 0 ≤ 0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h4 : ¬∀ {n a b c : Nat}, c ≤ n → a < b * n := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h4.inst (@hc_h (0) (0) (0) (0) HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h4.prem0)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h5.inst : ¬0 < 1 * 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h5.prem0 : 0 < 1 * 1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h5 : ¬∀ {n a b c : Nat}, a < b * c → a < b * n := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h5.inst (@hc_h (0) (0) (1) (1) HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.aux4.h5.prem0)

-- Std.Tactic.BVDecide.Reflect.Bool.xor_congr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.xor_congr.h4.inst : ¬(Bool.true ^^ Bool.false) = (Bool.false ^^ Bool.false) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.xor_congr.h4 : ¬∀ (lhs rhs lhs' rhs' : Bool), rhs' = rhs → (lhs' ^^ rhs') = (lhs ^^ rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.xor_congr.h4.inst (@hc_h (Bool.false) (Bool.false) (Bool.true) (Bool.false) rfl)

-- Std.Tactic.BVDecide.Reflect.Bool.xor_congr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.xor_congr.h5.inst : ¬(Bool.false ^^ Bool.true) = (Bool.false ^^ Bool.false) := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.xor_congr.h5 : ¬∀ (lhs rhs lhs' rhs' : Bool), lhs' = lhs → (lhs' ^^ rhs') = (lhs ^^ rhs) := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.xor_congr.h5.inst (@hc_h (Bool.false) (Bool.false) (Bool.false) (Bool.true) rfl)

-- Std.Tactic.BVDecide.BVPred.bitblast_decl_eq, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVPred.bitblast_decl_eq.h4.der : ∀
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (input : Std.Tactic.BVDecide.BVExpr.WithCache Std.Tactic.BVDecide.BVPred aig) (idx : Nat),
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
                  (@Std.Tactic.BVDecide.Return.result aig (Std.Tactic.BVDecide.BVPred.bitblast aig input)))))) := by
  (intros; grind)
theorem HypCheckProof.Std.Tactic.BVDecide.BVPred.bitblast_decl_eq.h4 : ∀
      (aig :
        @Std.Sat.AIG Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
          Std.Tactic.BVDecide.instHashableBVBit)
      (input : Std.Tactic.BVDecide.BVExpr.WithCache Std.Tactic.BVDecide.BVPred aig) (idx : Nat)
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
                (@Std.Tactic.BVDecide.Return.result aig (Std.Tactic.BVDecide.BVPred.bitblast aig input)))))
          idx (HypCheckProof.Std.Tactic.BVDecide.BVPred.bitblast_decl_eq.h4.der aig input idx h1))
        (@GetElem.getElem (Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) Nat
          (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)
          (fun (xs : Array (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit)) (i : Nat) =>
            @LT.lt Nat instLTNat i (@Array.size (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit) xs))
          (@Array.instGetElemNatLtSize (Std.Sat.AIG.Decl Std.Tactic.BVDecide.BVBit))
          (@Std.Sat.AIG.decls Std.Tactic.BVDecide.BVBit Std.Tactic.BVDecide.instDecidableEqBVBit
            Std.Tactic.BVDecide.instHashableBVBit aig)
          idx h1) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Std.Tactic.BVDecide.BVPred.bitblast_decl_eq hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Std.Tactic.BVDecide.BVPred.bitblast_decl_eq.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- List.mem_of_range'_eq_append_cons, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.mem_of_range'_eq_append_cons.h6.inst : ¬0 ∈ List.range' 0 0 0 := by
  decide
theorem HypCheckProof.List.mem_of_range'_eq_append_cons.h6 : ¬∀ {s n step : Nat} {xs : List Nat} {i : Nat} {ys : List Nat}, i ∈ List.range' s n step := fun hc_h => HypCheckProof.List.mem_of_range'_eq_append_cons.h6.inst (@hc_h (0) (0) (0) ([]) (0) ([]))

-- Std.Tactic.BVDecide.BVExpr.eval_append, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.eval_append.h5.der : ∀ {assign : Std.Tactic.BVDecide.BVExpr.Assignment} {a : Nat} {lhs : Std.Tactic.BVDecide.BVExpr a} {a_1 : Nat}
      {rhs : Std.Tactic.BVDecide.BVExpr a_1},
      @Eq Nat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a a_1)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a a_1) := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.eval_append.h5 : ∀ {assign : Std.Tactic.BVDecide.BVExpr.Assignment} {a : Nat} {lhs : Std.Tactic.BVDecide.BVExpr a} {a_1 : Nat}
      {rhs : Std.Tactic.BVDecide.BVExpr a_1},
      @Eq (BitVec (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a a_1))
        (@Std.Tactic.BVDecide.BVExpr.eval (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a a_1) assign
          (@Std.Tactic.BVDecide.BVExpr.append a a_1 (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a a_1) lhs rhs
            (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.eval_append.h5.der assign a lhs a_1 rhs)))
        (@HAppend.hAppend (BitVec a) (BitVec a_1) (BitVec (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a a_1))
          (@BitVec.instHAppendHAddNat a a_1) (@Std.Tactic.BVDecide.BVExpr.eval a assign lhs)
          (@Std.Tactic.BVDecide.BVExpr.eval a_1 assign rhs)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Std.Tactic.BVDecide.BVExpr.eval_append hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.eval_append.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Std.Tactic.BVDecide.Reflect.Bool.lemma_congr, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.lemma_congr.h2.inst : ¬Bool.false = Bool.true := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.lemma_congr.h2 : ¬∀ (x x' : Bool), x = Bool.true → x' = Bool.true := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.lemma_congr.h2.inst (@hc_h (Bool.true) (Bool.false) rfl)

-- Std.Tactic.BVDecide.Reflect.Bool.lemma_congr, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.lemma_congr.h3.inst : ¬Bool.false = Bool.true := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.lemma_congr.h3 : ¬∀ (x x' : Bool), x' = x → x' = Bool.true := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.Bool.lemma_congr.h3.inst (@hc_h (Bool.false) (Bool.false) rfl)

-- Std.TreeMap.size_keysArray, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.TreeMap.size_keysArray.h4.gneg.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp},
      ¬Std.TransCmp cmp → t.keysArray.size = t.size := by
  (intros; grind)
theorem HypCheckProof.Std.TreeMap.size_keysArray.h4.{u, v} : ∀ {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp}, t.keysArray.size = t.size := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact Classical.byCases (fun hc_h => @Std.TreeMap.size_keysArray hc_x0 hc_x1 hc_x2 hc_x3 hc_h) (fun hc_hn => @HypCheckProof.Std.TreeMap.size_keysArray.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn)

-- Std.Tactic.BVDecide.Reflect.BitVec.rotateLeft_congr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.rotateLeft_congr.h4.inst : ¬(1#1).rotateLeft 0 = (0#1).rotateLeft 0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.rotateLeft_congr.h4 : ¬∀ (n w : Nat) (x x' : BitVec w), x'.rotateLeft n = x.rotateLeft n := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.rotateLeft_congr.h4.inst (@hc_h (0) (1) (0#1) (1#1))

-- Std.Tactic.BVDecide.Reflect.BitVec.replicate_congr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.replicate_congr.h4.inst : ¬BitVec.replicate 1 1#1 = BitVec.replicate 1 0#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.replicate_congr.h4 : ¬∀ (n w : Nat) (expr expr' : BitVec w), BitVec.replicate n expr' = BitVec.replicate n expr := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.replicate_congr.h4.inst (@hc_h (1) (1) (0#1) (1#1))

-- List.Cursor.current_at, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Cursor.current_at.h3.inst : Not (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.length Nat (@List.nil Nat))) := by
  decide
theorem HypCheckProof.List.Cursor.current_at.h3 : Not (∀ {α : Type} {n : Nat} (l : List α), @LT.lt Nat instLTNat n (@List.length α l)) := fun hc_h => HypCheckProof.List.Cursor.current_at.h3.inst (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))

-- Std.Tactic.BVDecide.Normalize.BitVec.getElem_eq_getLsbD, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.getElem_eq_getLsbD.h3.inst : ¬0 < 0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.getElem_eq_getLsbD.h3 : ¬∀ {w : Nat} (a : BitVec w) (i : Nat), i < w := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.getElem_eq_getLsbD.h3.inst (@hc_h (0) (0#0) (0))

-- Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim', hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim'.h3.inst : ¬BitVec.signExtend 2 1#1 = BitVec.extractLsb' 0 2 1#1 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim'.h3 : ¬∀ {v : Nat} {x : BitVec v} {w : Nat}, BitVec.signExtend w x = BitVec.extractLsb' 0 w x := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim'.h3.inst (@hc_h (1) (1#1) (2))

-- List.Cursor.tail_at, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Cursor.tail_at.h3.inst : Not (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.length Nat (@List.nil Nat))) := by
  decide
theorem HypCheckProof.List.Cursor.tail_at.h3 : Not (∀ {α : Type} {n : Nat} (l : List α), @LT.lt Nat instLTNat n (@List.length α l)) := fun hc_h => HypCheckProof.List.Cursor.tail_at.h3.inst (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))

-- Std.Http.Internal.Char.not_quotedStringChar_of_not_qdtext_not_dquote_backslash, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Http.Internal.Char.not_quotedStringChar_of_not_qdtext_not_dquote_backslash.h2.inst : ¬¬Std.Http.Internal.Char.quotedStringChar 'a' = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Http.Internal.Char.not_quotedStringChar_of_not_qdtext_not_dquote_backslash.h2.prem0 : 'a' < '' := by
  decide
theorem HypCheckProof.Std.Http.Internal.Char.not_quotedStringChar_of_not_qdtext_not_dquote_backslash.h2 : ¬∀ (c : Char), c < '' → ¬Std.Http.Internal.Char.quotedStringChar c = Bool.true := fun hc_h => HypCheckProof.Std.Http.Internal.Char.not_quotedStringChar_of_not_qdtext_not_dquote_backslash.h2.inst (@hc_h ('a') HypCheckProof.Std.Http.Internal.Char.not_quotedStringChar_of_not_qdtext_not_dquote_backslash.h2.prem0)

-- Std.Tactic.BVDecide.Reflect.BitVec.ofBool_congr, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.ofBool_congr.h2.inst : ¬(1#1).getLsbD 0 = Bool.false := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.ofBool_congr.h2 : ¬∀ (b : Bool) (e' : BitVec 1), e'.getLsbD 0 = b := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Reflect.BitVec.ofBool_congr.h2.inst (@hc_h (Bool.false) (1#1))

-- Std.Tactic.BVDecide.Normalize.BitVec.ofNatLT_reduce, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.ofNatLT_reduce.h2.inst : ¬1 < 2 ^ 0 := by
  decide
theorem HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.ofNatLT_reduce.h2 : ¬∀ {w : Nat} (n : Nat), n < 2 ^ w := fun hc_h => HypCheckProof.Std.Tactic.BVDecide.Normalize.BitVec.ofNatLT_reduce.h2.inst (@hc_h (0) (1))

-- Lean.Order.le_prop_of_right, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.le_prop_of_right.h2.inst : Not (@Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp True False) := by
  simp
theorem HypCheckProof.Lean.Order.le_prop_of_right.h2 : Not (∀ (x y : Prop), @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp x y) := fun hc_h => HypCheckProof.Lean.Order.le_prop_of_right.h2.inst (@hc_h (True) (False))

-- Lean.Order.le_of_imp_top_le, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.le_of_imp_top_le.h2.inst : Not (@Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp True False) := by
  simp
theorem HypCheckProof.Lean.Order.le_of_imp_top_le.h2 : Not (∀ (x y : Prop), @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp x y) := fun hc_h => HypCheckProof.Lean.Order.le_of_imp_top_le.h2.inst (@hc_h (True) (False))

-- Lean.Order.true_le_of_top_le, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.true_le_of_top_le.h1.inst : Not (@Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp True False) := by
  simp
theorem HypCheckProof.Lean.Order.true_le_of_top_le.h1 : Not (∀ (x : Prop), @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp True x) := fun hc_h => HypCheckProof.Lean.Order.true_le_of_top_le.h1.inst (@hc_h (False))

-- Lean.Order.top_le_prop, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Order.top_le_prop.h1.inst : Not
      (@Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp
        (@Lean.Order.top Prop Std.Internal.Order.instCompleteLatticeProp) False) := by
  simp
theorem HypCheckProof.Lean.Order.top_le_prop.h1 : Not
      (∀ (x : Prop),
        @Lean.Order.PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp
          (@Lean.Order.top Prop Std.Internal.Order.instCompleteLatticeProp) x) := fun hc_h => HypCheckProof.Lean.Order.top_le_prop.h1.inst (@hc_h (False))

