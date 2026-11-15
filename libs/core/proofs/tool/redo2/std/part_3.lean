import Std

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Std.ExtDHashMap.get_insertMany_list_of_mem, hypothesis 13: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDHashMap.get_insertMany_list_of_mem.h13.{u, v} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} {m : Std.ExtDHashMap α β} [inst : LawfulBEq α]
      {l : List ((a : α) × β a)} {k k' : α},
      (k == k') = Bool.true →
        ∀ {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ m.insertMany l := by
  (intros; grind)

-- Std.DHashMap.get_ofList_of_mem, hypothesis 12: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.get_ofList_of_mem.h12.{u, v} : ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} [inst : LawfulBEq α] {l : List ((a : α) × β a)}
      {k k' : α},
      (k == k') = Bool.true →
        ∀ {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ Std.DHashMap.ofList l := by
  (intros; grind)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq.h9 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (assign : α → Bool) (curr : Nat) (s : aig.RefVec curr) (idx : Nat),
      idx < w → curr ≤ idx → curr ≤ w := by
  (intros; omega)

