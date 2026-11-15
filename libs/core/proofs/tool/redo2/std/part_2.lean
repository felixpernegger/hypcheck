import Std

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Std.DHashMap.get_insertMany_list_of_mem, hypothesis 13: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.get_insertMany_list_of_mem.h13.{u, v} : ∀ {α : Type u} {β : α → Type v} {x : BEq α} {x_1 : Hashable α} {m : Std.DHashMap α β} [inst : LawfulBEq α]
      {l : List ((a : α) × β a)} {k k' : α},
      (k == k') = Bool.true →
        ∀ {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ m.insertMany l := by
  (intros; grind)

-- Std.ExtDHashMap.get_ofList_of_mem, hypothesis 12: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.ExtDHashMap.get_ofList_of_mem.h12.{u, v} : ∀ {α : Type u} {x : BEq α} {x_1 : Hashable α} {β : α → Type v} [inst : LawfulBEq α] {l : List ((a : α) × β a)}
      {k k' : α},
      (k == k') = Bool.true →
        ∀ {v : β k},
          List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
            (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ Std.ExtDHashMap.ofList l := by
  (intros; grind)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get.h8 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (curr : Nat) (s : aig.RefVec curr) (idx : Nat), idx < w → curr ≤ idx → curr ≤ w := by
  (intros; omega)

