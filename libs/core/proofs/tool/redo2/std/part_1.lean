import Std

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Std.DHashMap.Raw.get_insertMany_list_of_mem, hypothesis 14: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.DHashMap.Raw.get_insertMany_list_of_mem.h14.{u, v} : ∀ {α : Type u} {β : α → Type v} {m : Std.DHashMap.Raw α β} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : LawfulBEq α],
      m.WF →
        ∀ {l : List ((a : α) × β a)} {k k' : α},
          (k == k') = Bool.true →
            ∀ {v : β k},
              List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) l →
                (⟨k, v⟩ : (a : α) × β a) ∈ l → k' ∈ m.insertMany l := by
  (intros; grind)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq.h9 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (distance : Nat)
      (input : aig.RefVec w) (assign : α → Bool) (curr : Nat) (s : aig.RefVec curr) (idx : Nat),
      idx < w → curr ≤ idx → curr ≤ w := by
  (intros; omega)

-- Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux, hypothesis 11: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux.h11.der : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (c : BitVec w) (curr : Nat),
      curr ≤ w → ∀ (s : aig.RefVec curr) (idx : Nat), idx < curr → aig.decls.size ≤ aig.decls.size := by
  (intros; omega)
theorem HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux.h11 : ∀ {α : Type} [inst : Hashable α] [inst_1 : DecidableEq α] {w : Nat} (aig : Std.Sat.AIG α) (c : BitVec w) (curr : Nat)
      (hcurr : curr ≤ w) (s : aig.RefVec curr) (idx : Nat) (hidx : idx < curr),
      (Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go aig c curr s hcurr).get idx (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = (s.get idx hidx).cast (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10
  exact @Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 (@HypCheckProof.Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_get_aux.h11.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10)

