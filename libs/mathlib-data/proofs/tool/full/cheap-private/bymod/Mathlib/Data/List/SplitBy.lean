import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.List.SplitBy.0.List.isChain_getLast_head_splitByLoop, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_getLast_head_splitByLoop.h8.inst : ¬List.IsChain
        (fun (a b : List ℕ) =>
          ∃ (ha : a ≠ []) (hb : b ≠ []),
            (fun (a b : ℕ) => Decidable.decide (a < b)) (a.getLast ha) (b.head hb) = Bool.false)
        (List.splitBy.loop (fun (a b : ℕ) => Decidable.decide (a < b)) [] 1 [] [[0]]) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_getLast_head_splitByLoop.h8.prem0 : [] ∉ [[0]] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_getLast_head_splitByLoop.h8.prem1 : List.IsChain
      (fun (b a : List ℕ) =>
        ∃ (ha : a ≠ []) (hb : b ≠ []), (fun (a b : ℕ) => Decidable.decide (a < b)) (a.getLast ha) (b.head hb) = Bool.false)
      [[0]] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.isChain_getLast_head_splitByLoop.h8 : ¬∀ {α : Type} {r : α → α → Bool} (l : List α) {a : α} {g : List α} {gs : List (List α)},
        [] ∉ gs →
          List.IsChain (fun (b a : List α) => ∃ (ha : a ≠ []) (hb : b ≠ []), r (a.getLast ha) (b.head hb) = Bool.false) gs →
            List.IsChain (fun (a b : List α) => ∃ (ha : a ≠ []) (hb : b ≠ []), r (a.getLast ha) (b.head hb) = Bool.false)
              (List.splitBy.loop r l a g gs) := fun hc_h => HypCheckProof.List.isChain_getLast_head_splitByLoop.h8.inst (@hc_h (ℕ) (fun (a b : ℕ) => Decidable.decide (a < b)) ([]) (1) ([]) ([[0]]) HypCheckProof.List.isChain_getLast_head_splitByLoop.h8.prem0 HypCheckProof.List.isChain_getLast_head_splitByLoop.h8.prem1)

-- _private.Mathlib.Data.List.SplitBy.0.List.splitBy_append_of_isChain, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_append_of_isChain.h4.inst : Not (@Ne (List Nat) (@List.nil Nat) (@List.nil Nat)) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_append_of_isChain.h4.prem0 : @List.IsChain Nat
      (fun (x y : Nat) =>
        @Eq Bool ((fun (a b : Nat) => @Decidable.decide (@LT.lt Nat instLTNat a b) (a.decLt b)) x y) Bool.true)
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.splitBy_append_of_isChain.h4 : Not
      (∀ {α : Type} {m : List α} {r : α → α → Bool} {l : List α},
        @List.IsChain α (fun (x y : α) => @Eq Bool (r x y) Bool.true) l → @Ne (List α) l (@List.nil α)) := fun hc_h => HypCheckProof.List.splitBy_append_of_isChain.h4.inst (@hc_h (Nat) (@List.nil Nat) (fun (a b : Nat) => @Decidable.decide (@LT.lt Nat instLTNat a b) (a.decLt b)) (@List.nil Nat) HypCheckProof.List.splitBy_append_of_isChain.h4.prem0)

-- _private.Mathlib.Data.List.SplitBy.0.List.splitBy_append_of_isChain, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.splitBy_append_of_isChain.h5 : ¬∀ {α : Type} {m : List α} {r : α → α → Bool} {l : List α} (hn : l ≠ []),
        (∀ x ∈ m.head?, r (l.getLast hn) x = Bool.false) → List.splitBy r (l ++ m) = l :: List.splitBy r m := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ([]) (fun a b => a < b : ℕ → ℕ → Bool) ([1, 0]) hc_k0 hc_k1) (by
  decide +kernel)

-- _private.Mathlib.Data.List.SplitBy.0.List.splitBy_append_of_isChain, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_append_of_isChain.h6.inst : ¬List.splitBy (fun (a b : ℕ) => Decidable.decide (a ≤ b)) ([0] ++ [0]) =
        [0] :: List.splitBy (fun (a b : ℕ) => Decidable.decide (a ≤ b)) [0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_append_of_isChain.h6.prem0 : [0] ≠ [] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_append_of_isChain.h6.prem1 : List.IsChain (fun (x y : ℕ) => (fun (a b : ℕ) => Decidable.decide (a ≤ b)) x y = Bool.true) [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.splitBy_append_of_isChain.h6 : ¬∀ {α : Type} {m : List α} {r : α → α → Bool} {l : List α},
        l ≠ [] → List.IsChain (fun (x y : α) => r x y = Bool.true) l → List.splitBy r (l ++ m) = l :: List.splitBy r m := fun hc_h => HypCheckProof.List.splitBy_append_of_isChain.h6.inst (@hc_h (ℕ) ([0]) (fun (a b : ℕ) => Decidable.decide (a ≤ b)) ([0]) HypCheckProof.List.splitBy_append_of_isChain.h6.prem0 HypCheckProof.List.splitBy_append_of_isChain.h6.prem1)

-- _private.Mathlib.Data.List.SplitBy.0.List.isChain_of_mem_splitByLoop, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_of_mem_splitByLoop.h6.inst : ¬List.IsChain (fun (x y : ℕ) => (fun (a b : ℕ) => Decidable.decide (a < b)) x y = Bool.true) [1, 0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_of_mem_splitByLoop.h6.prem0 : List.IsChain (fun (y x : ℕ) => (fun (a b : ℕ) => Decidable.decide (a < b)) x y = Bool.true) [1] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_of_mem_splitByLoop.h6.prem1 : [1, 0] ∈ List.splitBy.loop (fun (a b : ℕ) => Decidable.decide (a < b)) [] 0 [1] [] := by
  decide
theorem HypCheckProof.List.isChain_of_mem_splitByLoop.h6 : ¬∀ {α : Type} {m : List α} {r : α → α → Bool} {l : List α} {a : α} {g : List α},
        List.IsChain (fun (y x : α) => r x y = Bool.true) g →
          m ∈ List.splitBy.loop r l a g [] → List.IsChain (fun (x y : α) => r x y = Bool.true) m := fun hc_h => HypCheckProof.List.isChain_of_mem_splitByLoop.h6.inst (@hc_h (ℕ) ([1, 0]) (fun (a b : ℕ) => Decidable.decide (a < b)) ([]) (0) ([1]) HypCheckProof.List.isChain_of_mem_splitByLoop.h6.prem0 HypCheckProof.List.isChain_of_mem_splitByLoop.h6.prem1)

-- _private.Mathlib.Data.List.SplitBy.0.List.isChain_of_mem_splitByLoop, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_of_mem_splitByLoop.h8.inst : ¬List.IsChain (fun (x y : ℕ) => (fun (a b : ℕ) => Decidable.decide (a < b)) x y = Bool.true) [1, 0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_of_mem_splitByLoop.h8.prem0 : ∀ b ∈ [].head?, (fun (a b : ℕ) => Decidable.decide (a < b)) b 0 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_of_mem_splitByLoop.h8.prem1 : List.IsChain (fun (y x : ℕ) => (fun (a b : ℕ) => Decidable.decide (a < b)) x y = Bool.true) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.isChain_of_mem_splitByLoop.h8 : ¬∀ {α : Type} {m : List α} {r : α → α → Bool} {l : List α} {a : α} {g : List α},
        (∀ b ∈ g.head?, r b a = Bool.true) →
          List.IsChain (fun (y x : α) => r x y = Bool.true) g → List.IsChain (fun (x y : α) => r x y = Bool.true) m := fun hc_h => HypCheckProof.List.isChain_of_mem_splitByLoop.h8.inst (@hc_h (ℕ) ([1, 0]) (fun (a b : ℕ) => Decidable.decide (a < b)) ([]) (0) ([]) HypCheckProof.List.isChain_of_mem_splitByLoop.h8.prem0 HypCheckProof.List.isChain_of_mem_splitByLoop.h8.prem1)

-- _private.Mathlib.Data.List.SplitBy.0.List.splitByLoop_append, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitByLoop_append.h6.inst : ¬List.splitBy.loop (fun (a b : ℕ) => Decidable.decide (a < b)) ([0] ++ []) 0 [] [] =
        ([].reverse ++ [0, 0]) :: List.splitBy (fun (a b : ℕ) => Decidable.decide (a < b)) [] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitByLoop_append.h6.prem0 : ∀ x ∈ [].head?, (fun (a b : ℕ) => Decidable.decide (a < b)) ([0, 0].getLast (List.cons_ne_nil 0 [0])) x = Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.splitByLoop_append.h6 : ¬∀ {α : Type} {m : List α} {r : α → α → Bool} {l g : List α} {a : α},
        (∀ x ∈ m.head?, r ((a :: l).getLast (List.cons_ne_nil a l)) x = Bool.false) →
          List.splitBy.loop r (l ++ m) a g [] = (g.reverse ++ a :: l) :: List.splitBy r m := fun hc_h => HypCheckProof.List.splitByLoop_append.h6.inst (@hc_h (ℕ) ([]) (fun (a b : ℕ) => Decidable.decide (a < b)) ([0]) ([]) (0) HypCheckProof.List.splitByLoop_append.h6.prem0)

-- _private.Mathlib.Data.List.SplitBy.0.List.splitByLoop_append, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitByLoop_append.h7.inst : ¬List.splitBy.loop (fun (a b : ℕ) => Decidable.decide (a ≤ b)) ([] ++ [0]) 0 [] [] =
        ([].reverse ++ [0]) :: List.splitBy (fun (a b : ℕ) => Decidable.decide (a ≤ b)) [0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitByLoop_append.h7.prem0 : List.IsChain (fun (x y : ℕ) => (fun (a b : ℕ) => Decidable.decide (a ≤ b)) x y = Bool.true) ([].reverse ++ [0]) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.splitByLoop_append.h7 : ¬∀ {α : Type} {m : List α} {r : α → α → Bool} {l g : List α} {a : α},
        List.IsChain (fun (x y : α) => r x y = Bool.true) (g.reverse ++ a :: l) →
          List.splitBy.loop r (l ++ m) a g [] = (g.reverse ++ a :: l) :: List.splitBy r m := fun hc_h => HypCheckProof.List.splitByLoop_append.h7.inst (@hc_h (ℕ) ([0]) (fun (a b : ℕ) => Decidable.decide (a ≤ b)) ([]) ([]) (0) HypCheckProof.List.splitByLoop_append.h7.prem0)

