import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

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

-- _private.Mathlib.Data.List.Lex.0.List.Lex.isOrderConnected.aux, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.isOrderConnected.aux.h7 : ¬∀ {α : Type} (r : α → α → Prop) [inst : IsOrderConnected α r] [inst : Std.Trichotomous r] (x x_1 x_2 : List α),
        List.Lex r x x_1 ∨ List.Lex r x_1 x_2 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ _ ([]) ([]) ([])) (by
  decide +kernel)

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

-- _private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_left_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_mul_left_lt.h5 : ¬∀ {a b c : EReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ 0 < b → ∃ a' ∈ Set.Ioo a ⊤, a' * b < c := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  simp) (by
  decide)) (by
  simp)

-- _private.Mathlib.Data.Nat.Log.0.Nat.log.go_aux, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log.go_aux.h3 : ¬∀ {n b fuel : ℕ}, b ≤ n → n < (b * b) ^ fuel := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.Log.0.Nat.log.go_aux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log.go_aux.h4 : ¬∀ {n b fuel : ℕ}, n < b ^ (fuel + 1) → n < (b * b) ^ fuel := fun hc_h => absurd (@hc_h (1) (2) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.MinMax.0.List.foldl_argAux_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl_argAux_mem.h6 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] (l : List α) (a m : α), m ∈ a :: l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([]) (0) (1)) (by
  decide +kernel)

