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

-- _private.Mathlib.Data.List.Lex.0.List.Lex.asymm.aux, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.asymm.aux.h2 : ¬∀ {α : Type} (r : α → α → Prop) (x x_1 : List α), List.Lex r x x_1 → List.Lex r x_1 x → False := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([0]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.asymm.aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.asymm.aux.h5 : ¬∀ {α : Type} (r : α → α → Prop) [inst : Std.Asymm r] (x x_1 : List α), List.Lex r x_1 x → False := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.asymm.aux, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.asymm.aux.h6 : ¬∀ {α : Type} (r : α → α → Prop) [inst : Std.Asymm r] (x x_1 : List α), List.Lex r x x_1 → False := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_left_of_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_lt_mul_left_of_nonneg.h5 : ¬∀ {a b c : EReal}, 0 ≤ a → 0 ≤ c → ∃ a' ∈ Set.Ioo 0 a, c < a' * b := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  rfl) (by
  rfl)) (by
  simp)

-- _private.Mathlib.Data.EReal.Operations.0.EReal.exists_lt_add_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_lt_add_left.h3 : ¬∀ {a b c : EReal}, ∃ a' < a, c < a' + b := fun hc_h => absurd (@hc_h (0) (⊥) (0)) (by
  simp)

-- _private.Mathlib.Data.Int.Fib.Basic.0.Int.fib_natCast_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.fib_natCast_dvd.h2 : ¬∀ {m : ℕ} {n : ℤ}, Int.fib ↑m ∣ Int.fib n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.Fib.Zeckendorf.0.Nat.zeckendorf_aux, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.zeckendorf_aux.h1 : ¬∀ {m : ℕ}, m - Nat.fib m.greatestFib < m := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

