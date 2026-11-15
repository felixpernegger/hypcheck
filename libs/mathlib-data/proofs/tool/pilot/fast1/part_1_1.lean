import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Set.IsWF.min_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_mul.h5 : ¬∀ {α : Type} {s t : Set α} [inst : CommMonoid α] [inst_1 : LinearOrder α],
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty → IsOrderedCancelMonoid α := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (BooleanRing.toCommRing.toCommMonoid) (Bool.linearOrder) (by
  simp) (by
  simp) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.le_of_mul_le_mul_left (Bool.false : Bool) (Bool.true : Bool) (Bool.false : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Int.div_lt_div_iff_of_dvd_of_neg_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_neg_of_pos.h4 : ¬∀ {a b c d : ℤ}, 0 < d → b ∣ a → d ∣ c → (a / b < c / d ↔ c * b < d * a) := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.nontrivial_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_lt.h6 : ¬∀ {α : Type} {s : Set α} [inst : Preorder α] {x y : α}, x ∈ s → x < y → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (Nat.instPreorder) (0) (1) (by
  decide) (by
  decide)) (by
  simp)

-- List.mem_dlookup_kunion_middle, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dlookup_kunion_middle.h8 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {b : β a} {l₁ l₂ l₃ : List (Sigma β)},
        a ∉ l₂.keys → b ∈ List.dlookup a ((l₁.kunion l₂).kunion l₃) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) ([]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- Nat.gcd_greatest, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcd_greatest.h5 : ¬∀ {a b d : ℕ}, d ∣ a → d ∣ b → d = a.gcd b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- not_injective_dotProduct_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_injective_dotProduct_left.h5 : ¬∀ {m α : Type} [inst : Fintype m] [inst_1 : CommRing α] [inst_2 : Nontrivial m] (a : m → α),
        ¬Function.Injective (dotProduct a) := fun hc_h => absurd (@hc_h (Bool) (Unit) (Bool.fintype) (PUnit.commRing) _ (fun (a : Bool) => PUnit.unit)) (by
  decide +kernel)

-- List.minimum_anti, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_anti.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l₁ l₂ : List α}, l₂.minimum ≤ l₁.minimum := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([0]) ([])) (by
  decide +kernel)

-- Matrix.vecHead_vecAlt1, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.vecHead_vecAlt1.h3 : ¬∀ {α : Type} {m n : ℕ} (v : Fin (m + 2) → α), m + 2 = n + 1 + (n + 1) := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (fun (a : Fin (0 + 2)) => 0)) (by
  decide +kernel)

-- List.prev_singleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_singleton.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (x y : α), x ∈ [y] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (1)) (by
  decide +kernel)

-- Set.image2_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_left.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, Set.image2 (fun (x : α) (x_1 : β) => x) s t = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- List.IsChain.sortedGE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.sortedGE.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.pair_eq_of_unpair_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pair_eq_of_unpair_eq.h3 : ¬∀ {n a b : ℕ}, Nat.pair a b = n := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Rat.toNNRat_div', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_div'.h2 : ¬∀ {p q : ℚ}, (p / q).toNNRat = p.toNNRat / q.toNNRat := fun hc_h => absurd (@hc_h (-1) (-1)) (by
  decide +kernel)

