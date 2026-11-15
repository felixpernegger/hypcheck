import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- List.IsChain.concat_induction_head, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.concat_induction_head.h7 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (l ++ [b]) → (∀ ⦃x y : α⦄, r x y → p x → p y) → p a → p b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (0) (1) (fun n => n = 0 : ℕ → Prop) ([]) (by
  decide) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.Finite.toFinset_union, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Finite.toFinset_union.h5.der.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α], s.Finite → (s ∪ t).Finite → t.Finite := by
  (intros; simp_all; done)
theorem HypCheckProof.Set.Finite.toFinset_union.h5.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (hs : s.Finite) (h : (s ∪ t).Finite),
      h.toFinset = hs.toFinset ∪ (HypCheckProof.Set.Finite.toFinset_union.h5.der hs h).toFinset := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Set.Finite.toFinset_union hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Set.Finite.toFinset_union.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- List.mem_dropLast_of_mem_of_ne_getLastD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dropLast_of_mem_of_ne_getLastD.h5 : ¬∀ {α : Type} {l : List α} {a : α} {d : α}, a ∈ l → a ∈ l.dropLast := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.mul_right_cancel', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_right_cancel'.h4 : ¬∀ {m a b c : ℤ}, a * c ≡ b * c [ZMOD m * c] → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.idxOf_get, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_get.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l : List α} (h : List.idxOf a l < l.length),
        l.get (⟨List.idxOf a l, h⟩ : Fin l.length) = a := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (0) ([1]) hc_k0) (by
  decide +kernel)

-- List.Nodup.filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.filterMap.h5 : ¬∀ {α β : Type} {l : List α} {f : α → Option β},
        (∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a') → (List.filterMap f l).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0, 0]) (some : ℕ → Option ℕ) (by
  simp)) (by
  decide +kernel)

-- Nat.factorization_eq_one_of_squarefree, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_one_of_squarefree.h4 : ¬∀ {n p : ℕ}, Squarefree n → Nat.Prime p → n.factorization p = 1 := fun hc_h => absurd (@hc_h (1) (2) (by
  decide +kernel) (by
  decide)) (by
  decide +kernel)

-- Int.dvd_of_dvd_mul_left_of_gcd_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.dvd_of_dvd_mul_left_of_gcd_one.h4 : ¬∀ {a b c : ℤ}, a ∣ b * c → a ∣ b := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- ZMod.unitsMap_comp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.unitsMap_comp.h4 : ¬∀ {n m d : ℕ}, n ∣ m → m ∣ d := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Matrix.diagonal_ofNat', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.diagonal_ofNat'.h6 : ¬∀ {n α : Type} [inst : DecidableEq n] [inst : Zero α] [inst : NatCast α] (m : ℕ), m.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (instNatCastNat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.range_eq_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.range_eq_empty.h2 : ¬∀ {α ι : Type} (f : ι → α), Set.range f = ∅ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- EReal.bot_div_of_pos_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.bot_div_of_pos_ne_top.h2 : ¬∀ {a : EReal}, 0 < a → ⊥ / a = ⊥ := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- Nat.prod_pow_factorization_choose, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_pow_factorization_choose.h2 : ¬∀ (n k : ℕ), ∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p = n.choose k := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Fin.val_rev_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_rev_zero.h1 : ¬∀ {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

