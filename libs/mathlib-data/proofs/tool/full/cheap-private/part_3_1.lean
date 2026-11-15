import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.Mathlib.Data.Nat.PadicValNat.0.Nat.pow_dvd_iff_le_of_spec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_of_spec.h5 : ¬∀ {p k n a b : ℕ}, p ^ a * b = n → ¬p ∣ b → (p ^ k ∣ n ↔ k ≤ a) := fun hc_h => absurd (@hc_h (0) (2) _ (1) (1) rfl (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.PadicValNat.0.Nat.pow_dvd_iff_le_of_spec, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_of_spec.h6 : ¬∀ {p k n a b : ℕ}, 1 < p → ¬p ∣ b → (p ^ k ∣ n ↔ k ≤ a) := fun hc_h => absurd (@hc_h (2) (1) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.PadicValNat.0.Nat.pow_dvd_iff_le_of_spec, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_of_spec.h7 : ¬∀ {p k n a b : ℕ}, 1 < p → p ^ a * b = n → (p ^ k ∣ n ↔ k ≤ a) := fun hc_h => absurd (@hc_h (2) (1) _ (0) (0) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.MaxPowDiv.0.Nat.pow_dvd_iff_le_of_spec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_of_spec.h5 : ¬∀ {p k n a b : ℕ}, p ^ a * b = n → ¬p ∣ b → (p ^ k ∣ n ↔ k ≤ a) := fun hc_h => absurd (@hc_h (0) (2) _ (1) (1) rfl (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.MaxPowDiv.0.Nat.pow_dvd_iff_le_of_spec, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_of_spec.h6 : ¬∀ {p k n a b : ℕ}, 1 < p → ¬p ∣ b → (p ^ k ∣ n ↔ k ≤ a) := fun hc_h => absurd (@hc_h (2) (1) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.MaxPowDiv.0.Nat.pow_dvd_iff_le_of_spec, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_of_spec.h7 : ¬∀ {p k n a b : ℕ}, 1 < p → p ^ a * b = n → (p ^ k ∣ n ↔ k ≤ a) := fun hc_h => absurd (@hc_h (2) (1) _ (0) (0) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Shortlex.0.Acc.shortlex, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Acc.shortlex.h5.gneg.{u_1} : ∀ {α : Type u_1} {r : α → α → Prop} {a : α} {b : List α},
      Acc r a →
        ¬Acc (List.Shortlex r) b →
          (∀ (s : List α), s.length < (a :: b).length → Acc (List.Shortlex r) s) → Acc (List.Shortlex r) (a :: b) := by
  (intros; solve_by_elim)
theorem HypCheckProof.Acc.shortlex.h5.{u_1} : ∀ {α : Type u_1} {r : α → α → Prop} {a : α} {b : List α},
      Acc r a → (∀ (s : List α), s.length < (a :: b).length → Acc (List.Shortlex r) s) → Acc (List.Shortlex r) (a :: b) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6
  exact Classical.byCases (fun hc_h => @Acc.shortlex hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6) (fun hc_hn => @HypCheckProof.Acc.shortlex.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Acc.shortlex.h5.derivable.{u_1} : ∀ {α : Type u_1} {r : α → α → Prop} {a : α} {b : List α},
      Acc r a → (∀ (s : List α), s.length < (a :: b).length → Acc (List.Shortlex r) s) → Acc (List.Shortlex r) b := by
  (intros; solve_by_elim)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.trichotomous.aux, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.trichotomous.aux.h2 : ¬∀ {α : Type} (r : α → α → Prop) (x x_1 : List α), ¬List.Lex r x x_1 → ¬List.Lex r x_1 x → x = x_1 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) ([0]) ([1]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.trichotomous.aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.trichotomous.aux.h5 : ¬∀ {α : Type} (r : α → α → Prop) [inst : Std.Trichotomous r] (x x_1 : List α), ¬List.Lex r x_1 x → x = x_1 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.trichotomous.aux, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.trichotomous.aux.h6 : ¬∀ {α : Type} (r : α → α → Prop) [inst : Std.Trichotomous r] (x x_1 : List α), ¬List.Lex r x x_1 → x = x_1 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_right_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_mul_right_lt.h5 : ¬∀ {a b c : EReal}, 0 < a ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → ∃ b' ∈ Set.Ioo b ⊤, a * b' < c := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  simp) (by
  decide)) (by
  simp)

-- _private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_right_of_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_lt_mul_right_of_nonneg.h5 : ¬∀ {a b c : EReal}, 0 ≤ a → 0 ≤ c → ∃ b' ∈ Set.Ioo 0 b, c < a * b' := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  rfl) (by
  rfl)) (by
  simp)

