import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Set.BijOn.iInter_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.iInter_congr.h8 : ¬∀ {α β γ : Type} {s : Set β} {t : Set γ} (f : β → Set α) (g : γ → Set α) {h : β → γ},
        (∀ (x : β), g (h x) = f x) → ⋂ x ∈ s, f x = ⋂ y ∈ t, g y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- IsUnit.natCast_factorial_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_factorial_of_le.h5 : Not
      (∀ {A : Type} [inst : Semiring A] {n : Nat},
        @IsUnit A (@Semiring.toMonoid A inst)
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddCommMonoidWithOne.toAddMonoidWithOne A
                  (@NonAssocSemiring.toAddCommMonoidWithOne A (@Semiring.toNonAssocSemiring A inst))))
              n.factorial) →
          ∀ {m : Nat},
            @IsUnit A (@Semiring.toMonoid A inst)
              (@Nat.cast A
                (@AddMonoidWithOne.toNatCast A
                  (@AddCommMonoidWithOne.toAddMonoidWithOne A
                    (@NonAssocSemiring.toAddCommMonoidWithOne A (@Semiring.toNonAssocSemiring A inst))))
                m.factorial)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instSemiring) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- List.Nodup.pairwise_of_forall_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.pairwise_of_forall_ne.h4 : ¬∀ {α : Type} {l : List α} {r : α → α → Prop}, l.Nodup → List.Pairwise r l := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (fun a b => a < b : ℕ → ℕ → Prop) (by
  decide)) (by
  decide +kernel)

-- Sum.getRight_eq_getRight?, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Sum.getRight_eq_getRight?.h3.der.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β}, x.getRight?.isSome = Bool.true → x.isRight = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Sum.getRight_eq_getRight?.h3.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β} (h₂ : x.getRight?.isSome = Bool.true),
      x.getRight (HypCheckProof.Sum.getRight_eq_getRight?.h3.der h₂) = x.getRight?.get h₂ := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Sum.getRight_eq_getRight? hc_x0 hc_x1 hc_x2 (@HypCheckProof.Sum.getRight_eq_getRight?.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Nat.le_log_iff_pow_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_log_iff_pow_le.h1 : ¬∀ {b x y : ℕ}, y ≠ 0 → (x ≤ Nat.log b y ↔ b ^ x ≤ y) := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Set.empty_eq_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.empty_eq_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, ∅ = s → ∅ = t := fun hc_h => absurd (@hc_h (ℕ) _ ({n : ℕ | n = 0}) rfl) (by
  simp)

-- List.kerase_append_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.kerase_append_left.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {l₁ l₂ : List (Sigma β)},
        List.kerase a (l₁ ++ l₂) = List.kerase a l₁ ++ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- Nat.exists_eq_pow_mul_and_not_dvd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_eq_pow_mul_and_not_dvd.h1 : ¬∀ {n : ℕ} (p : ℕ), p ≠ 1 → ∃ (e : ℕ) (n' : ℕ), ¬p ∣ n' ∧ n = p ^ e * n' := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  (simp <;> omega))

-- List.map_mk_disjoint_sym2, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_mk_disjoint_sym2.h3 : ¬∀ {α : Type} (x : α) (xs : List α), (List.map (fun (y : α) => s(x, y)) xs).Disjoint xs.sym2 := fun hc_h => absurd (@hc_h (ℕ) (0) ([0])) (by
  (simp <;> decide))

-- Nat.le_two_mul_of_factorization_centralBinom_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_two_mul_of_factorization_centralBinom_pos.h2 : ¬∀ {p n : ℕ}, p ≤ 2 * n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.descFactorial_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.descFactorial_of_lt.h2 : ¬∀ {n k : ℕ}, n.descFactorial k = 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

