import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Set.IsWF.min_smul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_smul.h5 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : SMul G P] {s : Set G} {t : Set P},
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty → IsOrderedSMul G P := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Nat.instLinearOrder) (Bool.linearOrder) (NSMul.toSMul) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.smul_le_smul_right (1 : ℕ) (2 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.IsWF.min_smul, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_smul.h10 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : SMul G P] [inst_3 : IsOrderedSMul G P]
        {s : Set G} {t : Set P}, s.IsWF → t.IsWF → t.Nonempty → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instLinearOrder) (instSMulOfMul) _ ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Set.IsWF.min_smul, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_smul.h11 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : SMul G P] [inst_3 : IsOrderedSMul G P]
        {s : Set G} {t : Set P}, s.IsWF → t.IsWF → s.Nonempty → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instLinearOrder) (instSMulOfMul) _ ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Finset.smulAntidiagonal_min_smul_min, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.smulAntidiagonal_min_smul_min.h5 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : SMul G P] {s : Set G} {t : Set P},
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty → IsOrderedCancelSMul G P := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Nat.instLinearOrder) (Bool.linearOrder) (NSMul.toSMul) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedSMul.smul_le_smul_right (1 : ℕ) (2 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.antidiagonal_mono_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.antidiagonal_mono_right.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {u : Set α} {hu : u.IsPWO}, u ⊆ t → IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (Bool.false) ({b : Bool | b = Bool.true}) (by
  simp) (by
  rfl)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.PairwiseDisjoint.elim', hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h6.inst : ¬0 = 2 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h6.prem0 : 0 ∈ {n : ℕ | n % 2 = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h6.prem1 : 2 ∈ {n : ℕ | n % 2 = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h6.prem2 : Min.min ((fun (n : ℕ) => n + 1) 0) ((fun (n : ℕ) => n + 1) 2) ≠ ⊥ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h6 : ¬∀ {α ι : Type} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α} {i j : ι},
        i ∈ s → j ∈ s → f i ⊓ f j ≠ ⊥ → i = j := fun hc_h => HypCheckProof.Set.PairwiseDisjoint.elim'.h6.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (Nat.instOrderBot) ({n : ℕ | n % 2 = 0}) (fun (n : ℕ) => n + 1) (0) (2) HypCheckProof.Set.PairwiseDisjoint.elim'.h6.prem0 HypCheckProof.Set.PairwiseDisjoint.elim'.h6.prem1 HypCheckProof.Set.PairwiseDisjoint.elim'.h6.prem2)

-- Set.PairwiseDisjoint.elim', hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h9.inst : ¬1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h9.prem0 : {n : ℕ | n = 0}.PairwiseDisjoint fun (n : ℕ) => n + 1 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h9.prem1 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h9.prem2 : Min.min ((fun (n : ℕ) => n + 1) 1) ((fun (n : ℕ) => n + 1) 0) ≠ ⊥ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h9 : ¬∀ {α ι : Type} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},
        s.PairwiseDisjoint f → ∀ {i j : ι}, j ∈ s → f i ⊓ f j ≠ ⊥ → i = j := fun hc_h => HypCheckProof.Set.PairwiseDisjoint.elim'.h9.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (Nat.instOrderBot) ({n : ℕ | n = 0}) (fun (n : ℕ) => n + 1) HypCheckProof.Set.PairwiseDisjoint.elim'.h9.prem0 (1) (0) HypCheckProof.Set.PairwiseDisjoint.elim'.h9.prem1 HypCheckProof.Set.PairwiseDisjoint.elim'.h9.prem2)

-- Set.PairwiseDisjoint.elim', hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h10.inst : ¬0 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h10.prem0 : {n : ℕ | n = 0}.PairwiseDisjoint fun (n : ℕ) => n + 1 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h10.prem1 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h10.prem2 : Min.min ((fun (n : ℕ) => n + 1) 0) ((fun (n : ℕ) => n + 1) 1) ≠ ⊥ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.PairwiseDisjoint.elim'.h10 : ¬∀ {α ι : Type} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},
        s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → f i ⊓ f j ≠ ⊥ → i = j := fun hc_h => HypCheckProof.Set.PairwiseDisjoint.elim'.h10.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (Nat.instOrderBot) ({n : ℕ | n = 0}) (fun (n : ℕ) => n + 1) HypCheckProof.Set.PairwiseDisjoint.elim'.h10.prem0 (0) (1) HypCheckProof.Set.PairwiseDisjoint.elim'.h10.prem1 HypCheckProof.Set.PairwiseDisjoint.elim'.h10.prem2)

-- Finsupp.mapRange_comp, hypothesis 8: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finsupp.mapRange_comp.h8.der.{u_1, u_4, u_5, u_6} : ∀ {α : Type u_1} {M : Type u_4} {N : Type u_5} {O : Type u_6} [inst : Zero M] [inst_1 : Zero N] [inst_2 : Zero O]
      (f : N → O) (f₂ : M → N), f₂ 0 = 0 → (f ∘ f₂) 0 = 0 → ∀ (g : α →₀ M), f 0 = 0 := by
  (intros; lia)
theorem HypCheckProof.Finsupp.mapRange_comp.h8.{u_1, u_4, u_5, u_6} : ∀ {α : Type u_1} {M : Type u_4} {N : Type u_5} {O : Type u_6} [inst : Zero M] [inst_1 : Zero N] [inst_2 : Zero O]
      (f : N → O) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0) (g : α →₀ M),
      Finsupp.mapRange (f ∘ f₂) h g =
        Finsupp.mapRange f (HypCheckProof.Finsupp.mapRange_comp.h8.der f f₂ hf₂ h g) (Finsupp.mapRange f₂ hf₂ g) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Finsupp.mapRange_comp hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 (@HypCheckProof.Finsupp.mapRange_comp.h8.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11) hc_x8 hc_x9 hc_x10 hc_x11

-- Finsupp.mapRange_comp, hypothesis 11: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finsupp.mapRange_comp.h11.der.{u_1, u_4, u_5, u_6} : ∀ {α : Type u_1} {M : Type u_4} {N : Type u_5} {O : Type u_6} [inst : Zero M] [inst_1 : Zero N] [inst_2 : Zero O]
      (f : N → O), f 0 = 0 → ∀ (f₂ : M → N), f₂ 0 = 0 → ∀ (g : α →₀ M), (f ∘ f₂) 0 = 0 := by
  (intros; lia)
theorem HypCheckProof.Finsupp.mapRange_comp.h11.{u_1, u_4, u_5, u_6} : ∀ {α : Type u_1} {M : Type u_4} {N : Type u_5} {O : Type u_6} [inst : Zero M] [inst_1 : Zero N] [inst_2 : Zero O]
      (f : N → O) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (g : α →₀ M),
      Finsupp.mapRange (f ∘ f₂) (HypCheckProof.Finsupp.mapRange_comp.h11.der f hf f₂ hf₂ g) g =
        Finsupp.mapRange f hf (Finsupp.mapRange f₂ hf₂ g) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @Finsupp.mapRange_comp hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 (@HypCheckProof.Finsupp.mapRange_comp.h11.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11) hc_x11

-- Set.bijOn_image_image, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.bijOn_image_image.h10 : ¬∀ {α β γ δ : Type} {s : Set α} {t : Set β} {f : α → β} {p₁ : α → γ} {p₂ : β → δ} {g : γ → δ},
        Set.BijOn f s t → Set.InjOn g (p₁ '' s) → Set.BijOn g (p₁ '' s) (p₂ '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- Set.bijOn_image_image, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.bijOn_image_image.h11 : ¬∀ {α β γ δ : Type} {s : Set α} {t : Set β} {f : α → β} {p₁ : α → γ} {p₂ : β → δ} {g : γ → δ},
        (∀ (a : α), p₂ (f a) = g (p₁ a)) → Set.InjOn g (p₁ '' s) → Set.BijOn g (p₁ '' s) (p₂ '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- DFinsupp.mapRange_comp, hypothesis 9: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.DFinsupp.mapRange_comp.h9.der.{u, v, v₁, v₂} : ∀ {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [inst : (i : ι) → Zero (β i)]
      [inst_1 : (i : ι) → Zero (β₁ i)] [inst_2 : (i : ι) → Zero (β₂ i)] (f : (i : ι) → β₁ i → β₂ i)
      (f₂ : (i : ι) → β i → β₁ i),
      (∀ (i : ι), f₂ i 0 = 0) → (∀ (i : ι), (f i ∘ f₂ i) 0 = 0) → ∀ (g : Π₀ (i : ι), β i) (i : ι), f i 0 = 0 := by
  (intros; simp_all; done)
theorem HypCheckProof.DFinsupp.mapRange_comp.h9.{u, v, v₁, v₂} : ∀ {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [inst : (i : ι) → Zero (β i)]
      [inst_1 : (i : ι) → Zero (β₁ i)] [inst_2 : (i : ι) → Zero (β₂ i)] (f : (i : ι) → β₁ i → β₂ i)
      (f₂ : (i : ι) → β i → β₁ i) (hf₂ : ∀ (i : ι), f₂ i 0 = 0) (h : ∀ (i : ι), (f i ∘ f₂ i) 0 = 0) (g : Π₀ (i : ι), β i),
      DFinsupp.mapRange (fun (i : ι) => f i ∘ f₂ i) h g =
        DFinsupp.mapRange f (HypCheckProof.DFinsupp.mapRange_comp.h9.der f f₂ hf₂ h g) (DFinsupp.mapRange f₂ hf₂ g) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @DFinsupp.mapRange_comp hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 (@HypCheckProof.DFinsupp.mapRange_comp.h9.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11) hc_x9 hc_x10 hc_x11

-- DFinsupp.mapRange_comp, hypothesis 11: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.DFinsupp.mapRange_comp.h11.der.{u, v, v₁, v₂} : ∀ {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [inst : (i : ι) → Zero (β i)]
      [inst_1 : (i : ι) → Zero (β₁ i)] [inst_2 : (i : ι) → Zero (β₂ i)] (f : (i : ι) → β₁ i → β₂ i)
      (f₂ : (i : ι) → β i → β₁ i),
      (∀ (i : ι), f i 0 = 0) → (∀ (i : ι), f₂ i 0 = 0) → ∀ (g : Π₀ (i : ι), β i) (i : ι), (f i ∘ f₂ i) 0 = 0 := by
  (intros; simp_all; done)
theorem HypCheckProof.DFinsupp.mapRange_comp.h11.{u, v, v₁, v₂} : ∀ {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [inst : (i : ι) → Zero (β i)]
      [inst_1 : (i : ι) → Zero (β₁ i)] [inst_2 : (i : ι) → Zero (β₂ i)] (f : (i : ι) → β₁ i → β₂ i)
      (f₂ : (i : ι) → β i → β₁ i) (hf : ∀ (i : ι), f i 0 = 0) (hf₂ : ∀ (i : ι), f₂ i 0 = 0) (g : Π₀ (i : ι), β i),
      DFinsupp.mapRange (fun (i : ι) => f i ∘ f₂ i) (HypCheckProof.DFinsupp.mapRange_comp.h11.der f f₂ hf hf₂ g) g =
        DFinsupp.mapRange f hf (DFinsupp.mapRange f₂ hf₂ g) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact @DFinsupp.mapRange_comp hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 (@HypCheckProof.DFinsupp.mapRange_comp.h11.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11) hc_x11

-- List.not_of_mem_foldl_argAux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_of_mem_foldl_argAux.h4 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] {l : List α},
        IsTrans α r → ∀ {a m : α} {o : Option α}, a ∈ l → m ∈ List.foldl (List.argAux r) o l → ¬r a m := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (Nat.decLe) ([0]) ((@IsTrans.mk (Nat) (fun (a b : Nat) => @LE.le Nat instLENat a b) (by (try dsimp only);   (intros; omega)))) (0) (0) (Option.none) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.not_of_mem_foldl_argAux, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_of_mem_foldl_argAux.h9 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] {l : List α},
        Std.Irrefl r → IsTrans α r → ∀ {a m : α} {o : Option α}, m ∈ List.foldl (List.argAux r) o l → ¬r a m := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([]) ((@Std.Irrefl.mk (Nat) (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (by (try dsimp only);   (intros; omega)))) ((@IsTrans.mk (Nat) (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (by (try dsimp only);   (intros; omega)))) (0) (1) (Option.some 1) (by
  decide)) (by
  decide +kernel)

-- List.not_of_mem_foldl_argAux, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_of_mem_foldl_argAux.h10 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] {l : List α},
        Std.Irrefl r → IsTrans α r → ∀ {a m : α} {o : Option α}, a ∈ l → ¬r a m := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([0]) ((@Std.Irrefl.mk (Nat) (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (by (try dsimp only);   (intros; omega)))) ((@IsTrans.mk (Nat) (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (by (try dsimp only);   (intros; omega)))) (0) (1) (Option.none) (by
  decide)) (by
  decide +kernel)

-- Set.IsWF.min_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_add.h5 : ¬∀ {α : Type} {s t : Set α} [inst : AddCommMonoid α] [inst_1 : LinearOrder α],
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty → IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.linearOrder) (by
  simp) (by
  simp) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.IsWF.min_add, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_add.h8 : ¬∀ {α : Type} {s t : Set α} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [inst : IsOrderedCancelAddMonoid α],
        s.IsWF → t.IsWF → t.Nonempty → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (Nat.instAddCommMonoid) (Nat.instLinearOrder) _ (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Set.IsWF.min_add, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_add.h9 : ¬∀ {α : Type} {s t : Set α} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [inst : IsOrderedCancelAddMonoid α],
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (Nat.instAddCommMonoid) (Nat.instLinearOrder) _ (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- List.TFAE.out, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.TFAE.out.h6 : ¬∀ {l : List Prop},
        l.TFAE →
          ∀ (i j : ℕ) {a b : Prop},
            autoParam (l[j - 1]? = Option.some b) List.TFAE.out._auto_3 →
              autoParam (i ≠ 0) List.TFAE.out._auto_5 → autoParam (j ≠ 0) List.TFAE.out._auto_7 → (a ↔ b) := fun hc_h => absurd (@hc_h ([True]) (by
  simp) (1) (1) (False) (True) (by
  rfl) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.TFAE.out, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.TFAE.out.h7 : ¬∀ {l : List Prop},
        l.TFAE →
          ∀ (i j : ℕ) {a b : Prop},
            autoParam (l[i - 1]? = Option.some a) List.TFAE.out._auto_1 →
              autoParam (i ≠ 0) List.TFAE.out._auto_5 → autoParam (j ≠ 0) List.TFAE.out._auto_7 → (a ↔ b) := fun hc_h => absurd (@hc_h ([True]) (by
  simp) (1) (1) (True) (False) (by
  rfl) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.Finite.exists_between, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.exists_between.h2 : ¬∀ {α : Type} [inst : LinearOrder α] {s t : Set α},
        s.Finite →
          s.Nonempty → t.Finite → t.Nonempty → (∀ x ∈ s, ∀ y ∈ t, x < y) → ∃ (b : α), (∀ x ∈ s, x < b) ∧ ∀ y ∈ t, b < y := fun hc_h => absurd (@hc_h (Bool) (Bool.linearOrder) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (by
  simp) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.forall, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.forall.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.Pairwise R l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, b ∈ l → a ≠ b → R a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0, 1]) (by
  decide) (1) (by
  decide) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.forall.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} [inst : Std.Symm R],
        List.Pairwise R l → ∀ ⦃a b : α⦄, b ∈ l → a ≠ b → R a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) ([0]) _ (by
  decide) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.forall, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.forall.h8 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} [inst : Std.Symm R],
        List.Pairwise R l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, a ≠ b → R a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) ([0]) _ (by
  decide) (0) (by
  decide) (1) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.forall, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.forall.h9 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} [inst : Std.Symm R],
        List.Pairwise R l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, b ∈ l → R a b := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) ([Bool.false]) _ (by
  decide) (Bool.false) (by
  decide) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Rat.mk'_mul_mk', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk'_mul_mk'.h4 : ¬∀ (n₁ n₂ : ℤ) (d₁ d₂ : ℕ),
        d₂ ≠ 0 → n₁.natAbs.Coprime d₁ → n₂.natAbs.Coprime d₂ → n₁.natAbs.Coprime d₂ → n₂.natAbs.Coprime d₁ → d₁ ≠ 0 := fun hc_h => absurd (@hc_h (1) (1) (0) (1) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Rat.mk'_mul_mk', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk'_mul_mk'.h5 : ¬∀ (n₁ n₂ : ℤ) (d₁ d₂ : ℕ),
        d₁ ≠ 0 → n₁.natAbs.Coprime d₁ → n₂.natAbs.Coprime d₂ → n₁.natAbs.Coprime d₂ → n₂.natAbs.Coprime d₁ → d₂ ≠ 0 := fun hc_h => absurd (@hc_h (1) (1) (1) (0) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Rat.mk'_mul_mk', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk'_mul_mk'.h6 : ¬∀ (n₁ n₂ : ℤ) (d₁ d₂ : ℕ),
        d₁ ≠ 0 → d₂ ≠ 0 → n₂.natAbs.Coprime d₂ → n₁.natAbs.Coprime d₂ → n₂.natAbs.Coprime d₁ → n₁.natAbs.Coprime d₁ := fun hc_h => absurd (@hc_h (0) (1) (2) (1) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Rat.mk'_mul_mk', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk'_mul_mk'.h7 : ¬∀ (n₁ n₂ : ℤ) (d₁ d₂ : ℕ),
        d₁ ≠ 0 → d₂ ≠ 0 → n₁.natAbs.Coprime d₁ → n₁.natAbs.Coprime d₂ → n₂.natAbs.Coprime d₁ → n₂.natAbs.Coprime d₂ := fun hc_h => absurd (@hc_h (1) (0) (1) (2) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Rat.mk'_mul_mk', hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk'_mul_mk'.h8 : ¬∀ (n₁ n₂ : ℤ) (d₁ d₂ : ℕ),
        d₁ ≠ 0 → d₂ ≠ 0 → n₁.natAbs.Coprime d₁ → n₂.natAbs.Coprime d₂ → n₂.natAbs.Coprime d₁ → n₁.natAbs.Coprime d₂ := fun hc_h => absurd (@hc_h (0) (1) (1) (2) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Rat.mk'_mul_mk', hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk'_mul_mk'.h9 : ¬∀ (n₁ n₂ : ℤ) (d₁ d₂ : ℕ),
        d₁ ≠ 0 → d₂ ≠ 0 → n₁.natAbs.Coprime d₁ → n₂.natAbs.Coprime d₂ → n₁.natAbs.Coprime d₂ → n₂.natAbs.Coprime d₁ := fun hc_h => absurd (@hc_h (1) (0) (2) (1) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.pairwise_append_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_append_of_mem.h8 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ : List α} {a b : α} [inst : Std.Symm R] [inst : IsTrans α R],
        b ∈ l₂ → (List.Pairwise R (l₁ ++ l₂) ↔ R a b ∧ List.Pairwise R l₁ ∧ List.Pairwise R l₂) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) ([]) ([Bool.false]) (Bool.false) (Bool.false) _ _ (by
  decide)) (by
  decide +kernel)

-- List.pairwise_append_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_append_of_mem.h9 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ : List α} {a b : α} [inst : Std.Symm R] [inst : IsTrans α R],
        a ∈ l₁ → (List.Pairwise R (l₁ ++ l₂) ↔ R a b ∧ List.Pairwise R l₁ ∧ List.Pairwise R l₂) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) ([Bool.false]) ([]) (Bool.false) (Bool.false) _ _ (by
  decide)) (by
  decide +kernel)

-- List.index_of_argmin, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.index_of_argmin.h7.inst : ¬List.idxOf 1 [0] ≤ List.idxOf 0 [0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.index_of_argmin.h7.prem0 : 0 ∈ [0] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.index_of_argmin.h7.prem1 : (fun (n : ℕ) => n + 1) 0 ≤ (fun (n : ℕ) => n + 1) 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.index_of_argmin.h7 : ¬∀ {α β : Type} [inst : LinearOrder β] {f : α → β} [inst_1 : DecidableEq α] {l : List α} {m a : α},
        a ∈ l → f a ≤ f m → List.idxOf m l ≤ List.idxOf a l := fun hc_h => HypCheckProof.List.index_of_argmin.h7.inst (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun (n : ℕ) => n + 1) (instDecidableEqNat) ([0]) (1) (0) HypCheckProof.List.index_of_argmin.h7.prem0 HypCheckProof.List.index_of_argmin.h7.prem1)

-- List.index_of_argmin, hypothesis 9: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.index_of_argmin.h9.gneg.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder β] {f : α → β} [inst_1 : DecidableEq α] {l : List α} {m : α},
      m ∈ List.argmin f l → ∀ {a : α}, a ∉ l → f a ≤ f m → List.idxOf m l ≤ List.idxOf a l := by
  (intros; grind)
theorem HypCheckProof.List.index_of_argmin.h9.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder β] {f : α → β} [inst_1 : DecidableEq α] {l : List α} {m : α},
      m ∈ List.argmin f l → ∀ {a : α}, f a ≤ f m → List.idxOf m l ≤ List.idxOf a l := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @List.index_of_argmin hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.List.index_of_argmin.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)

-- List.index_of_argmin, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.index_of_argmin.h10 : ¬∀ {α β : Type} [inst : LinearOrder β] {f : α → β} [inst_1 : DecidableEq α] {l : List α} {m : α},
        m ∈ List.argmin f l → ∀ {a : α}, a ∈ l → List.idxOf m l ≤ List.idxOf a l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun n => n + 1 : ℕ → ℕ) (instDecidableEqNat) ([1, 0]) (0) (by
  decide) (1) (by
  decide)) (by
  decide +kernel)

-- Ordnode.balanceL_eq_balance', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balanceL_eq_balance'.h6 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced →
          r.Balanced →
            r.Sized →
              ((∃ (l' : ℕ), Ordnode.Raised l' l.size ∧ Ordnode.BalancedSz l' r.size) ∨
                  ∃ (r' : ℕ), Ordnode.Raised r.size r' ∧ Ordnode.BalancedSz l.size r') →
                l.balanceL x r = l.balance' x r := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.size_balanceL, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.size_balanceL.h6 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced →
          r.Balanced →
            r.Sized →
              ((∃ (l' : ℕ), Ordnode.Raised l' l.size ∧ Ordnode.BalancedSz l' r.size) ∨
                  ∃ (r' : ℕ), Ordnode.Raised r.size r' ∧ Ordnode.BalancedSz l.size r') →
                (l.balanceL x r).size = l.size + r.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Ordnode.size_balanceL, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.size_balanceL.h7 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced →
          r.Balanced →
            l.Sized →
              ((∃ (l' : ℕ), Ordnode.Raised l' l.size ∧ Ordnode.BalancedSz l' r.size) ∨
                  ∃ (r' : ℕ), Ordnode.Raised r.size r' ∧ Ordnode.BalancedSz l.size r') →
                (l.balanceL x r).size = l.size + r.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 1 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul.h8 : ¬∀ {p : ℕ}, Nat.Prime p → ∀ {m n k l : ℕ}, p ^ k ∣ m → p ^ l ∣ n → p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n := fun hc_h => absurd (@hc_h (2) (by
  decide) (1) (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ofNat_le_cast, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofNat_le_cast.h8 : ¬∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α] [inst_3 : ZeroLEOneClass α]
        [inst : CharZero α] {m : ℕ} {n : ℕ}, m.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ _ (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Forall₂.mp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.mp.h8 : ¬∀ {α β : Type} {R S Q : α → β → Prop},
        (∀ (a : α) (b : β), Q a b → R a b → S a b) →
          ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (by
  omega) ([0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Forall₂.mp, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.mp.h9 : ¬∀ {α β : Type} {R S Q : α → β → Prop},
        (∀ (a : α) (b : β), Q a b → R a b → S a b) →
          ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ Q l₁ l₂ → List.Forall₂ S l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a ≤ b : ℕ → ℕ → Prop) (by
  simp) ([0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- Finset.isPWO_support_vaddAntidiagonal, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isPWO_support_vaddAntidiagonal.h5 : ¬∀ {G P : Type} [inst : VAdd G P] [inst_1 : PartialOrder G] [inst_2 : PartialOrder P] {s : Set G} {t : Set P},
        s.IsPWO → t.IsPWO → IsOrderedCancelVAdd G P := fun hc_h => absurd (@hc_h (Bool) (Bool) (instVAddOfAdd) (Bool.instPartialOrder) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedVAdd.vadd_le_vadd_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.IsChain.induction, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.induction.h5.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.induction.h5.prem0 : List.IsChain (fun (a b : ℕ) => a < b) [0, 1] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.induction.h5.prem1 : ∀ (lne : [0, 1] ≠ []), (fun (n : ℕ) => n = 0) ([0, 1].head lne) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.induction.h5.prem2 : 1 ∈ [0, 1] := by
  decide
theorem HypCheckProof.List.IsChain.induction.h5 : ¬∀ {α : Type} {r : α → α → Prop} (p : α → Prop) (l : List α),
        List.IsChain r l → (∀ (lne : l ≠ []), p (l.head lne)) → ∀ i ∈ l, p i := fun hc_h => HypCheckProof.List.IsChain.induction.h5.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (fun (n : ℕ) => n = 0) ([0, 1]) HypCheckProof.List.IsChain.induction.h5.prem0 HypCheckProof.List.IsChain.induction.h5.prem1 (1) HypCheckProof.List.IsChain.induction.h5.prem2)

-- List.IsChain.induction, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.induction.h6 : ¬∀ {α : Type} {r : α → α → Prop} (p : α → Prop) (l : List α),
        List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p x → p y) → ∀ i ∈ l, p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun _ => False : ℕ → Prop) ([0]) (by
  decide) (by
  simp) (0) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.induction, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.induction.h8.inst : ¬(fun (x : ℕ) => False) 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.induction.h8.prem0 : List.IsChain (fun (a b : ℕ) => a < b) [] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.induction.h8.prem1 : ∀ ⦃x y : ℕ⦄, x < y → False → (fun (x : ℕ) => False) y := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.induction.h8.prem2 : ∀ (lne : [] ≠ []), (fun (x : ℕ) => False) ([].head lne) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.induction.h8 : ¬∀ {α : Type} {r : α → α → Prop} (p : α → Prop) (l : List α),
        List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p x → p y) → (∀ (lne : l ≠ []), p (l.head lne)) → ∀ (i : α), p i := fun hc_h => HypCheckProof.List.IsChain.induction.h8.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (fun (x : ℕ) => False) ([]) HypCheckProof.List.IsChain.induction.h8.prem0 HypCheckProof.List.IsChain.induction.h8.prem1 HypCheckProof.List.IsChain.induction.h8.prem2 (0))

-- Finset.swap_mem_addAntidiagonal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.swap_mem_addAntidiagonal.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {x : α × α}, IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (Bool.false) ((Bool.false, Bool.false))) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.swap_mem_mulAntidiagonal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.swap_mem_mulAntidiagonal.h3 : ¬∀ {α : Type} [inst : CommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {x : α × α}, IsOrderedCancelMonoid α := fun hc_h => absurd (@hc_h (Bool) (BooleanRing.toCommRing.toCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (Bool.false) ((Bool.false, Bool.false))) (by
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

-- Set.MapsTo.mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.mono.h7 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β}, s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂ t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  rfl) (by
  rfl)) (by
  simp)

-- Set.MapsTo.mono, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.mono.h8 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β}, Set.MapsTo f s₁ t₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂ t₂ := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  simp) (by
  rfl)) (by
  simp)

-- Set.MapsTo.mono, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.mono.h9 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β}, Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → Set.MapsTo f s₂ t₂ := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp) (by
  rfl)) (by
  simp)

-- Int.le_zpow_iff_clog_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_zpow_iff_clog_le.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {x : ℤ} {r : R}, 0 < r → (r ≤ ↑b ^ x ↔ Int.clog b r ≤ x) := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.le_zpow_iff_clog_le, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_zpow_iff_clog_le.h9 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ}, 1 < b → ∀ {x : ℤ} {r : R}, r ≤ ↑b ^ x ↔ Int.clog b r ≤ x := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (by
  decide) (-1) (0)) (by
  decide +kernel)

-- Int.clog_mono_right, hypothesis 8: necessary
/- FAILED: 4:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 21:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 4:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 21:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:53: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 24:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:53: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 24:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.clog_mono_right.h8 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {r₁ r₂ : R}, r₁ ≤ r₂ → Int.clog b r₁ ≤ Int.clog b r₂ := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (0) (1 / 2) (by
  decide)) (by
  decide +kernel)
-/

-- Int.zpow_le_iff_le_log, hypothesis 6: necessary
/- FAILED: 4:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 46:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 4:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 46:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:78: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 50:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:78: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 50:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.zpow_le_iff_le_log.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {x : ℤ} {r : R}, 0 < r → (↑b ^ x ≤ r ↔ x ≤ Int.log b r) := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (0) (0) (1 / 2) (by
  decide)) (by
  decide +kernel)
-/

-- Int.zpow_le_iff_le_log, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.zpow_le_iff_le_log.h9 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ}, 1 < b → ∀ {x : ℤ} {r : R}, ↑b ^ x ≤ r ↔ x ≤ Int.log b r := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (by
  decide) (0) (0)) (by
  decide +kernel)

-- List.NodupKeys.eq_of_fst_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.NodupKeys.eq_of_fst_eq.h6 : ¬∀ {α : Type} {β : α → Type} {l : List (Sigma β)}, l.NodupKeys → ∀ {s s' : Sigma β}, s' ∈ l → s.fst = s'.fst → s = s' := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp) ((⟨0, 1⟩ : (_ : ℕ) × ℕ)) ((⟨0, 0⟩ : (_ : ℕ) × ℕ)) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- List.NodupKeys.eq_of_fst_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.NodupKeys.eq_of_fst_eq.h7 : ¬∀ {α : Type} {β : α → Type} {l : List (Sigma β)}, l.NodupKeys → ∀ {s s' : Sigma β}, s ∈ l → s.fst = s'.fst → s = s' := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp) ((⟨0, 0⟩ : (_ : ℕ) × ℕ)) ((⟨0, 1⟩ : (_ : ℕ) × ℕ)) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- ENat.biSup_add_biSup_le', hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.biSup_add_biSup_le'.h9 : ¬∀ {ι κ : Type} {f : ι → ℕ∞} {a : ℕ∞} {p : ι → Prop} {q : κ → Prop},
        (∃ (i : ι), p i) →
          (∃ (j : κ), q j) → ∀ {g : κ → ℕ∞}, (⨆ (i : ι), ⨆ (_ : p i), f i) + ⨆ (j : κ), ⨆ (_ : q j), g j ≤ a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => 0) (0) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp) (by
  simp) (fun (a : ℕ) => 1)) (by
  simp)

-- Set.PairwiseDisjoint.insert_of_notMem, hypothesis 8: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.PairwiseDisjoint.insert_of_notMem.h8.gneg.{u_1, u_4} : ∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},
      s.PairwiseDisjoint f → ∀ {i : ι}, ¬i ∉ s → (∀ j ∈ s, Disjoint (f i) (f j)) → (Insert.insert i s).PairwiseDisjoint f := by
  (intros; simp_all; done)
theorem HypCheckProof.Set.PairwiseDisjoint.insert_of_notMem.h8.{u_1, u_4} : ∀ {α : Type u_1} {ι : Type u_4} [inst : PartialOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},
      s.PairwiseDisjoint f → ∀ {i : ι}, (∀ j ∈ s, Disjoint (f i) (f j)) → (Insert.insert i s).PairwiseDisjoint f := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9
  exact Classical.byCases (fun hc_h => @Set.PairwiseDisjoint.insert_of_notMem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9) (fun hc_hn => @HypCheckProof.Set.PairwiseDisjoint.insert_of_notMem.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9)

-- Set.MapsTo.prodMap, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.prodMap.h10 : ¬∀ {α₁ α₂ β₁ β₂ : Type} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂},
        Set.MapsTo f₂ s₂ t₂ → Set.MapsTo (fun (x : α₁ × α₂) => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.MapsTo.prodMap, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.prodMap.h11 : ¬∀ {α₁ α₂ β₁ β₂ : Type} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂},
        Set.MapsTo f₁ s₁ t₁ → Set.MapsTo (fun (x : α₁ × α₂) => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.EqOn.comp_left₂, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.comp_left₂.h11 : ¬∀ {α β δ γ : Type} {op : α → β → δ} {a₁ a₂ : γ → α} {b₁ b₂ : γ → β} {s : Set γ},
        Set.EqOn a₁ a₂ s → Set.EqOn (fun (x : γ) => op (a₁ x) (b₁ x)) (fun (x : γ) => op (a₂ x) (b₂ x)) s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.EqOn.left_of_eqOn_prodMap, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.left_of_eqOn_prodMap.h10 : ¬∀ {α β γ δ : Type} {s : Set α} {t : Set β} {f f' : α → γ} {g g' : β → δ}, t.Nonempty → Set.EqOn f f' s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.SurjOn.prodMap, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.prodMap.h10 : ¬∀ {α₁ α₂ β₁ β₂ : Type} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂},
        Set.SurjOn f₂ s₂ t₂ → Set.SurjOn (fun (x : α₁ × α₂) => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.SurjOn.prodMap, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.prodMap.h11 : ¬∀ {α₁ α₂ β₁ β₂ : Type} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂},
        Set.SurjOn f₁ s₁ t₁ → Set.SurjOn (fun (x : α₁ × α₂) => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.EqOn.right_of_eqOn_prodMap, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.right_of_eqOn_prodMap.h10 : ¬∀ {α β γ δ : Type} {s : Set α} {t : Set β} {f f' : α → γ} {g g' : β → δ}, s.Nonempty → Set.EqOn g g' t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.SurjOn.image_invFunOn_image_of_subset, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.image_invFunOn_image_of_subset.h7 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} [inst : Nonempty α] {r : Set β},
        r ⊆ t → f '' Function.invFunOn f s '' r = r := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) _ ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Int.zpow_pred_clog_lt_self, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.zpow_pred_clog_lt_self.h7 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {r : R}, 0 < r → ↑b ^ (Int.clog b r - 1) < r := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.zpow_pred_clog_lt_self, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.zpow_pred_clog_lt_self.h8 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {r : R}, 1 < b → ↑b ^ (Int.clog b r - 1) < r := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (0) (by
  decide)) (by
  decide +kernel)

-- List.Sublist.orderedInsert_sublist, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.orderedInsert_sublist.h7 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : IsTrans α r] {as bs : List α} (x : α),
        List.Pairwise r bs → (List.orderedInsert r x as).Sublist (List.orderedInsert r x bs) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ ([0]) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- List.NodupKeys.eq_of_mk_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.NodupKeys.eq_of_mk_mem.h7 : ¬∀ {α : Type} {β : α → Type} {a : α} {b b' : β a} {l : List (Sigma β)}, l.NodupKeys → (⟨a, b'⟩ : Sigma β) ∈ l → b = b' := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (0) (1) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- List.NodupKeys.eq_of_mk_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.NodupKeys.eq_of_mk_mem.h8 : ¬∀ {α : Type} {β : α → Type} {a : α} {b b' : β a} {l : List (Sigma β)}, l.NodupKeys → (⟨a, b⟩ : Sigma β) ∈ l → b = b' := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (0) (0) (1) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Set.surjOn_iInter, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.surjOn_iInter.h7 : ¬∀ {α β ι : Type} [inst : Nonempty ι] {s : ι → Set α} {t : Set β} {f : α → β},
        Set.InjOn f (⋃ (i : ι), s i) → Set.SurjOn f (⋂ (i : ι), s i) t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) _ (fun (a : ℕ) => {n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.prev_cons_cons_of_ne', hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.prev_cons_cons_of_ne'.h6.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y z : α), x ≠ y → x = z → x ∈ y :: z :: l := by
  (intros; simp_all; done)
theorem HypCheckProof.List.prev_cons_cons_of_ne'.h6.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y z : α) (hy : x ≠ y) (hz : x = z),
      (y :: z :: l).prev x (HypCheckProof.List.prev_cons_cons_of_ne'.h6.der l x y z hy hz) = y := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @List.prev_cons_cons_of_ne' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.prev_cons_cons_of_ne'.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7) hc_x6 hc_x7

-- List.prev_cons_cons_of_ne', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_cons_cons_of_ne'.h7 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y z : α) (h : x ∈ y :: z :: l), x = z → (y :: z :: l).prev x h = y := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([1]) _ (0) (0) hc_k0 rfl) (by
  decide +kernel)

-- List.prev_cons_cons_of_ne', hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_cons_cons_of_ne'.h8 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y z : α) (h : x ∈ y :: z :: l), x ≠ y → (y :: z :: l).prev x h = y := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (instDecidableEqNat) ([0]) (0) (1) (2) hc_k0 hc_k1) (by
  decide +kernel)

-- Quot.map₂_mk, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quot.map₂_mk.h8 : ¬∀ {α β γ : Type} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : α → β → γ),
        (∀ (a : α) (b₁ b₂ : β), s b₁ b₂ → t (f a b₁) (f a b₂)) →
          ∀ (a : α) (b : β) (a₁ a₂ : α) (b : β), r a₁ a₂ → t (f a₁ b) (f a₂ b) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (fun _ _ => True : Bool → Bool → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun (a : Bool) (n : ℕ) => n + 1) (by
  simp) (Bool.false) (0)) (by
  simp)

-- List.Perm.eq_of_pairwise', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.eq_of_pairwise'.h7 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Antisymm r] {l₁ l₂ : List α},
        List.Pairwise r l₁ → List.Pairwise r l₂ → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- EReal.sub_lt_sub_of_lt_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_lt_sub_of_lt_of_le.h4 : ¬∀ {x y z t : EReal}, z ≤ t → z ≠ ⊥ → t ≠ ⊤ → x - t < y - z := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  rfl) (by
  decide) (by
  decide)) (by
  simp)

-- Nat.ofDigits_inj_of_len_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_inj_of_len_eq.h4 : ¬∀ {b : ℕ},
        1 < b → ∀ {L1 L2 : List ℕ}, (∀ l ∈ L1, l < b) → (∀ l ∈ L2, l < b) → Nat.ofDigits b L1 = Nat.ofDigits b L2 → L1 = L2 := fun hc_h => absurd (@hc_h (2) (by
  decide) ([]) ([0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ofDigits_inj_of_len_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_inj_of_len_eq.h7 : ¬∀ {b : ℕ}, 1 < b → ∀ {L1 L2 : List ℕ}, L1.length = L2.length → (∀ l ∈ L1, l < b) → (∀ l ∈ L2, l < b) → L1 = L2 := fun hc_h => absurd (@hc_h (2) (by
  decide) ([0]) ([1]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- EReal.add_lt_add_of_lt_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_lt_add_of_lt_of_le.h4 : ¬∀ {x y z t : EReal}, z ≤ t → z ≠ ⊥ → t ≠ ⊤ → x + z < y + t := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  rfl) (by
  decide) (by
  decide)) (by
  simp)

-- Subtype.map_comp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.map_comp.h8 : ¬∀ {α β γ : Type} {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : Subtype p} (f : α → β) (g : β → γ),
        (∀ (a : β), q a → r (g a)) → ∀ (a : α), p a → q (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 })) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Subtype.map_comp, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.map_comp.h10 : ¬∀ {α β γ : Type} {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : Subtype p} (f : α → β),
        (∀ (a : α), p a → q (f a)) → ∀ (g : β → γ) (a : β), q a → r (g a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 })) (fun _ => 0 : ℕ → ℕ) (by
  simp) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Nat.not_ofNat_lt_one, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_ofNat_lt_one.h7 : ¬∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α] [inst_3 : ZeroLEOneClass α]
        [inst : CharZero α] {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.ModEq.of_div, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.of_div.h4 : ¬∀ {m a b c : ℕ}, c ∣ a → c ∣ b → c ∣ m → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.of_div, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.of_div.h5 : ¬∀ {m a b c : ℕ}, a / c ≡ b / c [MOD m / c] → c ∣ b → c ∣ m → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.of_div, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.of_div.h6 : ¬∀ {m a b c : ℕ}, a / c ≡ b / c [MOD m / c] → c ∣ a → c ∣ m → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.not_ofNat_le_one, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_ofNat_le_one.h7 : ¬∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α] [inst_3 : ZeroLEOneClass α]
        [inst : CharZero α] {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Int.div_le_div_iff_of_dvd_of_pos_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_pos_of_pos.h4 : ¬∀ {a b c d : ℤ}, 0 < d → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ d * a ≤ c * b) := fun hc_h => absurd (@hc_h (0) (0) (-1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_div_iff_of_dvd_of_pos_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_pos_of_pos.h5 : ¬∀ {a b c d : ℤ}, 0 < b → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ d * a ≤ c * b) := fun hc_h => absurd (@hc_h (1) (1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_div_iff_of_dvd_of_pos_of_pos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_pos_of_pos.h6 : ¬∀ {a b c d : ℤ}, 0 < b → 0 < d → d ∣ c → (a / b ≤ c / d ↔ d * a ≤ c * b) := fun hc_h => absurd (@hc_h (1) (2) (0) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Subset.antisymm_of_sortedGT, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_sortedGT.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₂ ⊆ l₁ → l₁.SortedGT → l₂.SortedGT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Subset.antisymm_of_sortedGT, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_sortedGT.h5 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₁.SortedGT → l₂.SortedGT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([]) ([0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Subset.antisymm_of_sortedGT, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_sortedGT.h6 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₂ ⊆ l₁ → l₂.SortedGT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0, 0]) ([0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Subset.antisymm_of_sortedGT, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_sortedGT.h7 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₂ ⊆ l₁ → l₁.SortedGT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([0, 0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Subset.antisymm_of_sortedLT, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_sortedLT.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₂ ⊆ l₁ → l₁.SortedLT → l₂.SortedLT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Subset.antisymm_of_sortedLT, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_sortedLT.h5 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₁.SortedLT → l₂.SortedLT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([]) ([0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Subset.antisymm_of_sortedLT, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_sortedLT.h6 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₂ ⊆ l₁ → l₂.SortedLT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0, 0]) ([0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Subset.antisymm_of_sortedLT, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_sortedLT.h7 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₂ ⊆ l₁ → l₁.SortedLT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([0, 0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Rat.sq_mul_squarefree_unique, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.sq_mul_squarefree_unique.h2 : ¬∀ {d₁ d₂ : ℤ}, Squarefree d₂ → ∀ (r₁ r₂ : ℚ), r₁ ≠ 0 → r₁ ^ 2 * ↑d₁ = r₂ ^ 2 * ↑d₂ → d₁ = d₂ := fun hc_h => absurd (@hc_h (0) (1) (by
  simp) (1) (0) (by
  decide) (by
  decide +kernel)) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_neg_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_neg_of_pos.h4 : ¬∀ {a b c d : ℤ}, 0 < d → b ∣ a → d ∣ c → (a / b < c / d ↔ c * b < d * a) := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_neg_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_neg_of_pos.h5 : ¬∀ {a b c d : ℤ}, b < 0 → b ∣ a → d ∣ c → (a / b < c / d ↔ c * b < d * a) := fun hc_h => absurd (@hc_h (1) (-1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_neg_of_pos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_neg_of_pos.h6 : ¬∀ {a b c d : ℤ}, b < 0 → 0 < d → d ∣ c → (a / b < c / d ↔ c * b < d * a) := fun hc_h => absurd (@hc_h (1) (-2) (0) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_neg_of_pos, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_neg_of_pos.h7 : ¬∀ {a b c d : ℤ}, b < 0 → 0 < d → b ∣ a → (a / b < c / d ↔ c * b < d * a) := fun hc_h => absurd (@hc_h (0) (-1) (1) (2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.one_lt_ofNat, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.one_lt_ofNat.h7 : ¬∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α] [inst_3 : ZeroLEOneClass α]
        [inst : CharZero α] {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Disjoint.ne_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.ne_of_mem.h3 : ¬∀ {α : Type} {s t : Set α} ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- Disjoint.ne_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.ne_of_mem.h5 : ¬∀ {α : Type} {s t : Set α}, Disjoint s t → ∀ ⦃a b : α⦄, b ∈ t → a ≠ b := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Disjoint.ne_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.ne_of_mem.h7 : ¬∀ {α : Type} {s t : Set α}, Disjoint s t → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, a ≠ b := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (0) (by
  decide) (0)) (by
  decide +kernel)

-- DFinsupp.instCanonicallyOrderedAddOfAddLeftMono, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.DFinsupp.instCanonicallyOrderedAddOfAddLeftMono.h7.gneg.{u_1, u_2} : ∀ {ι : Type u_1} (α : ι → Type u_2) [inst : (i : ι) → AddCommMonoid (α i)] [inst_1 : (i : ι) → PartialOrder (α i)]
      [inst_2 : ∀ (i : ι), CanonicallyOrderedAdd (α i)] [inst_3 : (i : ι) → Sub (α i)]
      [inst_4 : ∀ (i : ι), OrderedSub (α i)], (¬∀ (i : ι), AddLeftMono (α i)) → CanonicallyOrderedAdd (Π₀ (i : ι), α i) := by
  (intros; infer_instance)
theorem HypCheckProof.DFinsupp.instCanonicallyOrderedAddOfAddLeftMono.h7.{u_1, u_2} : ∀ {ι : Type u_1} (α : ι → Type u_2) [inst : (i : ι) → AddCommMonoid (α i)] [inst_1 : (i : ι) → PartialOrder (α i)]
      [inst_2 : ∀ (i : ι), CanonicallyOrderedAdd (α i)] [inst_3 : (i : ι) → Sub (α i)]
      [inst_4 : ∀ (i : ι), OrderedSub (α i)], CanonicallyOrderedAdd (Π₀ (i : ι), α i) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @DFinsupp.instCanonicallyOrderedAddOfAddLeftMono hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h) (fun hc_hn => @HypCheckProof.DFinsupp.instCanonicallyOrderedAddOfAddLeftMono.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.DFinsupp.instCanonicallyOrderedAddOfAddLeftMono.h7.derivable.{u_1, u_2} : ∀ {ι : Type u_1} (α : ι → Type u_2) [inst : (i : ι) → AddCommMonoid (α i)] [inst_1 : (i : ι) → PartialOrder (α i)]
      [inst_2 : ∀ (i : ι), CanonicallyOrderedAdd (α i)] [inst_3 : (i : ι) → Sub (α i)]
      [inst_4 : ∀ (i : ι), OrderedSub (α i)] (i : ι), AddLeftMono (α i) := by
  (intros; infer_instance)

-- Set.forall_insert_of_forall, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.forall_insert_of_forall.h4 : ¬∀ {α : Type} {P : α → Prop} {a : α} {s : Set α}, P a → ∀ x ∈ Insert.insert a s, P x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (0) ({n : ℕ | n % 2 = 0}) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (2) (by
  decide)) (by
  decide +kernel)

-- Set.forall_insert_of_forall, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.forall_insert_of_forall.h5.inst : ¬(fun (b : Bool) => b = Bool.true) Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.forall_insert_of_forall.h5.prem0 : ∀ x ∈ {b : Bool | b = Bool.true}, (fun (b : Bool) => b = Bool.true) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.forall_insert_of_forall.h5.prem1 : Bool.false ∈ Insert.insert Bool.false {b : Bool | b = Bool.true} := by
  decide
theorem HypCheckProof.Set.forall_insert_of_forall.h5 : ¬∀ {α : Type} {P : α → Prop} {a : α} {s : Set α}, (∀ x ∈ s, P x) → ∀ x ∈ Insert.insert a s, P x := fun hc_h => HypCheckProof.Set.forall_insert_of_forall.h5.inst (@hc_h (Bool) (fun (b : Bool) => b = Bool.true) (Bool.false) ({b : Bool | b = Bool.true}) HypCheckProof.Set.forall_insert_of_forall.h5.prem0 (Bool.false) HypCheckProof.Set.forall_insert_of_forall.h5.prem1)

-- Set.forall_insert_of_forall, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.forall_insert_of_forall.h7 : ¬∀ {α : Type} {P : α → Prop} {a : α} {s : Set α}, (∀ x ∈ s, P x) → P a → ∀ (x : α), P x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (0) ({n : ℕ | n = 0}) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1)) (by
  decide +kernel)

-- Set.BijOn.comp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.comp.h8 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ}, Set.BijOn f s t → Set.BijOn (g ∘ f) s p := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.BijOn.comp, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.comp.h9 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ}, Set.BijOn g t p → Set.BijOn (g ∘ f) s p := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (fun n => n + 1 : ℕ → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp)) (by
  simp)

-- List.SortedGT.getElem_le_getElem_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.getElem_le_getElem_iff.h3 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α] {i j : ℕ} {hi : i < l.length} {hj : j < l.length}, l[i] ≤ l[j] ↔ j ≤ i := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ([0, 1]) (Nat.instLinearOrder) (0) (1) hc_k0 hc_k1) (by
  decide +kernel)

-- List.SortedGT.getElem_le_getElem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.getElem_le_getElem_iff.h6 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α], l.SortedGT → ∀ {i j : ℕ} {hj : j < l.length}, i < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instLinearOrder) (by
  decide) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.SortedGT.getElem_le_getElem_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.getElem_le_getElem_iff.h7 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α], l.SortedGT → ∀ {i j : ℕ} {hi : i < l.length}, j < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instLinearOrder) (by
  decide) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.Infinite.exists_ne_map_eq_of_mapsTo, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.exists_ne_map_eq_of_mapsTo.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t → t.Finite → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- Nat.ModEq.sub', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub'.h6 : ¬∀ {n a b c d : ℕ}, (c ≤ a ↔ d ≤ b) → c ≡ d [MOD n] → a - c ≡ b - d [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub'.h7 : ¬∀ {n a b c d : ℕ}, (c ≤ a ↔ d ≤ b) → a ≡ b [MOD n] → a - c ≡ b - d [MOD n] := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_left_div_gcd', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_left_div_gcd'.h5 : ¬∀ {m a b c d : ℕ}, c ≡ d [MOD m] → c * a ≡ d * b [MOD m] → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_left_div_gcd', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_left_div_gcd'.h6 : ¬∀ {m a b c d : ℕ}, 0 < m → c * a ≡ d * b [MOD m] → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (2) (0) (1) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_left_div_gcd', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_left_div_gcd'.h7 : ¬∀ {m a b c d : ℕ}, 0 < m → c ≡ d [MOD m] → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (2) (0) (1) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Quot.liftOn₂_mk, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quot.liftOn₂_mk.h8 : ¬∀ {α β γ : Type} {r : α → α → Prop} {s : β → β → Prop} (a : α) (b : β) (f : α → β → γ),
        (∀ (a₁ a₂ : α) (b : β), r a₁ a₂ → f a₁ b = f a₂ b) → ∀ (a : α) (b₁ b₂ : β), s b₁ b₂ → f a b₁ = f a b₂ := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun _ _ => True : Bool → Bool → Prop) (0) (Bool.false) (fun (a : ℕ) (b : Bool) => if b = Bool.true then 1 else 0) (by
  simp)) (by
  simp)

-- Subtype.map_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.map_eq.h6 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} {f g : α → β},
        (∀ (a : α), p a → q (g a)) → ∀ {x y : Subtype p} (a : α), p a → q (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 })) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 }))) (by
  simp)

-- Subtype.map_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.map_eq.h7 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} {f g : α → β},
        (∀ (a : α), p a → q (f a)) → ∀ {x y : Subtype p} (a : α), p a → q (g a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 })) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 }))) (by
  simp)

-- Finset.isPWO_support_addAntidiagonal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isPWO_support_addAntidiagonal.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO},
        IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.support_mulAntidiagonal_subset_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.support_mulAntidiagonal_subset_mul.h3 : ¬∀ {α : Type} [inst : CommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO},
        IsOrderedCancelMonoid α := fun hc_h => absurd (@hc_h (Bool) (BooleanRing.toCommRing.toCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
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

-- Equiv.Finset.disjUnionEquiv_symm_left, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_left.h7.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t) {i : α}, i ∈ s → i ∈ s.disjUnion t h := by
  (intros; simp_all; done)
theorem HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_left.h7.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t) {i : α} (hi : i ∈ s),
      (Equiv.Finset.disjUnionEquiv s t h).symm
          (⟨i, HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_left.h7.der h hi⟩ : ↥(s.disjUnion t h)) =
        Sum.inl (⟨i, hi⟩ : ↥s) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Equiv.Finset.disjUnionEquiv_symm_left hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_left.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- Finset.support_antidiagonal_subset_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.support_antidiagonal_subset_add.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO},
        IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.BijOn.iInter_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.iInter_congr.h8 : ¬∀ {α β γ : Type} {s : Set β} {t : Set γ} (f : β → Set α) (g : γ → Set α) {h : β → γ},
        (∀ (x : β), g (h x) = f x) → ⋂ x ∈ s, f x = ⋂ y ∈ t, g y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.IsChain.length_le_length_destutter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.length_le_length_destutter.h6 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] [inst_1 : IsEquiv α Rᶜ] {l₁ l₂ : List α},
        List.IsChain R l₁ → l₁.length ≤ (List.destutter R l₂).length := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableFalse) (@IsEquiv.mk (Bool) (@Compl.compl (Bool → Bool → Prop)
      (@Pi.instCompl Bool (fun (a : Bool) => Bool → Prop) fun (i : Bool) =>
        @Pi.instCompl Bool (fun (a : Bool) => Prop) fun (i : Bool) => «Prop».instCompl)
      fun (x x_1 : Bool) => False) (@IsPreorder.mk (Bool) (@Compl.compl (Bool → Bool → Prop)
      (@Pi.instCompl Bool (fun (a : Bool) => Bool → Prop) fun (i : Bool) =>
        @Pi.instCompl Bool (fun (a : Bool) => Prop) fun (i : Bool) => «Prop».instCompl)
      fun (x x_1 : Bool) => False) (@Std.Refl.mk (Bool) (@Compl.compl (Bool → Bool → Prop)
      (@Pi.instCompl Bool (fun (a : Bool) => Bool → Prop) fun (i : Bool) =>
        @Pi.instCompl Bool (fun (a : Bool) => Prop) fun (i : Bool) => «Prop».instCompl)
      fun (x x_1 : Bool) => False) (by (try dsimp only);   (intros; simp_all; done))) (@IsTrans.mk (Bool) (@Compl.compl (Bool → Bool → Prop)
      (@Pi.instCompl Bool (fun (a : Bool) => Bool → Prop) fun (i : Bool) =>
        @Pi.instCompl Bool (fun (a : Bool) => Prop) fun (i : Bool) => «Prop».instCompl)
      fun (x x_1 : Bool) => False) (by (try dsimp only);   (intros; omega)))) inferInstance) ([Bool.false]) ([]) (by
  decide)) (by
  decide +kernel)

-- Sum.LiftRel.exists_of_isRight_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.exists_of_isRight_left.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ},
        x.isRight = Bool.true → ∃ (b : β) (d : δ), s b d ∧ x = Sum.inr b ∧ y = Sum.inr d := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inr 0) (Sum.inl 0) (by
  decide)) (by
  simp)

-- Sum.LiftRel.exists_of_isRight_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.exists_of_isRight_left.h9 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ},
        Sum.LiftRel r s x y → ∃ (b : β) (d : δ), s b d ∧ x = Sum.inr b ∧ y = Sum.inr d := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inl 0) (Sum.inl 0) (by
  decide)) (by
  simp)

-- Flag.rangeFin_carrier, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.rangeFin_carrier.h5.inst : ¬(fun (a : Fin (0 + 1)) => Bool.true) 0 = ⊥ := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.rangeFin_carrier.h5.prem0 : (fun (a : Fin (0 + 1)) => Bool.true) (Fin.last 0) = ⊤ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.rangeFin_carrier.h5.prem1 : ∀ (k : Fin 0), (fun (a : Fin (0 + 1)) => Bool.true) k.castSucc ⩿ (fun (a : Fin (0 + 1)) => Bool.true) k.succ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Flag.rangeFin_carrier.h5 : ¬∀ {α : Type} [inst : PartialOrder α] [inst_1 : BoundedOrder α] {n : ℕ} (f : Fin (n + 1) → α),
        f (Fin.last n) = ⊤ → (∀ (k : Fin n), f k.castSucc ⩿ f k.succ) → f 0 = ⊥ := fun hc_h => HypCheckProof.Flag.rangeFin_carrier.h5.inst (@hc_h (Bool) (Bool.instPartialOrder) (Bool.instBoundedOrder) (0) (fun (a : Fin (0 + 1)) => Bool.true) HypCheckProof.Flag.rangeFin_carrier.h5.prem0 HypCheckProof.Flag.rangeFin_carrier.h5.prem1)

-- Flag.rangeFin_carrier, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.rangeFin_carrier.h6.inst : ¬(fun (a : Fin (0 + 1)) => Bool.false) (Fin.last 0) = ⊤ := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.rangeFin_carrier.h6.prem0 : (fun (a : Fin (0 + 1)) => Bool.false) 0 = ⊥ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.rangeFin_carrier.h6.prem1 : ∀ (k : Fin 0), (fun (a : Fin (0 + 1)) => Bool.false) k.castSucc ⩿ (fun (a : Fin (0 + 1)) => Bool.false) k.succ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Flag.rangeFin_carrier.h6 : ¬∀ {α : Type} [inst : PartialOrder α] [inst_1 : BoundedOrder α] {n : ℕ} (f : Fin (n + 1) → α),
        f 0 = ⊥ → (∀ (k : Fin n), f k.castSucc ⩿ f k.succ) → f (Fin.last n) = ⊤ := fun hc_h => HypCheckProof.Flag.rangeFin_carrier.h6.inst (@hc_h (Bool) (Bool.instPartialOrder) (Bool.instBoundedOrder) (0) (fun (a : Fin (0 + 1)) => Bool.false) HypCheckProof.Flag.rangeFin_carrier.h6.prem0 HypCheckProof.Flag.rangeFin_carrier.h6.prem1)

-- List.mem_dlookup_kunion_middle, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dlookup_kunion_middle.h8 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {b : β a} {l₁ l₂ l₃ : List (Sigma β)},
        a ∉ l₂.keys → b ∈ List.dlookup a ((l₁.kunion l₂).kunion l₃) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) ([]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- Nat.chineseRemainderOfList_perm, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfList_perm.h5.inst : ¬[].Perm [0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfList_perm.h5.prem0 : ∀ i ∈ [], (fun (n : ℕ) => n + 1) i ≠ 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfList_perm.h5.prem1 : List.Pairwise (Function.onFun Nat.Coprime fun (n : ℕ) => n + 1) [] := by
  decide
theorem HypCheckProof.Nat.chineseRemainderOfList_perm.h5 : ¬∀ {ι : Type} (a s : ι → ℕ) {l l' : List ι},
        (∀ i ∈ l, s i ≠ 0) → List.Pairwise (Function.onFun Nat.Coprime s) l → l.Perm l' := fun hc_h => HypCheckProof.Nat.chineseRemainderOfList_perm.h5.inst (@hc_h (ℕ) (fun (n : ℕ) => n + 1) (fun (n : ℕ) => n + 1) ([]) ([0]) HypCheckProof.Nat.chineseRemainderOfList_perm.h5.prem0 HypCheckProof.Nat.chineseRemainderOfList_perm.h5.prem1)

-- List.next_cons_concat, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_cons_concat.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y : α),
        x ∉ l →
          ∀ (h : optParam (x ∈ y :: l ++ [x]) (List.mem_append_right (y :: l) (List.mem_singleton_self x))),
            (y :: l ++ [x]).next x h = y := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (instDecidableEqNat) ([1]) (0) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- List.next_cons_concat, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_cons_concat.h6 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y : α),
        x ≠ y →
          ∀ (h : optParam (x ∈ y :: l ++ [x]) (List.mem_append_right (y :: l) (List.mem_singleton_self x))),
            (y :: l ++ [x]).next x h = y := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (instDecidableEqNat) ([0]) (0) (1) hc_k0 hc_k1) (by
  decide +kernel)

-- List.next_cons_concat, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.next_cons_concat.h7.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y : α), x ≠ y → x ∉ l → x ∈ y :: l ++ [x] := by
  (intros; simp; done)
theorem HypCheckProof.List.next_cons_concat.h7.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y : α) (hy : x ≠ y) (hx : x ∉ l),
      (y :: l ++ [x]).next x (HypCheckProof.List.next_cons_concat.h7.der l x y hy hx) = y := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @List.next_cons_concat hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.List.next_cons_concat.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- List.isRotated_prev_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isRotated_prev_eq.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l l' : List α}, l.Nodup → ∀ {x : α}, x ∈ l → l ~r l' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([]) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- List.isRotated_prev_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isRotated_prev_eq.h7 : ¬∀ {α : Type} [inst : DecidableEq α] {l l' : List α}, l ~r l' → l.Nodup → ∀ {x : α}, x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (by
  decide) (by
  decide) (0)) (by
  decide +kernel)

-- Quot.lift₂_mk, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quot.lift₂_mk.h6 : ¬∀ {α β γ : Type} {r : α → α → Prop} {s : β → β → Prop} (f : α → β → γ),
        (∀ (a₁ a₂ : α) (b : β), r a₁ a₂ → f a₁ b = f a₂ b) →
          ∀ (a : α) (b : β) (a : α) (b₁ b₂ : β), s b₁ b₂ → f a b₁ = f a b₂ := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun _ _ => True : Bool → Bool → Prop) (fun (a : ℕ) (b : Bool) => if b = Bool.true then 1 else 0) (by
  simp) (0) (Bool.false)) (by
  simp)

-- Function.Semiconj.injOn_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj.injOn_range.h5 : ¬∀ {α β : Type} {fa : α → α} {fb : β → β} {f : α → β},
        Function.Injective fa → Set.InjOn f (Set.range fa) → Set.InjOn fb (Set.range f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (not : Bool → Bool) (fun _ => 0 : ℕ → ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) (by
  simp)) (by
  simp)

-- Set.mem_image2_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_image2_of_mem.h8 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β}, b ∈ t → f a b ∈ Set.image2 f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1) (0) (by
  decide)) (by
  simp)

-- Set.mem_image2_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_image2_of_mem.h9 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β}, a ∈ s → f a b ∈ Set.image2 f s t := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (fun (a : ℕ) (b : Bool) => if b = Bool.true then 1 else 0) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (0) (Bool.false) (by
  decide)) (by
  simp)

-- List.IsChain.cons_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_le.h5 : ¬∀ {α : Type} [inst : LinearOrder α] {a : α} {as m : List α},
        List.IsChain (fun (x1 x2 : α) => x1 > x2) m → m ≤ as → List.IsChain (fun (x1 x2 : α) => x1 > x2) (a :: m) := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ([0]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.cons_of_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_le.h7 : ¬∀ {α : Type} [inst : LinearOrder α] {a : α} {as m : List α},
        List.IsChain (fun (x1 x2 : α) => x1 > x2) (a :: as) →
          List.IsChain (fun (x1 x2 : α) => x1 > x2) m → List.IsChain (fun (x1 x2 : α) => x1 > x2) (a :: m) := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.head!_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.head!_le.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} [inst : Inhabited α], List.Pairwise R l → a ∈ l → R l.head! a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (instInhabitedNat) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.head!_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.head!_le.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} [inst : Inhabited α] [inst_1 : Std.Refl R], a ∈ l → R l.head! a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([1, 0]) (0) (instInhabitedNat) _ (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.head!_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.head!_le.h7 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} [inst : Inhabited α] [inst_1 : Std.Refl R],
        List.Pairwise R l → R l.head! a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([1]) (0) (instInhabitedNat) _ (by
  decide)) (by
  decide +kernel)

-- List.pairwise_cons_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_cons_of_mem.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a b : α} [inst : IsTrans α R],
        b ∈ l → (List.Pairwise R (a :: l) ↔ R a b ∧ List.Pairwise R l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0, 1]) (0) (1) _ (by
  decide)) (by
  decide +kernel)

-- List.pairwise_cons_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_cons_of_mem.h7 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a b : α} [inst : Std.Symm R] [inst : IsTrans α R],
        List.Pairwise R (a :: l) ↔ R a b ∧ List.Pairwise R l := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) ([]) (Bool.false) (Bool.false) _ _) (by
  decide +kernel)

-- DFinsupp.lex_lt_of_lt_of_preorder, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.lex_lt_of_lt_of_preorder.h8 : ¬∀ {ι : Type} {α : ι → Type} [inst : (i : ι) → Zero (α i)] [inst_1 : (i : ι) → Preorder (α i)] (r : ι → ι → Prop)
        [inst_2 : IsStrictOrder ι r] {x y : Π₀ (i : ι), α i},
        ∃ (i : ι), (∀ (j : ι), r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun (i : ℕ) => Nat.instPreorder) (fun a b => a < b : ℕ → ℕ → Prop) _ (0) (0)) (by
  simp)

-- List.forall₂_zip, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall₂_zip.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} {a : α} {b : β}, (a, b) ∈ l₁.zip l₂ → R a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.forall₂_zip, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall₂_zip.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α} {b : β}, R a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([]) (by
  decide) (0) (0)) (by
  decide +kernel)

-- Set.SurjOn.comp_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.comp_right.h7 : ¬∀ {α β γ : Type} {f : α → β} {g : β → γ} {s : Set β} {t : Set γ}, Set.SurjOn g s t → Set.SurjOn (g ∘ f) (f ⁻¹' s) t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Rat.isNat_intCeil_ofIsNNRat, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isNat_intCeil_ofIsNNRat.h8 : Not
      (∀ {α : Type} [inst : Field α] [inst_1 : LinearOrder α]
        [inst_2 :
          @IsStrictOrderedRing α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α (@Field.toSemifield α inst)))
            (@SemilatticeInf.toPartialOrder α
              (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))]
        [inst_3 : @FloorRing α (@DivisionRing.toRing α (@Field.toDivisionRing α inst)) inst_1] (r : α) (n d : Nat),
        @Mathlib.Meta.NormNum.IsNat Int (@AddGroupWithOne.toAddMonoidWithOne Int (@Ring.toAddGroupWithOne Int Int.instRing))
          (@Int.ceil α (@DivisionRing.toRing α (@Field.toDivisionRing α inst)) inst_1 inst_3 r)
          (@Neg.neg Int Int.instNegInt
              (@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv)
                (@Neg.neg Int Int.instNegInt (@Nat.cast Int instNatCastInt n)) (@Nat.cast Int instNatCastInt d))).toNat) := fun hc_h => absurd (@hc_h (Rat) (Rat.instField) (Rat.linearOrder) _ (Rat.instFloorRing) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  nofun)

-- List.isChain_cons_of_isChain_cons_map, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_cons_of_isChain_cons_map.h6.inst : ¬List.IsChain (fun (a b : ℕ) => a < b) [0, 0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.isChain_cons_of_isChain_cons_map.h6.prem0 : List.IsChain (fun (a b : ℕ) => a ≤ b) ((fun (n : ℕ) => n + 1) 0 :: List.map (fun (n : ℕ) => n + 1) [0]) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.isChain_cons_of_isChain_cons_map.h6 : ¬∀ {α β : Type} {R : α → α → Prop} {a : α} {S : β → β → Prop} (f : α → β) {l : List α},
        List.IsChain S (f a :: List.map f l) → List.IsChain R (a :: l) := fun hc_h => HypCheckProof.List.isChain_cons_of_isChain_cons_map.h6.inst (@hc_h (ℕ) (ℕ) (fun (a b : ℕ) => a < b) (0) (fun (a b : ℕ) => a ≤ b) (fun (n : ℕ) => n + 1) ([0]) HypCheckProof.List.isChain_cons_of_isChain_cons_map.h6.prem0)

-- List.isChain_cons_of_isChain_cons_map, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_cons_of_isChain_cons_map.h8 : ¬∀ {α β : Type} {R : α → α → Prop} {a : α} {S : β → β → Prop} (f : α → β),
        (∀ (a b : α), S (f a) (f b) → R a b) → ∀ {l : List α}, List.IsChain R (a :: l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (by
  simp) ([0])) (by
  decide +kernel)

-- List.le_of_mem_argmin, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_of_mem_argmin.h7 : ¬∀ {α β : Type} [inst : LinearOrder β] {f : α → β} {l : List α} {a m : α}, m ∈ List.argmin f l → f m ≤ f a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun n => n + 1 : ℕ → ℕ) ([1]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.le_of_mem_argmin, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_of_mem_argmin.h8 : ¬∀ {α β : Type} [inst : LinearOrder β] {f : α → β} {l : List α} {a m : α}, a ∈ l → f m ≤ f a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun n => n + 1 : ℕ → ℕ) ([0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Perm.kreplace, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.kreplace.h8 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {b : β a} {l₁ l₂ : List (Sigma β)},
        l₁.NodupKeys → (List.kreplace a b l₁).Perm (List.kreplace a b l₂) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp)) (by
  decide +kernel)

-- List.Nodup.prefix_of_head_mem_of_infix, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.prefix_of_head_mem_of_infix.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} {hne : l₂ ≠ []}, l₂.head hne ∈ l₁ → l₂.Nodup → l₁ <+: l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0, 1]) ([0]) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- List.Nodup.prefix_of_head_mem_of_infix, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.prefix_of_head_mem_of_infix.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₂.Nodup → l₂ ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Mathlib.Meta.NormNum.IsRat.natCeil, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Mathlib.Meta.NormNum.IsRat.natCeil.h8 : ¬∀ {R : Type} [inst : Field R] [inst_1 : LinearOrder R] [inst_2 : IsStrictOrderedRing R] [inst_3 : FloorSemiring R]
        (r : R) (n d : ℕ), Mathlib.Meta.NormNum.IsNat ⌈r⌉₊ 0 := fun hc_h => absurd (@hc_h (ℚ) (Rat.instField) (Rat.linearOrder) _ (FloorRing.toFloorSemiring) (1) (0) (0)) (by
  nofun)

-- List.cons_mem_fixedLengthDigits_succ, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_mem_fixedLengthDigits_succ.h1 : ¬∀ {b : ℕ} (l d : ℕ), d < b → ∀ {L : List ℕ}, 1 < b := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide) ([])) (by
  decide +kernel)

-- List.cons_mem_fixedLengthDigits_succ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_mem_fixedLengthDigits_succ.h4 : ¬∀ {b : ℕ} (hb : 1 < b) (l d : ℕ) {L : List ℕ},
        L ∈ List.fixedLengthDigits hb l → d :: L ∈ List.fixedLengthDigits hb (l + 1) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (2) hc_k0 (0) (2) ([]) hc_k1) (by
  simp)

-- List.cons_mem_fixedLengthDigits_succ, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_mem_fixedLengthDigits_succ.h6 : ¬∀ {b : ℕ} (hb : 1 < b) (l d : ℕ), d < b → ∀ {L : List ℕ}, d :: L ∈ List.fixedLengthDigits hb (l + 1) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (2) hc_k0 (0) (0) hc_k1 ([0])) (by
  simp)

-- PNat.Coprime.factor_eq_gcd_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_left.h4 : ¬∀ {a b m n : ℕ+}, a ∣ m → b ∣ n → a = (a * b).gcd m := fun hc_h => absurd (@hc_h (1) (2) (2) (2) (by
  simp) (by
  rfl)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_left.h5 : ¬∀ {a b m n : ℕ+}, m.Coprime n → b ∣ n → a = (a * b).gcd m := fun hc_h => absurd (@hc_h (2) (1) (1) (1) (by
  rfl) (by
  rfl)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_left.h6 : ¬∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m → a = (a * b).gcd m := fun hc_h => absurd (@hc_h (1) (2) (2) (1) (by
  rfl) (by
  simp)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_right_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_right_right.h4 : ¬∀ {a b m n : ℕ+}, a ∣ m → b ∣ n → a = m.gcd (b * a) := fun hc_h => absurd (@hc_h (1) (2) (2) (2) (by
  simp) (by
  rfl)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_right_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_right_right.h5 : ¬∀ {a b m n : ℕ+}, m.Coprime n → b ∣ n → a = m.gcd (b * a) := fun hc_h => absurd (@hc_h (2) (1) (1) (1) (by
  rfl) (by
  rfl)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_right_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_right_right.h6 : ¬∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m → a = m.gcd (b * a) := fun hc_h => absurd (@hc_h (1) (2) (2) (1) (by
  rfl) (by
  simp)) (by
  decide +kernel)

-- List.Nodup.rotate_congr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.rotate_congr.h2 : ¬∀ {α : Type} {l : List α}, l ≠ [] → ∀ (i j : ℕ), l.rotate i = l.rotate j → i % l.length = j % l.length := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (by
  decide) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.rotate_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.rotate_congr.h3 : ¬∀ {α : Type} {l : List α}, l.Nodup → ∀ (i j : ℕ), l.rotate i = l.rotate j → i % l.length = j % l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (by
  decide) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.rotate_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.rotate_congr.h6 : ¬∀ {α : Type} {l : List α}, l.Nodup → l ≠ [] → ∀ (i j : ℕ), i % l.length = j % l.length := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (by
  decide) (by
  decide) (0) (1)) (by
  decide +kernel)

-- Subtype.coind_bijective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coind_bijective.h4 : ¬∀ {α β : Type} {f : α → β} {p : Set β}, Function.Injective f → Set.SurjOn f Set.univ p → ∀ (a : α), f a ∈ p := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) ({n : ℕ | n = 0}) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Subtype.coind_bijective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coind_bijective.h5 : ¬∀ {α β : Type} {f : α → β} {p : Set β} (h : ∀ (a : α), f a ∈ p),
        Set.SurjOn f Set.univ p → Function.Bijective (Subtype.coind f h) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) ({n : ℕ | n = 0}) hc_k0 hc_k1) (by
  (simp <;> decide))

-- Nat.maxPowDvdDiv_of_pow_mul_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_of_pow_mul_eq.h4 : ¬∀ {p n k l : ℕ}, p ^ k * l = n → ¬p ∣ l → p.maxPowDvdDiv n = (k, l) := fun hc_h => absurd (@hc_h (0) _ (1) (1) rfl (by
  decide)) (by
  decide +kernel)

-- Nat.maxPowDvdDiv_of_pow_mul_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_of_pow_mul_eq.h5 : ¬∀ {p n k l : ℕ}, n ≠ 0 → ¬p ∣ l → p.maxPowDvdDiv n = (k, l) := fun hc_h => absurd (@hc_h (0) (1) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.maxPowDvdDiv_of_pow_mul_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_of_pow_mul_eq.h6 : ¬∀ {p n k l : ℕ}, n ≠ 0 → p ^ k * l = n → p.maxPowDvdDiv n = (k, l) := fun hc_h => absurd (@hc_h (1) _ (1) (1) (by
  decide) rfl) (by
  decide +kernel)

-- Nat.ofNat_nonneg', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofNat_nonneg'.h6 : ¬∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α] [inst : ZeroLEOneClass α]
        (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Nodup.getElem_inj_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.getElem_inj_iff.h2 : ¬∀ {α : Type} {l : List α} {i : ℕ} {hi : i < l.length} {j : ℕ} {hj : j < l.length}, l[i] = l[j] ↔ i = j := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ([0, 0]) (0) hc_k0 (1) hc_k1) (by
  decide +kernel)

-- List.Nodup.getElem_inj_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.getElem_inj_iff.h4 : ¬∀ {α : Type} {l : List α}, l.Nodup → ∀ {i j : ℕ} {hj : j < l.length}, i < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (by
  decide) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.getElem_inj_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.getElem_inj_iff.h6 : ¬∀ {α : Type} {l : List α}, l.Nodup → ∀ {i : ℕ} {hi : i < l.length} {j : ℕ}, j < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (by
  decide) (0) (by
  decide) (1)) (by
  decide +kernel)

-- Set.Finite.exists_bijOn_of_encard_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.exists_bijOn_of_encard_eq.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} [inst : Nonempty β], s.Finite → ∃ (f : α → β), Set.BijOn f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) _ (by
  simp)) (by
  simp)

-- le_sSup_iff_of_directedOn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.le_sSup_iff_of_directedOn.h4 : ¬∀ {α : Type} [inst : CompleteLattice α] {s : Set α} {a : α},
        s.Finite → DirectedOn (fun (x1 x2 : α) => x1 ≤ x2) s → (a ≤ SupSet.sSup s ↔ ∃ b ∈ s, a ≤ b) := fun hc_h => absurd (@hc_h (Fin 2) (CompleteLinearOrder.toCompletelyDistribLattice.toCompleteLattice) (∅) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Nat.factorization_choose, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose.h4 : ¬∀ {p n k b : ℕ},
        k ≤ n →
          Nat.log p n < b → (n.choose k).factorization p = {i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}.card := fun hc_h => absurd (@hc_h (0) (0) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose.h6 : ¬∀ {p n k b : ℕ},
        Nat.Prime p → k ≤ n → (n.choose k).factorization p = {i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}.card := fun hc_h => absurd (@hc_h (2) (2) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- LE.le.ssubset_of_mem_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.LE.le.ssubset_of_mem_notMem.h5 : ¬∀ {α : Type} {s t : Set α} {a : α}, s ⊆ t → a ∉ s → s ⊂ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1) (by
  rfl) (by
  decide)) (by
  simp)

-- LE.le.ssubset_of_mem_notMem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.LE.le.ssubset_of_mem_notMem.h6 : ¬∀ {α : Type} {s t : Set α} {a : α}, s ⊆ t → a ∈ t → s ⊂ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (by
  rfl) (by
  decide)) (by
  simp)

-- Nat.count_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_injective.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {m n : ℕ}, p n → Nat.count p m = Nat.count p n → m = n := fun hc_h => absurd (@hc_h (fun n => n % 2 = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (1) (2) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Nat.count_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_injective.h5 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {m n : ℕ}, p m → Nat.count p m = Nat.count p n → m = n := fun hc_h => absurd (@hc_h (fun n => n % 2 = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (2) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Nat.count_injective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_injective.h6 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {m n : ℕ}, p m → p n → m = n := fun hc_h => absurd (@hc_h (fun n => n % 2 = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (0) (2) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.nontrivial_of_mem_mem_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_mem_mem_ne.h4 : ¬∀ {α : Type} {s : Set α} {x y : α}, y ∈ s → x ≠ y → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (0) (by
  decide) (by
  decide)) (by
  simp)

-- Set.nontrivial_of_mem_mem_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_mem_mem_ne.h5 : ¬∀ {α : Type} {s : Set α} {x y : α}, x ∈ s → x ≠ y → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (1) (by
  decide) (by
  decide)) (by
  simp)

-- Set.nontrivial_of_mem_mem_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_mem_mem_ne.h6 : ¬∀ {α : Type} {s : Set α} {x y : α}, x ∈ s → y ∈ s → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (0) (by
  decide) (by
  decide)) (by
  simp)

-- List.IsChain.cons_of_ne_nil, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_ne_nil.h4 : ¬∀ {α : Type} {R : α → α → Prop} {x : α} {l : List α}, List.IsChain R l → l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) ([]) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.cons_of_ne_nil, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_ne_nil.h5 : ¬∀ {α : Type} {R : α → α → Prop} {x : α} {l : List α} (l_ne_nil : l ≠ []),
        R x (l.head l_ne_nil) → List.IsChain R (x :: l) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) ([1, 0]) hc_k0 hc_k1) (by
  decide +kernel)

-- List.IsChain.cons_of_ne_nil, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_ne_nil.h6 : ¬∀ {α : Type} {R : α → α → Prop} {x : α} {l : List α}, l ≠ [] → List.IsChain R l → List.IsChain R (x :: l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Choose.choose_modEq_prod_range_choose_nat, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.choose_modEq_prod_range_choose_nat.h6 : ¬∀ {n k p : ℕ} [inst : Fact (Nat.Prime p)] {a : ℕ},
        n < p ^ a → n.choose k ≡ ∏ i ∈ Finset.range a, (n / p ^ i % p).choose (k / p ^ i % p) [MOD p] := fun hc_h => absurd (@hc_h (0) (1) (2) _ (0) (by
  decide)) (by
  decide +kernel)

-- Choose.lucas_theorem_nat, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.lucas_theorem_nat.h6 : ¬∀ {n k p : ℕ} [inst : Fact (Nat.Prime p)] {a : ℕ},
        n < p ^ a → n.choose k ≡ ∏ i ∈ Finset.range a, (n / p ^ i % p).choose (k / p ^ i % p) [MOD p] := fun hc_h => absurd (@hc_h (0) (1) (2) _ (0) (by
  decide)) (by
  decide +kernel)

-- Set.eq_of_preimage_val_eq_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_preimage_val_eq_of_subset.h5 : Not
      (∀ {α : Type} {A B C : Set α},
        @LE.le (Set α) (@Set.instLE α) B A →
          @Eq (Set (@Set.Elem α A))
              (@Set.preimage (@Set.Elem α A) α
                (@Subtype.val α fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) A x) B)
              (@Set.preimage (@Set.Elem α A) α
                (@Subtype.val α fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) A x) C) →
            @Eq (Set α) B C) := fun hc_h => absurd (@hc_h (Nat) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => True) (by
  rfl) (by
  simp)) (by
  simp)

-- Set.eq_of_preimage_val_eq_of_subset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_preimage_val_eq_of_subset.h6 : ¬∀ {α : Type} {A B C : Set α}, B ⊆ A → C ⊆ A → B = C := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl) (by
  simp)) (by
  simp)

-- Nat.Coprime.mul_add_mul_ne_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.mul_add_mul_ne_mul.h4 : ¬∀ {m n a b : ℕ}, a ≠ 0 → b ≠ 0 → a * m + b * n ≠ m * n := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Coprime.mul_add_mul_ne_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.mul_add_mul_ne_mul.h5 : ¬∀ {m n a b : ℕ}, m.Coprime n → b ≠ 0 → a * m + b * n ≠ m * n := fun hc_h => absurd (@hc_h (1) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Coprime.mul_add_mul_ne_mul, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.mul_add_mul_ne_mul.h6 : ¬∀ {m n a b : ℕ}, m.Coprime n → a ≠ 0 → a * m + b * n ≠ m * n := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.node4L_lemma₄, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node4L_lemma₄.h4 : ¬∀ {a b c d : ℕ}, b + c + 1 ≤ 3 * d → b ≤ 3 * c → a + b + 1 ≤ 3 * (c + d + 1) := fun hc_h => absurd (@hc_h (6) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Multiset.coe_sort, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_sort.h5 : ¬∀ {α : Type} (l : List α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
        Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) ([]) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.coe_sort, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_sort.h6 : ¬∀ {α : Type} (l : List α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ([]) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.sort_singleton, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sort_singleton.h5 : ¬∀ {α : Type} (a : α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
        Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) (Bool.false) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.sort_singleton, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sort_singleton.h6 : ¬∀ {α : Type} (a : α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) (0) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.ModEq.sub_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_right.h4 : ¬∀ {n a b c : ℕ}, a ≤ c → b ≡ c [MOD n] → b - a ≡ c - a [MOD n] := fun hc_h => absurd (@hc_h (2) (1) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_right.h5 : ¬∀ {n a b c : ℕ}, a ≤ b → b ≡ c [MOD n] → b - a ≡ c - a [MOD n] := fun hc_h => absurd (@hc_h (2) (1) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_right.h6 : ¬∀ {n a b c : ℕ}, a ≤ b → a ≤ c → b - a ≡ c - a [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- PFunctor.M.eq_of_bisim, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.PFunctor.M.eq_of_bisim.h2.gneg.{uA, uB} : ∀ {F : PFunctor.{uA, uB}} (R : F.M → F.M → Prop),
      ¬Nonempty F.M → PFunctor.M.IsBisimulation R → ∀ (s₁ s₂ : F.M), R s₁ s₂ → s₁ = s₂ := by
  (intros; solve_by_elim)
theorem HypCheckProof.PFunctor.M.eq_of_bisim.h2.{uA, uB} : ∀ {F : PFunctor.{uA, uB}} (R : F.M → F.M → Prop), PFunctor.M.IsBisimulation R → ∀ (s₁ s₂ : F.M), R s₁ s₂ → s₁ = s₂ := by
  intro hc_x0 hc_x1 hc_x3 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @PFunctor.M.eq_of_bisim hc_x0 hc_x1 hc_h hc_x3 hc_x4 hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.PFunctor.M.eq_of_bisim.h2.gneg hc_x0 hc_x1 hc_hn hc_x3 hc_x4 hc_x5 hc_x6)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.PFunctor.M.eq_of_bisim.h2.derivable.{uA, uB} : ∀ {F : PFunctor.{uA, uB}} (R : F.M → F.M → Prop), PFunctor.M.IsBisimulation R → ∀ (s₁ s₂ : F.M), R s₁ s₂ → Nonempty F.M := by
  (intros; solve_by_elim)

-- Finset.sort_singleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_singleton.h4 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r] (a : α),
        Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (Bool.false)) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.sort_singleton, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_singleton.h5 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r] (a : α),
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- PNat.find_mono, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.PNat.find_mono.h5.der : ∀ {p q : PNat → Prop} [inst : @DecidablePred PNat p] [inst : @DecidablePred PNat q],
      (∀ (n : PNat), q n → p n) → ∀ {hq : ∃ (n : PNat), q n}, ∃ (n : PNat), p n := by
  (intros; grind)
theorem HypCheckProof.PNat.find_mono.h5 : ∀ {p q : PNat → Prop} [inst : @DecidablePred PNat p] [inst_1 : @DecidablePred PNat q] (h : ∀ (n : PNat), q n → p n)
      {hq : ∃ (n : PNat), q n},
      @LE.le PNat
        (@Preorder.toLE PNat
          (@PartialOrder.toPreorder PNat
            (@SemilatticeInf.toPartialOrder PNat
              (@Lattice.toSemilatticeInf PNat
                (@DistribLattice.toLattice PNat (@instDistribLatticeOfLinearOrder PNat instLinearOrderPNat))))))
        (@PNat.find p inst (@HypCheckProof.PNat.find_mono.h5.der p q inst inst_1 h hq)) (@PNat.find q inst_1 hq) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @PNat.find_mono hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.PNat.find_mono.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- Set.Finite.toFinset_union, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Finite.toFinset_union.h4.der.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α], t.Finite → (s ∪ t).Finite → s.Finite := by
  (intros; simp_all; done)
theorem HypCheckProof.Set.Finite.toFinset_union.h4.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (ht : t.Finite) (h : (s ∪ t).Finite),
      h.toFinset = (HypCheckProof.Set.Finite.toFinset_union.h4.der ht h).toFinset ∪ ht.toFinset := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Set.Finite.toFinset_union hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Set.Finite.toFinset_union.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x4 hc_x5

-- Set.Finite.toFinset_union, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Finite.toFinset_union.h5.der.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α], s.Finite → (s ∪ t).Finite → t.Finite := by
  (intros; simp_all; done)
theorem HypCheckProof.Set.Finite.toFinset_union.h5.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (hs : s.Finite) (h : (s ∪ t).Finite),
      h.toFinset = hs.toFinset ∪ (HypCheckProof.Set.Finite.toFinset_union.h5.der hs h).toFinset := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Set.Finite.toFinset_union hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Set.Finite.toFinset_union.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- Set.Finite.toFinset_union, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Finite.toFinset_union.h6.der.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α], s.Finite → t.Finite → (s ∪ t).Finite := by
  (intros; simp_all; done)
theorem HypCheckProof.Set.Finite.toFinset_union.h6.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (hs : s.Finite) (ht : t.Finite),
      (HypCheckProof.Set.Finite.toFinset_union.h6.der hs ht).toFinset = hs.toFinset ∪ ht.toFinset := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Set.Finite.toFinset_union hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Set.Finite.toFinset_union.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Set.infinite_of_injective_forall_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_of_injective_forall_mem.h5 : ¬∀ {α β : Type} [inst : Infinite α] {s : Set β} {f : α → β}, (∀ (x : α), f x ∈ s) → s.Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.Finite.toFinset_symmDiff, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Finite.toFinset_symmDiff.h6.der.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α], s.Finite → t.Finite → (symmDiff s t).Finite := by
  (intros; simp_all; done)
theorem HypCheckProof.Set.Finite.toFinset_symmDiff.h6.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (hs : s.Finite) (ht : t.Finite),
      (HypCheckProof.Set.Finite.toFinset_symmDiff.h6.der hs ht).toFinset = symmDiff hs.toFinset ht.toFinset := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Set.Finite.toFinset_symmDiff hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Set.Finite.toFinset_symmDiff.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Set.powersetCard.exists_mem_notMem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.powersetCard.exists_mem_notMem.h6 : ¬∀ {α : Type} {n : ℕ}, 1 ≤ n → ↑n < ENat.card α → ∀ {a b : α}, ∃ (s : ↑(Set.powersetCard α n)), a ∈ s ∧ b ∉ s := fun hc_h => absurd (@hc_h (ℕ) (1) (by
  decide) (by
  simp) (0) (0)) (by
  nofun)

-- Set.ncard_image2_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_image2_le.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β}, s.Finite → (Set.image2 f s t).ncard ≤ s.ncard * t.ncard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) (by
  simp)) (by
  simp)

-- Finite.ciInf_le_of_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.ciInf_le_of_le.h7 : ¬∀ {α ι : Type} [inst : Finite ι] [inst : ConditionallyCompleteLattice α] {a : α} {f : ι → α} (c : ι), iInf f ≤ a := fun hc_h => absurd (@hc_h (ℕ) (Fin 2) _ (Nat.instConditionallyCompleteLinearOrderBot.toConditionallyCompleteLattice) (0) (fun (a : Fin 2) => 1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  simp)

-- Set.BijOn.subset_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.subset_right.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {r : Set β}, r ⊆ t → Set.BijOn f (s ∩ f ⁻¹' r) r := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.true}) ({n : ℕ | n = 0}) (fun b => if b then 1 else 0 : Bool → ℕ) ({n : ℕ | n = 0}) (by
  rfl)) (by
  norm_num)

-- Set.image2_assoc, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_assoc.h13 : ¬∀ {α β γ δ ε ε' : Type} {s : Set α} {t : Set β} {u : Set γ} {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε}
        {g' : β → γ → ε'}, Set.image2 f (Set.image2 g s t) u = Set.image2 f' s (Set.image2 g' t u) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Bool) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun (a : Bool) (n : ℕ) => n + 1) (fun a b => a < b : ℕ → ℕ → Bool) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ)) (by
  (simp <;> omega))

-- Set.MapsTo.inter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.inter.h6 : ¬∀ {α β : Type} {s : Set α} {t₁ t₂ : Set β} {f : α → β}, Set.MapsTo f s t₂ → Set.MapsTo f s (t₁ ∩ t₂) := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp)) (by
  simp)

-- Set.MapsTo.inter, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.inter.h7 : ¬∀ {α β : Type} {s : Set α} {t₁ t₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → Set.MapsTo f s (t₁ ∩ t₂) := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp)) (by
  simp)

-- Set.EqOn.mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.mono.h6 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {f₁ f₂ : α → β}, Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.EqOn.mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.mono.h7 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {f₁ f₂ : α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₁ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  rfl)) (by
  simp)

-- StrictMono.codRestrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.codRestrict.h5 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β} {s : Set β} (hs : ∀ (x : α), f x ∈ s),
        StrictMono (Set.codRestrict f s hs) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun _ => 0 : Bool → ℕ) ({n : ℕ | n = 0}) hc_k0) (by
  decide +kernel)

-- StrictMono.codRestrict, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.codRestrict.h7 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β}, StrictMono f → ∀ {s : Set β} (x : α), f x ∈ s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) ({n : ℕ | n = 0})) (by
  decide +kernel)

-- Monotone.codRestrict, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.codRestrict.h7 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β}, Monotone f → ∀ {s : Set β} (x : α), f x ∈ s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) ({n : ℕ | n = 0})) (by
  decide +kernel)

-- Function.antitone_of_rightInverse, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.antitone_of_rightInverse.h6 : ¬∀ {α β : Type} [inst : PartialOrder α] [inst_1 : LinearOrder β] {φ : β → α} {ψ : α → β},
        Function.RightInverse ψ φ → Antitone ψ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instPartialOrder) (Nat.instLinearOrder) (fun n => n == 1 : ℕ → Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  decide +kernel)

-- Function.antitone_of_rightInverse, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.antitone_of_rightInverse.h7 : ¬∀ {α β : Type} [inst : PartialOrder α] [inst_1 : LinearOrder β] {φ : β → α} {ψ : α → β}, Antitone φ → Antitone ψ := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.instPartialOrder) (Bool.linearOrder) (not : Bool → Bool) (fun b => b : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Set.RightInvOn.mapsTo, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.RightInvOn.mapsTo.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {f' : β → α}, Set.SurjOn f' t s → Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.lookup_graph, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookup_graph.h3 : ¬∀ {α β : Type} [inst : BEq α] (f : α → β) {a : α} {as : List α},
        a ∈ as → List.lookup a (List.map (fun (x : α) => (x, f x)) as) = Option.some (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) (fun n => n + 1 : ℕ → ℕ) (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.lookup_graph, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookup_graph.h7 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : LawfulBEq α] (f : α → β) {a : α} {as : List α},
        List.lookup a (List.map (fun (x : α) => (x, f x)) as) = Option.some (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instBEqOfDecidableEq) _ (fun n => n + 1 : ℕ → ℕ) (0) ([])) (by
  decide +kernel)

-- List.Forall₂.imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.imp.h4 : ¬∀ {α β : Type} {R S : α → β → Prop} {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Forall₂.imp, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.imp.h7 : ¬∀ {α β : Type} {R S : α → β → Prop},
        (∀ (a : α) (b : β), R a b → S a b) → ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ S l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (by
  simp) ([]) ([0])) (by
  decide +kernel)

-- Set.biInter_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.biInter_mono.h7 : ¬∀ {α β : Type} {s s' : Set α} {t t' : α → Set β}, s ⊆ s' → ⋂ x ∈ s', t x ⊆ ⋂ x ∈ s, t' x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {x : ℕ | False}) (by
  rfl)) (by
  simp)

-- List.perm_insertIdx_iff_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_insertIdx_iff_of_le.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {m n : ℕ},
        n ≤ l₂.length → ∀ (a : α), (l₁.insertIdx m a).Perm (l₂.insertIdx n a) ↔ l₁.Perm l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (1) (0) (by
  decide) (0)) (by
  decide +kernel)

-- List.perm_insertIdx_iff_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_insertIdx_iff_of_le.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} {m n : ℕ},
        m ≤ l₁.length → ∀ (a : α), (l₁.insertIdx m a).Perm (l₂.insertIdx n a) ↔ l₁.Perm l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0) (1) (by
  decide) (0)) (by
  decide +kernel)

-- List.min_le_of_le', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min_le_of_le'.h6 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a x : α} (b : α), x ≤ a → List.foldr Min.min b l ≤ a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.min_le_of_le', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min_le_of_le'.h7 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a x : α} (b : α), x ∈ l → List.foldr Min.min b l ≤ a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([1]) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- List.min_le_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min_le_of_le.h6 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] {l : List α} {a x : α}, x ≤ a → List.foldr Min.min ⊤ l ≤ a := fun hc_h => absurd (@hc_h (Bool) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ([]) (Bool.false) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- List.min_le_of_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min_le_of_le.h7 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] {l : List α} {a x : α}, x ∈ l → List.foldr Min.min ⊤ l ≤ a := fun hc_h => absurd (@hc_h (Bool) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ([Bool.true]) (Bool.false) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- List.le_max_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_max_of_le.h6 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] {l : List α} {a x : α}, a ≤ x → a ≤ List.foldr Max.max ⊥ l := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (Nat.instOrderBot) ([]) (1) (1) (by
  decide)) (by
  decide +kernel)

-- List.le_max_of_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_max_of_le.h7 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] {l : List α} {a x : α}, x ∈ l → a ≤ List.foldr Max.max ⊥ l := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (Nat.instOrderBot) ([0]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.MapsTo.mono_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.mono_left.h6 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t : Set β} {f : α → β}, s₂ ⊆ s₁ → Set.MapsTo f s₂ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  rfl)) (by
  simp)

-- Set.MapsTo.mono_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.mono_left.h7 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s₁ t → Set.MapsTo f s₂ t := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({n : ℕ | n = 0}) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  simp)) (by
  simp)

-- List.perm_lookupAll, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_lookupAll.h7 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (a : α) {l₁ l₂ : List (Sigma β)},
        l₁.NodupKeys → List.lookupAll a l₁ = List.lookupAll a l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp)) (by
  decide +kernel)

-- List.length_destutter'_congr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.length_destutter'_congr.h6.inst : ¬(List.destutter' (fun (a b : ℕ) => a ≤ b) 1 [0]).length = (List.destutter' (fun (a b : ℕ) => a ≤ b) 0 [0]).length := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.length_destutter'_congr.h6.prem0 : ¬(fun (a b : ℕ) => a ≤ b) 1 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.length_destutter'_congr.h6 : ¬∀ {α : Type} (l : List α) {R : α → α → Prop} [inst : DecidableRel R] {a b : α},
        ¬R a b → (List.destutter' R a l).length = (List.destutter' R b l).length := fun hc_h => HypCheckProof.List.length_destutter'_congr.h6.inst (@hc_h (ℕ) ([0]) (fun (a b : ℕ) => a ≤ b) (Nat.decLe) (1) (0) HypCheckProof.List.length_destutter'_congr.h6.prem0)

-- List.forall_mem_of_forall_mem_union_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall_mem_of_forall_mem_union_left.h5 : ¬∀ {α : Type} {l₁ : List α} {l₂ : List α} {p : α → Prop} [inst : DecidableEq α], ∀ x ∈ l₁, p x := fun hc_h => absurd (@hc_h (Bool) ([Bool.false]) ([]) (fun b => b = true : Bool → Prop) (instDecidableEqBool) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- List.forall_mem_of_forall_mem_union_left, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_of_forall_mem_union_left.h7.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_of_forall_mem_union_left.h7.prem0 : ∀ x ∈ [] ∪ [], (fun (n : ℕ) => n = 0) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.forall_mem_of_forall_mem_union_left.h7 : ¬∀ {α : Type} {l₁ l₂ : List α} {p : α → Prop} [inst : DecidableEq α], (∀ x ∈ l₁ ∪ l₂, p x) → ∀ (x : α), p x := fun hc_h => HypCheckProof.List.forall_mem_of_forall_mem_union_left.h7.inst (@hc_h (ℕ) ([]) ([]) (fun (n : ℕ) => n = 0) (instDecidableEqNat) HypCheckProof.List.forall_mem_of_forall_mem_union_left.h7.prem0 (1))

-- List.forall_mem_inter_of_forall_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall_mem_inter_of_forall_right.h5 : ¬∀ {α : Type} {l₂ : List α} {p : α → Prop} [inst : DecidableEq α] (l₁ : List α), ∀ x ∈ l₁ ∩ l₂, p x := fun hc_h => absurd (@hc_h (Bool) ([Bool.false]) (fun b => b = true : Bool → Prop) (instDecidableEqBool) ([Bool.false]) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- List.forall_mem_inter_of_forall_right, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_inter_of_forall_right.h7.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_inter_of_forall_right.h7.prem0 : ∀ x ∈ [], (fun (n : ℕ) => n = 0) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.forall_mem_inter_of_forall_right.h7 : ¬∀ {α : Type} {l₂ : List α} {p : α → Prop} [inst : DecidableEq α] (l₁ : List α), (∀ x ∈ l₂, p x) → ∀ (x : α), p x := fun hc_h => HypCheckProof.List.forall_mem_inter_of_forall_right.h7.inst (@hc_h (ℕ) ([]) (fun (n : ℕ) => n = 0) (instDecidableEqNat) ([]) HypCheckProof.List.forall_mem_inter_of_forall_right.h7.prem0 (1))

-- List.forall_mem_of_forall_mem_union_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall_mem_of_forall_mem_union_right.h5 : ¬∀ {α : Type} {l₁ : List α} {l₂ : List α} {p : α → Prop} [inst : DecidableEq α], ∀ x ∈ l₂, p x := fun hc_h => absurd (@hc_h (Bool) ([]) ([Bool.false]) (fun b => b = true : Bool → Prop) (instDecidableEqBool) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- List.forall_mem_of_forall_mem_union_right, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_of_forall_mem_union_right.h7.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_of_forall_mem_union_right.h7.prem0 : ∀ x ∈ [] ∪ [], (fun (n : ℕ) => n = 0) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.forall_mem_of_forall_mem_union_right.h7 : ¬∀ {α : Type} {l₁ l₂ : List α} {p : α → Prop} [inst : DecidableEq α], (∀ x ∈ l₁ ∪ l₂, p x) → ∀ (x : α), p x := fun hc_h => HypCheckProof.List.forall_mem_of_forall_mem_union_right.h7.inst (@hc_h (ℕ) ([]) ([]) (fun (n : ℕ) => n = 0) (instDecidableEqNat) HypCheckProof.List.forall_mem_of_forall_mem_union_right.h7.prem0 (1))

-- Int.log_of_right_le_zero, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.log_of_right_le_zero.h7 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        (b : ℕ) {r : R}, Int.log b r = 0 := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (1 / 2)) (by
  decide +kernel)

-- Int.self_le_zpow_clog, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.self_le_zpow_clog.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} (r : R), r ≤ ↑b ^ Int.clog b r := fun hc_h => absurd (@hc_h (ℚ≥0) (NNRat.instSemifield) (instLinearOrderNNRat) (NNRat.instFloorSemiring) _ (0) (2)) (by
  decide +kernel)

-- Set.sup_mem_sups, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sup_mem_sups.h6 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s t : Set α} {a b : α},
        @Membership.mem α (Set α) (@Set.instMembership α) t b →
          @Membership.mem α (Set α) (@Set.instMembership α) (@HasSups.sups (Set α) (@Set.hasSups α inst) s t)
            (@Max.max α (@SemilatticeSup.toMax α inst) a b)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  simp)

-- Set.sup_mem_sups, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sup_mem_sups.h7 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s t : Set α} {a b : α},
        @Membership.mem α (Set α) (@Set.instMembership α) s a →
          @Membership.mem α (Set α) (@Set.instMembership α) (@HasSups.sups (Set α) (@Set.hasSups α inst) s t)
            (@Max.max α (@SemilatticeSup.toMax α inst) a b)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  simp)

-- Set.inf_mem_infs, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inf_mem_infs.h6 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s t : Set α} {a b : α},
        @Membership.mem α (Set α) (@Set.instMembership α) t b →
          @Membership.mem α (Set α) (@Set.instMembership α) (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t)
            (@Min.min α (@SemilatticeInf.toMin α inst) a b)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Set.ofPred Nat fun (x : Nat) => False) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  simp)

-- Set.inf_mem_infs, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inf_mem_infs.h7 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s t : Set α} {a b : α},
        @Membership.mem α (Set α) (@Set.instMembership α) s a →
          @Membership.mem α (Set α) (@Set.instMembership α) (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t)
            (@Min.min α (@SemilatticeInf.toMin α inst) a b)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  simp)

-- Fin.take_update_of_ge, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.take_update_of_ge.h3.der.{u_1} : ∀ {n : ℕ} {α : Fin n → Sort u_1} (m : ℕ) (v : (i : Fin n) → α i) (i : Fin n), ↑i ≥ m → ∀ (x : α i), m ≤ n := by
  (intros; lia)
theorem HypCheckProof.Fin.take_update_of_ge.h3.{u_1} : ∀ {n : ℕ} {α : Fin n → Sort u_1} (m : ℕ) (v : (i : Fin n) → α i) (i : Fin n) (hi : ↑i ≥ m) (x : α i),
      Fin.take m (HypCheckProof.Fin.take_update_of_ge.h3.der m v i hi x) (Function.update v i x) =
        Fin.take m (HypCheckProof.Fin.take_update_of_ge.h3.der m v i hi x) v := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Fin.take_update_of_ge hc_x0 hc_x1 hc_x2 (@HypCheckProof.Fin.take_update_of_ge.h3.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x3 hc_x4 hc_x5 hc_x6

-- Ordnode.map.valid, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.map.valid.h7 : ¬∀ {α : Type} [inst : Preorder α] {β : Type} [inst_1 : Preorder β] {f : α → β},
        StrictMono f → ∀ {t : Ordnode α}, (Ordnode.map f t).Valid := fun hc_h => absurd (@hc_h (Bool) (Bool.instPartialOrder.toPreorder) (ℕ) (Nat.instPreorder) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) (Ordnode.node 0 Ordnode.nil Bool.false Ordnode.nil)) (by
  nofun)

-- List.Perm.kerase, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.kerase.h7 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {l₁ l₂ : List (Sigma β)},
        l₁.NodupKeys → (List.kerase a l₁).Perm (List.kerase a l₂) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([]) ([(⟨1, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp)) (by
  decide +kernel)

-- Part.sdiff_mem_sdiff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.sdiff_mem_sdiff.h6 : ¬∀ {α : Type} [inst : SDiff α] (a b : Part α) (ma mb : α), mb ∈ b → ma \ mb ∈ a \ b := fun hc_h => absurd (@hc_h (Bool) (Bool.instBooleanAlgebra.toSDiff) (0) (0) (Bool.true) (Bool.false) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.sdiff_mem_sdiff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.sdiff_mem_sdiff.h7 : ¬∀ {α : Type} [inst : SDiff α] (a b : Part α) (ma mb : α), ma ∈ a → ma \ mb ∈ a \ b := fun hc_h => absurd (@hc_h (Bool) (Bool.instBooleanAlgebra.toSDiff) (0) (⊥) (Bool.false) (Bool.false) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Mathlib.Meta.NormNum.IsInt.natCeil, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Mathlib.Meta.NormNum.IsInt.natCeil.h7 : ¬∀ {R : Type} [inst : Ring R] [inst_1 : LinearOrder R] [inst_2 : IsStrictOrderedRing R] [inst_3 : FloorSemiring R]
        (r : R) (m : ℕ), Mathlib.Meta.NormNum.IsNat ⌈r⌉₊ 0 := fun hc_h => absurd (@hc_h (ℤ) (Int.instRing) (Int.instLinearOrder) _ (FloorRing.toFloorSemiring) (1) (0)) (by
  nofun)

-- Finsupp.mapRange_surjective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mapRange_surjective.h6 : ¬∀ {α : Type} {M N : Type} [inst : Zero M] [inst_1 : Zero N] (e : M → N), Function.Surjective e → e 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Bool) (instZeroBool_mathlib) (instZeroBool_mathlib) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Part.union_mem_union, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.union_mem_union.h6 : ¬∀ {α : Type} [inst : Union α] (a b : Part α) (ma mb : α), mb ∈ b → ma ∪ mb ∈ a ∪ b := fun hc_h => absurd (@hc_h (Multiset ℕ) (Multiset.instUnion) (⊥) (0) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.union_mem_union, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.union_mem_union.h7 : ¬∀ {α : Type} [inst : Union α] (a b : Part α) (ma mb : α), ma ∈ a → ma ∪ mb ∈ a ∪ b := fun hc_h => absurd (@hc_h (Multiset ℕ) (Multiset.instUnion) (0) (⊥) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.div_mem_div, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.div_mem_div.h6 : ¬∀ {α : Type} [inst : Div α] (a b : Part α) (ma mb : α), mb ∈ b → ma / mb ∈ a / b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instDiv) (⊥) (0) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.div_mem_div, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.div_mem_div.h7 : ¬∀ {α : Type} [inst : Div α] (a b : Part α) (ma mb : α), ma ∈ a → ma / mb ∈ a / b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instDiv) (0) (⊥) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Set.domRestrict₂_comp_domRestrict₂, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.domRestrict₂_comp_domRestrict₂.h5 : ¬∀ {α : Type} {π : α → Type} {s t u : Set α}, t ⊆ u → s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.domRestrict₂_comp_domRestrict₂, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.domRestrict₂_comp_domRestrict₂.h6 : ¬∀ {α : Type} {π : α → Type} {s t u : Set α}, s ⊆ t → t ⊆ u := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- Nat.Prime.emultiplicity_choose_prime_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_choose_prime_pow.h3 : ¬∀ {p n k : ℕ}, k ≤ p ^ n → k ≠ 0 → emultiplicity p ((p ^ n).choose k) = ↑(n - multiplicity p k) := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide) (by
  decide)) (by
  simp)

-- Set.Nonempty.pairwise_iff_exists_forall, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.pairwise_iff_exists_forall.h4 : ¬∀ {α ι : Type} {r : α → α → Prop} {f : ι → α} {s : Set ι},
        s.Nonempty → (s.Pairwise (Function.onFun r f) ↔ ∃ (z : α), ∀ x ∈ s, r (f x) z) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ _ => False : Bool → Bool → Prop) (fun n => n % 2 == 0 : ℕ → Bool) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Fin.cast_eq_zero, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.cast_eq_zero.h2.der : ∀ {k l : Nat} [inst : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) l],
      @Eq Nat k l → ∀ (x : Fin k), @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) k := by
  (intros; lia)
theorem HypCheckProof.Fin.cast_eq_zero.h2 : ∀ {k l : Nat} [inst : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) l] (h : @Eq Nat k l) (x : Fin k),
      Iff (@Eq (Fin l) (@Fin.cast k l h x) (@OfNat.ofNat (Fin l) (nat_lit 0) (@Fin.instOfNat l inst (nat_lit 0))))
        (@Eq (Fin k) x
          (@OfNat.ofNat (Fin k) (nat_lit 0)
            (@Fin.instOfNat k (@HypCheckProof.Fin.cast_eq_zero.h2.der k l inst h x) (nat_lit 0)))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Fin.cast_eq_zero hc_x0 hc_x1 (@HypCheckProof.Fin.cast_eq_zero.h2.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x2 hc_x3 hc_x4

-- Fin.cast_eq_zero, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.cast_eq_zero.h3.der : ∀ {k l : Nat} [inst : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) k],
      @Eq Nat k l → ∀ (x : Fin k), @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) l := by
  (intros; lia)
theorem HypCheckProof.Fin.cast_eq_zero.h3 : ∀ {k l : Nat} [inst : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) k] (h : @Eq Nat k l) (x : Fin k),
      Iff
        (@Eq (Fin l) (@Fin.cast k l h x)
          (@OfNat.ofNat (Fin l) (nat_lit 0)
            (@Fin.instOfNat l (@HypCheckProof.Fin.cast_eq_zero.h3.der k l inst h x) (nat_lit 0))))
        (@Eq (Fin k) x (@OfNat.ofNat (Fin k) (nat_lit 0) (@Fin.instOfNat k inst (nat_lit 0)))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Fin.cast_eq_zero hc_x0 hc_x1 hc_x2 (@HypCheckProof.Fin.cast_eq_zero.h3.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x3 hc_x4

-- Fin.cast_eq_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cast_eq_zero.h4 : ¬∀ {k l : ℕ} [inst : NeZero k] [inst : NeZero l] (x : Fin k), k = l := fun hc_h => absurd (@hc_h (1) (2) _ _ ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.idxOf_append_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_append_of_notMem.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] {a : α}, a ∉ l₁ → List.idxOf a (l₁ ++ l₂) = l₁.length + List.idxOf a l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (1) (by
  decide)) (by
  decide +kernel)

-- List.idxOf_append_of_notMem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_append_of_notMem.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α},
        List.idxOf a (l₁ ++ l₂) = l₁.length + List.idxOf a l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (instBEqOfDecidableEq) _ (0)) (by
  decide +kernel)

-- Fin.castPred_succAbove_castPred, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_succAbove_castPred.h3 : ¬∀ {n : ℕ} {a : Fin (n + 2)} {b : Fin (n + 1)}, b ≠ Fin.last n → a ≠ Fin.last (n + 1) := fun hc_h => absurd (@hc_h (1) ((⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_succAbove_castPred, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_succAbove_castPred.h4 : ¬∀ {n : ℕ} {a : Fin (n + 2)} {b : Fin (n + 1)}, a ≠ Fin.last (n + 1) → b ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Set.image_image2_distrib_left, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_image2_distrib_left.h11 : ¬∀ {α α' β γ δ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {g : γ → δ} {f' : α' → β → δ} {g' : α → α'},
        g '' Set.image2 f s t = Set.image2 f' (g' '' s) t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- exists_ne_zero_dotProduct_eq_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.exists_ne_zero_dotProduct_eq_zero.h4 : ¬∀ {m α : Type} [inst : Fintype m] [inst_1 : CommRing α] [inst_2 : Nontrivial α] (a : m → α),
        ∃ (b : m → α), b ≠ 0 ∧ b ⬝ᵥ a = 0 := fun hc_h => absurd (@hc_h (Unit) (Bool) (PUnit.fintype) (BooleanRing.toCommRing) _ (fun (a : Unit) => Bool.true)) (by
  decide +kernel)

-- exists_ne_zero_dotProduct_eq_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.exists_ne_zero_dotProduct_eq_zero.h5 : ¬∀ {m α : Type} [inst : Fintype m] [inst_1 : CommRing α] [inst_2 : Nontrivial m] (a : m → α),
        ∃ (b : m → α), b ≠ 0 ∧ b ⬝ᵥ a = 0 := fun hc_h => absurd (@hc_h (Bool) (Unit) (Bool.fintype) (PUnit.commRing) _ (fun (a : Bool) => PUnit.unit)) (by
  decide +kernel)

-- Set.surjOn_of_subsingleton', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.surjOn_of_subsingleton'.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β} (f : α → β), (t.Nonempty → s.Nonempty) → Set.SurjOn f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.surjOn_of_subsingleton', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.surjOn_of_subsingleton'.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} [inst : Subsingleton β] (f : α → β), Set.SurjOn f s t := fun hc_h => absurd (@hc_h (ℕ) (Unit) ({x : ℕ | False}) (⊤) _ (fun (a : ℕ) => PUnit.unit)) (by
  simp)

-- not_injective_dotProduct_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_injective_dotProduct_left.h4 : ¬∀ {m α : Type} [inst : Fintype m] [inst_1 : CommRing α] [inst_2 : Nontrivial α] (a : m → α),
        ¬Function.Injective (dotProduct a) := fun hc_h => absurd (@hc_h (Unit) (Bool) (PUnit.fintype) (BooleanRing.toCommRing) _ (fun (a : Unit) => Bool.true)) (by
  decide +kernel)

-- not_injective_dotProduct_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_injective_dotProduct_left.h5 : ¬∀ {m α : Type} [inst : Fintype m] [inst_1 : CommRing α] [inst_2 : Nontrivial m] (a : m → α),
        ¬Function.Injective (dotProduct a) := fun hc_h => absurd (@hc_h (Bool) (Unit) (Bool.fintype) (PUnit.commRing) _ (fun (a : Bool) => PUnit.unit)) (by
  decide +kernel)

-- Set.eq_of_subset_of_ncard_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_subset_of_ncard_le.h3 : ¬∀ {α : Type} {s t : Set α}, t.ncard ≤ s.ncard → autoParam t.Finite Set.eq_of_subset_of_ncard_le._auto_1 → s = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.eq_of_subset_of_ncard_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_subset_of_ncard_le.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → autoParam t.Finite Set.eq_of_subset_of_ncard_le._auto_1 → s = t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.eq_of_subset_of_ncard_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_subset_of_ncard_le.h5 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → t.ncard ≤ s.ncard → s = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) (by
  simp) (by
  simp)) (by
  simp)

-- EReal.toReal_eq_toReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_eq_toReal.h2 : ¬∀ {x y : EReal}, x ≠ ⊥ → y ≠ ⊤ → y ≠ ⊥ → (x.toReal = y.toReal ↔ x = y) := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.toReal_eq_toReal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_eq_toReal.h3 : ¬∀ {x y : EReal}, x ≠ ⊤ → y ≠ ⊤ → y ≠ ⊥ → (x.toReal = y.toReal ↔ x = y) := fun hc_h => absurd (@hc_h (⊥) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.toReal_eq_toReal, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_eq_toReal.h4 : ¬∀ {x y : EReal}, x ≠ ⊤ → x ≠ ⊥ → y ≠ ⊥ → (x.toReal = y.toReal ↔ x = y) := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.toReal_eq_toReal, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_eq_toReal.h5 : ¬∀ {x y : EReal}, x ≠ ⊤ → x ≠ ⊥ → y ≠ ⊤ → (x.toReal = y.toReal ↔ x = y) := fun hc_h => absurd (@hc_h (0) (⊥) (by
  decide) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.toReal_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_add.h3 : ¬∀ {x y : EReal}, x ≠ ⊤ → y ≠ ⊤ → y ≠ ⊥ → (x + y).toReal = x.toReal + y.toReal := fun hc_h => absurd (@hc_h (⊥) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.toReal_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_add.h5 : ¬∀ {x y : EReal}, x ≠ ⊤ → x ≠ ⊥ → y ≠ ⊤ → (x + y).toReal = x.toReal + y.toReal := fun hc_h => absurd (@hc_h (1) (⊥) (by
  decide) (by
  decide) (by
  decide)) (by
  simp)

-- Set.mapsTo_of_subsingleton', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mapsTo_of_subsingleton'.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β} (f : α → β), (s.Nonempty → t.Nonempty) → Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.mapsTo_of_subsingleton', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mapsTo_of_subsingleton'.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} [inst : Subsingleton β] (f : α → β), Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (Unit) ({n : ℕ | n = 0}) (∅) _ (fun (a : ℕ) => PUnit.unit)) (by
  simp)

-- memPartitionSet_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.memPartitionSet_of_mem.h5 : ¬∀ {α : Type} {f : ℕ → Set α} {n : ℕ} {a : α} {s : Set α}, a ∈ s → memPartitionSet f n a = s := fun hc_h => absurd (@hc_h (Bool) (fun (a : ℕ) => {b : Bool | b = Bool.true}) (0) (Bool.true) ({b : Bool | b = Bool.true}) (by
  decide)) (by
  simp)

-- EReal.div_eq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_eq_iff.h3 : ¬∀ {a b c : EReal}, b ≠ ⊤ → b ≠ 0 → (c / b = a ↔ c = a * b) := fun hc_h => absurd (@hc_h (0) (⊥) (1) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.div_eq_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_eq_iff.h4 : ¬∀ {a b c : EReal}, b ≠ ⊥ → b ≠ 0 → (c / b = a ↔ c = a * b) := fun hc_h => absurd (@hc_h (0) (⊤) (1) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.div_eq_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_eq_iff.h5 : ¬∀ {a b c : EReal}, b ≠ ⊥ → b ≠ ⊤ → (c / b = a ↔ c = a * b) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.div_lt_div_right_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_lt_div_right_of_pos.h3 : ¬∀ {a b c : EReal}, c ≠ ⊤ → a < b → a / c < b / c := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide) (by
  simp)) (by
  simp)

-- EReal.div_lt_div_right_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_lt_div_right_of_pos.h5 : ¬∀ {a b c : EReal}, 0 < c → c ≠ ⊤ → a / c < b / c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  simp) (by
  decide)) (by
  simp)

-- Set.disjoint_image_of_injective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_image_of_injective.h6 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f → ∀ {s t : Set α}, Disjoint (f '' s) (f '' t) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true})) (by
  simp)

-- Matrix.single_apply_of_col_ne, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.single_apply_of_col_ne.h10 : ¬∀ {m n α : Type} [inst : DecidableEq m] [inst_1 : DecidableEq n] [inst_2 : Zero α] (i i' : m) {j j' : n} (a : α),
        Matrix.single i j a i' j' = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (0) (0) (0) (0) (1)) (by
  decide +kernel)

-- Set.image_eq_preimage_of_leftInvOn_injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_eq_preimage_of_leftInvOn_injOn.h5 : ¬∀ {α β : Type} {f : α → β} {g : β → α} {s : Set α}, Set.InjOn g (g ⁻¹' s) → f '' s = g ⁻¹' s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n : ℕ → ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- List.Subperm.append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.append.h5 : ¬∀ {α : Type} {l₁ l₂ r₁ r₂ : List α}, r₁.Subperm r₂ → (l₁ ++ r₁).Subperm (l₂ ++ r₂) := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Subperm.append, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.append.h6 : ¬∀ {α : Type} {l₁ l₂ r₁ r₂ : List α}, l₁.Subperm l₂ → (l₁ ++ r₁).Subperm (l₂ ++ r₂) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- Nat.binomial_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.binomial_one.h5 : ¬∀ {α : Type} {f : α → ℕ} {a b : α} [inst : DecidableEq α], f a = 1 → Nat.multinomial {a, b} f = (f b).succ := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0) (instDecidableEqNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.binomial_one, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.binomial_one.h6 : ¬∀ {α : Type} {f : α → ℕ} {a b : α} [inst : DecidableEq α], a ≠ b → Nat.multinomial {a, b} f = (f b).succ := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (1) (0) (instDecidableEqNat) (by
  decide)) (by
  decide +kernel)

-- Set.image_image2_right_anticomm, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_image2_right_anticomm.h11 : ¬∀ {α β β' γ δ : Type} {s : Set α} {t : Set β} {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ},
        Set.image2 f s (g '' t) = g' '' Set.image2 f' t s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun a b => a - b : ℕ → ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- List.countP_diff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countP_diff.h2 : ¬∀ {α : Type} [inst : BEq α] {l₁ l₂ : List α},
        l₂.Subperm l₁ → ∀ (p : α → Bool), List.countP p (l₁.diff l₂) = List.countP p l₁ - List.countP p l₂ := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) ([0]) ([0]) (by
  decide) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- List.countP_diff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countP_diff.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ : List α} (p : α → Bool),
        List.countP p (l₁.diff l₂) = List.countP p l₁ - List.countP p l₂ := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ ([0]) ([1]) (fun _ => true : ℕ → Bool)) (by
  decide +kernel)

-- List.Nodup.mem_sdiff_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.mem_sdiff_iff.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {a : α} [inst : BEq α], l₁.Nodup → (a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂) := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([1]) (0) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (by
  decide)) (by
  decide +kernel)

-- Set.image2_image_left_comm, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_image_left_comm.h11 : ¬∀ {α α' β γ δ : Type} {s : Set α} {t : Set β} {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ},
        Set.image2 f (g '' s) t = g' '' Set.image2 f' s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.inter_subset_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_subset_inter.h5 : ¬∀ {α : Type} {s₁ s₂ t₁ t₂ : Set α}, s₂ ⊆ t₂ → s₁ ∩ s₂ ⊆ t₁ ∩ t₂ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.inter_subset_inter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_subset_inter.h6 : ¬∀ {α : Type} {s₁ s₂ t₁ t₂ : Set α}, s₁ ⊆ t₁ → s₁ ∩ s₂ ⊆ t₁ ∩ t₂ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- Matrix.single_apply_of_row_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.single_apply_of_row_ne.h8 : ¬∀ {m n α : Type} [inst : DecidableEq m] [inst_1 : DecidableEq n] [inst_2 : Zero α] {i i' : m} (j j' : n) (a : α),
        Matrix.single i j a i' j' = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (0) (0) (0) (0) (1)) (by
  decide +kernel)

-- Set.inter_eq_inter_mono_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_eq_inter_mono_right.h5 : ¬∀ {α : Type} {s t u₁ u₂ : Set α}, u₂ ⊆ u₁ → s ∩ u₂ = t ∩ u₂ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.union_eq_union_mono_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_eq_union_mono_right.h5 : ¬∀ {α : Type} {s t u₁ u₂ : Set α}, u₁ ⊆ u₂ → s ∪ u₂ = t ∪ u₂ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.Finite.exists_subset_finite_image_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.exists_subset_finite_image_eq.h6 : ¬∀ {α β : Type} {f : α → β} {s : Set α} {u : Set β}, u.Finite → ∃ t ⊆ s, ∃ (_ : t.Finite), f '' t = u := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.union_eq_union_mono_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_eq_union_mono_left.h5 : ¬∀ {α : Type} {t u s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂ ∪ t = s₂ ∪ u := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  rfl)) (by
  simp)

-- Function.invFunOn_pos, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Function.invFunOn_pos.h5.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {b : β},
      (∃ (a : α), And (@Membership.mem α (Set α) (@Set.instMembership α) s a) (@Eq β (f a) b)) → Nonempty α := by
  (intros; tauto)
theorem HypCheckProof.Function.invFunOn_pos.h5.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {b : β}
      (h : ∃ (a : α), And (@Membership.mem α (Set α) (@Set.instMembership α) s a) (@Eq β (f a) b)),
      And
        (@Membership.mem α (Set α) (@Set.instMembership α) s
          (@Function.invFunOn α β (@HypCheckProof.Function.invFunOn_pos.h5.der α β s f b h) f s b))
        (@Eq β (f (@Function.invFunOn α β (@HypCheckProof.Function.invFunOn_pos.h5.der α β s f b h) f s b)) b) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Function.invFunOn_pos hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Function.invFunOn_pos.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- Function.invFunOn_pos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.invFunOn_pos.h6 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {b : β} [inst : Nonempty α],
        Function.invFunOn f s b ∈ s ∧ f (Function.invFunOn f s b) = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (0) _) (by
  simp)

-- Subtype.map_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.map_injective.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} {f : α → β}, Function.Injective f → ∀ (a : α), p a → q (f a) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => b = true : Bool → Prop) (fun n => n = 0 : ℕ → Prop) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  decide +kernel)

-- Nat.find_add, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.find_add.h4.der : ∀ {n : Nat} {p : Nat → Prop} [inst : @DecidablePred Nat p]
      {hₘ : ∃ (m : Nat), p (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m n)}, ∃ (n : Nat), p n := by
  (intros; grind)
theorem HypCheckProof.Nat.find_add.h4 : ∀ {n : Nat} {p : Nat → Prop} [inst : @DecidablePred Nat p]
      {hₘ : ∃ (m : Nat), p (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m n)},
      @LE.le Nat instLENat n (@Nat.find p inst (@HypCheckProof.Nat.find_add.h4.der n p inst hₘ)) →
        @Eq Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@Nat.find (fun (n_1 : Nat) => p (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n_1 n))
              (fun (a : Nat) => inst (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a n)) hₘ)
            n)
          (@Nat.find p inst (@HypCheckProof.Nat.find_add.h4.der n p inst hₘ)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Nat.find_add hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Nat.find_add.h4.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x4

-- Nat.find_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_add.h5 : ¬∀ {n : ℕ} {p : ℕ → Prop} [inst : DecidablePred p] {hₘ : ∃ (m : ℕ), p (m + n)} {hₙ : ∃ (n : ℕ), p n},
        Nat.find hₘ + n = Nat.find hₙ := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (1) (fun _ => True : ℕ → Prop) (fun (a : ℕ) => instDecidableTrue) hc_k0 hc_k1) (by
  simp)

-- List.subset_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subset_inter.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l l₁ l₂ : List α}, l ⊆ l₂ → l ⊆ l₁ ∩ l₂ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.subset_inter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subset_inter.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {l l₁ l₂ : List α}, l ⊆ l₁ → l ⊆ l₁ ∩ l₂ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- Nat.find_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_congr.h5 : ¬∀ {p q : ℕ → Prop} [inst : DecidablePred p] [inst : DecidablePred q] {x : ℕ}, (∀ n ≤ x, p n ↔ q n) → p x := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableEqNat a 0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.find_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_congr.h6 : ¬∀ {p q : ℕ → Prop} [inst : DecidablePred p] [inst : DecidablePred q] {x : ℕ}, p x → ∀ n ≤ x, p n ↔ q n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableFalse) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.infinite_of_not_bddAbove, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_of_not_bddAbove.h5 : ¬∀ {α : Type} [inst : Preorder α] [inst : IsDirectedOrder α] [inst : Nonempty α] {s : Set α}, s.Infinite := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) _ _ ({n : ℕ | n = 0})) (by
  simp)

-- Nat.decreasingInduction_succ, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.decreasingInduction_succ.h6.der.{u_1} : ∀ {m n : Nat}
      {motive :
        (m : Nat) →
          @LE.le Nat instLENat m
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Sort u_1}
      (of_succ :
        (k : Nat) →
          (h :
              @LT.lt Nat instLTNat k
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                h →
              motive k
                (@Nat.le_of_succ_le k
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  h))
      (self :
        motive
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Nat.le_refl
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
      @LE.le Nat instLENat m n →
        @LE.le Nat instLENat m
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  (intros; solve_by_elim)
theorem HypCheckProof.Nat.decreasingInduction_succ.h6.{u_1} : ∀ {m n : Nat}
      {motive :
        (m : Nat) →
          @LE.le Nat instLENat m
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Sort u_1}
      (of_succ :
        (k : Nat) →
          (h :
              @LT.lt Nat instLTNat k
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                h →
              motive k
                (@Nat.le_of_succ_le k
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  h))
      (self :
        motive
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Nat.le_refl
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (mn : @LE.le Nat instLENat m n),
      @Eq (motive m (@HypCheckProof.Nat.decreasingInduction_succ.h6.der m n motive of_succ self mn))
        (@Nat.decreasingInduction
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          motive of_succ self m (@HypCheckProof.Nat.decreasingInduction_succ.h6.der m n motive of_succ self mn))
        (@Nat.decreasingInduction n (fun (m : Nat) (h : @LE.le Nat instLENat m n) => motive m (@Nat.le_succ_of_le m n h))
          (fun (x : Nat) (x_1 : @LT.lt Nat instLTNat x n) =>
            of_succ x
              (@Nat.le_succ_of_le
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) x
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                n x_1))
          (of_succ n
            (Nat.le_refl
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            self)
          m mn) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Nat.decreasingInduction_succ hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Nat.decreasingInduction_succ.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Set.eq_of_subset_of_card_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_subset_of_card_le.h5 : ¬∀ {α : Type} {s t : Set α} [inst : Fintype ↑s] [inst_1 : Fintype ↑t], Fintype.card ↑t ≤ Fintype.card ↑s → s = t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true})) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.false})) (by
  decide)) (by
  simp)

-- Set.eq_of_subset_of_card_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_subset_of_card_le.h6 : ¬∀ {α : Type} {s t : Set α} [inst : Fintype ↑s] [inst : Fintype ↑t], s ⊆ t → s = t := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | False}) ({b : Bool | b = Bool.true}) (Subtype.fintype (Membership.mem {x : Bool | False})) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true})) (by
  simp)) (by
  simp)

-- Nat.find_mono_of_le, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.find_mono_of_le.h5.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.find_mono_of_le.h5.prem0 : ∀ n ≤ 1, n = 0 → (fun (n : ℕ) => n = 0) n := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.find_mono_of_le.h5 : ¬∀ {p q : ℕ → Prop} [inst : DecidablePred p] [inst : DecidablePred q] {x : ℕ}, (∀ n ≤ x, q n → p n) → q x := fun hc_h => HypCheckProof.Nat.find_mono_of_le.h5.inst (@hc_h (fun (n : ℕ) => n = 0) (fun (n : ℕ) => n = 0) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableEqNat a 0) (1) HypCheckProof.Nat.find_mono_of_le.h5.prem0)

-- Nat.find_mono_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_mono_of_le.h6 : ¬∀ {p q : ℕ → Prop} [inst : DecidablePred p] [inst : DecidablePred q] {x : ℕ}, q x → ∀ n ≤ x, q n → p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- PFun.asSubtype_eq_of_mem, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.PFun.asSubtype_eq_of_mem.h6.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {f : α →. β} {x : α} {y : β}, y ∈ f x → x ∈ f.Dom := by
  (intros; simp_all <;> grind)
theorem HypCheckProof.PFun.asSubtype_eq_of_mem.h6.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x),
      f.asSubtype (⟨x, HypCheckProof.PFun.asSubtype_eq_of_mem.h6.der fxy⟩ : { x : α // x ∈ f.Dom }) = y := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @PFun.asSubtype_eq_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.PFun.asSubtype_eq_of_mem.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Set.BijOn.compl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.compl.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Function.Bijective f → Set.BijOn f sᶜ tᶜ := fun hc_h => absurd (@hc_h (Bool) (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (not : Bool → Bool) (by
  decide)) (by
  simp)

-- Set.image_image2_right_comm, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_image2_right_comm.h11 : ¬∀ {α β β' γ δ : Type} {s : Set α} {t : Set β} {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ},
        Set.image2 f s (g '' t) = g' '' Set.image2 f' s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun a b => a - b : ℕ → ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.iInter_congr_Prop, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iInter_congr_Prop.h5 : ¬∀ {α : Type} {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α}, p ↔ q := fun hc_h => absurd (@hc_h (ℕ) (True) (False) (fun (a : True) => {n : ℕ | n = 0}) (fun (a : False) => {n : ℕ | n = 0})) (by
  decide +kernel)

-- Set.iInter_congr_Prop, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iInter_congr_Prop.h6 : ¬∀ {α : Type} {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α}, (p ↔ q) → Set.iInter f₁ = Set.iInter f₂ := fun hc_h => absurd (@hc_h (ℕ) (True) (True) (fun (a : True) => {n : ℕ | n = 0}) (fun (a : True) => {x : ℕ | False}) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- PSigma.subtype_ext, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PSigma.subtype_ext.h5 : Not
      (∀ {α β : Type} {p : α → β → Prop} {x₀ x₁ : @PSigma α fun (a : α) => @Subtype β (p a)},
        @Eq β
            (@Subtype.val β (p (@PSigma.fst α (fun (a : α) => @Subtype β (p a)) x₀))
              (@PSigma.snd α (fun (a : α) => @Subtype β (p a)) x₀))
            (@Subtype.val β (p (@PSigma.fst α (fun (a : α) => @Subtype β (p a)) x₁))
              (@PSigma.snd α (fun (a : α) => @Subtype β (p a)) x₁)) →
          @Eq (@PSigma α fun (a : α) => @Subtype β (p a)) x₀ x₁) := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@PSigma.mk Nat (fun (a : Nat) => @Subtype Bool ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) a))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Subtype.mk Bool
        ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        Bool.true
        (@of_decide_eq_true
          ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            Bool.true)
          (instDecidableEqBool Bool.true Bool.true)
          (@id
            (@Eq Bool
              (@Decidable.decide
                ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Bool.true)
                (instDecidableEqBool Bool.true Bool.true))
              Bool.true)
            (@Eq.refl Bool Bool.true))))) (@PSigma.mk Nat (fun (a : Nat) => @Subtype Bool ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) a))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Subtype.mk Bool
        ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        Bool.true
        (@of_decide_eq_true
          ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            Bool.true)
          (instDecidableEqBool Bool.true Bool.true)
          (@id
            (@Eq Bool
              (@Decidable.decide
                ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.true)
                (instDecidableEqBool Bool.true Bool.true))
              Bool.true)
            (@Eq.refl Bool Bool.true))))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.mem_range_iff_mem_finset_range_of_mod_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_range_iff_mem_finset_range_of_mod_eq.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {f : ℤ → α} {a : α} {n : ℕ},
        (∀ (i : ℤ), f (i % ↑n) = f i) → (a ∈ Set.range f ↔ a ∈ Finset.image (fun (i : ℕ) => f ↑i) (Finset.range n)) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (fun (a : ℤ) => 0) (0) (0) (by
  simp)) (by
  simp)

-- List.Shortlex.cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Shortlex.cons.h6 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Irrefl r] {a : α} {s t : List α}, List.Shortlex r (a :: s) (a :: t) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ (0) ([]) ([])) (by
  simp)

-- Nat.chineseRemainderOfList_modEq_unique, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfList_modEq_unique.h4.inst : ¬List.Pairwise (Function.onFun Nat.Coprime fun (x : ℕ) => 0) [0, 1] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfList_modEq_unique.h4.prem0 : ∀ i ∈ [0, 1], 0 ≡ (fun (x : ℕ) => 0) i [MOD (fun (x : ℕ) => 0) i] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.chineseRemainderOfList_modEq_unique.h4 : ¬∀ {ι : Type} (a s : ι → ℕ) (l : List ι) {z : ℕ},
        (∀ i ∈ l, z ≡ a i [MOD s i]) → List.Pairwise (Function.onFun Nat.Coprime s) l := fun hc_h => HypCheckProof.Nat.chineseRemainderOfList_modEq_unique.h4.inst (@hc_h (ℕ) (fun (x : ℕ) => 0) (fun (x : ℕ) => 0) ([0, 1]) (0) HypCheckProof.Nat.chineseRemainderOfList_modEq_unique.h4.prem0)

-- Nat.chineseRemainderOfList_modEq_unique, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainderOfList_modEq_unique.h6 : ¬∀ {ι : Type} (a s : ι → ℕ) (l : List ι) (co : List.Pairwise (Function.onFun Nat.Coprime s) l) {z : ℕ},
        z ≡ ↑(Nat.chineseRemainderOfList a s l co) [MOD (List.map s l).prod] := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ([0]) hc_k0 (0)) (by
  decide +kernel)

-- List.Lex.imp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.imp.h3 : ¬∀ {α : Type} {r s : α → α → Prop} (l₁ l₂ : List α), List.Lex r l₁ l₂ → List.Lex s l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Lex.imp, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.imp.h6 : ¬∀ {α : Type} {r s : α → α → Prop}, (∀ (a b : α), r a b → s a b) → ∀ (l₁ l₂ : List α), List.Lex s l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (by
  simp) ([]) ([])) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_iff.h3 : ¬∀ {p k n : ℕ}, n < p → n ≤ k → (p ∣ k.choose n ↔ ∃ i < n, p ∣ k - i) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_iff.h4 : ¬∀ {p k n : ℕ}, Nat.Prime p → n ≤ k → (p ∣ k.choose n ↔ ∃ i < n, p ∣ k - i) := fun hc_h => absurd (@hc_h (2) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.not_dvd_lcm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.not_dvd_lcm.h4 : ¬∀ {p a b : ℕ}, Nat.Prime p → ¬p ∣ b → ¬p ∣ a.lcm b := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.not_dvd_lcm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.not_dvd_lcm.h5 : ¬∀ {p a b : ℕ}, Nat.Prime p → ¬p ∣ a → ¬p ∣ a.lcm b := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.le_nth_of_monotoneOn_of_surjOn, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_nth_of_monotoneOn_of_surjOn.h2 : ¬∀ {p : ℕ → Prop} (f : ℕ → ℕ),
        MonotoneOn f {n : ℕ | ∀ (hf : (Set.ofPred p).Finite), n < hf.toFinset.card} →
          ∀ {n : ℕ}, (∀ (hf : (Set.ofPred p).Finite), n < hf.toFinset.card) → f n ≤ Nat.nth p n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (0) (by
  simp)) (by
  simp)

-- Nat.lt_of_nth_lt_nth_of_lt_card, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_of_nth_lt_nth_of_lt_card.h4 : ¬∀ {p : ℕ → Prop} (hf : (Set.ofPred p).Finite) {m n : ℕ}, m < hf.toFinset.card → m < n := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (fun n => n = 0 : ℕ → Prop) hc_k0 (0) (0) hc_k1) (by
  simp)

-- Set.SurjOn.image_invFunOn_image, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.image_invFunOn_image.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} [inst : Nonempty α], f '' Function.invFunOn f s '' t = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) _) (by
  simp)

-- Ordnode.balancedSz_down, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balancedSz_down.h3 : ¬∀ {l r₁ r₂ : ℕ}, l + r₂ ≤ 1 ∨ l ≤ Ordnode.delta * r₁ → Ordnode.BalancedSz l r₂ → Ordnode.BalancedSz l r₁ := fun hc_h => absurd (@hc_h (0) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.balancedSz_down, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balancedSz_down.h4 : ¬∀ {l r₁ r₂ : ℕ}, r₁ ≤ r₂ → Ordnode.BalancedSz l r₂ → Ordnode.BalancedSz l r₁ := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.balancedSz_down, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balancedSz_down.h5 : ¬∀ {l r₁ r₂ : ℕ}, r₁ ≤ r₂ → l + r₂ ≤ 1 ∨ l ≤ Ordnode.delta * r₁ → Ordnode.BalancedSz l r₁ := fun hc_h => absurd (@hc_h (0) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul.h5 : ¬∀ {n a b c d : ℤ}, c ≡ d [ZMOD n] → a * c ≡ b * d [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.mul, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul.h6 : ¬∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → a * c ≡ b * d [ZMOD n] := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.add_left_cancel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add_left_cancel.h5 : ¬∀ {n a b c d : ℤ}, a + c ≡ b + d [ZMOD n] → c ≡ d [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.add_left_cancel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add_left_cancel.h6 : ¬∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.sub, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.sub.h5 : ¬∀ {n a b c d : ℤ}, c ≡ d [ZMOD n] → a - c ≡ b - d [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.sub, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.sub.h6 : ¬∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → a - c ≡ b - d [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_prime_pow_of_dvd_least_prime_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_prime_pow_of_dvd_least_prime_pow.h3 : ¬∀ {a p k : ℕ}, ¬a ∣ p ^ k → a ∣ p ^ (k + 1) → a = p ^ (k + 1) := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_prime_pow_of_dvd_least_prime_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_prime_pow_of_dvd_least_prime_pow.h4 : ¬∀ {a p k : ℕ}, Nat.Prime p → a ∣ p ^ (k + 1) → a = p ^ (k + 1) := fun hc_h => absurd (@hc_h (1) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_prime_pow_of_dvd_least_prime_pow, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_prime_pow_of_dvd_least_prime_pow.h5 : ¬∀ {a p k : ℕ}, Nat.Prime p → ¬a ∣ p ^ k → a = p ^ (k + 1) := fun hc_h => absurd (@hc_h (0) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Option.map_map₂_distrib_right, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map_map₂_distrib_right.h11 : ¬∀ {α β γ δ : Type} {f : α → β → γ} {a : Option α} {b : Option β} {β' : Type} {g : γ → δ} {f' : α → β' → δ}
        {g' : β → β'}, Option.map g (Option.map₂ f a b) = Option.map₂ f' a (Option.map g' b) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (Option.some 0) (Option.some 0) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Option.map_map₂_right_comm, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map_map₂_right_comm.h11 : ¬∀ {α β γ δ : Type} {a : Option α} {b : Option β} {β' : Type} {f : α → β' → γ} {g : β → β'} {f' : α → β → δ}
        {g' : δ → γ}, Option.map₂ f a (Option.map g b) = Option.map g' (Option.map₂ f' a b) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (Option.some 0) (Option.some 0) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Nat.Prime.not_dvd_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.not_dvd_mul.h3 : ¬∀ {p m n : ℕ}, ¬p ∣ m → ¬p ∣ n → ¬p ∣ m * n := fun hc_h => absurd (@hc_h (4) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.not_dvd_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.not_dvd_mul.h4 : ¬∀ {p m n : ℕ}, Nat.Prime p → ¬p ∣ n → ¬p ∣ m * n := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.not_dvd_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.not_dvd_mul.h5 : ¬∀ {p m n : ℕ}, Nat.Prime p → ¬p ∣ m → ¬p ∣ m * n := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.cast_ncard_sdiff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.cast_ncard_sdiff.h5 : Not
      (∀ {α : Type} {s t : Set α} {R : Type} [inst : AddGroupWithOne R],
        @Set.Finite α t →
          @Eq R
            (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst))
              (@Set.ncard α (@SDiff.sdiff (Set α) (@Set.instSDiff α) t s)))
            (@HSub.hSub R R R
              (@instHSub R (@SubNegMonoid.toSub R (@AddGroup.toSubNegMonoid R (@AddGroupWithOne.toAddGroup R inst))))
              (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst)) (@Set.ncard α t))
              (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst)) (@Set.ncard α s)))) := fun hc_h => absurd (@hc_h (Nat) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (Int) (@Ring.toAddGroupWithOne Int Int.instRing) (by
  simp)) (by
  simp)

-- Set.exists_min_image, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_min_image.h6 : ¬∀ {α β : Type} [inst : LinearOrder β] (s : Set α) (f : α → β), s.Finite → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- ENat.mul_le_mul_of_le_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.mul_le_mul_of_le_right.h3 : ¬∀ {a x y : ℕ∞}, a ≠ 0 → a ≠ ⊤ → x * a ≤ y * a := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- ENat.mul_le_mul_of_le_right, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.ENat.mul_le_mul_of_le_right.h4.gneg : ∀ {a x y : ℕ∞}, x ≤ y → ¬a ≠ 0 → a ≠ ⊤ → x * a ≤ y * a := by
  (intros; simp_all; done)
theorem HypCheckProof.ENat.mul_le_mul_of_le_right.h4 : ∀ {a x y : ℕ∞}, x ≤ y → a ≠ ⊤ → x * a ≤ y * a := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5
  exact Classical.byCases (fun hc_h => @ENat.mul_le_mul_of_le_right hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5) (fun hc_hn => @HypCheckProof.ENat.mul_le_mul_of_le_right.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5)

-- Nat.div_dvd_div_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_dvd_div_iff_left.h3 : ¬∀ {n m k : ℕ}, m ∣ k → n ∣ k → (k / m ∣ k / n ↔ n ∣ m) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.div_dvd_div_iff_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_dvd_div_iff_left.h4 : ¬∀ {n m k : ℕ}, 0 < k → n ∣ k → (k / m ∣ k / n ↔ n ∣ m) := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.div_dvd_div_iff_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_dvd_div_iff_left.h5 : ¬∀ {n m k : ℕ}, 0 < k → m ∣ k → (k / m ∣ k / n ↔ n ∣ m) := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsSuffix.idxOf_add_length_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsSuffix.idxOf_add_length_le.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (a : α),
        List.idxOf a l₂ + l₁.length ≤ List.idxOf a l₁ + l₂.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (instBEqOfDecidableEq) _ (0)) (by
  decide +kernel)

-- Function.invFunOn_eq, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Function.invFunOn_eq.h5.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {b : β},
      (∃ (a : α), And (@Membership.mem α (Set α) (@Set.instMembership α) s a) (@Eq β (f a) b)) → Nonempty α := by
  (intros; tauto)
theorem HypCheckProof.Function.invFunOn_eq.h5.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {b : β}
      (h : ∃ (a : α), And (@Membership.mem α (Set α) (@Set.instMembership α) s a) (@Eq β (f a) b)),
      @Eq β (f (@Function.invFunOn α β (@HypCheckProof.Function.invFunOn_eq.h5.der α β s f b h) f s b)) b := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Function.invFunOn_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Function.invFunOn_eq.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- Function.invFunOn_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.invFunOn_eq.h6 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {b : β} [inst : Nonempty α], f (Function.invFunOn f s b) = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (0) _) (by
  decide +kernel)

-- Nat.ModEq.eq_of_lt_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.eq_of_lt_of_lt.h3 : ¬∀ {m a b : ℕ}, a < m → b < m → a = b := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.eq_of_lt_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.eq_of_lt_of_lt.h4 : ¬∀ {m a b : ℕ}, a ≡ b [MOD m] → b < m → a = b := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.eq_of_lt_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.eq_of_lt_of_lt.h5 : ¬∀ {m a b : ℕ}, a ≡ b [MOD m] → a < m → a = b := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.enumerate_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.enumerate_mem.h2 : ¬∀ {α : Type} (sel : Set α → Option α) {s : Set α} {n : ℕ} {a : α}, Set.enumerate sel s n = Option.some a → a ∈ s := fun hc_h => absurd (@hc_h (Bool) (fun (a : Set Bool) => Option.some Bool.false) ({b : Bool | b = Bool.true}) (0) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Set.enumerate_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.enumerate_mem.h6 : ¬∀ {α : Type} (sel : Set α → Option α),
        (∀ (s : Set α) (a : α), sel s = Option.some a → a ∈ s) → ∀ {s : Set α} {n : ℕ} {a : α}, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (fun (a : Set ℕ) => Option.none) (by
  simp) ({n : ℕ | n = 0}) (0) (1)) (by
  decide +kernel)

-- Nat.ModEq.of_natCast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.of_natCast.h6 : ¬∀ {M : Type} [inst : AddCommMonoidWithOne M] [inst : CharZero M] {a b n : ℕ}, a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddCommMonoidWithOne) _ (0) (1) (0)) (by
  decide +kernel)

-- Multiset.noncommFold_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommFold_coe.h2 : ¬∀ {α : Type} (op : α → α → α) (l : List α),
        ({x : α | x ∈ ↑l}.Pairwise fun (x y : α) => op x y = op y x) → ∀ (a : α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !a || b : Bool → Bool → Bool) ([]) (by
  simp) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.notMem_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.notMem_of_subset.h3 : ¬∀ {α : Type} {l l₁ : List α} {a : α}, a ∉ l₁ → a ∉ l := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- List.notMem_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.notMem_of_subset.h5 : ¬∀ {α : Type} {l l₁ : List α}, l ⊆ l₁ → ∀ {a : α}, a ∉ l := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0]) (by
  decide) (0)) (by
  decide +kernel)

-- List.append_subset_of_subset_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.append_subset_of_subset_of_subset.h4 : ¬∀ {α : Type} {l₁ l₂ l : List α}, l₂ ⊆ l → l₁ ++ l₂ ⊆ l := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.append_subset_of_subset_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.append_subset_of_subset_of_subset.h5 : ¬∀ {α : Type} {l₁ l₂ l : List α}, l₁ ⊆ l → l₁ ++ l₂ ⊆ l := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- Finsupp.apply_single', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.apply_single'.h6 : ¬∀ {α N P : Type} [inst : Zero N] [inst_1 : Zero P] (e : N → P) (a : α) (n : N) (b : α),
        e ((fun₀ | a => n) b) = (fun₀ | a => e n) b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) (0) (0) (1)) (by
  simp)

-- Prod.instAntisymmLexOfIsStrictOrder, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instAntisymmLexOfIsStrictOrder.h4 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : Std.Antisymm s], Std.Antisymm (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm ((0, 0) : ℕ × ℕ) ((0, 1) : ℕ × ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.instAntisymmLexOfIsStrictOrder, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instAntisymmLexOfIsStrictOrder.h5 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : IsStrictOrder α r], Std.Antisymm (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => a < b : ℕ → ℕ → Prop) (fun _ _ => True : Bool → Bool → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm ((0, Bool.false) : ℕ × Bool) ((0, Bool.true) : ℕ × Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.instAsymmLex_mathlib, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instAsymmLex_mathlib.h4 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : Std.Asymm s], Std.Asymm (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.asymm ((0, 0) : ℕ × ℕ) ((0, 0) : ℕ × ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.instAsymmLex_mathlib, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instAsymmLex_mathlib.h5 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : Std.Asymm r], Std.Asymm (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a ≤ b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.asymm ((0, 0) : ℕ × ℕ) ((0, 0) : ℕ × ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.insert_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.insert_subset.h4 : ¬∀ {α : Type} {s t : Set α} {a : α}, s ⊆ t → Insert.insert a s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1) (by
  rfl)) (by
  simp)

-- Set.insert_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.insert_subset.h5 : ¬∀ {α : Type} {s t : Set α} {a : α}, a ∈ t → Insert.insert a s ⊆ t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (Bool.false) (by
  decide)) (by
  simp)

-- Prod.instIrreflLex_mathlib, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instIrreflLex_mathlib.h4 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : Std.Irrefl s], Std.Irrefl (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd (hc_c.irrefl ((0, 0) : ℕ × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.instIrreflLex_mathlib, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instIrreflLex_mathlib.h5 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : Std.Irrefl r], Std.Irrefl (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a ≤ b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd (hc_c.irrefl ((0, 0) : ℕ × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.instIsTransLex, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instIsTransLex.h4 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : IsTrans β s], IsTrans (α × β) (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.trans ((0, 0) : ℕ × ℕ) ((1, 0) : ℕ × ℕ) ((0, 0) : ℕ × ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.instIsTransLex, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instIsTransLex.h5 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : IsTrans α r], IsTrans (α × β) (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a ≠ b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.trans ((0, 0) : ℕ × ℕ) ((0, 1) : ℕ × ℕ) ((0, 0) : ℕ × ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.nontrivial_of_pair_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_pair_subset.h4 : ¬∀ {α : Type} {s : Set α} {x y : α}, {x, y} ⊆ s → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (0) (by
  simp)) (by
  simp)

-- Set.nontrivial_of_pair_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_pair_subset.h5 : ¬∀ {α : Type} {s : Set α} {x y : α}, x ≠ y → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (1) (by
  decide)) (by
  simp)

-- Nat.ModEq.mul_left_cancel', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_left_cancel'.h4 : ¬∀ {a b c m : ℕ}, c * a ≡ c * b [MOD c * m] → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.mul_left_cancel', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_left_cancel'.h5 : ¬∀ {a b c m : ℕ}, c ≠ 0 → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub_left', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_left'.h4 : ¬∀ {n a b c : ℕ}, b ≡ c [MOD n] → a - b ≡ a - c [MOD n] := fun hc_h => absurd (@hc_h (2) (1) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub_left', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_left'.h5 : ¬∀ {n a b c : ℕ}, (b ≤ a ↔ c ≤ a) → a - b ≡ a - c [MOD n] := fun hc_h => absurd (@hc_h (0) (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.mul_right_cancel', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_right_cancel'.h4 : ¬∀ {a b c m : ℕ}, a * c ≡ b * c [MOD m * c] → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.mul_right_cancel', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_right_cancel'.h5 : ¬∀ {a b c m : ℕ}, c ≠ 0 → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.nonempty_of_union_eq_top_of_nonempty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_of_union_eq_top_of_nonempty.h5 : ¬∀ {α ι : Type} (t : Set ι) (s : ι → Set α), Nonempty α → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun (a : ℕ) => {n : ℕ | n = 0}) (by
  (repeat' constructor) <;> done)) (by
  simp)

-- Set.iUnion_eq_const, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iUnion_eq_const.h5 : ¬∀ {α ι : Type} [inst : Nonempty ι] {f : ι → Set α} {s : Set α}, ⋃ (i : ι), f i = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun (a : ℕ) => {n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.encard_exchange, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_exchange.h5 : ¬∀ {α : Type} {s : Set α} {a b : α}, a ∉ s → (Insert.insert a (s \ {b})).encard = s.encard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (0) (0) (by
  decide)) (by
  simp)

-- Set.ncard_exchange, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_exchange.h5 : ¬∀ {α : Type} {s : Set α} {a b : α}, a ∉ s → (Insert.insert a (s \ {b})).ncard = s.ncard := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) (Bool.false) (Bool.false) (by
  decide)) (by
  simp)

-- Set.pairwise_insert_of_symm_of_refl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pairwise_insert_of_symm_of_refl.h5 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} {a : α} [inst : Std.Symm r],
        (Insert.insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop) ({n : ℕ | n = 0}) (0) _) (by
  simp)

-- List.IsChain.prefix, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.prefix.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l l₁ : List α}, List.IsChain R l → List.IsChain R l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([1, 0]) (by
  decide)) (by
  decide +kernel)

-- Set.Nontrivial.image_of_injOn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.image_of_injOn.h4 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, Set.InjOn f s → (f '' s).Nontrivial := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- DFinsupp.comapDomain_single, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain_single.h7 : ¬∀ {ι : Type} {β : ι → Type} {κ : Type} [inst : DecidableEq ι] [inst : DecidableEq κ] [inst : (i : ι) → Zero (β i)]
        (h : κ → ι) (k : κ) (x : β (h k)), Function.Injective h := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun _ => 0 : ℕ → ℕ) (0) (0)) (by
  simp)

-- Set.pairwise_union_of_symm_of_refl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pairwise_union_of_symm_of_refl.h5 : ¬∀ {α : Type} {r : α → α → Prop} {s t : Set α} [inst : Std.Symm r],
        (s ∪ t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ ∀ a ∈ s, ∀ b ∈ t, r a b := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) _) (by
  simp)

-- Set.subsingleton_of_preimage, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_of_preimage.h5 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f → ∀ (s : Set β), s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (by
  decide) ({x : Bool | True})) (by
  decide +kernel)

-- Nat.findGreatest_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_spec.h4 : ¬∀ {m : ℕ} {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, P m → P (Nat.findGreatest P n) := fun hc_h => absurd (@hc_h (1) (fun n => n = 1 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.findGreatest_spec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_spec.h5 : ¬∀ {m : ℕ} {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, m ≤ n → P (Nat.findGreatest P n) := fun hc_h => absurd (@hc_h (0) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0) (by
  decide)) (by
  decide +kernel)

-- Fin.val_sub_lt_of_lt_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_lt_of_lt_of_le.h4 : ¬∀ {n m : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) < m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.val_sub_lt_of_lt_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_lt_of_lt_of_le.h5 : ¬∀ {n m : ℕ} {a b : Fin n}, ↑a < m → ↑(a - b) < m := fun hc_h => absurd (@hc_h (2) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Fin.val_sub_castLT_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_castLT_of_lt.h4 : ¬∀ {n m : ℕ} {a b : Fin m}, a < b → ↑b < n := fun hc_h => absurd (@hc_h (0) (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.val_sub_castLT_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_castLT_of_lt.h5 : ¬∀ {n m : ℕ} {a b : Fin m}, ↑b < n → a < b := fun hc_h => absurd (@hc_h (1) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Fin.le_of_castSucc_lt_of_succ_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.le_of_castSucc_lt_of_succ_lt.h4 : ¬∀ {n : ℕ} {a b : Fin (n + 1)} {i : Fin n}, b < i.succ → b < a := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.le_of_castSucc_lt_of_succ_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.le_of_castSucc_lt_of_succ_lt.h5 : ¬∀ {n : ℕ} {a b : Fin (n + 1)} {i : Fin n}, i.castSucc < a → b < a := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.find_le_of_pos, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.find_le_of_pos.h3.der : ∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] {j : Fin n}, p j → ∃ (k : Fin n), p k := by
  (intros; solve_by_elim)
theorem HypCheckProof.Fin.find_le_of_pos.h3 : ∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] {j : Fin n} (a : p j),
      Fin.find p (HypCheckProof.Fin.find_le_of_pos.h3.der a) ≤ j := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Fin.find_le_of_pos hc_x0 hc_x1 hc_x2 (@HypCheckProof.Fin.find_le_of_pos.h3.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x3 hc_x4

-- List.prev_eq_getElem?_idxOf_pred_of_ne_head, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_eq_getElem?_idxOf_pred_of_ne_head.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  decide +kernel)

-- List.prev_eq_getElem?_idxOf_pred_of_ne_head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_eq_getElem?_idxOf_pred_of_ne_head.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α} (ha : a ∈ l),
        Option.some (l.prev a ha) = l[List.idxOf a l - 1]? := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([0, 1]) (0) hc_k0) (by
  decide +kernel)

-- List.prev_infix_of_mem_tail, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_infix_of_mem_tail.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  decide +kernel)

-- List.prev_infix_of_mem_tail, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_infix_of_mem_tail.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α} (ha : a ∈ l), [l.prev a ha, a] <:+: l := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([0]) (0) hc_k0) (by
  decide +kernel)

-- List.next_reverse_eq_prev, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_reverse_eq_prev.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.Nodup → ∀ (x : α), x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- List.nextOr_getLast_of_notMem_dropLast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_getLast_of_notMem_dropLast.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} (d : α), l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  decide +kernel)

-- List.nextOr_getLast_of_notMem_dropLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_getLast_of_notMem_dropLast.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} (hl : l ≠ []) (d : α), l.nextOr (l.getLast hl) d = d := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([0, 0]) hc_k0 (1)) (by
  decide +kernel)

-- List.prev_eq_getElem_idxOf_pred_of_ne_head, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_eq_getElem_idxOf_pred_of_ne_head.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  decide +kernel)

-- List.prev_eq_getElem_idxOf_pred_of_ne_head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_eq_getElem_idxOf_pred_of_ne_head.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α} (ha : a ∈ l),
        l.prev a ha = GetElem.getElem l (List.idxOf a l - 1) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([0, 1]) (0) hc_k0) (by
  decide +kernel)

-- Int.cast_div_ofNat_charZero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_div_ofNat_charZero.h5 : Not
      (∀ {k : Type} [inst : DivisionRing k]
        [inst_1 :
          @CharZero k (@AddGroupWithOne.toAddMonoidWithOne k (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k inst)))]
        {m n : Nat},
        @Eq k
          (@Int.cast k (@AddGroupWithOne.toIntCast k (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k inst)))
            (@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) (@Nat.cast Int instNatCastInt m)
              (@Nat.cast Int instNatCastInt n)))
          (@HDiv.hDiv k k k (@instHDiv k (@DivInvMonoid.toDiv k (@DivisionRing.toDivInvMonoid k inst)))
            (@Nat.cast k
              (@AddMonoidWithOne.toNatCast k
                (@AddGroupWithOne.toAddMonoidWithOne k (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k inst))))
              m)
            (@Nat.cast k
              (@AddMonoidWithOne.toNatCast k
                (@AddGroupWithOne.toAddMonoidWithOne k (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k inst))))
              n))) := fun hc_h => absurd (@hc_h (Rat) (Rat.instDivisionRing) _ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Int.cast_div_charZero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_div_charZero.h5 : Not
      (∀ {k : Type} [inst : DivisionRing k]
        [inst_1 :
          @CharZero k (@AddGroupWithOne.toAddMonoidWithOne k (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k inst)))]
        {m n : Int},
        @Eq k
          (@Int.cast k (@AddGroupWithOne.toIntCast k (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k inst)))
            (@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) m n))
          (@HDiv.hDiv k k k (@instHDiv k (@DivInvMonoid.toDiv k (@DivisionRing.toDivInvMonoid k inst)))
            (@Int.cast k (@AddGroupWithOne.toIntCast k (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k inst))) m)
            (@Int.cast k (@AddGroupWithOne.toIntCast k (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k inst))) n))) := fun hc_h => absurd (@hc_h (Rat) (Rat.instDivisionRing) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))) (by
  decide +kernel)

-- Set.Nonempty.prod, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.prod.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, t.Nonempty → (s ×ˢ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.Nonempty.prod, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.prod.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, s.Nonempty → (s ×ˢ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Int.ModEq.cancel_left_div_gcd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.cancel_left_div_gcd.h4 : ¬∀ {m a b c : ℤ}, c * a ≡ c * b [ZMOD m] → a ≡ b [ZMOD m / ↑(m.gcd c)] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.cancel_left_div_gcd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.cancel_left_div_gcd.h5 : ¬∀ {m a b c : ℤ}, 0 < m → a ≡ b [ZMOD m / ↑(m.gcd c)] := fun hc_h => absurd (@hc_h (2) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Set.mem_diff_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_diff_of_mem.h4 : ¬∀ {α : Type} {s t : Set α} {x : α}, x ∉ t → x ∈ s \ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1) (by
  decide)) (by
  decide +kernel)

-- Set.mem_diff_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_diff_of_mem.h5 : ¬∀ {α : Type} {s t : Set α} {x : α}, x ∈ s → x ∈ s \ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.mul_right_cancel', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_right_cancel'.h4 : ¬∀ {m a b c : ℤ}, a * c ≡ b * c [ZMOD m * c] → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.mul_right_cancel', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_right_cancel'.h5 : ¬∀ {m a b c : ℤ}, c ≠ 0 → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.of_dvd.h4 : ¬∀ {m n a b : ℤ}, a ≡ b [ZMOD n] → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.of_dvd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.of_dvd.h5 : ¬∀ {m n a b : ℤ}, m ∣ n → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.getEquivOfForallMemList_symm_apply_val, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.getEquivOfForallMemList_symm_apply_val.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.Nodup → ∀ (a x : α), x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (by
  decide) (0)) (by
  simp)

-- ZMod.cast_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.cast_one.h4 : Not
      (∀ {n : Nat} {R : Type} [inst : Ring R] {m : Nat},
        @Dvd.dvd Nat Nat.instDvd m n →
          @Eq R
            (@ZMod.cast R (@Ring.toAddGroupWithOne R inst) n
              (@OfNat.ofNat (ZMod n) (nat_lit 1)
                (@One.toOfNat1 (ZMod n)
                  (@AddMonoidWithOne.toOne (ZMod n)
                    (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                      (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))))))
            (@OfNat.ofNat R (nat_lit 1)
              (@One.toOfNat1 R
                (@AddMonoidWithOne.toOne R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst)))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- ZMod.cast_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.cast_one.h5 : Not
      (∀ {n : Nat} {R : Type} [inst : Ring R] {m : Nat}
        [inst_1 : @CharP R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst)) m],
        @Eq R
          (@ZMod.cast R (@Ring.toAddGroupWithOne R inst) n
            (@OfNat.ofNat (ZMod n) (nat_lit 1)
              (@One.toOfNat1 (ZMod n)
                (@AddMonoidWithOne.toOne (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))))))
          (@OfNat.ofNat R (nat_lit 1)
            (@One.toOfNat1 R
              (@AddMonoidWithOne.toOne R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst)))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Int) (Int.instRing) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) _) (by
  decide +kernel)

-- Nat.toDigitsCore_length, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toDigitsCore_length.h4 : ¬∀ (b f n e : ℕ), n < b ^ e → (b.toDigitsCore f n []).length ≤ e := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.toDigitsCore_length, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toDigitsCore_length.h5 : ¬∀ (b f n e : ℕ), 0 < e → (b.toDigitsCore f n []).length ≤ e := fun hc_h => absurd (@hc_h (1) (2) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.lt_of_mem_digitsAppend, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_of_mem_digitsAppend.h2 : ¬∀ {n b : ℕ} (l i : ℕ), i ∈ b.digitsAppend l n → i < b := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.lt_of_mem_digitsAppend, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_of_mem_digitsAppend.h5 : ¬∀ {n : ℕ} {b : ℕ}, 1 < b → ∀ (l i : ℕ), i < b := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (0) (2)) (by
  decide +kernel)

-- List.consFixedLengthDigits_head, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.consFixedLengthDigits_head.h1 : ¬∀ {b : ℕ} {l d : ℕ} {L : List ℕ}, 1 < b := fun hc_h => absurd (@hc_h (0) (0) (0) ([])) (by
  decide +kernel)

-- Nat.Prime.emultiplicity_choose', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_choose'.h4 : ¬∀ {p n k b : ℕ},
        Nat.log p (n + k) < b →
          emultiplicity p ((n + k).choose k) = ↑{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i}.card := fun hc_h => absurd (@hc_h (1) (0) (0) (1) (by
  decide)) (by
  simp)

-- Nat.cast_div_charZero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_div_charZero.h5 : Not
      (∀ {K : Type} [inst : DivisionSemiring K] {m n : Nat}
        [inst_1 :
          @CharZero K
            (@AddCommMonoidWithOne.toAddMonoidWithOne K
              (@NonAssocSemiring.toAddCommMonoidWithOne K
                (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst))))],
        @Eq K
          (@Nat.cast K
            (@AddMonoidWithOne.toNatCast K
              (@AddCommMonoidWithOne.toAddMonoidWithOne K
                (@NonAssocSemiring.toAddCommMonoidWithOne K
                  (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
            (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) m n))
          (@HDiv.hDiv K K K
            (@instHDiv K
              (@DivInvMonoid.toDiv K (@GroupWithZero.toDivInvMonoid K (@DivisionSemiring.toGroupWithZero K inst))))
            (@Nat.cast K
              (@AddMonoidWithOne.toNatCast K
                (@AddCommMonoidWithOne.toAddMonoidWithOne K
                  (@NonAssocSemiring.toAddCommMonoidWithOne K
                    (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
              m)
            (@Nat.cast K
              (@AddMonoidWithOne.toNatCast K
                (@AddCommMonoidWithOne.toAddMonoidWithOne K
                  (@NonAssocSemiring.toAddCommMonoidWithOne K
                    (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
              n))) := fun hc_h => absurd (@hc_h (Rat) (@Semifield.toDivisionSemiring Rat (@Field.toSemifield Rat Rat.instField)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _) (by
  decide +kernel)

-- Set.mem_of_subset_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_subset_of_mem.h4 : ¬∀ {α : Type} {s₁ s₂ : Set α} {a : α}, a ∈ s₁ → a ∈ s₂ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (0) (by
  decide)) (by
  decide +kernel)

-- Set.mem_of_subset_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_subset_of_mem.h5 : ¬∀ {α : Type} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s₂ → a ∈ s₂ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1) (by
  rfl)) (by
  decide +kernel)

-- List.cons_subset_of_subset_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_subset_of_subset_of_mem.h4 : ¬∀ {α : Type} {a : α} {l m : List α}, l ⊆ m → a :: l ⊆ m := fun hc_h => absurd (@hc_h (ℕ) (0) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.cons_subset_of_subset_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_subset_of_subset_of_mem.h5 : ¬∀ {α : Type} {a : α} {l m : List α}, a ∈ m → a :: l ⊆ m := fun hc_h => absurd (@hc_h (ℕ) (0) ([1]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.idxOf_get, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_get.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l : List α} (h : List.idxOf a l < l.length),
        l.get (⟨List.idxOf a l, h⟩ : Fin l.length) = a := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (0) ([1]) hc_k0) (by
  decide +kernel)

-- List.idxOf_get, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_get.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α} {l : List α}, List.idxOf a l < l.length := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ (0) ([])) (by
  decide +kernel)

-- List.Forall.imp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall.imp.h3 : ¬∀ {α : Type} {p q : α → Prop} {l : List α}, List.Forall p l → List.Forall q l := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Forall.imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall.imp.h5 : ¬∀ {α : Type} {p q : α → Prop}, (∀ (x : α), p x → q x) → ∀ {l : List α}, List.Forall q l := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp) ([1])) (by
  decide +kernel)

-- Set.union_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_subset.h4 : ¬∀ {α : Type} {s t r : Set α}, t ⊆ r → s ∪ t ⊆ r := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  rfl)) (by
  simp)

-- Set.union_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_subset.h5 : ¬∀ {α : Type} {s t r : Set α}, s ⊆ r → s ∪ t ⊆ r := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) (by
  rfl)) (by
  simp)

-- List.erase_getElem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.erase_getElem.h2 : ¬∀ {ι : Type} [inst : BEq ι] {l : List ι} {i : ℕ} (hi : i < l.length), (l.erase l[i]).Perm (l.eraseIdx i) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) ([0]) (0) hc_k0) (by
  decide +kernel)

-- List.erase_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.erase_getElem.h5 : ¬∀ {ι : Type} [inst : BEq ι] [inst : LawfulBEq ι] {l : List ι} {i : ℕ}, i < l.length := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ ([]) (0)) (by
  decide +kernel)

-- List.mem_filter_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.mem_filter_of_mem.h4.inst : 0 ∉ List.filter (fun (n : ℕ) => n % 2 == 0) [] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.mem_filter_of_mem.h4.prem0 : (fun (n : ℕ) => n % 2 == 0) 0 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.mem_filter_of_mem.h4 : ¬∀ {α : Type} {p : α → Bool} {a : α} {l : List α}, p a = Bool.true → a ∈ List.filter p l := fun hc_h => HypCheckProof.List.mem_filter_of_mem.h4.inst (@hc_h (ℕ) (fun (n : ℕ) => n % 2 == 0) (0) ([]) HypCheckProof.List.mem_filter_of_mem.h4.prem0)

-- List.mem_filter_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_filter_of_mem.h5 : ¬∀ {α : Type} {p : α → Bool} {a : α} {l : List α}, a ∈ l → a ∈ List.filter p l := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (1) ([1]) (by
  decide)) (by
  decide +kernel)

-- List.succ_idxOf_lt_length_of_mem_dropLast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.succ_idxOf_lt_length_of_mem_dropLast.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l : List α} {a : α}, List.idxOf a l + 1 < l.length := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ ([]) (0)) (by
  decide +kernel)

-- Nat.exponent_dvd_of_prime_pow_eq_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exponent_dvd_of_prime_pow_eq_pow.h4 : ¬∀ {p a m n : ℕ}, p ^ m = a ^ n → n ∣ m := fun hc_h => absurd (@hc_h (1) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.exponent_dvd_of_prime_pow_eq_pow, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exponent_dvd_of_prime_pow_eq_pow.h5 : ¬∀ {p : ℕ} {a : ℕ} {m n : ℕ}, Nat.Prime p → n ∣ m := fun hc_h => absurd (@hc_h (2) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow.h4 : ¬∀ {p a m n : ℕ}, p ^ m = a ^ n → m = n * a.factorization p := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow.h5 : ¬∀ {p a m n : ℕ}, Nat.Prime p → m = n * a.factorization p := fun hc_h => absurd (@hc_h (2) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.length_dropSlice_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_dropSlice_lt.h3 : ¬∀ {α : Type} (i j : ℕ) (xs : List α), i < xs.length → (List.dropSlice i j xs).length < xs.length := fun hc_h => absurd (@hc_h (ℕ) (0) (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.length_dropSlice_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_dropSlice_lt.h5 : ¬∀ {α : Type} (i j : ℕ), 0 < j → ∀ (xs : List α), (List.dropSlice i j xs).length < xs.length := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (by
  decide) ([])) (by
  decide +kernel)

-- Rat.cast_pos_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.cast_pos_of_pos.h5 : Not
      (∀ {q : Rat} {K : Type} [inst : Field K] [inst_1 : LinearOrder K]
        [inst_2 :
          @IsStrictOrderedRing K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@SemilatticeInf.toPartialOrder K
              (@Lattice.toSemilatticeInf K (@DistribLattice.toLattice K (@instDistribLatticeOfLinearOrder K inst_1))))],
        @LT.lt K
          (@Preorder.toLT K
            (@PartialOrder.toPreorder K
              (@SemilatticeInf.toPartialOrder K
                (@Lattice.toSemilatticeInf K (@DistribLattice.toLattice K (@instDistribLatticeOfLinearOrder K inst_1))))))
          (@OfNat.ofNat K (nat_lit 0)
            (@Zero.toOfNat0 K
              (@MulZeroClass.toZero K
                (@instMulZeroClassOfSemiring K
                  (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))))
          (@Rat.cast K (@DivisionRing.toRatCast K (@Field.toDivisionRing K inst)) q)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Rat) (Rat.instField) (Rat.linearOrder) _) (by
  decide +kernel)

-- List.pairwise_of_coe_toFinset_pairwise, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_of_coe_toFinset_pairwise.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {r : α → α → Prop} {l : List α}, l.Nodup → List.Pairwise r l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) (by
  decide)) (by
  decide +kernel)

-- List.pairwise_of_coe_toFinset_pairwise, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_of_coe_toFinset_pairwise.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {r : α → α → Prop} {l : List α},
        @Set.Pairwise α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) (@List.toFinset α inst l)) r →
          @List.Pairwise α r l) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (fun a b => a < b : Nat → Nat → Prop) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))) (by
  decide)) (by
  decide +kernel)

-- Set.infs_eq_inter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infs_eq_inter.h4 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s t : Set α},
        @IsLowerSet α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst))) t →
          @Eq (Set α) (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t) (@Min.min (Set α) (@Set.instMin α) s t)) := fun hc_h => absurd (@hc_h (Bool) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (x : Bool) => True) (by
  aesop)) (by
  simp)

-- Set.infs_eq_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infs_eq_inter.h5 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s t : Set α},
        @IsLowerSet α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst))) s →
          @Eq (Set α) (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t) (@Min.min (Set α) (@Set.instMin α) s t)) := fun hc_h => absurd (@hc_h (Bool) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@Set.ofPred Bool fun (x : Bool) => True) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (by
  aesop)) (by
  simp)

-- List.any_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.any_of_mem.h4.inst : ¬([].any fun (n : ℕ) => n % 2 == 0) = Bool.true := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.any_of_mem.h4.prem0 : (fun (n : ℕ) => n % 2 == 0) 0 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.any_of_mem.h4 : ¬∀ {α : Type} {l : List α} {a : α} {p : α → Bool}, p a = Bool.true → l.any p = Bool.true := fun hc_h => HypCheckProof.List.any_of_mem.h4.inst (@hc_h (ℕ) ([]) (0) (fun (n : ℕ) => n % 2 == 0) HypCheckProof.List.any_of_mem.h4.prem0)

-- List.any_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.any_of_mem.h5 : ¬∀ {α : Type} {l : List α} {a : α} {p : α → Bool}, a ∈ l → l.any p = Bool.true := fun hc_h => absurd (@hc_h (ℕ) ([1]) (1) (fun n => n % 2 == 0 : ℕ → Bool) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_head_tail, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_head_tail.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} (ha : a ∈ l.tail),
        R (l.head (List.ne_nil_of_mem (List.mem_of_mem_tail ha))) a := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) (0) hc_k0) (by
  decide +kernel)

-- List.Pairwise.rel_head_tail, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_head_tail.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α}, List.Pairwise R l → a ∈ l.tail := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- List.perm_lookmap, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.perm_lookmap.h5.inst : Not
      (@List.Perm Nat (@List.lookmap Nat (fun (x : Nat) => @Option.none Nat) (@List.nil Nat))
        (@List.lookmap Nat (fun (x : Nat) => @Option.none Nat)
          (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.perm_lookmap.h5.prem0 : @List.Pairwise Nat
      (fun (a b : Nat) =>
        ∀ (c : Nat),
          @Membership.mem Nat (Option Nat) (@Option.instMembership Nat) ((fun (x : Nat) => @Option.none Nat) a) c →
            ∀ (d : Nat),
              @Membership.mem Nat (Option Nat) (@Option.instMembership Nat) ((fun (x : Nat) => @Option.none Nat) b) d →
                And (@Eq Nat a b) (@Eq Nat c d))
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.perm_lookmap.h5 : Not
      (∀ {α : Type} (f : α → Option α) {l₁ l₂ : List α},
        @List.Pairwise α
            (fun (a b : α) =>
              ∀ (c : α),
                @Membership.mem α (Option α) (@Option.instMembership α) (f a) c →
                  ∀ (d : α), @Membership.mem α (Option α) (@Option.instMembership α) (f b) d → And (@Eq α a b) (@Eq α c d))
            l₁ →
          @List.Perm α (@List.lookmap α f l₁) (@List.lookmap α f l₂)) := fun hc_h => HypCheckProof.List.perm_lookmap.h5.inst (@hc_h (Nat) (fun (x : Nat) => @Option.none Nat) (@List.nil Nat) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) HypCheckProof.List.perm_lookmap.h5.prem0)

-- List.Nodup.product, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.product.h4 : ¬∀ {α β : Type} {l₁ : List α} {l₂ : List β}, l₂.Nodup → (l₁ ×ˢ l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0, 0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.product, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.product.h5 : ¬∀ {α β : Type} {l₁ : List α} {l₂ : List β}, l₁.Nodup → (l₁ ×ˢ l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) ([0, 0]) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.map_on, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.map_on.h4 : ¬∀ {α β : Type} {l : List α} {f : α → β}, l.Nodup → (List.map f l).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0, 1]) (fun _ => 0 : ℕ → ℕ) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.map_on, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Nodup.map_on.h5.inst : ¬(List.map (fun (n : ℕ) => n + 1) [0, 0]).Nodup := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Nodup.map_on.h5.prem0 : ∀ x ∈ [0, 0], ∀ y ∈ [0, 0], (fun (n : ℕ) => n + 1) x = (fun (n : ℕ) => n + 1) y → x = y := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.Nodup.map_on.h5 : ¬∀ {α β : Type} {l : List α} {f : α → β}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (List.map f l).Nodup := fun hc_h => HypCheckProof.List.Nodup.map_on.h5.inst (@hc_h (ℕ) (ℕ) ([0, 0]) (fun (n : ℕ) => n + 1) HypCheckProof.List.Nodup.map_on.h5.prem0)

-- List.Nodup.erase_get, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.erase_get.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α}, l.Nodup → ∀ (i : Fin l.length), l.erase (l.get i) = l.eraseIdx ↑i := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) ([0]) (by
  decide) (0)) (by
  decide +kernel)

-- List.Interleaves.pairwise_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Interleaves.pairwise_left.h5 : ¬∀ {α : Type} {r : α → α → Prop} {l₁ : List α} {l₂ : List α} [inst : IsTrans α r], List.Pairwise r l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) ([]) _) (by
  decide +kernel)

-- List.HasPeriod.drop_of_hasPeriod_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.HasPeriod.drop_of_hasPeriod_add.h5 : ¬∀ {α : Type} {q k : ℕ} {w : List α}, w.HasPeriod q → (List.drop q w).HasPeriod k := fun hc_h => absurd (@hc_h (ℕ) (0) (1) ([0, 1]) (by
  simp)) (by
  nofun)

-- IsUnit.natCast_of_isNilpotent_of_coprime, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_of_isNilpotent_of_coprime.h4 : Not
      (∀ {A : Type} [inst : CommRing A] {n p : Nat},
        p.Coprime n →
          @IsUnit A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddGroupWithOne.toAddMonoidWithOne A (@Ring.toAddGroupWithOne A (@CommRing.toRing A inst))))
              n)) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toCommRing Bool instBooleanRingBool) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- IsUnit.natCast_of_isNilpotent_of_coprime, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_of_isNilpotent_of_coprime.h5 : Not
      (∀ {A : Type} [inst : CommRing A] {n p : Nat},
        @IsNilpotent A
            (@MulZeroClass.toZero A
              (@instMulZeroClassOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@NPow.toPow A
              (@Monoid.toNPow A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))))
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddGroupWithOne.toAddMonoidWithOne A (@Ring.toAddGroupWithOne A (@CommRing.toRing A inst))))
              p) →
          @IsUnit A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddGroupWithOne.toAddMonoidWithOne A (@Ring.toAddGroupWithOne A (@CommRing.toRing A inst))))
              n)) := fun hc_h => absurd (@hc_h (Int) (Int.instCommRing) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  simp)) (by
  decide +kernel)

-- PosNum.divMod_to_nat_aux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PosNum.divMod_to_nat_aux.h4 : Not
      (∀ {n d : PosNum} {q r : Num},
        @LT.lt Nat instLTNat (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) r)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@castPosNum Nat Nat.instOne instAddNat d)) →
          And
            (@Eq Nat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
                  (@Prod.snd Num Num (d.divModAux q r)))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@castPosNum Nat Nat.instOne instAddNat d)
                  (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
                    (@Prod.fst Num Num (d.divModAux q r)))))
              (@castPosNum Nat Nat.instOne instAddNat n))
            (@LT.lt Nat instLTNat
              (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
                (@Prod.snd Num Num (d.divModAux q r)))
              (@castPosNum Nat Nat.instOne instAddNat d))) := fun hc_h => absurd (@hc_h (PosNum.one) (PosNum.one) (Num.zero) (Num.zero) (by
  decide)) (by
  decide +kernel)

-- PosNum.divMod_to_nat_aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PosNum.divMod_to_nat_aux.h5 : Not
      (∀ {n d : PosNum} {q r : Num},
        @Eq Nat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) r)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@castPosNum Nat Nat.instOne instAddNat d)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) q)
                  (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) q))))
            (@castPosNum Nat Nat.instOne instAddNat n) →
          And
            (@Eq Nat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
                  (@Prod.snd Num Num (d.divModAux q r)))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@castPosNum Nat Nat.instOne instAddNat d)
                  (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
                    (@Prod.fst Num Num (d.divModAux q r)))))
              (@castPosNum Nat Nat.instOne instAddNat n))
            (@LT.lt Nat instLTNat
              (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
                (@Prod.snd Num Num (d.divModAux q r)))
              (@castPosNum Nat Nat.instOne instAddNat d))) := fun hc_h => absurd (@hc_h (PosNum.one.bit1) (PosNum.one) (Num.zero) (Num.pos PosNum.one.bit1) (by
  decide)) (by
  decide +kernel)

-- Set.Infinite.biUnion, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.biUnion.h4 : ¬∀ {α ι : Type} {s : ι → Set α} {a : Set ι}, Set.InjOn s a → (⋃ i ∈ a, s i).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.finite_subset_iUnion, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.finite_subset_iUnion.h5 : ¬∀ {α : Type} {s : Set α}, s.Finite → ∀ {ι : Type} {t : ι → Set α}, ∃ (I : Set ι), I.Finite ∧ s ⊆ ⋃ i ∈ I, t i := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (by
  simp) (ℕ) (fun (a : ℕ) => {x : ℕ | False})) (by
  simp)

-- Disjoint.subset_left_of_subset_union, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.subset_left_of_subset_union.h4 : ¬∀ {α : Type} {s t u : Set α}, Disjoint s u → s ⊆ t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp)) (by
  simp)

-- Disjoint.subset_left_of_subset_union, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.subset_left_of_subset_union.h5 : ¬∀ {α : Type} {s t u : Set α}, s ⊆ t ∪ u → s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Disjoint.notMem_of_mem_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_right.h3 : ¬∀ {α : Type} {s t : Set α} ⦃a : α⦄, a ∈ t → a ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (by
  decide)) (by
  decide +kernel)

-- Disjoint.notMem_of_mem_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_right.h5 : ¬∀ {α : Type} {s t : Set α}, Disjoint s t → ∀ ⦃a : α⦄, a ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (0)) (by
  decide +kernel)

-- Set.pair_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pair_subset.h4 : ¬∀ {α : Type} {s : Set α} {a b : α}, b ∈ s → {a, b} ⊆ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (0) (by
  decide)) (by
  simp)

-- Set.pair_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pair_subset.h5 : ¬∀ {α : Type} {s : Set α} {a b : α}, a ∈ s → {a, b} ⊆ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (1) (by
  decide)) (by
  simp)

-- Function.update_comp_eq_of_notMem_range, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_comp_eq_of_notMem_range.h8 : ¬∀ {α β γ : Type} [inst : DecidableEq β] (g : β → γ) {f : α → β} {i : β} (a : γ), Function.update g i a ∘ f = g ∘ f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (0) (0)) (by
  decide +kernel)

-- Sum.LiftRel.isLeft_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.isLeft_left.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {c : γ}, x.isLeft = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inr 0) (0)) (by
  decide +kernel)

-- Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits.h2 : ¬∀ {p : ℕ} (L : List ℕ), (∀ l ∈ L, l < p) → L ≠ [] := fun hc_h => absurd (@hc_h (0) ([]) (by
  decide)) (by
  decide +kernel)

-- Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits.h4 : ¬∀ {p : ℕ} (L : List ℕ) {h_nonempty : L ≠ []},
        L.getLast h_nonempty ≠ 0 →
          (p - 1) * ∑ i ∈ Finset.range L.length, Nat.ofDigits p L / p ^ i.succ = Nat.ofDigits p L - L.sum := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (2) ([2]) hc_k0 hc_k1) (by
  decide +kernel)

-- EReal.mul_div_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_div_cancel.h2 : ¬∀ {a b : EReal}, b ≠ ⊤ → b ≠ 0 → b * (a / b) = a := fun hc_h => absurd (@hc_h (1) (⊥) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.mul_div_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_div_cancel.h3 : ¬∀ {a b : EReal}, b ≠ ⊥ → b ≠ 0 → b * (a / b) = a := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.mul_div_cancel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_div_cancel.h4 : ¬∀ {a b : EReal}, b ≠ ⊥ → b ≠ ⊤ → b * (a / b) = a := fun hc_h => absurd (@hc_h (1) (0) (by
  decide) (by
  decide)) (by
  simp)

-- Nat.Prime.factorization_pos_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.factorization_pos_of_dvd.h2 : ¬∀ {n p : ℕ}, n ≠ 0 → p ∣ n → 0 < n.factorization p := fun hc_h => absurd (@hc_h (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.factorization_pos_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.factorization_pos_of_dvd.h3 : ¬∀ {n p : ℕ}, Nat.Prime p → p ∣ n → 0 < n.factorization p := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.factorization_pos_of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.factorization_pos_of_dvd.h4 : ¬∀ {n p : ℕ}, Nat.Prime p → n ≠ 0 → 0 < n.factorization p := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- AList.insert_insert_of_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AList.insert_insert_of_ne.h8 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a a' : α} {b : β a} {b' : β a'} (s : AList β),
        (AList.insert a' b' (AList.insert a b s)).entries.Perm (AList.insert a b (AList.insert a' b' s)).entries := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) (0) (1) (∅)) (by
  decide +kernel)

-- Nat.dvd_ordProj_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_ordProj_of_dvd.h2 : ¬∀ {n p : ℕ}, Nat.Prime p → p ∣ n → p ∣ p ^ n.factorization p := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_ordProj_of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_ordProj_of_dvd.h4 : ¬∀ {n p : ℕ}, n ≠ 0 → Nat.Prime p → p ∣ p ^ n.factorization p := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Sum.LiftRel.isRight_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.isRight_left.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {d : δ}, x.isRight = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inl 0) (0)) (by
  decide +kernel)

-- Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat.h2 : ¬∀ {n p : ℕ}, 0 < n → (∀ i ∈ Finset.Icc 1 (n - 1), n.choose i ≡ 0 [MOD p]) → n = p ^ multiplicity p n := fun hc_h => absurd (@hc_h (2) (1) (by
  decide) (by
  decide)) (by
  simp)

-- DFinsupp.filter_single_pos, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.filter_single_pos.h8 : ¬∀ {ι : Type} {β : ι → Type} [inst : (i : ι) → Zero (β i)] [inst_1 : DecidableEq ι] {p : ι → Prop}
        [inst_2 : DecidablePred p] (i : ι) (x : β i), (DFinsupp.filter p fun₀ | i => x) = fun₀ | i => x := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (instDecidableEqNat) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) (1)) (by
  decide +kernel)

-- Sum.LiftRel.isLeft_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.isLeft_congr.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ},
        x.isLeft = Bool.true ↔ y.isLeft = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inl 0) (Sum.inr 0)) (by
  decide +kernel)

-- Even.eq_of_totient_eq_totient, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Even.eq_of_totient_eq_totient.h2 : ¬∀ {a b : ℕ}, Even a → a.totient = b.totient → a = b := fun hc_h => absurd (@hc_h (2) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Even.eq_of_totient_eq_totient, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Even.eq_of_totient_eq_totient.h3 : ¬∀ {a b : ℕ}, a ∣ b → a.totient = b.totient → a = b := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Even.eq_of_totient_eq_totient, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Even.eq_of_totient_eq_totient.h4 : ¬∀ {a b : ℕ}, a ∣ b → Even a → a = b := fun hc_h => absurd (@hc_h (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finsupp.mapRange_single, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mapRange_single.h6 : ¬∀ {α M N : Type} [inst : Zero M] [inst_1 : Zero N] {f : M → N} {a : α} {b : M}, f 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) (0) (0)) (by
  decide +kernel)

-- PNat.find_comp_succ, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.PNat.find_comp_succ.h2.der : ∀ {p : ℕ+ → Prop} [inst : DecidablePred p], (∃ (n : ℕ+), p (n + 1)) → ¬p 1 → ∃ (n : ℕ+), p n := by
  (intros; grind)
theorem HypCheckProof.PNat.find_comp_succ.h2 : ∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h₂ : ∃ (n : ℕ+), p (n + 1)) (h1 : ¬p 1),
      PNat.find (HypCheckProof.PNat.find_comp_succ.h2.der h₂ h1) = PNat.find h₂ + 1 := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @PNat.find_comp_succ hc_x0 hc_x1 (@HypCheckProof.PNat.find_comp_succ.h2.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x2 hc_x3

-- Set.mem_image2_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_image2_iff.h8 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β}, f a b ∈ Set.image2 f s t ↔ a ∈ s ∧ b ∈ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (1)) (by
  (simp <;> omega))

-- DFinsupp.comapDomain'_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain'_apply.h6 : ¬∀ {ι : Type} {β : ι → Type} {κ : Type} [inst : (i : ι) → Zero (β i)] (h : κ → ι) {h' : ι → κ} (f : Π₀ (i : ι), β i)
        (k : κ), Function.LeftInverse h' h := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (Bool) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (0) (Bool.false)) (by
  decide +kernel)

-- Matrix.map_intCast, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.map_intCast.h7 : Not
      (∀ {n α β : Type} [inst : DecidableEq n] [inst_1 : AddGroupWithOne α] [inst_2 : Zero β] {f : α → β} (d : Int),
        @Eq (Matrix n n β)
          (@Matrix.map n n α β
            (@Int.cast (Matrix n n α)
              (@Matrix.instIntCastOfZero n α inst
                (@NegZeroClass.toZero α
                  (@SubNegZeroMonoid.toNegZeroClass α
                    (@SubtractionMonoid.toSubNegZeroMonoid α
                      (@AddGroup.toSubtractionMonoid α (@AddGroupWithOne.toAddGroup α inst_1)))))
                (@AddGroupWithOne.toIntCast α inst_1))
              d)
            f)
          (@Matrix.diagonal n β inst inst_2 fun (x : n) => f (@Int.cast α (@AddGroupWithOne.toIntCast α inst_1) d))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (instDecidableEqBool) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)) (instZeroBool_mathlib) (not : Bool → Bool) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- EReal.toReal_le_toReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_le_toReal.h2 : ¬∀ {x y : EReal}, x ≠ ⊥ → y ≠ ⊤ → x.toReal ≤ y.toReal := fun hc_h => absurd (@hc_h (1) (0) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.toReal_le_toReal, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_le_toReal.h4 : ¬∀ {x y : EReal}, x ≤ y → x ≠ ⊥ → x.toReal ≤ y.toReal := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide) (by
  decide)) (by
  simp)

-- Int.le_add_iff_lt_of_dvd_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_add_iff_lt_of_dvd_sub.h3 : ¬∀ {a b c : ℤ}, a ∣ c - b → (a + b ≤ c ↔ b < c) := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.le_add_iff_lt_of_dvd_sub, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_add_iff_lt_of_dvd_sub.h4 : ¬∀ {a b c : ℤ}, 0 < a → (a + b ≤ c ↔ b < c) := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide)) (by
  decide +kernel)

-- strictAntiOn_insert_iff_of_forall_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.strictAntiOn_insert_iff_of_forall_le.h7 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β} {s : Set α} {a : α},
        StrictAntiOn f (Insert.insert a s) ↔ (∀ b ∈ s, b < a → f a < f b) ∧ StrictAntiOn f s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun b => if b then 1 else 0 : Bool → ℕ) ({b : Bool | b = Bool.true}) (Bool.false)) (by
  decide +kernel)

-- Nat.Prime.dvd_or_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_or_dvd.h4 : ¬∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ∨ p ∣ n := fun hc_h => absurd (@hc_h (2) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.ext_ediv_modEq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ext_ediv_modEq.h3 : ¬∀ {n a b : ℤ}, a ≡ b [ZMOD n] → a = b := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Int.ext_ediv_modEq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ext_ediv_modEq.h4 : ¬∀ {n a b : ℤ}, a / n = b / n → a = b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.getBijectionOfForallMemList_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.getBijectionOfForallMemList_coe.h3 : ¬∀ {α : Type} (l : List α), l.Nodup → ∀ (i : Fin l.length) (x : α), x ∈ l := fun hc_h => absurd (@hc_h (Bool) ([Bool.false]) (by
  decide) (0)) (by
  decide +kernel)

-- not_surjective_finite_infinite, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_surjective_finite_infinite.h3 : ¬∀ {α β : Type} [inst : Finite α] (f : α → β), ¬Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (not : Bool → Bool)) (by
  decide +kernel)

-- Set.encard_diff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_diff.h3 : ¬∀ {α : Type} {s t : Set α}, s.Finite → (t \ s).encard = t.encard - s.encard := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (by
  simp)) (by
  simp)

-- Set.ncard_ne_zero_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_ne_zero_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, autoParam s.Finite Set.ncard_ne_zero_of_mem._auto_1 → s.ncard ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (0) (by
  simp)) (by
  simp)

-- Set.ncard_ne_zero_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_ne_zero_of_mem.h4 : ¬∀ {α : Type} {s : Set α} {a : α}, a ∈ s → s.ncard ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) (0) (by
  decide)) (by
  simp)

-- Set.diff_nonempty_of_ncard_lt_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.diff_nonempty_of_ncard_lt_ncard.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam s.Finite Set.sdiff_nonempty_of_ncard_lt_ncard._auto_1 → (t \ s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  nofun)

-- Set.diff_nonempty_of_ncard_lt_ncard, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.diff_nonempty_of_ncard_lt_ncard.h4 : ¬∀ {α : Type} {s t : Set α}, s.ncard < t.ncard → (t \ s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Nat.replicate_subperm_primeFactorsList_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.replicate_subperm_primeFactorsList_iff.h3 : ¬∀ {a b n : ℕ}, b ≠ 0 → ((List.replicate n a).Subperm b.primeFactorsList ↔ a ^ n ∣ b) := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.replicate_subperm_primeFactorsList_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.replicate_subperm_primeFactorsList_iff.h4 : ¬∀ {a b n : ℕ}, Nat.Prime a → ((List.replicate n a).Subperm b.primeFactorsList ↔ a ^ n ∣ b) := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.mem_primeFactorsList_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList_mul.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → ∀ {p : ℕ}, p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∨ p ∈ b.primeFactorsList := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (2)) (by
  decide +kernel)

-- Nat.mem_primeFactorsList_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList_mul.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → ∀ {p : ℕ}, p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∨ p ∈ b.primeFactorsList := fun hc_h => absurd (@hc_h (2) (0) (by
  decide) (2)) (by
  decide +kernel)

-- Set.ncard_diff_add_ncard_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_diff_add_ncard_of_subset.h3 : ¬∀ {α : Type} {s t : Set α},
        autoParam t.Finite Set.ncard_sdiff_add_ncard_of_subset._auto_1 → (t \ s).ncard + s.ncard = t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- ZMod.isUnit_natCast_iff_not_dvd_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.isUnit_natCast_iff_not_dvd_pow.h3 : Not
      (∀ {p d a : Nat},
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d →
          Iff
            (@IsUnit
              (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
              (@Semiring.toMonoid
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                (@CommSemiring.toSemiring
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                  (@CommRing.toCommSemiring
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d))
                    (ZMod.commRing
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d)))))
              (@Nat.cast
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                (@AddMonoidWithOne.toNatCast
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                  (@AddGroupWithOne.toAddMonoidWithOne
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d))
                    (@Ring.toAddGroupWithOne
                      (ZMod
                        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                          d))
                      (@CommRing.toRing
                        (ZMod
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p d))
                        (ZMod.commRing
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p d))))))
                a))
            (Not (@Dvd.dvd Nat Nat.instDvd p a))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- ZMod.isUnit_natCast_iff_not_dvd_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.isUnit_natCast_iff_not_dvd_pow.h4 : Not
      (∀ {p d a : Nat},
        Nat.Prime p →
          Iff
            (@IsUnit
              (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
              (@Semiring.toMonoid
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                (@CommSemiring.toSemiring
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                  (@CommRing.toCommSemiring
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d))
                    (ZMod.commRing
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d)))))
              (@Nat.cast
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                (@AddMonoidWithOne.toNatCast
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                  (@AddGroupWithOne.toAddMonoidWithOne
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d))
                    (@Ring.toAddGroupWithOne
                      (ZMod
                        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                          d))
                      (@CommRing.toRing
                        (ZMod
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p d))
                        (ZMod.commRing
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p d))))))
                a))
            (Not (@Dvd.dvd Nat Nat.instDvd p a))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Set.ncard_sdiff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_sdiff.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam s.Finite Set.ncard_sdiff._auto_1 → (t \ s).ncard = t.ncard - s.ncard := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (by
  simp)) (by
  simp)

-- Set.ncard_diff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_diff.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam s.Finite Set.ncard_sdiff._auto_1 → (t \ s).ncard = t.ncard - s.ncard := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (by
  simp)) (by
  simp)

-- Set.ncard_sdiff_singleton_add_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_sdiff_singleton_add_one.h3 : ¬∀ {α : Type} {s : Set α} {a : α},
        autoParam s.Finite Set.ncard_sdiff_singleton_add_one._auto_1 → (s \ {a}).ncard + 1 = s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (by
  simp)) (by
  simp)

-- Nat.maxPowDvdDiv_base_pow_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_base_pow_mul.h2 : ¬∀ {p n : ℕ}, n ≠ 0 → ∀ (k : ℕ), p.maxPowDvdDiv (p ^ k * n) = (multiplicity p n + k, n.divMaxPow p) := fun hc_h => absurd (@hc_h (0) (1) (by
  decide) (1)) (by
  decide +kernel)

-- Nat.maxPowDvdDiv_base_pow_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_base_pow_mul.h3 : ¬∀ {p n : ℕ}, 1 < p → ∀ (k : ℕ), p.maxPowDvdDiv (p ^ k * n) = (multiplicity p n + k, n.divMaxPow p) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide) (1)) (by
  decide +kernel)

-- multiplicity_base_pow_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.multiplicity_base_pow_mul.h2 : ¬∀ {p n : ℕ}, n ≠ 0 → ∀ (k : ℕ), multiplicity p (p ^ k * n) = multiplicity p n + k := fun hc_h => absurd (@hc_h (1) (1) (by
  decide) (1)) (by
  simp)

-- Set.Finite.encard_lt_encard, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.encard_lt_encard.h4 : ¬∀ {α : Type} {s t : Set α}, s.Finite → s.encard < t.encard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Nat.ordCompl_div_pow_of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_div_pow_of_dvd.h4 : ¬∀ (k : ℕ) {x p : ℕ}, Nat.Prime p → x / p ^ k / p ^ (x / p ^ k).factorization p = x / p ^ x.factorization p := fun hc_h => absurd (@hc_h (1) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_eq_of_coprime_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_of_coprime_right.h3 : ¬∀ {p a b : ℕ}, p ∈ b.primeFactorsList → (a * b).factorization p = b.factorization p := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.factorization_eq_of_coprime_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_of_coprime_right.h4 : ¬∀ {p a b : ℕ}, a.Coprime b → (a * b).factorization p = b.factorization p := fun hc_h => absurd (@hc_h (2) (2) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ordCompl_pow_mul_of_not_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_pow_mul_of_not_dvd.h3 : ¬∀ {m : ℕ} (k : ℕ) {p : ℕ}, ¬p ∣ m → p ^ k * m / p ^ (p ^ k * m).factorization p = m := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ordCompl_pow_mul_of_not_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_pow_mul_of_not_dvd.h4 : ¬∀ {m : ℕ} (k : ℕ) {p : ℕ}, Nat.Prime p → p ^ k * m / p ^ (p ^ k * m).factorization p = m := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_pow_of_factorization_eq_single, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_pow_of_factorization_eq_single.h3 : ¬∀ {n p k : ℕ}, (n.factorization = fun₀ | p => k) → n = p ^ k := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  simp)) (by
  decide +kernel)

-- Nat.eq_pow_of_factorization_eq_single, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_pow_of_factorization_eq_single.h4 : ¬∀ {n p k : ℕ}, n ≠ 0 → n = p ^ k := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_eq_zero_iff_remainder, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_zero_iff_remainder.h3 : ¬∀ {p r : ℕ} (i : ℕ), r ≠ 0 → (¬p ∣ r ↔ (p * i + r).factorization p = 0) := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_eq_zero_iff_remainder, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_zero_iff_remainder.h4 : ¬∀ {p r : ℕ} (i : ℕ), Nat.Prime p → (¬p ∣ r ↔ (p * i + r).factorization p = 0) := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Bool.le_and, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.le_and.h3 : ¬∀ {x y z : Bool}, x ≤ z → x ≤ (y && z) := fun hc_h => absurd (@hc_h (Bool.true) (Bool.false) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Bool.le_and, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.le_and.h4 : ¬∀ {x y z : Bool}, x ≤ y → x ≤ (y && z) := fun hc_h => absurd (@hc_h (Bool.true) (Bool.true) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_factorial, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_factorial.h1 : ¬∀ {p n b : ℕ}, Nat.log p n < b → n.factorial.factorization p = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := fun hc_h => absurd (@hc_h (1) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_factorial, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_factorial.h4 : ¬∀ {p : ℕ}, Nat.Prime p → ∀ {n b : ℕ}, n.factorial.factorization p = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := fun hc_h => absurd (@hc_h (2) (by
  decide) (2) (0)) (by
  decide +kernel)

-- Set.map_eq_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.map_eq_of_subset.h3 : ¬∀ {α : Type} {s : Set α} {f : α ↪ α}, autoParam s.Finite Set.map_eq_of_subset._auto_1 → ⇑f '' s = s := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({ toFun := Bool.not, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ Bool }) (by
  simp)) (by
  simp)

-- Set.encard_sdiff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_sdiff.h3 : ¬∀ {α : Type} {s t : Set α}, s.Finite → (t \ s).encard = t.encard - s.encard := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (by
  simp)) (by
  simp)

-- Set.Finite.injOn_iff_bijOn_of_mapsTo, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.injOn_iff_bijOn_of_mapsTo.h4 : ¬∀ {α : Type} {s : Set α} {f : α → α}, s.Finite → (Set.InjOn f s ↔ Set.BijOn f s s) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Sym2.fromRel_mono_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_mono_iff.h3 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop}, Std.Symm r₂ → Std.Symm r₁ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) ((@Std.Symm.mk (Nat) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega))))) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sym2.fromRel_mono_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_mono_iff.h4 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop}, Std.Symm r₁ → Std.Symm r₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) ((@Std.Symm.mk (Nat) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega))))) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sym2.fromRel_eq_fromRel_iff_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_eq_fromRel_iff_eq.h3 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop}, Std.Symm r₂ → Std.Symm r₁ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) ((@Std.Symm.mk (Nat) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega))))) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sym2.fromRel_eq_fromRel_iff_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_eq_fromRel_iff_eq.h4 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop}, Std.Symm r₁ → Std.Symm r₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) ((@Std.Symm.mk (Nat) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega))))) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.Infinite.inter_of_finite_diff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.inter_of_finite_diff.h3 : ¬∀ {α : Type} {s t : Set α}, (s \ t).Finite → (s ∩ t).Infinite := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n % 2 = 0}) (by
  simp)) (by
  simp)

-- Set.sdiff_nonempty_of_ncard_lt_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sdiff_nonempty_of_ncard_lt_ncard.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam s.Finite Set.sdiff_nonempty_of_ncard_lt_ncard._auto_1 → (t \ s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  nofun)

-- Set.sdiff_nonempty_of_ncard_lt_ncard, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sdiff_nonempty_of_ncard_lt_ncard.h4 : ¬∀ {α : Type} {s t : Set α}, s.ncard < t.ncard → (t \ s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.Nontrivial.mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.mono.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → t.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Int.le.elim, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le.elim.h2 : ¬∀ {a b : ℤ} {P : Prop}, (∀ (n : ℕ), a + ↑n = b → P) → P := fun hc_h => absurd (@hc_h (1) (0) (False) (by
  omega)) (by
  decide +kernel)

-- Int.le.elim, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le.elim.h4 : ¬∀ {a b : ℤ}, a ≤ b → ∀ {P : Prop}, P := fun hc_h => absurd (@hc_h (0) (0) (by
  decide) (False)) (by
  decide +kernel)

-- Nat.count_lt_card, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_lt_card.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ} (hp : (Set.ofPred p).Finite), Nat.count p n < hp.toFinset.card := fun hc_h => absurd (fun hc_k0 => @hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) hc_k0) (by
  (simp <;> decide))

-- Set.powersetCard.exist_mem_powersetCard_of_inf, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.powersetCard.exist_mem_powersetCard_of_inf.h2 : ¬∀ (α : Type) (n : ℕ) [inst : Infinite α] (a : α), ∃ s ∈ Set.powersetCard α n, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (0) _ (0)) (by
  simp)

-- Set.powersetCard.exist_mem_powersetCard_of_inf, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.powersetCard.exist_mem_powersetCard_of_inf.h3 : ¬∀ (α : Type) (n : ℕ), 0 < n → ∀ (a : α), ∃ s ∈ Set.powersetCard α n, a ∈ s := fun hc_h => absurd (@hc_h (Bool) (3) (by
  decide) (Bool.false)) (by
  (simp <;> decide))

-- Stream'.mem_cycle, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Stream'.mem_cycle.h3.der.{u} : ∀ {α : Type u} {a : α} {l : List α}, a ∈ l → l ≠ [] := by
  (intros; grind)
theorem HypCheckProof.Stream'.mem_cycle.h3.{u} : ∀ {α : Type u} {a : α} {l : List α} (a_1 : a ∈ l), a ∈ Stream'.cycle l (HypCheckProof.Stream'.mem_cycle.h3.der a_1) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Stream'.mem_cycle hc_x0 hc_x1 hc_x2 (@HypCheckProof.Stream'.mem_cycle.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Set.pairwiseDisjoint_insert_of_notMem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pairwiseDisjoint_insert_of_notMem.h7 : ¬∀ {α ι : Type} [inst : PartialOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α} {i : ι},
        (Insert.insert i s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧ ∀ j ∈ s, Disjoint (f i) (f j) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instPartialOrder) (Nat.instOrderBot) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  simp)

-- Set.image2_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_congr.h7 : ¬∀ {α β γ : Type} {f f' : α → β → γ} {s : Set α} {t : Set β}, Set.image2 f s t = Set.image2 f' s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (fun a b => a < b : ℕ → ℕ → Bool) (fun a b => a ≤ b : ℕ → ℕ → Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Computation.get_eq_of_mem, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Computation.get_eq_of_mem.h2.der.{u} : ∀ {α : Type u} (s : Computation α) {a : α},
      @Membership.mem α (Computation α) (@Computation.instMembership α) s a → @Computation.Terminates α s := by
  (intros; solve_by_elim)
theorem HypCheckProof.Computation.get_eq_of_mem.h2.{u} : ∀ {α : Type u} (s : Computation α) {a : α}
      (a_1 : @Membership.mem α (Computation α) (@Computation.instMembership α) s a),
      @Eq α (@Computation.get α s (@HypCheckProof.Computation.get_eq_of_mem.h2.der α s a a_1)) a := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Computation.get_eq_of_mem hc_x0 hc_x1 (@HypCheckProof.Computation.get_eq_of_mem.h2.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x2 hc_x3

-- Finite.exists_ne_map_eq_of_infinite, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.exists_ne_map_eq_of_infinite.h2 : ¬∀ {α β : Type} [inst : Finite β] (f : α → β), ∃ (x : α) (y : α), x ≠ y ∧ f x = f y := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (not : Bool → Bool)) (by
  decide +kernel)

-- Finite.exists_ne_map_eq_of_infinite, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.exists_ne_map_eq_of_infinite.h3 : ¬∀ {α β : Type} [inst : Infinite α] (f : α → β), ∃ (x : α) (y : α), x ≠ y ∧ f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Nat.log_lt_of_lt_pow', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_lt_of_lt_pow'.h3 : ¬∀ {b x y : ℕ}, y < b ^ x → Nat.log b y < x := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.log_lt_of_lt_pow', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_lt_of_lt_pow'.h4 : ¬∀ {b x y : ℕ}, x ≠ 0 → Nat.log b y < x := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.log_lt_iff_lt_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_lt_iff_lt_pow.h1 : ¬∀ {b x y : ℕ}, y ≠ 0 → (Nat.log b y < x ↔ y < b ^ x) := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.log_lt_iff_lt_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_lt_iff_lt_pow.h4 : ¬∀ {b : ℕ}, 1 < b → ∀ {x y : ℕ}, Nat.log b y < x ↔ y < b ^ x := fun hc_h => absurd (@hc_h (2) (by
  decide) (0) (0)) (by
  decide +kernel)

-- Nat.le_log_iff_pow_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_log_iff_pow_le.h1 : ¬∀ {b x y : ℕ}, y ≠ 0 → (x ≤ Nat.log b y ↔ b ^ x ≤ y) := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.le_log_iff_pow_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_log_iff_pow_le.h4 : ¬∀ {b : ℕ}, 1 < b → ∀ {x y : ℕ}, x ≤ Nat.log b y ↔ b ^ x ≤ y := fun hc_h => absurd (@hc_h (2) (by
  decide) (0) (0)) (by
  decide +kernel)

-- Set.Nonempty.mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.mono.h3 : ¬∀ {α : Type} {s t : Set α}, s.Nonempty → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.Nonempty.mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.mono.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- Nat.le_log_of_pow_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_log_of_pow_le.h3 : ¬∀ {b x y : ℕ}, b ^ x ≤ y → x ≤ Nat.log b y := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.le_log_of_pow_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_log_of_pow_le.h4 : ¬∀ {b x y : ℕ}, 1 < b → x ≤ Nat.log b y := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.mem_dropLast_of_mem_of_ne_getLast?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dropLast_of_mem_of_ne_getLast?.h3 : ¬∀ {α : Type} {l : List α} {a : α}, Option.some a ≠ l.getLast? → a ∈ l.dropLast := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- List.mem_dropLast_of_mem_of_ne_getLast?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dropLast_of_mem_of_ne_getLast?.h4 : ¬∀ {α : Type} {l : List α} {a : α}, a ∈ l → a ∈ l.dropLast := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- EReal.le_sub_iff_add_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.le_sub_iff_add_le.h3 : ¬∀ {a b c : EReal}, b ≠ ⊤ ∨ c ≠ ⊤ → (a ≤ c - b ↔ a + b ≤ c) := fun hc_h => absurd (@hc_h (0) (⊥) (⊥) (by
  decide)) (by
  decide +kernel)

-- WellFounded.listPairwise_reverse_compl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WellFounded.listPairwise_reverse_compl.h3 : ¬∀ {α : Type} {r : α → α → Prop} {l : List α}, List.IsChain r l → List.Pairwise rᶜ l.reverse := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) ([Bool.false, Bool.true]) (by
  decide)) (by
  simp)

-- EReal.div_le_div_right_of_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_le_div_right_of_nonneg.h4 : ¬∀ {a b c : EReal}, 0 ≤ c → a / c ≤ b / c := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  simp)) (by
  (simp <;> omega))

-- DFinsupp.erase_single_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.erase_single_ne.h7 : ¬∀ {ι : Type} {β : ι → Type} [inst : (i : ι) → Zero (β i)] [inst_1 : DecidableEq ι] {i j : ι} (x : β i),
        (DFinsupp.erase j fun₀ | i => x) = fun₀ | i => x := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (instDecidableEqNat) (0) (0) (1)) (by
  decide +kernel)

-- DFinsupp.support_single_ne_zero, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.support_single_ne_zero.h7 : Not
      (∀ {ι : Type} {β : ι → Type} [inst : DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]
        [inst_2 :
          (i : ι) → (x : β i) → Decidable (@Ne (β i) x (@OfNat.ofNat (β i) (nat_lit 0) (@Zero.toOfNat0 (β i) (inst_1 i))))]
        {i : ι} {b : β i},
        @Eq (Finset ι) (@DFinsupp.support ι β inst inst_1 inst_2 (@DFinsupp.single ι β inst_1 inst i b))
          (@Singleton.singleton ι (Finset ι) (@Finset.instSingleton ι) i)) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instDecidableEqNat) (fun (i : Nat) => @MulZeroClass.toZero Nat Nat.instMulZeroClass) (fun (i x : Nat) =>
      @instDecidableNot
        (@Eq ((fun (a : Nat) => Nat) i) x
          (@OfNat.ofNat ((fun (a : Nat) => Nat) i) (nat_lit 0)
            (@Zero.toOfNat0 ((fun (a : Nat) => Nat) i)
              ((fun (i : Nat) => @MulZeroClass.toZero Nat Nat.instMulZeroClass) i))))
        (instDecidableEqNat x
          (@OfNat.ofNat ((fun (a : Nat) => Nat) i) (nat_lit 0)
            (@Zero.toOfNat0 ((fun (a : Nat) => Nat) i)
              ((fun (i : Nat) => @MulZeroClass.toZero Nat Nat.instMulZeroClass) i))))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- EReal.lt_div_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.lt_div_iff.h3 : ¬∀ {a b c : EReal}, b ≠ ⊤ → (a < c / b ↔ a * b < c) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- Set.univ_ne_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.univ_ne_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, Set.univ ≠ s → Set.univ ≠ t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({x : Bool | True}) (by
  simp)) (by
  simp)

-- Set.univ_ne_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.univ_ne_of_subset.h4 : ¬∀ {α : Type} {s t : Set α}, t ⊆ s → Set.univ ≠ t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) ({x : ℕ | True}) (by
  rfl)) (by
  simp)

-- List.injective_foldl_comp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.injective_foldl_comp.h3 : ¬∀ {α : Type} {l : List (α → α)} {f : α → α}, Function.Injective f → Function.Injective (List.foldl Function.comp f l) := fun hc_h => absurd (@hc_h (Bool) ([fun (x : Bool) => Bool.true]) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- List.injective_foldl_comp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.injective_foldl_comp.h4 : ¬∀ {α : Type} {l : List (α → α)} {f : α → α},
        (∀ f ∈ l, Function.Injective f) → Function.Injective (List.foldl Function.comp f l) := fun hc_h => absurd (@hc_h (ℕ) ([]) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Int.lt_div_iff_of_dvd_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.lt_div_iff_of_dvd_of_pos.h3 : ¬∀ {a b c : ℤ}, c ∣ b → (a < b / c ↔ c * a < b) := fun hc_h => absurd (@hc_h (-1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.lt_div_iff_of_dvd_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.lt_div_iff_of_dvd_of_pos.h4 : ¬∀ {a b c : ℤ}, 0 < c → (a < b / c ↔ c * a < b) := fun hc_h => absurd (@hc_h (0) (1) (2) (by
  decide)) (by
  decide +kernel)

-- List.getElem_mem_tail, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_mem_tail.h3 : ¬∀ {α : Type} {k : ℕ} (l : List α) (hk : k < l.length), l[k] ∈ l.tail := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (0) ([0]) hc_k0) (by
  decide +kernel)

-- List.getElem_mem_tail, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_mem_tail.h4 : ¬∀ {α : Type} {k : ℕ} (l : List α), k ≠ 0 → k < l.length := fun hc_h => absurd (@hc_h (ℕ) (1) ([]) (by
  decide)) (by
  decide +kernel)

-- Set.disjoint_image_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_image_image.h7 : ¬∀ {α β γ : Type} {f : β → α} {g : γ → α} {s : Set β} {t : Set γ}, Disjoint (f '' s) (g '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Int.div_lt_iff_of_dvd_of_neg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_iff_of_dvd_of_neg.h3 : ¬∀ {a b c : ℤ}, b ∣ a → (a / b < c ↔ b * c < a) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_iff_of_dvd_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_iff_of_dvd_of_neg.h4 : ¬∀ {a b c : ℤ}, b < 0 → (a / b < c ↔ b * c < a) := fun hc_h => absurd (@hc_h (1) (-2) (0) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_iff_of_dvd_of_neg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_iff_of_dvd_of_neg.h3 : ¬∀ {a b c : ℤ}, b ∣ a → (a / b ≤ c ↔ b * c ≤ a) := fun hc_h => absurd (@hc_h (0) (0) (-1) (by
  decide)) (by
  decide +kernel)

-- Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs.h3 : ¬∀ {a b c : ℤ}, (a - c).natAbs < b.natAbs → a = c := fun hc_h => absurd (@hc_h (0) (2) (1) (by
  decide)) (by
  decide +kernel)

-- Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs.h4 : ¬∀ {a b c : ℤ}, a % b = c → a = c := fun hc_h => absurd (@hc_h (1) (1) _ rfl) (by
  decide +kernel)

-- Matrix.cons_vecAppend, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.cons_vecAppend.h4 : ¬∀ {α : Type} {m n o : ℕ} (x : α) (u : Fin m → α) (v : Fin n → α), o + 1 = m + 1 + n := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (1) (0) (fun (a : Fin 0) => 0) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- WellFoundedRelation.asymmetricₙ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WellFoundedRelation.asymmetricₙ.h3 : ¬∀ {α : Type} [inst : WellFoundedRelation α] {l : List α}, List.IsChain WellFoundedRelation.rel l → l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (sizeOfWFRel) ([]) (by
  simp)) (by
  decide +kernel)

-- Set.empty_ne_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.empty_ne_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, ∅ ≠ s → ∅ ≠ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.empty_ne_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.empty_ne_of_subset.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → ∅ ≠ t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- Rat.mk_denom_ne_zero_of_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk_denom_ne_zero_of_ne_zero.h3 : ¬∀ {q : ℚ} {n d : ℤ}, q = Rat.divInt n d → d ≠ 0 := fun hc_h => absurd (@hc_h _ (0) (0) rfl) (by
  decide +kernel)

-- Rat.mk_denom_ne_zero_of_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk_denom_ne_zero_of_ne_zero.h4 : ¬∀ {q : ℚ} {n : ℤ} {d : ℤ}, q ≠ 0 → d ≠ 0 := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Part.get_eq_get_of_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.get_eq_get_of_eq.h2 : ¬∀ {α : Type} (a : Part α) {b : Part α}, a = b → a.Dom := fun hc_h => absurd (@hc_h (ℕ) _ (⊥) rfl) (by
  nofun)

-- Tuple.lt_card_ge_iff_apply_ge_of_antitone, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Tuple.lt_card_ge_iff_apply_ge_of_antitone.h7 : Not
      (∀ {n : Nat} {α : Type} {j : Fin n} {f : Fin n → α} [inst : Preorder α] {a : α}
        [inst_1 : @DecidableLE α (@Preorder.toLE α inst)],
        Iff
          (@LT.lt Nat instLTNat (@Fin.val n j)
            (@Finset.card (Fin n) {i : Fin n | @LE.le α (@Preorder.toLE α inst) a (f i)}))
          (@LE.le α (@Preorder.toLE α inst) a (f j))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Nat) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
      @ite Nat
        (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@of_decide_eq_true
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Bool.true)
                (@Eq.refl Bool Bool.true)))))
        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@of_decide_eq_true
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Bool.true)
                (@Eq.refl Bool Bool.true)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Nat.instPreorder) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.decLe)) (by
  decide +kernel)

-- Tuple.lt_card_lt_iff_apply_lt_of_monotone, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Tuple.lt_card_lt_iff_apply_lt_of_monotone.h7 : Not
      (∀ {n : Nat} {α : Type} {j : Fin n} {f : Fin n → α} [inst : Preorder α] {a : α}
        [inst_1 : @DecidableLT α (@Preorder.toLT α inst)],
        Iff
          (@LT.lt Nat instLTNat (@Fin.val n j)
            (@Finset.card (Fin n) {i : Fin n | @LT.lt α (@Preorder.toLT α inst) (f i) a}))
          (@LT.lt α (@Preorder.toLT α inst) (f j) a)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Nat) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
      @ite Nat
        (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@of_decide_eq_true
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Bool.true)
                (@Eq.refl Bool Bool.true)))))
        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@of_decide_eq_true
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Bool.true)
                (@Eq.refl Bool Bool.true)))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Nat.instPreorder) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.decLt)) (by
  decide +kernel)

-- Rat.mk'_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk'_pow.h2 : ¬∀ (num : ℤ) (den : ℕ), num.natAbs.Coprime den → ∀ (n : ℕ), den ≠ 0 := fun hc_h => absurd (@hc_h (1) (0) (by
  decide) (0)) (by
  decide +kernel)

-- Rat.mk'_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk'_pow.h3 : ¬∀ (num : ℤ) (den : ℕ), den ≠ 0 → ∀ (n : ℕ), num.natAbs.Coprime den := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (0)) (by
  decide +kernel)

-- ZMod.unitsMap_comp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.unitsMap_comp.h3 : ¬∀ {n m d : ℕ}, m ∣ d → n ∣ m := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- ZMod.unitsMap_comp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.unitsMap_comp.h4 : ¬∀ {n m d : ℕ}, n ∣ m → m ∣ d := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.ne_empty_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ne_empty_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, s ≠ ∅ → t ≠ ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.ne_empty_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ne_empty_of_subset.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → t ≠ ∅ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- List.Nodup.subperm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.subperm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.subperm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.subperm.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Nodup → l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- Matrix.ofNat_apply, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.ofNat_apply.h7 : ¬∀ {n α : Type} [inst : DecidableEq n] [inst : AddMonoidWithOne α] {i j : n} {d : ℕ}, d.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instAddMonoidWithOne) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.bitwise_of_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bitwise_of_ne_zero.h3 : ¬∀ {f : Bool → Bool → Bool} {n m : ℕ},
        m ≠ 0 → Nat.bitwise f n m = Nat.bit (f n.bodd m.bodd) (Nat.bitwise f (n / 2) (m / 2)) := fun hc_h => absurd (@hc_h (fun a b => !a || b : Bool → Bool → Bool) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.bitwise_of_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bitwise_of_ne_zero.h4 : ¬∀ {f : Bool → Bool → Bool} {n m : ℕ},
        n ≠ 0 → Nat.bitwise f n m = Nat.bit (f n.bodd m.bodd) (Nat.bitwise f (n / 2) (m / 2)) := fun hc_h => absurd (@hc_h (fun a b => !a || b : Bool → Bool → Bool) (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.find_min, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_min.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {m : ℕ}, ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0)) (by
  simp)

-- Nat.find_min, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_min.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p], (∃ (n : ℕ), p n) → ∀ {m : ℕ}, ¬p m := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (by
  simp) (0)) (by
  decide +kernel)

-- Finset.Pi.cons_same, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.Pi.cons_same.h7.der.{v, u_1} : ∀ {α : Type u_1} {δ : α → Sort v} [inst : DecidableEq α] (s : Finset α) (a : α) (b : δ a) (f : (a : α) → a ∈ s → δ a),
      a ∈ Insert.insert a s := by
  (intros; simp; done)
theorem HypCheckProof.Finset.Pi.cons_same.h7.{v, u_1} : ∀ {α : Type u_1} {δ : α → Sort v} [inst : DecidableEq α] (s : Finset α) (a : α) (b : δ a) (f : (a : α) → a ∈ s → δ a),
      Finset.Pi.cons s a b f a (HypCheckProof.Finset.Pi.cons_same.h7.der s a b f) = b := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Finset.Pi.cons_same hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Finset.Pi.cons_same.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- Fin.ne_last_of_ne_last_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.ne_last_of_ne_last_of_le.h3 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, a ≤ b → a ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.ne_last_of_ne_last_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.ne_last_of_ne_last_of_le.h4 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, b ≠ Fin.last n → a ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Set.nontrivial_of_exists_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_exists_ne.h3 : ¬∀ {α : Type} {s : Set α} {x : α}, (∃ y ∈ s, y ≠ x) → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (by
  simp)) (by
  simp)

-- Set.nontrivial_of_exists_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_exists_ne.h4 : ¬∀ {α : Type} {s : Set α} {x : α}, x ∈ s → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (by
  decide)) (by
  simp)

-- Set.Subsingleton.anti, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.anti.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True}) ({x : Bool | True}) (by
  rfl)) (by
  decide +kernel)

-- Set.Subsingleton.anti, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.anti.h4 : ¬∀ {α : Type} {s t : Set α}, t.Subsingleton → s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True}) ({b : Bool | b = Bool.true}) (by
  decide)) (by
  decide +kernel)

-- Fin.natCast_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_mono.h3 : Not
      (∀ {n a b : Nat},
        @LE.le Nat instLENat a b →
          @LE.le
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@instLEFin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Nat.cast
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Fin.NatCast.instNatCast
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
              a)
            (@Nat.cast
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Fin.NatCast.instNatCast
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
              b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Fin.natCast_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_mono.h4 : Not
      (∀ {n a b : Nat},
        @LE.le Nat instLENat b n →
          @LE.le
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@instLEFin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Nat.cast
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Fin.NatCast.instNatCast
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
              a)
            (@Nat.cast
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Fin.NatCast.instNatCast
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
              b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finsupp.filter_single_of_neg, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.filter_single_of_neg.h7 : ¬∀ {α M : Type} [inst : Zero M] (p : α → Prop) [inst_1 : DecidablePred p] {a : α} {b : M},
        (Finsupp.filter p fun₀ | a => b) = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (1)) (by
  simp)

-- Fin.predAbove_pred_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_pred_of_le.h3 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), p ≠ 0 → p ≤ i := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.predAbove_pred_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_pred_of_le.h4 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), p ≤ i → p ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_le_pred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_le_pred_iff.h3 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, b ≠ 0 → a ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_le_pred_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_le_pred_iff.h4 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, a ≠ Fin.last n → b ≠ 0 := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_succAbove, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_succAbove.h3 : ¬∀ {n : ℕ} (x : Fin n) (y : Fin (n + 1)), x.castSucc < y := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- List.Nodup.cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.cons.h3 : ¬∀ {α : Type} {l : List α} {a : α}, l.Nodup → (a :: l).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.cons.h4 : ¬∀ {α : Type} {l : List α} {a : α}, a ∉ l → (a :: l).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (1) (by
  decide)) (by
  decide +kernel)

-- Matrix.diag_single_of_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.diag_single_of_ne.h7 : ¬∀ {n α : Type} [inst : DecidableEq n] [inst_1 : Zero α] (i j : n) (c : α), (Matrix.single i j c).diag = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (0) (0) (1)) (by
  simp)

-- ENat.mul_le_mul_right_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.mul_le_mul_right_iff.h3 : ¬∀ {a x y : ℕ∞}, a ≠ ⊤ → (x * a ≤ y * a ↔ x ≤ y) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- ENat.mul_le_mul_right_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.mul_le_mul_right_iff.h4 : ¬∀ {a x y : ℕ∞}, a ≠ 0 → (x * a ≤ y * a ↔ x ≤ y) := fun hc_h => absurd (@hc_h (⊤) (2) (1) (by
  decide)) (by
  decide +kernel)

-- Fin.val_sub_castPred_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_castPred_of_le.h3 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, b ≤ a → a ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.val_sub_castPred_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_castPred_of_le.h4 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, a ≠ Fin.last n → b ≤ a := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.pred_lt_castPred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_lt_castPred_iff.h3 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, b ≠ Fin.last n → a ≠ 0 := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.pred_lt_castPred_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_lt_castPred_iff.h4 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, a ≠ 0 → b ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- HolorIndex.cast_type, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.HolorIndex.cast_type.h3 : ¬∀ {ds₁ ds₂ : List ℕ} (is : List ℕ), List.Forall₂ (fun (x1 x2 : ℕ) => x1 < x2) is ds₁ → ds₁ = ds₂ := fun hc_h => absurd (@hc_h ([]) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- HolorIndex.cast_type, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.HolorIndex.cast_type.h4 : ¬∀ {ds₁ ds₂ : List ℕ} (is : List ℕ), ds₁ = ds₂ → List.Forall₂ (fun (x1 x2 : ℕ) => x1 < x2) is ds₁ := fun hc_h => absurd (@hc_h _ ([]) ([0]) rfl) (by
  decide +kernel)

-- Int.natAbs_coe_sub_coe_lt_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_coe_sub_coe_lt_of_lt.h3 : Not
      (∀ {a b n : Nat},
        @LT.lt Nat instLTNat b n →
          @LT.lt Nat instLTNat
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
                (@Nat.cast Int instNatCastInt b)).natAbs
            n) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_coe_sub_coe_lt_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_coe_sub_coe_lt_of_lt.h4 : Not
      (∀ {a b n : Nat},
        @LT.lt Nat instLTNat a n →
          @LT.lt Nat instLTNat
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
                (@Nat.cast Int instNatCastInt b)).natAbs
            n) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- List.argmin_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.argmin_mem.h7 : ¬∀ {α β : Type} [inst : Preorder β] [inst : DecidableLT β] {f : α → β} {l : List α} {m : α}, m ∈ l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instPreorder) (Nat.decLt) (fun n => n + 1 : ℕ → ℕ) ([]) (0)) (by
  decide +kernel)

-- Nat.Coprime.of_dvd_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.of_dvd_left.h3 : ¬∀ {a₁ a₂ b : ℕ}, a₂.Coprime b → a₁.Coprime b := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.Coprime.of_dvd_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.of_dvd_left.h4 : ¬∀ {a₁ a₂ b : ℕ}, a₁ ∣ a₂ → a₁.Coprime b := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_inj.h3 : ¬∀ {n : ℕ} {i j : Fin (n + 1)} {hj : j ≠ Fin.last n}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_inj.h4 : ¬∀ {n : ℕ} {i j : Fin (n + 1)} {hi : i ≠ Fin.last n}, j ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.val_sub_castPred_of_ge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_castPred_of_ge.h3 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, a ≤ b → b ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.val_sub_castPred_of_ge, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_castPred_of_ge.h4 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, b ≠ Fin.last n → a ≤ b := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_lt_castPred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_lt_castPred_iff.h3 : ¬∀ {n : ℕ} {i j : Fin (n + 1)} {hj : j ≠ Fin.last n}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_lt_castPred_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_lt_castPred_iff.h4 : ¬∀ {n : ℕ} {i j : Fin (n + 1)} {hi : i ≠ Fin.last n}, j ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- List.forall_zipWith, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall_zipWith.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {p : γ → Prop} {l₁ : List α} {l₂ : List β},
        List.Forall p (List.zipWith f l₁ l₂) ↔ List.Forall₂ (fun (x : α) (y : β) => p (f x y)) l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n = 0 : ℕ → Prop) ([]) ([0])) (by
  decide +kernel)

-- List.zipWith_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.zipWith_congr.h7 : ¬∀ {α β γ : Type} (f g : α → β → γ) (la : List α) (lb : List β), List.zipWith f la lb = List.zipWith g la lb := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a + b : ℕ → ℕ → ℕ) ([0]) ([1])) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_add_sub_one_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_add_sub_one_iff.h3 : ¬∀ {p k n : ℕ}, n < p → (p ∣ (k + n - 1).choose n ↔ ∃ i < n, p ∣ k + i) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_add_sub_one_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_add_sub_one_iff.h4 : ¬∀ {p k n : ℕ}, Nat.Prime p → (p ∣ (k + n - 1).choose n ↔ ∃ i < n, p ∣ k + i) := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide)) (by
  decide +kernel)

-- List.mem_permutations_of_perm_lemma, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.mem_permutations_of_perm_lemma.h3.gneg.{u_1} : ∀ {α : Type u_1} {is l : List α},
      ¬(l.Perm ([] ++ is) → (∃ (ts' : List α) (_ : ts'.Perm []), l = ts' ++ is) ∨ l ∈ is.permutationsAux []) →
        l.Perm is → l ∈ is.permutations := by
  (intros; simp_all; done)
theorem HypCheckProof.List.mem_permutations_of_perm_lemma.h3.{u_1} : ∀ {α : Type u_1} {is l : List α}, l.Perm is → l ∈ is.permutations := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @List.mem_permutations_of_perm_lemma hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.List.mem_permutations_of_perm_lemma.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)

-- List.mem_permutations_of_perm_lemma, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_permutations_of_perm_lemma.h4 : ¬∀ {α : Type} {is l : List α},
        (l.Perm ([] ++ is) → (∃ (ts' : List α) (_ : ts'.Perm []), l = ts' ++ is) ∨ l ∈ is.permutationsAux []) →
          l ∈ is.permutations := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (by
  simp)) (by
  simp)

-- List.next_getLast_eq_head_of_notMem_dropLast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_getLast_eq_head_of_notMem_dropLast.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- Nat.nth_mem_anti, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_mem_anti.h4 : ¬∀ {p : ℕ → Prop} {a b : ℕ}, a ≤ b → p (Nat.nth p a) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.filter_range_nth_eq_insert_of_finite, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.filter_range_nth_eq_insert_of_finite.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p],
        (Set.ofPred p).Finite →
          ∀ {k : ℕ},
            {n ∈ Finset.range (Nat.nth p (k + 1)) | p n} =
              Insert.insert (Nat.nth p k) ({n ∈ Finset.range (Nat.nth p k) | p n}) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (by
  simp) (0)) (by
  simp)

-- Nat.count_nth_of_lt_card_finite, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_nth_of_lt_card_finite.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, (Set.ofPred p).Finite → Nat.count p (Nat.nth p n) = n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1) (by
  simp)) (by
  simp)

-- Set.univ_eq_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.univ_eq_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, Set.univ = s → Set.univ = t := fun hc_h => absurd (@hc_h (Bool) _ ({b : Bool | b = Bool.true}) rfl) (by
  simp)

-- Set.univ_eq_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.univ_eq_of_subset.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → Set.univ = t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  rfl)) (by
  simp)

-- Nat.gcd_mul_of_coprime_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcd_mul_of_coprime_of_dvd.h3 : ¬∀ {a b c : ℕ}, b ∣ c → (a * b).gcd c = b := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.gcd_mul_of_coprime_of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcd_mul_of_coprime_of_dvd.h4 : ¬∀ {a b c : ℕ}, a.Coprime c → (a * b).gcd c = b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.div_mul_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_mul_div.h3 : ¬∀ {n m k : ℕ}, n ∣ m → k / m * (m / n) = k / n := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.div_mul_div, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_mul_div.h4 : ¬∀ {n m k : ℕ}, m ∣ k → k / m * (m / n) = k / n := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Set.Subset.antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subset.antisymm.h3 : ¬∀ {α : Type} {a b : Set α}, b ⊆ a → a = b := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.Subset.antisymm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subset.antisymm.h4 : ¬∀ {α : Type} {a b : Set α}, a ⊆ b → a = b := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Nat.modEq_of_dvd', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_of_dvd'.h3 : ¬∀ {n a b : ℕ}, n ∣ b - a → a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.modEq_of_dvd', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_of_dvd'.h4 : ¬∀ {n a b : ℕ}, a ≤ b → a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.eq_empty_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_empty_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, s = ∅ → t = ∅ := fun hc_h => absurd (@hc_h (ℕ) _ ({n : ℕ | n = 0}) rfl) (by
  simp)

-- Set.eq_empty_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_empty_of_subset.h4 : ¬∀ {α : Type} {s t : Set α}, t ⊆ s → t = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Ordnode.Valid'.rotateL_lemma₃, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.rotateL_lemma₃.h3 : ¬∀ {a b c : ℕ}, b < 2 * c → a + b < 3 * c := fun hc_h => absurd (@hc_h (2) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.rotateL_lemma₃, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.rotateL_lemma₃.h4 : ¬∀ {a b c : ℕ}, 3 * a ≤ b + c → a + b < 3 * c := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.add_le_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_le_of_lt.h3 : ¬∀ {m a b : ℕ}, a < b → a + m ≤ b := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.add_le_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_le_of_lt.h4 : ¬∀ {m a b : ℕ}, a ≡ b [MOD m] → a + m ≤ b := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.SortedGE.sortedGT_of_nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.sortedGT_of_nodup.h3 : ¬∀ {α : Type} [inst : PartialOrder α] {l : List α}, l.Nodup → l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- List.SortedGE.sortedGT_of_nodup, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.sortedGT_of_nodup.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l : List α}, l.SortedGE → l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0, 0]) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.le_of_lt_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.le_of_lt_add.h3 : ¬∀ {m a b : ℕ}, a < b + m → a ≤ b := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.le_of_lt_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.le_of_lt_add.h4 : ¬∀ {m a b : ℕ}, a ≡ b [MOD m] → a ≤ b := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.eq_of_abs_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.eq_of_abs_lt.h3 : Not
      (∀ {m a b : Nat},
        @LT.lt Int Int.instLTInt
            (@abs Int instLatticeInt Int.instAddGroup
              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt b)
                (@Nat.cast Int instNatCastInt a)))
            (@Nat.cast Int instNatCastInt m) →
          @Eq Nat a b) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.eq_of_abs_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.eq_of_abs_lt.h4 : ¬∀ {m a b : ℕ}, a ≡ b [MOD m] → a = b := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.IsSuffix.nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsSuffix.nodup.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂.Nodup → l₁.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.IsSuffix.nodup, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsSuffix.nodup.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([0, 0]) (by
  decide)) (by
  decide +kernel)

-- Vector3.append_insert, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Vector3.append_insert.h7.der.{u_1} : ∀ {α : Type u_1} {m n : ℕ} (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (n + 1)), n + 1 + m = n + m + 1 := by
  (intros; lia)
theorem HypCheckProof.Vector3.append_insert.h7.{u_1} : ∀ {α : Type u_1} {m n : ℕ} (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (n + 1)),
      Vector3.insert a (t.append v) (Eq.recOn (HypCheckProof.Vector3.append_insert.h7.der a t v i) (i.add m)) =
        Eq.recOn (HypCheckProof.Vector3.append_insert.h7.der a t v i) (t.append (Vector3.insert a v i)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Vector3.append_insert hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Vector3.append_insert.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- Set.Nonempty.eq_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.eq_one.h1 : ¬∀ {α : Type} [inst : One α] {s : Set α}, s.Nonempty → s = {1} := fun hc_h => absurd (@hc_h (ℕ) (Nat.instOne) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.Nonempty.eq_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.eq_one.h4 : ¬∀ {α : Type} [inst : Subsingleton α] [inst : One α] {s : Set α}, s = {1} := fun hc_h => absurd (@hc_h (Unit) _ (PUnit.instOne_mathlib) (∅)) (by
  simp)

-- StrictAnti.sortedGE_listMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictAnti.sortedGE_listMap.h6 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : Preorder β] {f : α → β} {l : List α},
        (List.map f l).SortedGE ↔ l.SortedLE := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instPreorder) (fun n => n + 1 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- Set.MapsTo.val_restrict_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.val_restrict_apply.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} (x : ↑s), Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} }))) (by
  simp)

-- StrictAnti.sortedLE_listMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictAnti.sortedLE_listMap.h6 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : Preorder β] {f : α → β} {l : List α},
        (List.map f l).SortedLE ↔ l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instPreorder) (fun n => n + 1 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- Set.Subsingleton.antitoneOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.antitoneOn.h6 : ¬∀ {α β : Type} {s : Set α} [inst : Preorder α] [inst_1 : Preorder β] (f : α → β), AntitoneOn f s := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({x : Bool | True}) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- Finsupp.uniqueEquiv_symm_apply_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.uniqueEquiv_symm_apply_apply.h4 : ¬∀ {α M : Type} [inst : Zero M] (a : α) (m : M) (b : α), Subsingleton α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.of_mem_dlookup, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.of_mem_dlookup.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {b : β a} {l : List (Sigma β)}, (⟨a, b⟩ : Sigma β) ∈ l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) ([])) (by
  decide +kernel)

-- List.kerase_cons_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.kerase_cons_eq.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {s : Sigma β} {l : List (Sigma β)},
        List.kerase a (s :: l) = l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ((⟨1, 0⟩ : (_ : ℕ) × ℕ)) ([])) (by
  decide +kernel)

-- List.forall₂_take_append, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall₂_take_append.h6 : ¬∀ {α β : Type} {R : α → β → Prop} (l : List α) (l₁ l₂ : List β), List.Forall₂ R (List.take l₁.length l) l₁ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([0]) ([])) (by
  decide +kernel)

-- List.forall₂_drop, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall₂_drop.h6 : ¬∀ {α β : Type} {R : α → β → Prop} (n : ℕ) {l₁ : List α} {l₂ : List β}, List.Forall₂ R (List.drop n l₁) (List.drop n l₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) ([]) ([0])) (by
  decide +kernel)

-- StrictAntiOn.strictAnti, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictAntiOn.strictAnti.h6 : Not
      (∀ {α β : Type} {s : Set α} {f : α → β} [inst : Preorder α] [inst_1 : Preorder β],
        @StrictAnti (@Set.Elem α s) β
          (@Subtype.preorder α inst fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x) inst_1
          (@Function.comp (@Set.Elem α s) α β f
            (@Subtype.val α fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x))) := fun hc_h => absurd (@hc_h (Bool) (Nat) (@Set.ofPred Bool fun (x : Bool) => True) (fun b => if b then 1 else 0 : Bool → Nat) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (Nat.instPreorder)) (by
  decide +kernel)

-- List.forall₂_take, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall₂_take.h6 : ¬∀ {α β : Type} {R : α → β → Prop} (n : ℕ) {l₁ : List α} {l₂ : List β}, List.Forall₂ R (List.take n l₁) (List.take n l₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) ([]) ([0])) (by
  decide +kernel)

-- Matrix.sum_single_ofNat, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.sum_single_ofNat.h6 : ¬∀ {m α : Type} [inst : DecidableEq m] [inst : AddCommMonoidWithOne α] [inst : Fintype m] (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (Bool) (ℕ) (instDecidableEqBool) (Nat.instAddCommMonoidWithOne) (Bool.fintype) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.interleaves_append_singleton_append_singleton_of_length_eq_length, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleaves_append_singleton_append_singleton_of_length_eq_length.h6 : ¬∀ {α : Type} {r : α → α → Prop} {l₁ l₂ : List α} {a b : α},
        List.Interleaves r (l₁ ++ [a]) (l₂ ++ [b]) ↔ r b a ∧ List.Interleaves r l₁ (l₂ ++ [b]) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([]) ([0]) (0) (0)) (by
  simp)

-- Fin.contractNth_apply_of_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.contractNth_apply_of_eq.h6 : ¬∀ {n : ℕ} {α : Type} (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n),
        j.contractNth op g k = op (g k.castSucc) (g k.succ) := fun hc_h => absurd (@hc_h (1) (ℕ) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (fun a b => a - b : ℕ → ℕ → ℕ) (fun (a : Fin (1 + 1)) => 1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Matrix.vecAppend_apply_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.vecAppend_apply_zero.h4 : ¬∀ {m n : ℕ} {α : Type} {o : ℕ} (u : Fin (m + 1) → α) (v : Fin n → α), o + 1 = m + 1 + n := fun hc_h => absurd (@hc_h (0) (0) (ℕ) (1) (fun (a : Fin (0 + 1)) => 0) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- Mathlib.Meta.NormNum.IsNat.natCeil, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Mathlib.Meta.NormNum.IsNat.natCeil.h6 : ¬∀ {R : Type} [inst : Semiring R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] (r : R) (m : ℕ),
        Mathlib.Meta.NormNum.IsNat ⌈r⌉₊ m := fun hc_h => absurd (@hc_h (ℕ) (Nat.instSemiring) (Nat.instLinearOrder) (instFloorSemiringNat) (0) (1)) (by
  nofun)

-- Fin.append_cast_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.append_cast_right.h6 : ¬∀ {α : Type} {n m : ℕ} (xs : Fin n → α) (ys : Fin m → α) (m' : ℕ), m' = m := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (fun (a : Fin 0) => 0) (fun (a : Fin 0) => 0) (1)) (by
  decide +kernel)

-- Matrix.cons_vecAlt0, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.cons_vecAlt0.h3 : ¬∀ {α : Type} {m n : ℕ} (x y : α) (u : Fin m → α), m + 1 + 1 = n + 1 + (n + 1) := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0) (0) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- Matrix.vecAppend_eq_ite, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.vecAppend_eq_ite.h4 : ¬∀ {m n : ℕ} {α : Type} {o : ℕ} (u : Fin m → α) (v : Fin n → α), o = m + n := fun hc_h => absurd (@hc_h (0) (0) (ℕ) (1) (fun (a : Fin 0) => 0) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- Equiv.sigmaQuotFromRel_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.sigmaQuotFromRel_apply.h3 : ¬∀ {α β : Type} {r : α → α → Prop} {r' : β → β → Prop} (f : r →r r'), Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (1)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.isChain_cons_destutter'_of_rel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_cons_destutter'_of_rel.h6 : ¬∀ {α : Type} (R : α → α → Prop) [inst : DecidableRel R] (l : List α) {a b : α},
        List.IsChain R (a :: List.destutter' R b l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([]) (0) (0)) (by
  decide +kernel)

-- List.destutter'_cons_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.destutter'_cons_neg.h6 : ¬∀ {α : Type} (l : List α) {R : α → α → Prop} [inst : DecidableRel R] {a b : α},
        List.destutter' R b (a :: l) = List.destutter' R b l := fun hc_h => absurd (@hc_h (ℕ) ([]) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (1) (0)) (by
  decide +kernel)

-- Set.EqOn.bijOn_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.bijOn_iff.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β}, Set.BijOn f₁ s t ↔ Set.BijOn f₂ s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.EqOn.comp_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.comp_eq.h6 : ¬∀ {α β ι : Type} {f : ι → α} {g₁ g₂ : α → β}, g₁ ∘ f = g₂ ∘ f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  decide +kernel)

-- SemiconjBy.intCast_mul_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SemiconjBy.intCast_mul_right.h5 : ¬∀ {α : Type} [inst : Ring α] {a x y : α} (n : ℤ), SemiconjBy a (↑n * x) (↑n * y) := fun hc_h => absurd (@hc_h (Bool) (instBooleanRingBool.toRing) (Bool.true) (Bool.false) (Bool.true) (1)) (by
  nofun)

-- StrictMonoOn.restrict, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMonoOn.restrict.h6 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β} {s : Set α}, StrictMono (s.domRestrict f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun _ => 0 : Bool → ℕ) ({x : Bool | True})) (by
  decide +kernel)

-- Rat.isInt_intFloor, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isInt_intFloor.h6 : ¬∀ {R : Type} [inst : Ring R] [inst_1 : LinearOrder R] [inst_2 : FloorRing R] (r : R) (m : ℤ),
        Mathlib.Meta.NormNum.IsInt ⌊r⌋ m := fun hc_h => absurd (@hc_h (ℤ) (Int.instRing) (Int.instLinearOrder) (instFloorRingInt) (0) (1)) (by
  nofun)

-- DFinsupp.comapDomain'_zero, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain'_zero.h6 : ¬∀ {ι : Type} {β : ι → Type} {κ : Type} [inst : (i : ι) → Zero (β i)] (h : κ → ι) {h' : ι → κ},
        Function.LeftInverse h' h := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (Bool) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- Set.surjOn_iUnion, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.surjOn_iUnion.h6 : ¬∀ {α β ι : Type} {s : Set α} {t : ι → Set β} {f : α → β}, Set.SurjOn f s (⋃ (i : ι), t i) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.Nonempty.of_image2_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_image2_left.h6 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Int.clog_of_right_le_one, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.clog_of_right_le_one.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] (b : ℕ) {r : R},
        Int.clog b r = -↑(Nat.log b ⌊r⁻¹⌋₊) := fun hc_h => absurd (@hc_h (ℚ≥0) (NNRat.instSemifield) (instLinearOrderNNRat) (NNRat.instFloorSemiring) (2) (2)) (by
  decide +kernel)

-- Int.log_of_right_le_one, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.log_of_right_le_one.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] (b : ℕ) {r : R},
        Int.log b r = -↑(Nat.clog b ⌈r⁻¹⌉₊) := fun hc_h => absurd (@hc_h (ℚ≥0) (NNRat.instSemifield) (instLinearOrderNNRat) (NNRat.instFloorSemiring) (2) (2)) (by
  decide +kernel)

-- Set.mapsTo_iUnion_iUnion, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mapsTo_iUnion_iUnion.h6 : ¬∀ {α β ι : Type} {s : ι → Set α} {t : ι → Set β} {f : α → β}, Set.MapsTo f (⋃ (i : ι), s i) (⋃ (i : ι), t i) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Function.extend_val_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.extend_val_apply.h6 : ¬∀ {β γ : Type} {p : β → Prop} {g : { x : β // p x } → γ} {j : β → γ} {b : β}, p b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : { x : ℕ // (fun (n : ℕ) => n = 0) x }) => 0) (fun n => n + 1 : ℕ → ℕ) (1)) (by
  decide +kernel)

-- Finsupp.single_eq_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.single_eq_of_ne.h6 : ¬∀ {α M : Type} [inst : Zero M] {a a' : α} {b : M}, (fun₀ | a => b) a' = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) (0) (1)) (by
  simp)

-- List.head_le_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head_le_of_lt.h6 : ¬∀ {α : Type} [inst : Preorder α] {a a' : α} {l l' : List α}, a' ≤ a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (1) ([]) ([])) (by
  decide +kernel)

-- Nat.xgcdAux_rec, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.xgcdAux_rec.h6 : ¬∀ {r : ℕ} {s t : ℤ} {r' : ℕ} {s' t' : ℤ},
        r.xgcdAux s t r' s' t' = (r' % r).xgcdAux (s' - ↑r' / ↑r * s) (t' - ↑r' / ↑r * t) r s t := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (0) (1)) (by
  decide +kernel)

-- Matrix.diagonal_ofNat, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.diagonal_ofNat.h6 : ¬∀ {n α : Type} [inst : DecidableEq n] [inst : Zero α] [inst : NatCast α] (m : ℕ), m.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (instNatCastNat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- MonotoneOn.monotone, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.MonotoneOn.monotone.h6 : Not
      (∀ {α β : Type} {s : Set α} {f : α → β} [inst : Preorder α] [inst_1 : Preorder β],
        @Monotone (@Set.Elem α s) β
          (@Subtype.preorder α inst fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x) inst_1
          (@Function.comp (@Set.Elem α s) α β f
            (@Subtype.val α fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@Set.ofPred Bool fun (x : Bool) => True) (not : Bool → Bool) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (@PartialOrder.toPreorder Bool Bool.instPartialOrder)) (by
  decide +kernel)

-- Set.odd_ncard_compl_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.odd_ncard_compl_iff.h1 : ¬∀ {α : Type}, Even (Nat.card α) → ∀ (s : Set α), Odd sᶜ.ncard ↔ Odd s.ncard := fun hc_h => absurd (@hc_h (ℕ) (by
  simp) ({n : ℕ | n = 0})) (by
  simp)

-- Set.odd_ncard_compl_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.odd_ncard_compl_iff.h2 : ¬∀ {α : Type} [inst : Finite α] (s : Set α), Odd sᶜ.ncard ↔ Odd s.ncard := fun hc_h => absurd (@hc_h (Fin 3) _ (∅)) (by
  norm_num)

-- Int.ediv_of_neg_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ediv_of_neg_of_pos.h3 : ¬∀ {a b : ℤ}, a < 0 → a.ediv b = -((-a - 1) / b + 1) := fun hc_h => absurd (@hc_h (-1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.toFinset_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.toFinset_congr.h5 : ¬∀ {α : Type} {s t : Set α} [inst : Fintype ↑s] [inst_1 : Fintype ↑t], s.toFinset = t.toFinset := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true})) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.false}))) (by
  decide +kernel)

-- Set.toFinset_strict_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.toFinset_strict_mono.h5 : ¬∀ {α : Type} {s t : Set α} [inst : Fintype ↑s] [inst_1 : Fintype ↑t], s.toFinset ⊂ t.toFinset := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true})) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true}))) (by
  decide +kernel)

-- Set.toFinset_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.toFinset_mono.h5 : ¬∀ {α : Type} {s t : Set α} [inst : Fintype ↑s] [inst_1 : Fintype ↑t], s.toFinset ⊆ t.toFinset := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true})) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.false}))) (by
  decide +kernel)

-- Set.mk_preimage_prod_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mk_preimage_prod_right.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {a : α}, Prod.mk a ⁻¹' s ×ˢ t = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n % 2 = 0}) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Fin.instNeZeroHAddNatOfNat_mathlib, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.instNeZeroHAddNatOfNat_mathlib.h2 : Not
      (∀ {n m : Nat}
        [inst : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat m (instOfNatNat m))],
        @NeZero (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat m (instOfNatNat m))))
          (@Zero.ofOfNat0 (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat m (instOfNatNat m))))
            (@Fin.instOfNat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat m (instOfNatNat m)))
              (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat m (instOfNatNat m)) inst) (nat_lit 0)))
          (@OfNat.ofNat (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat m (instOfNatNat m)))) m
            (@Fin.instOfNat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat m (instOfNatNat m)))
              (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat m (instOfNatNat m)) inst) m))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) _) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.clog_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_pos.h2 : ¬∀ {b n : ℕ}, 1 < n → 0 < Nat.clog b n := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_pos.h3 : ¬∀ {b n : ℕ}, 1 < b → 0 < Nat.clog b n := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Function.LeftInverse.image_image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.image_image.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α} (s : Set α), g '' f '' s = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.log_lt_log_succ_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_lt_log_succ_iff.h3 : ¬∀ {b n : ℕ}, 1 < b → (Nat.log b n < Nat.log b (n + 1) ↔ b ^ Nat.log b (n + 1) = n + 1) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- EReal.toENNReal_lt_toENNReal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toENNReal_lt_toENNReal.h3 : ¬∀ {x y : EReal}, 0 ≤ x → x.toENNReal < y.toENNReal := fun hc_h => absurd (@hc_h (0) (0) (by
  rfl)) (by
  simp)

-- List.map_subset_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_subset_iff.h5 : ¬∀ {α β : Type} {l₁ l₂ : List α} (f : α → β), List.map f l₁ ⊆ List.map f l₂ ↔ l₁ ⊆ l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) ([1]) (fun _ => 0 : ℕ → ℕ)) (by
  decide +kernel)

-- EReal.sub_neg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_neg.h2 : ¬∀ {x y : EReal}, x ≠ ⊥ ∨ y ≠ ⊥ → (x - y < 0 ↔ x < y) := fun hc_h => absurd (@hc_h (⊤) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.sub_neg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_neg.h3 : ¬∀ {x y : EReal}, x ≠ ⊤ ∨ y ≠ ⊤ → (x - y < 0 ↔ x < y) := fun hc_h => absurd (@hc_h (⊥) (⊥) (by
  decide)) (by
  decide +kernel)

-- EReal.add_lt_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_lt_top.h2 : ¬∀ {x y : EReal}, y ≠ ⊤ → x + y < ⊤ := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  decide +kernel)

-- EReal.add_lt_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_lt_top.h3 : ¬∀ {x y : EReal}, x ≠ ⊤ → x + y < ⊤ := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  decide +kernel)

-- ENNReal.toEReal_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toEReal_sub.h2 : Not
      (∀ {x y : ENNReal},
        @LE.le ENNReal ENNReal.instLE y x →
          @Eq EReal (↑(@HSub.hSub ENNReal ENNReal ENNReal (@instHSub ENNReal ENNReal.instSub) x y))
            (@HSub.hSub EReal EReal EReal
              (@instHSub EReal
                (@SubNegMonoid.toSub EReal (@SubNegZeroMonoid.toSubNegMonoid EReal EReal.instSubNegZeroMonoid)))
              ↑x ↑y)) := fun hc_h => absurd (@hc_h (@Top.top ENNReal ENNReal.instTop) (@Top.top ENNReal ENNReal.instTop) (by
  decide)) (by
  decide +kernel)

-- EReal.sub_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_nonneg.h2 : ¬∀ {x y : EReal}, x ≠ ⊥ ∨ y ≠ ⊥ → (0 ≤ x - y ↔ y ≤ x) := fun hc_h => absurd (@hc_h (⊤) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.sub_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_nonneg.h3 : ¬∀ {x y : EReal}, x ≠ ⊤ ∨ y ≠ ⊤ → (0 ≤ x - y ↔ y ≤ x) := fun hc_h => absurd (@hc_h (⊥) (⊥) (by
  decide)) (by
  decide +kernel)

-- EReal.add_pos_of_pos_of_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_pos_of_pos_of_nonneg.h2 : ¬∀ {a b : EReal}, 0 ≤ b → 0 < a + b := fun hc_h => absurd (@hc_h (0) (0) (by
  rfl)) (by
  simp)

-- Function.apply_eq_of_range_eq_singleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.apply_eq_of_range_eq_singleton.h4 : ¬∀ {α β : Type} {f : α → β} {b : β} (a : α), f a = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0)) (by
  decide +kernel)

-- Nat.set_induction, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.set_induction.h1 : ¬∀ {S : Set ℕ}, (∀ k ∈ S, k + 1 ∈ S) → ∀ (n : ℕ), n ∈ S := fun hc_h => absurd (@hc_h ({x : ℕ | False}) (by
  simp) (0)) (by
  decide +kernel)

-- Nat.set_induction, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.set_induction.h2 : ¬∀ {S : Set ℕ}, 0 ∈ S → ∀ (n : ℕ), n ∈ S := fun hc_h => absurd (@hc_h ({n : ℕ | n = 0}) (by
  decide) (1)) (by
  decide +kernel)

-- Set.MapsTo.restrict_surjective_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.restrict_surjective_iff.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- List.inter_cons_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.inter_cons_of_mem.h5 : ¬∀ {α : Type} {l₂ : List α} {a : α} [inst : DecidableEq α] (l₁ : List α), (a :: l₁) ∩ l₂ = a :: l₁ ∩ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- Disjoint.of_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.of_image.h5 : ¬∀ {α β : Type} {f : α → β} {s t : Set α}, Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.minimum_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_mem.h5 : ¬∀ {α : Type} [inst : Preorder α] [inst : DecidableLT α] {l : List α} {m : α}, m ∈ l := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLt) ([]) (0)) (by
  decide +kernel)

-- List.not_lt_minimum_of_mem', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_lt_minimum_of_mem'.h5 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : DecidableLT α] {l : List α} {a : α}, ¬↑a < l.minimum := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLt) ([]) (0)) (by
  decide +kernel)

-- List.max_le_of_forall_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.max_le_of_forall_le.h5 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] (l : List α) (a : α), List.foldr Max.max ⊥ l ≤ a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (Nat.instOrderBot) ([1]) (0)) (by
  decide +kernel)

-- List.bagInter_erase_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.bagInter_erase_of_notMem.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {a : α} [inst : DecidableEq α], l₁.bagInter (l₂.erase a) = l₁.bagInter l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0]) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- List.maximum_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maximum_mem.h5 : ¬∀ {α : Type} [inst : Preorder α] [inst : DecidableLT α] {l : List α} {m : α}, m ∈ l := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLt) ([]) (0)) (by
  decide +kernel)

-- Fin.succ_predAbove_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succ_predAbove_zero.h3 : ¬∀ {n : ℕ} [inst : NeZero n] {j : Fin (n + 1)}, (Fin.predAbove 0 j).succ = j := fun hc_h => absurd (@hc_h (1) _ ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- List.mem_of_mem_inter_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_of_mem_inter_left.h5 : ¬∀ {α : Type} {l₁ : List α} {l₂ : List α} {a : α} [inst : DecidableEq α], a ∈ l₁ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- Fin.castPred_eq_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_eq_zero.h3 : ¬∀ {n : ℕ} [inst : NeZero n] {i : Fin (n + 1)}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) _ ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- List.mem_union_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_union_left.h4 : ¬∀ {α : Type} {l₁ : List α} {a : α} [inst : DecidableEq α] (l₂ : List α), a ∈ l₁ ∪ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- List.mem_of_mem_inter_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_of_mem_inter_right.h5 : ¬∀ {α : Type} {l₁ : List α} {l₂ : List α} {a : α} [inst : DecidableEq α], a ∈ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- List.erase_bagInter_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.erase_bagInter_of_notMem.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {a : α} [inst : DecidableEq α], (l₁.erase a).bagInter l₂ = l₁.bagInter l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0]) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- List.erase_bagInter_of_not_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.erase_bagInter_of_not_mem.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {a : α} [inst : DecidableEq α], (l₁.erase a).bagInter l₂ = l₁.bagInter l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0]) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- Fin.pred_lt_castPred, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_lt_castPred.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a ≠ Fin.last n → a ≠ 0 := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.pred_lt_castPred, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_lt_castPred.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a ≠ 0 → a ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- EReal.div_nonpos_of_nonneg_of_nonpos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_nonpos_of_nonneg_of_nonpos.h3 : ¬∀ {a b : EReal}, 0 ≤ a → a / b ≤ 0 := fun hc_h => absurd (@hc_h (1) (1) (by
  simp)) (by
  (simp <;> omega))

-- Fin.rev_castPred, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.rev_castPred.h2 : ¬∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.rev_castPred, hypothesis 3: removable
/- FAILED: 3:24: `grind` failed
case grind
n : ℕ
i : Fin (n + 1)
h : ¬i = Fin.last n
⊢ ¬¬i.rev = 0 → False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬i = Fin.last n
  [eqc] False propositions
    [prop] i = Fin.last n
  [ematch] E-matching patterns
    [thm] Fin.val_last: [Fin.last #0]
[grind] Issues
  [issue] (deterministic) timeout at `«abstract nested proofs»`, maximum number of heartbeats (1000) has been reached
      
      Note: Use `set_option maxHeartbeats <num>` to set the limit.
     | 27:24: `grind` failed
case grind
n : ℕ
i : Fin (n + 1)
h : ¬i = Fin.last n
⊢ ¬¬i.rev = 0 → False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬i = Fin.last n
  [eqc] False propositions
    [prop] i = Fin.last n
  [ematch] E-matching patterns
    [thm] Fin.val_last: [Fin.last #0]
[grind] Issues
  [issue] (deterministic) timeout at `whnf`, maximum number of heartbeats (1000) has been reached
      
      Note: Use `set_option maxHeartbeats <num>` to set the limit.
      
      Hint: Addit | 3:24: `grind` failed
case grind
n : ℕ
i : Fin (n + 1)
h : ¬i = Fin.last n
⊢ ¬¬i.rev = 0 → False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬i = Fin.last n
  [eqc] False propositions
    [prop] i = Fin.last n
  [ematch] E-matching patterns
    [thm] Fin.val_last: [Fin.last #0]
[grind] Issues
  [issue] (deterministic) timeout at `«abstract nested proofs»`, maximum number of heartbeats (1000) has been reached
      
      Note: Use `set_option maxHeartbeats <num>` to set the limit.
     | 25:24: `grind` failed
case grind
n : ℕ
i : Fin (n + 1)
h : ¬i = Fin.last n
⊢ ¬¬i.rev = 0 → False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬i = Fin.last n
  [eqc] False propositions
    [prop] i = Fin.last n
  [ematch] E-matching patterns
    [thm] Fin.val_last: [Fin.last #0]
[grind] Issues
  [issue] (deterministic) timeout at `whnf`, maximum number of heartbeats (1000) has been reached
      
      Note: Use `set_option maxHeartbeats <num>` to set the limit.
      
      Hint: Addit | 3:24: `grind` failed
case grind
n : ℕ
i : Fin (n + 1)
h : ¬i = Fin.last n
⊢ ¬¬i.rev = 0 → False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬i = Fin.last n
  [eqc] False propositions
    [prop] i = Fin.last n
  [ematch] E-matching patterns
    [thm] Fin.val_last: [Fin.last #0]
[grind] Issues
  [issue] (deterministic) timeout at `isDefEq`, maximum number of heartbeats (1000) has been reached
      
      Note: Use `set_option maxHeartbeats <num>` to set the limit.
      
      Hint: Ad
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.rev_castPred.h3.der : ∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → i.rev ≠ 0 := by
  (intros; simp_all <;> grind)
theorem HypCheckProof.Fin.rev_castPred.h3 : ∀ {n : ℕ} {i : Fin (n + 1)} (h : i ≠ Fin.last n),
      (i.castPred h).rev = i.rev.pred (HypCheckProof.Fin.rev_castPred.h3.der h) := by
  intro hc_x0 hc_x1 hc_x2
  exact @Fin.rev_castPred hc_x0 hc_x1 hc_x2 (@HypCheckProof.Fin.rev_castPred.h3.der hc_x0 hc_x1 hc_x2)
-/

-- List.Perm.bagInter_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.bagInter_right.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l₁ l₂ : List α} (t : List α), (l₁.bagInter t).Perm (l₂.bagInter t) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([0]) ([0])) (by
  decide +kernel)

-- Set.MapsTo.coe_restrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.coe_restrict.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- List.getI_append_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getI_append_right.h5 : ¬∀ {α : Type} [inst : Inhabited α] (l l' : List α) (n : ℕ), (l ++ l').getI n = l'.getI (n - l.length) := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ([1]) ([]) (0)) (by
  decide +kernel)

-- List.getI_append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getI_append.h5 : ¬∀ {α : Type} [inst : Inhabited α] (l l' : List α) (n : ℕ), (l ++ l').getI n = l.getI n := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ([]) ([1]) (0)) (by
  decide +kernel)

-- List.getD_append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getD_append.h5 : ¬∀ {α : Type} (l l' : List α) (d : α) (n : ℕ), (l ++ l').getD n d = l.getD n d := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (1) (0)) (by
  decide +kernel)

-- Nat.succ_mul_binomial, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.succ_mul_binomial.h5 : ¬∀ {α : Type} {f : α → ℕ} {a b : α} [inst : DecidableEq α],
        (f a + f b).succ * Nat.multinomial {a, b} f = (f a).succ * Nat.multinomial {a, b} (Function.update f a (f a).succ) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- Function.Surjective.bijective_of_finite, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.bijective_of_finite.h3 : ¬∀ {α : Type} [inst : Finite α] {f : α → α}, Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) _ (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Nat.binomial_spec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.binomial_spec.h5 : ¬∀ {α : Type} {f : α → ℕ} {a b : α} [inst : DecidableEq α],
        (f a).factorial * (f b).factorial * Nat.multinomial {a, b} f = (f a + f b).factorial := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- Set.iUnion_mono', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iUnion_mono'.h5 : ¬∀ {α ι ι₂ : Type} {s : ι → Set α} {t : ι₂ → Set α}, ⋃ (i : ι), s i ⊆ ⋃ (i : ι₂), t i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {x : ℕ | False})) (by
  simp)

-- ENat.le_iInf_add_iInf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.le_iInf_add_iInf.h5 : ¬∀ {ι : Type} {f : ι → ℕ∞} {a : ℕ∞} {κ : Type} {g : κ → ℕ∞}, a ≤ iInf f + iInf g := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => 0) (1) (ℕ) (fun (a : ℕ) => 0)) (by
  simp)

-- Finite.surjective_of_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.surjective_of_injective.h3 : ¬∀ {α : Type} [inst : Finite α] {f : α → α}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) _ (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Set.exists_set_mem_of_union_eq_top, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_set_mem_of_union_eq_top.h4 : ¬∀ {β ι : Type} (t : Set ι) (s : ι → Set β) (x : β), ∃ i ∈ t, x ∈ s i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (1)) (by
  simp)

-- Fintype.card_of_bijective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_of_bijective.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] {f : α → β}, Fintype.card α = Fintype.card β := fun hc_h => absurd (@hc_h (Bool) (Fin 3) (Bool.fintype) (Fin.fintype 3) (fun (a : Bool) => (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3))) (by
  decide +kernel)

-- Set.codRestrict_domRestrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.codRestrict_domRestrict.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} (x : ↑s), f ↑x ∈ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.mem_iUnion_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_iUnion_of_mem.h5 : ¬∀ {α ι : Type} {s : ι → Set α} {a : α} (i : ι), a ∈ ⋃ (i : ι), s i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (1) (0)) (by
  simp)

-- Nat.not_exists_sq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_exists_sq.h2 : ¬∀ {m n : ℕ}, n < (m + 1) * (m + 1) → ¬∃ (t : ℕ), t * t = n := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- Nat.not_exists_sq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_exists_sq.h3 : ¬∀ {m n : ℕ}, m * m < n → ¬∃ (t : ℕ), t * t = n := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- Nat.coprime_div_gcd_of_squarefree, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_div_gcd_of_squarefree.h2 : ¬∀ {m n : ℕ}, n ≠ 0 → (m / m.gcd n).Coprime n := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.squarefree_pow_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.squarefree_pow_iff.h2 : ¬∀ {n k : ℕ}, k ≠ 0 → (Squarefree (n ^ k) ↔ Squarefree n ∧ k = 1) := fun hc_h => absurd (@hc_h (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.squarefree_pow_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.squarefree_pow_iff.h3 : ¬∀ {n k : ℕ}, n ≠ 1 → (Squarefree (n ^ k) ↔ Squarefree n ∧ k = 1) := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Set.exists_lt_mem_inter_of_not_pairwiseDisjoint, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_lt_mem_inter_of_not_pairwiseDisjoint.h5 : ¬∀ {α ι : Type} {s : Set ι} [inst : LinearOrder ι] {f : ι → Set α}, ∃ i ∈ s, ∃ j ∈ s, i < j ∧ ∃ (x : α), x ∈ f i ∩ f j := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (Nat.instLinearOrder) (fun (a : ℕ) => {n : ℕ | n = 0})) (by
  simp)

-- List.filterMap_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.filterMap_congr.h5 : ¬∀ {α β : Type} {f g : α → Option β} {l : List α}, List.filterMap f l = List.filterMap g l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => none : ℕ → Option ℕ) (some : ℕ → Option ℕ) ([0])) (by
  decide +kernel)

-- List.pairwise_cons_cons_iff_of_trans, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_cons_cons_iff_of_trans.h2 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a b : α},
        List.Pairwise R (a :: b :: l) ↔ R a b ∧ List.Pairwise R (b :: l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop) ([0]) (0) (1)) (by
  decide +kernel)

-- Nat.pow_sub_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_sub_one.h2 : ¬∀ {x a : ℕ}, a ≠ 0 → x ^ (a - 1) = x ^ a / x := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.pow_sub_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_sub_one.h3 : ¬∀ {x a : ℕ}, x ≠ 0 → x ^ (a - 1) = x ^ a / x := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Set.LeftInvOn.eqOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.LeftInvOn.eqOn.h5 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {f' : β → α}, Set.EqOn (f' ∘ f) id s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.EqOn.symm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.symm.h5 : ¬∀ {α β : Type} {s : Set α} {f₁ f₂ : α → β}, Set.EqOn f₂ f₁ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Function.Embedding.is_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.is_empty.h2 : ¬∀ {α β : Type} [inst : Finite β], IsEmpty (α ↪ β) := fun hc_h => absurd (@hc_h (Bool) (Bool) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.false ({ toFun := Bool.not, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ Bool } : Bool ↪ Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.image_subset_preimage_of_inverse, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_subset_preimage_of_inverse.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α} (s : Set α), f '' s ⊆ g ⁻¹' s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- WithZeroMulInt.toNNReal_pos_apply, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_pos_apply.h1 : ¬∀ {e : NNReal} {x : WithZero (Multiplicative ℤ)}, x = 0 → e ≠ 0 := fun hc_h => absurd (@hc_h (0) _ rfl) (by
  simp)

-- WithZeroMulInt.toNNReal_pos_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_pos_apply.h3 : ¬∀ {e : NNReal} (he : e ≠ 0) {x : WithZero (Multiplicative ℤ)}, (WithZeroMulInt.toNNReal he) x = 0 := fun hc_h => absurd (fun hc_k0 => @hc_h (1) hc_k0 (1)) (by
  simp)

-- WithZeroMulInt.toNNReal_neg_apply, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_neg_apply.h1 : ¬∀ {e : NNReal} {x : WithZero (Multiplicative ℤ)}, x ≠ 0 → e ≠ 0 := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- WithZeroMulInt.toNNReal_neg_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_neg_apply.h3 : ¬∀ {e : NNReal} (he : e ≠ 0) {x : WithZero (Multiplicative ℤ)}, (WithZeroMulInt.toNNReal he) x = e ^ x.log := fun hc_h => absurd (fun hc_k0 => @hc_h (1) hc_k0 (0)) (by
  simp)

-- List.Forall₂.flip, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.flip.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {a : List α} {b : List β}, List.Forall₂ R a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([0])) (by
  decide +kernel)

-- Set.card_le_card, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.card_le_card.h5 : ¬∀ {α : Type} {s t : Set α} [inst : Fintype ↑s] [inst_1 : Fintype ↑t], Fintype.card ↑s ≤ Fintype.card ↑t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({x : Bool | False}) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true})) (Subtype.fintype (Membership.mem {x : Bool | False}))) (by
  decide +kernel)

-- Disjoint.preimage, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.preimage.h5 : ¬∀ {α β : Type} (f : α → β) {s t : Set β}, Disjoint (f ⁻¹' s) (f ⁻¹' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- ZMod.coe_int_mul_val_inv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.coe_int_mul_val_inv.h1 : Not
      (∀ {n : Nat} {m : Int},
        @IsCoprime Int Int.instCommSemiring m (@Nat.cast Int instNatCastInt n) →
          @Eq (ZMod n)
            (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
              (@instHMul (ZMod n)
                (@Distrib.toMul (ZMod n)
                  (@instDistribOfSemiring (ZMod n)
                    (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
              (@Int.cast (ZMod n)
                (@AddGroupWithOne.toIntCast (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                m)
              (@Nat.cast (ZMod n)
                (@AddMonoidWithOne.toNatCast (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                (@ZMod.val n
                  (@Inv.inv (ZMod n) (ZMod.instInv n)
                    (@Int.cast (ZMod n)
                      (@AddGroupWithOne.toIntCast (ZMod n)
                        (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                      m)))))
            (@OfNat.ofNat (ZMod n) (nat_lit 1)
              (@One.toOfNat1 (ZMod n)
                (@AddMonoidWithOne.toOne (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide)) (by
  decide +kernel)

-- ZMod.coe_int_mul_val_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.coe_int_mul_val_inv.h3 : Not
      (∀ {n : Nat} [inst : @NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) n] {m : Int},
        @Eq (ZMod n)
          (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
            (@instHMul (ZMod n)
              (@Distrib.toMul (ZMod n)
                (@instDistribOfSemiring (ZMod n)
                  (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              m)
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              (@ZMod.val n
                (@Inv.inv (ZMod n) (ZMod.instInv n)
                  (@Int.cast (ZMod n)
                    (@AddGroupWithOne.toIntCast (ZMod n)
                      (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                    m)))))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- Set.card_range_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.card_range_of_injective.h4 : ¬∀ {α β : Type} [inst : Fintype α] {f : α → β} [inst_1 : Fintype ↑(Set.range f)],
        Fintype.card ↑(Set.range f) = Fintype.card α := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (fun _ => 0 : Bool → ℕ) (Set.fintypeRange fun (x : Bool) => 0)) (by
  decide +kernel)

-- List.Forall₂.length_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.length_eq.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([0])) (by
  decide +kernel)

-- List.prev_cons_cons_eq, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.prev_cons_cons_eq.h5.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x z : α), x ∈ x :: z :: l := by
  (intros; solve_by_elim)
theorem HypCheckProof.List.prev_cons_cons_eq.h5.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x z : α),
      (x :: z :: l).prev x (HypCheckProof.List.prev_cons_cons_eq.h5.der l x z) = (z :: l).getLast (List.cons_ne_nil z l) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.prev_cons_cons_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.prev_cons_cons_eq.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- List.take_insertIdx_eq_take_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.take_insertIdx_eq_take_of_le.h5 : ¬∀ {α : Type} (l : List α) (x : α) (i j : ℕ), List.take i (l.insertIdx j x) = List.take i l := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (1) (0)) (by
  decide +kernel)

-- List.eq_or_mem_of_mem_insertIdx, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_or_mem_of_mem_insertIdx.h5 : ¬∀ {α : Type} {l : List α} {n : ℕ} {a b : α}, a = b ∨ a ∈ l := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0) (1)) (by
  decide +kernel)

-- Finsupp.support_single_ne_bot, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_single_ne_bot.h5 : ¬∀ {α M : Type} [inst : Zero M] {b : M} (i : α), (fun₀ | i => b).support ≠ ⊥ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) (0)) (by
  simp)

-- List.mem_of_nextOr_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_of_nextOr_ne.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {xs : List α} {x : α} {d : α}, x ∈ xs := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0) (0)) (by
  decide +kernel)

-- Set.Nonempty.subset_preimage_const, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.subset_preimage_const.h3 : ¬∀ {α β : Type} {s : Set α} (t : Set β) (a : β), s ⊆ (fun (x : α) => a) ⁻¹' t ↔ a ∈ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- List.next_cons_cons_eq, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.next_cons_cons_eq.h5.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x z : α), x ∈ x :: z :: l := by
  (intros; solve_by_elim)
theorem HypCheckProof.List.next_cons_cons_eq.h5.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x z : α),
      (x :: z :: l).next x (HypCheckProof.List.next_cons_cons_eq.h5.der l x z) = z := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.next_cons_cons_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.next_cons_cons_eq.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Set.card_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.card_insert.h4 : ¬∀ {α : Type} {a : α} (s : Set α) [inst : Fintype ↑s] {d : Fintype ↑(Insert.insert a s)},
        Fintype.card ↑(Insert.insert a s) = Fintype.card ↑s + 1 := fun hc_h => absurd (@hc_h (Bool) (Bool.false) ({b : Bool | b = Bool.false}) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.false})) (Set.fintypeInsert Bool.false {b : Bool | b = Bool.false})) (by
  decide +kernel)

-- List.nextOr_eq_getElem_idxOf_succ_of_mem_dropLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_eq_getElem_idxOf_succ_of_mem_dropLast.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α} (d : α), a ∈ l.dropLast := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0) (0)) (by
  decide +kernel)

-- Set.preimage_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.preimage_mono.h5 : ¬∀ {α β : Type} {f : α → β} {s t : Set β}, f ⁻¹' s ⊆ f ⁻¹' t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.infs_subset_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infs_subset_left.h5 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s t₁ t₂ : Set α},
        @LE.le (Set α) (@Set.instLE α) (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t₁)
          (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t₂)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False)) (by
  simp)

-- Set.image_subset_sups_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_subset_sups_left.h5 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s t : Set α} {b : α},
        @LE.le (Set α) (@Set.instLE α) (@Set.image α α (fun (a : α) => @Max.max α (@SemilatticeSup.toMax α inst) a b) s)
          (@HasSups.sups (Set α) (@Set.hasSups α inst) s t)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)

-- Set.sups_subset_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sups_subset_left.h5 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s t₁ t₂ : Set α},
        @LE.le (Set α) (@Set.instLE α) (@HasSups.sups (Set α) (@Set.hasSups α inst) s t₁)
          (@HasSups.sups (Set α) (@Set.hasSups α inst) s t₂)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False)) (by
  simp)

-- List.map_perm_map_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_perm_map_iff.h5 : ¬∀ {α β : Type} {l l' : List α} {f : α → β}, (List.map f l).Perm (List.map f l') ↔ l.Perm l' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) ([1]) (fun _ => 0 : ℕ → ℕ)) (by
  decide +kernel)

-- List.Perm.flatMap_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.flatMap_left.h5 : ¬∀ {α β : Type} (l : List α) {f g : α → List β}, (List.flatMap f l).Perm (List.flatMap g l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) (fun _ => [] : ℕ → List ℕ) (fun n => [n] : ℕ → List ℕ)) (by
  decide +kernel)

-- List.Perm.insertIdx, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.insertIdx.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} (n : ℕ) (a : α), (l₁.insertIdx n a).Perm (l₂.insertIdx n a) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (0) (0)) (by
  decide +kernel)

-- Finsupp.comapDomain_zero, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finsupp.comapDomain_zero.h5.der.{u_1, u_2, u_5} : ∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : Zero M] (f : α → β),
      @Set.InjOn α β f
        (@Set.preimage α β f
          (@SetLike.coe (Finset β) β (@Finset.instSetLike β)
            (@Finsupp.support β M inst
              (@OfNat.ofNat (@Finsupp β M inst) (nat_lit 0)
                (@Zero.toOfNat0 (@Finsupp β M inst) (@Finsupp.instZero β M inst)))))) := by
  (intros; simp; done)
theorem HypCheckProof.Finsupp.comapDomain_zero.h5.{u_1, u_2, u_5} : ∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : Zero M] (f : α → β),
      @Eq (@Finsupp α M inst)
        (@Finsupp.comapDomain α β M inst f
          (@OfNat.ofNat (@Finsupp β M inst) (nat_lit 0) (@Zero.toOfNat0 (@Finsupp β M inst) (@Finsupp.instZero β M inst)))
          (@HypCheckProof.Finsupp.comapDomain_zero.h5.der α β M inst f))
        (@OfNat.ofNat (@Finsupp α M inst) (nat_lit 0) (@Zero.toOfNat0 (@Finsupp α M inst) (@Finsupp.instZero α M inst))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Finsupp.comapDomain_zero hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Finsupp.comapDomain_zero.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- PosNum.cast_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PosNum.cast_le.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : LinearOrder α] {m n : PosNum},
        Iff
          (@LE.le α
            (@Preorder.toLE α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
            (@castPosNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst)) m)
            (@castPosNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst)) n))
          (@LE.le PosNum PosNum.instLE m n)) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.linearOrder) (PosNum.one.bit1) (PosNum.one)) (by
  decide +kernel)

-- Fin.Embedding.snoc_castSucc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.Embedding.snoc_castSucc.h4 : ¬∀ {α : Type} {n : ℕ} {x : Fin n ↪ α} {a : α} {i : Fin n}, a ∉ Set.range ⇑x := fun hc_h => absurd (@hc_h (ℕ) (1) ({ toFun := fun (a : Fin 1) => 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Fin 1 ↪ ℕ }) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.Embedding.coe_append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.Embedding.coe_append.h5 : ¬∀ {α : Type} {m n : ℕ} {x : Fin m ↪ α} {y : Fin n ↪ α}, Disjoint (Set.range ⇑x) (Set.range ⇑y) := fun hc_h => absurd (@hc_h (ℕ) (1) (1) ({ toFun := fun (a : Fin 1) => 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Fin 1 ↪ ℕ }) ({ toFun := fun (a : Fin 1) => 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Fin 1 ↪ ℕ })) (by
  simp)

-- List.lookupAll_eq_dlookup, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookupAll_eq_dlookup.h5 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (a : α) {l : List (Sigma β)},
        List.lookupAll a l = (List.dlookup a l).toList := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- Nat.Prime.five_le_of_ne_two_of_ne_three, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.five_le_of_ne_two_of_ne_three.h1 : ¬∀ {p : ℕ}, p ≠ 2 → p ≠ 3 → 5 ≤ p := fun hc_h => absurd (@hc_h (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.five_le_of_ne_two_of_ne_three, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.five_le_of_ne_two_of_ne_three.h2 : ¬∀ {p : ℕ}, Nat.Prime p → p ≠ 3 → 5 ≤ p := fun hc_h => absurd (@hc_h (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.five_le_of_ne_two_of_ne_three, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.five_le_of_ne_two_of_ne_three.h3 : ¬∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → 5 ≤ p := fun hc_h => absurd (@hc_h (3) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.not_prime_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_mul.h2 : ¬∀ {a b : ℕ}, b ≠ 1 → ¬Nat.Prime (a * b) := fun hc_h => absurd (@hc_h (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.not_prime_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_mul.h3 : ¬∀ {a b : ℕ}, a ≠ 1 → ¬Nat.Prime (a * b) := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.coprime_primes, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_primes.h2 : ¬∀ {p q : ℕ}, Nat.Prime q → (p.Coprime q ↔ p ≠ q) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.coprime_primes, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_primes.h3 : ¬∀ {p q : ℕ}, Nat.Prime p → (p.Coprime q ↔ p ≠ q) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- List.Vector.mOfFn_pure, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Vector.mOfFn_pure.h2 : Not
      (∀ {m : Type → Type} [inst : Monad m] {α : Type} {n : Nat} (f : Fin n → α),
        @Eq (m (List.Vector α n))
          (@List.Vector.mOfFn m inst α n fun (i : Fin n) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) α (f i))
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List.Vector α n) (@List.Vector.ofFn α n f))) := fun hc_h => absurd (@hc_h (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
      @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.Prime.pow_minFac, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pow_minFac.h2 : ¬∀ {p k : ℕ}, k ≠ 0 → (p ^ k).minFac = p := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.pow_minFac, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pow_minFac.h3 : ¬∀ {p k : ℕ}, Nat.Prime p → (p ^ k).minFac = p := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- List.lookupAll_length_le_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookupAll_length_le_one.h5 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (a : α) {l : List (Sigma β)}, (List.lookupAll a l).length ≤ 1 := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- Nat.primeFactorsList_unique, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactorsList_unique.h2 : ¬∀ {n : ℕ} {l : List ℕ}, (∀ p ∈ l, Nat.Prime p) → l.Perm n.primeFactorsList := fun hc_h => absurd (@hc_h (2) ([]) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactorsList_unique, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactorsList_unique.h3 : ¬∀ {n : ℕ} {l : List ℕ}, l.prod = n → l.Perm n.primeFactorsList := fun hc_h => absurd (@hc_h _ ([0]) rfl) (by
  decide +kernel)

-- Nat.dvd_of_primeFactorsList_subperm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_of_primeFactorsList_subperm.h2 : ¬∀ {a b : ℕ}, a.primeFactorsList.Subperm b.primeFactorsList → a ∣ b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.dvd_of_primeFactorsList_subperm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_of_primeFactorsList_subperm.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → a ∣ b := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Sym.erase_cons_head, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Sym.erase_cons_head.h5.der.{u_1} : ∀ {α : Type u_1} {n : ℕ} [inst : DecidableEq α] (s : Sym α n) (a : α), a ∈ a ::ₛ s := by
  (intros; simp; done)
theorem HypCheckProof.Sym.erase_cons_head.h5.{u_1} : ∀ {α : Type u_1} {n : ℕ} [inst : DecidableEq α] (s : Sym α n) (a : α),
      (a ::ₛ s).erase a (HypCheckProof.Sym.erase_cons_head.h5.der s a) = s := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Sym.erase_cons_head hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Sym.erase_cons_head.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- List.exists_of_kerase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_of_kerase.h5 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {l : List (Sigma β)},
        ∃ (b : β a) (l₁ : List (Sigma β)) (l₂ : List (Sigma β)),
          a ∉ l₁.keys ∧ l = l₁ ++ (⟨a, b⟩ : Sigma β) :: l₂ ∧ List.kerase a l = l₁ ++ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([])) (by
  simp)

-- Nat.primeFactorsList_sublist_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactorsList_sublist_of_dvd.h2 : ¬∀ {n k : ℕ}, k ≠ 0 → n.primeFactorsList.Sublist k.primeFactorsList := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactorsList_sublist_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactorsList_sublist_of_dvd.h3 : ¬∀ {n k : ℕ}, n ∣ k → n.primeFactorsList.Sublist k.primeFactorsList := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactors_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_mul.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactors_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_mul.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactors_prime_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_prime_pow.h2 : ¬∀ {k p : ℕ}, Nat.Prime p → (p ^ k).primeFactors = {p} := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactors_prime_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_prime_pow.h3 : ¬∀ {k p : ℕ}, k ≠ 0 → (p ^ k).primeFactors = {p} := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactors_mono, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_mono.h2 : ¬∀ {m n : ℕ}, n ≠ 0 → m.primeFactors ⊆ n.primeFactors := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactors_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_mono.h3 : ¬∀ {m n : ℕ}, m ∣ n → m.primeFactors ⊆ n.primeFactors := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- ZMod.prime_natCast_not_isUnit_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.prime_natCast_not_isUnit_pow.h2 : Not
      (∀ {p d : Nat},
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d →
          Not
            (@IsUnit
              (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
              (@Semiring.toMonoid
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                (@CommSemiring.toSemiring
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                  (@CommRing.toCommSemiring
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d))
                    (ZMod.commRing
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d)))))
              (@Nat.cast
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                (@AddMonoidWithOne.toNatCast
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                  (@AddGroupWithOne.toAddMonoidWithOne
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d))
                    (@Ring.toAddGroupWithOne
                      (ZMod
                        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                          d))
                      (@CommRing.toRing
                        (ZMod
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p d))
                        (ZMod.commRing
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p d))))))
                p))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- ZMod.prime_natCast_not_isUnit_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.prime_natCast_not_isUnit_pow.h3 : Not
      (∀ {p d : Nat},
        Nat.Prime p →
          Not
            (@IsUnit
              (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
              (@Semiring.toMonoid
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                (@CommSemiring.toSemiring
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                  (@CommRing.toCommSemiring
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d))
                    (ZMod.commRing
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d)))))
              (@Nat.cast
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                (@AddMonoidWithOne.toNatCast
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p d))
                  (@AddGroupWithOne.toAddMonoidWithOne
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        d))
                    (@Ring.toAddGroupWithOne
                      (ZMod
                        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                          d))
                      (@CommRing.toRing
                        (ZMod
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p d))
                        (ZMod.commRing
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p d))))))
                p))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Fintype.sum_eq_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.sum_eq_zero.h5 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : AddCommMonoid M] (f : α → M), ∑ a : α, f a = 0 := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (Nat.instAddCommMonoid) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- ZMod.cast_injective_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.cast_injective_of_le.h3 : Not
      (∀ {m n : Nat} [nzm : @NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) m],
        @Function.Injective (ZMod m) (ZMod n)
          (@ZMod.cast (ZMod n) (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))) m)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) _) (by
  decide +kernel)

-- Nat.digits_def', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_def'.h1 : ¬∀ {b n : ℕ}, 0 < n → b.digits n = n % b :: b.digits (n / b) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_def', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_def'.h3 : ¬∀ {b : ℕ}, 1 < b → ∀ {n : ℕ}, b.digits n = n % b :: b.digits (n / b) := fun hc_h => absurd (@hc_h (2) (by
  decide) (0)) (by
  decide +kernel)

-- Nat.ofDigits_lt_base_pow_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_lt_base_pow_length.h3 : ¬∀ {b : ℕ} {l : List ℕ}, 1 < b → Nat.ofDigits b l < b ^ l.length := fun hc_h => absurd (@hc_h (2) ([2]) (by
  decide)) (by
  decide +kernel)

-- Nat.toDigitsCore_lens_eq_aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toDigitsCore_lens_eq_aux.h5 : ¬∀ (b f n : ℕ) (l1 l2 : List Char), (b.toDigitsCore f n l1).length = (b.toDigitsCore f n l2).length := fun hc_h => absurd (@hc_h (0) (0) (0) ([]) (['a'])) (by
  decide +kernel)

-- Nat.pow_length_le_mul_ofDigits, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_length_le_mul_ofDigits.h2 : ¬∀ {b : ℕ} {l : List ℕ}, l ≠ [] := fun hc_h => absurd (@hc_h (0) ([])) (by
  decide +kernel)

-- Nat.pow_length_le_mul_ofDigits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_length_le_mul_ofDigits.h3 : ¬∀ {b : ℕ} {l : List ℕ}, l ≠ [] → (b + 2) ^ l.length ≤ (b + 2) * Nat.ofDigits (b + 2) l := fun hc_h => absurd (@hc_h (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- Nat.length_digits, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.length_digits.h2 : ¬∀ (b n : ℕ), n ≠ 0 → (b.digits n).length = Nat.log b n + 1 := fun hc_h => absurd (@hc_h (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.length_digits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.length_digits.h3 : ¬∀ (b n : ℕ), 1 < b → (b.digits n).length = Nat.log b n + 1 := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- List.HasPeriod.factor, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.HasPeriod.factor.h5 : ¬∀ {α : Type} {u : List α} {v : List α} {w : List α} {p : ℕ}, v.HasPeriod p := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0, 1]) ([]) (1)) (by
  nofun)

-- NNRat.ext_num_den, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.ext_num_den.h2 : ¬∀ {p q : ℚ≥0}, p.den = q.den → p = q := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.shortlex_cons_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.shortlex_cons_iff.h2 : ¬∀ {α : Type} {r : α → α → Prop} {a : α} {s t : List α}, List.Shortlex r (a :: s) (a :: t) ↔ List.Shortlex r s t := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (0) ([]) ([])) (by
  simp)

-- List.Shortlex.append_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Shortlex.append_right.h5 : ¬∀ {α : Type} {r : α → α → Prop} {s₁ s₂ : List α} (t : List α), List.Shortlex r s₁ (s₂ ++ t) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([]) ([])) (by
  simp)

-- List.Shortlex.append_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Shortlex.append_left.h4 : ¬∀ {α : Type} {r : α → α → Prop} {t₁ t₂ : List α} (s : List α), List.Shortlex r (s ++ t₁) (s ++ t₂) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([]) ([])) (by
  simp)

-- ENat.toNat_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_add.h2 : ¬∀ {m n : ℕ∞}, n ≠ ⊤ → (m + n).toNat = m.toNat + n.toNat := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  decide +kernel)

-- ENat.toNat_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_add.h3 : ¬∀ {m n : ℕ∞}, m ≠ ⊤ → (m + n).toNat = m.toNat + n.toNat := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  decide +kernel)

-- Rat.den_div_eq_of_coprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.den_div_eq_of_coprime.h2 : Not
      (∀ {a b : Int},
        a.natAbs.Coprime b.natAbs →
          @Eq Int
            (@Nat.cast Int instNatCastInt
              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                  (@Int.cast Rat Rat.instIntCast b)).den)
            b) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Rat.den_div_eq_of_coprime, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.den_div_eq_of_coprime.h3 : Not
      (∀ {a b : Int},
        @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) b →
          @Eq Int
            (@Nat.cast Int instNatCastInt
              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                  (@Int.cast Rat Rat.instIntCast b)).den)
            b) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_prod_pow_of_factorization_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_prod_pow_of_factorization_le.h2 : ¬∀ {n : ℕ} {f : ℕ →₀ ℕ}, n.factorization ≤ f → n ∣ f.prod fun (x1 x2 : ℕ) => x1 ^ x2 := fun hc_h => absurd (@hc_h (0) (0) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.dvd_prod_pow_of_factorization_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_prod_pow_of_factorization_le.h3 : ¬∀ {n : ℕ} {f : ℕ →₀ ℕ}, n ≠ 0 → n ∣ f.prod fun (x1 x2 : ℕ) => x1 ^ x2 := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_le_iff_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_le_iff_dvd.h2 : ¬∀ {d n : ℕ}, n ≠ 0 → (d.factorization ≤ n.factorization ↔ d ∣ n) := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_le_iff_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_le_iff_dvd.h3 : ¬∀ {d n : ℕ}, d ≠ 0 → (d.factorization ≤ n.factorization ↔ d ∣ n) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_iff_exists_le_factorization, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_iff_exists_le_factorization.h3 : ¬∀ {n d : ℕ}, d ≠ 0 → (d ∣ n ↔ ∃ f ≤ n.factorization, d = f.prod fun (x1 x2 : ℕ) => x1 ^ x2) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  simp)

-- Nat.factorization_gcd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_gcd.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → (a.gcd b).factorization = a.factorization ⊓ b.factorization := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  norm_num)

-- Nat.factorization_gcd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_gcd.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → (a.gcd b).factorization = a.factorization ⊓ b.factorization := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  norm_num)

-- Set.injOn_union, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.injOn_union.h5 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {f : α → β},
        Set.InjOn f (s₁ ∪ s₂) ↔ Set.InjOn f s₁ ∧ Set.InjOn f s₂ ∧ ∀ x ∈ s₁, ∀ y ∈ s₂, f x ≠ f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Nat.case_strong_induction_on, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.case_strong_induction_on.h3 : ¬∀ {motive : ℕ → Prop} (a : ℕ), motive 0 → motive a := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.exists_eq_pow_mul_and_not_dvd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_eq_pow_mul_and_not_dvd.h1 : ¬∀ {n : ℕ} (p : ℕ), p ≠ 1 → ∃ (e : ℕ) (n' : ℕ), ¬p ∣ n' ∧ n = p ^ e * n' := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  (simp <;> omega))

-- Nat.exists_eq_pow_mul_and_not_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_eq_pow_mul_and_not_dvd.h3 : ¬∀ {n : ℕ}, n ≠ 0 → ∀ (p : ℕ), ∃ (e : ℕ) (n' : ℕ), ¬p ∣ n' ∧ n = p ^ e * n' := fun hc_h => absurd (@hc_h (1) (by
  decide) (1)) (by
  simp)

-- Subsingleton.eq_univ_of_nonempty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subsingleton.eq_univ_of_nonempty.h1 : ¬∀ {α : Type} {s : Set α}, s.Nonempty → s = Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Nat.maxPrimeFac_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPrimeFac_mul.h2 : ¬∀ {m n : ℕ}, n ≠ 0 → (m * n).maxPrimeFac = Max.max m.maxPrimeFac n.maxPrimeFac := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.maxPrimeFac_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPrimeFac_mul.h3 : ¬∀ {m n : ℕ}, m ≠ 0 → (m * n).maxPrimeFac = Max.max m.maxPrimeFac n.maxPrimeFac := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.not_dvd_ordCompl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_dvd_ordCompl.h2 : ¬∀ {n p : ℕ}, n ≠ 0 → ¬p ∣ n / p ^ n.factorization p := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.not_dvd_ordCompl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_dvd_ordCompl.h3 : ¬∀ {n p : ℕ}, Nat.Prime p → ¬p ∣ n / p ^ n.factorization p := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Set.BijOn.subset_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.subset_range.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, t ⊆ Set.range f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- List.map_subperm_map_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_subperm_map_iff.h5 : ¬∀ {α β : Type} {l₁ l₂ : List α} {f : α → β}, (List.map f l₁).Subperm (List.map f l₂) ↔ l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) ([1]) (fun _ => 0 : ℕ → ℕ)) (by
  decide +kernel)

-- Set.MapsTo.subset_preimage, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.subset_preimage.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, s ⊆ f ⁻¹' t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Nat.coprime_ordCompl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_ordCompl.h2 : ¬∀ {n p : ℕ}, n ≠ 0 → p.Coprime (n / p ^ n.factorization p) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.coprime_ordCompl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_ordCompl.h3 : ¬∀ {n p : ℕ}, Nat.Prime p → p.Coprime (n / p ^ n.factorization p) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.nth_mem_of_lt_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_mem_of_lt_card.h3 : ¬∀ {p : ℕ → Prop} {n : ℕ}, (Set.ofPred p).Finite → p (Nat.nth p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0) (by
  simp)) (by
  decide +kernel)

-- Nat.nth_eq_orderEmbOfFin, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_eq_orderEmbOfFin.h3 : ¬∀ {p : ℕ → Prop} (hf : (Set.ofPred p).Finite) {n : ℕ}, n < hf.toFinset.card := fun hc_h => absurd (fun hc_k0 => @hc_h (fun n => n = 0 : ℕ → Prop) hc_k0 (1)) (by
  simp)

-- Nat.lt_card_toFinset_of_nth_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_card_toFinset_of_nth_ne_zero.h2 : ¬∀ {p : ℕ → Prop} {n : ℕ} (hf : (Set.ofPred p).Finite), n < hf.toFinset.card := fun hc_h => absurd (fun hc_k0 => @hc_h (fun n => n = 0 : ℕ → Prop) (1) hc_k0) (by
  simp)

-- Nat.Coprime.eq_of_mul_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.eq_of_mul_eq_zero.h2 : ¬∀ {m n : ℕ}, m * n = 0 → m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 := fun hc_h => absurd (@hc_h (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.Coprime.eq_of_mul_eq_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.eq_of_mul_eq_zero.h3 : ¬∀ {m n : ℕ}, m.Coprime n → m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- cmpUsing_eq_gt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.cmpUsing_eq_gt.h3 : ¬∀ {α : Type} {lt : α → α → Prop} [inst : DecidableRel lt] (a b : α), cmpUsing lt a b = Ordering.gt ↔ lt b a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (Nat.decLe) (0) (0)) (by
  decide +kernel)

-- Ordnode.Sized.eq_node', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.eq_node'.h5 : ¬∀ {α : Type} {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α}, Ordnode.node s l x r = l.node' x r := fun hc_h => absurd (@hc_h (ℕ) (0) (Ordnode.nil) (0) (Ordnode.nil)) (by
  simp)

-- Set.LeftInvOn.image_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.LeftInvOn.image_image.h5 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {f' : β → α}, f' '' f '' s = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Ordnode.Bounded.to_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.to_lt.h5 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {x y : α}, x < y := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (0)) (by
  decide +kernel)

-- List.Sublist.flatMap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.flatMap.h4 : ¬∀ {α β : Type} {l₁ l₂ : List α} (f : α → List β), (List.flatMap f l₁).Sublist (List.flatMap f l₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) ([]) (fun n => [n] : ℕ → List ℕ)) (by
  decide +kernel)

-- Codisjoint.preimage, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Codisjoint.preimage.h5 : ¬∀ {α β : Type} (f : α → β) {s t : Set β}, Codisjoint (f ⁻¹' s) (f ⁻¹' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.Sublist.flatMap_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.flatMap_right.h5 : ¬∀ {α β : Type} (l : List α) {f g : α → List β}, (List.flatMap f l).Sublist (List.flatMap g l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) (fun n => [n] : ℕ → List ℕ) (fun _ => [] : ℕ → List ℕ)) (by
  decide +kernel)

-- List.head_flatten_eq_head_head, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head_flatten_eq_head_head.h2 : ¬∀ {α : Type} {l : List (List α)}, l.flatten ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- List.head_flatten_eq_head_head, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head_flatten_eq_head_head.h3 : ¬∀ {α : Type} {l : List (List α)} (hl : l.flatten ≠ []),
        l.head
            ((fun {α : Type} {l : List (List α)} (hl : l.flatten ≠ []) =>
                (fun {α : Type} {l : List (List α)} (hl : l.flatten ≠ []) =>
                    Classical.byContradiction
                      (Lean.Grind.intro_with_eq (¬¬l = []) (l = []) False (Lean.Grind.not_not (l = [])) fun (h : l = []) =>
                        id
                          (Eq.mp
                            (Eq.trans
                              (Eq.symm
                                (eq_true
                                  (Eq.trans (congrArg List.flatten h)
                                    (Eq.mp (Eq.refl ([].flatten = [])) List.flatten_nil))))
                              (eq_false hl))
                            True.intro)))
                  hl)
              hl) ≠
          [] := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([[], [0]]) hc_k0) (by
  decide +kernel)

-- Sym2.exact, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.exact.h5 : ¬∀ {α : Type} {a b c d : α}, Sym2.Rel α (a, b) (c, d) := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (0) (1)) (by
  decide +kernel)

-- List.Lex.isOrderConnected, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.isOrderConnected.h3 : ¬∀ {α : Type} (r : α → α → Prop) [inst : IsOrderConnected α r], IsOrderConnected (List α) (List.Lex r) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) (@IsOrderConnected.mk (Bool) (fun (x x_1 : Bool) => False) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.conn ([Bool.false] : List Bool) ([Bool.true] : List Bool) ([Bool.false, Bool.true] : List Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Lex.append_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.append_left.h4 : ¬∀ {α : Type} (R : α → α → Prop) {t₁ t₂ : List α} (s : List α), List.Lex R (s ++ t₁) (s ++ t₂) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([]) ([])) (by
  decide +kernel)

-- Nat.ModEq.add_iff_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_iff_left.h5 : ¬∀ {n a b c d : ℕ}, a + c ≡ b + d [MOD n] ↔ c ≡ d [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0)) (by
  decide +kernel)

-- Set.SurjOn.exists_subset_injOn_image_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.exists_subset_injOn_image_eq.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, ∃ u ⊆ s, Set.InjOn f u ∧ f '' u = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Nat.pow_sub_lt_descFactorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_sub_lt_descFactorial.h2 : ¬∀ {n k : ℕ}, k ≤ n → (n + 1 - k) ^ k < n.descFactorial k := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.pow_sub_lt_descFactorial, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_sub_lt_descFactorial.h3 : ¬∀ {n k : ℕ}, 2 ≤ k → (n + 1 - k) ^ k < n.descFactorial k := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- pow_eq_one_iff_of_coprime, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.pow_eq_one_iff_of_coprime.h5 : ¬∀ {M : Type} [inst : Monoid M] {a : M} {m n : ℕ}, a ^ m = 1 ∧ a ^ n = 1 ↔ a = 1 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMonoid) (0) (0) (0)) (by
  decide +kernel)

-- Set.Countable.exists_surjective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Countable.exists_surjective.h2 : ¬∀ {α : Type} {s : Set α}, s.Countable → ∃ (f : ℕ → ↑s), Function.Surjective f := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.image2_right_identity, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_right_identity.h4 : ¬∀ {α β : Type} {f : α → β → α} {b : β} (s : Set α), Set.image2 f s {b} = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a + b : ℕ → ℕ → ℕ) (1) ({n : ℕ | n = 0})) (by
  simp)

-- Prod.Lex.refl_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.Lex.refl_left.h4 : ¬∀ {α β : Type} (r : α → α → Prop) (s : β → β → Prop) (x : α × β), Prod.Lex r s x x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) ((0, 0))) (by
  decide +kernel)

-- List.IsChain.rel_head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_head.h5 : ¬∀ {α : Type} {R : α → α → Prop} {a b : α} {l : List α}, R a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) ([])) (by
  decide +kernel)

-- Set.image2_left_identity, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_left_identity.h4 : ¬∀ {α β : Type} {f : α → β → β} {a : α} (t : Set β), Set.image2 f {a} t = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (1) ({n : ℕ | n = 0})) (by
  simp)

-- uzpow_coe_nat, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.uzpow_coe_nat.h5 : Not
      (∀ {R : Type} [inst : CommSemiring R]
        [inst :
          @Module R (Additive (@Units Int Int.instMonoid)) (@CommSemiring.toSemiring R inst)
            (@Additive.addCommMonoid (@Units Int Int.instMonoid)
              (@CommGroup.toCommMonoid (@Units Int Int.instMonoid) (@Units.instCommGroupUnits Int Int.instCommMonoid)))]
        (s : @Units Int Int.instMonoid) (n : Nat), n.AtLeastTwo) := fun hc_h => absurd (@hc_h (Nat) (Nat.instCommSemiring) (@AddCommMonoid.toNatModule (Additive (@Units Int Int.instMonoid))
      (@Additive.addCommMonoid (@Units Int Int.instMonoid)
        (@CommGroup.toCommMonoid (@Units Int Int.instMonoid) (@Units.instCommGroupUnits Int Int.instCommMonoid)))) (@Units.mk Int Int.instMonoid (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@of_decide_eq_true
        (@Eq Int
          (@HMul.hMul Int Int Int
            (@instHMul Int (@MulOne.toMul Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1)
            (@One.toOfNat1 Int (@MulOne.toOne Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))))
        ((@HMul.hMul Int Int Int
              (@instHMul Int (@MulOne.toMul Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).instDecidableEq
          (@OfNat.ofNat Int (nat_lit 1)
            (@One.toOfNat1 Int (@MulOne.toOne Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Eq Int
                (@HMul.hMul Int Int Int
                  (@instHMul Int (@MulOne.toMul Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))
                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@OfNat.ofNat Int (nat_lit 1)
                  (@One.toOfNat1 Int
                    (@MulOne.toOne Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))))
              ((@HMul.hMul Int Int Int
                    (@instHMul Int
                      (@MulOne.toMul Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).instDecidableEq
                (@OfNat.ofNat Int (nat_lit 1)
                  (@One.toOfNat1 Int
                    (@MulOne.toOne Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (@Eq Int
          (@HMul.hMul Int Int Int
            (@instHMul Int (@MulOne.toMul Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1)
            (@One.toOfNat1 Int (@MulOne.toOne Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))))
        ((@HMul.hMul Int Int Int
              (@instHMul Int (@MulOne.toMul Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).instDecidableEq
          (@OfNat.ofNat Int (nat_lit 1)
            (@One.toOfNat1 Int (@MulOne.toOne Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Eq Int
                (@HMul.hMul Int Int Int
                  (@instHMul Int (@MulOne.toMul Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))
                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@OfNat.ofNat Int (nat_lit 1)
                  (@One.toOfNat1 Int
                    (@MulOne.toOne Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))))
              ((@HMul.hMul Int Int Int
                    (@instHMul Int
                      (@MulOne.toMul Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid))))
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).instDecidableEq
                (@OfNat.ofNat Int (nat_lit 1)
                  (@One.toOfNat1 Int
                    (@MulOne.toOne Int (@MulOneClass.toMulOne Int (@Monoid.toMulOneClass Int Int.instMonoid)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.image_congr', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_congr'.h5 : ¬∀ {α β : Type} {f g : α → β} {s : Set α}, f '' s = g '' s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- List.IsRotated.dropLast_tail, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.dropLast_tail.h2 : ¬∀ {α : Type} {L : List α}, L ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- List.IsRotated.dropLast_tail, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.dropLast_tail.h3 : ¬∀ {α : Type} {L : List α}, L ≠ [] → L.dropLast ~r L.tail := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_or_eq_of_totient_eq_totient, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_or_eq_of_totient_eq_totient.h2 : ¬∀ {a b : ℕ}, a.totient = b.totient → a = b ∨ 2 * a = b := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_or_eq_of_totient_eq_totient, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_or_eq_of_totient_eq_totient.h3 : ¬∀ {a b : ℕ}, a ∣ b → a = b ∨ 2 * a = b := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.totient_mul_of_prime_of_not_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_mul_of_prime_of_not_dvd.h2 : ¬∀ {p n : ℕ}, ¬p ∣ n → (p * n).totient = (p - 1) * n.totient := fun hc_h => absurd (@hc_h (4) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.totient_mul_of_prime_of_not_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_mul_of_prime_of_not_dvd.h3 : ¬∀ {p n : ℕ}, Nat.Prime p → (p * n).totient = (p - 1) * n.totient := fun hc_h => absurd (@hc_h (2) (2) (by
  decide)) (by
  decide +kernel)

-- List.le_maximum_of_mem', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_maximum_of_mem'.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a : α}, ↑a ≤ l.maximum := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) (0)) (by
  decide +kernel)

-- Part.map_get, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.map_get.h4 : ¬∀ {α β : Type} (f : α → β) (o : Part α), o.Dom := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (⊥)) (by
  nofun)

-- Finset.orderEmbOfFin_compl_singleton_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.orderEmbOfFin_compl_singleton_apply.h3 : Not
      (∀ {n : Nat}
        {i :
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
        {k : Nat} (j : Fin k),
        @Eq Nat
          (@Finset.card
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Compl.compl
              (Finset
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@BooleanAlgebra.toCompl
                (Finset
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Finset.booleanAlgebra
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin.fintype
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@Singleton.singleton
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Finset
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Finset.instSingleton
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                i)))
          k) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Set.inter_insert_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_insert_of_notMem.h4 : ¬∀ {α : Type} {s t : Set α} {a : α}, s ∩ Insert.insert a t = s ∩ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (0)) (by
  simp)

-- Set.insert_inter_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.insert_inter_of_notMem.h4 : ¬∀ {α : Type} {s t : Set α} {a : α}, Insert.insert a s ∩ t = s ∩ t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- List.insertIdx_eraseIdx_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insertIdx_eraseIdx_self.h3 : ¬∀ {α : Type} {l : List α} {n : ℕ} (a : α), (l.eraseIdx n).insertIdx n a = l.set n a := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0)) (by
  decide +kernel)

-- Int.ModEq.sub_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.sub_left.h4 : ¬∀ {n a b : ℤ} (c : ℤ), c - a ≡ c - b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Int.ModEq.mul_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_left.h4 : ¬∀ {n a b : ℤ} (c : ℤ), c * a ≡ c * b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- Int.ModEq.add_right_cancel', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add_right_cancel'.h4 : ¬∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Int.ModEq.of_mul_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.of_mul_right.h4 : ¬∀ {n a b : ℤ} (m : ℤ), a ≡ b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Int.ModEq.add_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add_left.h4 : ¬∀ {n a b : ℤ} (c : ℤ), c + a ≡ c + b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Set.sInter_prod, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sInter_prod.h3 : ¬∀ {α β : Type} {S : Set (Set α)} (t : Set β), ⋂₀ S ×ˢ t = ⋂ s ∈ S, s ×ˢ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (∅) ({n : ℕ | n = 0})) (by
  simp)

-- Int.ModEq.mul_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_right.h4 : ¬∀ {n a b : ℤ} (c : ℤ), a * c ≡ b * c [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- Int.ModEq.mul_left', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_left'.h4 : ¬∀ {n a b c : ℤ}, c * a ≡ c * b [ZMOD c * n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- Set.mem_of_mem_inter_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_mem_inter_right.h4 : ¬∀ {α : Type} {x : α} {a : Set α} {b : Set α}, x ∈ b := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  decide +kernel)

-- Set.iUnion_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iUnion_congr.h4 : ¬∀ {α ι : Type} {s t : ι → Set α}, ⋃ (i : ι), s i = ⋃ (i : ι), t i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {x : ℕ | False})) (by
  simp)

-- nsmul_zmod_val_inv_nsmul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.nsmul_zmod_val_inv_nsmul.h3 : Not
      (∀ {α : Type} [inst : AddGroup α] {n : Nat} (a : α),
        @Eq α
          (@HSMul.hSMul Nat α α
            (@instHSMul Nat α
              (@NSMul.toSMul α (@AddMonoid.toNSMul α (@SubNegMonoid.toAddMonoid α (@AddGroup.toSubNegMonoid α inst)))))
            n
            (@HSMul.hSMul Nat α α
              (@instHSMul Nat α
                (@NSMul.toSMul α (@AddMonoid.toNSMul α (@SubNegMonoid.toAddMonoid α (@AddGroup.toSubNegMonoid α inst)))))
              (@ZMod.val (Nat.card α)
                (@Inv.inv (ZMod (Nat.card α)) (ZMod.instInv (Nat.card α))
                  (@Nat.cast (ZMod (Nat.card α))
                    (@AddMonoidWithOne.toNatCast (ZMod (Nat.card α))
                      (@AddGroupWithOne.toAddMonoidWithOne (ZMod (Nat.card α))
                        (@Ring.toAddGroupWithOne (ZMod (Nat.card α))
                          (@CommRing.toRing (ZMod (Nat.card α)) (ZMod.commRing (Nat.card α))))))
                    n)))
              a))
          a) := fun hc_h => absurd (@hc_h (Bool) (@AddGroupWithOne.toAddGroup Bool (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Bool.true)) (by
  decide +kernel)

-- Set.mem_iInter_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_iInter_of_mem.h4 : ¬∀ {α ι : Type} {s : ι → Set α} {a : α}, a ∈ ⋂ (i : ι), s i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (1)) (by
  simp)

-- List.foldr_min_of_ne_nil, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldr_min_of_ne_nil.h4 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] {l : List α}, ↑(List.foldr Min.min ⊤ l) = l.minimum := fun hc_h => absurd (@hc_h (Bool) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ([])) (by
  decide +kernel)

-- List.maximum_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maximum_mono.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l₁ l₂ : List α}, l₁.maximum ≤ l₂.maximum := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([0]) ([])) (by
  decide +kernel)

-- Set.subset_iInter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_iInter.h4 : ¬∀ {β ι : Type} {t : Set β} {s : ι → Set β}, t ⊆ ⋂ (i : ι), s i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {x : ℕ | False})) (by
  simp)

-- List.foldr_max_of_ne_nil, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldr_max_of_ne_nil.h4 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] {l : List α}, ↑(List.foldr Max.max ⊥ l) = l.maximum := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (Nat.instOrderBot) ([])) (by
  decide +kernel)

-- Multiset.powersetCardAux_perm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.powersetCardAux_perm.h4 : ¬∀ {α : Type} {n : ℕ} {l₁ l₂ : List α}, (Multiset.powersetCardAux n l₁).Perm (Multiset.powersetCardAux n l₂) := fun hc_h => absurd (@hc_h (ℕ) (1) ([]) ([0])) (by
  decide +kernel)

-- Set.iInter_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iInter_mono.h4 : ¬∀ {α ι : Type} {s t : ι → Set α}, ⋂ (i : ι), s i ⊆ ⋂ (i : ι), t i := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : ℕ) => {b : Bool | b = Bool.true}) (fun (a : ℕ) => {b : Bool | b = Bool.false})) (by
  simp)

-- Set.union_subset_union_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_subset_union_left.h4 : ¬∀ {α : Type} {s₁ s₂ : Set α} (t : Set α), s₁ ∪ t ⊆ s₂ ∪ t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true})) (by
  simp)

-- mem_permsOfList_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mem_permsOfList_of_mem.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {l : List α} {f : Equiv.Perm α},
        @Membership.mem (Equiv.Perm α) (List (Equiv.Perm α)) (@List.instMembership (Equiv.Perm α)) (@permsOfList α inst l)
          f) := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (@List.nil Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
      (@of_decide_eq_true (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
        (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
        (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Set.sep_eq_inter_sep, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sep_eq_inter_sep.h4 : ¬∀ {α : Type} {s t : Set α} {p : α → Prop}, {x : α | x ∈ s ∧ p x} = s ∩ {x : α | x ∈ t ∧ p x} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun n => n = 0 : ℕ → Prop)) (by
  simp)

-- Set.MapsTo.iterate, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.iterate.h3 : ¬∀ {α : Type} {f : α → α} {s : Set α} (n : ℕ), Set.MapsTo f^[n] s s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Finset.noncommProd_empty, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.noncommProd_empty.h4.der.{u_3, u_4} : ∀ {α : Type u_3} {β : Type u_4} [inst : Monoid β] (f : α → β),
      @Set.Pairwise α
        (@SetLike.coe (Finset α) α (@Finset.instSetLike α)
          (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α)))
        (@Function.onFun α β Prop (@Commute β (@MulOne.toMul β (@MulOneClass.toMulOne β (@Monoid.toMulOneClass β inst)))) f) := by
  (intros; simp; done)
theorem HypCheckProof.Finset.noncommProd_empty.h4.{u_3, u_4} : ∀ {α : Type u_3} {β : Type u_4} [inst : Monoid β] (f : α → β),
      @Eq β
        (@Finset.noncommProd α β inst (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α)) f
          (@HypCheckProof.Finset.noncommProd_empty.h4.der α β inst f))
        (@OfNat.ofNat β (nat_lit 1)
          (@One.toOfNat1 β (@MulOne.toOne β (@MulOneClass.toMulOne β (@Monoid.toMulOneClass β inst))))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Finset.noncommProd_empty hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Finset.noncommProd_empty.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Nat.filter_Ico_card_eq_of_periodic, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.filter_Ico_card_eq_of_periodic.h4 : ¬∀ (n a : ℕ) (p : ℕ → Prop) [inst : DecidablePred p], (Finset.filter p (Finset.Ico n (n + a))).card = Nat.count p a := fun hc_h => absurd (@hc_h (1) (1) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0)) (by
  decide +kernel)

-- exists_lt_mem_inter_of_not_pairwise_disjoint, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.exists_lt_mem_inter_of_not_pairwise_disjoint.h4 : ¬∀ {α ι : Type} [inst : LinearOrder ι] {f : ι → Set α}, ∃ (i : ι) (j : ι), i < j ∧ ∃ (x : α), x ∈ f i ∩ f j := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun (a : ℕ) => {x : ℕ | False})) (by
  simp)

-- Set.subset_of_image_val_subset_image_val, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_of_image_val_subset_image_val.h4 : ¬∀ {α : Type} {A : Set α} {D E : Set ↑A}, D ⊆ E := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (⊤) (∅)) (by
  norm_num)

-- Finset.singleton_disjiUnion, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.singleton_disjiUnion.h4.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {t : α → Finset β} (a : α),
      @Set.PairwiseDisjoint (Finset β) α (@Finset.instPartialOrder β) (@Finset.instOrderBot β)
        (@SetLike.coe (Finset α) α (@Finset.instSetLike α) (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a))
        t := by
  (intros; simp; done)
theorem HypCheckProof.Finset.singleton_disjiUnion.h4.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {t : α → Finset β} (a : α),
      @Eq (Finset β)
        (@Finset.disjiUnion α β (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a) t
          (@HypCheckProof.Finset.singleton_disjiUnion.h4.der α β t a))
        (t a) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Finset.singleton_disjiUnion hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Finset.singleton_disjiUnion.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- List.count_lt_length_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_lt_length_iff.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α} {a : α}, List.count a l < l.length ↔ ∃ b ∈ l, b ≠ a := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([0]) (1)) (by
  decide +kernel)

-- Set.subset_symmDiff_union_symmDiff_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_symmDiff_union_symmDiff_left.h4 : ¬∀ {α : Type} {s t u : Set α}, u ⊆ symmDiff s u ∪ symmDiff t u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n % 2 = 0})) (by
  simp)

-- Set.subset_symmDiff_union_symmDiff_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_symmDiff_union_symmDiff_right.h4 : ¬∀ {α : Type} {s t u : Set α}, s ⊆ symmDiff s t ∪ symmDiff s u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n % 2 = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.nodup_map_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_map_iff.h4 : ¬∀ {α β : Type} {f : α → β} {l : List α}, (List.map f l).Nodup ↔ l.Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- Subtype.coind_injective_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coind_injective_iff.h4 : ¬∀ {α β : Type} {f : α → β} {p : β → Prop} (a : α), p (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop)) (by
  simp)

-- List.Nodup.get_inj_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.get_inj_iff.h2 : ¬∀ {α : Type} {l : List α} {i j : Fin l.length}, l.get i = l.get j ↔ i = j := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (0) (1)) (by
  decide +kernel)

-- Finsupp.single_left_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.single_left_injective.h4 : ¬∀ {α M : Type} [inst : Zero M] {b : M}, Function.Injective fun (a : α) => fun₀ | a => b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0)) (by
  simp)

-- Set.range_quot_lift, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.range_quot_lift.h4 : ¬∀ {α ι : Type} {f : ι → α} {r : ι → ι → Prop} (x y : ι), r x y → f x = f y := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ _ => True : Bool → Bool → Prop)) (by
  decide +kernel)

-- Set.preimage_eq_empty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.preimage_eq_empty.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set β}, f ⁻¹' s = ∅ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Fin.cast_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cast_inj.h2 : ¬∀ {n m : ℕ} {a b : Fin n}, n = m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Vector.pmap_nil, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.Vector.pmap_nil.h4.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β), ∀ x ∈ List.Vector.nil.toList, p x := by
  (intros; trivial)
theorem HypCheckProof.List.Vector.pmap_nil.h4.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β),
      List.Vector.pmap f List.Vector.nil (HypCheckProof.List.Vector.pmap_nil.h4.der f) = List.Vector.nil := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @List.Vector.pmap_nil hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.List.Vector.pmap_nil.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Nat.findGreatest_mono_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_mono_right.h4 : ¬∀ (P : ℕ → Prop) [inst : DecidablePred P] {m n : ℕ}, Nat.findGreatest P m ≤ Nat.findGreatest P n := fun hc_h => absurd (@hc_h (fun n => n % 2 = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (2) (0)) (by
  decide +kernel)

-- Sym.replicate_right_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.replicate_right_inj.h4 : ¬∀ {α : Type} {a b : α} {n : ℕ}, Sym.replicate n a = Sym.replicate n b ↔ a = b := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0)) (by
  decide +kernel)

-- Sym.map_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.map_injective.h3 : Not (∀ {α β : Type} {f : α → β} (n : Nat), @Function.Injective (Sym α n) (Sym β n) (@Sym.map α β n f)) := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ => 0 : Bool → Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Subtype.restrict_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.restrict_injective.h4 : ¬∀ {α β : Type} {f : α → β} (p : α → Prop), Function.Injective (Subtype.restrict p f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) (fun _ => True : Bool → Prop)) (by
  decide +kernel)

-- List.getI_eq_default, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getI_eq_default.h4 : ¬∀ {α : Type} (l : List α) [inst : Inhabited α] {n : ℕ}, l.getI n = Inhabited.default := fun hc_h => absurd (@hc_h (ℕ) ([1]) (instInhabitedNat) (0)) (by
  decide +kernel)

-- List.getI_eq_getElem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getI_eq_getElem.h4 : ¬∀ {α : Type} (l : List α) [inst : Inhabited α] {n : ℕ}, n < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (instInhabitedNat) (0)) (by
  decide +kernel)

-- Set.inter_subset_inter_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_subset_inter_right.h4 : ¬∀ {α : Type} {s t : Set α} (u : Set α), u ∩ s ⊆ u ∩ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Matrix.cons_val_zero', hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Matrix.cons_val_zero'.h2.der.{u} : ∀ {α : Type u} {m : ℕ} (x : α) (u : Fin m → α), 0 < m.succ := by
  (intros; simp; done)
theorem HypCheckProof.Matrix.cons_val_zero'.h2.{u} : ∀ {α : Type u} {m : ℕ} (x : α) (u : Fin m → α),
      Matrix.vecCons x u (⟨0, HypCheckProof.Matrix.cons_val_zero'.h2.der x u⟩ : Fin m.succ) = x := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Matrix.cons_val_zero' hc_x0 hc_x1 (@HypCheckProof.Matrix.cons_val_zero'.h2.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x2 hc_x3

-- Matrix.vecHead_vecAlt1, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.vecHead_vecAlt1.h3 : ¬∀ {α : Type} {m n : ℕ} (v : Fin (m + 2) → α), m + 2 = n + 1 + (n + 1) := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (fun (a : Fin (0 + 2)) => 0)) (by
  decide +kernel)

-- Nat.cast_sub, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_sub.h4 : Not
      (∀ {R : Type} [inst : AddGroupWithOne R] {m n : Nat},
        @Eq R
          (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst))
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n m))
          (@HSub.hSub R R R
            (@instHSub R (@SubNegMonoid.toSub R (@AddGroup.toSubNegMonoid R (@AddGroupWithOne.toAddGroup R inst))))
            (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst)) n)
            (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst)) m))) := fun hc_h => absurd (@hc_h (Bool) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Part.left_dom_of_sdiff_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.left_dom_of_sdiff_dom.h4 : ¬∀ {α : Type} [inst : SDiff α] {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (Bool) (Bool.instBooleanAlgebra.toSDiff) (⊥) (0)) (by
  nofun)

-- Part.add_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.add_get_eq.h4 : ¬∀ {α : Type} [inst : Add α] (a b : Part α), (a + b).Dom := fun hc_h => absurd (@hc_h (ℕ) (instAddNat) (0) (⊥)) (by
  nofun)

-- Part.right_dom_of_div_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_div_dom.h4 : ¬∀ {α : Type} [inst : Div α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (ℕ) (Nat.instDiv) (0) (⊥)) (by
  nofun)

-- Part.append_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.append_get_eq.h4 : ¬∀ {α : Type} [inst : Append α] (a b : Part α), (a ++ b).Dom := fun hc_h => absurd (@hc_h (Lean.MessageData) (Lean.MessageData.instAppend) (⊥) (⊥)) (by
  nofun)

-- Part.left_dom_of_union_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.left_dom_of_union_dom.h4 : ¬∀ {α : Type} [inst : Union α] {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (Lean.NameSet) (Lean.NameSet.instUnion_batteries) (⊥) (⊥)) (by
  nofun)

-- Part.Dom.of_bind, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.Dom.of_bind.h4 : ¬∀ {α β : Type} {f : α → Part β} {a : Part α}, a.Dom := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => 0) (⊥)) (by
  nofun)

-- Part.right_dom_of_mod_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_mod_dom.h4 : ¬∀ {α : Type} [inst : Mod α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMod) (0) (⊥)) (by
  nofun)

-- List.ofFn_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ofFn_congr.h3 : ¬∀ {α : Type} {m n : ℕ} (f : Fin m → α), m = n := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- Part.right_dom_of_union_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_union_dom.h4 : ¬∀ {α : Type} [inst : Union α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (Lean.NameSet) (Lean.NameSet.instUnion_batteries) (⊥) (⊥)) (by
  nofun)

-- Part.right_dom_of_append_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_append_dom.h4 : ¬∀ {α : Type} [inst : Append α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (Lean.MessageData) (Lean.MessageData.instAppend) (⊥) (⊥)) (by
  nofun)

-- Part.sdiff_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.sdiff_get_eq.h4 : ¬∀ {α : Type} [inst : SDiff α] (a b : Part α), (a \ b).Dom := fun hc_h => absurd (@hc_h (Bool) (Bool.instBooleanAlgebra.toSDiff) (0) (⊥)) (by
  nofun)

-- Part.mod_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mod_get_eq.h4 : ¬∀ {α : Type} [inst : Mod α] (a b : Part α), (a % b).Dom := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMod) (0) (⊥)) (by
  nofun)

-- Part.right_dom_of_add_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_add_dom.h4 : ¬∀ {α : Type} [inst : Add α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (ℕ) (instAddNat) (0) (⊥)) (by
  nofun)

-- Part.left_dom_of_append_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.left_dom_of_append_dom.h4 : ¬∀ {α : Type} [inst : Append α] {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (Lean.MessageData) (Lean.MessageData.instAppend) (⊥) (⊥)) (by
  nofun)

-- Multiset.eq_of_mem_replicate, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_of_mem_replicate.h4 : ¬∀ {α : Type} {a b : α} {n : ℕ}, b = a := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0)) (by
  decide +kernel)

-- Multiset.replicate_right_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.replicate_right_inj.h4 : ¬∀ {α : Type} {a b : α} {n : ℕ}, Multiset.replicate n a = Multiset.replicate n b ↔ a = b := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0)) (by
  decide +kernel)

-- Multiset.replicate_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.replicate_mono.h4 : ¬∀ {α : Type} (a : α) {k n : ℕ}, Multiset.replicate k a ≤ Multiset.replicate n a := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0)) (by
  decide +kernel)

-- List.Pairwise.insertionSort_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.insertionSort_eq.h4 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] {l : List α}, List.insertionSort r l = l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([1, 0])) (by
  decide +kernel)

-- Multiset.foldr_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldr_zero.h3 : ¬∀ {α β : Type} (f : α → β → β) (b : β), LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.ModEq.mul_right', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_right'.h4 : ¬∀ {n a b : ℕ} (c : ℕ), a * c ≡ b * c [MOD n * c] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- Nat.ModEq.add_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_left.h4 : ¬∀ {n a b : ℕ} (c : ℕ), c + a ≡ c + b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Nat.ModEq.add_right_cancel', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_right_cancel'.h4 : ¬∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Set.Nonempty.of_image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_image.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({x : ℕ | False})) (by
  simp)

-- Nat.ModEq.mul_right_cancel_iff', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_right_cancel_iff'.h4 : ¬∀ {a b c m : ℕ}, a * c ≡ b * c [MOD m * c] ↔ a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (1) (0) (0)) (by
  decide +kernel)

-- Nat.ModEq.mul_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_right.h4 : ¬∀ {n a b : ℕ} (c : ℕ), a * c ≡ b * c [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- List.Pairwise.pwFilter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.pwFilter.h4 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] {l : List α}, List.pwFilter R l = l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([1, 0])) (by
  decide +kernel)

-- List.SortedLE.monotone, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.monotone.h4 : ¬∀ {α : Type} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, Monotone f := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (2) (fun (a : Fin 2) => if a = (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) then 1 else 0)) (by
  decide +kernel)

-- Set.Nonempty.of_sups_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_sups_left.h4 : ¬∀ {α : Type} [inst : SemilatticeSup α] {s : Set α} {t : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeSup) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.Nonempty.of_infs_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_infs_right.h4 : ¬∀ {α : Type} [inst : SemilatticeInf α] {s : Set α} {t : Set α}, t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeInf) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.Nonempty.of_infs_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_infs_left.h4 : ¬∀ {α : Type} [inst : SemilatticeInf α] {s : Set α} {t : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeInf) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.Nonempty.of_sups_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_sups_right.h4 : ¬∀ {α : Type} [inst : SemilatticeSup α] {s : Set α} {t : Set α}, t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeSup) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.InjOn.ncard_image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.ncard_image.h4 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, (f '' s).ncard = s.ncard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | True}) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- List.SortedGT.strictAnti, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.strictAnti.h4 : ¬∀ {α : Type} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, StrictAnti f := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (2) (fun (a : Fin 2) => 0)) (by
  decide +kernel)

-- Disjoint.inter_right', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.inter_right'.h4 : ¬∀ {α : Type} {s t : Set α} (u : Set α), Disjoint s (u ∩ t) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.Disjoint.inter_eq_nil, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Disjoint.inter_eq_nil.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : DecidableEq α], l₁ ∩ l₂ = [] := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0]) (instDecidableEqNat)) (by
  decide +kernel)

-- PosNum.one_le_cast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PosNum.one_le_cast.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : PartialOrder α] (n : PosNum),
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α inst_1))
          (@OfNat.ofNat α (nat_lit 1)
            (@One.toOfNat1 α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))))
          (@castPosNum α
            (@AddMonoidWithOne.toOne α
              (@AddCommMonoidWithOne.toAddMonoidWithOne α
                (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
            (@Distrib.toAdd α (@instDistribOfSemiring α inst)) n)) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.instPartialOrder) (PosNum.one.bit0)) (by
  decide +kernel)

-- PosNum.cast_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PosNum.cast_pos.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : PartialOrder α] (n : PosNum),
        @LT.lt α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))
          (@OfNat.ofNat α (nat_lit 0) (@Zero.toOfNat0 α (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α inst))))
          (@castPosNum α
            (@AddMonoidWithOne.toOne α
              (@AddCommMonoidWithOne.toAddMonoidWithOne α
                (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
            (@Distrib.toAdd α (@instDistribOfSemiring α inst)) n)) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.instPartialOrder) (PosNum.one.bit0)) (by
  decide +kernel)

-- Set.InjOn.encard_image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.encard_image.h4 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, (f '' s).encard = s.encard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | True}) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- List.getEquivOfForallCountEqOne_symm_apply_val, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getEquivOfForallCountEqOne_symm_apply_val.h3 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (a x : α), List.count x l = 1 := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  simp)

-- List.Nodup.getEquiv_apply_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.getEquiv_apply_coe.h3 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (i : Fin l.length), l.Nodup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0, 0]) (0)) (by
  decide +kernel)

-- Set.ncard_image_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_image_le.h4 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, (f '' s).ncard ≤ s.ncard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | True}) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Nat.ofNat_nsmul_eq_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofNat_nsmul_eq_mul.h3 : ¬∀ {α : Type} [inst : NonAssocSemiring α] (n : ℕ) (a : α), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instNonAssocSemiring) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.Embedding.coe_snoc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.Embedding.coe_snoc.h4 : ¬∀ {α : Type} {n : ℕ} (x : Fin n ↪ α) {a : α}, a ∉ Set.range ⇑x := fun hc_h => absurd (@hc_h (ℕ) (1) ({ toFun := fun (a : Fin 1) => 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Fin 1 ↪ ℕ }) (0)) (by
  decide +kernel)

-- Fin.Embedding.coe_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.Embedding.coe_cons.h4 : ¬∀ {α : Type} {n : ℕ} (x : Fin n ↪ α) {a : α}, a ∉ Set.range ⇑x := fun hc_h => absurd (@hc_h (ℕ) (1) ({ toFun := fun (a : Fin 1) => 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Fin 1 ↪ ℕ }) (0)) (by
  decide +kernel)

-- Fin.get_take_ofFn_eq_take_comp_cast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.get_take_ofFn_eq_take_comp_cast.h4 : ¬∀ {n : ℕ} {α : Type} {m : ℕ} (v : Fin n → α), m ≤ n := fun hc_h => absurd (@hc_h (0) (ℕ) (1) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- List.lookmap_cons_none, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookmap_cons_none.h4 : ¬∀ {α : Type} (f : α → Option α) {a : α} (l : List α), List.lookmap f (a :: l) = a :: List.lookmap f l := fun hc_h => absurd (@hc_h (ℕ) (fun n => some (n + 1) : ℕ → Option ℕ) (0) ([])) (by
  decide +kernel)

-- List.dedup_cons_of_mem', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dedup_cons_of_mem'.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {l : List α}, (a :: l).dedup = l.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ([])) (by
  decide +kernel)

-- List.Perm.dedup, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.dedup.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l₁ l₂ : List α}, l₁.dedup.Perm l₂.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([0])) (by
  decide +kernel)

-- List.replicate_dedup, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.replicate_dedup.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {x : α} {k : ℕ}, (List.replicate k x).dedup = [x] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0)) (by
  decide +kernel)

-- List.nodupKeys_of_nodupKeys_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodupKeys_of_nodupKeys_cons.h4 : ¬∀ {α : Type} {β : α → Type} {s : Sigma β} {l : List (Sigma β)}, l.NodupKeys := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ((⟨0, 0⟩ : (_ : ℕ) × ℕ)) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  simp)

-- List.dedup_cons_of_notMem', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dedup_cons_of_notMem'.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {l : List α}, (a :: l).dedup = a :: l.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ([0])) (by
  decide +kernel)

-- List.dedup_cons_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dedup_cons_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {l : List α}, (a :: l).dedup = l.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ([])) (by
  decide +kernel)

-- List.exists_of_mem_keys, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_of_mem_keys.h4 : ¬∀ {α : Type} {β : α → Type} {a : α} {l : List (Sigma β)}, ∃ (b : β a), (⟨a, b⟩ : Sigma β) ∈ l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (0) ([])) (by
  simp)

-- List.Disjoint.union_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Disjoint.union_eq.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {xs ys : List α}, xs ∪ ys = xs.dedup ++ ys := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([0])) (by
  decide +kernel)

-- Set.InjOn.imageFactorization_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.imageFactorization_injective.h4 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, Function.Injective (Set.imageFactorization f s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | True}) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Function.Embedding.isEmpty_of_card_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.isEmpty_of_card_lt.h4 : ¬∀ {α β : Type} [inst : Fintype α] [inst : Fintype β], IsEmpty (α ↪ β) := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype)) (by
  exact fun hc_c =>
    absurd
      (hc_c.false ({ toFun := Bool.not, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ Bool } : Bool ↪ Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Quot.surjective_lift, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quot.surjective_lift.h4 : ¬∀ {α γ : Type} {r : α → α → Prop} {f : α → γ} (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ _ => True : Bool → Bool → Prop) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- Set.subset_image_compl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_image_compl.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set α}, (f '' s)ᶜ ⊆ f '' sᶜ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- List.choose_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.choose_spec.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : List α), ∃ a ∈ l, p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ([])) (by
  decide +kernel)

-- Set.subset_range_of_surjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_range_of_surjective.h3 : ¬∀ {α β : Type} {f : α → β} (s : Set β), s ⊆ Set.range f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.Ioc_filter_modEq_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Ioc_filter_modEq_card.h3 : Not
      (∀ (a b : Nat) {r : Nat} (v : Nat),
        @Eq Int
          (@Nat.cast Int instNatCastInt
            (@Finset.card Nat ({x ∈ @Finset.Ioc Nat Nat.instPreorder Nat.instLocallyFiniteOrder a b | r.ModEq x v})))
          (@Max.max Int Int.instMax
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
              (@Int.floor Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                  (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@Nat.cast Rat Rat.instNatCast b)
                    (@Nat.cast Rat Rat.instNatCast v))
                  (@Nat.cast Rat Rat.instNatCast r)))
              (@Int.floor Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                  (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@Nat.cast Rat Rat.instNatCast a)
                    (@Nat.cast Rat Rat.instNatCast v))
                  (@Nat.cast Rat Rat.instNatCast r))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Int.Ico_filter_modEq_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.Ico_filter_modEq_card.h3 : Not
      (∀ (a b : Int) {r : Int} (v : Int),
        @Eq Int
          (@Nat.cast Int instNatCastInt
            (@Finset.card Int ({x ∈ @Finset.Ico Int Int.instPreorder Int.instLocallyFiniteOrder a b | r.ModEq x v})))
          (@Max.max Int Int.instMax
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
              (@Int.ceil Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                  (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@Int.cast Rat Rat.instIntCast b)
                    (@Int.cast Rat Rat.instIntCast v))
                  (@Int.cast Rat Rat.instIntCast r)))
              (@Int.ceil Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                  (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@Int.cast Rat Rat.instIntCast a)
                    (@Int.cast Rat Rat.instIntCast v))
                  (@Int.cast Rat Rat.instIntCast r))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- List.mem_takeWhile_imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_takeWhile_imp.h4 : ¬∀ {α : Type} {p : α → Bool} {l : List α} {x : α}, p x = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([]) (1)) (by
  decide +kernel)

-- List.rdropWhile_concat_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rdropWhile_concat_neg.h4 : ¬∀ {α : Type} (p : α → Bool) (l : List α) (x : α), List.rdropWhile p (l ++ [x]) = l ++ [x] := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([]) (0)) (by
  decide +kernel)

-- List.rdrop_append_of_le_length, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rdrop_append_of_le_length.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} (k : ℕ), (l₁ ++ l₂).rdrop k = l₁ ++ l₂.rdrop k := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (1)) (by
  decide +kernel)

-- List.rtakeWhile_concat_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rtakeWhile_concat_pos.h4 : ¬∀ {α : Type} (p : α → Bool) (l : List α) (x : α), List.rtakeWhile p (l ++ [x]) = List.rtakeWhile p l ++ [x] := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([]) (1)) (by
  decide +kernel)

-- List.toFinset_eq_of_perm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinset_eq_of_perm.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (l l' : List α), l.toFinset = l'.toFinset := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([0])) (by
  decide +kernel)

-- List.interleaves_reverse_reverse_of_length_eq_length, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleaves_reverse_reverse_of_length_eq_length.h4 : ¬∀ {α : Type} {r : α → α → Prop} {l₁ l₂ : List α},
        List.Interleaves r l₁.reverse l₂.reverse ↔ List.Interleaves (Function.swap r) l₂ l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([0])) (by
  simp)

-- List.modifyLast_append_of_right_ne_nil, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.modifyLast_append_of_right_ne_nil.h4 : ¬∀ {α : Type} (f : α → α) (l₁ l₂ : List α), List.modifyLast f (l₁ ++ l₂) = l₁ ++ List.modifyLast f l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) ([0]) ([])) (by
  decide +kernel)

-- List.Palindrome.map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Palindrome.map.h4 : ¬∀ {α β : Type} {l : List α} (f : α → β), (List.map f l).Palindrome := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0, 1]) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- List.idxOf_eq_zero_iff_eq_nil_or_head_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_eq_zero_iff_eq_nil_or_head_eq.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α} (a : α), List.idxOf a l = 0 ↔ l = [] ∨ l.head? = Option.some a := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([0]) (1)) (by
  decide +kernel)

-- List.exists_mem_cons_of_exists, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_mem_cons_of_exists.h4 : ¬∀ {α : Type} {p : α → Prop} {a : α} {l : List α}, ∃ x ∈ a :: l, p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (1) ([])) (by
  decide +kernel)

-- List.of_mem_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.of_mem_filter.h4 : ¬∀ {α : Type} {p : α → Bool} {a : α} {l : List α}, p a = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (1) ([])) (by
  decide +kernel)

-- List.Shortlex.of_length_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Shortlex.of_length_lt.h4 : ¬∀ {α : Type} {r : α → α → Prop} {s t : List α}, List.Shortlex r s t := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([])) (by
  simp)

-- List.isPrefix_append_of_length, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isPrefix_append_of_length.h4 : ¬∀ {α : Type} {l₁ l₂ l₃ : List α}, l₁ <+: l₂ ++ l₃ ↔ l₁ <+: l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) ([0])) (by
  decide +kernel)

-- List.length_splitLengths_getElem_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_splitLengths_getElem_le.h4 : ¬∀ {α : Type} (l : List α) (sz : List ℕ) {i : ℕ}, i < (sz.splitLengths l).length := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0)) (by
  decide +kernel)

-- Set.preimage_const_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.preimage_const_of_notMem.h4 : ¬∀ {α β : Type} {b : β} {s : Set β}, (fun (x : α) => b) ⁻¹' s = ∅ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) ({n : ℕ | n = 0})) (by
  simp)

-- List.IsPrefix.take, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.take.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} (n : ℕ), List.take n l₁ <+: List.take n l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (1)) (by
  decide +kernel)

-- Set.Nonempty.subset_pair_iff_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.subset_pair_iff_eq.h4 : ¬∀ {α : Type} {s : Set α} {a b : α}, s ⊆ {a, b} ↔ s = {a} ∨ s = {b} ∨ s = {a, b} := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (0) (0)) (by
  simp)

-- Choose.choose_pow_mul_pow_mul_modEq_choose_nat, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.choose_pow_mul_pow_mul_modEq_choose_nat.h4 : ¬∀ {k a b p : ℕ}, (p ^ k * a).choose (p ^ k * b) ≡ a.choose b [MOD p] := fun hc_h => absurd (@hc_h (1) (0) (1) (0)) (by
  decide +kernel)

-- List.mem_getLast?_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_getLast?_cons.h4 : ¬∀ {α : Type} {x y : α} {l : List α}, x ∈ (y :: l).getLast? := fun hc_h => absurd (@hc_h (ℕ) (0) (1) ([])) (by
  decide +kernel)

-- Function.RightInverse.list_map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.list_map.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.RightInverse (List.map f) (List.map g) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  (simp <;> decide))

-- Nat.lt_nth_iff_count_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_nth_iff_count_lt.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {a b : ℕ}, a < Nat.count p b ↔ Nat.nth p a < b := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0) (1)) (by
  simp)

-- Set.ne_insert_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ne_insert_of_notMem.h4 : ¬∀ {α : Type} {s : Set α} (t : Set α) {a : α}, s ≠ Insert.insert a t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- List.insert_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insert_neg.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {x : α} {l : List α}, Insert.insert x l = x :: l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ([0])) (by
  decide +kernel)

-- List.mem_map_of_involutive, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_map_of_involutive.h2 : ¬∀ {α : Type} {f : α → α} {a : α} {l : List α}, a ∈ List.map f l ↔ f a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) ([1])) (by
  decide +kernel)

-- Ordnode.Sized.rotateR_size, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.rotateR_size.h4 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α}, (l.rotateR x r).size = l.size + r.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil)) (by
  decide +kernel)

-- Ordnode.Sized.rotateL_size, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.rotateL_size.h4 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α}, (l.rotateL x r).size = l.size + r.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  decide +kernel)

-- Function.Surjective.surjOn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.surjOn.h4 : ¬∀ {α β : Type} {t : Set β} {f : α → β}, Set.SurjOn f Set.univ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.nonempty_of_nonempty_preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_of_nonempty_preimage.h4 : ¬∀ {α β : Type} {s : Set β} {f : α → β}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.eq_or_mem_of_mem_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_or_mem_of_mem_insert.h4 : ¬∀ {α : Type} {x a : α} {s : Set α}, x = a ∨ x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (1) (0) ({n : ℕ | n = 0})) (by
  decide +kernel)

-- List.replicate_right_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.replicate_right_inj.h4 : ¬∀ {α : Type} {a b : α} {n : ℕ}, List.replicate n a = List.replicate n b ↔ a = b := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0)) (by
  decide +kernel)

-- Function.Involutive.exists_mem_and_apply_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.exists_mem_and_apply_eq_iff.h2 : ¬∀ {α : Type} {f : α → α} (x : α) (l : List α), (∃ y ∈ l, f y = x) ↔ f x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) ([1])) (by
  decide +kernel)

-- List.mem_of_mem_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_of_mem_filter.h4 : ¬∀ {α : Type} {p : α → Bool} {a : α} {l : List α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (0) ([])) (by
  decide +kernel)

-- List.choose_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.choose_mem.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : List α), ∃ a ∈ l, p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ([])) (by
  decide +kernel)

-- List.getElem_permutations'Aux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_permutations'Aux.h4 : ¬∀ {α : Type} (s : List α) (x : α) (n : ℕ), n < (List.permutations'Aux x s).length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (1)) (by
  decide +kernel)

-- List.perm_of_mem_permutationsAux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_of_mem_permutationsAux.h4 : ¬∀ {α : Type} {ts is l : List α}, l.Perm (ts ++ is) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) ([0])) (by
  decide +kernel)

-- List.prev_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x : α), x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  decide +kernel)

-- List.insert_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insert_pos.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {x : α} {l : List α}, Insert.insert x l = l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ([])) (by
  decide +kernel)

-- List.next_singleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_singleton.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (x y : α), x ∈ [y] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (1)) (by
  decide +kernel)

-- Set.insert_inter_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.insert_inter_of_mem.h4 : ¬∀ {α : Type} {s t : Set α} {a : α}, Insert.insert a s ∩ t = Insert.insert a (s ∩ t) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (0)) (by
  simp)

-- Prod.total_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.total_left.h4 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop}, Std.Total (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.total ((0, 0) : ℕ × ℕ) ((0, 0) : ℕ × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.next_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x : α), x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  decide +kernel)

-- List.prev_singleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_singleton.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (x y : α), x ∈ [y] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (1)) (by
  decide +kernel)

-- Set.inter_subset_inter_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_subset_inter_left.h4 : ¬∀ {α : Type} {s t : Set α} (u : Set α), s ∩ u ⊆ t ∩ u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.enumerate_eq_none_of_sel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.enumerate_eq_none_of_sel.h3 : ¬∀ {α : Type} (sel : Set α → Option α) {s : Set α} {n : ℕ}, Set.enumerate sel s n = Option.none := fun hc_h => absurd (@hc_h (ℕ) (fun (a : Set ℕ) => Option.some 0) ({n : ℕ | n = 0}) (0)) (by
  decide +kernel)

-- Set.insert_subset_insert_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.insert_subset_insert_iff.h4 : ¬∀ {α : Type} {s t : Set α} {a : α}, Insert.insert a s ⊆ Insert.insert a t ↔ s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (0)) (by
  simp)

-- List.maximum_of_length_pos_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maximum_of_length_pos_mem.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α}, 0 < l.length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([])) (by
  decide +kernel)

-- Nat.digitsAppend_eq_digits_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digitsAppend_eq_digits_iff.h3 : ¬∀ {b l : ℕ} {n : ℕ}, n ≠ 0 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Nat.find_eq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_eq_iff.h3 : ¬∀ {m : ℕ} {p : ℕ → Prop} [inst : DecidablePred p], ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (0) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse)) (by
  simp)

-- isPrimePow_of_minFac_pow_factorization_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.isPrimePow_of_minFac_pow_factorization_eq.h1 : ¬∀ {n : ℕ}, n ≠ 1 → IsPrimePow n := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- isPrimePow_of_minFac_pow_factorization_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.isPrimePow_of_minFac_pow_factorization_eq.h2 : ¬∀ {n : ℕ}, n.minFac ^ n.factorization n.minFac = n → IsPrimePow n := fun hc_h => absurd (@hc_h (1) (by
  decide +kernel)) (by
  decide +kernel)

-- Set.union_eq_self_of_subset_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_eq_self_of_subset_left.h3 : ¬∀ {α : Type} {s t : Set α}, s ∪ t = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Part.get_eq_iff_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.get_eq_iff_mem.h3 : ¬∀ {α : Type} {o : Part α} {a : α}, o.Dom := fun hc_h => absurd (@hc_h (ℕ) (⊥) (0)) (by
  nofun)

-- Nat.squarefree_of_factorization_le_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.squarefree_of_factorization_le_one.h1 : ¬∀ {n : ℕ}, (∀ (p : ℕ), n.factorization p ≤ 1) → Squarefree n := fun hc_h => absurd (@hc_h (0) (by
  simp)) (by
  decide +kernel)

-- Nat.squarefree_of_factorization_le_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.squarefree_of_factorization_le_one.h2 : ¬∀ {n : ℕ}, n ≠ 0 → Squarefree n := fun hc_h => absurd (@hc_h (4) (by
  decide)) (by
  decide +kernel)

-- univ_eq_singleton_of_card_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.univ_eq_singleton_of_card_one.h3 : ¬∀ {α : Type} [inst : Fintype α] (x : α), Finset.univ = {x} := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) (Bool.false)) (by
  decide +kernel)

-- Set.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ext.h3 : ¬∀ {α : Type} {a b : Set α}, a = b := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Nat.divMaxPow_base_pow_mul, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.divMaxPow_base_pow_mul.h1 : ¬∀ {p : ℕ} (n k : ℕ), (p ^ k * n).divMaxPow p = n.divMaxPow p := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- Set.sUnion_symmDiff_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sUnion_symmDiff_subset.h3 : ¬∀ {α : Type} {s : Set α} {S : Set (Set α)}, symmDiff (⋃₀ S) s ⊆ ⋃₀ ((fun (x : Set α) => symmDiff x s) '' S) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (∅)) (by
  simp)

-- Multiset.Aesop.toFinset_nonempty_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.Aesop.toFinset_nonempty_of_ne.h3.{u_1} : ¬∀ {α : Type u_1} [inst : DecidableEq α] {s : Multiset α}, s.toFinset.Nonempty := by
  (simp_all; done)

-- Nat.factorization_eq_zero_of_remainder, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_zero_of_remainder.h3 : ¬∀ {p r : ℕ} (i : ℕ), (p * i + r).factorization p = 0 := fun hc_h => absurd (@hc_h (2) (0) (1)) (by
  decide +kernel)

-- Nat.findGreatest_of_not, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_of_not.h3 : ¬∀ {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, Nat.findGreatest P (n + 1) = Nat.findGreatest P n := fun hc_h => absurd (@hc_h (fun n => n % 2 = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (1)) (by
  decide +kernel)

-- List.take_one_drop_eq_of_lt_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.take_one_drop_eq_of_lt_length.h3 : ¬∀ {α : Type} {l : List α} {n : ℕ}, n < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Int.Ioc_filter_dvd_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.Ioc_filter_dvd_card.h3 : Not
      (∀ (a b : Int) {r : Int},
        @Eq Int
          (@Nat.cast Int instNatCastInt
            (@Finset.card Int
              ({x ∈ @Finset.Ioc Int Int.instPreorder Int.instLocallyFiniteOrder a b | @Dvd.dvd Int Int.instDvd r x})))
          (@Max.max Int Int.instMax
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
              (@Int.floor Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast b)
                  (@Int.cast Rat Rat.instIntCast r)))
              (@Int.floor Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                  (@Int.cast Rat Rat.instIntCast r))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.lt_find_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_find_iff.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (n : ℕ), ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0)) (by
  simp)

-- ENat.add_le_add_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_le_add_iff_left.h3 : ¬∀ {m n k : ℕ∞}, k + n ≤ k + m ↔ n ≤ m := fun hc_h => absurd (@hc_h (0) (1) (⊤)) (by
  decide +kernel)

-- ENat.add_lt_add_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_lt_add_iff_right.h3 : ¬∀ {m n k : ℕ∞}, n + k < m + k ↔ n < m := fun hc_h => absurd (@hc_h (1) (0) (⊤)) (by
  decide +kernel)

-- List.exists_not_getElem_of_not_isChain, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_not_getElem_of_not_isChain.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, ∃ (n : ℕ) (h : n + 1 < l.length), ¬R l[n] l[n + 1] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([])) (by
  simp)

-- Set.exists_of_ssubset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_of_ssubset.h3 : ¬∀ {α : Type} {s t : Set α}, ∃ x ∈ t, x ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.val_comp_inclusion, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.val_comp_inclusion.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Nat.factorization_mul_apply_of_coprime, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_mul_apply_of_coprime.h3 : ¬∀ {p a b : ℕ}, (a * b).factorization p = a.factorization p + b.factorization p := fun hc_h => absurd (@hc_h (2) (0) (2)) (by
  decide +kernel)

-- List.minimum_ne_top_of_ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_ne_top_of_ne_nil.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α}, l.minimum ≠ ⊤ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([])) (by
  decide +kernel)

-- ENat.WithBot.add_ofNat_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.WithBot.add_ofNat_cancel.h3 : ¬∀ {a b : WithBot ℕ∞} {c : ℕ}, c.AtLeastTwo := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.Nonempty.of_sdiff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_sdiff.h3 : ¬∀ {α : Type} {s : Set α} {t : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- List.Duplicate.mem_cons_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.mem_cons_self.h3 : ¬∀ {α : Type} {l : List α} {x : α}, x ∈ l := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- LT.lt.ssubset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.LT.lt.ssubset.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊂ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.Duplicate.ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.ne_nil.h3 : ¬∀ {α : Type} {l : List α} {x : α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime.h3 : ¬∀ {x n m : ℕ}, x.gcd n * x.gcd m = x ↔ x ∣ n * m := fun hc_h => absurd (@hc_h (2) (0) (0)) (by
  decide +kernel)

-- List.Mem.duplicate_cons_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Mem.duplicate_cons_self.h3 : ¬∀ {α : Type} {l : List α} {x : α}, List.Duplicate x (x :: l) := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Nat.dvd_lcm_of_dvd_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_lcm_of_dvd_left.h2 : ¬∀ {a b : ℕ} (c : ℕ), a ∣ b.lcm c := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- Nat.Coprime.dvd_mul_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.dvd_mul_right.h3 : ¬∀ {m n k : ℕ}, k ∣ m * n ↔ k ∣ m := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  decide +kernel)

-- Nat.pow_sub_one_dvd_pow_sub_one_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_sub_one_dvd_pow_sub_one_iff.h3 : ¬∀ {a b c : ℕ}, a ^ b - 1 ∣ a ^ c - 1 ↔ b ∣ c := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Nat.Dvd.dvd.nat_lcm_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Dvd.dvd.nat_lcm_left.h2 : ¬∀ {a b : ℕ} (c : ℕ), a ∣ c.lcm b := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- Nat.dvd_of_lcm_right_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_of_lcm_right_dvd.h3 : ¬∀ {a : ℕ} {b : ℕ} {c : ℕ}, a ∣ c := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Nat.coprime_add_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_add_iff_left.h3 : ¬∀ {a b c : ℕ}, a.Coprime (b + c) ↔ a.Coprime b := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Nat.modEq_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_of_dvd.h3 : ¬∀ {n a b : ℕ}, a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- List.rotate'_eq_drop_append_take, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rotate'_eq_drop_append_take.h3 : ¬∀ {α : Type} {l : List α} {n : ℕ}, l.rotate' n = List.drop n l ++ List.take n l := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (3)) (by
  decide +kernel)

-- StrictAnti.sortedGT, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictAnti.sortedGT.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedLT.of_reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.of_reverse.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.Pairwise.sortedLE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.sortedLE.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLE := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.coe_minimum_of_length_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.coe_minimum_of_length_pos.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α}, 0 < l.length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([])) (by
  decide +kernel)

-- PNat.Coprime.gcd_mul_right_cancel_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.gcd_mul_right_cancel_right.h3 : ¬∀ (m : ℕ+) {n k : ℕ+}, m.gcd (n * k) = m.gcd n := fun hc_h => absurd (@hc_h (2) (1) (2)) (by
  decide +kernel)

-- Set.union_eq_self_of_subset_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_eq_self_of_subset_right.h3 : ¬∀ {α : Type} {s t : Set α}, s ∪ t = s := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.count_succ_eq_succ_count, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_succ_eq_succ_count.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, Nat.count p (n + 1) = Nat.count p n + 1 := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1)) (by
  decide +kernel)

-- NNRat.cast_ofNat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.cast_ofNat.h3 : ¬∀ {α : Type} [inst : DivisionSemiring α] (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield.toDivisionSemiring) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.modEq_sub_modulus_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_sub_modulus_iff.h3 : ¬∀ {n a b : ℕ}, a ≡ b - n [MOD n] ↔ a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (2) (0) (1)) (by
  decide +kernel)

-- Nat.ModEq.gcd_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.gcd_eq.h3 : ¬∀ {m a b : ℕ}, a.gcd m = b.gcd m := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Nat.ModEq.dvd', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.dvd'.h3 : ¬∀ {n a b : ℕ}, n ∣ b - a := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- List.SortedGE.map_toDual, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.map_toDual.h3 : ¬∀ {α : Type} [inst : Preorder α] {l : List α}, l.SortedLE := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) ([1, 0])) (by
  decide +kernel)

-- Nat.sub_modulus_modEq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sub_modulus_modEq_iff.h3 : ¬∀ {n a b : ℕ}, a - n ≡ b [MOD n] ↔ a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (2) (1) (0)) (by
  decide +kernel)

-- Finset.mk_coe, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.mk_coe.h3.der.{u_1} : ∀ {α : Type u_1} {s : Finset α} (x : @Set.Elem α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)),
      @Membership.mem α (Set α) (@Set.instMembership α) (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
        (@Subtype.val α
          (fun (x : α) =>
            @Membership.mem α (Set α) (@Set.instMembership α) (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) x)
          x) := by
  (intros; simp; done)
theorem HypCheckProof.Finset.mk_coe.h3.{u_1} : ∀ {α : Type u_1} {s : Finset α} (x : @Set.Elem α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)),
      @Eq
        (@Subtype α fun (x : α) =>
          @Membership.mem α (Set α) (@Set.instMembership α) (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) x)
        (@Subtype.mk α
          (fun (x : α) =>
            @Membership.mem α (Set α) (@Set.instMembership α) (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) x)
          (@Subtype.val α
            (fun (x : α) =>
              @Membership.mem α (Set α) (@Set.instMembership α) (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) x)
            x)
          (@HypCheckProof.Finset.mk_coe.h3.der α s x))
        x := by
  intro hc_x0 hc_x1 hc_x2
  exact @Finset.mk_coe hc_x0 hc_x1 hc_x2 (@HypCheckProof.Finset.mk_coe.h3.der hc_x0 hc_x1 hc_x2)

-- Nat.add_div_of_dvd_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_div_of_dvd_left.h3 : ¬∀ {a b c : ℕ}, (a + b) / c = a / c + b / c := fun hc_h => absurd (@hc_h (1) (1) (2)) (by
  decide +kernel)

-- Monotone.sortedLE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.sortedLE.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLE := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedLT.nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.nodup.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedGE.of_reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.of_reverse.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLE := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Set.image_val_sInter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_val_sInter.h3 : ¬∀ {α : Type} {A : Set α} {T : Set (Set ↑A)}, Subtype.val '' ⋂₀ T = ⋂₀ {x : Set α | ∃ B ∈ T, Subtype.val '' B = x} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (∅)) (by
  norm_num)

-- List.SortedLT.pairwise, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.pairwise.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], List.Pairwise (fun (x1 x2 : α) => x1 < x2) l := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Int.ModEq.neg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.neg.h3 : ¬∀ {n a b : ℤ}, -a ≡ -b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Set.exists_mem_const, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_mem_const.h3 : ¬∀ {α : Type} {s : Set α} {p : Prop}, (∃ x ∈ s, p) ↔ p := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (True)) (by
  simp)

-- List.tfae_concat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.tfae_concat.h3 : ¬∀ {a b : Prop} {l : List Prop}, (l ++ [a]).TFAE ↔ (a ↔ b) ∧ l.TFAE := fun hc_h => absurd (@hc_h (True) (False) ([])) (by
  simp)

-- List.SortedLT.sortedLE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.sortedLE.h3 : ¬∀ {α : Type} [inst : Preorder α] {l : List α}, l.SortedLE := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) ([1, 0])) (by
  decide +kernel)

-- List.Pairwise.reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.reverse.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.Pairwise R l.reverse := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0, 1])) (by
  decide +kernel)

-- Set.ncard_sdiff_singleton_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_sdiff_singleton_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, (s \ {a}).ncard = s.ncard - 1 := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- List.SortedGT.strictAnti_get, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.strictAnti_get.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], StrictAnti l.get := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.Pairwise.of_reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.of_reverse.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.Pairwise (fun (a b : α) => R b a) l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0, 1])) (by
  decide +kernel)

-- Function.Injective.preimage_surjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.preimage_surjective.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective (Set.preimage f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Nat.descFactorial_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.descFactorial_le.h3 : ¬∀ (n : ℕ) {k m : ℕ}, k.descFactorial n ≤ m.descFactorial n := fun hc_h => absurd (@hc_h (1) (1) (0)) (by
  decide +kernel)

-- Set.Nontrivial.not_subset_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.not_subset_singleton.h3 : ¬∀ {α : Type} {s : Set α} {x : α}, ¬s ⊆ {x} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Nat.factorization_le_of_le_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_le_of_le_pow.h3 : ¬∀ {n p b : ℕ}, n.factorization p ≤ b := fun hc_h => absurd (@hc_h (2) (2) (0)) (by
  decide +kernel)

-- List.tfae_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.tfae_cons.h3 : ¬∀ {a b : Prop} {l : List Prop}, (a :: l).TFAE ↔ (a ↔ b) ∧ l.TFAE := fun hc_h => absurd (@hc_h (True) (False) ([])) (by
  simp)

-- Set.exists_subset_encard_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_subset_encard_eq.h3 : ¬∀ {α : Type} {s : Set α} {k : ℕ∞}, ∃ t ⊆ s, t.encard = k := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (1)) (by
  simp)

-- List.SortedGE.reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.reverse.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.reverse.SortedLE := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.exists_not_and_succ_of_not_zero_of_exists, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_not_and_succ_of_not_zero_of_exists.h1 : ¬∀ {p : ℕ → Prop}, (∃ (n : ℕ), p n) → ∃ (n : ℕ), ¬p n ∧ p (n + 1) := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (by
  simp)) (by
  simp)

-- Nat.exists_not_and_succ_of_not_zero_of_exists, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.exists_not_and_succ_of_not_zero_of_exists.h2.inst : ¬∃ (n : ℕ), ¬(fun (x : ℕ) => False) n ∧ (fun (x : ℕ) => False) (n + 1) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.exists_not_and_succ_of_not_zero_of_exists.h2.prem0 : ¬(fun (x : ℕ) => False) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.exists_not_and_succ_of_not_zero_of_exists.h2 : ¬∀ {p : ℕ → Prop}, ¬p 0 → ∃ (n : ℕ), ¬p n ∧ p (n + 1) := fun hc_h => HypCheckProof.Nat.exists_not_and_succ_of_not_zero_of_exists.h2.inst (@hc_h (fun (x : ℕ) => False) HypCheckProof.Nat.exists_not_and_succ_of_not_zero_of_exists.h2.prem0)

-- Nat.size_shiftLeft', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.size_shiftLeft'.h3 : ¬∀ {b : Bool} {m n : ℕ}, (Nat.shiftLeft' b m n).size = m.size + n := fun hc_h => absurd (@hc_h (Bool.false) (0) (1)) (by
  decide +kernel)

-- Nat.shiftLeft'_ne_zero_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.shiftLeft'_ne_zero_left.h2 : ¬∀ (b : Bool) {m : ℕ} (n : ℕ), Nat.shiftLeft' b m n ≠ 0 := fun hc_h => absurd (@hc_h (Bool.false) (0) (0)) (by
  decide +kernel)

-- ZMod.castHom_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.castHom_injective.h3 : ¬∀ {n : ℕ} (R : Type) [inst : Ring R], CharP R n := fun hc_h => absurd (@hc_h (0) (Bool) (instBooleanRingBool.toRing)) (by
  exact fun hc_c =>
    absurd (hc_c.cast_eq_zero_iff (2 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Subsingleton.mem_iff_nonempty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subsingleton.mem_iff_nonempty.h1 : ¬∀ {α : Type} {s : Set α} {x : α}, x ∈ s ↔ s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Nat.bitwise_comm, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bitwise_comm.h1 : ¬∀ {f : Bool → Bool → Bool} (n m : ℕ), Nat.bitwise f n m = Nat.bitwise f m n := fun hc_h => absurd (@hc_h (fun a b => !a || b : Bool → Bool → Bool) (0) (1)) (by
  decide +kernel)

-- StrictMono.sortedLT, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.sortedLT.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.getElem_bijective_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_bijective_iff.h3 : ¬∀ {α : Type} {l : List α} [inst : BEq α],
        (Function.Bijective fun (n : Fin l.length) => l[n]) ↔ ∀ (a : α), List.count a l = 1 := fun hc_h => absurd (@hc_h (Bool) ([Bool.false]) (⟨fun _ _ => true⟩ : BEq Bool)) (by
  decide +kernel)

-- Set.ncard_inter_le_ncard_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_inter_le_ncard_right.h3 : ¬∀ {α : Type} (s t : Set α), (s ∩ t).ncard ≤ t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True})) (by
  simp)

-- List.Sublist.sublists', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.sublists'.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.sublists'.Sublist l₂.sublists' := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([])) (by
  decide +kernel)

-- Set.encard_insert_of_notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_insert_of_notMem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, (Insert.insert a s).encard = s.encard + 1 := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  norm_num)

-- List.disjoint_of_nodup_append, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_nodup_append.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Disjoint l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0])) (by
  simp)

-- Set.encard_le_encard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_le_encard.h3 : ¬∀ {α : Type} {s t : Set α}, s.encard ≤ t.encard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Nat.factorization_choose_le_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_le_one.h3 : ¬∀ {p n k : ℕ}, (n.choose k).factorization p ≤ 1 := fun hc_h => absurd (@hc_h (2) (4) (1)) (by
  decide +kernel)

-- Int.gcd_eq_one_of_gcd_mul_right_eq_one_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_eq_one_of_gcd_mul_right_eq_one_left.h3 : ¬∀ {a : ℤ} {m : ℕ} {n : ℕ}, a.gcd ↑m = 1 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Fin.le_of_surjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.le_of_surjective.h3 : ¬∀ {m n : ℕ} (f : Fin m → Fin n), n ≤ m := fun hc_h => absurd (@hc_h (0) (1) (fun (a : Fin 0) => (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Set.nonempty_inter_compl_of_ncard_add_ncard_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_inter_compl_of_ncard_add_ncard_lt.h3 : ¬∀ {α : Type} {s t : Set α}, (sᶜ ∩ tᶜ).Nonempty := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false})) (by
  simp)

-- Set.nonempty_of_ssubset', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_of_ssubset'.h3 : ¬∀ {α : Type} {s : Set α} {t : Set α}, t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- List.NodupKeys.nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.NodupKeys.nodup.h3 : ¬∀ {α : Type} {β : α → Type} {l : List (Sigma β)}, l.Nodup := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- Set.exists_ne_of_one_lt_encard, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_ne_of_one_lt_encard.h2 : ¬∀ {α : Type} {s : Set α} (a : α), ∃ b ∈ s, b ≠ a := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- List.NodupKeys.pairwise_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.NodupKeys.pairwise_ne.h3 : ¬∀ {α : Type} {β : α → Type} {l : List (Sigma β)}, List.Pairwise (fun (s s' : Sigma β) => s.fst ≠ s'.fst) l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- Nat.exists_dvd_of_not_prime2, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_dvd_of_not_prime2.h1 : ¬∀ {n : ℕ}, ¬Nat.Prime n → ∃ (m : ℕ), m ∣ n ∧ 2 ≤ m ∧ m < n := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- Nat.exists_dvd_of_not_prime2, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_dvd_of_not_prime2.h2 : ¬∀ {n : ℕ}, 2 ≤ n → ∃ (m : ℕ), m ∣ n ∧ 2 ≤ m ∧ m < n := fun hc_h => absurd (@hc_h (2) (by
  decide)) (by
  omega)

-- List.Nodup.dedup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.dedup.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α}, l.dedup = l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0, 0])) (by
  decide +kernel)

-- Set.sigmaToiUnion_bijective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sigmaToiUnion_bijective.h3 : ¬∀ {α β : Type} (t : α → Set β), Function.Bijective (Set.sigmaToiUnion t) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) => {n : ℕ | n = 0})) (by
  (simp <;> decide))

-- Set.ncard_diff_singleton_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_diff_singleton_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, (s \ {a}).ncard = s.ncard - 1 := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Set.ncard_pair, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_pair.h3 : Not
      (∀ {α : Type} {a b : α},
        @Eq Nat
          (@Set.ncard α
            (@Insert.insert α (Set α) (@Set.instInsert α) a (@Singleton.singleton α (Set α) (@Set.instSingletonSet α) b)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)

-- Set.inter_eq_self_of_subset_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_eq_self_of_subset_right.h3 : ¬∀ {α : Type} {s t : Set α}, s ∩ t = t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- ZMod.natCast_pow_eq_zero_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.natCast_pow_eq_zero_of_le.h3 : Not
      (∀ (p : Nat) {m n : Nat},
        @Eq (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
          (@HPow.hPow
            (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
            Nat
            (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
            (@instHPow
              (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
              Nat
              (@NPow.toPow
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
                (@Monoid.toNPow
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
                  (@Semiring.toMonoid
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        n))
                    (@CommSemiring.toSemiring
                      (ZMod
                        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                          n))
                      (@CommRing.toCommSemiring
                        (ZMod
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p n))
                        (ZMod.commRing
                          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            p n))))))))
            (@Nat.cast
              (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
              (@AddMonoidWithOne.toNatCast
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
                (@AddGroupWithOne.toAddMonoidWithOne
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
                  (@Ring.toAddGroupWithOne
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        n))
                    (@CommRing.toRing
                      (ZMod
                        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                          n))
                      (ZMod.commRing
                        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                          n))))))
              p)
            m)
          (@OfNat.ofNat
            (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
            (nat_lit 0)
            (@Zero.toOfNat0
              (ZMod (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
              (@MulZeroClass.toZero
                (ZMod
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
                (@instMulZeroClassOfSemiring
                  (ZMod
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p n))
                  (@CommSemiring.toSemiring
                    (ZMod
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                        n))
                    (@CommRing.toCommSemiring
                      (ZMod
                        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                          n))
                      (ZMod.commRing
                        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) p
                          n))))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Set.image_perm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_perm.h3 : Not
      (∀ {α : Type} {s : Set α} {σ : Equiv.Perm α},
        @Eq (Set α)
          (@Set.image α α
            (@DFunLike.coe (Equiv.Perm α) α (fun (x : α) => α)
              (@EquivLike.toFunLike (Equiv.Perm α) α α (@Equiv.instEquivLike α α)) σ)
            s)
          s) := fun hc_h => absurd (@hc_h (Bool) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Equiv.mk Bool Bool Bool.not Bool.not
      (@of_decide_eq_true (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
        (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
        (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  simp)

-- Function.Surjective.image_surjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.image_surjective.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective (Set.image f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  (simp <;> decide))

-- Set.surjOn_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.surjOn_of_subsingleton.h1 : ¬∀ {α : Type} (f : α → α) (s : Set α), Set.SurjOn f s s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- AList.keys_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AList.keys_mk.h3 : ¬∀ {α : Type} {β : α → Type} (l : List (Sigma β)), l.NodupKeys := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  simp)

-- Computation.eq_of_pure_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.eq_of_pure_mem.h3 : ¬∀ {α : Type} {a a' : α}, a' = a := fun hc_h => absurd (@hc_h (ℕ) (0) (1)) (by
  decide +kernel)

-- Set.Aesop.toFinset_nonempty_of_nonempty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Aesop.toFinset_nonempty_of_nonempty.h3 : ¬∀ {α : Type} {s : Set α} [inst : Fintype ↑s], s.toFinset.Nonempty := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | False}) (Subtype.fintype (Membership.mem {x : Bool | False}))) (by
  decide +kernel)

-- Set.forall_mem_const, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.forall_mem_const.h3 : ¬∀ {α : Type} {s : Set α} {p : Prop}, (∀ x ∈ s, p) ↔ p := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (False)) (by
  simp)

-- Nat.Prime.even_sub_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.even_sub_one.h1 : ¬∀ {p : ℕ}, p ≠ 2 → Even (p - 1) := fun hc_h => absurd (@hc_h (4) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.even_sub_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.even_sub_one.h2 : ¬∀ {p : ℕ}, Nat.Prime p → Even (p - 1) := fun hc_h => absurd (@hc_h (2) (by
  decide)) (by
  decide +kernel)

-- Nat.pow_lt_of_lt_clog, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_lt_of_lt_clog.h3 : ¬∀ {b x y : ℕ}, b ^ y < x := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Nat.lt_clog_iff_pow_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_clog_iff_pow_lt.h1 : ¬∀ {b x y : ℕ}, y < Nat.clog b x ↔ b ^ y < x := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- Set.range_inclusion, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.range_inclusion.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Fin.val_add_eq_of_add_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_add_eq_of_add_lt.h3 : Not
      (∀ {n : Nat} {a b : Fin n},
        @Eq Nat (@Fin.val n (@HAdd.hAdd (Fin n) (Fin n) (Fin n) (@instHAdd (Fin n) (@Fin.instAdd n)) a b))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val n a) (@Fin.val n b))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Fin.ne_last_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.ne_last_of_lt.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.get_bijective_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.get_bijective_iff.h3 : ¬∀ {α : Type} {l : List α} [inst : BEq α], Function.Bijective l.get ↔ ∀ (a : α), List.count a l = 1 := fun hc_h => absurd (@hc_h (Bool) ([Bool.false]) (⟨fun _ _ => true⟩ : BEq Bool)) (by
  decide +kernel)

-- Nat.dvd_prime_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_prime_pow.h1 : ¬∀ {p m i : ℕ}, i ∣ p ^ m ↔ ∃ k ≤ m, i = p ^ k := fun hc_h => absurd (@hc_h (0) (1) (2)) (by
  decide +kernel)

-- Set.setOf_subset_setOf_of_imp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.setOf_subset_setOf_of_imp.h3 : ¬∀ {α : Type} {p q : α → Prop}, {a : α | p a} ⊆ {a : α | q a} := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop)) (by
  simp)

-- Set.nonempty_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {x : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (0)) (by
  simp)

-- Fin.exists_ne_and_ne_of_two_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_ne_and_ne_of_two_lt.h3 : ¬∀ {n : ℕ} (i j : Fin n), ∃ (k : Fin n), k ≠ i ∧ k ≠ j := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.sub_succ_le_sub_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_succ_le_sub_of_le.h3 : ¬∀ {n : ℕ} {u v : Fin (n + 2)}, v - (u + 1) < v - u := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- List.Nodup.mergeSort, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.mergeSort.h3 : ¬∀ {α : Type} {l : List α} {le : α → α → Bool}, (l.mergeSort le).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (fun a b => a < b : ℕ → ℕ → Bool)) (by
  simp)

-- List.not_nodup_cons_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_nodup_cons_of_mem.h3 : ¬∀ {α : Type} {l : List α} {a : α}, ¬(a :: l).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Function.Surjective.preimage_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.preimage_injective.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Injective (Set.preimage f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  (simp <;> decide))

-- EReal.coe_toReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.coe_toReal.h1 : ¬∀ {x : EReal}, x ≠ ⊥ → ↑x.toReal = x := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.coe_toReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.coe_toReal.h2 : ¬∀ {x : EReal}, x ≠ ⊤ → ↑x.toReal = x := fun hc_h => absurd (@hc_h (⊥) (by
  decide)) (by
  decide +kernel)

-- Rat.divInt_mul_divInt_cancel, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.divInt_mul_divInt_cancel.h1 : ¬∀ {x : ℤ} (n d : ℤ), Rat.divInt n x * Rat.divInt x d = Rat.divInt n d := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- Fin.le_castSucc_pred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.le_castSucc_pred_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Set.offDiag_union, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.offDiag_union.h3 : ¬∀ {α : Type} {s t : Set α}, (s ∪ t).offDiag = s.offDiag ∪ t.offDiag ∪ s ×ˢ t ∪ t ×ˢ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.IsPrefix.reduceOption, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.reduceOption.h3 : ¬∀ {α : Type} {l₁ l₂ : List (Option α)}, l₁.reduceOption <+: l₂.reduceOption := fun hc_h => absurd (@hc_h (ℕ) ([Option.some 0]) ([])) (by
  decide +kernel)

-- Fin.lt_succ_castPred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.lt_succ_castPred_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.getLast_getLast_splitBy, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast_getLast_splitBy.h3 : ¬∀ {α : Type} (r : α → α → Bool) {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Bool) ([])) (by
  decide +kernel)

-- Fin.pred_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_le_iff.h3 : ¬∀ {n : ℕ} {j : Fin n} {i : Fin (n + 1)}, i ≠ 0 := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- EReal.sub_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_self.h1 : ¬∀ {x : EReal}, x ≠ ⊥ → x - x = 0 := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.sub_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_self.h2 : ¬∀ {x : EReal}, x ≠ ⊤ → x - x = 0 := fun hc_h => absurd (@hc_h (⊥) (by
  decide)) (by
  decide +kernel)

-- Fin.le_pred_castSucc_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.le_pred_castSucc_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a.castSucc ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- ENat.sSup_mem_of_nonempty_of_lt_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.sSup_mem_of_nonempty_of_lt_top.h1 : ¬∀ {s : Set ℕ∞}, SupSet.sSup s < ⊤ → SupSet.sSup s ∈ s := fun hc_h => absurd (@hc_h (∅) (by
  simp)) (by
  decide +kernel)

-- Fin.predAbove_castSucc_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_castSucc_of_lt.h3 : ¬∀ {n : ℕ} (p i : Fin n), p < i := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.le_pred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.le_pred_iff.h3 : ¬∀ {n : ℕ} {j : Fin n} {i : Fin (n + 1)}, i ≠ 0 := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Choose.gcd_choose_eq_one_of_not_isPrimePow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.gcd_choose_eq_one_of_not_isPrimePow.h1 : ¬∀ {n : ℕ}, ¬IsPrimePow n → (Finset.Icc 1 (n - 1)).gcd n.choose = 1 := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- Choose.gcd_choose_eq_one_of_not_isPrimePow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.gcd_choose_eq_one_of_not_isPrimePow.h2 : ¬∀ {n : ℕ}, 1 < n → (Finset.Icc 1 (n - 1)).gcd n.choose = 1 := fun hc_h => absurd (@hc_h (2) (by
  decide)) (by
  decide +kernel)

-- Choose.choose_modEq_choose_mod_mul_choose_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.choose_modEq_choose_mod_mul_choose_div.h3 : ¬∀ {n k p : ℕ}, ↑(n.choose k) ≡ ↑((n % p).choose (k % p)) * ↑((n / p).choose (k / p)) [ZMOD ↑p] := fun hc_h => absurd (@hc_h (4) (2) (4)) (by
  decide +kernel)

-- Rat.mk'_zero, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Rat.mk'_zero.h1.der : ∀ (d : ℕ), (Int.natAbs 0).Coprime d → d ≠ 0 := by
  (intros; simp_all; done)
theorem HypCheckProof.Rat.mk'_zero.h1 : ∀ (d : ℕ) (w : (Int.natAbs 0).Coprime d),
      { num := 0, den := d, den_nz := HypCheckProof.Rat.mk'_zero.h1.der d w, reduced := w : ℚ } = 0 := by
  intro hc_x0 hc_x1
  exact @Rat.mk'_zero hc_x0 (@HypCheckProof.Rat.mk'_zero.h1.der hc_x0 hc_x1) hc_x1

-- Rat.mk'_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk'_zero.h2 : ¬∀ (d : ℕ), d ≠ 0 → (Int.natAbs 0).Coprime d := fun hc_h => absurd (@hc_h (2) (by
  decide)) (by
  decide +kernel)

-- Choose.choose_modEq_choose_mod_mul_choose_div_nat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.choose_modEq_choose_mod_mul_choose_div_nat.h3 : ¬∀ {n k p : ℕ}, n.choose k ≡ (n % p).choose (k % p) * (n / p).choose (k / p) [MOD p] := fun hc_h => absurd (@hc_h (4) (2) (4)) (by
  decide +kernel)

-- NNRat.divNat_mul_left, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.divNat_mul_left.h1 : ¬∀ {a : ℕ} (n d : ℕ), NNRat.divNat (a * n) (a * d) = NNRat.divNat n d := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- EReal.sub_le_of_le_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_le_of_le_add.h3 : ¬∀ {a b c : EReal}, a - c ≤ b := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  simp)

-- List.Aesop.toFinset_nonempty_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Aesop.toFinset_nonempty_of_ne.h3 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.toFinset.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- Choose.choose_mul_mul_modEq_choose_nat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.choose_mul_mul_modEq_choose_nat.h3 : ¬∀ {a b p : ℕ}, (p * a).choose (p * b) ≡ a.choose b [MOD p] := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- EReal.sub_lt_of_lt_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_lt_of_lt_add.h3 : ¬∀ {a b c : EReal}, a - c < b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Choose.choose_mul_mul_modEq_choose, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.choose_mul_mul_modEq_choose.h3 : ¬∀ {a b p : ℕ}, ↑((p * a).choose (p * b)) ≡ ↑(a.choose b) [ZMOD ↑p] := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- Nat.eleven_dvd_of_palindrome, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eleven_dvd_of_palindrome.h1 : ¬∀ {n : ℕ}, Even (Nat.digits 10 n).length → 11 ∣ n := fun hc_h => absurd (@hc_h (10) (by
  decide)) (by
  decide +kernel)

-- Nat.eleven_dvd_of_palindrome, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eleven_dvd_of_palindrome.h2 : ¬∀ {n : ℕ}, (Nat.digits 10 n).Palindrome → 11 ∣ n := fun hc_h => absurd (@hc_h (1) (by
  decide)) (by
  decide +kernel)

-- Fin.pred_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_lt_iff.h3 : ¬∀ {n : ℕ} {j : Fin n} {i : Fin (n + 1)}, i ≠ 0 := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Set.eq_singleton_or_nontrivial, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_singleton_or_nontrivial.h3 : ¬∀ {α : Type} {a : α} {s : Set α}, s = {a} ∨ s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.count_nth_succ_of_infinite, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_nth_succ_of_infinite.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (n : ℕ), Nat.count p (Nat.nth p n + 1) = n + 1 := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0)) (by
  simp)

-- EReal.add_lt_add_left_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_lt_add_left_coe.h2 : ¬∀ {x y : EReal} (z : ℝ), ↑z + x < ↑z + y := fun hc_h => absurd (@hc_h (0) (0) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Int.dvd_div_iff_mul_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.dvd_div_iff_mul_dvd.h3 : ¬∀ {a b c : ℤ}, a ∣ b / c ↔ c * a ∣ b := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- Set.Nonempty.right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.right.h3 : ¬∀ {α : Type} {s : Set α} {t : Set α}, t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Nat.le_nth_count', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_nth_count'.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, n ≤ Nat.nth p (Nat.count p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1)) (by
  simp)

-- Set.bijOn_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.bijOn_of_subsingleton.h1 : ¬∀ {α : Type} (f : α → α) (s : Set α), Set.BijOn f s s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Fin.le_castPred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.le_castPred_iff.h3 : ¬∀ {n : ℕ} {j : Fin n} {i : Fin (n + 1)}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Set.insert_eq_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.insert_eq_of_mem.h3 : ¬∀ {α : Type} {a : α} {s : Set α}, Insert.insert a s = s := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0})) (by
  simp)

-- NeZero.of_neZero_natCast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NeZero.of_neZero_natCast.h3 : ¬∀ (R : Type) [inst : AddMonoidWithOne R] {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- NeZero.pos_of_neZero_natCast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NeZero.pos_of_neZero_natCast.h3 : ¬∀ (R : Type) [inst : AddMonoidWithOne R] {n : ℕ}, 0 < n := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (0)) (by
  decide +kernel)

-- Nat.count_nth_succ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_nth_succ.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, Nat.count p (Nat.nth p n + 1) = n + 1 := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0)) (by
  simp)

-- Nat.count_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_eq_zero.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, Nat.count p n = 0 ↔ n ≤ Nat.nth p 0 := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1)) (by
  simp)

-- Fin.succAbove_castSucc_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_castSucc_of_lt.h3 : ¬∀ {n : ℕ} (p i : Fin n), p.castSucc.succAbove i = i.castSucc := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- finCongr_apply_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finCongr_apply_coe.h2 : ¬∀ {n m : ℕ} (k : Fin m), m = n := fun hc_h => absurd (@hc_h (0) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.predAbove_of_lt_succ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_of_lt_succ.h3 : ¬∀ {n : ℕ} (p : Fin n) (i : Fin (n + 1)), i < p.succ := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Fin.succAbove_castPred_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_castPred_of_lt.h3 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), i < p := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.castSucc_ne_zero_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castSucc_ne_zero_of_lt.h3 : ¬∀ {n : ℕ} {p : Fin n} {i : Fin n}, i.castSucc ≠ 0 := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.length_eraseIdx_add_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_eraseIdx_add_one.h3 : ¬∀ {ι : Type} {l : List ι} {i : ℕ}, (l.eraseIdx i).length + 1 = l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Sym2.Rel.symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.Rel.symm.h3 : ¬∀ {α : Type} {x y : α × α}, Sym2.Rel α y x := fun hc_h => absurd (@hc_h (ℕ) ((0, 0)) ((0, 1))) (by
  decide +kernel)

-- Fin.castPred_eq_iff_eq_castSucc, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_eq_iff_eq_castSucc.h2 : ¬∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Set.inter_singleton_of_notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_singleton_of_notMem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, s ∩ {a} = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Set.EqOn.image_eq_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.image_eq_self.h3 : ¬∀ {α : Type} {s : Set α} {f : α → α}, f '' s = s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.subset_sUnion_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_sUnion_of_mem.h3 : ¬∀ {α : Type} {S : Set (Set α)} {t : Set α}, t ⊆ ⋃₀ S := fun hc_h => absurd (@hc_h (ℕ) (∅) ({n : ℕ | n = 0})) (by
  simp)

-- Ordnode.Raised.add_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Raised.add_right.h3 : ¬∀ (k : ℕ) {n m : ℕ}, Ordnode.Raised (n + k) (m + k) := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  nofun)

-- Set.mapsTo_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mapsTo_of_subsingleton.h1 : ¬∀ {α : Type} (f : α → α) (s : Set α), Set.MapsTo f s s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Set.nonempty_of_not_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_of_not_subset.h3 : ¬∀ {α : Type} {s t : Set α}, (s \ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  nofun)

-- Fin.predAbove_castSucc_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_castSucc_of_le.h3 : ¬∀ {n : ℕ} (p i : Fin n), p.predAbove i.castSucc = i := fun hc_h => absurd (@hc_h (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Ordnode.eraseMax.valid, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.eraseMax.valid.h3 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α}, t.eraseMax.Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) 0 Ordnode.nil)) (by
  nofun)

-- Fin.predAbove_of_le_castSucc, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_of_le_castSucc.h3 : ¬∀ {n : ℕ} (p : Fin n) (i : Fin (n + 1)), i ≤ p.castSucc := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Set.mem_singleton_of_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_singleton_of_eq.h3 : Not
      (∀ {α : Type} {x y : α},
        @Membership.mem α (Set α) (@Set.instMembership α) (@Singleton.singleton α (Set α) (@Set.instSingletonSet α) y) x) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Fin.predAbove_of_succ_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_of_succ_le.h3 : ¬∀ {n : ℕ} (p : Fin n) (i : Fin (n + 1)), p.succ ≤ i := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Set.Nonempty.subset_singleton_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.subset_singleton_iff.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, s ⊆ {a} ↔ s = {a} := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (0)) (by
  simp)

-- EReal.inv_neg_of_neg_ne_bot, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.inv_neg_of_neg_ne_bot.h1 : ¬∀ {a : EReal}, a ≠ ⊥ → a⁻¹ < 0 := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- EReal.inv_neg_of_neg_ne_bot, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.inv_neg_of_neg_ne_bot.h2 : ¬∀ {a : EReal}, a < 0 → a⁻¹ < 0 := fun hc_h => absurd (@hc_h (⊥) (by
  decide)) (by
  simp)

-- Set.ssubset_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ssubset_insert.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, s ⊂ Insert.insert a s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Fin.pred_castSucc_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_castSucc_lt_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a.castSucc ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Sym2.diagElem_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.diagElem_mk.h3 : ¬∀ {α : Type} {a b : α}, s(a, b).IsDiag := fun hc_h => absurd (@hc_h (ℕ) (0) (1)) (by
  decide +kernel)

-- Nat.dvd_div_of_mul_dvd_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_div_of_mul_dvd_left.h3 : ¬∀ {a b c : ℕ}, b ∣ c / a := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  decide +kernel)

-- finCongr_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finCongr_apply.h2 : ¬∀ {n m : ℕ} (i : Fin n), n = m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Perm.permutations, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.permutations.h3 : ¬∀ {α : Type} {s t : List α}, s.permutations.Perm t.permutations := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  (simp <;> decide))

-- Fin.castPred_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_lt_iff.h3 : ¬∀ {n : ℕ} {j : Fin n} {i : Fin (n + 1)}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Nat.le_find_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_find_iff.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (n : ℕ), ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0)) (by
  simp)

-- EReal.top_div_of_neg_ne_bot, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.top_div_of_neg_ne_bot.h1 : ¬∀ {a : EReal}, a ≠ ⊥ → ⊤ / a = ⊥ := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- EReal.top_div_of_neg_ne_bot, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.top_div_of_neg_ne_bot.h2 : ¬∀ {a : EReal}, a < 0 → ⊤ / a = ⊥ := fun hc_h => absurd (@hc_h (⊥) (by
  decide)) (by
  simp)

-- PNat.modDivAux_spec, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.modDivAux_spec.h3 : ¬∀ (k : ℕ+) (r q : ℕ), ↑(k.modDivAux r q).1 + ↑k * (k.modDivAux r q).2 = r + ↑k * q := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  decide +kernel)

-- Nat.find_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_le_iff.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (n : ℕ), ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0)) (by
  simp)

-- List.Sublist.sym2, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.sym2.h3 : ¬∀ {α : Type} {xs ys : List α}, xs.sym2.Sublist ys.sym2 := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([])) (by
  decide +kernel)

-- Finset.orderEmbOfFin_compl_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.orderEmbOfFin_compl_singleton.h3 : Not
      (∀ {n : Nat}
        {i :
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
        {k : Nat},
        @Eq Nat
          (@Finset.card
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Compl.compl
              (Finset
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@BooleanAlgebra.toCompl
                (Finset
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Finset.booleanAlgebra
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin.fintype
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@Singleton.singleton
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Finset
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Finset.instSingleton
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                i)))
          k) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Cycle.chain_ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.chain_ne_nil.h3 : ¬∀ {α : Type} (r : α → α → Prop) {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([])) (by
  decide +kernel)

-- List.getElem_cons_eraseIdx_perm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_cons_eraseIdx_perm.h3 : ¬∀ {α : Type} {l : List α} {n : ℕ}, n < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq.h3 : ¬∀ {b : ℕ} {l1 l2 : List ℕ},
        Nat.ofDigits b l1 + Nat.ofDigits b l2 = Nat.ofDigits b (List.zipWith (fun (x1 x2 : ℕ) => x1 + x2) l1 l2) := fun hc_h => absurd (@hc_h (0) ([]) ([1])) (by
  decide +kernel)

-- List.Subperm.sym2, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.sym2.h3 : ¬∀ {α : Type} {xs ys : List α}, xs.sym2.Subperm ys.sym2 := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([])) (by
  decide +kernel)

-- Fin.get_find?_eq_find_of_eq_true, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.get_find?_eq_find_of_eq_true.h3 : ¬∀ {n : ℕ} {i : Fin n} {p : Fin n → Bool}, p i = Bool.true := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Bool.false)) (by
  decide +kernel)

-- List.eq_cons_of_mem_head?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_cons_of_mem_head?.h3 : ¬∀ {α : Type} {x : α} {l : List α}, l = x :: l.tail := fun hc_h => absurd (@hc_h (ℕ) (0) ([])) (by
  decide +kernel)

-- Membership.mem.out, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Membership.mem.out.h3 : ¬∀ {α : Type} {a : α} {p : α → Prop}, p a := fun hc_h => absurd (@hc_h (ℕ) (1) (fun n => n = 0 : ℕ → Prop)) (by
  decide +kernel)

-- Set.iUnion_of_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iUnion_of_empty.h2 : ¬∀ {α ι : Type} (s : ι → Set α), ⋃ (i : ι), s i = ∅ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0})) (by
  simp)

-- List.Lex.to_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.to_ne.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ ≠ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([])) (by
  decide +kernel)

-- List.IsChain.tail, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.tail.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.IsChain R l.tail := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([2, 1, 0])) (by
  decide +kernel)

-- Set.inclusion_eq_subtype_map, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inclusion_eq_subtype_map.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.Nonempty.forall_const, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.forall_const.h2 : ¬∀ {α : Type} {s : Set α} {p : Prop}, (∀ x ∈ s, p) ↔ p := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (False)) (by
  simp)

-- Nat.bit_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bit_le.h3 : ¬∀ (b : Bool) {m n : ℕ}, Nat.bit b m ≤ Nat.bit b n := fun hc_h => absurd (@hc_h (Bool.false) (1) (0)) (by
  decide +kernel)

-- Nat.le_length_digits_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_length_digits_le.h3 : ¬∀ (b n m : ℕ), (b.digits n).length ≤ (b.digits m).length := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- Int.sq_eq_one_of_sq_lt_four, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.sq_eq_one_of_sq_lt_four.h1 : ¬∀ {x : ℤ}, x ≠ 0 → x ^ 2 = 1 := fun hc_h => absurd (@hc_h (2) (by
  decide)) (by
  decide +kernel)

-- Int.sq_eq_one_of_sq_lt_four, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.sq_eq_one_of_sq_lt_four.h2 : ¬∀ {x : ℤ}, x ^ 2 < 4 → x ^ 2 = 1 := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- Nat.modEq_digits_sum, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_digits_sum.h2 : ¬∀ (b b' n : ℕ), n ≡ (b'.digits n).sum [MOD b] := fun hc_h => absurd (@hc_h (0) (2) (2)) (by
  decide +kernel)

-- Set.setOf_mem_list_eq_singleton_of_nodup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.setOf_mem_list_eq_singleton_of_nodup.h2 : ¬∀ {α : Type} {l : List α} {a : α}, {x : α | x ∈ l} = {a} ↔ l = [a] := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (0)) (by
  simp)

-- List.nodup_ofFn_ofInjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_ofFn_ofInjective.h3 : ¬∀ {α : Type} {n : ℕ} {f : Fin n → α}, (List.ofFn f).Nodup := fun hc_h => absurd (@hc_h (ℕ) (2) (fun (a : Fin 2) => 0)) (by
  decide +kernel)

-- Nat.Prime.dvd_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_mul.h3 : ¬∀ {p m n : ℕ}, p ∣ m * n ↔ p ∣ m ∨ p ∣ n := fun hc_h => absurd (@hc_h (4) (2) (2)) (by
  decide +kernel)

-- Part.assert_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.assert_pos.h3 : ¬∀ {α : Type} {p : Prop} {f : p → Part α}, p := fun hc_h => absurd (@hc_h (ℕ) (False) (fun (a : False) => 0)) (by
  decide +kernel)

-- List.mem_fixedLengthDigits_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_fixedLengthDigits_iff.h1 : ¬∀ {b : ℕ} {l : ℕ} {L : List ℕ}, 1 < b := fun hc_h => absurd (@hc_h (0) (0) ([])) (by
  decide +kernel)

-- Nat.digitsAppend_ne_nil_of_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digitsAppend_ne_nil_of_ne_zero.h3 : ¬∀ {b l n : ℕ}, b.digitsAppend l n ≠ [] := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Nat.pair_lt_pair_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pair_lt_pair_left.h3 : ¬∀ {a₁ a₂ : ℕ} (b : ℕ), Nat.pair a₁ b < Nat.pair a₂ b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- List.tail_sublistForall₂_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.tail_sublistForall₂_self.h2 : ¬∀ {α : Type} {Rₐ : α → α → Prop} (l : List α), List.SublistForall₂ Rₐ l.tail l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0, 1])) (by
  nofun)

-- Nat.pair_eq_of_unpair_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pair_eq_of_unpair_eq.h3 : ¬∀ {n a b : ℕ}, Nat.pair a b = n := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Nat.factorization_eq_zero_of_not_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_zero_of_not_dvd.h2 : ¬∀ {n p : ℕ}, n.factorization p = 0 := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Set.Nontrivial.ne_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.ne_empty.h2 : ¬∀ {α : Type} {s : Set α}, s ≠ ∅ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Nat.factorization_eq_zero_of_not_prime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_zero_of_not_prime.h2 : ¬∀ (n : ℕ) {p : ℕ}, n.factorization p = 0 := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Set.Nonempty.of_subtype, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_subtype.h2 : ¬∀ {α : Type} {s : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Fin.find?_eq_some_find_of_exists, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.find?_eq_some_find_of_exists.h2 : ¬∀ {n : ℕ} {p : Fin n → Bool}, ∃ (i : Fin n), p i = Bool.true := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false)) (by
  decide +kernel)

-- Int.ofNat_add_negSucc_of_ge, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ofNat_add_negSucc_of_ge.h2 : ¬∀ {m n : ℕ}, Int.ofNat m + Int.negSucc n = Int.ofNat (m - n.succ) := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- WithZeroMulInt.toNNReal_lt_one_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_lt_one_iff.h2 : ¬∀ {e : NNReal} {m : WithZero (Multiplicative ℤ)}, 1 < e := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Int.toNat_lt_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.toNat_lt_of_ne_zero.h2 : ¬∀ {m : ℤ} {n : ℕ}, m.toNat < n ↔ m < ↑n := fun hc_h => absurd (@hc_h (-1) (0)) (by
  decide +kernel)

-- List.eq_cons_of_length_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_cons_of_length_one.h2 : ¬∀ {α : Type} {l : List α}, l.length = 1 := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- ZMod.valMinAbs_natCast_eq_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.valMinAbs_natCast_eq_self.h2 : Not
      (∀ {n a : Nat},
        Iff
          (@Eq Int
            (@ZMod.valMinAbs n
              (@Nat.cast (ZMod n)
                (@AddMonoidWithOne.toNatCast (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                a))
            (@Nat.cast Int instNatCastInt a))
          (@LE.le Nat instLENat a
            (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) n
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- ZMod.valMinAbs_natCast_of_le_half, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.valMinAbs_natCast_of_le_half.h2 : Not
      (∀ {n a : Nat},
        @Eq Int
          (@ZMod.valMinAbs n
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              a))
          (@Nat.cast Int instNatCastInt a)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Nat.factorization_eq_zero_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_zero_of_lt.h2 : ¬∀ {n p : ℕ}, n.factorization p = 0 := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- ZMod.unitsMap_def, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.unitsMap_def.h2 : ¬∀ {n m : ℕ}, n ∣ m := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.ordProj_of_not_prime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordProj_of_not_prime.h2 : ¬∀ (n p : ℕ), p ^ n.factorization p = 1 := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Set.Nonempty.exists_eq_singleton_or_nontrivial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.exists_eq_singleton_or_nontrivial.h2 : ¬∀ {α : Type} {s : Set α}, (∃ (a : α), s = {a}) ∨ s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- ZMod.intCast_inv_mul_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.intCast_inv_mul_eq_one.h2 : Not
      (∀ {n : Nat} {x : Int},
        @Eq (ZMod n)
          (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
            (@instHMul (ZMod n)
              (@Distrib.toMul (ZMod n)
                (@instDistribOfSemiring (ZMod n)
                  (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
            (@Inv.inv (ZMod n) (ZMod.instInv n)
              (@Int.cast (ZMod n)
                (@AddGroupWithOne.toIntCast (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                x))
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              x))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- List.length_eq_two', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_eq_two'.h2 : ¬∀ {α : Type} {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Option.coe_get, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.coe_get.h2 : ¬∀ {α : Type} {o : Option α}, o.isSome = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (Option.none)) (by
  decide +kernel)

-- Nat.lt_ratSqrt_add_inv_prec_sq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_ratSqrt_add_inv_prec_sq.h2 : ¬∀ (x : ℕ) {prec : ℕ}, ↑x < (x.ratSqrt prec + 1 / ↑prec) ^ 2 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.factorial_mul_descFactorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_mul_descFactorial.h2 : ¬∀ {n k : ℕ}, (n - k).factorial * n.descFactorial k = n.factorial := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.add_factorial_le_factorial_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_factorial_le_factorial_add.h2 : ¬∀ (i : ℕ) {n : ℕ}, i + n.factorial ≤ (i + n).factorial := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.pow_sub_lt_descFactorial', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_sub_lt_descFactorial'.h2 : ¬∀ {n k : ℕ}, (n - (k + 1)) ^ (k + 2) < n.descFactorial (k + 2) := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.factorial_mul_pow_sub_le_factorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_mul_pow_sub_le_factorial.h2 : ¬∀ {n m : ℕ}, n.factorial * n ^ (m - n) ≤ m.factorial := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- ENat.add_sSup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_sSup.h2 : ¬∀ {s : Set ℕ∞} {a : ℕ∞}, a + SupSet.sSup s = ⨆ b ∈ s, a + b := fun hc_h => absurd (@hc_h (∅) (1)) (by
  simp)

-- Fintype.card_fin_lt_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_fin_lt_of_le.h2 : ¬∀ {m n : ℕ}, Fintype.card { i : Fin n // ↑i < m } = m := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- ENat.iInf_eq_top_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.iInf_eq_top_of_isEmpty.h2 : Not
      (∀ {ι : Type} {f : ι → Nat}, @Eq ENat (⨅ (i : ι), @Nat.cast ENat ENat.instNatCast (f i)) (@Top.top ENat instTopENat)) := fun hc_h => absurd (@hc_h (Nat) (fun n => n + 1 : Nat → Nat)) (by
  simp)

-- ENat.toNat_eq_iff_eq_natCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_eq_iff_eq_natCast.h2 : ¬∀ (n : ℕ∞) (m : ℕ), n.toNat = m ↔ n = ↑m := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  decide +kernel)

-- Nat.factorial_dvd_factorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_dvd_factorial.h2 : ¬∀ {m n : ℕ}, m.factorial ∣ n.factorial := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- Int.card_fintype_Icc_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.card_fintype_Icc_of_le.h2 : ¬∀ (a b : ℤ), ↑(Fintype.card ↑(Set.Icc a b)) = b + 1 - a := fun hc_h => absurd (@hc_h (1) (-1)) (by
  decide +kernel)

-- Int.card_Ioc_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.card_Ioc_of_le.h2 : ¬∀ (a b : ℤ), ↑(Finset.Ioc a b).card = b - a := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Int.card_Ioo_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.card_Ioo_of_lt.h2 : ¬∀ (a b : ℤ), ↑(Finset.Ioo a b).card = b - a - 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.two_pow_le_of_mem_bitIndices, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.two_pow_le_of_mem_bitIndices.h2 : ¬∀ {a n : ℕ}, 2 ^ a ≤ n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- ENat.lift_le_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.lift_le_iff.h1 : ¬∀ {x : ℕ∞} {n : ℕ}, x < ⊤ := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  decide +kernel)

-- ENat.lt_lift_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.lt_lift_iff.h2 : ¬∀ {x : ℕ} {n : ℕ∞}, n < ⊤ := fun hc_h => absurd (@hc_h (0) (⊤)) (by
  decide +kernel)

-- Sym2.disjoint_diagSet_fromRel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.disjoint_diagSet_fromRel.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Nodup.injective_get, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.injective_get.h2 : ¬∀ {α : Type} {l : List α}, Function.Injective l.get := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- Sym2.fromRel_top_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_top_iff.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Nodup.of_attach, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.of_attach.h2 : ¬∀ {α : Type} {l : List α}, l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- ENat.self_le_mul_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.self_le_mul_left.h2 : ¬∀ {c : ℕ∞} (a : ℕ∞), a ≤ c * a := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- ENat.eq_top_of_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.eq_top_of_pow.h2 : ¬∀ {a : ℕ∞} (n : ℕ), a = ⊤ := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.sqrt_add_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sqrt_add_eq.h2 : ¬∀ {a : ℕ} (n : ℕ), (n * n + a).sqrt = n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- List.cyclicPermutations_of_ne_nil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cyclicPermutations_of_ne_nil.h2 : ¬∀ {α : Type} (l : List α),
        l.cyclicPermutations = (List.zipWith (fun (x1 x2 : List α) => x1 ++ x2) l.tails l.inits).dropLast := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Nat.ascFactorial_lt_pow_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ascFactorial_lt_pow_add.h2 : ¬∀ (n : ℕ) {k : ℕ}, (n + 1).ascFactorial k < (n + k) ^ k := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- ENat.lift_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.lift_add.h2 : ¬∀ (a b : ℕ∞), a + b < ⊤ := fun hc_h => absurd (@hc_h (0) (⊤)) (by
  decide +kernel)

-- Set.Infinite.sUnion, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.sUnion.h2 : ¬∀ {α : Type} {s : Set (Set α)}, (⋃₀ s).Infinite := fun hc_h => absurd (@hc_h (ℕ) (∅)) (by
  simp)

-- Nat.add_factorial_succ_lt_factorial_add_succ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_factorial_succ_lt_factorial_add_succ.h2 : ¬∀ {i : ℕ} (n : ℕ), i + (n + 1).factorial < (i + n + 1).factorial := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- ENat.natCast_le_of_coe_top_le_withTop, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.natCast_le_of_coe_top_le_withTop.h1 : ¬∀ {N : WithTop ℕ∞} (n : ℕ), ↑n ≤ N := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- List.Nodup.sym2, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.sym2.h2 : ¬∀ {α : Type} {xs : List α}, xs.sym2.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- ENat.one_le_epow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.one_le_epow.h2 : ¬∀ {x y : ℕ∞}, 1 ≤ x ^ y := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Int.gcd_least_linear, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_least_linear.h2 : ¬∀ {a b : ℤ}, IsLeast {n : ℕ | 0 < n ∧ ∃ (x : ℤ) (y : ℤ), ↑n = a * x + b * y} (a.gcd b) := fun hc_h => absurd (@hc_h (0) (0)) (by
  (simp <;> decide))

-- Bool.ofNat_le_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.ofNat_le_ofNat.h2 : ¬∀ {n m : ℕ}, Bool.ofNat n ≤ Bool.ofNat m := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.coprime_sub_self_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_sub_self_left.h2 : ¬∀ {m n : ℕ}, (n - m).Coprime m ↔ n.Coprime m := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- Nat.psub_eq_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.psub_eq_sub.h2 : ¬∀ {m n : ℕ}, m.psub n = Option.some (m - n) := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.size_shiftLeft, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.size_shiftLeft.h1 : ¬∀ {m : ℕ} (n : ℕ), (m <<< n).size = m.size + n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.shiftLeft'_true_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.shiftLeft'_true_ne_zero.h2 : ¬∀ (m : ℕ) {n : ℕ}, Nat.shiftLeft' Bool.true m n ≠ 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.size_le_size, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.size_le_size.h2 : ¬∀ {m n : ℕ}, m.size ≤ n.size := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Int.gcd_div_gcd_div_gcd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_div_gcd_div_gcd.h2 : ¬∀ {i j : ℤ}, (i / ↑(i.gcd j)).gcd (j / ↑(i.gcd j)) = 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.coprime_self_sub_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_self_sub_right.h2 : ¬∀ {m n : ℕ}, n.Coprime (n - m) ↔ n.Coprime m := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Bool.of_decide_true, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.of_decide_true.h2 : ¬∀ {p : Prop} [inst : Decidable p], p := fun hc_h => absurd (@hc_h (False) (instDecidableFalse)) (by
  decide +kernel)

-- Bool.decide_false, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.decide_false.h2 : ¬∀ {p : Prop} [inst : Decidable p], Decidable.decide p = Bool.false := fun hc_h => absurd (@hc_h (True) (instDecidableTrue)) (by
  decide +kernel)

-- List.IsChain.length_sub_one_le_two_mul_count_bool, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.length_sub_one_le_two_mul_count_bool.h1 : ¬∀ {l : List Bool} (b : Bool), l.length - 1 ≤ 2 * List.count b l := fun hc_h => absurd (@hc_h ([Bool.false, Bool.false]) (Bool.true)) (by
  decide +kernel)

-- List.IsChain.two_mul_count_bool_eq_ite, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.two_mul_count_bool_eq_ite.h1 : ¬∀ {l : List Bool} (b : Bool),
        2 * List.count b l =
          if Even l.length then l.length else if (Option.some b == l.head?) = Bool.true then l.length + 1 else l.length - 1 := fun hc_h => absurd (@hc_h ([Bool.false, Bool.false]) (Bool.false)) (by
  decide +kernel)

-- List.IsChain.count_not_le_count_add_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.count_not_le_count_add_one.h1 : ¬∀ {l : List Bool} (b : Bool), List.count (!b) l ≤ List.count b l + 1 := fun hc_h => absurd (@hc_h ([Bool.false, Bool.false]) (Bool.true)) (by
  decide +kernel)

-- Finset.Nonempty.toList_ne_nil, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.toList_ne_nil.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, s.toList ≠ [] := by
  (simp_all; done)

-- Set.Pairwise.subsingleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Pairwise.subsingleton.h2 : ¬∀ {α : Type} {s : Set α}, s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True})) (by
  decide +kernel)

-- Finset.Nonempty.attach, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.attach.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, s.attach.Nonempty := by
  (simp_all; done)

-- Finset.Nonempty.ne_empty, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.ne_empty.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, s ≠ ∅ := by
  (simp_all; done)

-- Nat.of_le_succ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.of_le_succ.h2 : ¬∀ {m n : ℕ}, m ≤ n ∨ m = n.succ := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- List.drop_length_sub_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.drop_length_sub_one.h2 : ¬∀ {α : Type} {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Set.Nonempty.not_subset_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.not_subset_empty.h2 : ¬∀ {α : Type} {s : Set α}, ¬s ⊆ ∅ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Fin.coe_of_injective_castSucc_symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.coe_of_injective_castSucc_symm.h2 : ¬∀ {n : ℕ} (i : Fin n.succ), i ∈ Set.range Fin.castSucc := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Finset.univ_nontrivial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.univ_nontrivial.h2 : Not (∀ {α : Type} [inst : Fintype α], @Finset.Nontrivial α (@Finset.univ α inst)) := fun hc_h => absurd (@hc_h (Unit) (PUnit.fintype)) (by
  decide +kernel)

-- Prod.fst_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.fst_injective.h2 : Not (∀ {α β : Type}, @Function.Injective (Prod α β) α (@Prod.fst α β)) := fun hc_h => absurd (@hc_h (Bool) (Bool)) (by
  decide +kernel)

-- Finset.univ_eq_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.univ_eq_empty.h2 : Not
      (∀ {α : Type} [inst : Fintype α],
        @Eq (Finset α) (@Finset.univ α inst) (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))) := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype)) (by
  decide +kernel)

-- Fintype.univ_ofSubsingleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.univ_ofSubsingleton.h2 : ¬∀ {α : Type} (a : α), Subsingleton α := fun hc_h => absurd (@hc_h (ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Bool.or_inl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.or_inl.h2 : ¬∀ {a b : Bool}, (a || b) = Bool.true := fun hc_h => absurd (@hc_h (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Nat.modEq_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_sub.h2 : ¬∀ {a b : ℕ}, a ≡ b [MOD a - b] := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- FinEnum.card_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FinEnum.card_eq_zero.h2 : ¬∀ {α : Type} [inst : FinEnum α], FinEnum.card α = 0 := fun hc_h => absurd (@hc_h (Fin 2) (FinEnum.fin)) (by
  decide +kernel)

-- Fin.one_le_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.one_le_of_ne_zero.h2 : Not
      (∀ {n : Nat} {k : Fin n},
        @LE.le (Fin n) (@instLEFin n) (@OfNat.ofNat (Fin n) (nat_lit 1) (@Fin.instOfNat n (@Fin.neZero n k) (nat_lit 1))) k) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Multiset.noncommProd_empty, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Multiset.noncommProd_empty.h2.der.{u_3} : ∀ {α : Type u_3} [inst : Monoid α],
      @Set.Pairwise α
        (@Set.ofPred α fun (x : α) =>
          @Membership.mem α (Multiset α) (@Multiset.instMembership α)
            (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α))) x)
        (@Commute α (@MulOne.toMul α (@MulOneClass.toMulOne α (@Monoid.toMulOneClass α inst)))) := by
  (intros; simp; done)
theorem HypCheckProof.Multiset.noncommProd_empty.h2.{u_3} : ∀ {α : Type u_3} [inst : Monoid α],
      @Eq α
        (@Multiset.noncommProd α inst
          (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α)))
          (@HypCheckProof.Multiset.noncommProd_empty.h2.der α inst))
        (@OfNat.ofNat α (nat_lit 1)
          (@One.toOfNat1 α (@MulOne.toOne α (@MulOneClass.toMulOne α (@Monoid.toMulOneClass α inst))))) := by
  intro hc_x0 hc_x1
  exact @Multiset.noncommProd_empty hc_x0 hc_x1 (@HypCheckProof.Multiset.noncommProd_empty.h2.der hc_x0 hc_x1)

-- Set.Nontrivial.choose_fst_ne_choose_snd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.choose_fst_ne_choose_snd.h2 : ¬∀ {α : Type} {s : Set α}, s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Fin.coe_ofNat_eq_mod, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.coe_ofNat_eq_mod.h2 : ¬∀ (m n : ℕ), NeZero m := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.natCast_eq_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_eq_mk.h2 : ¬∀ {m n : ℕ}, m < n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Set.Nontrivial.coe_sort, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.coe_sort.h2 : ¬∀ {α : Type} {s : Set α}, Nontrivial ↑s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  nofun)

-- Fin.val_intCast, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_intCast.h1 : ¬∀ {n : ℕ} (x : ℤ), NeZero n := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.totient_dvd_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_dvd_of_dvd.h2 : ¬∀ {a b : ℕ}, a.totient ∣ b.totient := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.totient_mul_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_mul_of_dvd.h2 : ¬∀ {p n : ℕ}, (p * n).totient = p * n.totient := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- Nat.card_units_zmod_lt_sub_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.card_units_zmod_lt_sub_one.h1 : ¬∀ {p : ℕ} [inst : Fintype (ZMod p)ˣ], Fintype.card (ZMod p)ˣ ≤ p - 1 := fun hc_h => absurd (@hc_h (1) (instFintypeUnitsOfDecidableEq)) (by
  decide +kernel)

-- Int.nonneg_or_nonpos_of_mul_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.nonneg_or_nonpos_of_mul_nonneg.h2 : ¬∀ {a b : ℤ}, 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := fun hc_h => absurd (@hc_h (1) (-1)) (by
  decide +kernel)

-- Set.eq_univ_of_forall, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_univ_of_forall.h2 : ¬∀ {α : Type} {s : Set α}, s = Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Fin.succ_succAbove_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succ_succAbove_one.h1 : ¬∀ {n : ℕ} (i : Fin (n + 1)), NeZero n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.Infinite.ncard, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.ncard.h2 : ¬∀ {α : Type} {s : Set α}, s.ncard = 0 := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Fin.castSucc_pred_eq_pred_castSucc, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castSucc_pred_eq_pred_castSucc.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Set.Infinite.nonempty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.nonempty.h2 : ¬∀ {α : Type} {s : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Finset.Nontrivial.nonempty, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nontrivial.nonempty.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, s.Nonempty := by
  (simp_all; done)

-- List.dropLast_append_getLast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dropLast_append_getLast.h2 : ¬∀ {α : Type} {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Set.Nonempty.of_sUnion, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_sUnion.h2 : ¬∀ {α : Type} {s : Set (Set α)}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (∅)) (by
  simp)

-- Nat.minFac_lemma, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minFac_lemma.h2 : ¬∀ (n k : ℕ), n.sqrt - k < n.sqrt + 2 - k := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Nat.dvd_prime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_prime.h2 : ¬∀ {p m : ℕ}, m ∣ p ↔ m = 1 ∨ m = p := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Fin.succ_castPred_eq_add_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succ_castPred_eq_add_one.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Rat.toNNRat_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_mul.h2 : ¬∀ {p q : ℚ}, (p * q).toNNRat = p.toNNRat * q.toNNRat := fun hc_h => absurd (@hc_h (-1) (-1)) (by
  decide +kernel)

-- List.Ico.eq_nil_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.eq_nil_of_le.h2 : ¬∀ {n m : ℕ}, List.Ico n m = [] := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- List.Ico.filter_lt_of_succ_bot, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.filter_lt_of_succ_bot.h2 : ¬∀ {n m : ℕ}, List.filter (fun (x : ℕ) => Decidable.decide (x < n + 1)) (List.Ico n m) = [n] := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- List.Ico.eq_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.eq_cons.h2 : ¬∀ {n m : ℕ}, List.Ico n m = n :: List.Ico (n + 1) m := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Set.Nontrivial.nonempty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.nonempty.h2 : ¬∀ {α : Type} {s : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Finset.Nonempty.card_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.card_ne_zero.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, s.card ≠ 0 := by
  (simp_all; done)

-- Set.ncard_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_eq_zero.h2 : ¬∀ {α : Type} {s : Set α}, s.ncard = 0 ↔ s = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True})) (by
  simp)

-- Set.Nontrivial.not_subset_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.not_subset_empty.h2 : ¬∀ {α : Type} {s : Set α}, ¬s ⊆ ∅ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Fin.eq_castSucc_of_ne_last, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_castSucc_of_ne_last.h2 : ¬∀ {n : ℕ} {x : Fin (n + 1)}, ∃ (y : Fin n), y.castSucc = x := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Multiset.replicate_right_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.replicate_right_injective.h2 : Not (∀ {α : Type} {n : Nat}, @Function.Injective α (Multiset α) (@Multiset.replicate α n)) := fun hc_h => absurd (@hc_h (Bool) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Set.Finite.toFinset_univ, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Finite.toFinset_univ.h2.der.{u} : ∀ {α : Type u} [inst : Fintype α], @Set.Finite α (@Set.univ α) := by
  (intros; simp; done)
theorem HypCheckProof.Set.Finite.toFinset_univ.h2.{u} : ∀ {α : Type u} [inst : Fintype α],
      @Eq (Finset α) (@Set.Finite.toFinset α (@Set.univ α) (@HypCheckProof.Set.Finite.toFinset_univ.h2.der α inst))
        (@Finset.univ α inst) := by
  intro hc_x0 hc_x1
  exact @Set.Finite.toFinset_univ hc_x0 hc_x1 (@HypCheckProof.Set.Finite.toFinset_univ.h2.der hc_x0 hc_x1)

-- Int.lt_of_ofNat_lt_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.lt_of_ofNat_lt_ofNat.h2 : ¬∀ {n m : ℕ}, n < m := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Rat.toNNRat_lt_toNNRat_iff_of_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_lt_toNNRat_iff_of_nonneg.h2 : ¬∀ {p q : ℚ}, q.toNNRat < p.toNNRat ↔ q < p := fun hc_h => absurd (@hc_h (0) (-1)) (by
  decide +kernel)

-- Fin.leftInverse_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.leftInverse_cast.h2 : ¬∀ {n m : ℕ}, n = m := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.coprime_or_dvd_of_prime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_or_dvd_of_prime.h1 : ¬∀ {p : ℕ} (i : ℕ), p.Coprime i ∨ p ∣ i := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- NNRat.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.ext.h2 : ¬∀ {p q : ℚ≥0}, p = q := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Set.Infinite.encard_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.encard_eq.h2 : ¬∀ {α : Type} {s : Set α}, s.encard = ⊤ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Rat.toNNRat_div', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_div'.h2 : ¬∀ {p q : ℚ}, (p / q).toNNRat = p.toNNRat / q.toNNRat := fun hc_h => absurd (@hc_h (-1) (-1)) (by
  decide +kernel)

-- Int.mul_nonneg_of_nonneg_or_nonpos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.mul_nonneg_of_nonneg_or_nonpos.h2 : ¬∀ {a b : ℤ}, 0 ≤ a * b := fun hc_h => absurd (@hc_h (1) (-1)) (by
  decide +kernel)

-- Set.ncard_le_one_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_le_one_of_subsingleton.h1 : ¬∀ {α : Type} (s : Set α), s.ncard ≤ 1 := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True})) (by
  simp)

-- Nat.Prime.not_prime_pow', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.not_prime_pow'.h2 : ¬∀ {x n : ℕ}, ¬Nat.Prime (x ^ n) := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- Fin.lt_succ_castPred, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.lt_succ_castPred.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- EReal.le_of_forall_ratCast_lt_imp_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.le_of_forall_ratCast_lt_imp_le.h2 : ¬∀ {a b : EReal}, a ≤ b := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- PNat.eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.eq.h2 : ¬∀ {m n : ℕ+}, m = n := fun hc_h => absurd (@hc_h (1) (2)) (by
  decide +kernel)

-- EReal.le_of_forall_lt_ratCast_imp_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.le_of_forall_lt_ratCast_imp_le.h2 : ¬∀ {a b : EReal}, a ≤ b := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- Nat.dist_eq_sub_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dist_eq_sub_of_le.h2 : ¬∀ {n m : ℕ}, n.dist m = m - n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.eq_of_dist_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_dist_eq_zero.h2 : ¬∀ {n m : ℕ}, n = m := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- EReal.exists_rat_btwn_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_rat_btwn_of_lt.h2 : Not
      (∀ {a b : EReal},
        ∃ (x : Rat),
          And
            (@LT.lt EReal (@Preorder.toLT EReal (@PartialOrder.toPreorder EReal instPartialOrderEReal)) a
              ↑(@Rat.cast Real Real.instRatCast x))
            (@LT.lt EReal (@Preorder.toLT EReal (@PartialOrder.toPreorder EReal instPartialOrderEReal))
              (↑(@Rat.cast Real Real.instRatCast x)) b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat EReal (nat_lit 0) (@Zero.toOfNat0 EReal instZeroEReal)) (@Bot.bot EReal instBotEReal)) (by
  simp)

-- Nat.maxPrimeFac_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPrimeFac_pow.h1 : ¬∀ {k : ℕ} (n : ℕ), (n ^ k).maxPrimeFac = n.maxPrimeFac := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- EReal.lt_neg_of_lt_neg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.lt_neg_of_lt_neg.h2 : ¬∀ {a b : EReal}, b < -a := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nat.le_nth, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_nth.h2 : ¬∀ {p : ℕ → Prop} {n : ℕ}, n ≤ Nat.nth p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (1)) (by
  simp)

-- Fin.castSucc_pred_add_one_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castSucc_pred_add_one_eq.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Nat.Prime.eq_one_of_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.eq_one_of_pow.h2 : ¬∀ {x : ℕ} {n : ℕ}, n = 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.nth_of_forall, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_of_forall.h2 : ¬∀ {p : ℕ → Prop} {n : ℕ}, Nat.nth p n = n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (1)) (by
  simp)

-- Fin.castSucc_pred_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castSucc_pred_lt.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Nat.pos_of_mem_primeFactorsList, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pos_of_mem_primeFactorsList.h2 : ¬∀ {n : ℕ} {p : ℕ}, 0 < p := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.prime_of_mem_primeFactorsList, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_of_mem_primeFactorsList.h2 : ¬∀ {n : ℕ} {p : ℕ}, Nat.Prime p := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.isChain_cons_primeFactorsList, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.isChain_cons_primeFactorsList.h2 : ¬∀ {n a : ℕ}, List.IsChain (fun (x1 x2 : ℕ) => x1 ≤ x2) (a :: n.primeFactorsList) := fun hc_h => absurd (@hc_h (2) (3)) (by
  decide +kernel)

-- Int.eq_zero_or_eq_zero_of_mul_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.eq_zero_or_eq_zero_of_mul_eq_zero.h2 : ¬∀ {a b : ℤ}, a = 0 ∨ b = 0 := fun hc_h => absurd (@hc_h (1) (1)) (by
  decide +kernel)

-- Set.nonempty_of_ncard_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_of_ncard_ne_zero.h2 : ¬∀ {α : Type} {s : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Nat.primeFactorsList_sublist_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactorsList_sublist_right.h2 : ¬∀ {n k : ℕ}, n.primeFactorsList.Sublist (n * k).primeFactorsList := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- Nat.prime_of_mem_primeFactors, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_of_mem_primeFactors.h2 : ¬∀ {n : ℕ} {p : ℕ}, Nat.Prime p := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.le_of_mem_primeFactors, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_of_mem_primeFactors.h2 : ¬∀ {n p : ℕ}, p ≤ n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Ordnode.BalancedSz.symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.BalancedSz.symm.h2 : ¬∀ {l r : ℕ}, Ordnode.BalancedSz r l := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- EReal.neg_le_of_neg_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.neg_le_of_neg_le.h2 : ¬∀ {a b : EReal}, -b ≤ a := fun hc_h => absurd (@hc_h (0) (⊥)) (by
  decide +kernel)

-- Rat.den_div_intCast_eq_one_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.den_div_intCast_eq_one_iff.h2 : Not
      (∀ (m n : Int),
        Iff
          (@Eq Nat
            (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast m)
                (@Int.cast Rat Rat.instIntCast n)).den
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Dvd.dvd Int Int.instDvd n m)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- Ordnode.Sized.dual, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.dual.h2 : ¬∀ {α : Type} {t : Ordnode α}, t.dual.Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  nofun)

-- Set.ncard_powerset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_powerset.h2 : ¬∀ {α : Type} (s : Set α), (𝒫 s).ncard = 2 ^ s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True})) (by
  simp)

-- PNat.add_sub_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.add_sub_of_lt.h2 : ¬∀ {a b : ℕ+}, a + (b - a) = b := fun hc_h => absurd (@hc_h (1) (1)) (by
  decide +kernel)

-- List.replicate_right_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.replicate_right_injective.h2 : Not (∀ {α : Type} {n : Nat}, @Function.Injective α (List α) (@List.replicate α n)) := fun hc_h => absurd (@hc_h (Bool) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Rat.exists_eq_mul_div_num_and_eq_mul_div_den, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.exists_eq_mul_div_num_and_eq_mul_div_den.h2 : Not
      (∀ (n : Int) {d : Int},
        ∃ (c : Int),
          And
            (@Eq Int n
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) c
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast n)
                    (@Int.cast Rat Rat.instIntCast d)).num))
            (@Eq Int d
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) c
                (@Nat.cast Int instNatCastInt
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast n)
                      (@Int.cast Rat Rat.instIntCast d)).den)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  simp)

-- Fin.castLE_comp_castSucc, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLE_comp_castSucc.h2 : ¬∀ {n m : ℕ}, n + 1 ≤ m := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- List.Nodup.offDiag, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.offDiag.h2 : ¬∀ {α : Type} {l : List α}, l.offDiag.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- Nat.choose_mul_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_mul_right.h2 : ¬∀ {m n : ℕ}, (m * n).choose n = m * (m * n - 1).choose (n - 1) := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Finset.Nat.antidiagonal.snd_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nat.antidiagonal.snd_lt.h2 : ¬∀ {n : ℕ} {kl : ℕ × ℕ}, kl.2 < n + 1 := fun hc_h => absurd (@hc_h (0) ((0, 1))) (by
  decide +kernel)

-- Finset.Nat.antidiagonal.fst_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nat.antidiagonal.fst_lt.h2 : ¬∀ {n : ℕ} {kl : ℕ × ℕ}, kl.1 < n + 1 := fun hc_h => absurd (@hc_h (0) ((1, 0))) (by
  decide +kernel)

-- PrimeMultiset.mem_ofNatList, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PrimeMultiset.mem_ofNatList.h2 : ¬∀ {p : ℕ+} {l : List ℕ}, ∀ p ∈ l, Nat.Prime p := fun hc_h => absurd (@hc_h (1) ([0])) (by
  decide +kernel)

-- PrimeMultiset.coeNat_prime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PrimeMultiset.coeNat_prime.h2 : ¬∀ (v : PrimeMultiset) (p : ℕ), Nat.Prime p := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Set.Nontrivial.choose_fst_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.choose_fst_mem.h2 : ¬∀ {α : Type} {s : Set α}, s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.choose_mul_factorial_mul_factorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_mul_factorial_mul_factorial.h2 : ¬∀ {n k : ℕ}, n.choose k * k.factorial * (n - k).factorial = n.factorial := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.clog_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_pow.h2 : ¬∀ (b x : ℕ), Nat.clog b (b ^ x) = x := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.clog_of_right_le_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_of_right_le_one.h1 : ¬∀ {n : ℕ} (b : ℕ), Nat.clog b n = 0 := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Nat.sum_le_ofDigits, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sum_le_ofDigits.h2 : ¬∀ {p : ℕ} (L : List ℕ), L.sum ≤ Nat.ofDigits p L := fun hc_h => absurd (@hc_h (0) ([0, 1])) (by
  decide +kernel)

-- Nat.choose_eq_zero_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_eq_zero_of_lt.h2 : ¬∀ {n k : ℕ}, n.choose k = 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.lt_pow_succ_log_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_pow_succ_log_self.h1 : ¬∀ {b : ℕ} (x : ℕ), x < b ^ (Nat.log b x).succ := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.log_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_of_lt.h2 : ¬∀ {b n : ℕ}, Nat.log b n = 0 := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Nat.log_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_pow.h1 : ¬∀ {b : ℕ} (x : ℕ), Nat.log b (b ^ x) = x := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Fin.range_natAdd_castLEEmb, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.range_natAdd_castLEEmb.h2 : ¬∀ {n m : ℕ}, n ≤ m := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Sym.replicate_right_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.replicate_right_injective.h2 : Not (∀ {α : Type} {n : Nat}, @Function.Injective α (Sym α n) (@Sym.replicate α n)) := fun hc_h => absurd (@hc_h (Bool) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.pow_log_le_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_log_le_self.h2 : ¬∀ (b : ℕ) {x : ℕ}, b ^ Nat.log b x ≤ x := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.bijOn_ofDigits', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bijOn_ofDigits'.h1 : ¬∀ {b : ℕ} (l : ℕ), 1 < b := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.log_of_left_le_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_of_left_le_one.h1 : ¬∀ {b : ℕ} (n : ℕ), Nat.log b n = 0 := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Nat.clog_eq_clog_succ_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_eq_clog_succ_iff.h2 : ¬∀ {b n : ℕ}, Nat.clog b n = Nat.clog b (n + 1) ↔ b ^ Nat.clog b n ≠ n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.bijOn_digitsAppend', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bijOn_digitsAppend'.h1 : ¬∀ {b : ℕ} (l : ℕ), 1 < b := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- List.card_fixedLengthDigits, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.card_fixedLengthDigits.h1 : ¬∀ {b : ℕ} (l : ℕ), 1 < b := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- isPrimePow_pow_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.isPrimePow_pow_iff.h2 : ¬∀ {n k : ℕ}, IsPrimePow (n ^ k) ↔ IsPrimePow n := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- Nat.base_pow_length_digits_le', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.base_pow_length_digits_le'.h2 : ¬∀ (b m : ℕ), (b + 2) ^ ((b + 2).digits m).length ≤ (b + 2) * m := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Set.Nonempty.coe_sort, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.coe_sort.h2 : ¬∀ {α : Type} {s : Set α}, Nonempty ↑s := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Nat.prod_primeFactors_dvd_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_primeFactors_dvd_iff.h2 : ¬∀ {n k : ℕ}, ∏ p ∈ n.primeFactors, p ∣ k ↔ n.primeFactors ⊆ k.primeFactors := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- Nat.find_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_eq_zero.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p], ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse)) (by
  simp)

-- List.Lex.asymm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.asymm.h2 : ¬∀ {α : Type} (r : α → α → Prop), Std.Asymm (List.Lex r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.asymm ([0] : List ℕ) ([0] : List ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sym2.infinite_fromRel_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.infinite_fromRel_iff.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sym2.finite_fromRel_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.finite_fromRel_iff.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.sum_fixedLengthDigits_sum, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sum_fixedLengthDigits_sum.h1 : ¬∀ {b : ℕ} (l : ℕ), 1 < b := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.divMaxPow_base_mul, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.divMaxPow_base_mul.h1 : ¬∀ {p : ℕ} (n : ℕ), (p * n).divMaxPow p = n.divMaxPow p := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.divMaxPow_base_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.divMaxPow_base_pow.h1 : ¬∀ {p : ℕ} (k : ℕ), (p ^ k).divMaxPow p = 1 := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- ZMod.eq_zero_iff_gcd_ne_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.eq_zero_iff_gcd_ne_one.h2 : Not
      (∀ {a : Int} {p : Nat},
        Iff
          (@Eq (ZMod p)
            (@Int.cast (ZMod p)
              (@AddGroupWithOne.toIntCast (ZMod p)
                (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p))))
              a)
            (@OfNat.ofNat (ZMod p) (nat_lit 0)
              (@Zero.toOfNat0 (ZMod p)
                (@MulZeroClass.toZero (ZMod p)
                  (@instMulZeroClassOfSemiring (ZMod p)
                    (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p))))))))
          (@Ne Nat (a.gcd (@Nat.cast Int instNatCastInt p)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Nat.exists_most_significant_bit, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_most_significant_bit.h1 : ¬∀ {n : ℕ}, ∃ (i : ℕ), n.testBit i = Bool.true ∧ ∀ (j : ℕ), i < j → n.testBit j = Bool.false := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- ENat.natCast_sInf, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.natCast_sInf.h1 : Not
      (∀ {s : Set Nat},
        @Eq ENat (@Nat.cast ENat ENat.instNatCast (@InfSet.sInf Nat Nat.instInfSet s))
          (⨅ (a : Nat),
            ⨅ (_ : @Membership.mem Nat (Set Nat) (@Set.instMembership Nat) s a), @Nat.cast ENat ENat.instNatCast a)) := fun hc_h => absurd (@hc_h (@Set.ofPred Nat fun (x : Nat) => False)) (by
  simp)

-- Nat.xor_one_of_even, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.xor_one_of_even.h1 : ¬∀ {n : ℕ}, n ^^^ 1 = n + 1 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- EReal.bot_mul_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.bot_mul_of_pos.h1 : ¬∀ {x : EReal}, ⊥ * x = ⊥ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Prime.nat_prime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prime.nat_prime.h1 : ¬∀ {p : ℕ}, Nat.Prime p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- EReal.sub_bot, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_bot.h1 : ¬∀ {x : EReal}, x - ⊥ = ⊤ := fun hc_h => absurd (@hc_h (⊥)) (by
  decide +kernel)

-- Nat.Prime.one_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.one_lt.h1 : ¬∀ {p : ℕ}, 1 < p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Rat.intCast_num_of_den_eq_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.intCast_num_of_den_eq_one.h1 : ¬∀ {q : ℚ}, ↑q.num = q := fun hc_h => absurd (@hc_h (1 / 2)) (by
  decide +kernel)

-- Set.Finite.toFinset_empty, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Finite.toFinset_empty.h1.der.{u} : ∀ {α : Type u}, @Set.Finite α (@EmptyCollection.emptyCollection (Set α) (@Set.instEmptyCollection α)) := by
  (intros; simp; done)
theorem HypCheckProof.Set.Finite.toFinset_empty.h1.{u} : ∀ {α : Type u},
      @Eq (Finset α)
        (@Set.Finite.toFinset α (@EmptyCollection.emptyCollection (Set α) (@Set.instEmptyCollection α))
          (@HypCheckProof.Set.Finite.toFinset_empty.h1.der α))
        (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α)) := by
  intro hc_x0
  exact @Set.Finite.toFinset_empty hc_x0 (@HypCheckProof.Set.Finite.toFinset_empty.h1.der hc_x0)

-- EReal.top_mul_of_neg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.top_mul_of_neg.h1 : ¬∀ {x : EReal}, ⊤ * x = ⊥ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nat.exists_prime_and_dvd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_prime_and_dvd.h1 : ¬∀ {n : ℕ}, ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n := fun hc_h => absurd (@hc_h (1)) (by
  (simp <;> decide))

-- Fin.val_one', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_one'.h1 : ¬∀ (n : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.Prime.minFac_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.minFac_eq.h1 : ¬∀ {p : ℕ}, p.minFac = p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- EReal.add_top_of_ne_bot, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_top_of_ne_bot.h1 : ¬∀ {x : EReal}, x + ⊤ = ⊤ := fun hc_h => absurd (@hc_h (⊥)) (by
  decide +kernel)

-- Nat.four_pow_le_two_mul_self_mul_centralBinom, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.four_pow_le_two_mul_self_mul_centralBinom.h1 : ¬∀ (n : ℕ), 4 ^ n ≤ 2 * n * n.centralBinom := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.ne_zero.h1 : ¬∀ {n : ℕ}, n ≠ 0 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.mem_primeFactors_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mem_primeFactors_self.h1 : ¬∀ {p : ℕ}, p ∈ p.primeFactors := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Int.toNat_pred_coe_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.toNat_pred_coe_of_pos.h1 : ¬∀ {i : ℤ}, ↑(i.toNat - 1) = i - 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.gcdA_zero_right, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcdA_zero_right.h1 : ¬∀ {s : ℕ}, s.gcdA 0 = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Int.natCast_pred_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natCast_pred_of_pos.h1 : Not
      (∀ {n : Nat},
        @Eq Int
          (@Nat.cast Int instNatCastInt
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt n)
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Fin.default_eq_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.default_eq_zero.h1 : ¬∀ (n : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.totient_even, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_even.h1 : ¬∀ {n : ℕ}, Even n.totient := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Nat.totient_prime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_prime.h1 : ¬∀ {p : ℕ}, p.totient = p - 1 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Nat.neZero_totient, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.neZero_totient.h1 : ¬∀ {n : ℕ}, NeZero n.totient := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENat.coe_toNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.coe_toNat.h1 : ¬∀ {n : ℕ∞}, ↑n.toNat = n := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- Rat.inv_intCast_num_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.inv_intCast_num_of_pos.h1 : Not
      (∀ {a : Int},
        @Eq Int (@Inv.inv Rat Rat.instInv (@Int.cast Rat Rat.instIntCast a)).num
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- Bool.eq_true_of_not_eq_false, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.eq_true_of_not_eq_false.h1 : ¬∀ {b : Bool}, b = Bool.true := fun hc_h => absurd (@hc_h (Bool.false)) (by
  decide +kernel)

-- Nat.log2_eq_succ_log2_shiftRight, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log2_eq_succ_log2_shiftRight.h1 : ¬∀ {n : ℕ}, n.log2 = (n >>> 1).log2.succ := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Sym2.instIsEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.instIsEmpty.h1 : ¬∀ {α : Type}, IsEmpty (Sym2 α) := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false (Inhabited.default : Sym2 ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sym2.instSubsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.instSubsingleton.h1 : ¬∀ {α : Type}, Subsingleton (Sym2 α) := fun hc_h => absurd (@hc_h (Bool)) (by
  nofun)

-- ENat.ofNat_eq_natCast_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.ofNat_eq_natCast_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Int.isUnit_sq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.isUnit_sq.h1 : ¬∀ {a : ℤ}, a ^ 2 = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- ENat.lift_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.lift_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.succ_zero_eq_one', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succ_zero_eq_one'.h1 : ¬∀ {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENat.addLECancellable_of_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.addLECancellable_of_ne_top.h1 : ¬∀ {a : ℕ∞}, AddLECancellable a := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- ENat.add_left_injective_of_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_left_injective_of_ne_top.h1 : ¬∀ {n : ℕ∞}, Function.Injective fun (x : ℕ∞) => x + n := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- Nat.AtLeastTwo.one_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.AtLeastTwo.one_lt.h1 : ¬∀ {n : ℕ}, 1 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- NNRat.coe_mk, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.coe_mk.h1 : ¬∀ (q : ℚ), 0 ≤ q := fun hc_h => absurd (@hc_h (-1)) (by
  decide +kernel)

-- Nat.prod_primeFactors_pow_factorization, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_primeFactors_pow_factorization.h1 : ¬∀ {n : ℕ}, n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- PrimeMultiset.toPNatMultiset_ofPNatList, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PrimeMultiset.toPNatMultiset_ofPNatList.h1 : ¬∀ {l : List ℕ+}, ∀ p ∈ l, p.Prime := fun hc_h => absurd (@hc_h ([1])) (by
  simp)

-- ENat.add_right_injective_of_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_right_injective_of_ne_top.h1 : ¬∀ {n : ℕ∞}, Function.Injective fun (x : ℕ∞) => n + x := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- Nat.fib_lt_fib_succ, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.fib_lt_fib_succ.h1 : ¬∀ {n : ℕ}, Nat.fib n < Nat.fib (n + 1) := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- ZMod.nontrivial, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.nontrivial.h1 : ¬∀ (n : ℕ), Nontrivial (ZMod n) := fun hc_h => absurd (@hc_h (1)) (by
  exact fun hc_c =>
    absurd (hc_c.exists_pair_ne)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.Prime.odd_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.odd_iff.h1 : ¬∀ {p : ℕ}, Odd p ↔ 3 ≤ p := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Nat.Coprime.odd_of_left, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.odd_of_left.h1 : ¬∀ {n : ℕ}, Odd n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.AtLeastTwo.prop, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.AtLeastTwo.prop.h1 : ¬∀ {n : ℕ}, 2 ≤ n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- PNat.XgcdType.finish_isSpecial, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.XgcdType.finish_isSpecial.h1 : ¬∀ (u : PNat.XgcdType), u.finish.IsSpecial := fun hc_h => absurd (@hc_h ({ wp := 0, x := 0, y := 0, zp := 1, ap := 0, bp := 0 : PNat.XgcdType })) (by
  nofun)

-- Nat.four_pow_lt_mul_centralBinom, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.four_pow_lt_mul_centralBinom.h1 : ¬∀ (n : ℕ), 4 ^ n < n * n.centralBinom := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.unpair_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.unpair_lt.h1 : ¬∀ {n : ℕ}, (Nat.unpair n).1 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.AtLeastTwo.toNeZero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.AtLeastTwo.toNeZero.h1 : ¬∀ (n : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.Prime.divisors_sq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.divisors_sq.h1 : ¬∀ {p : ℕ}, (p ^ 2).divisors = {p ^ 2, p, 1} := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- EReal.coe_ennreal_toReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.coe_ennreal_toReal.h1 : Not (∀ {x : ENNReal}, @Eq EReal ↑x.toReal ↑x) := fun hc_h => absurd (@hc_h (@Top.top ENNReal ENNReal.instTop)) (by
  decide +kernel)

-- Choose.minFac_sq_ndvd_gcd_choose_of_isPrimePow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.minFac_sq_ndvd_gcd_choose_of_isPrimePow.h1 : ¬∀ {n : ℕ}, ¬n.minFac ^ 2 ∣ (Finset.Icc 1 (n - 1)).gcd n.choose := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.dvd_prod_primeFactors_pow_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_prod_primeFactors_pow_self.h1 : ¬∀ {n : ℕ}, n ∣ (∏ p ∈ n.primeFactors, p) ^ n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- EReal.toENNReal_of_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toENNReal_of_nonpos.h1 : ¬∀ {x : EReal}, x.toENNReal = 0 := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- Int.fib_of_nonneg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.fib_of_nonneg.h1 : ¬∀ {n : ℤ}, Int.fib n = ↑(Nat.fib n.toNat) := fun hc_h => absurd (@hc_h (-1)) (by
  decide +kernel)

-- Fintype.univ_ofIsEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.univ_ofIsEmpty.h1 : ¬∀ {α : Type}, IsEmpty α := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- PNat.Prime.ne_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Prime.ne_one.h1 : ¬∀ {p : ℕ+}, p ≠ 1 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- EReal.coe_toReal_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.coe_toReal_le.h1 : ¬∀ {x : EReal}, ↑x.toReal ≤ x := fun hc_h => absurd (@hc_h (⊥)) (by
  decide +kernel)

-- Nat.Primes.prodNatEquiv_symm_apply, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Primes.prodNatEquiv_symm_apply.h1 : ¬∀ {n : ℕ}, IsPrimePow n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.not_isPrimePow_iff_nontrivial_of_two_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_isPrimePow_iff_nontrivial_of_two_le.h1 : ¬∀ {n : ℕ}, ¬IsPrimePow n ↔ n.primeFactors.Nontrivial := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.bitIndices_sum_map_two_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bitIndices_sum_map_two_pow.h1 : ¬∀ {L : List ℕ}, (List.map (fun (i : ℕ) => 2 ^ i) L).sum.bitIndices = L := fun hc_h => absurd (@hc_h ([1, 0])) (by
  decide +kernel)

-- Multiset.coe_subsingletonEquiv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_subsingletonEquiv.h1 : ¬∀ {α : Type}, Subsingleton α := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.coe_divisors_eq_prod_pow_le_factorization, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coe_divisors_eq_prod_pow_le_factorization.h1 : ¬∀ {n : ℕ}, ↑n.divisors = {x : ℕ | ∃ f ≤ n.factorization, (f.prod fun (x1 x2 : ℕ) => x1 ^ x2) = x} := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- isPrimePow_iff_minFac_pow_factorization_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.isPrimePow_iff_minFac_pow_factorization_eq.h1 : ¬∀ {n : ℕ}, IsPrimePow n ↔ n.minFac ^ n.factorization n.minFac = n := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Fin.natCast_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_self.h1 : ¬∀ (n : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.univ_set_of_isEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.univ_set_of_isEmpty.h1 : Not
      (∀ {α : Type},
        @Eq (Set (Set α)) (@Set.univ (Set α))
          (@Singleton.singleton (Set α) (Set (Set α)) (@Set.instSingletonSet (Set α))
            (@EmptyCollection.emptyCollection (Set α) (@Set.instEmptyCollection α)))) := fun hc_h => absurd (@hc_h (Nat)) (by
  simp)

-- Rat.zero_of_num_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.zero_of_num_zero.h1 : ¬∀ {q : ℚ}, q = 0 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- PNat.toPNat'_coe, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.toPNat'_coe.h1 : ¬∀ {n : ℕ}, ↑n.toPNat' = n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.sqrt_lt_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sqrt_lt_self.h1 : ¬∀ {n : ℕ}, n.sqrt < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Set.infinite_univ, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_univ.h1 : Not (∀ {α : Type}, @Set.Infinite α (@Set.univ α)) := fun hc_h => absurd (@hc_h (Bool)) (by
  simp)

-- Odd.coprime_two_right, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Odd.coprime_two_right.h1 : ¬∀ {n : ℕ}, n.Coprime 2 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.eq_two_or_odd', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.eq_two_or_odd'.h1 : ¬∀ {p : ℕ}, p = 2 ∨ Odd p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Coprime.odd_of_right, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.odd_of_right.h1 : ¬∀ {n : ℕ}, Odd n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.pred_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pred_pos.h1 : ¬∀ {p : ℕ}, 0 < p.pred := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.odd_of_mod_four_eq_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.odd_of_mod_four_eq_one.h1 : ¬∀ {n : ℕ}, n % 2 = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Rat.coe_int_num_of_den_eq_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.coe_int_num_of_den_eq_one.h1 : ¬∀ {q : ℚ}, ↑q.num = q := fun hc_h => absurd (@hc_h (1 / 2)) (by
  decide +kernel)

-- Matrix.empty_vecAlt0, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Matrix.empty_vecAlt0.h1.der.{u_1} : ∀ (α : Type u_1),
      @Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  (intros; trivial)
theorem HypCheckProof.Matrix.empty_vecAlt0.h1.{u_1} : ∀ (α : Type u_1),
      @Eq (Fin (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → α)
        (@Matrix.vecAlt0 α (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (HypCheckProof.Matrix.empty_vecAlt0.h1.der α)
          (@Matrix.vecEmpty α))
        (@Matrix.vecEmpty α) := by
  intro hc_x0
  exact @Matrix.empty_vecAlt0 hc_x0 (@HypCheckProof.Matrix.empty_vecAlt0.h1.der hc_x0)

-- Fin.castPred_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_one.h1 : ¬∀ {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- PNat.natPred_eq_pred, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.natPred_eq_pred.h1 : ¬∀ {n : ℕ}, 0 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Matrix.empty_vecAlt1, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Matrix.empty_vecAlt1.h1.der.{u_1} : ∀ (α : Type u_1),
      @Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  (intros; trivial)
theorem HypCheckProof.Matrix.empty_vecAlt1.h1.{u_1} : ∀ (α : Type u_1),
      @Eq (Fin (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → α)
        (@Matrix.vecAlt1 α (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (HypCheckProof.Matrix.empty_vecAlt1.h1.der α)
          (@Matrix.vecEmpty α))
        (@Matrix.vecEmpty α) := by
  intro hc_x0
  exact @Matrix.empty_vecAlt1 hc_x0 (@HypCheckProof.Matrix.empty_vecAlt1.h1.der hc_x0)

-- Nat.prime_zero_false, hypothesis 0: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_zero_false.h0 : ¬False := fun hc_h => absurd (@hc_h ) (by
  decide +kernel)

-- PNat.mk_one, hypothesis 0: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.PNat.mk_one.h0.der : 0 < 1 := by
  (intros; trivial)
theorem HypCheckProof.PNat.mk_one.h0 : (⟨1, HypCheckProof.PNat.mk_one.h0.der⟩ : { n : ℕ // 0 < n }) = 1 := by
  exact @PNat.mk_one (@HypCheckProof.PNat.mk_one.h0.der )

