import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Finset.map_sort, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.map_sort.h7.inst : ¬Std.Antisymm fun (x x_1 : Bool) => True := by
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
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.map_sort.h7.prem0 : ∀ a ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool },
      ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool },
        (fun (x x_1 : Bool) => True) a b ↔
          (fun (a b : ℕ) => a ≤ b)
            ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0,
                inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ ℕ }
              a)
            ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0,
                inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ ℕ }
              b) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.map_sort.h7 : ¬∀ {α β : Type} (f : α ↪ β) (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r]
        [inst : Std.Total r] (r' : β → β → Prop) [inst : DecidableRel r'] [inst : IsTrans β r'] [inst : Std.Antisymm r']
        [inst : Std.Total r'], (∀ a ∈ s, ∀ b ∈ s, r a b ↔ r' (f a) (f b)) → Std.Antisymm r := fun hc_h => HypCheckProof.Finset.map_sort.h7.inst (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun (x x_1 : Bool) => True) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (fun (a b : ℕ) => a ≤ b) (Nat.decLe) _ (@Std.Antisymm.mk (Nat) (fun (a b : Nat) => @LE.le Nat instLENat a b) (by (try dsimp only);   (intros; omega))) _ HypCheckProof.Finset.map_sort.h7.prem0)

-- Ordnode.Valid'.node3R, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node3R.h10 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α} {o₁ : WithBot α}
        {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x →
          Ordnode.Valid' (↑y) r o₂ →
            Ordnode.BalancedSz l.size (m.size + r.size + 1) →
              Ordnode.BalancedSz m.size r.size → Ordnode.Valid' o₁ (l.node3R x m y r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (Ordnode.nil) (0) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.balanceL_aux, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balanceL_aux.h7 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑x) r o₂ →
          (l.size = 0 → r.size ≤ 1) →
            (1 ≤ l.size → 1 ≤ r.size → r.size ≤ Ordnode.delta * l.size) →
              2 * l.size ≤ 9 * r.size + 5 ∨ l.size ≤ 3 → Ordnode.Valid' o₁ (l.balanceL x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.balanceL_aux, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balanceL_aux.h8 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x →
          (l.size = 0 → r.size ≤ 1) →
            (1 ≤ l.size → 1 ≤ r.size → r.size ≤ Ordnode.delta * l.size) →
              2 * l.size ≤ 9 * r.size + 5 ∨ l.size ≤ 3 → Ordnode.Valid' o₁ (l.balanceL x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (Ordnode.nil) (0) (0) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide) (by
  decide)) (by
  nofun)

-- Finset.sort_insert, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_insert.h5.inst : ¬Std.Antisymm fun (x x_1 : Bool) => True := by
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
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_insert.h5.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool },
      (fun (x x_1 : Bool) => True) Bool.false b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_insert.h5.prem1 : Bool.false ∉ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool } := by
  decide
theorem HypCheckProof.Finset.sort_insert.h5 : ¬∀ {α : Type} {s : Finset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r]
        [inst : DecidableEq α] {a : α}, (∀ b ∈ s, r a b) → a ∉ s → Std.Antisymm r := fun hc_h => HypCheckProof.Finset.sort_insert.h5.inst (@hc_h (Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun (x x_1 : Bool) => True) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (instDecidableEqBool) (Bool.false) HypCheckProof.Finset.sort_insert.h5.prem0 HypCheckProof.Finset.sort_insert.h5.prem1)

-- Finset.sort_insert, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_insert.h6.inst : ¬Std.Total fun (a b : ℕ) => a < b := by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_insert.h6.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }, (fun (a b : ℕ) => a < b) 0 b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_insert.h6.prem1 : 0 ∉ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ } := by
  decide
theorem HypCheckProof.Finset.sort_insert.h6 : ¬∀ {α : Type} {s : Finset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r]
        [inst : DecidableEq α] {a : α}, (∀ b ∈ s, r a b) → a ∉ s → Std.Total r := fun hc_h => HypCheckProof.Finset.sort_insert.h6.inst (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a b : ℕ) => a < b) (Nat.decLt) _ _ (instDecidableEqNat) (0) HypCheckProof.Finset.sort_insert.h6.prem0 HypCheckProof.Finset.sort_insert.h6.prem1)

-- Ordnode.Valid'.balance'_aux, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balance'_aux.h7 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑x) r o₂ →
          2 * r.size ≤ 9 * l.size + 5 ∨ r.size ≤ 3 →
            2 * l.size ≤ 9 * r.size + 5 ∨ l.size ≤ 3 → Ordnode.Valid' o₁ (l.balance' x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.balance'_aux, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balance'_aux.h8 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x →
          2 * r.size ≤ 9 * l.size + 5 ∨ r.size ≤ 3 →
            2 * l.size ≤ 9 * r.size + 5 ∨ l.size ≤ 3 → Ordnode.Valid' o₁ (l.balance' x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (Ordnode.nil) (0) (0) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide)) (by
  nofun)

-- Cycle.forall_eq_of_chain, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.forall_eq_of_chain.h5 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : IsTrans α r] [inst : Std.Antisymm r] {a b : α},
        a ∈ s → b ∈ s → a = b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ((([0, 1] : List Nat) : Cycle Nat) : Cycle ℕ) _ _ (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Cycle.forall_eq_of_chain, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.forall_eq_of_chain.h8 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : IsTrans α r] [inst : Std.Antisymm r],
        Cycle.Chain r s → ∀ {a b : α}, b ∈ s → a = b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) _ _ (by
  simp) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Cycle.forall_eq_of_chain, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.forall_eq_of_chain.h9 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : IsTrans α r] [inst : Std.Antisymm r],
        Cycle.Chain r s → ∀ {a b : α}, a ∈ s → a = b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) _ _ (by
  simp) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.fold_disjiUnion, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_disjiUnion.h4.inst : Not (@Std.Commutative Nat fun (a x : Nat) => a) := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_disjiUnion.h4.prem0 : @Set.PairwiseDisjoint (Finset Nat) Nat (@Finset.instPartialOrder Nat) (@Finset.instOrderBot Nat)
      (@SetLike.coe (Finset Nat) Nat (@Finset.instSetLike Nat)
        (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
          (@of_decide_eq_true
            (@Multiset.Nodup Nat
              (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
            (@Multiset.nodupDecidable Nat instDecidableEqNat
              (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@Multiset.Nodup Nat
                    (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                  (@Multiset.nodupDecidable Nat instDecidableEqNat
                    (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
                Bool.true)
              (@Eq.refl Bool Bool.true)))))
      fun (a : Nat) =>
      @Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
        (@of_decide_eq_true
          (@Multiset.Nodup Nat
            (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
          (@Multiset.nodupDecidable Nat instDecidableEqNat
            (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
          (@id
            (@Eq Bool
              (@Decidable.decide
                (@Multiset.Nodup Nat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                (@Multiset.nodupDecidable Nat instDecidableEqNat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
              Bool.true)
            (@Eq.refl Bool Bool.true))) := by
  simp
theorem HypCheckProof.Finset.fold_disjiUnion.h4 : Not
      (∀ {α β : Type} {f : α → β} {op : β → β → β} [ha : @Std.Associative β op] {ι : Type} {s : Finset ι} {t : ι → Finset α}
        {b : ι → β} {b₀ : β},
        @Set.PairwiseDisjoint (Finset α) ι (@Finset.instPartialOrder α) (@Finset.instOrderBot α)
            (@SetLike.coe (Finset ι) ι (@Finset.instSetLike ι) s) t →
          @Std.Commutative β op) := fun hc_h => HypCheckProof.Finset.fold_disjiUnion.h4.inst (@hc_h (Nat) (Nat) (fun (n : Nat) =>
      @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (fun (a x : Nat) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun (a : Nat) =>
      @Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
        (@of_decide_eq_true
          (@Multiset.Nodup Nat
            (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
          (@Multiset.nodupDecidable Nat instDecidableEqNat
            (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
          (@id
            (@Eq Bool
              (@Decidable.decide
                (@Multiset.Nodup Nat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                (@Multiset.nodupDecidable Nat instDecidableEqNat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
              Bool.true)
            (@Eq.refl Bool Bool.true)))) (fun (n : Nat) =>
      @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Finset.fold_disjiUnion.h4.prem0)

-- Finset.fold_disjiUnion, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_disjiUnion.h5 : Not
      (∀ {α β : Type} {f : α → β} {op : β → β → β} [hc : @Std.Commutative β op] {ι : Type} {s : Finset ι} {t : ι → Finset α}
        {b : ι → β} {b₀ : β},
        @Set.PairwiseDisjoint (Finset α) ι (@Finset.instPartialOrder α) (@Finset.instOrderBot α)
            (@SetLike.coe (Finset ι) ι (@Finset.instSetLike ι) s) t →
          @Std.Associative β op) := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun n => n % 2 == 0 : Nat → Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun (a : Nat) =>
      @Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
        (@of_decide_eq_true
          (@Multiset.Nodup Nat
            (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
          (@Multiset.nodupDecidable Nat instDecidableEqNat
            (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
          (@id
            (@Eq Bool
              (@Decidable.decide
                (@Multiset.Nodup Nat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                (@Multiset.nodupDecidable Nat instDecidableEqNat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
              Bool.true)
            (@Eq.refl Bool Bool.true)))) (fun n => n % 2 == 0 : Nat → Bool) (Bool.false) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.noncommProd_induction, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.noncommProd_induction.h8 : Not
      (∀ {α β : Type} [inst : Monoid β] (s : Finset α) (f : α → β)
        (comm :
          @Set.Pairwise α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
            (@Function.onFun α β Prop
              (@Commute β (@MulOne.toMul β (@MulOneClass.toMulOne β (@Monoid.toMulOneClass β inst)))) f))
        (p : β → Prop),
        (∀ (a b : β),
            p a →
              p b →
                p
                  (@HMul.hMul β β β (@instHMul β (@MulOne.toMul β (@MulOneClass.toMulOne β (@Monoid.toMulOneClass β inst))))
                    a b)) →
          (∀ (x : α),
              @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x → p (f x)) →
            p (@Finset.noncommProd α β inst s f comm)) := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (Nat.instMonoid) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) hc_k0 (fun n => n = 0 : Nat → Prop) hc_k1 hc_k2) (by
  (simp <;> omega))

-- Finset.noncommSum_induction, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.noncommSum_induction.h8 : Not
      (∀ {α β : Type} [inst : AddMonoid β] (s : Finset α) (f : α → β)
        (comm :
          @Set.Pairwise α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
            (@Function.onFun α β Prop
              (@AddCommute β (@AddZero.toAdd β (@AddZeroClass.toAddZero β (@AddMonoid.toAddZeroClass β inst)))) f))
        (p : β → Prop),
        (∀ (a b : β),
            p a →
              p b →
                p
                  (@HAdd.hAdd β β β
                    (@instHAdd β (@AddZero.toAdd β (@AddZeroClass.toAddZero β (@AddMonoid.toAddZeroClass β inst)))) a b)) →
          (∀ (x : α),
              @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x → p (f x)) →
            p (@Finset.noncommSum α β inst s f comm)) := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (Nat.instAddMonoid) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) hc_k0 (fun _ => False : Nat → Prop) hc_k1 hc_k2) (by
  simp)

-- Finset.fold_op_rel_iff_or, hypothesis 4: necessary
/- FAILED: 4:3: `simp` made no progress | 19:3: `simp` made no progress | 4:3: `simp` made no progress | 5:3: `simp` made no progress | 15:445: don't know how to synthesize implicit argument `z`
  @h4.prem0 (?m.29 hc_h) (?m.30 hc_h) (?m.31 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∨ r x z) → ∀ {c : β}, Std.Associative op
x✝ y✝ z✝ : Bool
⊢ Bool | 33:68: don't know how to synthesize implicit argument `z`
  @h4.prem0 (?m.10 hc_h) (?m.11 hc_h) (?m.12 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∨ r x z) → ∀ {c : β}, Std.Associative op
x✝ y✝ z✝ : Bool
⊢ Bool | 15:511: don't know how to synthesize implicit argument `z`
  @h4.prem0 (?m.27 hc_h) (?m.28 hc_h) (?m.29 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∨ r x z) → ∀ {c : β}, Std.Associative op
x✝ y✝ z✝ : Bool
⊢ Bool | 19:334: don't know how to synthesize implicit argument `z`
  @h4.prem0 (?m.12 hc_h) (?m.13 hc_h) (?m.14 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∨ r x z) → ∀ {c : β}, Std.Associative op
x✝ y✝ z✝ : Bool
⊢ Bool
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_op_rel_iff_or.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
        (∀ {x y z : β}, r x (op y z) ↔ r x y ∨ r x z) → ∀ {c : β}, Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun _ _ => True : Bool → Bool → Prop) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))
-/

-- Finset.fold_insert, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_insert.h3.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_insert.h3.prem0 : 0 ∉ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ } := by
  decide
theorem HypCheckProof.Finset.fold_insert.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α} {a : α}
        [inst : DecidableEq α], a ∉ s → Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_insert.h3.inst (@hc_h (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (instDecidableEqNat) HypCheckProof.Finset.fold_insert.h3.prem0)

-- Finset.fold_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_insert.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {a : α}
        [inst : DecidableEq α], a ∉ s → Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (instDecidableEqNat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.fold_cons, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_cons.h3.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_cons.h3.prem0 : 0 ∉ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ } := by
  decide
theorem HypCheckProof.Finset.fold_cons.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α} {a : α},
        a ∉ s → Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_cons.h3.inst (@hc_h (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) HypCheckProof.Finset.fold_cons.h3.prem0)

-- Finset.fold_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_cons.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {a : α},
        a ∉ s → Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.fold_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_congr.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {g : α → β},
        (∀ x ∈ s, f x = g x) → Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finsupp.le_weight_of_ne_zero', hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.le_weight_of_ne_zero'.h9 : ¬∀ {σ M : Type} [inst : AddCommMonoid M] [inst_1 : PartialOrder M] [inst_2 : IsOrderedAddMonoid M]
        [inst_3 : CanonicallyOrderedAdd M] (w : σ → M) {s : σ} {f : σ →₀ ℕ}, w s ≤ (Finsupp.weight w) f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instAddCommMonoid) (Nat.instPartialOrder) _ _ (fun n => n + 1 : ℕ → ℕ) (0) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  decide +kernel)

-- Finset.mul_noncommProd_erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mul_noncommProd_erase.h6 : Not
      (∀ {α β : Type} [inst : Monoid β] [inst_1 : DecidableEq α] (s : Finset α) {a : α} (f : α → β)
        (comm :
          @Set.Pairwise α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
            (@Function.onFun α β Prop
              (@Commute β (@MulOne.toMul β (@MulOneClass.toMulOne β (@Monoid.toMulOneClass β inst)))) f))
        (comm' :
          optParam
            (∀ (x : α),
              @Membership.mem α (Set α) (@Set.instMembership α)
                  (@SetLike.coe (Finset α) α (@Finset.instSetLike α) (@Finset.erase α inst_1 s a)) x →
                ∀ (x_1 : α),
                  @Membership.mem α (Set α) (@Set.instMembership α)
                      (@SetLike.coe (Finset α) α (@Finset.instSetLike α) (@Finset.erase α inst_1 s a)) x_1 →
                    @Ne α x x_1 →
                      @Function.onFun α β Prop
                        (@Commute β (@MulOne.toMul β (@MulOneClass.toMulOne β (@Monoid.toMulOneClass β inst)))) f x x_1)
            fun (x : α)
              (hx :
                @Membership.mem α (Set α) (@Set.instMembership α)
                  (@SetLike.coe (Finset α) α (@Finset.instSetLike α) (@Finset.erase α inst_1 s a)) x)
              (x_1 : α)
              (hy :
                @Membership.mem α (Set α) (@Set.instMembership α)
                  (@SetLike.coe (Finset α) α (@Finset.instSetLike α) (@Finset.erase α inst_1 s a)) x_1)
              (hxy : @Ne α x x_1) =>
            @comm x (@Finset.mem_of_mem_erase α inst_1 s a x hx) x_1 (@Finset.mem_of_mem_erase α inst_1 s a x_1 hy) hxy),
        @Eq β
          (@HMul.hMul β β β (@instHMul β (@MulOne.toMul β (@MulOneClass.toMulOne β (@Monoid.toMulOneClass β inst)))) (f a)
            (@Finset.noncommProd α β inst (@Finset.erase α inst_1 s a) f comm'))
          (@Finset.noncommProd α β inst s f comm)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (Nat.instMonoid) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun _ => 0 : Nat → Nat) hc_k0 hc_k1) (by
  simp)

-- Finset.noncommProd_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.noncommProd_congr.h7 : Not
      (∀ {α β : Type} [inst : Monoid β] {s₁ s₂ : Finset α} {f g : α → β},
        (∀ (x : α),
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s₂ x →
              @Eq β (f x) (g x)) →
          @Set.Pairwise α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s₁)
              (@Function.onFun α β Prop
                (@Commute β (@MulOne.toMul β (@MulOneClass.toMulOne β (@Monoid.toMulOneClass β inst)))) f) →
            @Eq (Finset α) s₁ s₂) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat.instMonoid) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp)) (by
  decide +kernel)

-- Multiset.foldl_induction, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldl_induction.h2.inst : Not (@RightCommutative Bool Bool fun (a b : Bool) => a.not.or b) := by
  exact fun hc_c =>
    absurd (hc_c.right_comm (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldl_induction.h2.prem0 : ∀ (a b : Bool),
      @Eq Bool a Bool.true →
        @Eq Bool b Bool.true → (fun (b : Bool) => @Eq Bool b Bool.true) ((fun (a b : Bool) => a.not.or b) b a) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldl_induction.h2.prem1 : (fun (b : Bool) => @Eq Bool b Bool.true) Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldl_induction.h2.prem2 : ∀ (a : Bool),
      @Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
          (@OfNat.ofNat (Multiset Bool) (nat_lit 0) (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool))) a →
        (fun (b : Bool) => @Eq Bool b Bool.true) a := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Multiset.foldl_induction.h2 : Not
      (∀ {α : Type} (f : α → α → α) (x : α) (p : α → Prop) (s : Multiset α),
        (∀ (a b : α), p a → p b → p (f b a)) →
          p x →
            (∀ (a : α), @Membership.mem α (Multiset α) (@Multiset.instMembership α) s a → p a) → @RightCommutative α α f) := fun hc_h => HypCheckProof.Multiset.foldl_induction.h2.inst (@hc_h (Bool) (fun (a b : Bool) => a.not.or b) (Bool.true) (fun (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat (Multiset Bool) (nat_lit 0) (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool))) HypCheckProof.Multiset.foldl_induction.h2.prem0 HypCheckProof.Multiset.foldl_induction.h2.prem1 HypCheckProof.Multiset.foldl_induction.h2.prem2)

-- Multiset.foldl_induction, hypothesis 7: necessary
/- FAILED: 5:3: `simp` made no progress | 8:3: `simp` made no progress | 5:3: `simp` made no progress | 8:3: `simp` made no progress | 2:82: failed to synthesize instance of type class
  RightCommutative fun a b => a - b

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 62:25: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 2:82: failed to synthesize instance of type class
  RightCommutative fun a b => a - b

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 4:192: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldl_induction.h7 : ¬∀ {α : Type} (f : α → α → α) [inst : RightCommutative f] (x : α) (p : α → Prop) (s : Multiset α),
        (∀ (a b : α), p a → p b → p (f b a)) → (∀ a ∈ s, p a) → p (Multiset.foldl f x s) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (@RightCommutative.mk (Nat) (Nat) (fun (a b : Nat) => @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b) (by (try dsimp only);   grind)) (1) (fun n => n = 0 : ℕ → Prop) ((0 : Multiset Nat) : Multiset ℕ) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

-- Finset.inf'_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_congr.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s t : Finset β} {f g : β → α}, s = t → (∀ x ∈ s, f x = g x) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) _ ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) rfl (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.inf'_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_congr.h8 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β},
        @Finset.Nonempty β s →
          ∀ {t : Finset β} {f g : β → α},
            (∀ (x : β),
                @Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β)) s x →
                  @Eq α (f x) (g x)) →
              @Eq (Finset β) s t) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.inf'_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_congr.h9 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (H : @Finset.Nonempty β s) {t : Finset β} {f g : β → α}
        (h₁ : @Eq (Finset β) s t),
        @Eq α (@Finset.inf' α β inst s H f)
          (@Finset.inf' α β inst t
            (@Eq.rec (Finset β) s (fun (x : Finset β) (h : @Eq (Finset β) s x) => @Finset.Nonempty β x) H t h₁) g)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) _ hc_k0 (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat) rfl) (by
  decide +kernel)

-- Ordnode.Valid'.glue, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.glue.h7 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑x) r o₂ →
          Ordnode.BalancedSz l.size r.size → Ordnode.Valid' o₁ (l.glue r) o₂ ∧ (l.glue r).size = l.size + r.size := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (Ordnode.nil) (1) (1) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.glue, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.glue.h8 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x →
          Ordnode.BalancedSz l.size r.size → Ordnode.Valid' o₁ (l.glue r) o₂ ∧ (l.glue r).size = l.size + r.size := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (Ordnode.nil) (0) (0) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.node', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node'.h7 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑x) r o₂ → Ordnode.BalancedSz l.size r.size → Ordnode.Valid' o₁ (l.node' x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.node', hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node'.h8 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x → Ordnode.BalancedSz l.size r.size → Ordnode.Valid' o₁ (l.node' x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (Ordnode.nil) (0) (0) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Finset.inf_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_mem.h4.inst : ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.inf fun (n : ℕ) => n % 2 == 0) ∉
      {b : Bool | b = Bool.false} := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_mem.h4.prem0 : ∀ x ∈ {b : Bool | b = Bool.false}, ∀ y ∈ {b : Bool | b = Bool.false}, Min.min x y ∈ {b : Bool | b = Bool.false} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_mem.h4.prem1 : ∀ i ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      (fun (n : ℕ) => n % 2 == 0) i ∈ {b : Bool | b = Bool.false} := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.inf_mem.h4 : ¬∀ {α : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] (s : Set α),
        (∀ x ∈ s, ∀ y ∈ s, x ⊓ y ∈ s) → ∀ {ι : Type} (t : Finset ι) (p : ι → α), (∀ i ∈ t, p i ∈ s) → t.inf p ∈ s := fun hc_h => HypCheckProof.Finset.inf_mem.h4.inst (@hc_h (Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({b : Bool | b = Bool.false}) HypCheckProof.Finset.inf_mem.h4.prem0 (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n % 2 == 0) HypCheckProof.Finset.inf_mem.h4.prem1)

-- Finset.inf_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_mem.h9 : Not
      (∀ {α : Type} [inst : SemilatticeInf α]
        [inst_1 : @OrderTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))]
        (s : Set α),
        @Membership.mem α (Set α) (@Set.instMembership α) s
            (@Top.top α
              (@OrderTop.toTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))
                inst_1)) →
          (∀ (x : α),
              @Membership.mem α (Set α) (@Set.instMembership α) s x →
                ∀ (y : α),
                  @Membership.mem α (Set α) (@Set.instMembership α) s y →
                    @Membership.mem α (Set α) (@Set.instMembership α) s (@Min.min α (@SemilatticeInf.toMin α inst) x y)) →
            ∀ {ι : Type} (t : Finset ι) (p : ι → α),
              @Membership.mem α (Set α) (@Set.instMembership α) s (@Finset.inf α ι inst inst_1 t p)) := fun hc_h => absurd (@hc_h (Bool) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@CoheytingAlgebra.toOrderTop Bool
      (@Order.Coframe.toCoheytingAlgebra Bool
        (@CompleteDistribLattice.toCoframe Bool
          (@CompleteBooleanAlgebra.toCompleteDistribLattice Bool Bool.completeBooleanAlgebra)))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (by
  decide) (by
  decide) (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Finset.sup'_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_congr.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s t : Finset β} {f g : β → α}, s = t → (∀ x ∈ s, f x = g x) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) _ ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) rfl (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.sup'_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_congr.h8 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β},
        @Finset.Nonempty β s →
          ∀ {t : Finset β} {f g : β → α},
            (∀ (x : β),
                @Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β)) s x →
                  @Eq α (f x) (g x)) →
              @Eq (Finset β) s t) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.sup'_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_congr.h9 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (H : @Finset.Nonempty β s) {t : Finset β} {f g : β → α}
        (h₁ : @Eq (Finset β) s t),
        @Eq α (@Finset.sup' α β inst s H f)
          (@Finset.sup' α β inst t
            (@Eq.rec (Finset β) s (fun (x : Finset β) (h : @Eq (Finset β) s x) => @Finset.Nonempty β x) H t h₁) g)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) _ hc_k0 (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat) rfl) (by
  decide +kernel)

-- Finset.inf_induction, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_induction.h7.inst : ¬(fun (b : Bool) => b = Bool.false)
        ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.inf fun (n : ℕ) => n % 2 == 0) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_induction.h7.prem0 : ∀ (a₁ : Bool), a₁ = Bool.false → ∀ (a₂ : Bool), a₂ = Bool.false → (fun (b : Bool) => b = Bool.false) (Min.min a₁ a₂) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_induction.h7.prem1 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      (fun (b : Bool) => b = Bool.false) ((fun (n : ℕ) => n % 2 == 0) b) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.inf_induction.h7 : ¬∀ {α β : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {p : α → Prop},
        (∀ (a₁ : α), p a₁ → ∀ (a₂ : α), p a₂ → p (a₁ ⊓ a₂)) → (∀ b ∈ s, p (f b)) → p (s.inf f) := fun hc_h => HypCheckProof.Finset.inf_induction.h7.inst (@hc_h (Bool) (ℕ) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n % 2 == 0) (fun (b : Bool) => b = Bool.false) HypCheckProof.Finset.inf_induction.h7.prem0 HypCheckProof.Finset.inf_induction.h7.prem1)

-- Finset.inf_induction, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_induction.h9.inst : Not
      ((fun (b : Bool) => @Eq Bool b Bool.true)
        (@Finset.inf Bool Nat
          (@Lattice.toSemilatticeInf Bool
            (@ConditionallyCompleteLattice.toLattice Bool
              (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
                (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
                  (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder)))))
          (@CoheytingAlgebra.toOrderTop Bool
            (@Order.Coframe.toCoheytingAlgebra Bool
              (@CompleteDistribLattice.toCoframe Bool
                (@CompleteBooleanAlgebra.toCompleteDistribLattice Bool Bool.completeBooleanAlgebra))))
          (@Finset.mk Nat
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@of_decide_eq_true
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@Multiset.Nodup Nat
                      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Multiset.nodupDecidable Nat instDecidableEqNat
                      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  Bool.true)
                (@Eq.refl Bool Bool.true))))
          fun (n : Nat) =>
          @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_induction.h9.prem0 : (fun (b : Bool) => @Eq Bool b Bool.true)
      (@Top.top Bool
        (@OrderTop.toTop Bool
          (@Preorder.toLE Bool
            (@PartialOrder.toPreorder Bool
              (@SemilatticeInf.toPartialOrder Bool
                (@Lattice.toSemilatticeInf Bool
                  (@ConditionallyCompleteLattice.toLattice Bool
                    (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
                      (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
                        (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))))))
          (@CoheytingAlgebra.toOrderTop Bool
            (@Order.Coframe.toCoheytingAlgebra Bool
              (@CompleteDistribLattice.toCoframe Bool
                (@CompleteBooleanAlgebra.toCompleteDistribLattice Bool Bool.completeBooleanAlgebra)))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_induction.h9.prem1 : ∀ (a₁ : Bool),
      @Eq Bool a₁ Bool.true →
        ∀ (a₂ : Bool),
          @Eq Bool a₂ Bool.true →
            (fun (b : Bool) => @Eq Bool b Bool.true)
              (@Min.min Bool
                (@SemilatticeInf.toMin Bool
                  (@Lattice.toSemilatticeInf Bool
                    (@ConditionallyCompleteLattice.toLattice Bool
                      (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
                        (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
                          (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))))
                a₁ a₂) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.inf_induction.h9 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α]
        [inst_1 : @OrderTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))]
        {s : Finset β} {f : β → α} {p : α → Prop},
        p
            (@Top.top α
              (@OrderTop.toTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))
                inst_1)) →
          (∀ (a₁ : α), p a₁ → ∀ (a₂ : α), p a₂ → p (@Min.min α (@SemilatticeInf.toMin α inst) a₁ a₂)) →
            p (@Finset.inf α β inst inst_1 s f)) := fun hc_h => HypCheckProof.Finset.inf_induction.h9.inst (@hc_h (Bool) (Nat) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@CoheytingAlgebra.toOrderTop Bool
      (@Order.Coframe.toCoheytingAlgebra Bool
        (@CompleteDistribLattice.toCoframe Bool
          (@CompleteBooleanAlgebra.toCompleteDistribLattice Bool Bool.completeBooleanAlgebra)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun (n : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (b : Bool) => @Eq Bool b Bool.true) HypCheckProof.Finset.inf_induction.h9.prem0 HypCheckProof.Finset.inf_induction.h9.prem1)

-- Finsupp.mapRange_mapRange, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mapRange_mapRange.h9 : ¬∀ {α M N O : Type} [inst : Zero M] [inst_1 : Zero N] [inst_2 : Zero O] (e₁ : N → O) (e₂ : M → N),
        e₂ 0 = 0 → ∀ (f : α →₀ M), e₁ 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  decide +kernel)

-- Finsupp.mapRange_mapRange, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mapRange_mapRange.h10 : ¬∀ {α M N O : Type} [inst : Zero M] [inst_1 : Zero N] [inst_2 : Zero O] (e₁ : N → O) (e₂ : M → N),
        e₁ 0 = 0 → ∀ (f : α →₀ M), e₂ 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  decide +kernel)

-- Finset.apply_inf_eq_inf_comp_of_linearOrder, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.apply_inf_eq_inf_comp_of_linearOrder.h11 : ¬∀ {α β ι : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] {s : Finset ι} {f : ι → α} [inst_2 : SemilatticeInf β]
        [inst_3 : OrderTop β] (g : α → β), Monotone g → g (s.inf f) = s.inf (g ∘ f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) (fun _ => false : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Finset.apply_sup_eq_sup_comp, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.apply_sup_eq_sup_comp.h11 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] [inst_2 : SemilatticeSup γ] [inst_3 : OrderBot γ]
        {s : Finset β} {f : β → α} (g : α → γ), (∀ (x y : α), g (x ⊔ y) = g x ⊔ g y) → g (s.sup f) = s.sup (g ∘ f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  grind)) (by
  decide +kernel)

-- Ordnode.Bounded.of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.of_lt.h6 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α} {x : α},
        Ordnode.nil.Bounded o₁ ↑x → Ordnode.All (fun (x_1 : α) => x_1 < x) t → t.Bounded o₁ ↑x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Ordnode.Bounded.of_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.of_lt.h7 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α} {x : α},
        t.Bounded o₁ o₂ → Ordnode.All (fun (x_1 : α) => x_1 < x) t → t.Bounded o₁ ↑x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (1) (0) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Finset.sup'_mem, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup'_mem.h6.inst : ¬{ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.Nonempty := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup'_mem.h6.prem0 : ∀ x ∈ {n : ℕ | n = 0}, ∀ y ∈ {n : ℕ | n = 0}, Max.max x y ∈ {n : ℕ | n = 0} := by
  grind
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup'_mem.h6.prem1 : ∀ i ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      (fun (n : ℕ) => n + 1) i ∈ {n : ℕ | n = 0} := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sup'_mem.h6 : ¬∀ {α : Type} [inst : SemilatticeSup α] (s : Set α),
        (∀ x ∈ s, ∀ y ∈ s, x ⊔ y ∈ s) → ∀ {ι : Type} (t : Finset ι) (p : ι → α), (∀ i ∈ t, p i ∈ s) → t.Nonempty := fun hc_h => HypCheckProof.Finset.sup'_mem.h6.inst (@hc_h (ℕ) (Nat.instLattice.toSemilatticeSup) ({n : ℕ | n = 0}) HypCheckProof.Finset.sup'_mem.h6.prem0 (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) HypCheckProof.Finset.sup'_mem.h6.prem1)

-- Finset.fold_disjSum, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_disjSum.h9.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
theorem HypCheckProof.Finset.fold_disjSum.h9 : ¬∀ {α β γ : Type} (s : Finset α) (t : Finset β) (f : α ⊕ β → γ) (b₁ b₂ : γ) (op : γ → γ → γ)
        [inst : Std.Associative op], Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_disjSum.h9.inst (@hc_h (ℕ) (ℕ) (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ ⊕ ℕ) => 0) (0) (0) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))))

-- Finset.fold_disjSum, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_disjSum.h10 : ¬∀ {α β γ : Type} (s : Finset α) (t : Finset β) (f : α ⊕ β → γ) (b₁ b₂ : γ) (op : γ → γ → γ)
        [inst : Std.Commutative op], Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ ⊕ ℕ) => Bool.false) (Bool.false) (Bool.false) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.fold_union_inter, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_union_inter.h3.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
theorem HypCheckProof.Finset.fold_union_inter.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} [inst : DecidableEq α] {s₁ s₂ : Finset α}
        {b₁ b₂ : β}, Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_union_inter.h3.inst (@hc_h (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0))

-- Finset.fold_union_inter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_union_inter.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} [inst : DecidableEq α] {s₁ s₂ : Finset α}
        {b₁ b₂ : β}, Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Bool.false) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.sort_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_mk.h5 : ¬∀ {α : Type} {m : Multiset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
        m.Nodup → Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) ((0 : Multiset Bool) : Multiset Bool) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (by
  decide)) (by
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

-- Finset.sort_mk, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_mk.h6 : ¬∀ {α : Type} {m : Multiset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        m.Nodup → Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _ (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.sort_mk, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_mk.h7 : ¬∀ {α : Type} {m : Multiset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r]
        [inst : Std.Total r], m.Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (Nat.decLe) _ _ _) (by
  decide +kernel)

-- Finset.surjOn_of_injOn_of_card_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.surjOn_of_injOn_of_card_le.h7 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} (f : α → β),
        @Set.MapsTo α β f (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
            (@SetLike.coe (Finset β) β (@Finset.instSetLike β) t) →
          @Set.InjOn α β f (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) →
            @Set.SurjOn α β f (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
              (@SetLike.coe (Finset β) β (@Finset.instSetLike β) t)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Stream'.Seq.all_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.all_cons.h4 : ¬∀ {α : Type} {p : α → Prop} {hd : α} {tl : Stream'.Seq α}, (∀ x ∈ tl, p x) → ∀ x ∈ Stream'.Seq.cons hd tl, p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (1) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (by
  simp) (1) (by
  simp)) (by
  decide +kernel)

-- Stream'.Seq.all_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.all_cons.h5 : ¬∀ {α : Type} {p : α → Prop} {hd : α} {tl : Stream'.Seq α}, p hd → ∀ x ∈ Stream'.Seq.cons hd tl, p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (0) (Stream'.Seq.cons 0 (Stream'.Seq.cons 1 Stream'.Seq.nil) : Stream'.Seq ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (by
  simp)) (by
  decide +kernel)

-- Stream'.Seq.all_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.all_cons.h7 : ¬∀ {α : Type} {p : α → Prop} {hd : α} {tl : Stream'.Seq α}, p hd → (∀ x ∈ tl, p x) → ∀ (x : α), p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (0) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) (1)) (by
  decide +kernel)

-- Finset.sup_le_of_le_directed, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_le_of_le_directed.h4 : ¬∀ {α : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] (s : Set α),
        DirectedOn (fun (x1 x2 : α) => x1 ≤ x2) s → ∀ (t : Finset α), (∀ x ∈ t, ∃ y ∈ s, x ≤ y) → ∃ x ∈ s, t.sup id ≤ x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({x : ℕ | False}) (by
  simp) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  simp)) (by
  simp)

-- Finset.sup_le_of_le_directed, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_le_of_le_directed.h7 : Not
      (∀ {α : Type} [inst : SemilatticeSup α]
        [inst_1 : @OrderBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))]
        (s : Set α),
        @Set.Nonempty α s →
          @DirectedOn α
              (fun (x1 x2 : α) =>
                @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst))) x1 x2)
              s →
            ∀ (t : Finset α),
              ∃ (x : α),
                And (@Membership.mem α (Set α) (@Set.instMembership α) s x)
                  (@LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))
                    (@Finset.sup α α inst inst_1 t (@id α)) x)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (Nat.instOrderBot) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp) (by
  simp) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  (simp <;> omega))

-- Equiv.Finset.disjUnionEquiv_symm_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_right.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {i : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t i →
          @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Equiv.Finset.disjUnionEquiv_symm_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_right.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α}
        (h : @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) {i : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
            (@Finset.disjUnion α s t h) i →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t i) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) hc_k0 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k1) (by
  decide +kernel)

-- Equiv.Finset.union_symm_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.union_symm_right.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {i : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t i →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
              (@Max.max (Finset α) (@Finset.instMax α inst) s t) i →
            @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Equiv.Finset.union_symm_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.union_symm_right.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t →
          ∀ {i : α},
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
                (@Max.max (Finset α) (@Finset.instMax α inst) s t) i →
              @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t i) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Equiv.Finset.disjUnionEquiv_symm_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_left.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {i : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i →
          @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Equiv.Finset.disjUnionEquiv_symm_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_left.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α}
        (h : @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) {i : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
            (@Finset.disjUnion α s t h) i →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) hc_k0 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k1) (by
  decide +kernel)

-- Multiset.fold_distrib, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.fold_distrib.h3.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
theorem HypCheckProof.Multiset.fold_distrib.h3 : ¬∀ {α β : Type} (op : α → α → α) [ha : Std.Associative op] {f g : β → α} (u₁ u₂ : α) (s : Multiset β),
        Std.Commutative op := fun hc_h => HypCheckProof.Multiset.fold_distrib.h3.inst (@hc_h (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) (fun (n : ℕ) => n + 1) (0) (0) (0))

-- Multiset.fold_distrib, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_distrib.h4 : ¬∀ {α β : Type} (op : α → α → α) [hc : Std.Commutative op] {f g : β → α} (u₁ u₂ : α) (s : Multiset β),
        Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) (Bool.false) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.fold_op_distrib, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_op_distrib.h3.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
theorem HypCheckProof.Finset.fold_op_distrib.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {s : Finset α} {f g : α → β} {b₁ b₂ : β}, Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_op_distrib.h3.inst (@hc_h (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (fun (n : ℕ) => n + 1) (0) (0))

-- Finset.fold_op_distrib, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_op_distrib.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {s : Finset α} {f g : α → β} {b₁ b₂ : β}, Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.sort_toFinset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_toFinset.h5 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r]
        [inst : DecidableEq α], Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (instDecidableEqBool)) (by
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

-- Finset.sort_toFinset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_toFinset.h6 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r]
        [inst : DecidableEq α], Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _ (instDecidableEqNat)) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finsupp.support_mapRange_of_injective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_mapRange_of_injective.h6 : ¬∀ {ι M N : Type} [inst : Zero M] [inst_1 : Zero N] {e : M → N} (f : ι →₀ M), Function.Injective e → e 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Bool) (instZeroBool_mathlib) (instZeroBool_mathlib) (not : Bool → Bool) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.inf_coe, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_coe.h5.inst : ¬(fun (b : Bool) => b = Bool.false) ⊤ := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_coe.h5.prem0 : ∀ ⦃x y : Bool⦄, x = Bool.false → y = Bool.false → (fun (b : Bool) => b = Bool.false) (Min.min x y) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.inf_coe.h5 : ¬∀ {α β : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {P : α → Prop}
        {Pinf : ∀ ⦃x y : α⦄, P x → P y → P (x ⊓ y)} (t : Finset β) (f : β → { x : α // P x }), P ⊤ := fun hc_h => HypCheckProof.Finset.inf_coe.h5.inst (@hc_h (Bool) (ℕ) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) (fun (b : Bool) => b = Bool.false) HypCheckProof.Finset.inf_coe.h5.prem0 ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ) =>
      (⟨Bool.false, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Bool // (fun (b : Bool) => b = Bool.false) x })))

-- Multiset.fold_union_inter, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_union_inter.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] [inst : DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α),
        Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_union_inter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_union_inter.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] [inst : DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α),
        Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (instDecidableEqBool) ((0 : Multiset Bool) : Multiset Bool) ((0 : Multiset Bool) : Multiset Bool) (Bool.false) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_bind, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.fold_bind.h2.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
theorem HypCheckProof.Multiset.fold_bind.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] {ι : Type} (s : Multiset ι) (t : ι → Multiset α) (b : ι → α)
        (b₀ : α), Std.Commutative op := fun hc_h => HypCheckProof.Multiset.fold_bind.h2.inst (@hc_h (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (ℕ) (0) (fun (a : ℕ) => 0) (fun (n : ℕ) => n + 1) (0))

-- Multiset.fold_bind, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_bind.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] {ι : Type} (s : Multiset ι) (t : ι → Multiset α) (b : ι → α)
        (b₀ : α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (fun (a : ℕ) => 0) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.sup_mem_sups, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_mem_sups.h7 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s t : Finset α} {a b : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t b →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
            (@HasSups.sups (Finset α) (@Finset.hasSups α inst inst_1) s t)
            (@Max.max α (@SemilatticeSup.toMax α inst_1) a b)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Multiset.countP_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.countP_congr.h3 : ¬∀ {α : Type} {s s' : Multiset α} {p p' : α → Prop} [inst : DecidablePred p] [inst_1 : DecidablePred p'],
        (∀ x ∈ s, p x = p' x) → Multiset.countP p s = Multiset.countP p' s' := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableEqNat a 0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Multiset.countP_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.countP_congr.h8 : ¬∀ {α : Type} {s s' : Multiset α},
        s = s' →
          ∀ {p p' : α → Prop} [inst : DecidablePred p] [inst_1 : DecidablePred p'],
            Multiset.countP p s = Multiset.countP p' s' := fun hc_h => absurd (@hc_h (ℕ) _ (({0} : Multiset Nat) : Multiset ℕ) rfl (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableFalse)) (by
  decide +kernel)

-- Ordnode.Bounded.to_sep, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.to_sep.h8 : ¬∀ {α : Type} [inst : Preorder α] {t₁ t₂ : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α} {x : α},
        t₁.Bounded o₁ ↑x → Ordnode.All (fun (y : α) => Ordnode.All (fun (z : α) => y < z) t₂) t₁ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 1 Ordnode.nil) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (0) (2) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Nat.chineseRemainderOfMultiset_lt_prod, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfMultiset_lt_prod.h4.inst : Not
      (@Multiset.Nodup Nat
        (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfMultiset_lt_prod.h4.prem0 : ∀ (i : Nat),
      @Membership.mem Nat (Multiset Nat) (@Multiset.instMembership Nat)
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          i →
        @Ne Nat
          ((fun (n : Nat) =>
              @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            i)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfMultiset_lt_prod.h4.prem1 : @Set.Pairwise Nat
      (@Set.ofPred Nat fun (x : Nat) =>
        @Membership.mem Nat (Multiset Nat) (@Multiset.instMembership Nat)
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          x)
      (@Function.onFun Nat Nat Prop Nat.Coprime fun (n : Nat) =>
        @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  simp
theorem HypCheckProof.Nat.chineseRemainderOfMultiset_lt_prod.h4 : Not
      (∀ {ι : Type} (a s : ι → Nat) {m : Multiset ι},
        (∀ (i : ι),
            @Membership.mem ι (Multiset ι) (@Multiset.instMembership ι) m i →
              @Ne Nat (s i) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          @Set.Pairwise ι (@Set.ofPred ι fun (x : ι) => @Membership.mem ι (Multiset ι) (@Multiset.instMembership ι) m x)
              (@Function.onFun ι Nat Prop Nat.Coprime s) →
            @Multiset.Nodup ι m) := fun hc_h => HypCheckProof.Nat.chineseRemainderOfMultiset_lt_prod.h4.inst (@hc_h (Nat) (fun (n : Nat) =>
      @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (fun (n : Nat) =>
      @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) HypCheckProof.Nat.chineseRemainderOfMultiset_lt_prod.h4.prem0 HypCheckProof.Nat.chineseRemainderOfMultiset_lt_prod.h4.prem1)

-- Nat.chineseRemainderOfMultiset_lt_prod, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainderOfMultiset_lt_prod.h5 : ¬∀ {ι : Type} (a s : ι → ℕ) {m : Multiset ι},
        m.Nodup → {x : ι | x ∈ m}.Pairwise (Function.onFun Nat.Coprime s) → ∀ i ∈ m, s i ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (({0} : Multiset Nat) : Multiset ℕ) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Finset.eq_of_mem_cons_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_mem_cons_of_notMem.h4 : Not (∀ {α : Type} {s : Finset α} {a b : α}, b ∉ s → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Finset.eq_of_mem_cons_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_mem_cons_of_notMem.h5 : ¬∀ {α : Type} {s : Finset α} {a b : α}, a ∉ s → b ∉ s → b = a := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.eq_of_mem_cons_of_notMem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_mem_cons_of_notMem.h6 : Not
      (∀ {α : Type} {s : Finset α} {a b : α} (has : a ∉ s),
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) (@Finset.cons α a s has)
            b →
          @Eq α b a) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k0 hc_k1) (by
  decide +kernel)

-- Multiset.length_sort, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.length_sort.h5 : ¬∀ {α : Type} {s : Multiset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
        Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) ((0 : Multiset Bool) : Multiset Bool) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
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

-- Multiset.length_sort, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.length_sort.h6 : ¬∀ {α : Type} {s : Multiset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.sort_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sort_eq.h5 : ¬∀ {α : Type} (s : Multiset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
        Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) ((0 : Multiset Bool) : Multiset Bool) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
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

-- Multiset.sort_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sort_eq.h6 : ¬∀ {α : Type} (s : Multiset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.length_sort, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.length_sort.h5 : ¬∀ {α : Type} {s : Finset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
        Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
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

-- Finset.length_sort, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.length_sort.h6 : ¬∀ {α : Type} {s : Finset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.pairwise_sort, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.pairwise_sort.h5 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
        Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
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

-- Finset.pairwise_sort, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.pairwise_sort.h6 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.sort_perm_toList, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_perm_toList.h5 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
        Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
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

-- Finset.sort_perm_toList, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_perm_toList.h6 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.disjSum_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.disjSum_mono.h6 : ¬∀ {α β : Type} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β}, t₁ ≤ t₂ → s₁.disjSum t₁ ≤ s₂.disjSum t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Multiset.disjSum_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.disjSum_mono.h7 : ¬∀ {α β : Type} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β}, s₁ ≤ s₂ → s₁.disjSum t₁ ≤ s₂.disjSum t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset.h7 : ¬∀ {α β : Type} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β}, s₁ ⊆ s₂ → s₁.disjSum t₁ ⊂ s₂.disjSum t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Finset.sup'_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_cons.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {b : β} {hb : b ∉ s}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.sup'_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_cons.h7 : Not (∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β}, @Finset.Nonempty β s → ∀ (f : β → α) {b : β}, b ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.inf'_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_cons.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) {b : β} {hb : b ∉ s}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.inf'_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_cons.h7 : Not (∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β}, @Finset.Nonempty β s → ∀ (f : β → α) {b : β}, b ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.le_inf', hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.le_inf'.h4.inst : ¬{ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.Nonempty := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.le_inf'.h4.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }, 0 ≤ (fun (n : ℕ) => n + 1) b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.le_inf'.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) {a : α}, (∀ b ∈ s, a ≤ f b) → s.Nonempty := fun hc_h => HypCheckProof.Finset.le_inf'.h4.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (0) HypCheckProof.Finset.le_inf'.h4.prem0)

-- Finset.le_inf', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_inf'.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (H : @Finset.Nonempty β s) (f : β → α) {a : α},
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst))) a
          (@Finset.inf' α β inst s H f)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) hc_k0 (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Monotone.map_finset_min', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.map_finset_min'.h5 : Not
      (∀ {α β : Type} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β} {s : Finset α} (h : @Finset.Nonempty α s),
        @Eq β (f (@Finset.min' α inst s h))
          (@Finset.min' β inst_1 (@Finset.image α β (fun (a b : β) => @LinearOrder.toDecidableEq β inst_1 a b) f s)
            (@Finset.Nonempty.image α β (fun (a b : β) => @LinearOrder.toDecidableEq β inst_1 a b) s h f))) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Bool) (Nat.instLinearOrder) (Bool.linearOrder) (fun n => n % 2 == 0 : Nat → Bool) (@Finset.mk Nat
      (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) hc_k0) (by
  decide +kernel)

-- Monotone.map_finset_min', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.map_finset_min'.h7 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β}, Monotone f → ∀ {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.linearOrder) (Nat.instLinearOrder) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.min'_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_image.h5 : Not
      (∀ {α β : Type} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β} (s : Finset α)
        (h : @Finset.Nonempty β (@Finset.image α β (fun (a b : β) => @LinearOrder.toDecidableEq β inst_1 a b) f s)),
        @Eq β (@Finset.min' β inst_1 (@Finset.image α β (fun (a b : β) => @LinearOrder.toDecidableEq β inst_1 a b) f s) h)
          (f
            (@Finset.min' α inst s
              (@Finset.Nonempty.of_image α β (fun (a b : β) => @LinearOrder.toDecidableEq β inst_1 a b) f s h)))) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Bool) (Nat.instLinearOrder) (Bool.linearOrder) (fun n => n % 2 == 0 : Nat → Bool) (@Finset.mk Nat
      (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) hc_k0) (by
  decide +kernel)

-- Finset.min'_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_image.h7 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β},
        Monotone f → ∀ (s : Finset α), (Finset.image f s).Nonempty := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.linearOrder) (Nat.instLinearOrder) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Computation.LiftRel.imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.LiftRel.imp.h4 : ¬∀ {α β : Type} {R S : α → β → Prop} (s : Computation α) (t : Computation β),
        Computation.LiftRel R s t → Computation.LiftRel S s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Computation.pure 0 : Computation ℕ) (Computation.pure 0 : Computation ℕ) (by
  simp)) (by
  simp)

-- Computation.LiftRel.imp, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.LiftRel.imp.h7 : ¬∀ {α β : Type} {R S : α → β → Prop},
        (∀ {a : α} {b : β}, R a b → S a b) → ∀ (s : Computation α) (t : Computation β), Computation.LiftRel S s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (by
  simp) (Inhabited.default) (Computation.pure 0 : Computation ℕ)) (by
  simp)

-- Finset.forall_of_forall_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.forall_of_forall_insert.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {p : α → Prop} {a : α} {s : Finset α} (x : α),
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x → p x) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (fun n => n = 0 : Nat → Prop) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Finset.forall_of_forall_insert, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.forall_of_forall_insert.h7.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.forall_of_forall_insert.h7.prem0 : ∀ x ∈ Insert.insert 0 { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      (fun (n : ℕ) => n = 0) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.forall_of_forall_insert.h7 : ¬∀ {α : Type} [inst : DecidableEq α] {p : α → Prop} {a : α} {s : Finset α},
        (∀ x ∈ Insert.insert a s, p x) → ∀ (x : α), p x := fun hc_h => HypCheckProof.Finset.forall_of_forall_insert.h7.inst (@hc_h (ℕ) (instDecidableEqNat) (fun (n : ℕ) => n = 0) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) HypCheckProof.Finset.forall_of_forall_insert.h7.prem0 (1))

-- Finset.noncommSum_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.noncommSum_cons.h6 : Not (∀ {α β : Type} [inst : AddMonoid β] (s : Finset α) (a : α) (f : α → β), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat.instAddMonoid) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Finset.union_subset_union, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_subset_union.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u v : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) t
            v →
          @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Max.max (Finset α) (@Finset.instMax α inst) s t) (@Max.max (Finset α) (@Finset.instMax α inst) u v)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.union_subset_union, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_subset_union.h7 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u v : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
            u →
          @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Max.max (Finset α) (@Finset.instMax α inst) s t) (@Max.max (Finset α) (@Finset.instMax α inst) u v)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.noncommSum_cons', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.noncommSum_cons'.h6 : Not (∀ {α β : Type} [inst : AddMonoid β] (s : Finset α) (a : α) (f : α → β), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat.instAddMonoid) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Finset.sdiff_subset_sdiff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_subset_sdiff.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u v : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) v
            u →
          @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s u)
            (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t v)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Bounded.mono_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.mono_left.h4 : ¬∀ {α : Type} [inst : Preorder α] {x y : α} {t : Ordnode α} {o : WithTop α}, t.Bounded (↑y) o → t.Bounded (↑x) o := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (1) (0) (Ordnode.nil) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Bounded.mono_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.mono_left.h7 : ¬∀ {α : Type} [inst : Preorder α] {x y : α}, x ≤ y → ∀ {t : Ordnode α} {o : WithTop α}, t.Bounded (↑x) o := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (0) (by
  decide) (Ordnode.nil) (0)) (by
  nofun)

-- Multiset.fold_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_add.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b₁ b₂ : α) (s₁ s₂ : Multiset α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_add.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b₁ b₂ : α) (s₁ s₂ : Multiset α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) ((0 : Multiset Bool) : Multiset Bool) ((0 : Multiset Bool) : Multiset Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.lt_max'_of_mem_erase_max', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.lt_max'_of_mem_erase_max'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) [inst : DecidableEq α] {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat) (0)) (by
  decide +kernel)

-- Finset.lt_max'_of_mem_erase_max', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.lt_max'_of_mem_erase_max'.h6 : Not
      (∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (H : @Finset.Nonempty α s) [inst_1 : DecidableEq α] {a : α},
        @LT.lt α
          (@Preorder.toLT α
            (@PartialOrder.toPreorder α
              (@SemilatticeInf.toPartialOrder α
                (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
          a (@Finset.max' α inst s H)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) hc_k0 (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.min_le_of_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min_le_of_eq.h5 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a b : α},
        @Eq (WithTop α) (@Finset.min α inst s) (@WithTop.some α b) →
          @LE.le α
            (@Preorder.toLE α
              (@PartialOrder.toPreorder α
                (@SemilatticeSup.toPartialOrder α
                  (@Lattice.toSemilatticeSup α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
            b a) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Finset.min_le_of_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min_le_of_eq.h6 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a b : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s a →
          @LE.le α
            (@Preorder.toLE α
              (@PartialOrder.toPreorder α
                (@SemilatticeSup.toPartialOrder α
                  (@Lattice.toSemilatticeSup α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
            b a) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Stream'.Seq.get?_mem_take, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.get?_mem_take.h4 : ¬∀ {α : Type} {s : Stream'.Seq α} {m n : ℕ} {x : α}, s.get? m = Option.some x → x ∈ Stream'.Seq.take n s := fun hc_h => absurd (@hc_h (ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Stream'.Seq.get?_mem_take, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.get?_mem_take.h6 : ¬∀ {α : Type} {s : Stream'.Seq α} {m n : ℕ}, m < n → ∀ {x : α}, x ∈ Stream'.Seq.take n s := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0) (1) (by
  decide) (0)) (by
  decide +kernel)

-- Stream'.Seq.take_all, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.take_all.h6 : ¬∀ {α : Type} {s : Stream'.Seq α} {p : α → Prop}, (∀ x ∈ s, p x) → ∀ {n : ℕ} {x : α}, p x := fun hc_h => absurd (@hc_h (ℕ) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (fun n => n = 0 : ℕ → Prop) (by
  simp) (0) (1)) (by
  decide +kernel)

-- Finset.le_inf'_image₂, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_inf'_image₂.h11 : ¬∀ {α β γ δ : Type} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β} [inst_1 : SemilatticeInf δ]
        {g : γ → δ} {a : δ}, (Finset.image₂ f s t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (fun a b => a - b : ℕ → ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Nat.instLattice.toSemilatticeInf) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Nat.multinomial_insert_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multinomial_insert_one.h5 : Not
      (∀ {α : Type} {s : Finset α} {f : α → Nat} {a : α} [inst : DecidableEq α],
        @Eq Nat (f a) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq Nat (@Nat.multinomial α (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s) f)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@Finset.sum α Nat Nat.instAddCommMonoid s f).succ
              (@Nat.multinomial α s f))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instDecidableEqNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.multinomial_insert_one, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multinomial_insert_one.h6 : Not
      (∀ {α : Type} {s : Finset α} {f : α → Nat} {a : α} [inst : DecidableEq α],
        a ∉ s →
          @Eq Nat (@Nat.multinomial α (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s) f)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@Finset.sum α Nat Nat.instAddCommMonoid s f).succ
              (@Nat.multinomial α s f))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (instDecidableEqNat) (by
  decide)) (by
  decide +kernel)

-- Finset.sup'_image₂_le, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_image₂_le.h11 : ¬∀ {α β γ δ : Type} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β} [inst_1 : SemilatticeSup δ]
        {g : γ → δ} {a : δ}, (Finset.image₂ f s t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (fun a b => a - b : ℕ → ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Nat.instLattice.toSemilatticeSup) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Disjoint.powersetCard_powersetCard_multiset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.powersetCard_powersetCard_multiset.h6 : ¬∀ {α : Type} {s t : Multiset α},
        Disjoint s t → ∀ {n m : ℕ}, Disjoint (Multiset.powersetCard n s) (Multiset.powersetCard m t) := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  simp) (0) (0)) (by
  simp)

-- Finset.card_filter_powersetCard_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_filter_powersetCard_subset.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] (s t : Finset α) (n : Nat),
        @LE.le Nat instLENat (@Finset.card α s) n →
          @Eq Nat
            (@Finset.card (Finset α)
              ({x ∈ @Finset.powersetCard α n t |
                @LE.le (Finset α)
                  (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s x}))
            ((@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@Finset.card α t) (@Finset.card α s)).choose
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n (@Finset.card α s)))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Multiset.union_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.union_le.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t u : Multiset α}, t ≤ u → s ∪ t ≤ u := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Multiset.union_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.union_le.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {s t u : Multiset α}, s ≤ u → s ∪ t ≤ u := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Finset.union_congr_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_congr_right.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) t
            (@Max.max (Finset α) (@Finset.instMax α inst) s u) →
          @Eq (Finset α) (@Max.max (Finset α) (@Finset.instMax α inst) s u)
            (@Max.max (Finset α) (@Finset.instMax α inst) t u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.union_congr_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_congr_right.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
            (@Max.max (Finset α) (@Finset.instMax α inst) t u) →
          @Eq (Finset α) (@Max.max (Finset α) (@Finset.instMax α inst) s u)
            (@Max.max (Finset α) (@Finset.instMax α inst) t u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.union_left_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_left_inj.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) u t →
          Iff
            (@Eq (Finset α) (@Max.max (Finset α) (@Finset.instMax α inst) s u)
              (@Max.max (Finset α) (@Finset.instMax α inst) t u))
            (@Eq (Finset α) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.union_left_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_left_inj.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) u s →
          Iff
            (@Eq (Finset α) (@Max.max (Finset α) (@Finset.instMax α inst) s u)
              (@Max.max (Finset α) (@Finset.instMax α inst) t u))
            (@Eq (Finset α) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.disjiUnion_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjiUnion_cons.h4 : Not (∀ {α β : Type} (a : α) (s : Finset α) (f : α → Finset β), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun (a : Nat) =>
      @Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
        (@of_decide_eq_true
          (@Multiset.Nodup Nat
            (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
          (@Multiset.nodupDecidable Nat instDecidableEqNat
            (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
          (@id
            (@Eq Bool
              (@Decidable.decide
                (@Multiset.Nodup Nat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                (@Multiset.nodupDecidable Nat instDecidableEqNat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
              Bool.true)
            (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.filterMap_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filterMap_mono.h5 : ¬∀ {α β : Type} (f : α → Option β) {s t : Finset α}, s ⊆ t → ∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a' := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) => Option.some 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (by
  decide)) (by
  decide +kernel)

-- Finset.erase_sdiff_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_sdiff_erase.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s b →
          @Eq (Finset α)
            (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) (@Finset.erase α inst s a) (@Finset.erase α inst s b))
            (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) b)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.erase_sdiff_erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_sdiff_erase.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, a ≠ b → s.erase a \ s.erase b = {b} := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.filter_cons_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_cons_of_pos.h5 : Not (∀ {α : Type} (p : α → Prop) [inst : @DecidablePred α p] (a : α) (s : Finset α), p a → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.filter_cons_of_pos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_cons_of_pos.h6 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (a : α) (s : Finset α) (ha : a ∉ s),
        Finset.filter p (Finset.cons a s ha) =
          Finset.cons a (Finset.filter p s) (Function.mt (Finset.mem_of_mem_filter a) ha) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) hc_k0) (by
  decide +kernel)

-- Finset.disjoint_of_erase_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_of_erase_right.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s (@Finset.erase α inst t a) →
          @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.disjoint_of_erase_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_of_erase_right.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        a ∉ s → @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Finset.filter_card_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_card_eq.h4 : Not
      (∀ {α : Type} {s : Finset α} {p : α → Prop} [inst : @DecidablePred α p] (x : α),
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x → p x) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun _ => False : Nat → Prop) (fun (a : Nat) => instDecidableFalse) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.filter_card_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_card_eq.h6 : ¬∀ {α : Type} {s : Finset α} {p : α → Prop} [inst : DecidablePred p], (Finset.filter p s).card = s.card → ∀ (x : α), p x := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (by
  decide) (1)) (by
  decide +kernel)

-- Finset.card_le_card_of_injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_le_card_of_injOn.h5 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} (f : α → β),
        @Set.InjOn α β f (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) →
          @LE.le Nat instLENat (@Finset.card α s) (@Finset.card β t)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  decide +kernel)

-- Finset.card_bijective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_bijective.h5 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} (e : α → β),
        (∀ (i : α),
            Iff (@Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i)
              (@Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β)) t (e i))) →
          @Eq Nat (@Finset.card α s) (@Finset.card β t)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (by
  simp)) (by
  decide +kernel)

-- Finset.card_bijective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_bijective.h6 : ¬∀ {α β : Type} {s : Finset α} {t : Finset β} (e : α → β), Function.Bijective e → s.card = t.card := fun hc_h => absurd (@hc_h (Bool) (Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Multiset.fold_cons_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_cons_right.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b a : α) (s : Multiset α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_cons_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_cons_right.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b a : α) (s : Multiset α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) ((0 : Multiset Bool) : Multiset Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.sup'_image₂_left, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_image₂_left.h10 : ¬∀ {α β γ δ : Type} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β} [inst_1 : SemilatticeSup δ]
        (g : γ → δ), (Finset.image₂ f s t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (fun a b => a - b : ℕ → ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Nat.instLattice.toSemilatticeSup) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.sup'_prodMap, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_prodMap.h8 : ¬∀ {ι κ α β : Type} [inst : SemilatticeSup α] [inst : SemilatticeSup β] {s : Finset ι} {t : Finset κ} (f : ι → α)
        (g : κ → β), (s ×ˢ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.disjUnion_inj_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjUnion_inj_left.h4 : Not
      (∀ {α : Type} {s₁ s₂ t : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s₂ t →
          @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s₁ t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.disjUnion_inj_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjUnion_inj_left.h5 : Not
      (∀ {α : Type} {s₁ s₂ t : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s₁ t →
          @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s₂ t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.disjoint_of_subset_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_of_subset_right.h4 : Not
      (∀ {α : Type} {s t u : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s u →
          @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Computation.terminates_bind, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.terminates_bind.h4 : ¬∀ {α β : Type} (s : Computation α) (f : α → Computation β), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Inhabited.default) (fun (a : ℕ) => Inhabited.default)) (by
  nofun)

-- Equiv.Finset.congr_trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.congr_trans.h4 : Not (∀ {α : Type} {s t u : Finset α}, @Eq (Finset α) t u → @Eq (Finset α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) _ (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) rfl) (by
  decide +kernel)

-- Equiv.Finset.congr_trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.congr_trans.h5 : Not (∀ {α : Type} {s t u : Finset α}, @Eq (Finset α) s t → @Eq (Finset α) t u) := fun hc_h => absurd (@hc_h (Nat) _ (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) rfl) (by
  decide +kernel)

-- Finset.le_card_of_inj_on_range, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.le_card_of_inj_on_range.h4.inst : ¬1 ≤ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.card := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.le_card_of_inj_on_range.h4.prem0 : ∀ i < 1, ∀ j < 1, (fun (n : ℕ) => n + 1) i = (fun (n : ℕ) => n + 1) j → i = j := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.le_card_of_inj_on_range.h4 : ¬∀ {α : Type} {s : Finset α} {n : ℕ} (f : ℕ → α), (∀ i < n, ∀ j < n, f i = f j → i = j) → n ≤ s.card := fun hc_h => HypCheckProof.Finset.le_card_of_inj_on_range.h4.inst (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1) (fun (n : ℕ) => n + 1) HypCheckProof.Finset.le_card_of_inj_on_range.h4.prem0)

-- Multiset.fold_eq_foldr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_eq_foldr.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b : α) (s : Multiset α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_eq_foldr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_eq_foldr.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b : α) (s : Multiset α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) ((0 : Multiset Bool) : Multiset Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Cycle.Chain.imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.imp.h4 : ¬∀ {α : Type} {s : Cycle α} {r₁ r₂ : α → α → Prop}, Cycle.Chain r₁ s → Cycle.Chain r₂ s := fun hc_h => absurd (@hc_h (ℕ) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (by
  simp)) (by
  simp)

-- Cycle.Chain.imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.imp.h5 : ¬∀ {α : Type} {s : Cycle α} {r₁ r₂ : α → α → Prop}, (∀ (a b : α), r₁ a b → r₂ a b) → Cycle.Chain r₂ s := fun hc_h => absurd (@hc_h (ℕ) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (by
  simp)) (by
  simp)

-- Cycle.next_reverse_eq_prev', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.next_reverse_eq_prev'.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Cycle α), s.reverse.Nodup → ∀ (x : α), x ∈ s.reverse := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (∅) (by
  decide) (0)) (by
  decide +kernel)

-- Cycle.next_prev, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.next_prev.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Cycle α), s.Nodup → ∀ (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (∅) (by
  decide) (0)) (by
  decide +kernel)

-- Finset.orderEmbOfFin_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.orderEmbOfFin_zero.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {k : ℕ}, 0 < k → s.card = k := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.orderEmbOfFin_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.orderEmbOfFin_zero.h5 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {k : ℕ}, s.card = k → 0 < k := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) _ rfl) (by
  decide +kernel)

-- Multiset.Nodup.disjSum, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.disjSum.h4 : ¬∀ {α β : Type} {s : Multiset α} {t : Multiset β}, t.Nodup → (s.disjSum t).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Multiset.Nodup.disjSum, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.disjSum.h5 : ¬∀ {α β : Type} {s : Multiset α} {t : Multiset β}, s.Nodup → (s.disjSum t).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Computation.length_bind, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.length_bind.h4 : ¬∀ {α β : Type} (s : Computation α) (f : α → Computation β), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Inhabited.default) (fun (a : ℕ) => Inhabited.default)) (by
  nofun)

-- Computation.length_bind, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.length_bind.h5 : ¬∀ {α β : Type} (s : Computation α) (f : α → Computation β) [_T1 : s.Terminates], (f s.get).Terminates := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Computation.pure 0 : Computation ℕ) (fun (a : ℕ) => Inhabited.default) _) (by
  nofun)

-- Stream'.Seq.terminated_stable, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.terminated_stable.h4 : ¬∀ {α : Type} (s : Stream'.Seq α) {m n : ℕ}, s.TerminatedAt m → s.TerminatedAt n := fun hc_h => absurd (@hc_h (ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Stream'.Seq.terminated_stable, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.terminated_stable.h5 : ¬∀ {α : Type} (s : Stream'.Seq α) {m n : ℕ}, m ≤ n → s.TerminatedAt n := fun hc_h => absurd (@hc_h (ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Stream'.Seq.le_stable, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.le_stable.h4 : ¬∀ {α : Type} (s : Stream'.Seq α) {m n : ℕ}, s.get? m = Option.none → s.get? n = Option.none := fun hc_h => absurd (@hc_h (ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Stream'.Seq.le_stable, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.le_stable.h5 : ¬∀ {α : Type} (s : Stream'.Seq α) {m n : ℕ}, m ≤ n → s.get? n = Option.none := fun hc_h => absurd (@hc_h (ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Stream'.Seq.all_of_get, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.all_of_get.h5 : ¬∀ {α : Type} {p : α → Prop} {s : Stream'.Seq α}, (∀ (n : ℕ) (x : α), s.get? n = Option.some x → p x) → ∀ (x : α), p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (by
  simp) (1)) (by
  decide +kernel)

-- Finset.EquitableOn.le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.EquitableOn.le.h4 : ¬∀ {α : Type} {s : Finset α} {f : α → ℕ} {a : α}, a ∈ s → (∑ i ∈ s, f i) / s.card ≤ f a := fun hc_h => absurd (@hc_h (ℕ) (({0, 1, 2} : Finset Nat) : Finset ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.notMem_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_subset.h3 : Not (∀ {α : Type} {s t : Finset α} {a : α}, a ∉ t → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.notMem_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_subset.h5 : Not
      (∀ {α : Type} {s t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
            t →
          ∀ {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.ssubset_of_ssubset_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ssubset_of_ssubset_of_subset.h4 : ¬∀ {α : Type} {s₁ s₂ s₃ : Finset α}, s₂ ⊆ s₃ → s₁ ⊂ s₃ := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Finset.ssubset_of_ssubset_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ssubset_of_ssubset_of_subset.h5 : Not
      (∀ {α : Type} {s₁ s₂ s₃ : Finset α},
        @LT.lt (Finset α) (@Preorder.toLT (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s₁
            s₂ →
          @LT.lt (Finset α) (@Preorder.toLT (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            s₁ s₃) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- ENat.sum_lt_sum_of_nonempty, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.ENat.sum_lt_sum_of_nonempty.h2.inst : Not
      (@LT.lt ENat instLTENat
        (∑
          i ∈
            @Finset.mk Nat
              (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
              (@of_decide_eq_true
                (@Multiset.Nodup Nat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                (@Multiset.nodupDecidable Nat instDecidableEqNat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Multiset.Nodup Nat
                        (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                      (@Multiset.nodupDecidable Nat instDecidableEqNat
                        (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
                    Bool.true)
                  (@Eq.refl Bool Bool.true))),
          (fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) i)
        (∑
          i ∈
            @Finset.mk Nat
              (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
              (@of_decide_eq_true
                (@Multiset.Nodup Nat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                (@Multiset.nodupDecidable Nat instDecidableEqNat
                  (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Multiset.Nodup Nat
                        (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                      (@Multiset.nodupDecidable Nat instDecidableEqNat
                        (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
                    Bool.true)
                  (@Eq.refl Bool Bool.true))),
          (fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) i)) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.ENat.sum_lt_sum_of_nonempty.h2.prem0 : ∀ (i : Nat),
      @Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
          (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
            (@of_decide_eq_true
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@Multiset.Nodup Nat
                      (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
                    (@Multiset.nodupDecidable Nat instDecidableEqNat
                      (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
                  Bool.true)
                (@Eq.refl Bool Bool.true))))
          i →
        @LT.lt ENat instLTENat ((fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) i)
          ((fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) i) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.ENat.sum_lt_sum_of_nonempty.h2 : Not
      (∀ {α : Type} {s : Finset α} {f g : α → ENat},
        (∀ (i : α),
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i →
              @LT.lt ENat instLTENat (f i) (g i)) →
          @LT.lt ENat instLTENat (∑ i ∈ s, f i) (∑ i ∈ s, g i)) := fun hc_h => HypCheckProof.ENat.sum_lt_sum_of_nonempty.h2.inst (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) (fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) HypCheckProof.ENat.sum_lt_sum_of_nonempty.h2.prem0)

-- Finset.not_mem_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.not_mem_subset.h3 : Not (∀ {α : Type} {s t : Finset α} {a : α}, a ∉ t → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.not_mem_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.not_mem_subset.h5 : Not
      (∀ {α : Type} {s t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
            t →
          ∀ {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.chineseRemainderOfFinset_lt_prod, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainderOfFinset_lt_prod.h4 : Not
      (∀ {ι : Type} (a s : ι → Nat) {t : Finset ι},
        @Set.Pairwise ι (@SetLike.coe (Finset ι) ι (@Finset.instSetLike ι) t) (@Function.onFun ι Nat Prop Nat.Coprime s) →
          ∀ (i : ι),
            @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t i →
              @Ne Nat (s i) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := fun hc_h => absurd (@hc_h (Nat) (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Nat.chineseRemainderOfFinset_lt_prod, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfFinset_lt_prod.h5.inst : Not
      (@Set.Pairwise Bool
        (@SetLike.coe (Finset Bool) Bool (@Finset.instSetLike Bool)
          (@Finset.mk Bool
            (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
              (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false))
            (@of_decide_eq_true
              (@Multiset.Nodup Bool
                (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                  (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false)))
              (@Multiset.nodupDecidable Bool instDecidableEqBool
                (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                  (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false)))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@Multiset.Nodup Bool
                      (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                        (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false)))
                    (@Multiset.nodupDecidable Bool instDecidableEqBool
                      (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                        (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false))))
                  Bool.true)
                (@Eq.refl Bool Bool.true)))))
        (@Function.onFun Bool Nat Prop Nat.Coprime fun (a : Bool) =>
          @OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfFinset_lt_prod.h5.prem0 : ∀ (i : Bool),
      @Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
          (@Finset.mk Bool
            (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
              (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false))
            (@of_decide_eq_true
              (@Multiset.Nodup Bool
                (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                  (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false)))
              (@Multiset.nodupDecidable Bool instDecidableEqBool
                (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                  (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false)))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@Multiset.Nodup Bool
                      (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                        (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false)))
                    (@Multiset.nodupDecidable Bool instDecidableEqBool
                      (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                        (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false))))
                  Bool.true)
                (@Eq.refl Bool Bool.true))))
          i →
        @Ne Nat ((fun (a : Bool) => @OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.chineseRemainderOfFinset_lt_prod.h5 : Not
      (∀ {ι : Type} (a s : ι → Nat) {t : Finset ι},
        (∀ (i : ι),
            @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t i →
              @Ne Nat (s i) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          @Set.Pairwise ι (@SetLike.coe (Finset ι) ι (@Finset.instSetLike ι) t) (@Function.onFun ι Nat Prop Nat.Coprime s)) := fun hc_h => HypCheckProof.Nat.chineseRemainderOfFinset_lt_prod.h5.inst (@hc_h (Bool) (fun (b : Bool) =>
      @ite Nat (@Eq Bool b Bool.true) (instDecidableEqBool b Bool.true)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (a : Bool) => @OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Finset.mk Bool
      (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
        (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false))
      (@of_decide_eq_true
        (@Multiset.Nodup Bool
          (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
            (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false)))
        (@Multiset.nodupDecidable Bool instDecidableEqBool
          (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
            (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false)))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Bool
                (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                  (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false)))
              (@Multiset.nodupDecidable Bool instDecidableEqBool
                (@Insert.insert Bool (Multiset Bool) (@Multiset.instInsert Bool) Bool.true
                  (@Singleton.singleton Bool (Multiset Bool) (@Multiset.instSingleton Bool) Bool.false))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) HypCheckProof.Nat.chineseRemainderOfFinset_lt_prod.h5.prem0)

-- Finset.notMem_of_mem_powerset_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_of_mem_powerset_of_notMem.h4 : Not (∀ {α : Type} {s t : Finset α} {a : α}, a ∉ s → a ∉ t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.notMem_of_mem_powerset_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_of_mem_powerset_of_notMem.h5 : Not
      (∀ {α : Type} {s t : Finset α} {a : α},
        @Membership.mem (Finset α) (Finset (Finset α))
            (@SetLike.instMembership (Finset (Finset α)) (Finset α) (@Finset.instSetLike (Finset α))) (@Finset.powerset α s)
            t →
          a ∉ t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Multiset.rel_of_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.rel_of_forall.h5 : ¬∀ {α : Type} {m1 m2 : Multiset α} {r : α → α → Prop}, (∀ (a b : α), a ∈ m1 → b ∈ m2 → r a b) → Multiset.Rel r m1 m2 := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (by
  simp)) (by
  simp)

-- Multiset.noncommProd_eq_pow_card, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommProd_eq_pow_card.h5 : ¬∀ {α : Type} [inst : Monoid α] (s : Multiset α) (comm : {x : α | x ∈ s}.Pairwise Commute) (m : α),
        s.noncommProd comm = m ^ s.card := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (Nat.instMonoid) (({0} : Multiset Nat) : Multiset ℕ) hc_k0 (1)) (by
  (simp <;> decide))

-- Finset.inf'_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_image.h7 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] [inst : DecidableEq β] {s : Finset γ} {f : γ → β} (g : β → α),
        (Finset.image f s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.inf'_comp_eq_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_comp_eq_image.h7 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] [inst : DecidableEq β] {s : Finset γ} {f : γ → β} (g : β → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.preimage_compl, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.preimage_compl.h8 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst : DecidableEq β] [inst : Fintype α] [inst : Fintype β] {f : α → β}
        (s : Finset β), Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (instDecidableEqBool) (instDecidableEqBool) (Bool.fintype) (Bool.fintype) (fun _ => true : Bool → Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.sup'_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_image.h7 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] [inst : DecidableEq β] {s : Finset γ} {f : γ → β} (g : β → α),
        (Finset.image f s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Ordnode.Valid'.eraseMin_aux, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.eraseMin_aux.h8 : ¬∀ {α : Type} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑(l.findMin' x)) (l.node' x r).eraseMin o₂ ∧ (l.node' x r).size = (l.node' x r).eraseMin.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (Ordnode.nil) (0) (Ordnode.nil) (0) (0)) (by
  nofun)

-- Finsupp.mapRange_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mapRange_apply.h6 : ¬∀ {α M N : Type} [inst : Zero M] [inst_1 : Zero N] {f : M → N} {g : α →₀ M} {a : α}, f 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ) (0)) (by
  decide +kernel)

-- Finset.eq_of_superset_of_card_ge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_superset_of_card_ge.h3 : Not (∀ {α : Type} {s t : Finset α}, @LE.le Nat instLENat (@Finset.card α t) (@Finset.card α s) → @Eq (Finset α) t s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.eq_of_superset_of_card_ge, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_superset_of_card_ge.h4 : Not
      (∀ {α : Type} {s t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
            t →
          @Eq (Finset α) t s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- FiniteInter.finiteInter_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FiniteInter.finiteInter_mem.h2 : ¬∀ {α : Type} {S : Set (Set α)} (F : Finset (Set α)), ↑F ⊆ S → ⋂₀ ↑F ∈ S := fun hc_h => absurd (@hc_h (ℕ) (∅) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset (Set ℕ) }) (by
  simp)) (by
  decide +kernel)

-- Computation.mem_of_promises, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.mem_of_promises.h4 : ¬∀ {α : Type} (s : Computation α) [h : s.Terminates] {a : α}, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Computation.pure 0 : Computation ℕ) _ (1)) (by
  simp)

-- Finset.sup_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_le.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α]
        [inst_1 : @OrderBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))]
        {s : Finset β} {f : β → α} {a : α},
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))
          (@Finset.sup α β inst inst_1 s f) a) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (Nat.instOrderBot) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.sup_lt_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_lt_iff.h7 : ¬∀ {α ι : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},
        s.sup f < a ↔ ∀ b ∈ s, f b < a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.sup_eq_one, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_eq_one.h7 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} [inst_2 : One α],
        s.sup f = 1 ↔ ∀ i ∈ s, f i = 1 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (Nat.instOne)) (by
  decide +kernel)

-- Finset.le_sup_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_sup_iff.h7 : ¬∀ {α ι : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},
        a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.sup'_product_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_product_right.h6 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] {s : Finset β} {t : Finset γ} (f : β × γ → α), (s ×ˢ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ × ℕ) => 0)) (by
  decide +kernel)

-- Finset.inf'_product_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_product_right.h6 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] {s : Finset β} {t : Finset γ} (f : β × γ → α), (s ×ˢ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ × ℕ) => 0)) (by
  decide +kernel)

-- Finset.inf'_product_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_product_left.h6 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] {s : Finset β} {t : Finset γ} (f : β × γ → α), (s ×ˢ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ × ℕ) => 0)) (by
  decide +kernel)

-- Finset.card_image₂_singleton_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_image₂_singleton_left.h7 : Not
      (∀ {α β γ : Type} [inst : DecidableEq γ] {f : α → β → γ} (t : Finset β) {a : α},
        @Eq Nat
          (@Finset.card γ (@Finset.image₂ α β γ inst f (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a) t))
          (@Finset.card β t)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (instDecidableEqNat) (fun a b => a - b : Nat → Nat → Nat) (@Finset.mk Nat
      (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.Nonempty.of_image₂_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_image₂_right.h7 : ¬∀ {α β γ : Type} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β}, t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (fun a b => a - b : ℕ → ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Multiset.map_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_erase.h5 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] (f : α → β) (x : α) (s : Multiset α),
        Multiset.map f (s.erase x) = (Multiset.map f s).erase (f x) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (fun _ => 0 : ℕ → ℕ) (0) (({1} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.map_union, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_union.h5 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] {f : α → β} {s t : Multiset α},
        Multiset.map f (s ∪ t) = Multiset.map f s ∪ Multiset.map f t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (fun _ => 0 : ℕ → ℕ) (({0} : Multiset Nat) : Multiset ℕ) (({1} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.inf'_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_le.h6 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) {b : β}, b ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finsupp.onFinset_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.onFinset_apply.h5 : ¬∀ {α M : Type} [inst : Zero M] {s : Finset α} {f : α → M} {a : α} (a : α), f a ≠ 0 → a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  simp)

-- Finset.inf_eq_top_of_isEmpty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_eq_top_of_isEmpty.h4 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α]
        [inst_1 : @OrderTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))]
        (f : β → α) (S : Finset β),
        @Eq α (@Finset.inf α β inst inst_1 S f)
          (@Top.top α
            (@OrderTop.toTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))
              inst_1))) := fun hc_h => absurd (@hc_h (Bool) (Nat) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@CoheytingAlgebra.toOrderTop Bool
      (@Order.Coframe.toCoheytingAlgebra Bool
        (@CompleteDistribLattice.toCoframe Bool
          (@CompleteBooleanAlgebra.toCompleteDistribLattice Bool Bool.completeBooleanAlgebra)))) (fun n => n % 2 == 0 : Nat → Bool) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.inf_sdiff_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_sdiff_right.h4 : ¬∀ {α ι : Type} [inst : BooleanAlgebra α] {s : Finset ι} (f : ι → α) (a : α),
        (s.inf fun (b : ι) => f b \ a) = s.inf f \ a := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.true)) (by
  decide +kernel)

-- Finset.sup_himp_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_himp_left.h4 : ¬∀ {α ι : Type} [inst : BooleanAlgebra α] {s : Finset ι} (f : ι → α) (a : α),
        (s.sup fun (b : ι) => a ⇨ f b) = a ⇨ s.sup f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false)) (by
  decide +kernel)

-- Finset.image_preimage, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_preimage.h6 : Not
      (∀ {α β : Type} [inst : DecidableEq β] (f : α → β) (s : Finset β)
        [inst : (x : β) → Decidable (@Membership.mem β (Set β) (@Set.instMembership β) (@Set.range β α f) x)],
        @Set.InjOn α β f (@Set.preimage α β f (@SetLike.coe (Finset β) β (@Finset.instSetLike β) s))) := fun hc_h => absurd (@hc_h (Bool) (Nat) (instDecidableEqNat) (fun _ => 0 : Bool → Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun (x : Nat) =>
      @Fintype.decidableMemRangeFintype Bool Nat Bool.fintype instDecidableEqNat
        (fun (x : Bool) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)) (by
  simp)

-- Finset.sup'_inf_distrib_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_inf_distrib_right.h4 : ¬∀ {α ι : Type} [inst : DistribLattice α] {s : Finset ι} (f : ι → α) (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDistribLatticeNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.coe_inf_of_nonempty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.coe_inf_of_nonempty.h5 : ¬∀ {α β : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {s : Finset β} (f : β → α),
        ↑(s.inf f) = s.inf (WithTop.some ∘ f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- Finset.le_sup', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_sup'.h6 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {b : β}, b ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.sup_eq_bot_of_isEmpty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_eq_bot_of_isEmpty.h4 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α]
        [inst_1 : @OrderBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))]
        (f : β → α) (S : Finset β),
        @Eq α (@Finset.sup α β inst inst_1 S f)
          (@Bot.bot α
            (@OrderBot.toBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))
              inst_1))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (Nat.instOrderBot) (fun n => n + 1 : Nat → Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Disjoint.of_image_finset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.of_image_finset.h6 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {s t : Finset α} {f : α → β},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Finset.exists_mem_eq_sup, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_mem_eq_sup.h5 : ¬∀ {α ι : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] (s : Finset ι) (f : ι → α), ∃ i ∈ s, s.sup f = f i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Multiset.foldl_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldl_cons.h3 : ¬∀ {α β : Type} (f : β → α → β) (b : β) (a : α) (s : Multiset α), RightCommutative f := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (Bool.false) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.right_comm (Bool.false : Bool) (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.mem_inf', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_inf'.h6 : ¬∀ {α ι : Type} [inst : DecidableEq α] {s : Finset ι} {f : ι → Finset α} {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ) => { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finsupp.mem_support_onFinset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mem_support_onFinset.h5 : ¬∀ {α M : Type} [inst : Zero M] {s : Finset α} {f : α → M} {a : α} (a : α), f a ≠ 0 → a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  simp)

-- Multiset.dedup_map_of_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.dedup_map_of_injective.h5 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] {f : α → β} (s : Multiset α),
        (Multiset.map f s).dedup = Multiset.map f s.dedup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (fun _ => 0 : ℕ → ℕ) (({0, 1} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finsupp.comapDomain.addMonoidHom_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.comapDomain.addMonoidHom_apply.h5 : ¬∀ {α β M : Type} [inst : AddZeroClass M] {f : α → β} (x : β →₀ M), Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instAddMonoid.toAddZeroClass) (fun _ => 0 : ℕ → ℕ) (0)) (by
  simp)

-- Finset.sup'_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_lt_iff.h4 : ¬∀ {α ι : Type} [inst : LinearOrder α] {s : Finset ι} {f : ι → α} {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.cast_card_sdiff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cast_card_sdiff.h6 : Not
      (∀ {α R : Type} {s t : Finset α} [inst : DecidableEq α] [inst_1 : AddGroupWithOne R],
        @Eq R
          (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst_1))
            (@Finset.card α (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t s)))
          (@HSub.hSub R R R
            (@instHSub R (@SubNegMonoid.toSub R (@AddGroup.toSubNegMonoid R (@AddGroupWithOne.toAddGroup R inst_1))))
            (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst_1)) (@Finset.card α t))
            (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst_1))
              (@Finset.card α s)))) := fun hc_h => absurd (@hc_h (Nat) (Bool) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))) (by
  decide +kernel)

-- Finset.infs_subset_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.infs_subset_right.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s₁ s₂ t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@HasInfs.infs (Finset α) (@Finset.hasInfs α inst inst_1) s₁ t)
          (@HasInfs.infs (Finset α) (@Finset.hasInfs α inst inst_1) s₂ t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.pairwise_cons', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.pairwise_cons'.h4 : Not (∀ {α β : Type} {s : Finset α} {a : α} (r : β → β → Prop) (f : α → β), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun a b => a < b : Nat → Nat → Prop) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Finset.image_subset_infs_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_subset_infs_right.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s t : Finset α} {a : α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Finset.image α α inst (fun (x : α) => @Min.min α (@SemilatticeInf.toMin α inst_1) a x) t)
          (@HasInfs.infs (Finset α) (@Finset.hasInfs α inst inst_1) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.image_subset_infs_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_subset_infs_left.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s t : Finset α} {b : α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Finset.image α α inst (fun (x : α) => @Min.min α (@SemilatticeInf.toMin α inst_1) x b) s)
          (@HasInfs.infs (Finset α) (@Finset.hasInfs α inst inst_1) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.diffs_subset_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.diffs_subset_left.h6 : ¬∀ {α : Type} [inst : DecidableEq α] [inst_1 : GeneralizedBooleanAlgebra α] {s t₁ t₂ : Finset α},
        s.diffs t₁ ⊆ s.diffs t₂ := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (BooleanAlgebra.toGeneralizedBooleanAlgebra) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.image_subset_diffs_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_subset_diffs_right.h6 : ¬∀ {α : Type} [inst : DecidableEq α] [inst_1 : GeneralizedBooleanAlgebra α] {s t : Finset α} {a : α},
        Finset.image (fun (x : α) => a \ x) t ⊆ s.diffs t := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (BooleanAlgebra.toGeneralizedBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (Bool.false)) (by
  decide +kernel)

-- Multiset.countP_cons_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.countP_cons_of_neg.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α} (s : Multiset α),
        Multiset.countP p (a ::ₘ s) = Multiset.countP p s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.eq_sub_of_add_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_sub_of_add_eq.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t u : Multiset α}, s = u - t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.mem_erase_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_erase_of_ne.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} {s : Multiset α}, a ∈ s.erase b ↔ a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Computation.exists_of_mem_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.exists_of_mem_map.h5 : ¬∀ {α β : Type} {f : α → β} {b : β} {s : Computation α}, ∃ a ∈ s, f a = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (Inhabited.default)) (by
  simp)

-- Multiset.erase_add_right_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.erase_add_right_neg.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α} (t : Multiset α), (s + t).erase a = s + t.erase a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.erase_le_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.erase_le_erase.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α} (a : α), s.erase a ≤ t.erase a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (1)) (by
  decide +kernel)

-- Computation.results_thinkN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.results_thinkN.h5 : ¬∀ {α : Type} {s : Computation α} {a : α} {m : ℕ} (n : ℕ), (s.thinkN n).Results a (m + n) := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0) (0) (0)) (by
  nofun)

-- Finset.image₂_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image₂_left.h5 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} [inst : DecidableEq α],
        @Eq (Finset α) (@Finset.image₂ α β α inst (fun (x : α) (x_1 : β) => x) s t) s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat)) (by
  decide +kernel)

-- Computation.mem_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.mem_map.h5 : ¬∀ {α β : Type} (f : α → β) {a : α} {s : Computation α}, f a ∈ Computation.map f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (Inhabited.default)) (by
  nofun)

-- Multiset.pmap_eq_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.pmap_eq_map.h5 : ¬∀ {α β : Type} (p : α → Prop) (f : α → β) (s : Multiset α), ∀ a ∈ s, p a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (({1} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.map_lt_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_lt_map.h5 : ¬∀ {α β : Type} {f : α → β} {s t : Multiset α}, Multiset.map f s < Multiset.map f t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Stream'.Seq.exists_of_mem_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.exists_of_mem_map.h5 : ¬∀ {α β : Type} {f : α → β} {b : β} {s : Stream'.Seq α}, ∃ a ∈ s, f a = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (Inhabited.default)) (by
  simp)

-- Stream'.Seq.mem_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.mem_map.h5 : ¬∀ {α β : Type} (f : α → β) {a : α} {s : Stream'.Seq α}, f a ∈ Stream'.Seq.map f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (Inhabited.default)) (by
  nofun)

-- Multiset.mem_map_of_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_map_of_injective.h3 : ¬∀ {α β : Type} {f : α → β} {a : α} {s : Multiset α}, f a ∈ Multiset.map f s ↔ a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (0) (({1} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.image_preimage_of_bijective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_preimage_of_bijective.h5 : ¬∀ {α β : Type} [inst : DecidableEq β] {f : α → β} (s : Finset β), Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  nofun)

-- Finset.image_injOn_powerset_of_injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_injOn_powerset_of_injOn.h5 : Not
      (∀ {α : Type} {s : Finset α} {β : Type} [inst : DecidableEq β] {f : α → β},
        @Set.InjOn (Finset α) (Finset β) (fun (x : Finset α) => @Finset.image α β inst f x)
          (@SetLike.coe (Finset (Finset α)) (Finset α) (@Finset.instSetLike (Finset α)) (@Finset.powerset α s))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (Nat) (instDecidableEqNat) (fun _ => 0 : Nat → Nat)) (by
  decide +kernel)

-- Multiset.map_le_map_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_le_map_iff.h3 : ¬∀ {α β : Type} {f : α → β} {s t : Multiset α}, Multiset.map f s ≤ Multiset.map f t ↔ s ≤ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (({0} : Multiset Nat) : Multiset ℕ) (({1} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.mem_of_mem_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_erase.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α} {b : α}, b ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0)) (by
  decide +kernel)

-- Finset.ne_of_mem_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ne_of_mem_erase.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, b ≠ a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0)) (by
  decide +kernel)

-- Finset.union_subset_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_subset_right.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) t
          u) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Multiset.find?_eq_some_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.find?_eq_some_iff.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α} {s : Multiset α}, {x : α | x ∈ s ∧ p x}.Subsingleton := fun hc_h => absurd (@hc_h (Bool) (fun _ => True : Bool → Prop) (fun (a : Bool) => instDecidableTrue) (Bool.false) (({true, false} : Multiset Bool) : Multiset Bool)) (by
  decide +kernel)

-- Finset.inter_subset_inter_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_subset_inter_left.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Min.min (Finset α) (@Finset.instMin α inst) s t) (@Min.min (Finset α) (@Finset.instMin α inst) s u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finsupp.coe_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.coe_mk.h5 : ¬∀ {α M : Type} [inst : Zero M] (f : α → M) (s : Finset α) (a : α), a ∈ s ↔ f a ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.mem_union_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_union_left.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α} (t : Finset α), a ∈ s ∪ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.mem_of_mem_inter_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_inter_right.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s₁ : Finset α} {s₂ : Finset α}, a ∈ s₂ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finsupp.coe_onFinset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.coe_onFinset.h5 : ¬∀ {α M : Type} [inst : Zero M] (s : Finset α) (f : α → M) (a : α), f a ≠ 0 → a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Finset.union_subset_union_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_subset_union_right.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t₁ t₂ : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Max.max (Finset α) (@Finset.instMax α inst) s t₁) (@Max.max (Finset α) (@Finset.instMax α inst) s t₂)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.mem_union_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_union_right.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {t : Finset α} {a : α} (s : Finset α), a ∈ s ∪ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finsupp.support_onFinset_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_onFinset_subset.h5 : ¬∀ {α M : Type} [inst : Zero M] {s : Finset α} {f : α → M} (a : α), f a ≠ 0 → a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Finset.inter_insert_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_insert_of_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s₁ s₂ : Finset α} {a : α}, s₁ ∩ Insert.insert a s₂ = Insert.insert a (s₁ ∩ s₂) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.insert_inter_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_inter_of_notMem.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s₁ s₂ : Finset α} {a : α},
        @Eq (Finset α)
          (@Min.min (Finset α) (@Finset.instMin α inst) (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s₁) s₂)
          (@Min.min (Finset α) (@Finset.instMin α inst) s₁ s₂)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.insert_sdiff_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_sdiff_of_notMem.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] (s : Finset α) {t : Finset α} {x : α},
        @Eq (Finset α)
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) (@Insert.insert α (Finset α) (@Finset.instInsert α inst) x s)
            t)
          (@Insert.insert α (Finset α) (@Finset.instInsert α inst) x
            (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.sdiff_sdiff_eq_sdiff_union, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_sdiff_eq_sdiff_union.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @Eq (Finset α)
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t u))
          (@Max.max (Finset α) (@Finset.instMax α inst) (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t) u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finsupp.uniqueEquiv_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.uniqueEquiv_apply.h4 : ¬∀ {α M : Type} [inst : Zero M] (a : α) (f : α →₀ M), Subsingleton α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.filter_subset_filter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_subset_filter.h5 : Not
      (∀ {α : Type} (p : α → Prop) [inst : @DecidablePred α p] {s t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Finset.filter α p inst s) (@Finset.filter α p inst t)) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.Nonempty.of_sups_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_sups_left.h5 : ¬∀ {α : Type} [inst : DecidableEq α] [inst : SemilatticeSup α] {s : Finset α} {t : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.Nonempty.image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.image.h4 : ¬∀ {α β : Type} [inst : DecidableEq β] {s : Finset α} (f : α → β), (Finset.image f s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.Nonempty.of_infs_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_infs_right.h5 : ¬∀ {α : Type} [inst : DecidableEq α] [inst : SemilatticeInf α] {s : Finset α} {t : Finset α}, t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.image_nontrivial_iff_of_injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_nontrivial_iff_of_injOn.h5 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s : Finset α},
        Iff (@Finset.Nontrivial β (@Finset.image α β inst f s)) (@Finset.Nontrivial α s)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun _ => 0 : Nat → Nat) (@Finset.mk Nat
      (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.product_image_fst, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.product_image_fst.h5 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} [inst : DecidableEq α],
        @Eq (Finset α)
          (@Finset.image (Prod α β) α inst (@Prod.fst α β)
            (@SProd.sprod (Finset α) (Finset β) (Finset (Prod α β)) (@Finset.instSProd α β) s t))
          s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.product_disjUnion, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.product_disjUnion.h5 : Not
      (∀ {α β : Type} {s : Finset α} {t t' : Finset β},
        @Disjoint (Finset β) (@Finset.instPartialOrder β) (@Finset.instOrderBot β) t t') := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finsupp.mem_frange_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mem_frange_of_mem.h5 : ¬∀ {α M : Type} [inst : Zero M] {x : α} {f : α →₀ M}, f x ∈ f.frange := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  decide +kernel)

-- Finset.product_image_snd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.product_image_snd.h5 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} [inst : DecidableEq β],
        @Eq (Finset β)
          (@Finset.image (Prod α β) β inst (@Prod.snd α β)
            (@SProd.sprod (Finset α) (Finset β) (Finset (Prod α β)) (@Finset.instSProd α β) s t))
          t) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.Nonempty.of_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_image.h5 : ¬∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.Nonempty.of_infs_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_infs_left.h5 : ¬∀ {α : Type} [inst : DecidableEq α] [inst : SemilatticeInf α] {s : Finset α} {t : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.mem_map_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_map_of_mem.h5 : ¬∀ {α β : Type} (f : α ↪ β) {a : α} {s : Finset α}, f a ∈ Finset.map f s := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (Bool.false) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.sup'_const, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_const.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.filter_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_cons.h5 : Not (∀ {α : Type} (p : α → Prop) [inst : @DecidablePred α p] {a : α} (s : Finset α), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.mem_union_of_disjoint, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_union_of_disjoint.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {x : α},
        Iff
          (@Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
            (@Max.max (Finset α) (@Finset.instMax α inst) s t) x)
          (Xor (@Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x)
            (@Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t x))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Sym.map_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.map_mk.h5 : ¬∀ {α β : Type} {n : ℕ} {f : α → β} {m : Multiset α}, m.card = n := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) (fun n => n + 1 : ℕ → ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.exists_mem_eq_sup', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_mem_eq_sup'.h4 : ¬∀ {α ι : Type} [inst : LinearOrder α] {s : Finset ι} (f : ι → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.sdiff_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_erase.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α}, s \ t.erase a = Insert.insert a (s \ t) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.filter_disjUnion, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_disjUnion.h5 : Not
      (∀ {α : Type} (p : α → Prop) [inst : @DecidablePred α p] (s t : Finset α),
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.coe_sup', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.coe_sup'.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.inf'_const, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_const.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.disjoint_insert_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_insert_erase.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        Iff
          (@Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) (@Finset.erase α inst s a)
            (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a t))
          (@Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.erase_union_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_union_of_mem.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {t : Finset α} {a : α} (s : Finset α),
        @Eq (Finset α) (@Max.max (Finset α) (@Finset.instMax α inst) (@Finset.erase α inst s a) t)
          (@Max.max (Finset α) (@Finset.instMax α inst) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.subset_insert_iff_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.subset_insert_iff_of_notMem.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        Iff
          (@LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            s (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a t))
          (@LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Set.BijOn.finsetCard_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.finsetCard_eq.h5 : Not (∀ {α β : Type} {s : Finset α} {t : Finset β} (e : α → β), @Eq Nat (@Finset.card α s) (@Finset.card β t)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Finset.card_le_card_of_surjOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_le_card_of_surjOn.h5 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} (f : α → β), @LE.le Nat instLENat (@Finset.card β t) (@Finset.card α s)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Ordnode.Bounded.mem_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.mem_lt.h5 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o : WithBot α} {x : α}, Ordnode.All (fun (x_1 : α) => x_1 < x) t := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (0)) (by
  decide +kernel)

-- Ordnode.Bounded.dual, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.dual.h5 : Not
      (∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        @Ordnode.Bounded (OrderDual α) (@OrderDual.instPreorder α inst) (@Ordnode.dual (OrderDual α) t) o₂ o₁) := fun hc_h => absurd (@hc_h (Nat) (Nat.instPreorder) (@Ordnode.nil Nat) (@OfNat.ofNat (WithBot Nat) (nat_lit 0)
      (@Zero.toOfNat0 (WithBot Nat) (@WithBot.zero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))) (@OfNat.ofNat (WithTop Nat) (nat_lit 0)
      (@Zero.toOfNat0 (WithTop Nat) (@WithTop.zero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))) (by
  nofun)

-- Finset.dens_sdiff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.dens_sdiff.h5 : ¬∀ {α : Type} [inst : Fintype α] {s t : Finset α} [inst_1 : DecidableEq α], (t \ s).dens = t.dens - s.dens := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (({false} : Finset Bool) : Finset Bool) (instDecidableEqBool)) (by
  decide +kernel)

-- Finset.dens_union_of_disjoint, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.dens_union_of_disjoint.h5 : ¬∀ {α : Type} [inst : Fintype α] {s t : Finset α} [inst_1 : DecidableEq α], (s ∪ t).dens = s.dens + t.dens := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (instDecidableEqBool)) (by
  decide +kernel)

-- Ordnode.Bounded.mem_gt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.mem_gt.h5 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o : WithTop α} {x : α}, Ordnode.All (fun (x_1 : α) => x_1 > x) t := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (0)) (by
  decide +kernel)

-- Ordnode.Bounded.weak, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.weak.h5 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α}, t.Bounded ⊥ ⊤ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (0) (0)) (by
  nofun)

-- Finset.replicate_mem_sym, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.replicate_mem_sym.h4 : ¬∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α] (n : ℕ), Sym.replicate n a ∈ s.sym n := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (instDecidableEqNat) (1)) (by
  decide +kernel)

-- Finset.choose_property, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.choose_property.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Finset α), ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.erase_nonempty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_nonempty.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α},
        Iff (@Finset.Nonempty α (@Finset.erase α inst s a)) (@Finset.Nontrivial α s)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Finset.insert_erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_erase.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α}, Insert.insert a (s.erase a) = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.choose_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.choose_spec.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Finset α), ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.Nontrivial.erase_nonempty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nontrivial.erase_nonempty.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α}, (s.erase a).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.disjoint_disjUnion_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_disjUnion_right.h4 : Not
      (∀ {α : Type} {s : Finset α} {t u : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) t u) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.card_union_of_disjoint, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_union_of_disjoint.h4 : Not
      (∀ {α : Type} {s t : Finset α} [inst : DecidableEq α],
        @Eq Nat (@Finset.card α (@Max.max (Finset α) (@Finset.instMax α inst) s t))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Finset.card α s) (@Finset.card α t))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.card_sdiff_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_sdiff_of_subset.h4 : Not
      (∀ {α : Type} {s t : Finset α} [inst : DecidableEq α],
        @Eq Nat (@Finset.card α (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t s))
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@Finset.card α t) (@Finset.card α s))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.card_sdiff_add_card_eq_card, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_sdiff_add_card_eq_card.h4 : Not
      (∀ {α : Type} {s t : Finset α} [inst : DecidableEq α],
        @Eq Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@Finset.card α (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t s)) (@Finset.card α s))
          (@Finset.card α t)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.card_erase_lt_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_erase_lt_of_mem.h4 : ¬∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α], (s.erase a).card < s.card := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.card_sdiff_comm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_sdiff_comm.h4 : Not
      (∀ {α : Type} {s t : Finset α} [inst : DecidableEq α],
        @Eq Nat (@Finset.card α (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t))
          (@Finset.card α (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t s))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.card_erase_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_erase_of_mem.h4 : Not
      (∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α],
        @Eq Nat (@Finset.card α (@Finset.erase α inst s a))
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@Finset.card α s)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.Nonempty.sym, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.sym.h3 : ¬∀ {α : Type} {s : Finset α} [inst : DecidableEq α] (n : ℕ), (s.sym n).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat) (1)) (by
  decide +kernel)

-- Finset.not_isDiag_mk_of_mem_offDiag, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.not_isDiag_mk_of_mem_offDiag.h4 : ¬∀ {α : Type} {s : Finset α} {a b : α}, ¬s(a, b).IsDiag := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0)) (by
  decide +kernel)

-- Nat.Coprime.prod_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.prod_left.h4 : Not (∀ {ι : Type} {t : Finset ι} {s : ι → Nat} {x : Nat}, (∏ i ∈ t, s i).Coprime x) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun _ => 0 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Multiset.find?_eq_choose, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.find?_eq_choose.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] {s : Multiset α}, ∃! x : α, x ∈ s ∧ p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Multiset.find?_eq_none_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.find?_eq_none_iff.h4 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {s : Multiset α}, {x : α | x ∈ s ∧ p x}.Subsingleton := fun hc_h => absurd (@hc_h (Bool) (fun _ => True : Bool → Prop) (fun (a : Bool) => instDecidableTrue) (({true, false} : Multiset Bool) : Multiset Bool)) (by
  decide +kernel)

-- Computation.of_results_think, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.of_results_think.h4 : ¬∀ {α : Type} {s : Computation α} {a : α} {n : ℕ}, ∃ (m : ℕ), s.Results a m ∧ n = m + 1 := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0) (0)) (by
  simp)

-- Stream'.Seq.destruct_eq_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.destruct_eq_cons.h4 : ¬∀ {α : Type} {s : Stream'.Seq α} {a : α} {s' : Stream'.Seq α}, s = Stream'.Seq.cons a s' := fun hc_h => absurd (@hc_h (ℕ) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (0) (Inhabited.default)) (by
  simp)

-- Stream'.Seq.mem_cons_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.mem_cons_of_mem.h4 : ¬∀ {α : Type} (y : α) {a : α} {s : Stream'.Seq α}, a ∈ Stream'.Seq.cons y s := fun hc_h => absurd (@hc_h (ℕ) (0) (1) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ)) (by
  simp)

-- Stream'.Seq.of_mem_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.of_mem_append.h4 : ¬∀ {α : Type} {s₁ s₂ : Stream'.Seq α} {a : α}, a ∈ s₁ ∨ a ∈ s₂ := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (Inhabited.default) (0)) (by
  nofun)

-- Stream'.Seq.Pairwise.cons_elim, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.Pairwise.cons_elim.h4 : ¬∀ {α : Type} {R : α → α → Prop} {hd : α} {tl : Stream'.Seq α}, (∀ x ∈ tl, R hd x) ∧ Stream'.Seq.Pairwise R tl := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ)) (by
  simp)

-- Multiset.toEnumFinset_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.toEnumFinset_mono.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {m₁ m₂ : Multiset α}, m₁.toEnumFinset ⊆ m₂.toEnumFinset := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.cons_lt_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.cons_lt_cons.h4 : ¬∀ {α : Type} {s t : Multiset α} (a : α), a ::ₘ s < a ::ₘ t := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  simp)

-- Multiset.cons_le_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.cons_le_of_notMem.h4 : ¬∀ {α : Type} {s t : Multiset α} {a : α}, a ::ₘ s ≤ t ↔ a ∈ t ∧ s ≤ t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Multiset.ext', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.ext'.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s = t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.erase_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.erase_of_notMem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, s.erase a = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Sym.mem_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.mem_mk.h4 : ¬∀ {α : Type} {n : ℕ} (a : α) (s : Multiset α), s.card = n := fun hc_h => absurd (@hc_h (ℕ) (1) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.le_of_add_le_add_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.le_of_add_le_add_right.h4 : ¬∀ {α : Type} {s t : Multiset α} {u : Multiset α}, s ≤ t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.card_sub, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.card_sub.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, (s - t).card = s.card - t.card := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) (({1} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Nat.multinomial_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multinomial_cons.h3 : Not (∀ {α : Type} {s : Finset α} {a : α} (f : α → Nat), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Multiset.sub_add_cancel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sub_add_cancel.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s - t + t = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.card_erase_lt_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.card_erase_lt_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, (s.erase a).card < s.card := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.card_erase_add_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.card_erase_add_one.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, (s.erase a).card + 1 = s.card := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Fintype.card_of_finset', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_of_finset'.h3 : ¬∀ {α : Type} {p : Set α} (s : Finset α) [inst : Fintype ↑p], Fintype.card ↑p = s.card := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true}))) (by
  decide +kernel)

-- CovBy.exists_finset_erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CovBy.exists_finset_erase.h4 : ¬∀ {α : Type} {s t : Finset α} [inst : DecidableEq α], ∃ a ∈ t, t.erase a = s := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.card_Icc_finset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_Icc_finset.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Eq Nat
          (@Finset.card (Finset α)
            (@Finset.Icc (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))
              (@Finset.instLocallyFiniteOrder α inst) s t))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@Finset.card α t) (@Finset.card α s)))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.Icc_eq_image_powerset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Icc_eq_image_powerset.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Eq (Finset (Finset α))
          (@Finset.Icc (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))
            (@Finset.instLocallyFiniteOrder α inst) s t)
          (@Finset.image (Finset α) (Finset α) (fun (a b : Finset α) => @Finset.decidableEq α inst a b)
            (fun (x : Finset α) => @Max.max (Finset α) (@Finset.instMax α inst) s x)
            (@Finset.powerset α (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t s)))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Multiset.Nodup.of_map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.of_map.h4 : ¬∀ {α β : Type} {s : Multiset α} (f : α → β), s.Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Multiset.nodup_map_iff_inj_on, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.nodup_map_iff_inj_on.h4 : ¬∀ {α β : Type} {f : α → β} {s : Multiset α}, (Multiset.map f s).Nodup ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Set.Sized.card_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Sized.card_le.h4 : ¬∀ {α : Type} [inst : Fintype α] {𝒜 : Finset (Finset α)} {r : ℕ}, 𝒜.card ≤ (Fintype.card α).choose r := fun hc_h => absurd (@hc_h (Prop) («Prop».fintype) (⊤) (0)) (by
  decide +kernel)

-- Multiset.Nodup.erase_eq_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.erase_eq_filter.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (a : α) {s : Multiset α}, s.erase a = Multiset.filter (fun (x : α) => x ≠ a) s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.notMem_erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.notMem_erase.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, a ∉ s.erase a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.filter.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] {s : Multiset α}, (Multiset.filter p s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.inter_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.inter_left.h4 : ¬∀ {α : Type} {s : Multiset α} [inst : DecidableEq α] (t : Multiset α), (s ∩ t).Nodup := fun hc_h => absurd (@hc_h (Bool) (({true, true} : Multiset Bool) : Multiset Bool) (instDecidableEqBool) (({true, true} : Multiset Bool) : Multiset Bool)) (by
  decide +kernel)

-- Multiset.Nodup.inter_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.inter_right.h4 : ¬∀ {α : Type} {t : Multiset α} [inst : DecidableEq α] (s : Multiset α), (s ∩ t).Nodup := fun hc_h => absurd (@hc_h (Bool) (({true, true} : Multiset Bool) : Multiset Bool) (instDecidableEqBool) (({true, true} : Multiset Bool) : Multiset Bool)) (by
  decide +kernel)

-- Multiset.eq_union_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_union_left.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s ∪ t = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.eq_union_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_union_right.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s ∪ t = t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Disjoint.dedup_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Disjoint.dedup_add.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, (s + t).dedup = s.dedup + t.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.le_dedup_iff_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.le_dedup_iff_le.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s ≤ t.dedup ↔ s ≤ t := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (({true, true} : Multiset Bool) : Multiset Bool) (({true, true} : Multiset Bool) : Multiset Bool)) (by
  decide +kernel)

-- Multiset.dedup_cons_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.dedup_cons_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, (a ::ₘ s).dedup = s.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.offDiag_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.offDiag_insert.h4 : Not
      (∀ {α : Type} {s : Finset α} [inst : DecidableEq α] {a : α},
        @Eq (Finset (Prod α α)) (@Finset.offDiag α (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s))
          (@Max.max (Finset (Prod α α))
            (@Finset.instMax (Prod α α) fun (a b : Prod α α) => @instDecidableEqProd α α inst inst a b)
            (@Max.max (Finset (Prod α α))
              (@Finset.instMax (Prod α α) fun (a b : Prod α α) => @instDecidableEqProd α α inst inst a b)
              (@Finset.offDiag α s)
              (@SProd.sprod (Finset α) (Finset α) (Finset (Prod α α)) (@Finset.instSProd α α)
                (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a) s))
            (@SProd.sprod (Finset α) (Finset α) (Finset (Prod α α)) (@Finset.instSProd α α) s
              (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a)))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Multiset.ndinsert_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.ndinsert_of_notMem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, Multiset.ndinsert a s = a ::ₘ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.ndinter_eq_inter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.ndinter_eq_inter.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s.ndinter t = s ∩ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0, 0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.ndinter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.ndinter.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Multiset α} (t : Multiset α), (s.ndinter t).Nodup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0, 0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.length_ndinsert_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.length_ndinsert_of_notMem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, (Multiset.ndinsert a s).card = s.card + 1 := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.insert_eq_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_eq_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α}, Insert.insert a s = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.insert_val_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_val_of_notMem.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Finset α},
        @Eq (Multiset α) (@Finset.val α (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s))
          (@Multiset.cons α a (@Finset.val α s))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.cons_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_subset.h4 : Not (∀ {α : Type} {s : Finset α} {t : Finset α} {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.ssubset_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ssubset_insert.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α},
        @LT.lt (Finset α) (@Preorder.toLT (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
          (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.mem_disjUnion, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_disjUnion.h3 : Not
      (∀ {α : Type} {s t : Finset α} {a : α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.exists_next_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_next_left.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {x : α} {s : Finset α}, ∃ y ∈ s, y < x ∧ ∀ z ∈ s, z < x → z ≤ y := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.singleton_inter_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.singleton_inter_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Finset α}, {a} ∩ s = {a} := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.Nonempty.inl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.inl.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Finset α}, (s ∪ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.inter_singleton_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_singleton_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Finset α}, s ∩ {a} = {a} := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.sdiff_sdiff_eq_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_sdiff_eq_self.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Eq (Finset α)
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t)) t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.insert_sdiff_self_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_sdiff_self_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α}, Insert.insert a (s \ {a}) = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.insert_sdiff_cancel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_sdiff_cancel.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α},
        @Eq (Finset α)
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s)
            s)
          (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.min'_erase_ne_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_erase_ne_self.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {x : α} {s : Finset α}, (s.erase x).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.max_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max_of_mem.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a : α}, ∃ (b : α), s.max = ↑b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  simp)

-- Finset.card_le_sdiff_of_interleaved, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_le_sdiff_of_interleaved.h4 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s t : Finset α},
        @LE.le Nat instLENat (@Finset.card α s)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@Finset.card α
              (@SDiff.sdiff (Finset α) (@Finset.instSDiff α fun (a b : α) => @LinearOrder.toDecidableEq α inst a b) t s))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.card_le_of_interleaved, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_le_of_interleaved.h4 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s t : Finset α},
        @LE.le Nat instLENat (@Finset.card α s)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Finset.card α t)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.max_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max_le.h4 : Not
      (∀ {α : Type} [inst : LinearOrder α] {M : WithBot α} {s : Finset α},
        @LE.le (WithBot α)
          (@Preorder.toLE (WithBot α)
            (@WithBot.instPreorder α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))))
          (@Finset.max α inst s) M) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@OfNat.ofNat (WithBot Nat) (nat_lit 0)
      (@Zero.toOfNat0 (WithBot Nat) (@WithBot.zero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.le_max, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_max.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {a : α} {s : Finset α}, ↑a ≤ s.max := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.filter_false_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_false_of_mem.h4 : Not
      (∀ {α : Type} {p : α → Prop} [inst : @DecidablePred α p] {s : Finset α},
        @Eq (Finset α) (@Finset.filter α p inst s)
          (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.max'_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_insert.h4 : ¬∀ {α : Type} [inst : LinearOrder α] (a : α) (s : Finset α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.min'_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_insert.h4 : ¬∀ {α : Type} [inst : LinearOrder α] (a : α) (s : Finset α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.range_orderEmbOfFin, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.range_orderEmbOfFin.h4 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {k : ℕ}, s.card = k := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1)) (by
  decide +kernel)

-- Finset.listMap_orderEmbOfFin_finRange, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.listMap_orderEmbOfFin_finRange.h4 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {k : ℕ}, s.card = k := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1)) (by
  decide +kernel)

-- Fintype.card_ofFinset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_ofFinset.h3 : ¬∀ {α : Type} {p : Set α} (s : Finset α) (x : α), x ∈ s ↔ x ∈ p := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Fintype.subtype_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.subtype_card.h3 : ¬∀ {α : Type} {p : α → Prop} (s : Finset α) (x : α), x ∈ s ↔ p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Multiset.eq_replicate_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_replicate_of_mem.h3 : ¬∀ {α : Type} {a : α} {s : Multiset α}, s = Multiset.replicate s.card a := fun hc_h => absurd (@hc_h (ℕ) (0) (({1} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- CovBy.finset_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CovBy.finset_coe.h3 : Not
      (∀ {α : Type} {s t : Finset α},
        @CovBy (Set α)
          (@Preorder.toLT (Set α)
            (@PartialOrder.toPreorder (Set α)
              (@ConditionallyCompletePartialOrderSup.toPartialOrder (Set α)
                (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup (Set α)
                  (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder (Set α)
                    (@CompleteLattice.toConditionallyCompleteLattice (Set α)
                      (@CompleteBooleanAlgebra.toCompleteLattice (Set α)
                        (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set α)
                          (@Set.instCompleteAtomicBooleanAlgebra α)))))))))
          (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) (@SetLike.coe (Finset α) α (@Finset.instSetLike α) t)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  simp)

-- CovBy.card_finset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CovBy.card_finset.h3 : ¬∀ {α : Type} {s t : Finset α}, s.card ⋖ t.card := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- CovBy.exists_multiset_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CovBy.exists_multiset_cons.h3 : ¬∀ {α : Type} {s t : Multiset α}, ∃ (a : α), a ::ₘ s = t := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Finset.covBy_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.covBy_cons.h3 : Not (∀ {α : Type} {s : Finset α} {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.mem_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_mk.h3 : ¬∀ {α : Type} {a : α} {s : Multiset α}, s.Nodup := fun hc_h => absurd (@hc_h (ℕ) (0) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.subset_of_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.subset_of_eq.h3 : Not
      (∀ {α : Type} {s t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
          t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.Nonempty.of_compls, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_compls.h3 : ¬∀ {α : Type} [inst : BooleanAlgebra α] {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (Bool) (Bool.instBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.exists_of_ssubset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_of_ssubset.h3 : ¬∀ {α : Type} {s₁ s₂ : Finset α}, ∃ x ∈ s₂, x ∉ s₁ := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.exists_disjoint_union_of_even_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_disjoint_union_of_even_card.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α},
        ∃ (t : Finset α) (u : Finset α), t ∪ u = s ∧ Disjoint t u ∧ t.card = u.card := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide)

-- Multiset.powersetCard_eq_empty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.powersetCard_eq_empty.h3 : ¬∀ {α : Type} (n : ℕ) {s : Multiset α}, Multiset.powersetCard n s = 0 := fun hc_h => absurd (@hc_h (ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.revzip_powersetAux', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.revzip_powersetAux'.h3 : ¬∀ {α : Type} {l : List α} ⦃x : Multiset α × Multiset α⦄, x.1 + x.2 = ↑l := fun hc_h => absurd (@hc_h (ℕ) ([0]) ((0, 0))) (by
  decide +kernel)

-- Finset.exists_mem_notMem_of_card_lt_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_mem_notMem_of_card_lt_card.h3 : ¬∀ {α : Type} {s t : Finset α}, ∃ e ∈ t, e ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Computation.length_thinkN, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.length_thinkN.h2 : ¬∀ {α : Type} (s : Computation α) (n : ℕ), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- Finsupp.exists_le_degree_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.exists_le_degree_eq.h3 : ¬∀ {σ : Type} (f : σ →₀ ℕ) (n : ℕ), ∃ g ≤ f, Finsupp.degree g = n := fun hc_h => absurd (@hc_h (ℕ) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ) (2)) (by
  simp)

-- Set.toFinset_ofFinset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.toFinset_ofFinset.h3 : ¬∀ {α : Type} {p : Set α} (s : Finset α) (x : α), x ∈ s ↔ x ∈ p := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.Nonempty.dens_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.dens_pos.h3 : ¬∀ {α : Type} [inst : Fintype α] {s : Finset α}, 0 < s.dens := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.exists_subset_card_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_subset_card_eq.h3 : ¬∀ {α : Type} {s : Finset α} {n : ℕ}, ∃ t ⊆ s, t.card = n := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1)) (by
  decide +kernel)

-- Finset.sorted_last_eq_max', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sorted_last_eq_max'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α},
        (s.sort fun (a b : α) => a ≤ b).length - 1 < (s.sort fun (a b : α) => a ≤ b).length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Stream'.Seq.length_take_of_le_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.length_take_of_le_length.h3 : ¬∀ {α : Type} {s : Stream'.Seq α} {n : ℕ}, (Stream'.Seq.take n s).length = n := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (1)) (by
  decide +kernel)

-- Finset.card_ne_zero_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_ne_zero_of_mem.h3 : ¬∀ {α : Type} {s : Finset α} {a : α}, s.card ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.powersetCard_nonempty_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.powersetCard_nonempty_of_le.h3 : ¬∀ {α : Type} {n : ℕ} {s : Finset α}, (Finset.powersetCard n s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (1) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.forall_mem_const, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.forall_mem_const.h2 : ¬∀ {α : Type} {s : Finset α} {p : Prop}, (∀ x ∈ s, p) ↔ p := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (False)) (by
  decide +kernel)

-- Multiset.Nodup.of_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.of_cons.h3 : ¬∀ {α : Type} {s : Multiset α} {a : α}, s.Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Multiset.exists_cons_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.exists_cons_of_mem.h3 : ¬∀ {α : Type} {s : Multiset α} {a : α}, ∃ (t : Multiset α), s = a ::ₘ t := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  simp)

-- Multiset.Nodup.notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.notMem.h3 : ¬∀ {α : Type} {s : Multiset α} {a : α}, a ∉ s := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Finset.ssubset_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ssubset_cons.h3 : Not (∀ {α : Type} {s : Finset α} {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.eq_singleton_or_nontrivial, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_singleton_or_nontrivial.h3 : ¬∀ {α : Type} {s : Finset α} {a : α}, s = {a} ∨ s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.max'_eq_sup', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_eq_sup'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.disjUnion_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjUnion_singleton.h3 : Not
      (∀ {α : Type} (s : Finset α) (a : α),
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s
          (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.singleton_disjUnion, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.singleton_disjUnion.h3 : Not
      (∀ {α : Type} (a : α) (t : Finset α),
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α)
          (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a) t) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.isLUB_sup', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isLUB_sup'.h3 : ¬∀ {α : Type} [inst : SemilatticeSup α] {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.coe_disjUnion, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.coe_disjUnion.h3 : Not (∀ {α : Type} {s t : Finset α}, @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.card_disjUnion, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_disjUnion.h3 : Not (∀ {α : Type} (s t : Finset α), @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.coe_min', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.coe_min'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.min'_le_max', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_le_max'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.toDual_max', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.toDual_max'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.min'_lt_max'_of_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_lt_max'_of_card.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α), 1 < s.card := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Multiset.Nodup.sym2, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.sym2.h2 : ¬∀ {α : Type} {m : Multiset α}, m.sym2.Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.Nonempty.to_subtype, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.to_subtype.h2 : ¬∀ {α : Type} {s : Finset α}, Nonempty ↥s := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.Nonempty.coe_sort, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.coe_sort.h2 : ¬∀ {α : Type} {s : Finset α}, Nonempty ↥s := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.Nonempty.exists_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.exists_mem.h2 : ¬∀ {α : Type} {s : Finset α}, ∃ (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.eq_empty_of_forall_notMem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_empty_of_forall_notMem.h2 : Not
      (∀ {α : Type} {s : Finset α},
        @Eq (Finset α) s (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Multiset.eq_zero_of_forall_notMem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_zero_of_forall_notMem.h2 : ¬∀ {α : Type} {s : Multiset α}, s = 0 := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.exists_mem_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.exists_mem_of_ne_zero.h2 : ¬∀ {α : Type} {s : Multiset α}, ∃ (a : α), a ∈ s := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Finset.Nontrivial.two_le_card, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nontrivial.two_le_card.h2 : ¬∀ {α : Type} {s : Finset α}, 2 ≤ s.card := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.nonempty_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.nonempty_mk.h2 : ¬∀ {α : Type} {m : Multiset α}, m.Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.attach, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.attach.h2 : ¬∀ {α : Type} {s : Multiset α}, s.attach.Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Computation.get_think, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.get_think.h2 : ¬∀ {α : Type} (s : Computation α), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default)) (by
  nofun)

-- Finset.card_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_mk.h2 : ¬∀ {α : Type} {m : Multiset α}, m.Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Computation.Terminates.term, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.Terminates.term.h2 : ¬∀ {α : Type} {s : Computation α}, ∃ (a : α), a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default)) (by
  nofun)

-- Stream'.Seq.destruct_eq_none, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.destruct_eq_none.h2 : ¬∀ {α : Type} {s : Stream'.Seq α}, s = Stream'.Seq.nil := fun hc_h => absurd (@hc_h (ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ)) (by
  simp)

-- Finset.Nontrivial.of_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nontrivial.of_coe.h2 : ¬∀ {α : Type} {s : Finset α}, s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.card_le_one_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_le_one_of_subsingleton.h1 : Not
      (∀ {α : Type} (s : Finset α),
        @LE.le Nat instLENat (@Finset.card α s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.Nonempty.exists_eq_singleton_or_nontrivial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.exists_eq_singleton_or_nontrivial.h2 : ¬∀ {α : Type} {s : Finset α}, (∃ (a : α), s = {a}) ∨ s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.Nonempty.exists_cons_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.exists_cons_eq.h2 : ¬∀ {α : Type} {s : Finset α}, ∃ (t : Finset α) (a : α) (ha : a ∉ t), Finset.cons a t ha = s := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.exists_notMem_of_card_lt_enatCard, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_notMem_of_card_lt_enatCard.h2 : ¬∀ {α : Type} {s : Finset α}, ∃ (a : α), a ∉ s := fun hc_h => absurd (@hc_h (Bool) ({ val := {Bool.true, Bool.false}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

