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

-- Cycle.forall_eq_of_chain, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.forall_eq_of_chain.h9 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : IsTrans α r] [inst : Std.Antisymm r],
        Cycle.Chain r s → ∀ {a b : α}, a ∈ s → a = b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) _ _ (by
  simp) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.fold_image_idem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_image_idem.h4.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
theorem HypCheckProof.Finset.fold_image_idem.h4 : ¬∀ {α β γ : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} [inst : DecidableEq α] {g : γ → α}
        {s : Finset γ} [hi : Std.IdempotentOp op], Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_image_idem.h4.inst (@hc_h (ℕ) (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) (0) (instDecidableEqNat) (fun (n : ℕ) => n + 1) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (@Std.IdempotentOp.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))))

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

-- Finset.eq_of_mem_cons_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_mem_cons_of_notMem.h5 : ¬∀ {α : Type} {s : Finset α} {a b : α}, a ∉ s → b ∉ s → b = a := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.sort_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_eq.h6 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

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

-- Finset.inf'_image₂_right, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_image₂_right.h10 : ¬∀ {α β γ δ : Type} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β} [inst_1 : SemilatticeInf δ]
        (g : γ → δ), (Finset.image₂ f s t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (fun a b => a - b : ℕ → ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Nat.instLattice.toSemilatticeInf) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.Subset.antisymm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Subset.antisymm.h4 : Not
      (∀ {α : Type} {s₁ s₂ : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s₁
            s₂ →
          @Eq (Finset α) s₁ s₂) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.le_sup'_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_sup'_iff.h4 : ¬∀ {α ι : Type} [inst : LinearOrder α] {s : Finset ι} {f : ι → α} {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.union_subset_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_subset_left.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {t : Finset α} {u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
          u) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true))))) (by
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

