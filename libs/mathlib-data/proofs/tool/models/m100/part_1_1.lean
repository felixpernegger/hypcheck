import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

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

-- Finset.sup'_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_congr.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s t : Finset β} {f g : β → α}, s = t → (∀ x ∈ s, f x = g x) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) _ ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) rfl (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Ordnode.Bounded.of_gt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.of_gt.h6 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α} {x : α},
        Ordnode.nil.Bounded (↑x) o₂ → Ordnode.All (fun (x_1 : α) => x_1 > x) t → t.Bounded (↑x) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 1 Ordnode.nil) (0) (1) (0) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Finset.sup_le_of_le_directed, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_le_of_le_directed.h4 : ¬∀ {α : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] (s : Set α),
        DirectedOn (fun (x1 x2 : α) => x1 ≤ x2) s → ∀ (t : Finset α), (∀ x ∈ t, ∃ y ∈ s, x ≤ y) → ∃ x ∈ s, t.sup id ≤ x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({x : ℕ | False}) (by
  simp) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  simp)) (by
  simp)

-- Finset.Nonempty.biUnion, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.biUnion.h5.inst : ¬({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.biUnion fun (a : ℕ) =>
          { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }).Nonempty := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.biUnion.h5.prem0 : ∀ x ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      ((fun (a : ℕ) => { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) x).Nonempty := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.Nonempty.biUnion.h5 : ¬∀ {α β : Type} {s : Finset α} {t : α → Finset β} [inst : DecidableEq β],
        (∀ x ∈ s, (t x).Nonempty) → (s.biUnion t).Nonempty := fun hc_h => HypCheckProof.Finset.Nonempty.biUnion.h5.inst (@hc_h (ℕ) (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ) => { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat) HypCheckProof.Finset.Nonempty.biUnion.h5.prem0)

-- Multiset.fold_cons'_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_cons'_left.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b a : α) (s : Multiset α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.cons_subset_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_subset_cons.h4 : Not (∀ {α : Type} {s t : Finset α} {a : α} {ht : a ∉ t}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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

-- Finset.insert_compl_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_compl_insert.h5 : ¬∀ {α : Type} {s : Finset α} [inst : Fintype α] [inst_1 : DecidableEq α] {a : α},
        Insert.insert a (Insert.insert a s)ᶜ = sᶜ := fun hc_h => absurd (@hc_h (Bool) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (Bool.fintype) (instDecidableEqBool) (Bool.true)) (by
  decide +kernel)

-- Multiset.filter_le_filter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.filter_le_filter.h5 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] {s t : Multiset α}, Multiset.filter p s ≤ Multiset.filter p t := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.union_le_union_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.union_le_union_right.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α} (u : Multiset α), s ∪ u ≤ t ∪ u := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.insert_subset_insert_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_subset_insert_iff.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        Iff
          (@LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s)
            (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a t))
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

-- Finset.sdiff_subset_sdiff_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_subset_sdiff_right.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} (u : Finset α),
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) u t) (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) u s)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Finset.sdiff_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_erase.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α}, s \ t.erase a = Insert.insert a (s \ t) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.choose_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.choose_spec.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Finset α), ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.choose_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.choose_mem.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Finset α), ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Multiset.nodup_map_iff_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.nodup_map_iff_of_injective.h4 : ¬∀ {α β : Type} {s : Multiset α} {f : α → β}, (Multiset.map f s).Nodup ↔ s.Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0, 1} : Multiset Nat) : Multiset ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.ndinsert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.ndinsert.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Multiset α} (a : α), (Multiset.ndinsert a s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0, 0} : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Finset.le_max, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_max.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {a : α} {s : Finset α}, ↑a ≤ s.max := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

