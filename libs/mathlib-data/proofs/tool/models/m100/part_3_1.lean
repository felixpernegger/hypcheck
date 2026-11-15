import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Multiset.foldl_induction', hypothesis 9: necessary
/- FAILED: 5:3: `simp` made no progress | 9:3: `simp` made no progress | 5:3: `simp` made no progress | 9:3: `simp` made no progress | 2:83: failed to synthesize instance of type class
  RightCommutative fun a b => a - b

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 62:25: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 2:83: failed to synthesize instance of type class
  RightCommutative fun a b => a - b

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 4:192: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldl_induction'.h9 : ¬∀ {α β : Type} (f : β → α → β) [inst : RightCommutative f] (x : β) (q : α → Prop) (p : β → Prop) (s : Multiset α),
        (∀ (a : α) (b : β), q a → p b → p (f b a)) → (∀ a ∈ s, q a) → p (Multiset.foldl f x s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (@RightCommutative.mk (Nat) (Nat) (fun (a b : Nat) => @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b) (by (try dsimp only);   grind)) (1) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) ((0 : Multiset Nat) : Multiset ℕ) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

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

-- Finset.exists_equiv_extend_of_card_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_equiv_extend_of_card_eq.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {t : Finset β} {s : Finset α} {f : α → β},
        Finset.image f s ⊆ t → Set.InjOn f ↑s → ∃ (g : α ≃ ↥t), ∀ i ∈ s, ↑(g i) = f i := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.of_lt.h6 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.nil.Bounded o₁ ↑x → Ordnode.All (fun (x_1 : α) => x_1 < x) t → Ordnode.Valid' o₁ t ↑x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (1) (0) (0) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Multiset.countP_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.countP_congr.h3 : ¬∀ {α : Type} {s s' : Multiset α} {p p' : α → Prop} [inst : DecidablePred p] [inst_1 : DecidablePred p'],
        (∀ x ∈ s, p x = p' x) → Multiset.countP p s = Multiset.countP p' s' := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableEqNat a 0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Cycle.Chain.eq_nil_of_irrefl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.eq_nil_of_irrefl.h5 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : IsTrans α r] [inst : Std.Irrefl r], s = Cycle.nil := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) _ _) (by
  decide +kernel)

-- Finset.mem_of_mem_insert_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_insert_of_ne.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, b ∈ Insert.insert a s → b ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.inter_congr_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_congr_left.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Min.min (Finset α) (@Finset.instMin α inst) s u) t →
          @Eq (Finset α) (@Min.min (Finset α) (@Finset.instMin α inst) s t)
            (@Min.min (Finset α) (@Finset.instMin α inst) s u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Cycle.next_reverse_eq_prev', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.next_reverse_eq_prev'.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Cycle α), s.reverse.Nodup → ∀ (x : α), x ∈ s.reverse := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (∅) (by
  decide) (0)) (by
  decide +kernel)

-- Finset.orderEmbOfFin_last, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.orderEmbOfFin_last.h5 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {k : ℕ}, s.card = k → 0 < k := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) _ rfl) (by
  decide +kernel)

-- Finset.min'_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_subset.h5 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s t : Finset α},
        @Finset.Nonempty α s →
          @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
            t) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
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

-- Finset.inf'_comp_eq_map, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_comp_eq_map.h7 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] {s : Finset γ} {f : γ ↪ β} (g : β → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Multiset.foldr_swap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldr_swap.h3 : ¬∀ {α β : Type} (f : α → β → β) (b : β) (s : Multiset α), LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Computation.exists_of_mem_bind, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.exists_of_mem_bind.h5 : ¬∀ {α β : Type} {s : Computation α} {f : α → Computation β} {b : β}, ∃ a ∈ s, b ∈ f a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Inhabited.default) (fun (a : ℕ) => Inhabited.default) (0)) (by
  nofun)

-- Stream'.Seq.mem_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.mem_map.h5 : ¬∀ {α β : Type} (f : α → β) {a : α} {s : Stream'.Seq α}, f a ∈ Stream'.Seq.map f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (Inhabited.default)) (by
  nofun)

-- Stream'.Seq.Pairwise_cons_cons_head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.Pairwise_cons_cons_head.h5 : ¬∀ {α : Type} {R : α → α → Prop} {hd tl_hd : α} {tl_tl : Stream'.Seq α}, R hd tl_hd := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (Inhabited.default)) (by
  decide +kernel)

-- Finset.max_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max_of_mem.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a : α}, ∃ (b : α), s.max = ↑b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  simp)

-- Multiset.card_lt_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.card_lt_card.h3 : ¬∀ {α : Type} {s t : Multiset α}, s.card < t.card := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Computation.length_thinkN, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.length_thinkN.h2 : ¬∀ {α : Type} (s : Computation α) (n : ℕ), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- Finset.mk_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mk_cons.h3 : ¬∀ {α : Type} {a : α} {s : Multiset α}, (a ::ₘ s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
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

-- Finset.max'_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_mem.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

