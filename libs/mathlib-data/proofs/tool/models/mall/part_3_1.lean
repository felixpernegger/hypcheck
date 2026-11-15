import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Ordnode.Valid'.balanceR_aux, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balanceR_aux.h7 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑x) r o₂ →
          (r.size = 0 → l.size ≤ 1) →
            (1 ≤ r.size → 1 ≤ l.size → l.size ≤ Ordnode.delta * r.size) →
              2 * r.size ≤ 9 * l.size + 5 ∨ r.size ≤ 3 → Ordnode.Valid' o₁ (l.balanceR x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.balanceR_aux, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balanceR_aux.h8 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x →
          (r.size = 0 → l.size ≤ 1) →
            (1 ≤ r.size → 1 ≤ l.size → l.size ≤ Ordnode.delta * r.size) →
              2 * r.size ≤ 9 * l.size + 5 ∨ r.size ≤ 3 → Ordnode.Valid' o₁ (l.balanceR x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (Ordnode.nil) (0) (0) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide) (by
  decide)) (by
  nofun)

-- Multiset.foldr_induction', hypothesis 3: necessary
/- FAILED: 6:3: `simp` made no progress | 8:3: `simp` made no progress | 6:3: `simp` made no progress | 8:3: `simp` made no progress | 11:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 15:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 11:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 15:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldr_induction'.h3 : ¬∀ {α β : Type} (f : α → β → β) (x : β) (q : α → Prop) (p : β → Prop) (s : Multiset α),
        (∀ (a : α) (b : β), q a → p b → p (f a b)) → p x → (∀ a ∈ s, q a) → LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) ((0 : Multiset Nat) : Multiset ℕ) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))
-/

-- Finset.sort_cons, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_cons.h5.inst : ¬Std.Antisymm fun (x x_1 : Bool) => True := by
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
theorem HypCheckProof.Finset.sort_cons.h5.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool },
      (fun (x x_1 : Bool) => True) Bool.false b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_cons.h5.prem1 : Bool.false ∉ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool } := by
  decide
theorem HypCheckProof.Finset.sort_cons.h5 : ¬∀ {α : Type} {s : Finset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r]
        {a : α}, (∀ b ∈ s, r a b) → a ∉ s → Std.Antisymm r := fun hc_h => HypCheckProof.Finset.sort_cons.h5.inst (@hc_h (Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun (x x_1 : Bool) => True) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (Bool.false) HypCheckProof.Finset.sort_cons.h5.prem0 HypCheckProof.Finset.sort_cons.h5.prem1)

-- Finset.sort_cons, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_cons.h6.inst : ¬Std.Total fun (a b : ℕ) => a < b := by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_cons.h6.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }, (fun (a b : ℕ) => a < b) 0 b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_cons.h6.prem1 : 0 ∉ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ } := by
  decide
theorem HypCheckProof.Finset.sort_cons.h6 : ¬∀ {α : Type} {s : Finset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r]
        {a : α}, (∀ b ∈ s, r a b) → a ∉ s → Std.Total r := fun hc_h => HypCheckProof.Finset.sort_cons.h6.inst (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a b : ℕ) => a < b) (Nat.decLt) _ _ (0) HypCheckProof.Finset.sort_cons.h6.prem0 HypCheckProof.Finset.sort_cons.h6.prem1)

-- Finset.sort_cons, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_cons.h9.inst : Not
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) ∉
        @Finset.mk Nat
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
              (@Eq.refl Bool Bool.true)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sort_cons.h9.prem0 : ∀ (b : Nat),
      @Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
          (@Finset.mk Nat
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
                (@Eq.refl Bool Bool.true))))
          b →
        (fun (a b : Nat) => @LE.le Nat instLENat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sort_cons.h9 : Not
      (∀ {α : Type} {s : Finset α} (r : α → α → Prop) [inst : @DecidableRel α α r] [inst : IsTrans α r]
        [inst : @Std.Antisymm α r] [inst : @Std.Total α r] {a : α},
        (∀ (b : α),
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s b → r a b) →
          a ∉ s) := fun hc_h => HypCheckProof.Finset.sort_cons.h9.inst (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (fun (a b : Nat) => @LE.le Nat instLENat a b) (Nat.decLe) _ _ _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Finset.sort_cons.h9.prem0)

-- Finset.fold_ite', hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_ite'.h3.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_ite'.h3.prem0 : (fun (a x : ℕ) => a) 0 0 = 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.fold_ite'.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α} {g : α → β},
        op b b = b → ∀ (p : α → Prop) [inst : DecidablePred p], Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_ite'.h3.inst (@hc_h (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) HypCheckProof.Finset.fold_ite'.h3.prem0 (fun (n : ℕ) => n = 0) (fun (a : ℕ) => instDecidableEqNat a 0))

-- Ordnode.Valid'.glue_aux, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.glue_aux.h6 : ¬∀ {α : Type} [inst : Preorder α] {l r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ r o₂ →
          Ordnode.All (fun (x : α) => Ordnode.All (fun (y : α) => x < y) r) l →
            Ordnode.BalancedSz l.size r.size → Ordnode.Valid' o₁ (l.glue r) o₂ ∧ (l.glue r).size = l.size + r.size := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.glue_aux, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.glue_aux.h7 : ¬∀ {α : Type} [inst : Preorder α] {l r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ l o₂ →
          Ordnode.All (fun (x : α) => Ordnode.All (fun (y : α) => x < y) r) l →
            Ordnode.BalancedSz l.size r.size → Ordnode.Valid' o₁ (l.glue r) o₂ ∧ (l.glue r).size = l.size + r.size := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide)) (by
  nofun)

-- Finset.fold_insert_idem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_insert_idem.h3.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
theorem HypCheckProof.Finset.fold_insert_idem.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α} {a : α}
        [inst : DecidableEq α] [hi : Std.IdempotentOp op], Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_insert_idem.h3.inst (@hc_h (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (instDecidableEqNat) (@Std.IdempotentOp.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))))

-- Finset.inf_prodMap, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_prodMap.h10 : Not
      (∀ {ι κ α β : Type} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]
        [inst_2 : @OrderTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))]
        [inst_3 : @OrderTop β (@Preorder.toLE β (@PartialOrder.toPreorder β (@SemilatticeInf.toPartialOrder β inst_1)))]
        {s : Finset ι} {t : Finset κ},
        @Finset.Nonempty κ t →
          ∀ (f : ι → α) (g : κ → β),
            @Eq (Prod α β)
              (@Finset.inf (Prod α β) (Prod ι κ) (@Prod.instSemilatticeInf α β inst inst_1)
                (@Prod.instOrderTop α β
                  (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))
                  (@Preorder.toLE β (@PartialOrder.toPreorder β (@SemilatticeInf.toPartialOrder β inst_1))) inst_2 inst_3)
                (@SProd.sprod (Finset ι) (Finset κ) (Finset (Prod ι κ)) (@Finset.instSProd ι κ) s t)
                (@Prod.map ι α κ β f g))
              (@Prod.mk α β (@Finset.inf α ι inst inst_2 s f) (@Finset.inf β κ inst_1 inst_3 t g))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Bool) (Bool) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@CoheytingAlgebra.toOrderTop Bool
      (@Order.Coframe.toCoheytingAlgebra Bool
        (@CompleteDistribLattice.toCoframe Bool
          (@CompleteBooleanAlgebra.toCompleteDistribLattice Bool Bool.completeBooleanAlgebra)))) (@CoheytingAlgebra.toOrderTop Bool
      (@Order.Coframe.toCoheytingAlgebra Bool
        (@CompleteDistribLattice.toCoframe Bool
          (@CompleteBooleanAlgebra.toCompleteDistribLattice Bool Bool.completeBooleanAlgebra)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (by
  decide) (fun n => n % 2 == 0 : Nat → Bool) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Finset.inf_prodMap, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_prodMap.h11 : Not
      (∀ {ι κ α β : Type} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]
        [inst_2 : @OrderTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))]
        [inst_3 : @OrderTop β (@Preorder.toLE β (@PartialOrder.toPreorder β (@SemilatticeInf.toPartialOrder β inst_1)))]
        {s : Finset ι} {t : Finset κ},
        @Finset.Nonempty ι s →
          ∀ (f : ι → α) (g : κ → β),
            @Eq (Prod α β)
              (@Finset.inf (Prod α β) (Prod ι κ) (@Prod.instSemilatticeInf α β inst inst_1)
                (@Prod.instOrderTop α β
                  (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))
                  (@Preorder.toLE β (@PartialOrder.toPreorder β (@SemilatticeInf.toPartialOrder β inst_1))) inst_2 inst_3)
                (@SProd.sprod (Finset ι) (Finset κ) (Finset (Prod ι κ)) (@Finset.instSProd ι κ) s t)
                (@Prod.map ι α κ β f g))
              (@Prod.mk α β (@Finset.inf α ι inst inst_2 s f) (@Finset.inf β κ inst_1 inst_3 t g))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Bool) (Bool) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@CoheytingAlgebra.toOrderTop Bool
      (@Order.Coframe.toCoheytingAlgebra Bool
        (@CompleteDistribLattice.toCoframe Bool
          (@CompleteBooleanAlgebra.toCompleteDistribLattice Bool Bool.completeBooleanAlgebra)))) (@CoheytingAlgebra.toOrderTop Bool
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
  decide) (fun n => n % 2 == 0 : Nat → Bool) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Finsupp.le_weight_of_ne_zero, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.le_weight_of_ne_zero.h9 : ¬∀ {σ M : Type} [inst : AddCommMonoid M] [inst_1 : PartialOrder M] [inst_2 : IsOrderedAddMonoid M] {w : σ → M},
        (∀ (s : σ), 0 ≤ w s) → ∀ {s : σ} {f : σ →₀ ℕ}, w s ≤ (Finsupp.weight w) f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instAddCommMonoid) (Nat.instPartialOrder) _ (fun n => n + 1 : ℕ → ℕ) (by
  simp) (0) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  decide +kernel)

-- Computation.rel_of_liftRel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.rel_of_liftRel.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {ca : Computation α} {cb : Computation β} {a : α} {b : β}, a ∈ ca → b ∈ cb → R a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Computation.pure 0 : Computation ℕ) (Computation.pure 0 : Computation ℕ) (0) (0) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Computation.rel_of_liftRel, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.rel_of_liftRel.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {ca : Computation α} {cb : Computation β},
        Computation.LiftRel R ca cb → ∀ {a : α} {b : β}, b ∈ cb → R a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (Computation.pure 0 : Computation ℕ) (Computation.pure 0 : Computation ℕ) (by
  simp) (1) (0) (by
  simp)) (by
  decide +kernel)

-- Finset.noncommSum_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.noncommSum_congr.h7 : Not
      (∀ {α β : Type} [inst : AddMonoid β] {s₁ s₂ : Finset α} {f g : α → β},
        (∀ (x : α),
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s₂ x →
              @Eq β (f x) (g x)) →
          @Set.Pairwise α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s₁)
              (@Function.onFun α β Prop
                (@AddCommute β (@AddZero.toAdd β (@AddZeroClass.toAddZero β (@AddMonoid.toAddZeroClass β inst)))) f) →
            @Eq (Finset α) s₁ s₂) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat.instAddMonoid) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.exists_equiv_extend_of_card_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_equiv_extend_of_card_eq.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {t : Finset β} {s : Finset α} {f : α → β},
        Finset.image f s ⊆ t → Set.InjOn f ↑s → ∃ (g : α ≃ ↥t), ∀ i ∈ s, ↑(g i) = f i := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Multiset.foldr_induction, hypothesis 2: necessary
/- FAILED: 6:3: `simp` made no progress | 8:3: `simp` made no progress | 6:3: `simp` made no progress | 8:3: `simp` made no progress | 11:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 15:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 11:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 15:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldr_induction.h2 : ¬∀ {α : Type} (f : α → α → α) (x : α) (p : α → Prop) (s : Multiset α),
        (∀ (a b : α), p a → p b → p (f a b)) → p x → (∀ a ∈ s, p a) → LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (fun n => n = 0 : ℕ → Prop) ((0 : Multiset Nat) : Multiset ℕ) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))
-/

-- Multiset.foldr_induction, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldr_induction.h7.inst : Not
      ((fun (b : Bool) => @Eq Bool b Bool.true)
        (@Multiset.foldr Bool Bool (fun (a b : Bool) => a.not.or b)
          (@LeftCommutative.mk Bool Bool (fun (a b : Bool) => a.not.or b)
            (@of_decide_eq_true
              (∀ (a₁ a₂ b : Bool),
                @Eq Bool ((fun (a b : Bool) => a.not.or b) a₁ ((fun (a b : Bool) => a.not.or b) a₂ b))
                  ((fun (a b : Bool) => a.not.or b) a₂ ((fun (a b : Bool) => a.not.or b) a₁ b)))
              (@Bool.instDecidableForallOfDecidablePred
                (fun (a₁ : Bool) =>
                  ∀ (a₂ b : Bool),
                    @Eq Bool ((fun (a b : Bool) => a.not.or b) a₁ ((fun (a b : Bool) => a.not.or b) a₂ b))
                      ((fun (a b : Bool) => a.not.or b) a₂ ((fun (a b : Bool) => a.not.or b) a₁ b)))
                fun (a : Bool) =>
                @Bool.instDecidableForallOfDecidablePred
                  (fun (a₂ : Bool) =>
                    ∀ (b : Bool),
                      @Eq Bool ((fun (a b : Bool) => a.not.or b) a ((fun (a b : Bool) => a.not.or b) a₂ b))
                        ((fun (a b : Bool) => a.not.or b) a₂ ((fun (a b : Bool) => a.not.or b) a b)))
                  fun (a_1 : Bool) =>
                  @Bool.instDecidableForallOfDecidablePred
                    (fun (b : Bool) =>
                      @Eq Bool ((fun (a b : Bool) => a.not.or b) a ((fun (a b : Bool) => a.not.or b) a_1 b))
                        ((fun (a b : Bool) => a.not.or b) a_1 ((fun (a b : Bool) => a.not.or b) a b)))
                    fun (a_2 : Bool) =>
                    instDecidableEqBool ((fun (a b : Bool) => a.not.or b) a ((fun (a b : Bool) => a.not.or b) a_1 a_2))
                      ((fun (a b : Bool) => a.not.or b) a_1 ((fun (a b : Bool) => a.not.or b) a a_2)))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (∀ (a₁ a₂ b : Bool),
                      @Eq Bool ((fun (a b : Bool) => a.not.or b) a₁ ((fun (a b : Bool) => a.not.or b) a₂ b))
                        ((fun (a b : Bool) => a.not.or b) a₂ ((fun (a b : Bool) => a.not.or b) a₁ b)))
                    (@Bool.instDecidableForallOfDecidablePred
                      (fun (a₁ : Bool) =>
                        ∀ (a₂ b : Bool),
                          @Eq Bool ((fun (a b : Bool) => a.not.or b) a₁ ((fun (a b : Bool) => a.not.or b) a₂ b))
                            ((fun (a b : Bool) => a.not.or b) a₂ ((fun (a b : Bool) => a.not.or b) a₁ b)))
                      fun (a : Bool) =>
                      @Bool.instDecidableForallOfDecidablePred
                        (fun (a₂ : Bool) =>
                          ∀ (b : Bool),
                            @Eq Bool ((fun (a b : Bool) => a.not.or b) a ((fun (a b : Bool) => a.not.or b) a₂ b))
                              ((fun (a b : Bool) => a.not.or b) a₂ ((fun (a b : Bool) => a.not.or b) a b)))
                        fun (a_1 : Bool) =>
                        @Bool.instDecidableForallOfDecidablePred
                          (fun (b : Bool) =>
                            @Eq Bool ((fun (a b : Bool) => a.not.or b) a ((fun (a b : Bool) => a.not.or b) a_1 b))
                              ((fun (a b : Bool) => a.not.or b) a_1 ((fun (a b : Bool) => a.not.or b) a b)))
                          fun (a_2 : Bool) =>
                          instDecidableEqBool
                            ((fun (a b : Bool) => a.not.or b) a ((fun (a b : Bool) => a.not.or b) a_1 a_2))
                            ((fun (a b : Bool) => a.not.or b) a_1 ((fun (a b : Bool) => a.not.or b) a a_2))))
                  Bool.true)
                (@Eq.refl Bool Bool.true))))
          Bool.false (@OfNat.ofNat (Multiset Bool) (nat_lit 0) (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldr_induction.h7.prem0 : ∀ (a b : Bool),
      @Eq Bool a Bool.true →
        @Eq Bool b Bool.true → (fun (b : Bool) => @Eq Bool b Bool.true) ((fun (a b : Bool) => a.not.or b) a b) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldr_induction.h7.prem1 : ∀ (a : Bool),
      @Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
          (@OfNat.ofNat (Multiset Bool) (nat_lit 0) (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool))) a →
        (fun (b : Bool) => @Eq Bool b Bool.true) a := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Multiset.foldr_induction.h7 : Not
      (∀ {α : Type} (f : α → α → α) [inst : @LeftCommutative α α f] (x : α) (p : α → Prop) (s : Multiset α),
        (∀ (a b : α), p a → p b → p (f a b)) →
          (∀ (a : α), @Membership.mem α (Multiset α) (@Multiset.instMembership α) s a → p a) →
            p (@Multiset.foldr α α f inst x s)) := fun hc_h => HypCheckProof.Multiset.foldr_induction.h7.inst (@hc_h (Bool) (fun (a b : Bool) => a.not.or b) (@LeftCommutative.mk (Bool) (Bool) (fun (a b : Bool) => a.not.or b) (by (try dsimp only);   decide)) (Bool.false) (fun (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat (Multiset Bool) (nat_lit 0) (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool))) HypCheckProof.Multiset.foldr_induction.h7.prem0 HypCheckProof.Multiset.foldr_induction.h7.prem1)

-- Computation.liftRel_map, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.liftRel_map.h10 : ¬∀ {α β γ δ : Type} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Computation α} {s2 : Computation β} {f1 : α → γ}
        {f2 : β → δ},
        (∀ {a : α} {b : β}, R a b → S (f1 a) (f2 b)) → Computation.LiftRel S (Computation.map f1 s1) (Computation.map f2 s2) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Computation.pure 0 : Computation ℕ) (Computation.pure 0 : Computation ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Finset.apply_inf_eq_inf_comp, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.apply_inf_eq_inf_comp.h11.inst : ¬(fun (x : Bool) => Bool.false)
          ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.inf fun (n : ℕ) => n % 2 == 0) =
        { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.inf
          ((fun (x : Bool) => Bool.false) ∘ fun (n : ℕ) => n % 2 == 0) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.apply_inf_eq_inf_comp.h11.prem0 : ∀ (x y : Bool),
      (fun (x : Bool) => Bool.false) (Min.min x y) =
        Min.min ((fun (x : Bool) => Bool.false) x) ((fun (x : Bool) => Bool.false) y) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.apply_inf_eq_inf_comp.h11 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] [inst_2 : SemilatticeInf γ] [inst_3 : OrderTop γ]
        {s : Finset β} {f : β → α} (g : α → γ), (∀ (x y : α), g (x ⊓ y) = g x ⊓ g y) → g (s.inf f) = s.inf (g ∘ f) := fun hc_h => HypCheckProof.Finset.apply_inf_eq_inf_comp.h11.inst (@hc_h (Bool) (ℕ) (Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n % 2 == 0) (fun (x : Bool) => Bool.false) HypCheckProof.Finset.apply_inf_eq_inf_comp.h11.prem0)

-- Finset.comp_sup_eq_sup_comp_of_is_total, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.comp_sup_eq_sup_comp_of_is_total.h11 : ¬∀ {α β ι : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} [inst_2 : SemilatticeSup β]
        [inst_3 : OrderBot β] (g : α → β), Monotone g → g (s.sup f) = s.sup (g ∘ f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (Bool.linearOrder) (CompleteLattice.toCompletePartialOrder.toOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeSup) (CompleteLattice.toCompletePartialOrder.toOrderBot) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Finset.comp_inf_eq_inf_comp, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.comp_inf_eq_inf_comp.h11.inst : ¬(fun (x : Bool) => Bool.false)
          ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.inf fun (n : ℕ) => n % 2 == 0) =
        { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.inf
          ((fun (x : Bool) => Bool.false) ∘ fun (n : ℕ) => n % 2 == 0) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.comp_inf_eq_inf_comp.h11.prem0 : ∀ (x y : Bool),
      (fun (x : Bool) => Bool.false) (Min.min x y) =
        Min.min ((fun (x : Bool) => Bool.false) x) ((fun (x : Bool) => Bool.false) y) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.comp_inf_eq_inf_comp.h11 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] [inst_2 : SemilatticeInf γ] [inst_3 : OrderTop γ]
        {s : Finset β} {f : β → α} (g : α → γ), (∀ (x y : α), g (x ⊓ y) = g x ⊓ g y) → g (s.inf f) = s.inf (g ∘ f) := fun hc_h => HypCheckProof.Finset.comp_inf_eq_inf_comp.h11.inst (@hc_h (Bool) (ℕ) (Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n % 2 == 0) (fun (x : Bool) => Bool.false) HypCheckProof.Finset.comp_inf_eq_inf_comp.h11.prem0)

-- Finset.inf'_induction, hypothesis 4: necessary
/- FAILED: 5:3: `simp` made no progress

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    Eq.refl true
  has type
    true = true
  but is expected to have type
    decide (Multiset.Nodup 0) = true
  in | 23:3: `simp` made no progress

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    Eq.refl true
  has type
    true = true
  but is expected to have type
    decide (Multiset.Nodup 0) = true
  in | 5:3: `simp` made no progress

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    Eq.refl true
  has type
    true = true
  but is expected to have type
    decide (Multiset.Nodup 0) = true
  in | 9:3: `simp` made no progress

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    Eq.refl true
  has type
    true = true
  but is expected to have type
    decide (Multiset.Nodup 0) = true
  in | 6:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 27:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 6:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 14:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_induction.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) {p : α → Prop},
        (∀ (a₁ : α), p a₁ → ∀ (a₂ : α), p a₂ → p (a₁ ⊓ a₂)) → (∀ b ∈ s, p (f b)) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

-- Set.MapsTo.exists_equiv_extend_of_card_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.exists_equiv_extend_of_card_eq.h4 : ¬∀ {α β : Type} [inst : Fintype α] {t : Finset β} {s : Set α} {f : α → β},
        Set.MapsTo f s ↑t → Set.InjOn f s → ∃ (g : α ≃ ↥t), ∀ i ∈ s, ↑(g i) = f i := fun hc_h => absurd (@hc_h (Fin 2) (ℕ) (Fin.fintype 2) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (∅) (fun (a : Fin 2) => 0) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one.h8 : ¬∀ {α β : Type} {s : Finset α} {f : α → β} {t : Finset β} [inst : DecidableEq β],
        Set.InjOn f ↑s → Set.MapsTo f ↑s ↑t → ∃! x : β, x ∈ t ∧ x ∉ Finset.image f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat) (by
  decide) (by
  decide)) (by
  simp)

-- Ordnode.Bounded.of_gt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.of_gt.h6 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α} {x : α},
        Ordnode.nil.Bounded (↑x) o₂ → Ordnode.All (fun (x_1 : α) => x_1 > x) t → t.Bounded (↑x) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 1 Ordnode.nil) (0) (1) (0) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Ordnode.Bounded.of_gt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.of_gt.h7 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α} {x : α},
        t.Bounded o₁ o₂ → Ordnode.All (fun (x_1 : α) => x_1 > x) t → t.Bounded (↑x) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (1) (1) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Finset.sup'_induction, hypothesis 4: necessary
/- FAILED: 5:3: `simp` made no progress

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    Eq.refl true
  has type
    true = true
  but is expected to have type
    decide (Multiset.Nodup 0) = true
  in | 23:3: `simp` made no progress

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    Eq.refl true
  has type
    true = true
  but is expected to have type
    decide (Multiset.Nodup 0) = true
  in | 5:3: `simp` made no progress

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    Eq.refl true
  has type
    true = true
  but is expected to have type
    decide (Multiset.Nodup 0) = true
  in | 9:3: `simp` made no progress

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    Eq.refl true
  has type
    true = true
  but is expected to have type
    decide (Multiset.Nodup 0) = true
  in | 6:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 27:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 6:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `simp`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 14:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_induction.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {p : α → Prop},
        (∀ (a₁ : α), p a₁ → ∀ (a₂ : α), p a₂ → p (a₁ ⊔ a₂)) → (∀ b ∈ s, p (f b)) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

-- Stream'.Seq.set_all, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.set_all.h8 : ¬∀ {α : Type} {p : α → Prop} {s : Stream'.Seq α}, (∀ x ∈ s, p x) → ∀ {n : ℕ} {x : α}, p x → ∀ (y : α), p y := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (by
  simp) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1)) (by
  decide +kernel)

-- Multiset.noncommProd_induction, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommProd_induction.h6 : ¬∀ {α : Type} [inst : Monoid α] (s : Multiset α) (comm : {x : α | x ∈ s}.Pairwise Commute) (p : α → Prop),
        (∀ (a b : α), p a → p b → p (a * b)) → (∀ x ∈ s, p x) → p (s.noncommProd comm) := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) (Nat.instMonoid) ((0 : Multiset Nat) : Multiset ℕ) hc_k0 (fun n => n = 0 : ℕ → Prop) hc_k1 hc_k2) (by
  simp)

-- Multiset.noncommProd_erase_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommProd_erase_mul.h5 : ¬∀ {α : Type} [inst : Monoid α] [inst_1 : DecidableEq α] (s : Multiset α) {a : α}
        (comm : {x : α | x ∈ s}.Pairwise Commute)
        (comm' :
          optParam (∀ x ∈ {x : α | x ∈ s.erase a}, ∀ x_1 ∈ {x : α | x ∈ s.erase a}, x ≠ x_1 → Commute x x_1)
            fun (x : α) (hx : x ∈ {x : α | x ∈ s.erase a}) (x_1 : α) (hy : x_1 ∈ {x : α | x ∈ s.erase a}) (hxy : x ≠ x_1) =>
            comm (Multiset.mem_of_mem_erase hx) (Multiset.mem_of_mem_erase hy) hxy),
        (s.erase a).noncommProd comm' * a = s.noncommProd comm := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (Nat.instMonoid) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (0) hc_k0 hc_k1) (by
  simp)

-- Finset.inf_le_of_le, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_le_of_le.h8.inst : ¬({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.inf fun (n : ℕ) => n % 2 == 0) ≤
        Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf_le_of_le.h8.prem0 : (fun (n : ℕ) => n % 2 == 0) 1 ≤ Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.inf_le_of_le.h8 : ¬∀ {α β : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {a : α} {b : β},
        f b ≤ a → s.inf f ≤ a := fun hc_h => HypCheckProof.Finset.inf_le_of_le.h8.inst (@hc_h (Bool) (ℕ) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n % 2 == 0) (Bool.false) (1) HypCheckProof.Finset.inf_le_of_le.h8.prem0)

-- Finset.comp_inf'_eq_inf'_comp, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.comp_inf'_eq_inf'_comp.h6 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf γ] {s : Finset β} {f : β → α} (g : α → γ),
        (∀ (x y : α), g (x ⊓ y) = g x ⊓ g y) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  grind)) (by
  decide +kernel)

-- Finset.le_sup_of_le, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.le_sup_of_le.h8.inst : ¬1 ≤ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.sup fun (n : ℕ) => n + 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.le_sup_of_le.h8.prem0 : 1 ≤ (fun (n : ℕ) => n + 1) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.le_sup_of_le.h8 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α} {b : β},
        a ≤ f b → a ≤ s.sup f := fun hc_h => HypCheckProof.Finset.le_sup_of_le.h8.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (1) (0) HypCheckProof.Finset.le_sup_of_le.h8.prem0)

-- Disjoint.forall_ne_finset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.forall_ne_finset.h6 : Not
      (∀ {α : Type} {s t : Finset α} {a b : α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t b → @Ne α a b) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
  decide) (by
  decide)) (by
  decide +kernel)

-- Disjoint.forall_ne_finset, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.forall_ne_finset.h7 : Not
      (∀ {α : Type} {s t : Finset α} {a b : α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s a → @Ne α a b) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.comp_sup'_eq_sup'_comp, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.comp_sup'_eq_sup'_comp.h6 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β} {f : β → α} (g : α → γ),
        (∀ (x y : α), g (x ⊔ y) = g x ⊔ g y) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  grind)) (by
  decide +kernel)

-- Finset.comp_sup'_eq_sup'_comp, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.comp_sup'_eq_sup'_comp.h9 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
        (g : α → γ), g (s.sup' H f) = s.sup' H (g ∘ f) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (Bool) (Bool) (Nat.instLattice.toSemilatticeSup) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeSup) ({ val := {Bool.true, Bool.false}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) hc_k0 (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- Finset.inf_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_congr.h8 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α]
        [inst_1 : @OrderTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))]
        {s₁ s₂ : Finset β} {f g : β → α},
        (∀ (a : β),
            @Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β)) s₂ a →
              @Eq α (f a) (g a)) →
          @Eq α (@Finset.inf α β inst inst_1 s₁ f) (@Finset.inf α β inst inst_1 s₂ g)) := fun hc_h => absurd (@hc_h (Bool) (Nat) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@CoheytingAlgebra.toOrderTop Bool
      (@Order.Coframe.toCoheytingAlgebra Bool
        (@CompleteDistribLattice.toCoframe Bool
          (@CompleteBooleanAlgebra.toCompleteDistribLattice Bool Bool.completeBooleanAlgebra)))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (fun n => n % 2 == 0 : Nat → Bool) (fun n => n % 2 == 0 : Nat → Bool) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.inf_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_congr.h9 : ¬∀ {α β : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {s₁ s₂ : Finset β} {f g : β → α},
        s₁ = s₂ → s₁.inf f = s₂.inf g := fun hc_h => absurd (@hc_h (Bool) (Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) _ ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (not : Bool → Bool) (fun _ => true : Bool → Bool) rfl) (by
  decide +kernel)

-- Finset.inter_nonempty_of_card_lt_card_add_card, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_nonempty_of_card_lt_card_add_card.h5 : Not
      (∀ {α : Type} {s t u : Finset α} [inst : DecidableEq α],
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) u
            s →
          @LT.lt Nat instLTNat (@Finset.card α s)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Finset.card α t) (@Finset.card α u)) →
            @Finset.Nonempty α (@Min.min (Finset α) (@Finset.instMin α inst) t u)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.inter_nonempty_of_card_lt_card_add_card, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_nonempty_of_card_lt_card_add_card.h6 : Not
      (∀ {α : Type} {s t u : Finset α} [inst : DecidableEq α],
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) t
            s →
          @LT.lt Nat instLTNat (@Finset.card α s)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Finset.card α t) (@Finset.card α u)) →
            @Finset.Nonempty α (@Min.min (Finset α) (@Finset.instMin α inst) t u)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.inter_nonempty_of_card_lt_card_add_card, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_nonempty_of_card_lt_card_add_card.h7 : ¬∀ {α : Type} {s t u : Finset α} [inst : DecidableEq α], t ⊆ s → u ⊆ s → (t ∩ u).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Multiset.fold_dedup_idem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_dedup_idem.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] [inst : DecidableEq α] [hi : Std.IdempotentOp op]
        (s : Multiset α) (b : α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (instDecidableEqNat) (@Std.IdempotentOp.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.preimage_compl', hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.preimage_compl'.h8 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst : DecidableEq β] [inst_1 : Fintype α] [inst_2 : Fintype β] {f : α → β}
        (s : Finset β), Set.InjOn f (f ⁻¹' ↑s) → Set.InjOn f (f ⁻¹' ↑sᶜ) := fun hc_h => absurd (@hc_h (Bool) (Bool) (instDecidableEqBool) (instDecidableEqBool) (Bool.fintype) (Bool.fintype) (fun _ => true : Bool → Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (by
  simp)) (by
  simp)

-- Ordnode.Valid'.map_aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.map_aux.h5 : ¬∀ {α : Type} [inst : Preorder α] {β : Type} [inst_1 : Preorder β] {f : α → β} {t : Ordnode α} {a₁ : WithBot α}
        {a₂ : WithTop α},
        Ordnode.Valid' a₁ t a₂ →
          Ordnode.Valid' (Option.map f a₁) (Ordnode.map f t) (Option.map f a₂) ∧ (Ordnode.map f t).size = t.size := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (ℕ) (Nat.instPreorder) (fun _ => 0 : ℕ → ℕ) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Finset.le_sup'_of_le, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.le_sup'_of_le.h7.inst : 0 ∉ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ } := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.le_sup'_of_le.h7.prem0 : 0 ≤ (fun (n : ℕ) => n + 1) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.le_sup'_of_le.h7 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {a : α} {b : β}, a ≤ f b → b ∈ s := fun hc_h => HypCheckProof.Finset.le_sup'_of_le.h7.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (0) (0) HypCheckProof.Finset.le_sup'_of_le.h7.prem0)

-- Finset.le_sup'_of_le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_sup'_of_le.h8 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {a : α} {b : β}
        (hb : @Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β)) s b),
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst))) a
          (@Finset.sup' α β inst s
            (@Exists.intro β
              (fun (x : β) =>
                @Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β)) s x)
              b hb)
            f)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k0) (by
  decide +kernel)

-- Finset.sup'_eq_zero, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_eq_zero.h8 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} [inst_2 : Zero α]
        [inst : IsBotZeroClass α], s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (Nat.instMulZeroClass.toZero) _) (by
  decide +kernel)

-- Finset.inf_mem_infs, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_mem_infs.h7 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s t : Finset α} {a b : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t b →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
            (@HasInfs.infs (Finset α) (@Finset.hasInfs α inst inst_1) s t)
            (@Min.min α (@SemilatticeInf.toMin α inst_1) a b)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Ordnode.Bounded.trans_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.trans_left.h7 : ¬∀ {α : Type} [inst : Preorder α] {t₁ : Ordnode α} {t₂ : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        t₂.Bounded (↑x) o₂ → t₂.Bounded o₁ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.nil) (0) (1) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Bounded.trans_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.trans_left.h8 : ¬∀ {α : Type} [inst : Preorder α] {t₁ t₂ : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        t₁.Bounded o₁ ↑x → t₂.Bounded o₁ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.nil) (1) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Valid'.trans_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.trans_right.h7 : ¬∀ {α : Type} [inst : Preorder α] {t₁ t₂ : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        t₂.Bounded (↑x) o₂ → Ordnode.Valid' o₁ t₁ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.nil) (0) (1) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Valid'.trans_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.trans_right.h8 : ¬∀ {α : Type} [inst : Preorder α] {t₁ : Ordnode α} {t₂ : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ t₁ ↑x → Ordnode.Valid' o₁ t₁ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.nil) (1) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cycle.Subsingleton.congr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Subsingleton.congr.h2 : ¬∀ {α : Type} {s : Cycle α} ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x = y := fun hc_h => absurd (@hc_h (ℕ) ((([0, 1] : List Nat) : Cycle Nat) : Cycle ℕ) (0) (by
  decide) (1) (by
  decide)) (by
  decide +kernel)

-- Cycle.Subsingleton.congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Subsingleton.congr.h4 : ¬∀ {α : Type} {s : Cycle α}, s.Subsingleton → ∀ ⦃x y : α⦄, y ∈ s → x = y := fun hc_h => absurd (@hc_h (ℕ) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) (by
  (repeat' constructor) <;> done) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Cycle.Subsingleton.congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Subsingleton.congr.h6 : ¬∀ {α : Type} {s : Cycle α}, s.Subsingleton → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, x = y := fun hc_h => absurd (@hc_h (ℕ) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) (by
  (repeat' constructor) <;> done) (0) (by
  decide) (1)) (by
  decide +kernel)

-- Finset.sort_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_eq.h5 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
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

-- Multiset.disjSum_lt_disjSum_of_lt_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.disjSum_lt_disjSum_of_lt_of_le.h6 : ¬∀ {α β : Type} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β}, t₁ ≤ t₂ → s₁.disjSum t₁ < s₂.disjSum t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  simp)

-- Finset.inf'_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_mono.h6 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α] (f : β → α) {s₁ s₂ : Finset β},
        @Finset.Nonempty β s₁ →
          @LE.le (Finset β) (@Preorder.toLE (Finset β) (@PartialOrder.toPreorder (Finset β) (@Finset.instPartialOrder β)))
            s₁ s₂) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (fun n => n + 1 : Nat → Nat) (@Finset.mk Nat
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

-- Finset.inf'_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_mono.h7 : ¬∀ {α β : Type} [inst : SemilatticeInf α] (f : β → α) {s₁ s₂ : Finset β}, s₁ ⊆ s₂ → s₁.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (fun n => n + 1 : ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Finset.sup'_le, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup'_le.h4.inst : ¬{ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.Nonempty := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup'_le.h4.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }, (fun (n : ℕ) => n + 1) b ≤ 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sup'_le.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {a : α}, (∀ b ∈ s, f b ≤ a) → s.Nonempty := fun hc_h => HypCheckProof.Finset.sup'_le.h4.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (0) HypCheckProof.Finset.sup'_le.h4.prem0)

-- Finset.sup'_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_le.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (H : @Finset.Nonempty β s) (f : β → α) {a : α},
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))
          (@Finset.sup' α β inst s H f) a) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) hc_k0 (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.sup'_mono_fun, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup'_mono_fun.h4.inst : ¬{ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.Nonempty := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup'_mono_fun.h4.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      (fun (n : ℕ) => n + 1) b ≤ (fun (n : ℕ) => n + 1) b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sup'_mono_fun.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} {f g : β → α}, (∀ b ∈ s, f b ≤ g b) → s.Nonempty := fun hc_h => HypCheckProof.Finset.sup'_mono_fun.h4.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (fun (n : ℕ) => n + 1) HypCheckProof.Finset.sup'_mono_fun.h4.prem0)

-- Finset.sup'_mono_fun, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_mono_fun.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} {hs : @Finset.Nonempty β s} {f g : β → α},
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))
          (@Finset.sup' α β inst s hs f) (@Finset.sup' α β inst s hs g)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) hc_k0 (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat)) (by
  decide +kernel)

-- Finset.sup'_eq_of_forall, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup'_eq_of_forall.h4.inst : ¬{ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.Nonempty := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup'_eq_of_forall.h4.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }, (fun (n : ℕ) => n + 1) b = 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sup'_eq_of_forall.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {a : α}, (∀ b ∈ s, f b = a) → s.Nonempty := fun hc_h => HypCheckProof.Finset.sup'_eq_of_forall.h4.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (0) HypCheckProof.Finset.sup'_eq_of_forall.h4.prem0)

-- Finset.sup'_eq_of_forall, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_eq_of_forall.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (H : @Finset.Nonempty β s) (f : β → α) {a : α},
        @Eq α (@Finset.sup' α β inst s H f) a) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) hc_k0 (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.inf'_mono_fun, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf'_mono_fun.h4.inst : ¬{ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.Nonempty := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf'_mono_fun.h4.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      (fun (n : ℕ) => n + 1) b ≤ (fun (n : ℕ) => n + 1) b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.inf'_mono_fun.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} {f g : β → α}, (∀ b ∈ s, g b ≤ f b) → s.Nonempty := fun hc_h => HypCheckProof.Finset.inf'_mono_fun.h4.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (fun (n : ℕ) => n + 1) HypCheckProof.Finset.inf'_mono_fun.h4.prem0)

-- Finset.inf'_mono_fun, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_mono_fun.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} {hs : @Finset.Nonempty β s} {f g : β → α},
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))
          (@Finset.inf' α β inst s hs g) (@Finset.inf' α β inst s hs f)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) hc_k0 (fun _ => 0 : Nat → Nat) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Finset.max'_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_image.h5 : Not
      (∀ {α β : Type} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β} (s : Finset α)
        (h : @Finset.Nonempty β (@Finset.image α β (fun (a b : β) => @LinearOrder.toDecidableEq β inst_1 a b) f s)),
        @Eq β (@Finset.max' β inst_1 (@Finset.image α β (fun (a b : β) => @LinearOrder.toDecidableEq β inst_1 a b) f s) h)
          (f
            (@Finset.max' α inst s
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

-- Finset.max'_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_image.h7 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β},
        Monotone f → ∀ (s : Finset α), (Finset.image f s).Nonempty := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.linearOrder) (Nat.instLinearOrder) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Computation.mem_bind, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.mem_bind.h7 : ¬∀ {α β : Type} {s : Computation α} {f : α → Computation β} {a : α} {b : β}, a ∈ s → b ∈ s.bind f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Computation.pure 0 : Computation ℕ) (fun (a : ℕ) => Computation.pure 0) (0) (1) (by
  simp)) (by
  simp)

-- Computation.exists_of_liftRel_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.exists_of_liftRel_right.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {ca : Computation α} {cb : Computation β} {b : β}, b ∈ cb → ∃ a ∈ ca, R a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Inhabited.default) (Computation.pure 0 : Computation ℕ) (0) (by
  simp)) (by
  simp)

-- Finset.noncommProd_cons', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.noncommProd_cons'.h6 : Not (∀ {α β : Type} [inst : Monoid β] (s : Finset α) (a : α) (f : α → β), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat.instMonoid) (@Finset.mk Nat
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

-- Finset.noncommProd_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.noncommProd_cons.h6 : Not (∀ {α β : Type} [inst : Monoid β] (s : Finset α) (a : α) (f : α → β), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat.instMonoid) (@Finset.mk Nat
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

-- Multiset.find?_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.find?_congr.h7 : ¬∀ {α : Type} {p₁ p₂ : α → Prop} [inst : DecidablePred p₁] [inst : DecidablePred p₂] {s : Multiset α},
        {x : α | x ∈ s ∧ p₁ x}.Subsingleton → ∀ x ∈ s, p₁ x ↔ p₂ x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableFalse) (({0} : Multiset Nat) : Multiset ℕ) (by
  simp)) (by
  decide +kernel)

-- Ordnode.Valid'.mono_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.mono_right.h4 : ¬∀ {α : Type} [inst : Preorder α] {x y : α} {t : Ordnode α} {o : WithBot α},
        Ordnode.Valid' o t ↑x → Ordnode.Valid' o t ↑y := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (1) (0) (Ordnode.nil) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Valid'.mono_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.mono_right.h7 : ¬∀ {α : Type} [inst : Preorder α] {x y : α}, x ≤ y → ∀ {t : Ordnode α} {o : WithBot α}, Ordnode.Valid' o t ↑y := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (0) (by
  decide) (Ordnode.nil) (0)) (by
  nofun)

-- Finset.restrict₂_comp_restrict₂, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.restrict₂_comp_restrict₂.h5 : Not
      (∀ {ι : Type} {π : ι → Type} {s t u : Finset ι},
        @LE.le (Finset ι) (@Preorder.toLE (Finset ι) (@PartialOrder.toPreorder (Finset ι) (@Finset.instPartialOrder ι))) t
            u →
          @LE.le (Finset ι) (@Preorder.toLE (Finset ι) (@PartialOrder.toPreorder (Finset ι) (@Finset.instPartialOrder ι))) s
            t) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@Finset.mk Nat
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

-- Finset.restrict₂_comp_restrict₂, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.restrict₂_comp_restrict₂.h6 : Not
      (∀ {ι : Type} {π : ι → Type} {s t u : Finset ι},
        @LE.le (Finset ι) (@Preorder.toLE (Finset ι) (@PartialOrder.toPreorder (Finset ι) (@Finset.instPartialOrder ι))) s
            t →
          @LE.le (Finset ι) (@Preorder.toLE (Finset ι) (@PartialOrder.toPreorder (Finset ι) (@Finset.instPartialOrder ι))) t
            u) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.eq_of_mem_insert_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_mem_insert_of_notMem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, b ∉ s → b = a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.notMem_of_max_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_of_max_lt.h5 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a b : α},
        @Eq (WithBot α) (@Finset.max α inst s) (@WithBot.some α b) → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
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

-- Finset.notMem_of_max_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_of_max_lt.h6 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a b : α},
        @LT.lt α
            (@Preorder.toLT α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
            b a →
          a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Computation.le_stable, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.le_stable.h6 : Not
      (∀ {α : Type} (s : Computation α) {a : α} {m n : Nat},
        @LE.le Nat instLENat m n →
          @Eq (Option α)
            (@Subtype.val (Stream' (Option α))
              (fun (f : Stream' (Option α)) =>
                ∀ ⦃n : Nat⦄ ⦃a : α⦄,
                  @Eq (Option α) (f n) (@Option.some α a) →
                    @Eq (Option α)
                      (f
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@Option.some α a))
              s n)
            (@Option.some α a)) := fun hc_h => absurd (@hc_h (Nat) (@Inhabited.default (Computation Nat) (@Computation.instInhabited Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Stream'.Seq.ge_stable, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.ge_stable.h6 : ¬∀ {α : Type} (s : Stream'.Seq α) {aₙ : α} {n m : ℕ}, m ≤ n → ∃ (aₘ : α), s.get? m = Option.some aₘ := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0) (0) (0) (by
  decide)) (by
  nofun)

-- Stream'.Seq.all_get, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.all_get.h6 : ¬∀ {α : Type} {p : α → Prop} {s : Stream'.Seq α}, (∀ x ∈ s, p x) → ∀ {n : ℕ} {x : α}, p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (by
  simp) (0) (1)) (by
  decide +kernel)

-- Finset.filter_powersetCard_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_powersetCard_subset.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] (s t : Finset α) (n : Nat),
        @LE.le Nat instLENat (@Finset.card α s) n →
          @Eq (Finset (Finset α))
            ({x ∈ @Finset.powersetCard α n t |
              @LE.le (Finset α)
                (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s x})
            (@Finset.image (Finset α) (Finset α) (fun (a b : Finset α) => @Finset.decidableEq α inst a b)
              (fun (x : Finset α) => @Max.max (Finset α) (@Finset.instMax α inst) x s)
              (@Finset.powersetCard α (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n (@Finset.card α s))
                (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t s)))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Cycle.Chain.eq_nil_of_irrefl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.eq_nil_of_irrefl.h3 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : Std.Irrefl r], Cycle.Chain r s → s = Cycle.nil := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop) ((([0, 1] : List Nat) : Cycle Nat) : Cycle ℕ) _ (by
  simp)) (by
  decide +kernel)

-- Cycle.Chain.eq_nil_of_irrefl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.eq_nil_of_irrefl.h4 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : IsTrans α r], Cycle.Chain r s → s = Cycle.nil := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) _ (by
  simp)) (by
  decide +kernel)

-- Cycle.Chain.eq_nil_of_irrefl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.eq_nil_of_irrefl.h5 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : IsTrans α r] [inst : Std.Irrefl r], s = Cycle.nil := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) _ _) (by
  decide +kernel)

-- Multiset.mem_filter_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_filter_of_mem.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α} {l : Multiset α}, p a → a ∈ Multiset.filter p l := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) ((0 : Multiset Nat) : Multiset ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.infs_eq_inter, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.infs_eq_inter.h5.inst : Not
      (@Eq (Finset Nat)
        (@HasInfs.infs (Finset Nat) (@Finset.hasInfs Nat instDecidableEqNat (@Lattice.toSemilatticeInf Nat Nat.instLattice))
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
          (@Finset.mk Nat
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
                (@Eq.refl Bool Bool.true)))))
        (@Min.min (Finset Nat) (@Finset.instMin Nat instDecidableEqNat)
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
          (@Finset.mk Nat
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
                (@Eq.refl Bool Bool.true)))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.infs_eq_inter.h5.prem0 : @IsLowerSet Nat
      (@Preorder.toLE Nat
        (@PartialOrder.toPreorder Nat (@SemilatticeInf.toPartialOrder Nat (@Lattice.toSemilatticeInf Nat Nat.instLattice))))
      (@SetLike.coe (Finset Nat) Nat (@Finset.instSetLike Nat)
        (@Finset.mk Nat
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
              (@Eq.refl Bool Bool.true))))) := by
  aesop
theorem HypCheckProof.Finset.infs_eq_inter.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s t : Finset α},
        @IsLowerSet α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst_1)))
            (@SetLike.coe (Finset α) α (@Finset.instSetLike α) t) →
          @Eq (Finset α) (@HasInfs.infs (Finset α) (@Finset.hasInfs α inst inst_1) s t)
            (@Min.min (Finset α) (@Finset.instMin α inst) s t)) := fun hc_h => HypCheckProof.Finset.infs_eq_inter.h5.inst (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) HypCheckProof.Finset.infs_eq_inter.h5.prem0)

-- Finset.infs_eq_inter, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.infs_eq_inter.h6.inst : Not
      (@Eq (Finset Nat)
        (@HasInfs.infs (Finset Nat) (@Finset.hasInfs Nat instDecidableEqNat (@Lattice.toSemilatticeInf Nat Nat.instLattice))
          (@Finset.mk Nat
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
                (@Eq.refl Bool Bool.true))))
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
                (@Eq.refl Bool Bool.true)))))
        (@Min.min (Finset Nat) (@Finset.instMin Nat instDecidableEqNat)
          (@Finset.mk Nat
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
                (@Eq.refl Bool Bool.true))))
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
                (@Eq.refl Bool Bool.true)))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.infs_eq_inter.h6.prem0 : @IsLowerSet Nat
      (@Preorder.toLE Nat
        (@PartialOrder.toPreorder Nat (@SemilatticeInf.toPartialOrder Nat (@Lattice.toSemilatticeInf Nat Nat.instLattice))))
      (@SetLike.coe (Finset Nat) Nat (@Finset.instSetLike Nat)
        (@Finset.mk Nat
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
              (@Eq.refl Bool Bool.true))))) := by
  aesop
theorem HypCheckProof.Finset.infs_eq_inter.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s t : Finset α},
        @IsLowerSet α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst_1)))
            (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) →
          @Eq (Finset α) (@HasInfs.infs (Finset α) (@Finset.hasInfs α inst inst_1) s t)
            (@Min.min (Finset α) (@Finset.instMin α inst) s t)) := fun hc_h => HypCheckProof.Finset.infs_eq_inter.h6.inst (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) HypCheckProof.Finset.infs_eq_inter.h6.prem0)

-- Finset.Nonempty.diffs, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.diffs.h5 : ¬∀ {α : Type} [inst : DecidableEq α] [inst_1 : GeneralizedBooleanAlgebra α] {s t : Finset α},
        t.Nonempty → (s.diffs t).Nonempty := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (BooleanAlgebra.toGeneralizedBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (by
  decide)) (by
  decide +kernel)

-- Finset.eq_of_mem_of_notMem_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_mem_of_notMem_erase.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, b ∉ s.erase a → b = a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.eq_of_mem_of_notMem_erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_mem_of_notMem_erase.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s b → @Eq α b a) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.inter_congr_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_congr_left.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Min.min (Finset α) (@Finset.instMin α inst) s t) u →
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

-- Finset.inter_congr_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_congr_right.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Min.min (Finset α) (@Finset.instMin α inst) s u) t →
          @Eq (Finset α) (@Min.min (Finset α) (@Finset.instMin α inst) s u)
            (@Min.min (Finset α) (@Finset.instMin α inst) t u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.inter_congr_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_congr_right.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Min.min (Finset α) (@Finset.instMin α inst) t u) s →
          @Eq (Finset α) (@Min.min (Finset α) (@Finset.instMin α inst) s u)
            (@Min.min (Finset α) (@Finset.instMin α inst) t u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Finset.union_congr_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_congr_left.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) u
            (@Max.max (Finset α) (@Finset.instMax α inst) s t) →
          @Eq (Finset α) (@Max.max (Finset α) (@Finset.instMax α inst) s t)
            (@Max.max (Finset α) (@Finset.instMax α inst) s u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.union_congr_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_congr_left.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) t
            (@Max.max (Finset α) (@Finset.instMax α inst) s u) →
          @Eq (Finset α) (@Max.max (Finset α) (@Finset.instMax α inst) s t)
            (@Max.max (Finset α) (@Finset.instMax α inst) s u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (by
  decide)) (by
  decide +kernel)

-- Finset.sdiff_subset_sdiff_iff_subset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_subset_sdiff_iff_subset.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t r : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
            r →
          Iff
            (@LE.le (Finset α)
              (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
              (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) r s)
              (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) r t))
            (@LE.le (Finset α)
              (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) t s)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.subset_coe_filter_of_subset_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.subset_coe_filter_of_subset_forall.h5 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (s : Finset α) {t : Set α},
        (∀ x ∈ t, p x) → t ⊆ ↑(Finset.filter p s) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Finset.map_disjUnion', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.map_disjUnion'.h5 : ¬∀ {α β : Type} {f : α ↪ β} (s₁ s₂ : Finset α), Disjoint (Finset.map f s₁) (Finset.map f s₂) := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.insert_right_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_right_inj.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        a ∉ t →
          Iff
            (@Eq (Finset α) (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s)
              (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a t))
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.insert_right_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_right_inj.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        a ∉ s →
          Iff
            (@Eq (Finset α) (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s)
              (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a t))
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.erase_cons_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_cons_of_ne.h5 : Not (∀ {α : Type} [inst : DecidableEq α] {a b : α} {s : Finset α}, @Ne α a b → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Finset.mk Nat
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

-- Finset.erase_cons_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_cons_of_ne.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} {s : Finset α} (ha : a ∉ s),
        (Finset.cons a s ha).erase b = Finset.cons a (s.erase b) fun (h : a ∈ s.erase b) => ha (Finset.erase_subset b s h) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) (0) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) hc_k0) (by
  decide +kernel)

-- Finset.erase_eq_iff_eq_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_eq_iff_eq_insert.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α}, a ∉ t → (s.erase a = t ↔ s = Insert.insert a t) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.filter_cons_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.filter_cons_of_neg.h5.inst : Not
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) ∉
        @Finset.mk Nat
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
              (@Eq.refl Bool Bool.true)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.filter_cons_of_neg.h5.prem0 : Not
      ((fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.filter_cons_of_neg.h5 : Not (∀ {α : Type} (p : α → Prop) [inst : @DecidablePred α p] (a : α) (s : Finset α), Not (p a) → a ∉ s) := fun hc_h => HypCheckProof.Finset.filter_cons_of_neg.h5.inst (@hc_h (Nat) (fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) HypCheckProof.Finset.filter_cons_of_neg.h5.prem0)

-- Finset.filter_cons_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_cons_of_neg.h6 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (a : α) (s : Finset α) (ha : a ∉ s),
        Finset.filter p (Finset.cons a s ha) = Finset.filter p s := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) hc_k0) (by
  decide +kernel)

-- Finset.sdiff_union_erase_cancel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_union_erase_cancel.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t a →
          @Eq (Finset α)
            (@Max.max (Finset α) (@Finset.instMax α inst) (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t)
              (@Finset.erase α inst t a))
            (@Finset.erase α inst s a)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.sdiff_union_erase_cancel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_union_erase_cancel.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) t
            s →
          @Eq (Finset α)
            (@Max.max (Finset α) (@Finset.instMax α inst) (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t)
              (@Finset.erase α inst t a))
            (@Finset.erase α inst s a)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Finset.exists_ne_map_eq_of_card_lt_of_maps_to, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_ne_map_eq_of_card_lt_of_maps_to.h6 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β},
        @LT.lt Nat instLTNat (@Finset.card β t) (@Finset.card α s) →
          ∀ {f : α → β},
            ∃ (x : α),
              And (@Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x)
                (∃ (y : α),
                  And (@Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s y)
                    (And (@Ne α x y) (@Eq β (f x) (f y))))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat
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
  decide) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

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

-- Multiset.fold_cons'_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_cons'_left.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b a : α) (s : Multiset α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) ((0 : Multiset Bool) : Multiset Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_cons'_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_cons'_right.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b a : α) (s : Multiset α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_cons'_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_cons'_right.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b a : α) (s : Multiset α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) ((0 : Multiset Bool) : Multiset Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.inf'_prodMap, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_prodMap.h8 : ¬∀ {ι κ α β : Type} [inst : SemilatticeInf α] [inst : SemilatticeInf β] {s : Finset ι} {t : Finset κ} (f : ι → α)
        (g : κ → β), (s ×ˢ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.inf'_image₂_left, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_image₂_left.h10 : ¬∀ {α β γ δ : Type} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β} [inst_1 : SemilatticeInf δ]
        (g : γ → δ), (Finset.image₂ f s t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (fun a b => a - b : ℕ → ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Nat.instLattice.toSemilatticeInf) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.inf'_image₂_right, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_image₂_right.h10 : ¬∀ {α β γ δ : Type} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β} [inst_1 : SemilatticeInf δ]
        (g : γ → δ), (Finset.image₂ f s t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (fun a b => a - b : ℕ → ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Nat.instLattice.toSemilatticeInf) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.sup'_image₂_right, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_image₂_right.h10 : ¬∀ {α β γ δ : Type} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β} [inst_1 : SemilatticeSup δ]
        (g : γ → δ), (Finset.image₂ f s t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (fun a b => a - b : ℕ → ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Nat.instLattice.toSemilatticeSup) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.mem_cons_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_cons_of_mem.h4 : Not
      (∀ {α : Type} {a b : α} {s : Finset α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s a → b ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Finset.mem_cons_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_cons_of_mem.h5 : ¬∀ {α : Type} {a b : α} {s : Finset α} {hb : b ∉ s}, a ∈ Finset.cons b s hb := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (0) (1) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) hc_k0) (by
  decide +kernel)

-- Finset.disjUnion_inj_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjUnion_inj_right.h4 : Not
      (∀ {α : Type} {s t₁ t₂ : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t₂ →
          @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t₁) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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

-- Finset.disjUnion_inj_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjUnion_inj_right.h5 : Not
      (∀ {α : Type} {s t₁ t₂ : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t₁ →
          @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t₂) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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

-- Disjoint.notMem_of_mem_left_finset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_left_finset.h3 : Not
      (∀ {α : Type} {s t : Finset α} ⦃a : α⦄,
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s a → a ∉ t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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

-- Disjoint.notMem_of_mem_left_finset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_left_finset.h5 : Not
      (∀ {α : Type} {s t : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t → ∀ ⦃a : α⦄, a ∉ t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.sdiff_ssubset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_ssubset.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Finset α}, t ⊆ s → s \ t ⊂ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Finset.equivOfEq_trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.equivOfEq_trans.h4 : Not (∀ {α : Type} {s t u : Finset α}, @Eq (Finset α) t u → @Eq (Finset α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.equivOfEq_trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.equivOfEq_trans.h5 : Not (∀ {α : Type} {s t u : Finset α}, @Eq (Finset α) s t → @Eq (Finset α) t u) := fun hc_h => absurd (@hc_h (Nat) _ (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.image_iterate_stabilises_lt_card, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_iterate_stabilises_lt_card.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {f : α → α} {s : Finset α},
        Set.MapsTo f ↑s ↑s → ∃ n < s.card, ∀ (m : ℕ), n ≤ m → Finset.image f^[m] s = Finset.image f^[n] s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  simp)

-- Cycle.prev_next, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.prev_next.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Cycle α), s.Nodup → ∀ (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (∅) (by
  decide) (0)) (by
  decide +kernel)

-- Cycle.next_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.next_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Cycle α), s.Nodup → ∀ (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (∅) (by
  decide) (0)) (by
  decide +kernel)

-- Cycle.prev_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.prev_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Cycle α), s.Nodup → ∀ (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (∅) (by
  decide) (0)) (by
  decide +kernel)

-- Cycle.prev_reverse_eq_next', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.prev_reverse_eq_next'.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Cycle α), s.reverse.Nodup → ∀ (x : α), x ∈ s.reverse := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (∅) (by
  decide) (0)) (by
  decide +kernel)

-- Finset.exists_superset_card_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_superset_card_eq.h4 : ¬∀ {α : Type} [inst : Fintype α] {n : ℕ} {s : Finset α}, n ≤ Fintype.card α → ∃ (t : Finset α), s ⊆ t ∧ t.card = n := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) (0) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (by
  decide)) (by
  decide +kernel)

-- Finset.exists_superset_card_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_superset_card_eq.h5 : ¬∀ {α : Type} [inst : Fintype α] {n : ℕ} {s : Finset α}, s.card ≤ n → ∃ (t : Finset α), s ⊆ t ∧ t.card = n := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) (3) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (by
  decide)) (by
  decide +kernel)

-- Finset.min'_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_subset.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {s t : Finset α}, s ⊆ t → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
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

-- Finset.isLUB_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isLUB_mem.h5 : ¬∀ {α : Type} [inst : LinearOrder α] {i : α} (s : Finset α), IsLUB (↑s) i → i ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  simp)) (by
  decide +kernel)

-- Finset.le_min', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_min'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (x : α), (∀ y ∈ s, x ≤ y) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.le_min', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_min'.h5 : Not
      (∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (H : @Finset.Nonempty α s) (x : α),
        @LE.le α
          (@Preorder.toLE α
            (@PartialOrder.toPreorder α
              (@SemilatticeSup.toPartialOrder α
                (@Lattice.toSemilatticeSup α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
          x (@Finset.min' α inst s H)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) hc_k0 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Finset.max'_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_le.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (x : α), (∀ y ∈ s, y ≤ x) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.max'_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_le.h5 : Not
      (∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (H : @Finset.Nonempty α s) (x : α),
        @LE.le α
          (@Preorder.toLE α
            (@PartialOrder.toPreorder α
              (@SemilatticeInf.toPartialOrder α
                (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
          (@Finset.max' α inst s H) x) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) hc_k0 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.EquitableOn.le_add_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.EquitableOn.le_add_one.h5 : Not
      (∀ {α : Type} {s : Finset α} {f : α → Nat} {a : α},
        @Set.EquitableOn α Nat instLENat instAddNat Nat.instOne (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) f →
          @LE.le Nat instLENat (f a)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (∑ i ∈ s, f i) (@Finset.card α s))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  simp)) (by
  decide +kernel)

-- Multiset.notMem_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.notMem_mono.h4 : ¬∀ {α : Type} {s t : Multiset α} {a : α}, a ∉ t → a ∉ s := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Multiset.mem_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_of_subset.h4 : ¬∀ {α : Type} {s t : Multiset α} {a : α}, a ∈ s → a ∈ t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Multiset.mem_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_of_subset.h5 : ¬∀ {α : Type} {s t : Multiset α} {a : α}, s ⊆ t → a ∈ t := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0) (by
  simp)) (by
  decide +kernel)

-- Finset.notMem_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_mono.h3 : Not (∀ {α : Type} {s t : Finset α} {a : α}, a ∉ t → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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

-- Finset.notMem_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_mono.h5 : Not
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

-- Finset.mem_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_subset.h4 : Not
      (∀ {α : Type} {s₁ s₂ : Finset α} {a : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s₁ a →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s₂ a) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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

-- Finset.mem_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_subset.h5 : ¬∀ {α : Type} {s₁ s₂ : Finset α} {a : α}, s₁ ⊆ s₂ → a ∈ s₂ := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.ssubset_of_subset_of_ssubset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ssubset_of_subset_of_ssubset.h5 : ¬∀ {α : Type} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s₁ ⊂ s₃ := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Multiset.Nodup.map_on, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.map_on.h4 : ¬∀ {α β : Type} {s : Multiset α} {f : α → β}, s.Nodup → (Multiset.map f s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0, 1} : Multiset Nat) : Multiset ℕ) (fun _ => 0 : ℕ → ℕ) (by
  decide)) (by
  decide +kernel)

-- Multiset.Nodup.map_on, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.Nodup.map_on.h5.inst : Not
      (@Multiset.Nodup Nat
        (@Multiset.map Nat Nat
          (fun (n : Nat) =>
            @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.Nodup.map_on.h5.prem0 : ∀ (x : Nat),
      @Membership.mem Nat (Multiset Nat) (@Multiset.instMembership Nat)
          (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          x →
        ∀ (y : Nat),
          @Membership.mem Nat (Multiset Nat) (@Multiset.instMembership Nat)
              (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat)
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              y →
            @Eq Nat
                ((fun (n : Nat) =>
                    @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  x)
                ((fun (n : Nat) =>
                    @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  y) →
              @Eq Nat x y := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Multiset.Nodup.map_on.h5 : Not
      (∀ {α β : Type} {s : Multiset α} {f : α → β},
        (∀ (x : α),
            @Membership.mem α (Multiset α) (@Multiset.instMembership α) s x →
              ∀ (y : α), @Membership.mem α (Multiset α) (@Multiset.instMembership α) s y → @Eq β (f x) (f y) → @Eq α x y) →
          @Multiset.Nodup β (@Multiset.map α β f s)) := fun hc_h => HypCheckProof.Multiset.Nodup.map_on.h5.inst (@hc_h (Nat) (Nat) (@Insert.insert Nat (Multiset Nat) (@Multiset.instInsert Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (fun (n : Nat) =>
      @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) HypCheckProof.Multiset.Nodup.map_on.h5.prem0)

-- Multiset.Nodup.map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.map.h4 : ¬∀ {α β : Type} {f : α → β} {s : Multiset α}, s.Nodup → (Multiset.map f s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (({0, 1} : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Multiset.Nodup.map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.map.h5 : ¬∀ {α β : Type} {f : α → β} {s : Multiset α}, Function.Injective f → (Multiset.map f s).Nodup := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (({true, true} : Multiset Bool) : Multiset Bool) (by
  decide)) (by
  decide +kernel)

-- Multiset.noncommSum_eq_card_nsmul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommSum_eq_card_nsmul.h5 : ¬∀ {α : Type} [inst : AddMonoid α] (s : Multiset α) (comm : {x : α | x ∈ s}.Pairwise AddCommute) (m : α),
        s.noncommSum comm = s.card • m := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (Nat.instAddMonoid) (({0} : Multiset Nat) : Multiset ℕ) hc_k0 (1)) (by
  (simp <;> decide))

-- Disjoint.notMem_of_mem_right_multiset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_right_multiset.h3 : ¬∀ {α : Type} {s t : Multiset α} {a : α}, a ∈ t → a ∉ s := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Multiset.noncommFold_eq_fold, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommFold_eq_fold.h2 : ¬∀ {α : Type} (op : α → α → α) (s : Multiset α) [inst : Std.Commutative op] (a : α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) ((0 : Multiset Bool) : Multiset Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.noncommFold_eq_fold, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommFold_eq_fold.h4 : ¬∀ {α : Type} (op : α → α → α) [assoc : Std.Associative op] (s : Multiset α) (a : α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Ordnode.Valid'.eraseMax_aux, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.eraseMax_aux.h8 : ¬∀ {α : Type} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ (l.node' x r).eraseMax ↑(Ordnode.findMax' x r) ∧
          (l.node' x r).size = (l.node' x r).eraseMax.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (Ordnode.nil) (0) (Ordnode.nil) (0) (0)) (by
  nofun)

-- Fintype.card_filter_piFinset_const_eq_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_filter_piFinset_const_eq_of_mem.h8 : ¬∀ {ι κ : Type} [inst : DecidableEq ι] [inst_1 : DecidableEq κ] [inst_2 : Fintype ι] (s : Finset κ) (i : ι) {x : κ},
        {f ∈ Fintype.piFinset fun (x : ι) => s | f i = x}.card = s.card ^ (Fintype.card ι - 1) := fun hc_h => absurd (@hc_h (Unit) (ℕ) (instDecidableEqPUnit) (instDecidableEqNat) (PUnit.fintype) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (PUnit.unit) (0)) (by
  decide +kernel)

-- Finset.sup'_comp_eq_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_comp_eq_image.h7 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] [inst : DecidableEq β] {s : Finset γ} {f : γ → β} (g : β → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.sup'_map, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_map.h7 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] {s : Finset γ} {f : γ ↪ β} (g : β → α), (Finset.map f s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Computation.get_eq_of_promises, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.get_eq_of_promises.h4 : ¬∀ {α : Type} (s : Computation α) [h : s.Terminates] {a : α}, s.get = a := fun hc_h => absurd (@hc_h (ℕ) (Computation.pure 0 : Computation ℕ) _ (1)) (by
  decide +kernel)

-- Finset.le_sup, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_sup.h7 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {b : β}, f b ≤ s.sup f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.inf_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_le.h7 : ¬∀ {α β : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β}, s.inf f ≤ f b := fun hc_h => absurd (@hc_h (Bool) (ℕ) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (1)) (by
  decide +kernel)

-- Computation.get_eq_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.get_eq_of_mem.h4 : ¬∀ {α : Type} (s : Computation α) [h : s.Terminates] {a : α}, s.get = a := fun hc_h => absurd (@hc_h (ℕ) (Computation.pure 0 : Computation ℕ) _ (1)) (by
  decide +kernel)

-- Finset.image_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_erase.h5 : Not
      (∀ {α β : Type} [inst : DecidableEq β] [inst_1 : DecidableEq α] {f : α → β} (s : Finset α) (a : α),
        @Eq (Finset β) (@Finset.image α β inst f (@Finset.erase α inst_1 s a))
          (@Finset.erase β inst (@Finset.image α β inst f s) (f a))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (instDecidableEqNat) (fun _ => 0 : Nat → Nat) (@Finset.mk Nat
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

-- Finset.sup'_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_insert.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) [inst : DecidableEq β] {b : β}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (instDecidableEqNat) (0)) (by
  decide +kernel)

-- Finset.sup'_comp_eq_map, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_comp_eq_map.h7 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] {s : Finset γ} {f : γ ↪ β} (g : β → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.inf'_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_insert.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) [inst : DecidableEq β] {b : β}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (instDecidableEqNat) (0)) (by
  decide +kernel)

-- Finset.inf_mono_fun, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_mono_fun.h7 : ¬∀ {α β : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {s : Finset β} {f g : β → α}, s.inf g ≤ s.inf f := fun hc_h => absurd (@hc_h (Bool) (Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (not : Bool → Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Finset.inf'_comp_eq_map, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_comp_eq_map.h7 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] {s : Finset γ} {f : γ ↪ β} (g : β → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.le_inf, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_inf.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α]
        [inst_1 : @OrderTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))]
        {s : Finset β} {f : β → α} {a : α},
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst))) a
          (@Finset.inf α β inst inst_1 s f)) := fun hc_h => absurd (@hc_h (Bool) (Nat) (@Lattice.toSemilatticeInf Bool
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
          (@Eq.refl Bool Bool.true)))) (fun n => n % 2 == 0 : Nat → Bool) (Bool.true)) (by
  decide +kernel)

-- Finset.inf'_map, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_map.h7 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] {s : Finset γ} {f : γ ↪ β} (g : β → α), (Finset.map f s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.sup_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_mono.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α]
        [inst_1 : @OrderBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))]
        {s₁ s₂ : Finset β} {f : β → α},
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))
          (@Finset.sup α β inst inst_1 s₁ f) (@Finset.sup α β inst inst_1 s₂ f)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (Nat.instOrderBot) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Multiset.nodup_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.nodup_of_le.h3 : ¬∀ {α : Type} {s t : Multiset α}, t.Nodup → s.Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Finset.eq_of_subset_of_card_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_subset_of_card_le.h3 : Not (∀ {α : Type} {s t : Finset α}, @LE.le Nat instLENat (@Finset.card α t) (@Finset.card α s) → @Eq (Finset α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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

-- Finset.eq_of_subset_of_card_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_subset_of_card_le.h4 : Not
      (∀ {α : Type} {s t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
            t →
          @Eq (Finset α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.Nonempty.mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.mono.h4 : ¬∀ {α : Type} {s t : Finset α}, s ⊆ t → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Finset.image_subset_sups_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_subset_sups_left.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s t : Finset α} {b : α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Finset.image α α inst (fun (x : α) => @Max.max α (@SemilatticeSup.toMax α inst_1) x b) s)
          (@HasSups.sups (Finset α) (@Finset.hasSups α inst inst_1) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat
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

-- Finset.sups_subset_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sups_subset_left.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s t₁ t₂ : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@HasSups.sups (Finset α) (@Finset.hasSups α inst inst_1) s t₁)
          (@HasSups.sups (Finset α) (@Finset.hasSups α inst inst_1) s t₂)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat
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

-- Finset.le_inf'_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_inf'_iff.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.mem_sup', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_sup'.h6 : ¬∀ {α ι : Type} [inst : DecidableEq α] {s : Finset ι} {f : ι → Finset α} {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ) => { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Computation.of_results_bind, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.of_results_bind.h6 : ¬∀ {α β : Type} {s : Computation α} {f : α → Computation β} {b : β} {k : ℕ},
        ∃ (a : α) (m : ℕ) (n : ℕ), s.Results a m ∧ (f a).Results b n ∧ k = n + m := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Inhabited.default) (fun (a : ℕ) => Inhabited.default) (0) (0)) (by
  nofun)

-- Finset.lt_sup'_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.lt_sup'_iff.h4 : ¬∀ {α ι : Type} [inst : LinearOrder α] {s : Finset ι} {f : ι → α} {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.image_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_congr.h6 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {f g : α → β} {s : Finset α},
        @Eq (Finset β) (@Finset.image α β inst f s) (@Finset.image α β inst g s)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat) (@Finset.mk Nat
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

-- Finset.le_sup'_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_sup'_iff.h4 : ¬∀ {α ι : Type} [inst : LinearOrder α] {s : Finset ι} {f : ι → α} {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.inf_mem_of_nonempty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_mem_of_nonempty.h6 : ¬∀ {α ι : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] {s : Finset ι} {f : ι → α}, s.inf f ∈ f '' ↑s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  simp)

-- Finset.sup_himp_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_himp_right.h4 : ¬∀ {α ι : Type} [inst : BooleanAlgebra α] {s : Finset ι} (f : ι → α) (a : α),
        (s.sup fun (b : ι) => f b ⇨ a) = s.inf f ⇨ a := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.true)) (by
  decide +kernel)

-- Finset.sup_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_of_mem.h6 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {b : β}, ∃ (a : α), s.sup (WithBot.some ∘ f) = ↑a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  simp)

-- Finset.sup'_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_le_iff.h4 : ¬∀ {α β : Type} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.inf'_sup_distrib_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_sup_distrib_right.h4 : ¬∀ {α ι : Type} [inst : DistribLattice α] {s : Finset ι} (f : ι → α) (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDistribLatticeNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Multiset.countP_sub, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.countP_sub.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α} (p : α → Prop) [inst_1 : DecidablePred p],
        Multiset.countP p (s - t) = Multiset.countP p s - Multiset.countP p t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) (({1} : Multiset Nat) : Multiset ℕ) (fun _ => True : ℕ → Prop) (fun (a : ℕ) => instDecidableTrue)) (by
  decide +kernel)

-- Multiset.foldr_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldr_cons.h3 : ¬∀ {α β : Type} (f : α → β → β) (b : β) (a : α) (s : Multiset α), LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.foldr_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldr_add.h3 : ¬∀ {α β : Type} (f : α → β → β) (b : β) (s t : Multiset α), LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.filter_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_congr.h6 : Not
      (∀ {α : Type} {p q : α → Prop} [inst : @DecidablePred α p] [inst_1 : @DecidablePred α q] {s : Finset α},
        @Eq (Finset α) (@Finset.filter α p inst s) (@Finset.filter α q inst_1 s)) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun _ => False : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (a : Nat) => instDecidableFalse) (@Finset.mk Nat
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

-- Multiset.foldl_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldl_add.h3 : ¬∀ {α β : Type} (f : β → α → β) (b : β) (s t : Multiset α), RightCommutative f := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (Bool.false) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.right_comm (Bool.false : Bool) (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.count_filter_of_pos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_filter_of_pos.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {p : α → Prop} [inst_1 : DecidablePred p] {a : α} {s : Multiset α},
        Multiset.count a (Multiset.filter p s) = Multiset.count a s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) (({1} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.count_filter_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_filter_of_neg.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {p : α → Prop} [inst_1 : DecidablePred p] {a : α} {s : Multiset α},
        Multiset.count a (Multiset.filter p s) = 0 := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.filterMap_cons_some, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.filterMap_cons_some.h6 : ¬∀ {α β : Type} (f : α → Option β) (a : α) (s : Multiset α) {b : β},
        Multiset.filterMap f (a ::ₘ s) = b ::ₘ Multiset.filterMap f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => none : ℕ → Option ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Multiset.monotone_filter_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.monotone_filter_right.h6 : ¬∀ {α : Type} (s : Multiset α) ⦃p q : α → Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],
        Multiset.filter p s ≤ Multiset.filter q s := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableFalse)) (by
  decide +kernel)

-- Finset.symInsertEquiv_symm_apply_coe, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.symInsertEquiv_symm_apply_coe.h5 : Not
      (∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α] {n : Nat}
        (m :
          @Sigma
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            fun
              (i :
                Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
            ↥(@Finset.sym α inst s
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    i)))),
        a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Sigma.mk
      (Fin
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (fun
          (i :
            Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
        ↥(@Finset.sym Nat instDecidableEqNat
            (@Finset.mk Nat
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
                  (@Eq.refl Bool Bool.true))))
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i))))
      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
            (@Eq.refl Bool Bool.true))))
      (@Subtype.mk
        (Sym Nat
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Fin.val
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                    (@Eq.refl Bool Bool.true)))))))
        (fun
            (x :
              Sym Nat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true))))))) =>
          @Membership.mem
            (Sym Nat
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                        (@Eq.refl Bool Bool.true)))))))
            (Finset
              (Sym Nat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true))))))))
            (@SetLike.instMembership
              (Finset
                (Sym Nat
                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@Fin.val
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                            (@Eq.refl Bool Bool.true))))))))
              (Sym Nat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true)))))))
              (@Finset.instSetLike
                (Sym Nat
                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@Fin.val
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                            (@Eq.refl Bool Bool.true)))))))))
            (@Finset.sym Nat instDecidableEqNat
              (@Finset.mk Nat
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
                    (@Eq.refl Bool Bool.true))))
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                        (@Eq.refl Bool Bool.true)))))))
            x)
        (@Inhabited.default
          (Sym Nat
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                      (@Eq.refl Bool Bool.true)))))))
          (@Sym.inhabitedSym Nat instInhabitedNat
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                      (@Eq.refl Bool Bool.true))))))))
        (@of_decide_eq_true
          (@Membership.mem
            (Sym Nat
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                        (@Eq.refl Bool Bool.true)))))))
            (Finset
              (Sym Nat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true))))))))
            (@SetLike.instMembership
              (Finset
                (Sym Nat
                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@Fin.val
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                            (@Eq.refl Bool Bool.true))))))))
              (Sym Nat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true)))))))
              (@Finset.instSetLike
                (Sym Nat
                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@Fin.val
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                            (@Eq.refl Bool Bool.true)))))))))
            (@Finset.sym Nat instDecidableEqNat
              (@Finset.mk Nat
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
                    (@Eq.refl Bool Bool.true))))
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                        (@Eq.refl Bool Bool.true)))))))
            (@Inhabited.default
              (Sym Nat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true)))))))
              (@Sym.inhabitedSym Nat instInhabitedNat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true)))))))))
          (@Finset.decidableMem
            (Sym Nat
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                        (@Eq.refl Bool Bool.true)))))))
            (fun
                (a b :
                  Sym Nat
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@Fin.val
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                              (@Eq.refl Bool Bool.true))))))) =>
              @instDecidableEqSym Nat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true))))))
                instDecidableEqNat a b)
            (@Inhabited.default
              (Sym Nat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true)))))))
              (@Sym.inhabitedSym Nat instInhabitedNat
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                          (@Eq.refl Bool Bool.true))))))))
            (@Finset.sym Nat instDecidableEqNat
              (@Finset.mk Nat
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
                    (@Eq.refl Bool Bool.true))))
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                        (@Eq.refl Bool Bool.true))))))))
          (@id
            (@Eq Bool
              (@Decidable.decide
                (@Membership.mem
                  (Sym Nat
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@Fin.val
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                              (@Eq.refl Bool Bool.true)))))))
                  (Finset
                    (Sym Nat
                      (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@Fin.val
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                (@Eq.refl Bool Bool.true))))))))
                  (@SetLike.instMembership
                    (Finset
                      (Sym Nat
                        (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@Fin.val
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                  (@Eq.refl Bool Bool.true))))))))
                    (Sym Nat
                      (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@Fin.val
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                (@Eq.refl Bool Bool.true)))))))
                    (@Finset.instSetLike
                      (Sym Nat
                        (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@Fin.val
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                  (@Eq.refl Bool Bool.true)))))))))
                  (@Finset.sym Nat instDecidableEqNat
                    (@Finset.mk Nat
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
                          (@Eq.refl Bool Bool.true))))
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@Fin.val
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                              (@Eq.refl Bool Bool.true)))))))
                  (@Inhabited.default
                    (Sym Nat
                      (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@Fin.val
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                (@Eq.refl Bool Bool.true)))))))
                    (@Sym.inhabitedSym Nat instInhabitedNat
                      (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@Fin.val
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                (@Eq.refl Bool Bool.true)))))))))
                (@Finset.decidableMem
                  (Sym Nat
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@Fin.val
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                              (@Eq.refl Bool Bool.true)))))))
                  (fun
                      (a b :
                        Sym Nat
                          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@Fin.val
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                    (@Eq.refl Bool Bool.true))))))) =>
                    @instDecidableEqSym Nat
                      (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@Fin.val
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                (@Eq.refl Bool Bool.true))))))
                      instDecidableEqNat a b)
                  (@Inhabited.default
                    (Sym Nat
                      (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@Fin.val
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                (@Eq.refl Bool Bool.true)))))))
                    (@Sym.inhabitedSym Nat instInhabitedNat
                      (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@Fin.val
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                                (@Eq.refl Bool Bool.true))))))))
                  (@Finset.sym Nat instDecidableEqNat
                    (@Finset.mk Nat
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
                          (@Eq.refl Bool Bool.true))))
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@Fin.val
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
                              (@Eq.refl Bool Bool.true)))))))))
              Bool.true)
            (@Eq.refl Bool Bool.true)))))) (by
  decide +kernel)

-- Finsupp.comapDomain_mapDomain, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.comapDomain_mapDomain.h5 : ¬∀ {α β M : Type} [inst : AddCommMonoid M] (f : α → β) (l : α →₀ M), Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instAddCommMonoid) (fun _ => 0 : ℕ → ℕ) (0)) (by
  simp)

-- Finset.sup_const, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_const.h5 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} (c : α), (s.sup fun (x : β) => c) = c := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1)) (by
  decide +kernel)

-- Finset.image₂_right_identity, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image₂_right_identity.h5 : Not
      (∀ {β γ : Type} [inst : DecidableEq γ] {f : γ → β → γ} {b : β} (s : Finset γ),
        @Eq (Finset γ) (@Finset.image₂ γ β γ inst f s (@Singleton.singleton β (Finset β) (@Finset.instSingleton β) b)) s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun a b => a - b : Nat → Nat → Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Finset.mk Nat
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

-- Finset.diffs_subset_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.diffs_subset_right.h6 : ¬∀ {α : Type} [inst : DecidableEq α] [inst_1 : GeneralizedBooleanAlgebra α] {s₁ s₂ t : Finset α},
        s₁.diffs t ⊆ s₂.diffs t := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (BooleanAlgebra.toGeneralizedBooleanAlgebra) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.sups_subset_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sups_subset_right.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s₁ s₂ t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@HasSups.sups (Finset α) (@Finset.hasSups α inst inst_1) s₁ t)
          (@HasSups.sups (Finset α) (@Finset.hasSups α inst inst_1) s₂ t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat
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

-- Finset.disjoint_image, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_image.h6 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {s t : Finset α} {f : α → β},
        Iff
          (@Disjoint (Finset β) (@Finset.instPartialOrder β) (@Finset.instOrderBot β) (@Finset.image α β inst f s)
            (@Finset.image α β inst f t))
          (@Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (fun _ => 0 : Nat → Nat)) (by
  decide +kernel)

-- Multiset.erase_add_right_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.erase_add_right_pos.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {t : Multiset α} {a : α} (s : Multiset α), (s + t).erase a = s + t.erase a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.erase_cons_tail_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.erase_cons_tail_of_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Multiset α} {a b : α}, (b ::ₘ s).erase a = b ::ₘ s.erase a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (0) (0)) (by
  decide +kernel)

-- Multiset.erase_add_left_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.erase_add_left_neg.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {t : Multiset α} {a : α} (s : Multiset α), (s + t).erase a = s.erase a + t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.insert_compl_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_compl_insert.h5 : ¬∀ {α : Type} {s : Finset α} [inst : Fintype α] [inst_1 : DecidableEq α] {a : α},
        Insert.insert a (Insert.insert a s)ᶜ = sᶜ := fun hc_h => absurd (@hc_h (Bool) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (Bool.fintype) (instDecidableEqBool) (Bool.true)) (by
  decide +kernel)

-- Stream'.Seq.get?_set_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.get?_set_of_ne.h5 : ¬∀ {α : Type} (x : α) (s : Stream'.Seq α) {m n : ℕ}, (s.set m x).get? n = s.get? n := fun hc_h => absurd (@hc_h (ℕ) (1) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (0) (0)) (by
  decide +kernel)

-- Finset.image₂_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image₂_right.h5 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} [inst : DecidableEq β],
        @Eq (Finset β) (@Finset.image₂ α β β inst (fun (x : α) (y : β) => y) s t) t) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Stream'.Seq.drop_set_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.drop_set_of_lt.h5 : ¬∀ {α : Type} (x : α) (s : Stream'.Seq α) {m n : ℕ}, (s.set m x).drop n = s.drop n := fun hc_h => absurd (@hc_h (ℕ) (1) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (0) (0)) (by
  simp)

-- Multiset.map_le_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_le_map.h5 : ¬∀ {α β : Type} {f : α → β} {s t : Multiset α}, Multiset.map f s ≤ Multiset.map f t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.mem_map_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_map_of_mem.h5 : ¬∀ {α β : Type} (f : α → β) {a : α} {s : Multiset α}, f a ∈ Multiset.map f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.choose_eq_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.choose_eq_iff.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Multiset α) {a : α}, ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  simp)

-- Finset.powersetCard_succ_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.powersetCard_succ_insert.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {x : α} {s : Finset α} (n : Nat),
        @Eq (Finset (Finset α))
          (@Finset.powersetCard α n.succ (@Insert.insert α (Finset α) (@Finset.instInsert α inst) x s))
          (@Max.max (Finset (Finset α)) (@Finset.instMax (Finset α) fun (a b : Finset α) => @Finset.decidableEq α inst a b)
            (@Finset.powersetCard α n.succ s)
            (@Finset.image (Finset α) (Finset α) (fun (a b : Finset α) => @Finset.decidableEq α inst a b)
              (@Insert.insert α (Finset α) (@Finset.instInsert α inst) x) (@Finset.powersetCard α n s)))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Multiset.mem_of_mem_filter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_of_mem_filter.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α} {s : Multiset α}, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.map_filterMap_of_inv, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_filterMap_of_inv.h4 : ¬∀ {α β : Type} (f : α → Option β) (g : β → α) (s : Multiset α), Multiset.map g (Multiset.filterMap f s) = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => none : ℕ → Option ℕ) (fun n => n + 1 : ℕ → ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Nat.multinomial_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multinomial_insert.h4 : Not
      (∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α] (f : α → Nat),
        @Eq Nat (@Nat.multinomial α (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s) f)
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
            ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (f a) (∑ i ∈ s, f i)).choose (f a))
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instDecidableEqNat) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Multiset.Nodup.mem_erase_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.mem_erase_iff.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} {l : Multiset α}, a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.union_le_union_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.union_le_union_left.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α} (u : Multiset α), u ∪ s ≤ u ∪ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.cons_inter_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.cons_inter_of_neg.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {t : Multiset α} {a : α} (s : Multiset α), (a ::ₘ s) ∩ t = s ∩ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.cons_inter_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.cons_inter_of_pos.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {t : Multiset α} {a : α} (s : Multiset α), (a ::ₘ s) ∩ t = a ::ₘ s ∩ t.erase a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.union_le_union_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.union_le_union_right.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α} (u : Multiset α), s ∪ u ≤ t ∪ u := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.erase_insert_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_insert_of_ne.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} {s : Finset α}, (Insert.insert a s).erase b = Insert.insert a (s.erase b) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Multiset.ndinter_cons_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.ndinter_cons_of_notMem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} (s : Multiset α) {t : Multiset α}, (a ::ₘ s).ndinter t = s.ndinter t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.mem_ndinsert_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_ndinsert_of_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} {s : Multiset α}, a ∈ Multiset.ndinsert b s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (1) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.cons_ndinter_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.cons_ndinter_of_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} (s : Multiset α) {t : Multiset α}, (a ::ₘ s).ndinter t = a ::ₘ s.ndinter t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
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

-- Finset.insert_subset_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_subset_insert.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] (a : α) {s t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s)
          (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Multiset.noncommFoldr_eq_foldr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommFoldr_eq_foldr.h4 : ¬∀ {α β : Type} (f : α → β → β) (s : Multiset α) (b : β), LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.mem_insert_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_insert_of_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, a ∈ Insert.insert b s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (1)) (by
  decide +kernel)

-- Finset.erase_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_inj.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {x y : α} (s : Finset α), s.erase x = s.erase y ↔ x = y := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (1) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.erase_subset_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_subset_erase.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] (a : α) {s t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Finset.erase α inst s a) (@Finset.erase α inst t a)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Finset.inter_subset_inter_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_subset_inter_right.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Min.min (Finset α) (@Finset.instMin α inst) s u) (@Min.min (Finset α) (@Finset.instMin α inst) t u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Finset.inter_insert_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_insert_of_notMem.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s₁ s₂ : Finset α} {a : α},
        @Eq (Finset α)
          (@Min.min (Finset α) (@Finset.instMin α inst) s₁ (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s₂))
          (@Min.min (Finset α) (@Finset.instMin α inst) s₁ s₂)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Finset.sdiff_insert_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_insert_of_notMem.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {x : α} (t : Finset α),
        @Eq (Finset α)
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s
            (@Insert.insert α (Finset α) (@Finset.instInsert α inst) x t))
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.notMem_sdiff_of_notMem_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_sdiff_of_notMem_left.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        a ∉ @SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Finset.mem_map_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_map_mk.h5 : ¬∀ {α β : Type} (f : α → β) {a : α} {s : Finset α}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finsupp.mem_support_multiset_sum, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mem_support_multiset_sum.h5 : ¬∀ {α M : Type} [inst : AddCommMonoid M] {s : Multiset (α →₀ M)} (a : α), ∃ f ∈ s, a ∈ f.support := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instAddCommMonoid) (0) (0)) (by
  nofun)

-- Finset.Nonempty.piFinset_const, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.piFinset_const.h5 : ¬∀ {β ι : Type} [inst : Fintype ι] [inst_1 : DecidableEq ι] {s : Finset β}, (Fintype.piFinset fun (x : ι) => s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Bool.fintype) (instDecidableEqBool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finsupp.mk_mem_graph, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mk_mem_graph.h5 : ¬∀ {α M : Type} [inst : Zero M] (f : α →₀ M) {a : α}, (a, f a) ∈ f.graph := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ) (0)) (by
  decide +kernel)

-- Multiset.le_sup, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.le_sup.h5 : ¬∀ {α : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Multiset α} {a : α}, a ≤ s.sup := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ((0 : Multiset Nat) : Multiset ℕ) (1)) (by
  decide +kernel)

-- Multiset.inf_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.inf_mono.h5 : ¬∀ {α : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {s₁ s₂ : Multiset α}, s₂.inf ≤ s₁.inf := fun hc_h => absurd (@hc_h (Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) (({true, false} : Multiset Bool) : Multiset Bool) ((0 : Multiset Bool) : Multiset Bool)) (by
  decide +kernel)

-- Finset.nontrivial_of_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.nontrivial_of_image.h5 : ¬∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s : Finset α}, s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finsupp.optionElim_ne_zero_of_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.optionElim_ne_zero_of_left.h5 : ¬∀ {α M : Type} [inst : Zero M] (y : M) (f : α →₀ M), Finsupp.optionElim y f ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  simp)

-- Finset.injOn_of_card_image_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.injOn_of_card_image_eq.h5 : Not
      (∀ {α β : Type} {s : Finset α} {f : α → β} [inst : DecidableEq β],
        @Set.InjOn α β f (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (fun _ => 0 : Nat → Nat) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.not_injOn_of_card_image_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.not_injOn_of_card_image_lt.h5 : ¬∀ {α β : Type} {s : Finset α} [inst : DecidableEq β] {f : α → β}, ¬Set.InjOn f ↑s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.exists_min_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_min_image.h5 : ¬∀ {α β : Type} [inst : LinearOrder α] (s : Finset β) (f : β → α), ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.exists_max_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_max_image.h5 : ¬∀ {α β : Type} [inst : LinearOrder α] (s : Finset β) (f : β → α), ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.sym_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sym_mono.h4 : Not
      (∀ {α : Type} {s t : Finset α} [inst : DecidableEq α] (n : Nat),
        @LE.le (Finset (Sym α n))
          (@Preorder.toLE (Finset (Sym α n))
            (@PartialOrder.toPreorder (Finset (Sym α n)) (@Finset.instPartialOrder (Sym α n))))
          (@Finset.sym α inst s n) (@Finset.sym α inst t n)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Finset.filterMap_val, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filterMap_val.h4 : ¬∀ {α β : Type} (f : α → Option β) (s' : Finset α) (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a' := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) => Option.some 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.disjUnion_eq_union, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjUnion_eq_union.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] (s t : Finset α),
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
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.erase_ssubset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_ssubset.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Finset α}, s.erase a ⊂ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.erase_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_cons.h4 : Not (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Finset.erase_union_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_union_eq.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (a : α) (s : Finset α), s.erase a ∪ {a} = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.exists_of_one_lt_card_pi, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_of_one_lt_card_pi.h4 : ¬∀ {ι : Type} {α : ι → Type} [inst : (i : ι) → DecidableEq (α i)] {s : Finset ((i : ι) → α i)},
        ∃ (i : ι), 1 < (Finset.image (fun (x : (i : ι) → α i) => x i) s).card ∧ ∀ (ai : α i), {x ∈ s | x i = ai} ⊂ s := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (fun (i : ℕ) => instDecidableEqNat) (∅)) (by
  simp)

-- Finset.powersetCard_sup, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.powersetCard_sup.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] (u : Finset α) (n : Nat),
        @Eq (Finset α)
          (@Finset.sup (Finset α) (Finset α) (@Lattice.toSemilatticeSup (Finset α) (@Finset.instLattice α inst))
            (@Finset.instOrderBot α) (@Finset.powersetCard α n.succ u) (@id (Finset α)))
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Finset.powersetCard_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.powersetCard_mono.h4 : Not
      (∀ {α : Type} {n : Nat} {s t : Finset α},
        @LE.le (Finset (Finset α))
          (@Preorder.toLE (Finset (Finset α))
            (@PartialOrder.toPreorder (Finset (Finset α)) (@Finset.instPartialOrder (Finset α))))
          (@Finset.powersetCard α n s) (@Finset.powersetCard α n t)) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Finset.mk Nat
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

-- Finset.eq_empty_of_sym_eq_empty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_empty_of_sym_eq_empty.h4 : Not
      (∀ {α : Type} {s : Finset α} [inst : DecidableEq α] {n : Nat},
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
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.isDiag_mk_of_mem_diag, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isDiag_mk_of_mem_diag.h4 : ¬∀ {α : Type} {s : Finset α} {a b : α}, s(a, b).IsDiag := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (1)) (by
  decide +kernel)

-- Nat.Coprime.prod_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.prod_right.h4 : Not (∀ {ι : Type} {x : Nat} {t : Finset ι} {s : ι → Nat}, x.Coprime (∏ i ∈ t, s i)) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (fun _ => 0 : Nat → Nat)) (by
  decide +kernel)

-- Computation.Results.terminates, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.Results.terminates.h4 : ¬∀ {α : Type} {s : Computation α} {a : α} {n : ℕ}, s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0) (0)) (by
  nofun)

-- Computation.Results.mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.Results.mem.h4 : ¬∀ {α : Type} {s : Computation α} {a : α} {n : ℕ}, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0) (0)) (by
  nofun)

-- Finset.restrict₂_comp_restrict, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.restrict₂_comp_restrict.h4 : Not
      (∀ {ι : Type} {π : ι → Type} {s t : Finset ι},
        @LE.le (Finset ι) (@Preorder.toLE (Finset ι) (@PartialOrder.toPreorder (Finset ι) (@Finset.instPartialOrder ι))) s
          t) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@Finset.mk Nat
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

-- Stream'.Seq.get?_set_of_not_terminatedAt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.get?_set_of_not_terminatedAt.h4 : ¬∀ {α : Type} (x : α) {s : Stream'.Seq α} {n : ℕ}, (s.set n x).get? n = Option.some x := fun hc_h => absurd (@hc_h (ℕ) (0) (Inhabited.default) (0)) (by
  decide +kernel)

-- Stream'.Seq.mem_append_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.mem_append_left.h4 : ¬∀ {α : Type} {s₁ s₂ : Stream'.Seq α} {a : α}, a ∈ s₁.append s₂ := fun hc_h => absurd (@hc_h (ℕ) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (0)) (by
  simp)

-- Multiset.le_of_add_le_add_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.le_of_add_le_add_left.h4 : ¬∀ {α : Type} {s : Multiset α} {t u : Multiset α}, t ≤ u := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.erase_covBy, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_covBy.h4 : ¬∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α], s.erase a ⋖ s := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (instDecidableEqNat)) (by
  simp)

-- Finset.covBy_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.covBy_insert.h4 : Not
      (∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α],
        @CovBy (Finset α) (@Preorder.toLT (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
          (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instDecidableEqNat)) (by
  simp)

-- Multiset.nodup_map_iff_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.nodup_map_iff_of_injective.h4 : ¬∀ {α β : Type} {s : Multiset α} {f : α → β}, (Multiset.map f s).Nodup ↔ s.Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0, 1} : Multiset Nat) : Multiset ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  decide +kernel)

-- Multiset.choose_property, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.choose_property.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Multiset α), ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Multiset.choose_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.choose_spec.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Multiset α), ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Multiset.choose_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.choose_mem.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Multiset α), ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Finset.compl_mem_compls, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.compl_mem_compls.h4 : ¬∀ {α : Type} [inst : BooleanAlgebra α] {s : Finset α} {a : α}, aᶜ ∈ s.compls := fun hc_h => absurd (@hc_h (Bool) (Bool.instBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (Bool.false)) (by
  decide +kernel)

-- Multiset.Disjoint.ndinter_eq_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Disjoint.ndinter_eq_zero.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s.ndinter t = 0 := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.length_ndinsert_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.length_ndinsert_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, (Multiset.ndinsert a s).card = s.card := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Subset.ndinter_eq_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Subset.ndinter_eq_left.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s.ndinter t = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.ndunion, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.ndunion.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Multiset α) {t : Multiset α}, (s.ndunion t).Nodup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.ndinsert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.ndinsert.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Multiset α} (a : α), (Multiset.ndinsert a s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0, 0} : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Multiset.ndinter_le_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.ndinter_le_right.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Multiset α} (t : Multiset α), s.ndinter t ≤ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0, 0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Subset.ndunion_eq_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Subset.ndunion_eq_right.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s.ndunion t = t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.cons_eq_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_eq_insert.h4 : Not (∀ {α : Type} [inst : DecidableEq α] (a : α) (s : Finset α), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Finset.mem_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_cons.h4 : Not (∀ {α : Type} {s : Finset α} {a : α} {b : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.exists_mem_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_mem_cons.h3 : Not (∀ {α : Type} {s : Finset α} {a : α} (p : α → Prop), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun n => n = 0 : Nat → Prop)) (by
  decide +kernel)

-- Finset.pairwise_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.pairwise_cons.h3 : Not (∀ {α : Type} {s : Finset α} {a : α} (r : α → α → Prop), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun a b => a < b : Nat → Nat → Prop)) (by
  decide +kernel)

-- Finset.erase_eq_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_eq_of_notMem.h4 : Not (∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Finset α}, @Eq (Finset α) (@Finset.erase α inst s a) s) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Finset.Nonempty.inr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.inr.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Finset α}, (s ∪ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.inter_singleton_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inter_singleton_of_notMem.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Finset α},
        @Eq (Finset α)
          (@Min.min (Finset α) (@Finset.instMin α inst) s (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a))
          (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Finset.singleton_inter_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.singleton_inter_of_notMem.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Finset α},
        @Eq (Finset α)
          (@Min.min (Finset α) (@Finset.instMin α inst) (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a) s)
          (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Ordnode.valid'_nil, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.valid'_nil.h4 : ¬∀ {α : Type} [inst : Preorder α] {o₁ : WithBot α} {o₂ : WithTop α}, Ordnode.Valid' o₁ Ordnode.nil o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (0)) (by
  nofun)

-- Finset.sdiff_eq_self_of_disjoint, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_eq_self_of_disjoint.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Eq (Finset α) (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t) s) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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

-- Finset.exists_next_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_next_right.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {x : α} {s : Finset α}, ∃ y ∈ s, x < y ∧ ∀ z ∈ s, x < z → y ≤ z := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.le_min'_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_min'_iff.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {x : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.min_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min_of_mem.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a : α}, ∃ (b : α), s.min = ↑b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  simp)

-- Finset.lt_min'_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.lt_min'_iff.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {x : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.mem_of_min, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_min.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a : α}, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.min_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min_mono.h4 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s t : Finset α},
        @LE.le (WithTop α)
          (@Preorder.toLE (WithTop α)
            (@WithTop.instPreorder α
              (@PartialOrder.toPreorder α
                (@SemilatticeSup.toPartialOrder α
                  (@Lattice.toSemilatticeSup α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))))
          (@Finset.min α inst t) (@Finset.min α inst s)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
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

-- Finset.max'_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_le_iff.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {x : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.notMem_of_max_lt_coe, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_of_max_lt_coe.h4 : Not (∀ {α : Type} [inst : LinearOrder α] {a : α} {s : Finset α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Finset.le_min, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_min.h4 : Not
      (∀ {α : Type} [inst : LinearOrder α] {M : WithTop α} {s : Finset α},
        @LE.le (WithTop α)
          (@Preorder.toLE (WithTop α)
            (@WithTop.instPreorder α
              (@PartialOrder.toPreorder α
                (@SemilatticeSup.toPartialOrder α
                  (@Lattice.toSemilatticeSup α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))))
          M (@Finset.min α inst s)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@OfNat.ofNat (WithTop Nat) (nat_lit 1) (@One.toOfNat1 (WithTop Nat) (@WithTop.one Nat Nat.instOne))) (@Finset.mk Nat
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

-- Finset.map_orderEmbOfFin_univ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.map_orderEmbOfFin_univ.h4 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {k : ℕ}, s.card = k := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1)) (by
  decide +kernel)

-- Finset.eq_univ_of_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_univ_of_card.h3 : ¬∀ {α : Type} [inst : Fintype α] (s : Finset α), s = Finset.univ := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Multiset.subset_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.subset_of_le.h3 : ¬∀ {α : Type} {s t : Multiset α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Finset.equivOfEq_symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.equivOfEq_symm.h3 : Not (∀ {α : Type} {s t : Finset α}, @Eq (Finset α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.card_lt_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_lt_card.h3 : ¬∀ {α : Type} {s t : Finset α}, s.card < t.card := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.subset_iff_eq_of_card_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.subset_iff_eq_of_card_le.h3 : Not
      (∀ {α : Type} {s t : Finset α},
        Iff
          (@LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            s t)
          (@Eq (Finset α) s t)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.ssubset_iff_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ssubset_iff_of_subset.h3 : Not
      (∀ {α : Type} {s₁ s₂ : Finset α},
        Iff
          (@LT.lt (Finset α) (@Preorder.toLT (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            s₁ s₂)
          (∃ (x : α),
            And (@Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s₂ x)
              (x ∉ s₁))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.subset_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.subset_of_le.h3 : Not
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

-- Finset.Nonempty.compls, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.compls.h3 : ¬∀ {α : Type} [inst : BooleanAlgebra α] {s : Finset α}, s.compls.Nonempty := fun hc_h => absurd (@hc_h (Bool) (Bool.instBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Set.powersetCard.val_ofCard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.powersetCard.val_ofCard.h3 : ¬∀ {α : Type} {n : ℕ} {s : Finset α}, s.card = n := fun hc_h => absurd (@hc_h (ℕ) (1) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Equiv.Finset.congr_symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.congr_symm.h3 : Not (∀ {α : Type} {s t : Finset α}, @Eq (Finset α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Multiset.Nodup.powersetCard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.powersetCard.h3 : ¬∀ {α : Type} {n : ℕ} {s : Multiset α}, (Multiset.powersetCard n s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (1) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.min'_eq_sorted_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_eq_sorted_zero.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Multiset.powersetCard_card_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.powersetCard_card_add.h3 : ¬∀ {α : Type} (s : Multiset α) {i : ℕ}, Multiset.powersetCard (s.card + i) s = 0 := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Computation.thinkN_terminates, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.thinkN_terminates.h2 : ¬∀ {α : Type} (s : Computation α) (n : ℕ), (s.thinkN n).Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- Computation.exists_results_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.exists_results_of_mem.h3 : ¬∀ {α : Type} {s : Computation α} {a : α}, ∃ (n : ℕ), s.Results a n := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- Set.Infinite.exists_notMem_finset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.exists_notMem_finset.h2 : ¬∀ {α : Type} {s : Set α} (t : Finset α), ∃ a ∈ s, a ∉ t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Stream'.Seq.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.ext.h3 : ¬∀ {α : Type} {s t : Stream'.Seq α}, s = t := fun hc_h => absurd (@hc_h (ℕ) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ)) (by
  simp)

-- Multiset.toFinset_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.toFinset_eq.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Multiset α}, s.Nodup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.eq_empty_of_ssubset_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_empty_of_ssubset_singleton.h3 : Not
      (∀ {α : Type} {s : Finset α} {x : α},
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Finset.mk_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mk_cons.h3 : ¬∀ {α : Type} {a : α} {s : Multiset α}, (a ::ₘ s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.mem_cons_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_cons_self.h3 : Not (∀ {α : Type} (a : α) (s : Finset α), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Finset.Nonempty.subset_singleton_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.subset_singleton_iff.h3 : ¬∀ {α : Type} {s : Finset α} {a : α}, s ⊆ {a} ↔ s = {a} := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.Nontrivial.ne_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nontrivial.ne_singleton.h3 : Not
      (∀ {α : Type} {s : Finset α} {a : α},
        @Ne (Finset α) s (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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

-- Finset.Nontrivial.exists_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nontrivial.exists_ne.h2 : ¬∀ {α : Type} {s : Finset α} (a : α), ∃ b ∈ s, b ≠ a := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.isGLB_inf', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isGLB_inf'.h3 : ¬∀ {α : Type} [inst : SemilatticeInf α] {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.isLeast_min', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isLeast_min'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.coe_max', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.coe_max'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Sym.attach_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.attach_mk.h3 : ¬∀ {α : Type} {n : ℕ} {m : Multiset α}, m.card = n := fun hc_h => absurd (@hc_h (ℕ) (1) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.min'_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_mem.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.toDual_min', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.toDual_min'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Multiset.sym2_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sym2_mono.h3 : ¬∀ {α : Type} {m m' : Multiset α}, m.sym2 ≤ m'.sym2 := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.ofDual_max', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ofDual_max'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset αᵒᵈ}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕᵒᵈ })) (by
  decide +kernel)

-- Finset.sym2_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sym2_cons.h3 : Not (∀ {α : Type} (a : α) (s : Finset α), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Finset.disjoint_of_subset_iff_left_eq_empty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_of_subset_iff_left_eq_empty.h3 : Not
      (∀ {α : Type} {s t : Finset α},
        Iff (@Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t)
          (@Eq (Finset α) s (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α)))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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

-- Multiset.Nodup.powerset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.powerset.h2 : ¬∀ {α : Type} {s : Multiset α}, s.powerset.Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.ofPowerset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.ofPowerset.h2 : ¬∀ {α : Type} {s : Multiset α}, s.Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.Nontrivial.exists_cons_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nontrivial.exists_cons_eq.h2 : ¬∀ {α : Type} {s : Finset α},
        ∃ (t : Finset α) (a : α) (ha : a ∉ t) (b : α) (hb : b ∉ t) (hab : ¬a = b),
          Finset.cons a (Finset.cons b t hb) ((Iff.not Finset.mem_cons).mpr (not_or_intro hab ha)) = s := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.Nonempty.to_set, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.to_set.h2 : Not (∀ {α : Type} {s : Finset α}, @Set.Nonempty α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Computation.get_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.get_mem.h2 : ¬∀ {α : Type} (s : Computation α), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default)) (by
  nofun)

-- Computation.of_think_terminates, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.of_think_terminates.h2 : ¬∀ {α : Type} {s : Computation α}, s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default)) (by
  nofun)

-- Finset.Nontrivial.one_lt_card, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nontrivial.one_lt_card.h2 : ¬∀ {α : Type} {s : Finset α}, 1 < s.card := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.exists_not_mem_of_card_lt_enatCard, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_not_mem_of_card_lt_enatCard.h2 : ¬∀ {α : Type} {s : Finset α}, ∃ (a : α), a ∉ s := fun hc_h => absurd (@hc_h (Bool) ({ val := {Bool.true, Bool.false}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.sum_powerset_neg_one_pow_card_of_nonempty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sum_powerset_neg_one_pow_card_of_nonempty.h2 : ¬∀ {α : Type} {x : Finset α}, ∑ m ∈ x.powerset, (-1) ^ m.card = 0 := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

