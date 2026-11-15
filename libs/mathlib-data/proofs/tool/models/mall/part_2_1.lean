import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Multiset.map_sort, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.map_sort.h8.inst : Not (@Std.Total Nat fun (a b : Nat) => @LT.lt Nat instLTNat a b) := by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.map_sort.h8.prem0 : ∀ (a : Nat),
      @Membership.mem Nat (Multiset Nat) (@Multiset.instMembership Nat)
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))) a →
        ∀ (b : Nat),
          @Membership.mem Nat (Multiset Nat) (@Multiset.instMembership Nat)
              (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))) b →
            Iff ((fun (a b : Nat) => @LT.lt Nat instLTNat a b) a b)
              ((fun (a b : Nat) => @LE.le Nat instLENat a b)
                ((fun (n : Nat) =>
                    @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  a)
                ((fun (n : Nat) =>
                    @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  b)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Multiset.map_sort.h8 : Not
      (∀ {α β : Type} (f : α → β) (s : Multiset α) (r : α → α → Prop) [inst : @DecidableRel α α r] [inst : IsTrans α r]
        [inst : @Std.Antisymm α r] (r' : β → β → Prop) [inst : @DecidableRel β β r'] [inst : IsTrans β r']
        [inst : @Std.Antisymm β r'] [inst : @Std.Total β r'],
        (∀ (a : α),
            @Membership.mem α (Multiset α) (@Multiset.instMembership α) s a →
              ∀ (b : α), @Membership.mem α (Multiset α) (@Multiset.instMembership α) s b → Iff (r a b) (r' (f a) (f b))) →
          @Std.Total α r) := fun hc_h => HypCheckProof.Multiset.map_sort.h8.inst (@hc_h (Nat) (Nat) (fun (n : Nat) =>
      @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))) (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (Nat.decLt) _ _ (fun (a b : Nat) => @LE.le Nat instLENat a b) (Nat.decLe) _ _ (@Std.Total.mk (Nat) (fun (a b : Nat) => @LE.le Nat instLENat a b) (by (try dsimp only);   (intros; omega))) HypCheckProof.Multiset.map_sort.h8.prem0)

-- Ordnode.Valid'.node3L, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node3L.h10 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α} {o₁ : WithBot α}
        {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x →
          Ordnode.Valid' (↑y) r o₂ →
            Ordnode.BalancedSz l.size m.size →
              Ordnode.BalancedSz (l.size + m.size + 1) r.size → Ordnode.Valid' o₁ (l.node3L x m y r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (Ordnode.nil) (0) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.node, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node.h8 : ¬∀ {α : Type} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑x) r o₂ →
          Ordnode.BalancedSz l.size r.size → s = l.size + r.size + 1 → Ordnode.Valid' o₁ (Ordnode.node s l x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) _ (Ordnode.nil) (0) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide) rfl) (by
  nofun)

-- Ordnode.Valid'.node, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node.h9 : ¬∀ {α : Type} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x →
          Ordnode.BalancedSz l.size r.size → s = l.size + r.size + 1 → Ordnode.Valid' o₁ (Ordnode.node s l x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) _ (Ordnode.nil) (1) (Ordnode.nil) (0) (0) (by
  (repeat' constructor) <;> done) (by
  decide) rfl) (by
  nofun)

-- Finsupp.mapRange_comp, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mapRange_comp.h10 : ¬∀ {α M N O : Type} [inst : Zero M] [inst_1 : Zero N] [inst_2 : Zero O] (f : N → O),
        f 0 = 0 → ∀ (f₂ : M → N), (f ∘ f₂) 0 = 0 → ∀ (g : α →₀ M), f₂ 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun _ => 0 : ℕ → ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (fun n => n + 1 : ℕ → ℕ) (by
  decide) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  decide +kernel)

-- Multiset.foldl_induction', hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldl_induction'.h3.inst : Not
      (@RightCommutative Nat Bool fun (a : Bool) (n : Nat) =>
        @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  exact fun hc_c =>
    absurd (hc_c.right_comm (Bool.false : Bool) (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldl_induction'.h3.prem0 : ∀ (a : Nat) (b : Bool),
      @Eq Nat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq Bool b Bool.true →
          (fun (b : Bool) => @Eq Bool b Bool.true)
            ((fun (a : Bool) (n : Nat) =>
                @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                  (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              b a) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldl_induction'.h3.prem1 : (fun (b : Bool) => @Eq Bool b Bool.true) Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.foldl_induction'.h3.prem2 : ∀ (a : Nat),
      @Membership.mem Nat (Multiset Nat) (@Multiset.instMembership Nat)
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))) a →
        (fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) a := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Multiset.foldl_induction'.h3 : Not
      (∀ {α β : Type} (f : β → α → β) (x : β) (q : α → Prop) (p : β → Prop) (s : Multiset α),
        (∀ (a : α) (b : β), q a → p b → p (f b a)) →
          p x →
            (∀ (a : α), @Membership.mem α (Multiset α) (@Multiset.instMembership α) s a → q a) → @RightCommutative α β f) := fun hc_h => HypCheckProof.Multiset.foldl_induction'.h3.inst (@hc_h (Nat) (Bool) (fun (a : Bool) (n : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Bool.true) (fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))) HypCheckProof.Multiset.foldl_induction'.h3.prem0 HypCheckProof.Multiset.foldl_induction'.h3.prem1 HypCheckProof.Multiset.foldl_induction'.h3.prem2)

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

-- Finset.fold_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_image.h5 : ¬∀ {α β γ : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} [inst : DecidableEq α] {g : γ → α}
        {s : Finset γ}, Set.InjOn g ↑s → Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.fold_ite, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_ite.h3.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
theorem HypCheckProof.Finset.fold_ite.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α}
        [inst : Std.IdempotentOp op] {g : α → β} (p : α → Prop) [inst : DecidablePred p], Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_ite.h3.inst (@hc_h (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (@Std.IdempotentOp.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) (fun (n : ℕ) => n = 0) (fun (a : ℕ) => instDecidableEqNat a 0))

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

-- Finset.fold_op_rel_iff_and, hypothesis 3: necessary
/- FAILED: 4:3: `simp` made no progress | 19:3: `simp` made no progress | 4:3: `simp` made no progress | 5:3: `simp` made no progress | 15:426: don't know how to synthesize implicit argument `z`
  @h3.prem0 (?m.29 hc_h) (?m.30 hc_h) (?m.31 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Commutative op
x✝ y✝ z✝ : Bool
⊢ Bool | 33:68: don't know how to synthesize implicit argument `z`
  @h3.prem0 (?m.10 hc_h) (?m.11 hc_h) (?m.12 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Commutative op
x✝ y✝ z✝ : Bool
⊢ Bool | 15:492: don't know how to synthesize implicit argument `z`
  @h3.prem0 (?m.27 hc_h) (?m.28 hc_h) (?m.29 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Commutative op
x✝ y✝ z✝ : Bool
⊢ Bool | 19:334: don't know how to synthesize implicit argument `z`
  @h3.prem0 (?m.12 hc_h) (?m.13 hc_h) (?m.14 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Commutative op
x✝ y✝ z✝ : Bool
⊢ Bool
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_op_rel_iff_and.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
        (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a _ => a : Bool → Bool → Bool) (@Std.Associative.mk (Bool) (fun (a x : Bool) => a) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun _ _ => True : Bool → Bool → Prop) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))
-/

-- Finset.fold_op_rel_iff_and, hypothesis 4: necessary
/- FAILED: 4:3: `simp` made no progress | 19:3: `simp` made no progress | 4:3: `simp` made no progress | 5:3: `simp` made no progress | 15:446: don't know how to synthesize implicit argument `z`
  @h4.prem0 (?m.29 hc_h) (?m.30 hc_h) (?m.31 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Associative op
x✝ y✝ z✝ : Bool
⊢ Bool | 33:68: don't know how to synthesize implicit argument `z`
  @h4.prem0 (?m.10 hc_h) (?m.11 hc_h) (?m.12 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Associative op
x✝ y✝ z✝ : Bool
⊢ Bool | 15:512: don't know how to synthesize implicit argument `z`
  @h4.prem0 (?m.27 hc_h) (?m.28 hc_h) (?m.29 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Associative op
x✝ y✝ z✝ : Bool
⊢ Bool | 19:334: don't know how to synthesize implicit argument `z`
  @h4.prem0 (?m.12 hc_h) (?m.13 hc_h) (?m.14 hc_h)
context:
hc_h :
  ∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
    (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Associative op
x✝ y✝ z✝ : Bool
⊢ Bool
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_op_rel_iff_and.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {s : Finset α} {r : β → β → Prop},
        (∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) → ∀ {c : β}, Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun _ _ => True : Bool → Bool → Prop) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))
-/

-- Finset.fold_disjUnion, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_disjUnion.h3.inst : ¬Std.Commutative fun (a x : ℕ) => a := by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_disjUnion.h3.prem0 : Disjoint { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }
      { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ } := by
  decide
theorem HypCheckProof.Finset.fold_disjUnion.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {s₁ s₂ : Finset α} {b₁ b₂ : β},
        Disjoint s₁ s₂ → Std.Commutative op := fun hc_h => HypCheckProof.Finset.fold_disjUnion.h3.inst (@hc_h (ℕ) (ℕ) (fun (a x : ℕ) => a) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun (n : ℕ) => n + 1) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0) HypCheckProof.Finset.fold_disjUnion.h3.prem0)

-- Finset.fold_disjUnion, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_disjUnion.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {s₁ s₂ : Finset α} {b₁ b₂ : β},
        Disjoint s₁ s₂ → Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Bool.false) (Bool.false) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fintype.eq_of_subsingleton_of_sum_eq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.eq_of_subsingleton_of_sum_eq.h9 : ¬∀ {M : Type} [inst : AddCommMonoid M] {ι : Type} [inst_1 : Subsingleton ι] {s : Finset ι} {f : ι → M} {b : M},
        ∑ i ∈ s, f i = b → ∀ (i : ι), f i = b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddCommMonoid) (Unit) _ ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Unit }) (fun (a : Unit) => 1) _ rfl (PUnit.unit)) (by
  decide +kernel)

-- Multiset.sort_cons, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.sort_cons.h6.inst : Not (@Std.Antisymm Bool fun (x x_1 : Bool) => True) := by
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
theorem HypCheckProof.Multiset.sort_cons.h6.prem0 : ∀ (b : Bool),
      @Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
          (@OfNat.ofNat (Multiset Bool) (nat_lit 0) (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool))) b →
        (fun (x x_1 : Bool) => True) Bool.false b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Multiset.sort_cons.h6 : Not
      (∀ {α : Type} (a : α) (s : Multiset α) (r : α → α → Prop) [inst : @DecidableRel α α r] [inst : IsTrans α r]
        [inst : @Std.Total α r],
        (∀ (b : α), @Membership.mem α (Multiset α) (@Multiset.instMembership α) s b → r a b) → @Std.Antisymm α r) := fun hc_h => HypCheckProof.Multiset.sort_cons.h6.inst (@hc_h (Bool) (Bool.false) (@OfNat.ofNat (Multiset Bool) (nat_lit 0) (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool))) (fun (x x_1 : Bool) => True) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) HypCheckProof.Multiset.sort_cons.h6.prem0)

-- Multiset.sort_cons, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.sort_cons.h7.inst : Not (@Std.Total Nat fun (a b : Nat) => @LT.lt Nat instLTNat a b) := by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Multiset.sort_cons.h7.prem0 : ∀ (b : Nat),
      @Membership.mem Nat (Multiset Nat) (@Multiset.instMembership Nat)
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))) b →
        (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Multiset.sort_cons.h7 : Not
      (∀ {α : Type} (a : α) (s : Multiset α) (r : α → α → Prop) [inst : @DecidableRel α α r] [inst : IsTrans α r]
        [inst : @Std.Antisymm α r],
        (∀ (b : α), @Membership.mem α (Multiset α) (@Multiset.instMembership α) s b → r a b) → @Std.Total α r) := fun hc_h => HypCheckProof.Multiset.sort_cons.h7.inst (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))) (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (Nat.decLt) _ _ HypCheckProof.Multiset.sort_cons.h7.prem0)

-- Finset.fold_const, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_const.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {b : β} {s : Finset α} [hd : Decidable (s = ∅)] (c : β),
        op c (op b c) = op b c → Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.decidableEq ∅) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.fold_const, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_const.h4.inst : ¬Std.Associative fun (a b : Bool) => !(a && b) := by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.fold_const.h4.prem0 : (fun (a b : Bool) => !(a && b)) Bool.false ((fun (a b : Bool) => !(a && b)) Bool.false Bool.false) =
      (fun (a b : Bool) => !(a && b)) Bool.false Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.fold_const.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {b : β} {s : Finset α} [hd : Decidable (s = ∅)] (c : β),
        op c (op b c) = op b c → Std.Associative op := fun hc_h => HypCheckProof.Finset.fold_const.h4.inst (@hc_h (ℕ) (Bool) (fun (a b : Bool) => !(a && b)) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.decidableEq ∅) (Bool.false) HypCheckProof.Finset.fold_const.h4.prem0)

-- Computation.liftRel_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Computation.liftRel_of_mem.h8.inst : ¬Computation.LiftRel (fun (a b : ℕ) => a < b) (Computation.pure 0) (Computation.pure 0) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Computation.liftRel_of_mem.h8.prem0 : 0 ∈ Computation.pure 0 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Computation.liftRel_of_mem.h8.prem1 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Computation.liftRel_of_mem.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β} {ca : Computation α} {cb : Computation β},
        a ∈ ca → R a b → Computation.LiftRel R ca cb := fun hc_h => HypCheckProof.Computation.liftRel_of_mem.h8.inst (@hc_h (ℕ) (ℕ) (fun (a b : ℕ) => a < b) (0) (1) (Computation.pure 0) (Computation.pure 0) HypCheckProof.Computation.liftRel_of_mem.h8.prem0 HypCheckProof.Computation.liftRel_of_mem.h8.prem1)

-- Computation.liftRel_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.liftRel_of_mem.h9 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β} {ca : Computation α} {cb : Computation β},
        a ∈ ca → b ∈ cb → Computation.LiftRel R ca cb := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (Computation.pure 0 : Computation ℕ) (Computation.pure 0 : Computation ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- Finset.noncommProd_erase_mul, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.noncommProd_erase_mul.h6 : Not
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
          (@HMul.hMul β β β (@instHMul β (@MulOne.toMul β (@MulOneClass.toMulOne β (@Monoid.toMulOneClass β inst))))
            (@Finset.noncommProd α β inst (@Finset.erase α inst_1 s a) f comm') (f a))
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

-- Fintype.eq_of_subsingleton_of_prod_eq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.eq_of_subsingleton_of_prod_eq.h9 : ¬∀ {M : Type} [inst : CommMonoid M] {ι : Type} [inst_1 : Subsingleton ι] {s : Finset ι} {f : ι → M} {b : M},
        ∏ i ∈ s, f i = b → ∀ (i : ι), f i = b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoid) (Unit) _ ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Unit }) (fun (a : Unit) => 0) _ rfl (PUnit.unit)) (by
  decide +kernel)

-- Ordnode.Valid'.balanceL, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balanceL.h7 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑x) r o₂ →
          ((∃ (l' : ℕ), Ordnode.Raised l' l.size ∧ Ordnode.BalancedSz l' r.size) ∨
              ∃ (r' : ℕ), Ordnode.Raised r.size r' ∧ Ordnode.BalancedSz l.size r') →
            Ordnode.Valid' o₁ (l.balanceL x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Valid'.balanceL, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balanceL.h8 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x →
          ((∃ (l' : ℕ), Ordnode.Raised l' l.size ∧ Ordnode.BalancedSz l' r.size) ∨
              ∃ (r' : ℕ), Ordnode.Raised r.size r' ∧ Ordnode.BalancedSz l.size r') →
            Ordnode.Valid' o₁ (l.balanceL x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (Ordnode.nil) (0) (0) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Valid'.balanceR, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balanceR.h7 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑x) r o₂ →
          ((∃ (l' : ℕ), Ordnode.Raised l.size l' ∧ Ordnode.BalancedSz l' r.size) ∨
              ∃ (r' : ℕ), Ordnode.Raised r' r.size ∧ Ordnode.BalancedSz l.size r') →
            Ordnode.Valid' o₁ (l.balanceR x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (Ordnode.nil) (0) (1) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Valid'.balanceR, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.balanceR.h8 : ¬∀ {α : Type} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ l ↑x →
          ((∃ (l' : ℕ), Ordnode.Raised l.size l' ∧ Ordnode.BalancedSz l' r.size) ∨
              ∃ (r' : ℕ), Ordnode.Raised r' r.size ∧ Ordnode.BalancedSz l.size r') →
            Ordnode.Valid' o₁ (l.balanceR x r) o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (Ordnode.nil) (0) (0) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Finset.sup_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_mem.h4.inst : ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.sup fun (n : ℕ) => n % 2 == 0) ∉
      {b : Bool | b = Bool.true} := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_mem.h4.prem0 : ∀ x ∈ {b : Bool | b = Bool.true}, ∀ y ∈ {b : Bool | b = Bool.true}, Max.max x y ∈ {b : Bool | b = Bool.true} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_mem.h4.prem1 : ∀ i ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      (fun (n : ℕ) => n % 2 == 0) i ∈ {b : Bool | b = Bool.true} := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sup_mem.h4 : ¬∀ {α : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] (s : Set α),
        (∀ x ∈ s, ∀ y ∈ s, x ⊔ y ∈ s) → ∀ {ι : Type} (t : Finset ι) (p : ι → α), (∀ i ∈ t, p i ∈ s) → t.sup p ∈ s := fun hc_h => HypCheckProof.Finset.sup_mem.h4.inst (@hc_h (Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeSup) (CompleteLattice.toCompletePartialOrder.toOrderBot) ({b : Bool | b = Bool.true}) HypCheckProof.Finset.sup_mem.h4.prem0 (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n % 2 == 0) HypCheckProof.Finset.sup_mem.h4.prem1)

-- Finset.sup_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_mem.h9 : Not
      (∀ {α : Type} [inst : SemilatticeSup α]
        [inst_1 : @OrderBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))]
        (s : Set α),
        @Membership.mem α (Set α) (@Set.instMembership α) s
            (@Bot.bot α
              (@OrderBot.toBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))
                inst_1)) →
          (∀ (x : α),
              @Membership.mem α (Set α) (@Set.instMembership α) s x →
                ∀ (y : α),
                  @Membership.mem α (Set α) (@Set.instMembership α) s y →
                    @Membership.mem α (Set α) (@Set.instMembership α) s (@Max.max α (@SemilatticeSup.toMax α inst) x y)) →
            ∀ {ι : Type} (t : Finset ι) (p : ι → α),
              @Membership.mem α (Set α) (@Set.instMembership α) s (@Finset.sup α ι inst inst_1 t p)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (Nat.instOrderBot) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide) (by
  grind) (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.sup_induction, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_induction.h7.inst : ¬(fun (b : Bool) => b = Bool.true)
        ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.sup fun (n : ℕ) => n % 2 == 0) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_induction.h7.prem0 : ∀ (a₁ : Bool), a₁ = Bool.true → ∀ (a₂ : Bool), a₂ = Bool.true → (fun (b : Bool) => b = Bool.true) (Max.max a₁ a₂) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_induction.h7.prem1 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      (fun (b : Bool) => b = Bool.true) ((fun (n : ℕ) => n % 2 == 0) b) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sup_induction.h7 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {p : α → Prop},
        (∀ (a₁ : α), p a₁ → ∀ (a₂ : α), p a₂ → p (a₁ ⊔ a₂)) → (∀ b ∈ s, p (f b)) → p (s.sup f) := fun hc_h => HypCheckProof.Finset.sup_induction.h7.inst (@hc_h (Bool) (ℕ) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeSup) (CompleteLattice.toCompletePartialOrder.toOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n % 2 == 0) (fun (b : Bool) => b = Bool.true) HypCheckProof.Finset.sup_induction.h7.prem0 HypCheckProof.Finset.sup_induction.h7.prem1)

-- Finset.sup_induction, hypothesis 9: necessary
/- FAILED: 3:217: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide {0}.Nodup = true
in the application
  id (Eq.refl true) | 32:3: `simp` made no progress | 4:3: `simp` made no progress | 15:3: `simp` made no progress | 3:54: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide {0}.Nodup = true
in the application
  id (Eq.refl true) | 45:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 9:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 28:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_induction.h9 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {p : α → Prop},
        p ⊥ → (∀ (a₁ : α), p a₁ → ∀ (a₂ : α), p a₂ → p (a₁ ⊔ a₂)) → p (s.sup f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := {0}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp)) (by
  decide +kernel)
-/

-- Finset.comp_inf_eq_inf_comp_of_is_total, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.comp_inf_eq_inf_comp_of_is_total.h11 : ¬∀ {α β ι : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] {s : Finset ι} {f : ι → α} [inst_2 : SemilatticeInf β]
        [inst_3 : OrderTop β] (g : α → β), Monotone g → g (s.inf f) = s.inf (g ∘ f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) (fun _ => false : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Finset.apply_sup_eq_sup_comp_of_linearOrder, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.apply_sup_eq_sup_comp_of_linearOrder.h11 : ¬∀ {α β ι : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} [inst_2 : SemilatticeSup β]
        [inst_3 : OrderBot β] (g : α → β), Monotone g → g (s.sup f) = s.sup (g ∘ f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (Bool.linearOrder) (CompleteLattice.toCompletePartialOrder.toOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeSup) (CompleteLattice.toCompletePartialOrder.toOrderBot) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Finset.comp_sup_eq_sup_comp, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.comp_sup_eq_sup_comp.h11 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] [inst_2 : SemilatticeSup γ] [inst_3 : OrderBot γ]
        {s : Finset β} {f : β → α} (g : α → γ), (∀ (x y : α), g (x ⊔ y) = g x ⊔ g y) → g (s.sup f) = s.sup (g ∘ f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  grind)) (by
  decide +kernel)

-- Finset.apply_inf_eq_inf_comp_of_nonempty, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.apply_inf_eq_inf_comp_of_nonempty.h11 : ¬∀ {α β ι : Type} [inst : LinearOrder α] {s : Finset ι} {f : ι → α} [inst_1 : OrderTop α] [inst_2 : SemilatticeInf β]
        [inst_3 : OrderTop β] {g : α → β}, Monotone g → g (s.inf f) = s.inf (g ∘ f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (Bool.linearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) (fun _ => false : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Finset.apply_sup_eq_sup_comp_of_nonempty, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.apply_sup_eq_sup_comp_of_nonempty.h11 : ¬∀ {α β ι : Type} [inst : LinearOrder α] {s : Finset ι} {f : ι → α} [inst_1 : OrderBot α] [inst_2 : SemilatticeSup β]
        [inst_3 : OrderBot β] {g : α → β}, Monotone g → g (s.sup f) = s.sup (g ∘ f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (Bool.linearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (CompleteLattice.toCompletePartialOrder.toOrderBot) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeSup) (CompleteLattice.toCompletePartialOrder.toOrderBot) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Multiset.Rel.countP_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Rel.countP_eq.h8 : ¬∀ {α : Type} (r : α → α → Prop) [inst : IsTrans α r] [inst : Std.Symm r] {s t : Multiset α} (x : α)
        [inst : DecidablePred (r x)], Multiset.countP (r x) s = Multiset.countP (r x) t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Symm.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) ((0 : Multiset Bool) : Multiset Bool) (({true} : Multiset Bool) : Multiset Bool) (Bool.false) (fun (a : Bool) => instDecidableTrue)) (by
  decide +kernel)

-- Finset.inf'_mem, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf'_mem.h6.inst : ¬{ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.Nonempty := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf'_mem.h6.prem0 : ∀ x ∈ {n : ℕ | n = 0}, ∀ y ∈ {n : ℕ | n = 0}, Min.min x y ∈ {n : ℕ | n = 0} := by
  grind
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf'_mem.h6.prem1 : ∀ i ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      (fun (n : ℕ) => n + 1) i ∈ {n : ℕ | n = 0} := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.inf'_mem.h6 : ¬∀ {α : Type} [inst : SemilatticeInf α] (s : Set α),
        (∀ x ∈ s, ∀ y ∈ s, x ⊓ y ∈ s) → ∀ {ι : Type} (t : Finset ι) (p : ι → α), (∀ i ∈ t, p i ∈ s) → t.Nonempty := fun hc_h => HypCheckProof.Finset.inf'_mem.h6.inst (@hc_h (ℕ) (Nat.instLattice.toSemilatticeInf) ({n : ℕ | n = 0}) HypCheckProof.Finset.inf'_mem.h6.prem0 (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) HypCheckProof.Finset.inf'_mem.h6.prem1)

-- Ordnode.Valid'.of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.of_lt.h6 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.nil.Bounded o₁ ↑x → Ordnode.All (fun (x_1 : α) => x_1 < x) t → Ordnode.Valid' o₁ t ↑x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (1) (0) (0) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.of_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.of_lt.h7 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ t o₂ → Ordnode.All (fun (x_1 : α) => x_1 < x) t → Ordnode.Valid' o₁ t ↑x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.of_gt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.of_gt.h6 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.nil.Bounded (↑x) o₂ → Ordnode.All (fun (x_1 : α) => x_1 > x) t → Ordnode.Valid' (↑x) t o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 1 Ordnode.nil) (0) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Ordnode.Valid'.of_gt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.of_gt.h7 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' o₁ t o₂ → Ordnode.All (fun (x_1 : α) => x_1 > x) t → Ordnode.Valid' (↑x) t o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (1) (0) (1) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Multiset.noncommSum_induction, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommSum_induction.h6 : ¬∀ {α : Type} [inst : AddMonoid α] (s : Multiset α) (comm : {x : α | x ∈ s}.Pairwise AddCommute) (p : α → Prop),
        (∀ (a b : α), p a → p b → p (a + b)) → (∀ x ∈ s, p x) → p (s.noncommSum comm) := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) (Nat.instAddMonoid) ((0 : Multiset Nat) : Multiset ℕ) hc_k0 (fun _ => False : ℕ → Prop) hc_k1 hc_k2) (by
  simp)

-- Multiset.noncommFold_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommFold_cons.h2 : ¬∀ {α : Type} (op : α → α → α) (s : Multiset α) (a : α),
        ({x : α | x ∈ a ::ₘ s}.Pairwise fun (x y : α) => op x y = op y x) →
          ({x : α | x ∈ s}.Pairwise fun (x y : α) => op x y = op y x) → ∀ (x : α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !a || b : Bool → Bool → Bool) ((0 : Multiset Bool) : Multiset Bool) (Bool.false) (by
  simp) (by
  simp) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.forall_of_forall_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.forall_of_forall_cons.h4 : Not
      (∀ {α : Type} {s : Finset α} {a : α} {p : α → Prop} (x : α),
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun n => n = 0 : Nat → Prop) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.forall_of_forall_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.forall_of_forall_cons.h7 : ¬∀ {α : Type} {s : Finset α} {a : α} {p : α → Prop} {h : a ∉ s}, (∀ x ∈ Finset.cons a s h, p x) → ∀ (x : α), p x := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (fun n => n = 0 : ℕ → Prop) hc_k0 hc_k1 (1)) (by
  decide +kernel)

-- Finset.cons_sdiff_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_sdiff_cons.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α} (ha : a ∉ s) (hb : b ∉ s),
        Finset.cons a s ha \ Finset.cons b s hb = {a} := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- Finset.cons_sdiff_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_sdiff_cons.h6 : Not (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, @Ne α a b → b ∉ s → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.cons_sdiff_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_sdiff_cons.h7 : Not (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, @Ne α a b → a ∉ s → b ∉ s) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.sup_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_congr.h8 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α]
        [inst_1 : @OrderBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))]
        {s₁ s₂ : Finset β} {f g : β → α},
        (∀ (a : β),
            @Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β)) s₂ a →
              @Eq α (f a) (g a)) →
          @Eq α (@Finset.sup α β inst inst_1 s₁ f) (@Finset.sup α β inst inst_1 s₂ g)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (Nat.instOrderBot) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.sup_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_congr.h9 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α]
        [inst_1 : @OrderBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))]
        {s₁ s₂ : Finset β} {f g : β → α},
        @Eq (Finset β) s₁ s₂ → @Eq α (@Finset.sup α β inst inst_1 s₁ f) (@Finset.sup α β inst inst_1 s₂ g)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (Nat.instOrderBot) _ (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Equiv.Finset.union_symm_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.union_symm_left.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {i : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i →
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

-- Equiv.Finset.union_symm_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Finset.union_symm_left.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t →
          ∀ {i : α},
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
                (@Max.max (Finset α) (@Finset.instMax α inst) s t) i →
              @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.apply_sup'_eq_sup'_comp, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.apply_sup'_eq_sup'_comp.h6 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β} {f : β → α} (g : α → γ),
        (∀ (x y : α), g (x ⊔ y) = g x ⊔ g y) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  grind)) (by
  decide +kernel)

-- Finset.apply_sup'_eq_sup'_comp, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.apply_sup'_eq_sup'_comp.h9 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
        (g : α → γ), g (s.sup' H f) = s.sup' H (g ∘ f) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (Bool) (Bool) (Nat.instLattice.toSemilatticeSup) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeSup) ({ val := {Bool.true, Bool.false}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) hc_k0 (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- Finset.card_nbij, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_nbij.h5 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} (i : α → β),
        @Set.InjOn α β i (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) →
          @Set.SurjOn α β i (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
              (@SetLike.coe (Finset β) β (@Finset.instSetLike β) t) →
            @Eq Nat (@Finset.card α s) (@Finset.card β t)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.card_nbij, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_nbij.h7 : Not
      (∀ {α β : Type} {s : Finset α} {t : Finset β} (i : α → β),
        @Set.MapsTo α β i (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
            (@SetLike.coe (Finset β) β (@Finset.instSetLike β) t) →
          @Set.InjOn α β i (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s) →
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
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.apply_inf'_eq_inf'_comp, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.apply_inf'_eq_inf'_comp.h6 : ¬∀ {α β γ : Type} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf γ] {s : Finset β} {f : β → α} (g : α → γ),
        (∀ (x y : α), g (x ⊓ y) = g x ⊓ g y) → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  grind)) (by
  decide +kernel)

-- Finset.min'_lt_max', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_lt_max'.h6 : Not
      (∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {i j : α}
        (H1 : @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i),
        @Ne α i j →
          @LT.lt α
            (@Preorder.toLT α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
            (@Finset.min' α inst s
              (@Exists.intro α
                (fun (x : α) =>
                  @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x)
                i H1))
            (@Finset.max' α inst s
              (@Exists.intro α
                (fun (x : α) =>
                  @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x)
                i H1))) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) hc_k0 hc_k1) (by
  decide +kernel)

-- Finset.min'_lt_max', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_lt_max'.h7 : Not
      (∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {i j : α}
        (H1 : @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i),
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s j →
          @LT.lt α
            (@Preorder.toLT α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
            (@Finset.min' α inst s
              (@Exists.intro α
                (fun (x : α) =>
                  @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x)
                i H1))
            (@Finset.max' α inst s
              (@Exists.intro α
                (fun (x : α) =>
                  @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x)
                i H1))) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k0 hc_k1) (by
  decide +kernel)

-- Finset.sup_preimage_val_id, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_preimage_val_id.h5.inst : ¬(fun (b : Bool) => b = Bool.true) ⊥ := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_preimage_val_id.h5.prem0 : ∀ ⦃s t : Bool⦄, s = Bool.true → t = Bool.true → (fun (b : Bool) => b = Bool.true) (Max.max s t) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_preimage_val_id.h5.prem1 : ∀ x ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool },
      (fun (b : Bool) => b = Bool.true) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sup_preimage_val_id.h5 : ¬∀ {α : Type} [inst : Lattice α] [inst_1 : OrderBot α] {P : α → Prop},
        (∀ ⦃s t : α⦄, P s → P t → P (s ⊔ t)) → ∀ {t : Finset α}, (∀ x ∈ t, P x) → P ⊥ := fun hc_h => HypCheckProof.Finset.sup_preimage_val_id.h5.inst (@hc_h (Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toLattice) (CompleteLattice.toCompletePartialOrder.toOrderBot) (fun (b : Bool) => b = Bool.true) HypCheckProof.Finset.sup_preimage_val_id.h5.prem0 ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) HypCheckProof.Finset.sup_preimage_val_id.h5.prem1)

-- Finset.sup_preimage_val_id, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_preimage_val_id.h7.inst : Not
      (∀ (x : Nat),
        @Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
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
            x →
          (fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) x) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_preimage_val_id.h7.prem0 : ∀ ⦃s t : Nat⦄,
      @Eq Nat s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq Nat t (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          (fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Max.max Nat (@SemilatticeSup.toMax Nat (@Lattice.toSemilatticeSup Nat Nat.instLattice)) s t) := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_preimage_val_id.h7.prem1 : (fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Bot.bot Nat
        (@OrderBot.toBot Nat
          (@Preorder.toLE Nat
            (@PartialOrder.toPreorder Nat
              (@SemilatticeInf.toPartialOrder Nat (@Lattice.toSemilatticeInf Nat Nat.instLattice))))
          Nat.instOrderBot)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sup_preimage_val_id.h7 : Not
      (∀ {α : Type} [inst : Lattice α]
        [inst_1 :
          @OrderBot α
            (@Preorder.toLE α
              (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α (@Lattice.toSemilatticeInf α inst))))]
        {P : α → Prop},
        (∀ ⦃s t : α⦄, P s → P t → P (@Max.max α (@SemilatticeSup.toMax α (@Lattice.toSemilatticeSup α inst)) s t)) →
          P
              (@Bot.bot α
                (@OrderBot.toBot α
                  (@Preorder.toLE α
                    (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α (@Lattice.toSemilatticeInf α inst))))
                  inst_1)) →
            ∀ {t : Finset α} (x : α),
              @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t x → P x) := fun hc_h => HypCheckProof.Finset.sup_preimage_val_id.h7.inst (@hc_h (Nat) (Nat.instLattice) (Nat.instOrderBot) (fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Finset.sup_preimage_val_id.h7.prem0 HypCheckProof.Finset.sup_preimage_val_id.h7.prem1 (@Finset.mk Nat
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

-- Multiset.mem_sort, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_sort.h6 : ¬∀ {α : Type} {a : α} {s : Multiset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r]
        [inst : Std.Total r], Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) (Bool.false) ((0 : Multiset Bool) : Multiset Bool) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
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

-- Multiset.mem_sort, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_sort.h7 : ¬∀ {α : Type} {a : α} {s : Multiset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r]
        [inst : Std.Antisymm r], Std.Total r := fun hc_h => absurd (@hc_h (ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.mem_sort, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_sort.h5 : ¬∀ {α : Type} {s : Finset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r]
        {a : α}, Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Finset.mem_sort, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_sort.h6 : ¬∀ {α : Type} {s : Finset α} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r]
        {a : α}, Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.mul_noncommProd_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mul_noncommProd_erase.h5 : ¬∀ {α : Type} [inst : Monoid α] [inst_1 : DecidableEq α] (s : Multiset α) {a : α}
        (comm : {x : α | x ∈ s}.Pairwise Commute)
        (comm' :
          optParam (∀ x ∈ {x : α | x ∈ s.erase a}, ∀ x_1 ∈ {x : α | x ∈ s.erase a}, x ≠ x_1 → Commute x x_1)
            fun (x : α) (hx : x ∈ {x : α | x ∈ s.erase a}) (x_1 : α) (hy : x_1 ∈ {x : α | x ∈ s.erase a}) (hxy : x ≠ x_1) =>
            comm (Multiset.mem_of_mem_erase hx) (Multiset.mem_of_mem_erase hy) hxy),
        a * (s.erase a).noncommProd comm' = s.noncommProd comm := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (Nat.instMonoid) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (0) hc_k0 hc_k1) (by
  simp)

-- Finset.sup_coe, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_coe.h5.inst : ¬(fun (b : Bool) => b = Bool.true) ⊥ := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.sup_coe.h5.prem0 : ∀ ⦃x y : Bool⦄, x = Bool.true → y = Bool.true → (fun (b : Bool) => b = Bool.true) (Max.max x y) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.sup_coe.h5 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {P : α → Prop}
        {Psup : ∀ ⦃x y : α⦄, P x → P y → P (x ⊔ y)} (t : Finset β) (f : β → { x : α // P x }), P ⊥ := fun hc_h => HypCheckProof.Finset.sup_coe.h5.inst (@hc_h (Bool) (ℕ) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeSup) (CompleteLattice.toCompletePartialOrder.toOrderBot) (fun (b : Bool) => b = Bool.true) HypCheckProof.Finset.sup_coe.h5.prem0 ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ) =>
      (⟨Bool.true, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Bool // (fun (b : Bool) => b = Bool.true) x })))

-- Finsupp.support_mapRange_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_mapRange_eq.h6 : ¬∀ {α M N : Type} [inst : Zero M] [inst_1 : Zero N] {f : M → N} (g : α →₀ M), (∀ (x : M), f x = 0 → x = 0) → f 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ) (by
  simp)) (by
  decide +kernel)

-- Finset.inf'_le_of_le, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf'_le_of_le.h7.inst : 0 ∉ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ } := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf'_le_of_le.h7.prem0 : (fun (n : ℕ) => n + 1) 0 ≤ 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.inf'_le_of_le.h7 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) {a : α} {b : β}, f b ≤ a → b ∈ s := fun hc_h => HypCheckProof.Finset.inf'_le_of_le.h7.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (1) (0) HypCheckProof.Finset.inf'_le_of_le.h7.prem0)

-- Finset.inf'_le_of_le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_le_of_le.h8 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) {a : α} {b : β}
        (hb : @Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β)) s b),
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))
          (@Finset.inf' α β inst s
            (@Exists.intro β
              (fun (x : β) =>
                @Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β)) s x)
              b hb)
            f)
          a) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k0) (by
  decide +kernel)

-- Finset.sup'_eq_one, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_eq_one.h7 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} [inst_2 : One α]
        (hs : s.Nonempty), s.sup' hs f = 1 ↔ ∀ i ∈ s, f i = 1 := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (Bool) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := {Bool.true, Bool.false}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (fun b => if b then 1 else 0 : Bool → ℕ) (Nat.instOne) hc_k0) (by
  decide +kernel)

-- Multiset.count_map_eq_count, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_map_eq_count.h6 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] (f : α → β) (s : Multiset α),
        ∀ x ∈ s, Multiset.count (f x) (Multiset.map f s) = Multiset.count x s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (fun _ => 0 : ℕ → ℕ) (({0, 1} : Multiset Nat) : Multiset ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Multiset.count_map_eq_count, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_map_eq_count.h8 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] (f : α → β) (s : Multiset α),
        Set.InjOn f {x : α | x ∈ s} → ∀ (x : α), Multiset.count (f x) (Multiset.map f s) = Multiset.count x s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (fun _ => 0 : ℕ → ℕ) (({0} : Multiset Nat) : Multiset ℕ) (by
  simp) (1)) (by
  decide +kernel)

-- Ordnode.Bounded.trans_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.trans_right.h7 : ¬∀ {α : Type} [inst : Preorder α] {t₁ t₂ : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        t₂.Bounded (↑x) o₂ → t₁.Bounded o₁ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.nil) (0) (1) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Bounded.trans_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.trans_right.h8 : ¬∀ {α : Type} [inst : Preorder α] {t₁ : Ordnode α} {t₂ : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        t₁.Bounded o₁ ↑x → t₁.Bounded o₁ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.nil) (1) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Valid'.trans_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.trans_left.h7 : ¬∀ {α : Type} [inst : Preorder α] {t₁ : Ordnode α} {t₂ : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.Valid' (↑x) t₂ o₂ → Ordnode.Valid' o₁ t₂ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.nil) (0) (1) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Valid'.trans_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.trans_left.h8 : ¬∀ {α : Type} [inst : Preorder α] {t₁ t₂ : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        t₁.Bounded o₁ ↑x → Ordnode.Valid' o₁ t₂ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.nil) (1) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.size_erase_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.size_erase_of_mem.h7 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : DecidableLE α] {x : α} {t : Ordnode α} {a₁ : WithBot α} {a₂ : WithTop α},
        x ∈ t → (Ordnode.erase x t).size = t.size - 1 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLe) (0) (Ordnode.node 0 (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) 0 (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.exists_subsuperset_card_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_subsuperset_card_eq.h6 : ¬∀ {α : Type} {s t : Finset α} {n : ℕ}, s ⊆ t → s.card ≤ n → ∃ (u : Finset α), s ⊆ u ∧ u ⊆ t ∧ u.card = n := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1) (by
  decide) (by
  decide)) (by
  simp)

-- Finset.mem_of_mem_cons_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_cons_of_ne.h3 : Not (∀ {α : Type} {s : Finset α} {a i : α}, @Ne α i a → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.mem_of_mem_cons_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_cons_of_ne.h5 : ¬∀ {α : Type} {s : Finset α} {a : α} {has : a ∉ s} {i : α}, i ≠ a → i ∈ s := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (by
  decide) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.mem_of_mem_cons_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_cons_of_ne.h6 : ¬∀ {α : Type} {s : Finset α} {a : α} {has : a ∉ s} {i : α}, i ∈ Finset.cons a s has → i ∈ s := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) hc_k0 (0) hc_k1) (by
  decide +kernel)

-- Multiset.pairwise_sort, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.pairwise_sort.h5 : ¬∀ {α : Type} (s : Multiset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
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

-- Multiset.pairwise_sort, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.pairwise_sort.h6 : ¬∀ {α : Type} (s : Multiset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.sort_nodup, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_nodup.h5 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
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

-- Finset.sort_nodup, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_nodup.h6 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.sort_val, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_val.h5 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r],
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

-- Finset.sort_val, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_val.h6 : ¬∀ {α : Type} (s : Finset α) (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r],
        Std.Total r := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.disjSum_lt_disjSum_of_le_of_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.disjSum_lt_disjSum_of_le_of_lt.h7 : ¬∀ {α β : Type} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β}, s₁ ≤ s₂ → s₁.disjSum t₁ < s₂.disjSum t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  simp)

-- Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset.h6 : ¬∀ {α β : Type} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β}, t₁ ⊆ t₂ → s₁.disjSum t₁ ⊂ s₂.disjSum t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Finset.inf'_eq_of_forall, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf'_eq_of_forall.h4.inst : ¬{ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }.Nonempty := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.inf'_eq_of_forall.h4.prem0 : ∀ b ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }, (fun (n : ℕ) => n + 1) b = 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.inf'_eq_of_forall.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) {a : α}, (∀ b ∈ s, f b = a) → s.Nonempty := fun hc_h => HypCheckProof.Finset.inf'_eq_of_forall.h4.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (n : ℕ) => n + 1) (0) HypCheckProof.Finset.inf'_eq_of_forall.h4.prem0)

-- Finset.inf'_eq_of_forall, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_eq_of_forall.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (H : @Finset.Nonempty β s) (f : β → α) {a : α},
        @Eq α (@Finset.inf' α β inst s H f) a) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.sup'_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_mono.h7 : ¬∀ {α β : Type} [inst : SemilatticeSup α] (f : β → α) {s₁ s₂ : Finset β}, s₁ ⊆ s₂ → s₁.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (fun n => n + 1 : ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Monotone.map_finset_max', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.map_finset_max'.h5 : Not
      (∀ {α β : Type} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β} {s : Finset α} (h : @Finset.Nonempty α s),
        @Eq β (f (@Finset.max' α inst s h))
          (@Finset.max' β inst_1 (@Finset.image α β (fun (a b : β) => @LinearOrder.toDecidableEq β inst_1 a b) f s)
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

-- Monotone.map_finset_max', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.map_finset_max'.h7 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β}, Monotone f → ∀ {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.linearOrder) (Nat.instLinearOrder) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Computation.exists_of_liftRel_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.exists_of_liftRel_left.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {ca : Computation α} {cb : Computation β} {a : α}, a ∈ ca → ∃ b ∈ cb, R a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Computation.pure 0 : Computation ℕ) (Inhabited.default) (0) (by
  simp)) (by
  nofun)

-- Multiset.exists_mem_of_rel_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.exists_mem_of_rel_of_mem.h7 : ¬∀ {α β : Type} {r : α → β → Prop} {s : Multiset α} {t : Multiset β}, Multiset.Rel r s t → ∀ {a : α}, ∃ b ∈ t, r a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  simp) (0)) (by
  simp)

-- Multiset.map_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_congr.h6 : ¬∀ {α β : Type} {f g : α → β} {s t : Multiset α}, (∀ x ∈ t, f x = g x) → Multiset.map f s = Multiset.map g t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Multiset.map_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_congr.h7 : ¬∀ {α β : Type} {f g : α → β} {s t : Multiset α}, s = t → Multiset.map f s = Multiset.map g t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) _ (({0} : Multiset Nat) : Multiset ℕ) rfl) (by
  decide +kernel)

-- Finset.consPiProd_snd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.consPiProd_snd.h4 : Not
      (∀ {α : Type} {s : Finset α} {a : α} (f : α → Type) (i : α),
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Bounded.mono_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.mono_right.h4 : ¬∀ {α : Type} [inst : Preorder α] {x y : α} {t : Ordnode α} {o : WithBot α}, t.Bounded o ↑x → t.Bounded o ↑y := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (1) (0) (Ordnode.nil) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Bounded.mono_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.mono_right.h7 : ¬∀ {α : Type} [inst : Preorder α] {x y : α}, x ≤ y → ∀ {t : Ordnode α} {o : WithBot α}, t.Bounded o ↑y := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (0) (by
  decide) (Ordnode.nil) (0)) (by
  nofun)

-- Ordnode.Valid'.mono_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.mono_left.h4 : ¬∀ {α : Type} [inst : Preorder α] {x y : α} {t : Ordnode α} {o : WithTop α},
        Ordnode.Valid' (↑y) t o → Ordnode.Valid' (↑x) t o := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (1) (0) (Ordnode.nil) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Valid'.mono_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.mono_left.h7 : ¬∀ {α : Type} [inst : Preorder α] {x y : α}, x ≤ y → ∀ {t : Ordnode α} {o : WithTop α}, Ordnode.Valid' (↑x) t o := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (0) (by
  decide) (Ordnode.nil) (0)) (by
  nofun)

-- Finset.min'_lt_of_mem_erase_min', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_lt_of_mem_erase_min'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) [inst : DecidableEq α] {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat) (0)) (by
  decide +kernel)

-- Finset.min'_lt_of_mem_erase_min', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_lt_of_mem_erase_min'.h6 : Not
      (∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (H : @Finset.Nonempty α s) [inst_1 : DecidableEq α] {a : α},
        @LT.lt α
          (@Preorder.toLT α
            (@PartialOrder.toPreorder α
              (@SemilatticeSup.toPartialOrder α
                (@Lattice.toSemilatticeSup α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
          (@Finset.min' α inst s H) a) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.notMem_of_lt_min, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_of_lt_min.h5 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a b : α},
        @Eq (WithTop α) (@Finset.min α inst s) (@WithTop.some α b) → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.notMem_of_lt_min, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_of_lt_min.h6 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a b : α},
        @LT.lt α
            (@Preorder.toLT α
              (@PartialOrder.toPreorder α
                (@SemilatticeSup.toPartialOrder α
                  (@Lattice.toSemilatticeSup α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
            a b →
          a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.le_max_of_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_max_of_eq.h5 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a b : α},
        @Eq (WithBot α) (@Finset.max α inst s) (@WithBot.some α b) →
          @LE.le α
            (@Preorder.toLE α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
            a b) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.le_max_of_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_max_of_eq.h6 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a b : α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s a →
          @LE.le α
            (@Preorder.toLE α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
            a b) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
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

-- Finset.compl_eq_of_disjoint_of_card_add_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.compl_eq_of_disjoint_of_card_add_eq.h6 : ¬∀ {ι : Type} [inst : DecidableEq ι] [inst_1 : Fintype ι] {S₁ S₂ : Finset ι}, Disjoint S₁ S₂ → S₁ᶜ = S₂ := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (Bool.fintype) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (by
  decide)) (by
  decide +kernel)

-- Disjoint.powersetCard_powersetCard_finset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.powersetCard_powersetCard_finset.h6 : ¬∀ {α : Type} {n : ℕ} {s t : Finset α},
        Disjoint s t → ∀ {m : ℕ}, Disjoint (Finset.powersetCard n s) (Finset.powersetCard m t) := fun hc_h => absurd (@hc_h (ℕ) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide) (0)) (by
  decide +kernel)

-- Multiset.countP_pos_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.countP_pos_of_mem.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {s : Multiset α} {a : α}, p a → 0 < Multiset.countP p s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ((0 : Multiset Nat) : Multiset ℕ) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.mem_of_mem_insert_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_insert_of_ne.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, b ≠ a → b ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.mem_of_mem_insert_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_insert_of_ne.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, b ∈ Insert.insert a s → b ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.insert_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_subset.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α}, s ⊆ t → Insert.insert a s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.mem_erase_of_ne_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_erase_of_ne_of_mem.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, a ≠ b → a ∈ s.erase b := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.union_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_subset.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) t
            u →
          @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Max.max (Finset α) (@Finset.instMax α inst) s t) u) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.union_subset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_subset.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s
            u →
          @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Max.max (Finset α) (@Finset.instMax α inst) s t) u) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.mem_inter_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_inter_of_mem.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {a : α} {s₁ s₂ : Finset α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s₂ a →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
            (@Min.min (Finset α) (@Finset.instMin α inst) s₁ s₂) a) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.mem_inter_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_inter_of_mem.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {a : α} {s₁ s₂ : Finset α},
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s₁ a →
          @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α))
            (@Min.min (Finset α) (@Finset.instMin α inst) s₁ s₂) a) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.insert_sdiff_insert', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_sdiff_insert'.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α}, a ∉ s → Insert.insert a s \ Insert.insert b s = {a} := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.insert_sdiff_insert', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_sdiff_insert'.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α},
        @Ne α a b →
          @Eq (Finset α)
            (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst)
              (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s)
              (@Insert.insert α (Finset α) (@Finset.instInsert α inst) b s))
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Finset.sdiff_union_sdiff_cancel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_union_sdiff_cancel.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t u : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) u
            t →
          @Eq (Finset α)
            (@Max.max (Finset α) (@Finset.instMax α inst) (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s t)
              (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t u))
            (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.map_disjUnion, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.map_disjUnion.h5 : ¬∀ {α β : Type} {f : α ↪ β} (s₁ s₂ : Finset α), Disjoint s₁ s₂ := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Multiset.find?_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.find?_some.h5 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] {a : α} {s : Multiset α}, {x : α | x ∈ s ∧ p x}.Subsingleton := fun hc_h => absurd (@hc_h (Bool) (fun _ => True : Bool → Prop) (fun (a : Bool) => instDecidableTrue) (Bool.false) (({true, false} : Multiset Bool) : Multiset Bool)) (by
  decide +kernel)

-- Multiset.find?_some, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.find?_some.h6 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] {a : α} {s : Multiset α}
        {hp : {x : α | x ∈ s ∧ p x}.Subsingleton}, p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) ((0 : Multiset Nat) : Multiset ℕ) (by
  simp)) (by
  decide +kernel)

-- Finset.Nontrivial.image_of_injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nontrivial.image_of_injOn.h5 : ¬∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s : Finset α}, Set.InjOn f ↑s → (Finset.image f s).Nontrivial := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Finset.disjoint_of_erase_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_of_erase_left.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) (@Finset.erase α inst s a) t →
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

-- Finset.disjoint_of_erase_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_of_erase_left.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        a ∉ t → @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.sdiff_insert_insert_of_mem_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_insert_insert_of_mem_of_notMem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {x : α}, x ∉ t → Insert.insert x (s \ Insert.insert x t) = s \ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (by
  decide)) (by
  decide +kernel)

-- Ordnode.valid'_singleton, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.valid'_singleton.h5 : ¬∀ {α : Type} [inst : Preorder α] {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.nil.Bounded (↑x) o₂ → Ordnode.Valid' o₁ {x} o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (0) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.valid'_singleton, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.valid'_singleton.h6 : ¬∀ {α : Type} [inst : Preorder α] {x : α} {o₁ : WithBot α} {o₂ : WithTop α},
        Ordnode.nil.Bounded o₁ ↑x → Ordnode.Valid' o₁ {x} o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (1) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Sym.erase_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.erase_mk.h4 : ¬∀ {α : Type} {n : ℕ} [inst : DecidableEq α] (m : Multiset α), ∀ a ∈ m, m.card = n + 1 := fun hc_h => absurd (@hc_h (ℕ) (1) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Sym.erase_mk, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.erase_mk.h6 : ¬∀ {α : Type} {n : ℕ} [inst : DecidableEq α] (m : Multiset α), m.card = n + 1 → ∀ (a : α), a ∈ m := fun hc_h => absurd (@hc_h (ℕ) (0) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) (by
  decide) (1)) (by
  decide +kernel)

-- Multiset.fold_cons_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_cons_left.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b a : α) (s : Multiset α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_cons_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_cons_left.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b a : α) (s : Multiset α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) ((0 : Multiset Bool) : Multiset Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.disjoint_of_subset_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_of_subset_left.h4 : Not
      (∀ {α : Type} {s t u : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) u t →
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

-- Disjoint.notMem_of_mem_right_finset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_right_finset.h3 : Not
      (∀ {α : Type} {s t : Finset α} ⦃a : α⦄,
        @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) t a → a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Disjoint.notMem_of_mem_right_finset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_right_finset.h5 : Not
      (∀ {α : Type} {s t : Finset α},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t → ∀ ⦃a : α⦄, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Computation.get_bind, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.get_bind.h4 : ¬∀ {α β : Type} (s : Computation α) (f : α → Computation β), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Inhabited.default) (fun (a : ℕ) => Inhabited.default)) (by
  nofun)

-- Computation.get_bind, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.get_bind.h5 : ¬∀ {α β : Type} (s : Computation α) (f : α → Computation β) [inst : s.Terminates], (f s.get).Terminates := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Computation.pure 0 : Computation ℕ) (fun (a : ℕ) => Inhabited.default) _) (by
  nofun)

-- Computation.Results.length, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.Results.length.h5 : ¬∀ {α : Type} {s : Computation α} {a : α} {n : ℕ} [_T : s.Terminates], s.length = n := fun hc_h => absurd (@hc_h (ℕ) (Computation.pure 0 : Computation ℕ) (0) (1) _) (by
  decide +kernel)

-- Multiset.fold_eq_foldl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_eq_foldl.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b : α) (s : Multiset α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_eq_foldl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_eq_foldl.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b : α) (s : Multiset α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) ((0 : Multiset Bool) : Multiset Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.Nodup.product, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.product.h4 : ¬∀ {α β : Type} {s : Multiset α} {t : Multiset β}, t.Nodup → (s ×ˢ t).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Multiset.Nodup.product, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.product.h5 : ¬∀ {α β : Type} {s : Multiset α} {t : Multiset β}, s.Nodup → (s ×ˢ t).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0} : Multiset Nat) : Multiset ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Cycle.next_reverse_eq_prev, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.next_reverse_eq_prev.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Cycle α), s.Nodup → ∀ (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (∅) (by
  decide) (0)) (by
  decide +kernel)

-- Cycle.prev_reverse_eq_next, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.prev_reverse_eq_next.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (s : Cycle α), s.Nodup → ∀ (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (∅) (by
  decide) (0)) (by
  decide +kernel)

-- Finset.orderEmbOfFin_last, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.orderEmbOfFin_last.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {k : ℕ}, 0 < k → s.card = k := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.orderEmbOfFin_last, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.orderEmbOfFin_last.h5 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {k : ℕ}, s.card = k → 0 < k := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) _ rfl) (by
  decide +kernel)

-- Computation.mem_unique, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.mem_unique.h5 : ¬∀ {α : Type} {s : Computation α} {a b : α}, a ∈ s → a = b := fun hc_h => absurd (@hc_h (ℕ) (Computation.pure 0 : Computation ℕ) (0) (1) (by
  simp)) (by
  decide +kernel)

-- Finset.max'_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_subset.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {s t : Finset α}, s ⊆ t → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Finset.max'_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_subset.h5 : Not
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

-- Multiset.mem_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_of_le.h4 : ¬∀ {α : Type} {s t : Multiset α} {a : α}, a ∈ s → a ∈ t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Multiset.mem_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_of_le.h5 : ¬∀ {α : Type} {s t : Multiset α} {a : α}, s ≤ t → a ∈ t := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Finset.Subset.trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Subset.trans.h4 : Not
      (∀ {α : Type} {s₁ s₂ s₃ : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s₂
            s₃ →
          @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            s₁ s₃) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.Superset.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Superset.trans.h5 : Not
      (∀ {α : Type} {s₁ s₂ s₃ : Finset α},
        @GE.ge (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s₁
            s₂ →
          @GE.ge (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
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

-- ENat.exists_le_of_sum_le, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.ENat.exists_le_of_sum_le.h2.inst : Not
      (∃ (i : Nat),
        And
          (@Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
            (@Finset.mk Nat
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
                  (@Eq.refl Bool Bool.true))))
            i)
          (@LE.le ENat instLEENat ((fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) i)
            ((fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) i))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.ENat.exists_le_of_sum_le.h2.prem0 : @LE.le ENat instLEENat
      (∑
        i ∈
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
                (@Eq.refl Bool Bool.true))),
        (fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) i)
      (∑
        i ∈
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
                (@Eq.refl Bool Bool.true))),
        (fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) i) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.ENat.exists_le_of_sum_le.h2 : Not
      (∀ {α : Type} {s : Finset α} {f g : α → ENat},
        @LE.le ENat instLEENat (∑ i ∈ s, f i) (∑ i ∈ s, g i) →
          ∃ (i : α),
            And (@Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i)
              (@LE.le ENat instLEENat (f i) (g i))) := fun hc_h => HypCheckProof.ENat.exists_le_of_sum_le.h2.inst (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) (fun (a : Nat) => @OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) HypCheckProof.ENat.exists_le_of_sum_le.h2.prem0)

-- Finset.powersetCard_biUnion, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.powersetCard_biUnion.h4 : Not
      (∀ {α : Type} {s : Finset α} [inst : DecidableEq α] {r : Nat},
        @LE.le Nat instLENat r (@Finset.card α s) →
          @Eq (Finset α) (@Finset.biUnion (Finset α) α inst (@Finset.powersetCard α r s) (@id (Finset α))) s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Finset.powersetCard_biUnion, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.powersetCard_biUnion.h5 : Not
      (∀ {α : Type} {s : Finset α} [inst : DecidableEq α] {r : Nat},
        @Ne Nat r (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Eq (Finset α) (@Finset.biUnion (Finset α) α inst (@Finset.powersetCard α r s) (@id (Finset α))) s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Multiset.count_eq_one_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_eq_one_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, a ∈ s → Multiset.count a s = 1 := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0, 0} : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Multiset.count_eq_one_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_eq_one_of_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, s.Nodup → Multiset.count a s = 1 := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Multiset.Nodup.filterMap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.filterMap.h4 : ¬∀ {α β : Type} {s : Multiset α} (f : α → Option β), s.Nodup → (Multiset.filterMap f s).Nodup := fun hc_h => absurd (@hc_h (Bool) (ℕ) (({true, false} : Multiset Bool) : Multiset Bool) (fun (a : Bool) => Option.some 0) (by
  decide)) (by
  decide +kernel)

-- Multiset.Nodup.filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.filterMap.h5 : ¬∀ {α β : Type} {s : Multiset α} (f : α → Option β),
        (∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a') → (Multiset.filterMap f s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) (some : ℕ → Option ℕ) (by
  simp)) (by
  decide +kernel)

-- Disjoint.notMem_of_mem_left_multiset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_left_multiset.h3 : ¬∀ {α : Type} {s t : Multiset α} {a : α}, a ∈ s → a ∉ t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) (0) (by
  decide)) (by
  decide +kernel)

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

-- Finset.cons_subset_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_subset_cons.h5 : Not (∀ {α : Type} {s t : Finset α} {a : α} {hs : a ∉ s}, a ∉ t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.cons_swap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_swap.h4 : Not (∀ {α : Type} {s : Finset α} {a : α} {b : α}, b ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.cons_swap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_swap.h5 : ¬∀ {α : Type} {s : Finset α} {a b : α} (hb : b ∉ s), a ∉ Finset.cons b s hb := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (0) hc_k0) (by
  decide +kernel)

-- Infinite.exists_superset_card_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Infinite.exists_superset_card_eq.h4 : Not
      (∀ {α : Type} [inst : Infinite α] (s : Finset α) (n : Nat),
        ∃ (t : Finset α),
          And
            (@LE.le (Finset α)
              (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s t)
            (@Eq Nat (@Finset.card α t) n)) := fun hc_h => absurd (@hc_h (Nat) _ (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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
  (simp <;> decide))

-- Computation.mem_of_get_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.mem_of_get_eq.h2 : ¬∀ {α : Type} (s : Computation α) {a : α}, s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- Computation.mem_of_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.mem_of_get_eq.h4 : ¬∀ {α : Type} (s : Computation α) [h : s.Terminates] {a : α}, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Computation.pure 0 : Computation ℕ) _ (1)) (by
  simp)

-- Computation.results_of_terminates', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.results_of_terminates'.h4 : ¬∀ {α : Type} (s : Computation α) [T : s.Terminates] {a : α}, s.Results a s.length := fun hc_h => absurd (@hc_h (ℕ) (Computation.pure 0 : Computation ℕ) _ (1)) (by
  nofun)

-- Finset.sup_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_cons.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α]
        [inst : @OrderBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))]
        {s : Finset β} {f : β → α} {b : β}, b ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (Nat.instOrderBot) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Stream'.Seq.coinduction, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.coinduction.h3 : ¬∀ {α : Type} {s₁ s₂ : Stream'.Seq α},
        (∀ (β : Type) (fr : Stream'.Seq α → β), fr s₁ = fr s₂ → fr s₁.tail = fr s₂.tail) → s₁ = s₂ := fun hc_h => absurd (@hc_h (ℕ) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (by
  simp)) (by
  simp)

-- Stream'.Seq.coinduction, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.coinduction.h4 : ¬∀ {α : Type} {s₁ s₂ : Stream'.Seq α}, s₁.head = s₂.head → s₁ = s₂ := fun hc_h => absurd (@hc_h (ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (Stream'.Seq.cons 0 (Stream'.Seq.cons 1 Stream'.Seq.nil) : Stream'.Seq ℕ) (by
  decide)) (by
  simp)

-- Finset.lt_inf_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.lt_inf_iff.h7 : ¬∀ {α ι : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] {s : Finset ι} {f : ι → α} {a : α},
        a < s.inf f ↔ ∀ b ∈ s, a < f b := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.true)) (by
  decide +kernel)

-- Finset.sup_mono_fun, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_mono_fun.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeSup α]
        [inst_1 : @OrderBot α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))]
        {s : Finset β} {f g : β → α},
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeSup.toPartialOrder α inst)))
          (@Finset.sup α β inst inst_1 s f) (@Finset.sup α β inst inst_1 s g)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (Nat.instOrderBot) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat)) (by
  decide +kernel)

-- Finset.inf_le_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_le_iff.h7 : ¬∀ {α ι : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] {s : Finset ι} {f : ι → α} {a : α},
        s.inf f ≤ a ↔ ∃ b ∈ s, f b ≤ a := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.true)) (by
  decide +kernel)

-- Finset.sup'_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_apply.h5 : ¬∀ {α β : Type} {C : β → Type} [inst : (b : β) → SemilatticeSup (C b)] {s : Finset α} (f : α → (b : β) → C b) (b : β),
        s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => ℕ) (fun (b : ℕ) => Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun a b => a - b : ℕ → ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.inf_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_mono.h7 : Not
      (∀ {α β : Type} [inst : SemilatticeInf α]
        [inst_1 : @OrderTop α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))]
        {s₁ s₂ : Finset β} {f : β → α},
        @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@SemilatticeInf.toPartialOrder α inst)))
          (@Finset.inf α β inst inst_1 s₂ f) (@Finset.inf α β inst inst_1 s₁ f)) := fun hc_h => absurd (@hc_h (Bool) (Nat) (@Lattice.toSemilatticeInf Bool
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
          (@Eq.refl Bool Bool.true)))) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Finset.sup'_product_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_product_left.h6 : ¬∀ {α β γ : Type} [inst : SemilatticeSup α] {s : Finset β} {t : Finset γ} (f : β × γ → α), (s ×ˢ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ × ℕ) => 0)) (by
  decide +kernel)

-- Finset.card_image₂_singleton_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_image₂_singleton_right.h7 : ¬∀ {α β γ : Type} [inst : DecidableEq γ] {f : α → β → γ} (s : Finset α) {b : β}, (Finset.image₂ f s {b}).card = s.card := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (instDecidableEqNat) (fun (a : Bool) (n : ℕ) => n + 1) ({ val := {Bool.true, Bool.false}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (0)) (by
  decide +kernel)

-- Finset.biUnion_filter_eq_of_maps_to, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.biUnion_filter_eq_of_maps_to.h7 : Not
      (∀ {α β : Type} [inst : DecidableEq β] [inst_1 : DecidableEq α] {s : Finset α} {t : Finset β} {f : α → β},
        @Eq (Finset α) (@Finset.biUnion β α inst_1 t fun (a : β) => {c ∈ s | @Eq β (f c) a}) s) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Multiset.eq_of_le_of_card_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_of_le_of_card_le.h3 : ¬∀ {α : Type} {s t : Multiset α}, t.card ≤ s.card → s = t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Multiset.eq_of_le_of_card_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_of_le_of_card_le.h4 : ¬∀ {α : Type} {s t : Multiset α}, s ≤ t → s = t := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  decide +kernel)

-- Finset.Nonempty.of_image₂_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_image₂_left.h7 : ¬∀ {α β γ : Type} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (fun a b => a - b : ℕ → ℕ → ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.Subset.antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Subset.antisymm.h3 : Not
      (∀ {α : Type} {s₁ s₂ : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))) s₂
            s₁ →
          @Eq (Finset α) s₁ s₂) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.Nonempty.eq_univ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.eq_univ.h3 : ¬∀ {α : Type} {s : Finset α} [inst : Fintype α], s.Nonempty → s = Finset.univ := fun hc_h => absurd (@hc_h (Bool) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (Bool.fintype) (by
  decide)) (by
  decide +kernel)

-- Finset.Nonempty.eq_univ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.eq_univ.h4 : ¬∀ {α : Type} {s : Finset α} [inst : Fintype α] [inst_1 : Subsingleton α], s = Finset.univ := fun hc_h => absurd (@hc_h (Unit) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Unit }) (PUnit.fintype) _) (by
  decide +kernel)

-- Finsupp.mem_range_of_mapDomain_ne_zero, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mem_range_of_mapDomain_ne_zero.h7 : ¬∀ {α β M : Type} [inst : AddCommMonoid M] {f : α → β} {x : α →₀ M} {b : β}, b ∈ Set.range f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instAddCommMonoid) (fun n => n + 1 : ℕ → ℕ) (0) (0)) (by
  simp)

-- Finset.filter_union_filter_of_codisjoint, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_union_filter_of_codisjoint.h7 : Not
      (∀ {α : Type} (p q : α → Prop) [inst : @DecidablePred α p] [inst_1 : @DecidablePred α q] [inst_2 : DecidableEq α]
        (s : Finset α),
        @Eq (Finset α)
          (@Max.max (Finset α) (@Finset.instMax α inst_2) (@Finset.filter α p inst s) (@Finset.filter α q inst_1 s)) s) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun n => n = 0 : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (instDecidableEqNat) (@Finset.mk Nat
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

-- Multiset.map_erase_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_erase_of_mem.h7 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] (f : α → β) (s : Multiset α) {x : α},
        Multiset.map f (s.erase x) = (Multiset.map f s).erase (f x) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (fun _ => 0 : ℕ → ℕ) (({0} : Multiset Nat) : Multiset ℕ) (1)) (by
  decide +kernel)

-- Multiset.Nodup.cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.cons.h3 : ¬∀ {α : Type} {s : Multiset α} {a : α}, s.Nodup → (a ::ₘ s).Nodup := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Multiset.Nodup.cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.cons.h4 : ¬∀ {α : Type} {s : Multiset α} {a : α}, a ∉ s → (a ::ₘ s).Nodup := fun hc_h => absurd (@hc_h (Bool) (({true, true} : Multiset Bool) : Multiset Bool) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Finsupp.support_mapRange, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_mapRange.h6 : ¬∀ {α M N : Type} [inst : Zero M] [inst_1 : Zero N] {f : M → N} {g : α →₀ M}, f 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  decide +kernel)

-- Cycle.Chain.eq_nil_of_wellFounded, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.eq_nil_of_wellFounded.h3 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α}, Cycle.Chain r s → s = Cycle.nil := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) (by
  simp)) (by
  decide +kernel)

-- Cycle.Chain.eq_nil_of_wellFounded, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.eq_nil_of_wellFounded.h4 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : WellFounded r], s = Cycle.nil := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) _) (by
  decide +kernel)

-- Cycle.Chain.eq_nil_of_well_founded, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.eq_nil_of_well_founded.h3 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α}, Cycle.Chain r s → s = Cycle.nil := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) (by
  simp)) (by
  decide +kernel)

-- Cycle.Chain.eq_nil_of_well_founded, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.Chain.eq_nil_of_well_founded.h4 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α} [inst : WellFounded r], s = Cycle.nil := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ) _) (by
  decide +kernel)

-- Multiset.count_map_eq_count', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_map_eq_count'.h6 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] (f : α → β) (s : Multiset α) (x : α),
        Multiset.count (f x) (Multiset.map f s) = Multiset.count x s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (fun _ => 0 : ℕ → ℕ) (({0} : Multiset Nat) : Multiset ℕ) (1)) (by
  decide +kernel)

-- Multiset.Nodup.add_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.add_iff.h4 : ¬∀ {α : Type} {s t : Multiset α}, s.Nodup → ((s + t).Nodup ↔ Disjoint s t) := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0, 0} : Multiset Nat) : Multiset ℕ) (by
  decide)) (by
  simp)

-- Finset.image_subset_sups_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_subset_sups_right.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s t : Finset α} {a : α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Finset.image α α inst (fun (x : α) => @Max.max α (@SemilatticeSup.toMax α inst_1) a x) t)
          (@HasSups.sups (Finset α) (@Finset.hasSups α inst inst_1) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.image_subset_diffs_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_subset_diffs_left.h6 : ¬∀ {α : Type} [inst : DecidableEq α] [inst_1 : GeneralizedBooleanAlgebra α] {s t : Finset α} {b : α},
        Finset.image (fun (x : α) => x \ b) s ⊆ s.diffs t := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (BooleanAlgebra.toGeneralizedBooleanAlgebra) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (Bool.false)) (by
  decide +kernel)

-- Finset.image₂_left_identity, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image₂_left_identity.h5 : Not
      (∀ {α γ : Type} [inst : DecidableEq γ] {f : α → γ → γ} {a : α} (t : Finset γ),
        @Eq (Finset γ) (@Finset.image₂ α γ γ inst f (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a) t) t) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun a b => a - b : Nat → Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
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

-- Finset.sup_mem_of_nonempty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup_mem_of_nonempty.h6 : ¬∀ {α ι : Type} [inst : LinearOrder α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α}, s.sup f ∈ f '' ↑s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Finset.inf'_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_le_iff.h4 : ¬∀ {α ι : Type} [inst : LinearOrder α] {s : Finset ι} {f : ι → α} {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.inf_sdiff_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_sdiff_left.h4 : ¬∀ {α ι : Type} [inst : BooleanAlgebra α] {s : Finset ι} (f : ι → α) (a : α),
        (s.inf fun (b : ι) => a \ f b) = a \ s.sup f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false)) (by
  decide +kernel)

-- Finsupp.weight_sub_single_add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.weight_sub_single_add.h6 : ¬∀ {σ M : Type} {w : σ → M} [inst : AddCommMonoid M] {f : σ →₀ ℕ} {i : σ},
        (Finsupp.weight w) (f - fun₀ | i => 1) + w i = (Finsupp.weight w) f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (Nat.instAddCommMonoid) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ) (0)) (by
  decide +kernel)

-- Finset.image_eq_iff_eq_preimage, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_eq_iff_eq_preimage.h6 : ¬∀ {α β : Type} [inst : DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β}, Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun _ => 0 : Bool → ℕ)) (by
  nofun)

-- Finset.sup'_inf_distrib_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_inf_distrib_left.h4 : ¬∀ {α ι : Type} [inst : DistribLattice α] {s : Finset ι} (f : ι → α) (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDistribLatticeNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.inf'_sup_distrib_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_sup_distrib_left.h4 : ¬∀ {α ι : Type} [inst : DistribLattice α] {s : Finset ι} (f : ι → α) (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDistribLatticeNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.exists_mem_eq_inf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_mem_eq_inf.h5 : ¬∀ {α ι : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] (s : Finset ι) (f : ι → α), ∃ i ∈ s, s.inf f = f i := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- Finset.coe_sup_of_nonempty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.coe_sup_of_nonempty.h5 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} (f : β → α),
        ↑(s.sup f) = s.sup (WithBot.some ∘ f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.sup'_eq_sup, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sup'_eq_sup.h5 : ¬∀ {α β : Type} [inst : SemilatticeSup α] [inst : OrderBot α] {s : Finset β} (f : β → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.image_subset_image, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_subset_image.h6 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s₁ s₂ : Finset α},
        @LE.le (Finset β) (@Preorder.toLE (Finset β) (@PartialOrder.toPreorder (Finset β) (@Finset.instPartialOrder β)))
          (@Finset.image α β inst f s₁) (@Finset.image α β inst f s₂)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun n => n + 1 : Nat → Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Set.SurjOn.subset_finsetImage, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.subset_finsetImage.h6 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β},
        @LE.le (Finset β) (@Preorder.toLE (Finset β) (@PartialOrder.toPreorder (Finset β) (@Finset.instPartialOrder β))) t
          (@Finset.image α β inst f s)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun n => n + 1 : Nat → Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.monotone_filter_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.monotone_filter_right.h6 : Not
      (∀ {α : Type} (s : Finset α) ⦃p q : α → Prop⦄ [inst : @DecidablePred α p] [inst_1 : @DecidablePred α q],
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Finset.filter α p inst s) (@Finset.filter α q inst_1 s)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun n => n = 0 : Nat → Prop) (fun _ => False : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (a : Nat) => instDecidableFalse)) (by
  decide +kernel)

-- Multiset.filter_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.filter_congr.h6 : ¬∀ {α : Type} {p q : α → Prop} [inst : DecidablePred p] [inst_1 : DecidablePred q] {s : Multiset α},
        Multiset.filter p s = Multiset.filter q s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableFalse) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finsupp.support_onFinset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_onFinset.h6 : ¬∀ {α M : Type} [inst : Zero M] [inst_1 : DecidableEq M] {s : Finset α} {f : α → M} (a : α), f a ≠ 0 → a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Finset.disjiUnion_filter_eq_of_maps_to, hypothesis 6: necessary
/- FAILED: 3:86: expected token | 6:44: expected token | 3:158: `grind` failed
case grind
α β : Type
inst : DecidableEq β
s : Finset α
t : Finset β
f : α → β
h : ¬(↑t).PairwiseDisjoint fun a => {x ∈ s | f x = a}
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬(↑t).PairwiseDisjoint fun a => {x ∈ s | f x = a}
    [prop] Function.Injective SetLike.coe
  [eqc] True propositions
    [prop] Nonempty (Finset β)
    [prop] Function.Injective SetLike.coe
  [eqc] False propositions
    [prop] (↑t).PairwiseDisjoint fun a => {x ∈ s | f x = a}
  [eq | 4:192: `grind` failed
case grind
α β : Type
inst : DecidableEq β
s : Finset α
t : Finset β
f : α → β
h : ¬(↑t).PairwiseDisjoint fun a => {x ∈ s | f x = a}
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬(↑t).PairwiseDisjoint fun a => {x ∈ s | f x = a}
    [prop] Function.Injective SetLike.coe
  [eqc] True propositions
    [prop] Nonempty (Finset β)
    [prop] Function.Injective SetLike.coe
  [eqc] False propositions
    [prop] (↑t).PairwiseDisjoint fun a => {x ∈ s | f x = a}
  [eq | 6:40: expected token | 49:42: expected token | 3:274: (deterministic) timeout at `elaborator`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 19:75: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjiUnion_filter_eq_of_maps_to.h6 : ¬∀ {α β : Type} [inst : DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β},
        t.disjiUnion (fun (a : β) => {x ∈ s | f x = a}) Finset.pairwiseDisjoint_fibers✝ = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) ({ val := {0}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)
-/

-- Multiset.inter_add_sub_of_add_eq_add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.inter_add_sub_of_add_eq_add.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {M N P Q : Multiset α}, N ∩ Q + (P - M) = N := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.cast_card_erase_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cast_card_erase_of_mem.h6 : Not
      (∀ {α R : Type} {s : Finset α} {a : α} [inst : DecidableEq α] [inst_1 : AddGroupWithOne R],
        @Eq R
          (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst_1))
            (@Finset.card α (@Finset.erase α inst s a)))
          (@HSub.hSub R R R
            (@instHSub R (@SubNegMonoid.toSub R (@AddGroup.toSubNegMonoid R (@AddGroupWithOne.toAddGroup R inst_1))))
            (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst_1)) (@Finset.card α s))
            (@OfNat.ofNat R (nat_lit 1)
              (@One.toOfNat1 R (@AddMonoidWithOne.toOne R (@AddGroupWithOne.toAddMonoidWithOne R inst_1)))))) := fun hc_h => absurd (@hc_h (Nat) (Bool) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instDecidableEqNat) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))) (by
  decide +kernel)

-- Function.Injective.mem_finset_image, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.mem_finset_image.h6 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s : Finset α} {a : α},
        Iff
          (@Membership.mem β (Finset β) (@SetLike.instMembership (Finset β) β (@Finset.instSetLike β))
            (@Finset.image α β inst f s) (f a))
          (@Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s a)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun _ => 0 : Nat → Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Set.MapsTo.finsetImage_subset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.finsetImage_subset.h6 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β},
        @LE.le (Finset β) (@Preorder.toLE (Finset β) (@PartialOrder.toPreorder (Finset β) (@Finset.instPartialOrder β)))
          (@Finset.image α β inst f s) t) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun n => n + 1 : Nat → Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.inf_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_of_mem.h6 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α) {b : β}, ∃ (a : α), s.inf (WithTop.some ∘ f) = ↑a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  simp)

-- Set.SurjOn.finsetImage_eq_of_mapsTo, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.finsetImage_eq_of_mapsTo.h6 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β},
        And
          (@Set.SurjOn α β f (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
            (@SetLike.coe (Finset β) β (@Finset.instSetLike β) t))
          (@Set.MapsTo α β f (@SetLike.coe (Finset α) α (@Finset.instSetLike α) s)
            (@SetLike.coe (Finset β) β (@Finset.instSetLike β) t))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun n => n + 1 : Nat → Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.infs_subset_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.infs_subset_left.h6 : Not
      (∀ {α : Type} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s t₁ t₂ : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@HasInfs.infs (Finset α) (@Finset.hasInfs α inst inst_1) s t₁)
          (@HasInfs.infs (Finset α) (@Finset.hasInfs α inst inst_1) s t₂)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.lt_inf'_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.lt_inf'_iff.h4 : ¬∀ {α ι : Type} [inst : LinearOrder α] {s : Finset ι} {f : ι → α} {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.inf_const, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf_const.h5 : ¬∀ {α β : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {s : Finset β} (c : α), (s.inf fun (x : β) => c) = c := fun hc_h => absurd (@hc_h (Bool) (ℕ) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Bool.false)) (by
  decide +kernel)

-- Finset.mem_image_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_image_of_mem.h6 : ¬∀ {α β : Type} [inst : DecidableEq β] {s : Finset α} (f : α → β) {a : α}, f a ∈ Finset.image f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Finset.inf'_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.inf'_lt_iff.h4 : ¬∀ {α ι : Type} [inst : LinearOrder α] {s : Finset ι} {f : ι → α} {a : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Multiset.sub_le_sub_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sub_le_sub_right.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s t u : Multiset α}, s - u ≤ t - u := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.mem_sub_of_nodup, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_sub_of_nodup.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s t : Multiset α}, a ∈ s - t ↔ a ∈ s ∧ a ∉ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0, 0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.mem_of_mem_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_of_mem_erase.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {b : α} {s : Multiset α}, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.erase_add_left_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.erase_add_left_pos.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α} (t : Multiset α), (s + t).erase a = s.erase a + t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.count_erase_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_erase_of_ne.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} (s : Multiset α), Multiset.count a (s.erase b) = Multiset.count a s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.erase_cons_tail, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.erase_cons_tail.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} (s : Multiset α), (b ::ₘ s).erase a = b ::ₘ s.erase a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
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

-- Stream'.Seq.coinduction2, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.coinduction2.h5 : ¬∀ {α β : Type} (s : Stream'.Seq α) (f g : Stream'.Seq α → Stream'.Seq β), f s = g s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Inhabited.default) (fun (a : Stream'.Seq ℕ) => Stream'.Seq.nil) (fun (a : Stream'.Seq ℕ) => Stream'.Seq.cons 0 Stream'.Seq.nil)) (by
  simp)

-- Stream'.Seq.Pairwise_cons_cons_head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.Pairwise_cons_cons_head.h5 : ¬∀ {α : Type} {R : α → α → Prop} {hd tl_hd : α} {tl_tl : Stream'.Seq α}, R hd tl_hd := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (Inhabited.default)) (by
  decide +kernel)

-- Multiset.foldl_swap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldl_swap.h3 : ¬∀ {α β : Type} (f : β → α → β) (b : β) (s : Multiset α), RightCommutative f := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (Bool.false) ((0 : Multiset Nat) : Multiset ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.right_comm (Bool.false : Bool) (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.card_preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_preimage.h4 : Not
      (∀ {α β : Type} (s : Finset β) (f : α → β)
        [inst : @DecidablePred β fun (x : β) => @Membership.mem β (Set β) (@Set.instMembership β) (@Set.range β α f) x],
        @Set.InjOn α β f (@Set.preimage α β f (@SetLike.coe (Finset β) β (@Finset.instSetLike β) s))) := fun hc_h => absurd (@hc_h (Bool) (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (fun _ => 0 : Bool → Nat) (fun (a : Nat) =>
      @Fintype.decidableMemRangeFintype Bool Nat Bool.fintype instDecidableEqNat
        (fun (x : Bool) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a)) (by
  simp)

-- Multiset.disjoint_powersetCard_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.disjoint_powersetCard_of_ne.h3 : ¬∀ {α : Type} {m n : ℕ} (s t : Multiset α), Disjoint (Multiset.powersetCard m s) (Multiset.powersetCard n t) := fun hc_h => absurd (@hc_h (ℕ) (0) (0) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Finset.disjoint_powersetCard_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_powersetCard_of_ne.h3 : ¬∀ {α : Type} {m n : ℕ} (s t : Finset α), Disjoint (Finset.powersetCard m s) (Finset.powersetCard n t) := fun hc_h => absurd (@hc_h (ℕ) (0) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Multiset.filterMap_le_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.filterMap_le_filterMap.h5 : ¬∀ {α β : Type} (f : α → Option β) {s t : Multiset α}, Multiset.filterMap f s ≤ Multiset.filterMap f t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (some : ℕ → Option ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.of_mem_filter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.of_mem_filter.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α} {s : Multiset α}, p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.filter_le_filter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.filter_le_filter.h5 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] {s t : Multiset α}, Multiset.filter p s ≤ Multiset.filter p t := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.filter_cons_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.filter_cons_of_pos.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α} (s : Multiset α),
        Multiset.filter p (a ::ₘ s) = a ::ₘ Multiset.filter p s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.filter_cons_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.filter_cons_of_neg.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α} (s : Multiset α),
        Multiset.filter p (a ::ₘ s) = Multiset.filter p s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.filterMap_cons_none, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.filterMap_cons_none.h5 : ¬∀ {α β : Type} {f : α → Option β} (a : α) (s : Multiset α), Multiset.filterMap f (a ::ₘ s) = Multiset.filterMap f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (some : ℕ → Option ℕ) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.ne_insert_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ne_insert_of_notMem.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] (s t : Finset α) {a : α},
        @Ne (Finset α) s (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.insert_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_inj.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a b : α},
        Iff
          (@Eq (Finset α) (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s)
            (@Insert.insert α (Finset α) (@Finset.instInsert α inst) b s))
          (@Eq α a b)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Finset.consPiProd_fst, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.consPiProd_fst.h4 : Not (∀ {α : Type} {s : Finset α} {a : α} (f : α → Type), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a : Nat) => Nat)) (by
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

-- Finset.mem_of_mem_inter_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_inter_left.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s₁ : Finset α} {s₂ : Finset α}, a ∈ s₁ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.union_subset_union_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_subset_union_left.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s₁ s₂ t : Finset α},
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@Max.max (Finset α) (@Finset.instMax α inst) s₁ t) (@Max.max (Finset α) (@Finset.instMax α inst) s₂ t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.insert_inter_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_inter_of_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s₁ s₂ : Finset α} {a : α}, Insert.insert a s₁ ∩ s₂ = Insert.insert a (s₁ ∩ s₂) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.notMem_sdiff_of_mem_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_sdiff_of_mem_right.h5 : Not
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

-- Finset.sdiff_subset_sdiff_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_subset_sdiff_left.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} (u : Finset α),
        @LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s u) (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t u)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.insert_sdiff_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.insert_sdiff_of_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {t : Finset α} (s : Finset α) {x : α}, Insert.insert x s \ t = s \ t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.mem_of_mem_filter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_mem_filter.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.image_const, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_const.h4 : ¬∀ {α β : Type} [inst : DecidableEq β] {s : Finset α} (b : β), Finset.image (fun (x : α) => b) s = {b} := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.Nonempty.of_diffs_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_diffs_left.h5 : ¬∀ {α : Type} [inst : DecidableEq α] [inst : GeneralizedBooleanAlgebra α] {s : Finset α} {t : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (BooleanAlgebra.toGeneralizedBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.image_val_of_injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_val_of_injOn.h5 : Not
      (∀ {α β : Type} [inst : DecidableEq β] {f : α → β} {s : Finset α},
        @Eq (Multiset β) (@Finset.val β (@Finset.image α β inst f s)) (@Multiset.map α β f (@Finset.val α s))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (fun _ => 0 : Nat → Nat) (@Finset.mk Nat
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

-- Finset.disjUnion_product, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjUnion_product.h5 : Not
      (∀ {α β : Type} {s s' : Finset α} {t : Finset β},
        @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s s') := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.Nonempty.of_sups_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_sups_right.h5 : ¬∀ {α : Type} [inst : DecidableEq α] [inst : SemilatticeSup α] {s : Finset α} {t : Finset α}, t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.mem_filterMap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_filterMap.h4 : ¬∀ {α β : Type} (f : α → Option β) {s : Finset α} {b : β} (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a' := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) => Option.some 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (0)) (by
  decide +kernel)

-- Finset.Nonempty.of_diffs_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.of_diffs_right.h5 : ¬∀ {α : Type} [inst : DecidableEq α] [inst : GeneralizedBooleanAlgebra α] {s : Finset α} {t : Finset α}, t.Nonempty := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (BooleanAlgebra.toGeneralizedBooleanAlgebra) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Multiset.inf_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.inf_le.h5 : ¬∀ {α : Type} [inst : SemilatticeInf α] [inst_1 : OrderTop α] {s : Multiset α} {a : α}, s.inf ≤ a := fun hc_h => absurd (@hc_h (Bool) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ((0 : Multiset Bool) : Multiset Bool) (Bool.false)) (by
  decide +kernel)

-- Multiset.sup_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sup_mono.h5 : ¬∀ {α : Type} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s₁ s₂ : Multiset α}, s₁.sup ≤ s₂.sup := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLattice.toSemilatticeSup) (Nat.instOrderBot) (({1} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finsupp.optionElim_ne_zero_of_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.optionElim_ne_zero_of_right.h5 : ¬∀ {α M : Type} [inst : Zero M] (y : M) (f : α →₀ M), Finsupp.optionElim y f ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) ((0 : Nat →₀ Nat) : ℕ →₀ ℕ)) (by
  simp)

-- Finset.map_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.map_cons.h5 : ¬∀ {α β : Type} (f : α ↪ β) (a : α) (s : Finset α), a ∉ s := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (Bool.false) ({ val := {Bool.true, Bool.false}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.exists_mem_eq_inf', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_mem_eq_inf'.h4 : ¬∀ {α ι : Type} [inst : LinearOrder α] {s : Finset ι} (f : ι → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.choose_eq_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.choose_eq_iff.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Finset α) {a : α}, ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  simp)

-- Finset.erase_subset_iff_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.erase_subset_iff_of_mem.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        Iff
          (@LE.le (Finset α) (@Preorder.toLE (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α)))
            (@Finset.erase α inst s a) t)
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

-- Finset.disjoint_erase_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_erase_insert.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α} {a : α},
        Iff
          (@Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α)
            (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s) (@Finset.erase α inst t a))
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

-- Finset.union_erase_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_erase_of_mem.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α} (t : Finset α),
        @Eq (Finset α) (@Max.max (Finset α) (@Finset.instMax α inst) s (@Finset.erase α inst t a))
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

-- Ordnode.Bounded.to_nil, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.to_nil.h5 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α}, Ordnode.nil.Bounded o₁ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (0) (0)) (by
  nofun)

-- Finset.exists_ne_map_eq_of_card_image_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_ne_map_eq_of_card_image_lt.h5 : ¬∀ {α β : Type} {s : Finset α} [inst : DecidableEq β] {f : α → β}, ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.exists_subset_or_subset_of_two_mul_lt_card, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_subset_or_subset_of_two_mul_lt_card.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {X Y : Finset α} {n : ℕ}, ∃ (C : Finset α), n < C.card ∧ (C ⊆ X ∨ C ⊆ Y) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  simp)

-- Finset.coe_inf', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.coe_inf'.h4 : ¬∀ {α β : Type} [inst : SemilatticeInf α] {s : Finset β} (f : β → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.card_image_of_injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_image_of_injOn.h5 : Not
      (∀ {α β : Type} {s : Finset α} {f : α → β} [inst : DecidableEq β],
        @Eq Nat (@Finset.card β (@Finset.image α β inst f s)) (@Finset.card α s)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Finset.mk Nat
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

-- Ordnode.Bounded.weak_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.weak_left.h5 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α}, t.Bounded ⊥ o₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (0)) (by
  nofun)

-- Ordnode.Bounded.weak_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Bounded.weak_right.h5 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α}, t.Bounded o₁ ⊤ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (0)) (by
  nofun)

-- Finset.toDual_inf', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.toDual_inf'.h4 : ¬∀ {α ι : Type} [inst : SemilatticeInf α] {s : Finset ι} (f : ι → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.toDual_sup', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.toDual_sup'.h4 : ¬∀ {α ι : Type} [inst : SemilatticeSup α] {s : Finset ι} (f : ι → α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeSup) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Finset.dens_sdiff_add_dens_eq_dens, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.dens_sdiff_add_dens_eq_dens.h5 : ¬∀ {α : Type} [inst : Fintype α] {s t : Finset α} [inst_1 : DecidableEq α], (t \ s).dens + s.dens = t.dens := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (instDecidableEqBool)) (by
  decide +kernel)

-- Finset.dens_sdiff_comm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.dens_sdiff_comm.h5 : ¬∀ {α : Type} [inst : Fintype α] {s t : Finset α} [inst_1 : DecidableEq α], (s \ t).dens = (t \ s).dens := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (instDecidableEqBool)) (by
  decide +kernel)

-- Multiset.exists_min_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.exists_min_image.h5 : ¬∀ {α R : Type} [inst : LinearOrder R] (f : α → R) {s : Multiset α}, ∃ y ∈ s, ∀ z ∈ s, f y ≤ f z := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun n => n + 1 : ℕ → ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Multiset.exists_max_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.exists_max_image.h5 : ¬∀ {α R : Type} [inst : LinearOrder R] (f : α → R) {s : Multiset α}, ∃ y ∈ s, ∀ z ∈ s, f z ≤ f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun n => n + 1 : ℕ → ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Ordnode.Valid'.dual, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.dual.h5 : Not
      (∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},
        @Ordnode.Valid' (OrderDual α) (@OrderDual.instPreorder α inst) o₂ (@Ordnode.dual (OrderDual α) t) o₁) := fun hc_h => absurd (@hc_h (Nat) (Nat.instPreorder) (@Ordnode.nil Nat) (@OfNat.ofNat (WithBot Nat) (nat_lit 0)
      (@Zero.toOfNat0 (WithBot Nat) (@WithBot.zero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))) (@OfNat.ofNat (WithTop Nat) (nat_lit 0)
      (@Zero.toOfNat0 (WithTop Nat) (@WithTop.zero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))) (by
  nofun)

-- Ordnode.Valid'.valid, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.valid.h5 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α}, t.Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (0)) (by
  nofun)

-- Ordnode.Valid'.ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.ord.h5 : ¬∀ {α : Type} [inst : Preorder α] {lo : WithBot α} {t : Ordnode α} {hi : WithTop α}, t.Bounded lo hi := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (Ordnode.nil) (0)) (by
  nofun)

-- Multiset.card_eq_card_of_rel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.card_eq_card_of_rel.h5 : ¬∀ {α β : Type} {r : α → β → Prop} {s : Multiset α} {t : Multiset β}, s.card = t.card := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.countP_le_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.countP_le_of_le.h5 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] {s t : Multiset α}, Multiset.countP p s ≤ Multiset.countP p t := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.countP_cons_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.countP_cons_of_pos.h5 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α} (s : Multiset α),
        Multiset.countP p (a ::ₘ s) = Multiset.countP p s + 1 := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.count_cons_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_cons_of_ne.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} (s : Multiset α), Multiset.count a (b ::ₘ s) = Multiset.count a s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.image_orderEmbOfFin_univ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_orderEmbOfFin_univ.h4 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {k : ℕ}, s.card = k := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (1)) (by
  decide +kernel)

-- Finset.property_of_mem_map_subtype, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.property_of_mem_map_subtype.h4 : ¬∀ {α : Type} {p : α → Prop} (s : Finset { x : α // p x }) {a : α}, p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset { x : ℕ // (fun (n : ℕ) => n = 0) x } }) (1)) (by
  decide +kernel)

-- Finset.subtype_map_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.subtype_map_of_mem.h4 : Not
      (∀ {α : Type} {p : α → Prop} [inst : @DecidablePred α p] {s : Finset α},
        @Eq (Finset α) (@Finset.map (@Subtype α p) α (@Function.Embedding.subtype α p) (@Finset.subtype α p inst s)) s) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Finset.mk Nat
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

-- Finset.disjoint_disjUnion_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjoint_disjUnion_left.h4 : Not
      (∀ {α : Type} {s t : Finset α} {u : Finset α},
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
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Finset.choose_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.choose_mem.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : Finset α), ∃! a : α, a ∈ l ∧ p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.Nonempty.not_disjoint, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.not_disjoint.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Finset α}, ¬Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.sdiff_erase_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_erase_self.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Finset α} {a : α}, s \ s.erase a = {a} := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.sdiff_nonempty_of_card_lt_card, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_nonempty_of_card_lt_card.h4 : ¬∀ {α : Type} {s t : Finset α} [inst : DecidableEq α], (t \ s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.card_insert_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_insert_of_mem.h4 : ¬∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α], (Insert.insert a s).card = s.card := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- Finset.card_insert_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_insert_of_notMem.h4 : Not
      (∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α],
        @Eq Nat (@Finset.card α (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a s))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Finset.card α s)
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instDecidableEqNat)) (by
  decide +kernel)

-- List.maximum_le_of_forall_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maximum_le_of_forall_le.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {b : WithBot α}, l.maximum ≤ b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([1]) (0)) (by
  decide +kernel)

-- Finset.card_erase_add_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_erase_add_one.h4 : ¬∀ {α : Type} {s : Finset α} {a : α} [inst : DecidableEq α], (s.erase a).card + 1 = s.card := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- List.le_minimum_of_forall_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_minimum_of_forall_le.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {b : WithTop α}, b ≤ l.minimum := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([0]) (1)) (by
  decide +kernel)

-- Multiset.powersetCard_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.powersetCard_mono.h4 : ¬∀ {α : Type} (n : ℕ) {s t : Multiset α}, Multiset.powersetCard n s ≤ Multiset.powersetCard n t := fun hc_h => absurd (@hc_h (ℕ) (1) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.dens_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.dens_cons.h4 : ¬∀ {α : Type} [inst : Fintype α] {s : Finset α} {a : α}, a ∉ s := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (Bool.true)) (by
  decide +kernel)

-- Finset.dens_lt_dens, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.dens_lt_dens.h4 : ¬∀ {α : Type} [inst : Fintype α] {s t : Finset α}, s.dens < t.dens := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.dens_disjUnion, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.dens_disjUnion.h4 : ¬∀ {α : Type} [inst : Fintype α] (s t : Finset α), Disjoint s t := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.dens_le_dens, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.dens_le_dens.h4 : ¬∀ {α : Type} [inst : Fintype α] {s t : Finset α}, s.dens ≤ t.dens := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.disjiUnion_singleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjiUnion_singleton.h4 : ¬∀ {α β : Type} {s : Finset α} {f : α → β}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Finset.restrict₂_def, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.restrict₂_def.h4 : Not
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

-- Computation.terminates_map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.terminates_map.h4 : ¬∀ {α β : Type} (f : α → β) (s : Computation α), (Computation.map f s).Terminates := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (Inhabited.default)) (by
  nofun)

-- Finset.symmDiff_eq_union, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.symmDiff_eq_union.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Eq (Finset α) (@symmDiff (Finset α) (@Finset.instMax α inst) (@Finset.instSDiff α inst) s t)
          (@Max.max (Finset α) (@Finset.instMax α inst) s t)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Stream'.Seq.get?_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.get?_mem.h4 : ¬∀ {α : Type} {s : Stream'.Seq α} {n : ℕ} {x : α}, x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0) (0)) (by
  nofun)

-- Stream'.Seq.eq_or_mem_of_mem_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.eq_or_mem_of_mem_cons.h4 : ¬∀ {α : Type} {a b : α} {s : Stream'.Seq α}, a = b ∨ a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (Inhabited.default)) (by
  nofun)

-- Stream'.Seq.get?_set_of_terminatedAt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.get?_set_of_terminatedAt.h4 : ¬∀ {α : Type} (x : α) {s : Stream'.Seq α} {n : ℕ}, (s.set n x).get? n = Option.none := fun hc_h => absurd (@hc_h (ℕ) (0) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ) (0)) (by
  decide +kernel)

-- Multiset.mem_of_mem_toEnumFinset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.mem_of_mem_toEnumFinset.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {m : Multiset α} {p : α × ℕ}, p.1 ∈ m := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) ((0, 0))) (by
  decide +kernel)

-- Multiset.le_cons_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.le_cons_of_notMem.h4 : ¬∀ {α : Type} {s t : Multiset α} {a : α}, s ≤ a ::ₘ t ↔ s ≤ t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Multiset.cons_le_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.cons_le_cons.h4 : ¬∀ {α : Type} {s t : Multiset α} (a : α), a ::ₘ s ≤ a ::ₘ t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Multiset.count_eq_of_nodup, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_eq_of_nodup.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, Multiset.count a s = if a ∈ s then 1 else 0 := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.count_eq_zero_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.count_eq_zero_of_notMem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, Multiset.count a s = 0 := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.add_le_add_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.add_le_add_left.h4 : ¬∀ {α : Type} {s t u : Multiset α}, s + t ≤ s + u := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Nodup.erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.erase.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (a : α) {l : Multiset α}, (l.erase a).Nodup := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (Bool.false) (({true, true} : Multiset Bool) : Multiset Bool)) (by
  decide +kernel)

-- Multiset.add_sub_cancel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.add_sub_cancel.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s - t + t = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.cons_erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.cons_erase.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Multiset α} {a : α}, a ::ₘ s.erase a = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ((0 : Multiset Nat) : Multiset ℕ) (0)) (by
  decide +kernel)

-- Multiset.add_le_add_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.add_le_add_right.h4 : ¬∀ {α : Type} {s t u : Multiset α}, s + u ≤ t + u := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Nat.multinomial_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multinomial_congr.h4 : Not (∀ {α : Type} {s : Finset α} {f g : α → Nat}, @Eq Nat (@Nat.multinomial α s f) (@Nat.multinomial α s g)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
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
          (@Eq.refl Bool Bool.true)))) (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat)) (by
  decide +kernel)

-- Finset.card_lt_univ_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_lt_univ_of_notMem.h4 : ¬∀ {α : Type} [inst : Fintype α] {s : Finset α} {x : α}, s.card < Fintype.card α := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := {Bool.true, Bool.false}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) (Bool.false)) (by
  decide +kernel)

-- Fintype.card_of_subtype, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_of_subtype.h3 : ¬∀ {α : Type} {p : α → Prop} (s : Finset α) [inst : Fintype { x : α // p x }], Fintype.card { x : α // p x } = s.card := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (Fintype.subtypeEq 0)) (by
  decide +kernel)

-- CovBy.exists_finset_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CovBy.exists_finset_insert.h4 : ¬∀ {α : Type} {s t : Finset α} [inst : DecidableEq α], ∃ a ∉ s, Insert.insert a s = t := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (instDecidableEqNat)) (by
  simp)

-- Finset.Ico_eq_image_ssubsets, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Ico_eq_image_ssubsets.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Eq (Finset (Finset α))
          (@Finset.Ico (Finset α) (@PartialOrder.toPreorder (Finset α) (@Finset.instPartialOrder α))
            (@Finset.instLocallyFiniteOrder α inst) s t)
          (@Finset.image (Finset α) (Finset α) (fun (a b : Finset α) => @Finset.decidableEq α inst a b)
            (fun (x : Finset α) => @Max.max (Finset α) (@Finset.instMax α inst) s x)
            (@Finset.ssubsets α inst (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t s)))) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Multiset.map_mk_eq_map_mk_of_rel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.map_mk_eq_map_mk_of_rel.h4 : ¬∀ {α : Type} {r : α → α → Prop} {s t : Multiset α}, Multiset.map (Quot.mk r) s = Multiset.map (Quot.mk r) t := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ((0 : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Multiset.nodup_map_iff_of_inj_on, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.nodup_map_iff_of_inj_on.h4 : ¬∀ {α β : Type} {s : Multiset α} {f : α → β}, (Multiset.map f s).Nodup ↔ s.Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (({0, 1} : Multiset Nat) : Multiset ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  decide +kernel)

-- Multiset.dedup_cons_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.dedup_cons_of_notMem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, (a ::ₘ s).dedup = a ::ₘ s.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.offDiag_union, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.offDiag_union.h4 : Not
      (∀ {α : Type} {s t : Finset α} [inst : DecidableEq α],
        @Eq (Finset (Prod α α)) (@Finset.offDiag α (@Max.max (Finset α) (@Finset.instMax α inst) s t))
          (@Max.max (Finset (Prod α α))
            (@Finset.instMax (Prod α α) fun (a b : Prod α α) => @instDecidableEqProd α α inst inst a b)
            (@Max.max (Finset (Prod α α))
              (@Finset.instMax (Prod α α) fun (a b : Prod α α) => @instDecidableEqProd α α inst inst a b)
              (@Max.max (Finset (Prod α α))
                (@Finset.instMax (Prod α α) fun (a b : Prod α α) => @instDecidableEqProd α α inst inst a b)
                (@Finset.offDiag α s) (@Finset.offDiag α t))
              (@SProd.sprod (Finset α) (Finset α) (Finset (Prod α α)) (@Finset.instSProd α α) s t))
            (@SProd.sprod (Finset α) (Finset α) (Finset (Prod α α)) (@Finset.instSProd α α) t s))) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Multiset.Nodup.inter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.inter.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Multiset α} (t : Multiset α), (s ∩ t).Nodup := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (({true, true} : Multiset Bool) : Multiset Bool) (({true, true} : Multiset Bool) : Multiset Bool)) (by
  decide +kernel)

-- Multiset.Disjoint.ndunion_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Disjoint.ndunion_eq.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : Multiset α}, s.ndunion t = s.dedup + t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0} : Multiset Nat) : Multiset ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.ndinsert_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.ndinsert_of_mem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {s : Multiset α}, Multiset.ndinsert a s = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.forall_mem_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.forall_mem_cons.h3 : Not (∀ {α : Type} {s : Finset α} {a : α} (p : α → Prop), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.Nontrivial.sdiff_singleton_nonempty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nontrivial.sdiff_singleton_nonempty.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {c : α} {s : Finset α}, (s \ {c}).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.union_sdiff_cancel_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_sdiff_cancel_left.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Eq (Finset α)
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) (@Max.max (Finset α) (@Finset.instMax α inst) s t) s) t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.sdiff_union_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sdiff_union_of_subset.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s₁ s₂ : Finset α},
        @Eq (Finset α)
          (@Max.max (Finset α) (@Finset.instMax α inst) (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) s₂ s₁) s₁) s₂) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.union_sdiff_cancel_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_sdiff_cancel_right.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Eq (Finset α)
          (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) (@Max.max (Finset α) (@Finset.instMax α inst) s t) t) s) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.union_sdiff_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.union_sdiff_of_subset.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {s t : Finset α},
        @Eq (Finset α)
          (@Max.max (Finset α) (@Finset.instMax α inst) s (@SDiff.sdiff (Finset α) (@Finset.instSDiff α inst) t s)) t) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.min'_eq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_eq_iff.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.card_le_diff_of_interleaved, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_le_diff_of_interleaved.h4 : Not
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

-- Finset.filter_true_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_true_of_mem.h4 : Not
      (∀ {α : Type} {p : α → Prop} [inst : @DecidablePred α p] {s : Finset α}, @Eq (Finset α) (@Finset.filter α p inst s) s) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun (a : Nat) => instDecidableEqNat a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Finset.mk Nat
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

-- Finset.mem_of_max, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_of_max.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α} {a : α}, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.min_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min_le.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {a : α} {s : Finset α}, s.min ≤ ↑a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.filter_mem_eq_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filter_mem_eq_of_subset.h4 : Not
      (∀ {α : Type} {s t : Finset α}
        [inst :
          @DecidablePred α fun (x : α) =>
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x],
        @Eq (Finset α)
          ({x ∈ t | @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x}) s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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
          (@Eq.refl Bool Bool.true)))) (fun (a : Nat) =>
      @Finset.decidableMem Nat instDecidableEqNat a
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
              (@Eq.refl Bool Bool.true)))))) (by
  decide +kernel)

-- Finset.le_max', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.le_max'.h4 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.max_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max_mono.h4 : Not
      (∀ {α : Type} [inst : LinearOrder α] {s t : Finset α},
        @LE.le (WithBot α)
          (@Preorder.toLE (WithBot α)
            (@WithBot.instPreorder α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))))
          (@Finset.max α inst s) (@Finset.max α inst t)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.coe_filterMap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.coe_filterMap.h4 : ¬∀ {α β : Type} (f : α → Option β) {s : Finset α} (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a' := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) => Option.some 0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.max'_eq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_eq_iff.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.min'_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_le.h4 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) (x : α), x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.max'_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_lt_iff.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α) {x : α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.max'_erase_ne_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_erase_ne_self.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {x : α} {s : Finset α}, (s.erase x).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.notMem_of_coe_lt_min, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.notMem_of_coe_lt_min.h4 : Not (∀ {α : Type} [inst : LinearOrder α] {a : α} {s : Finset α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (Nat.instLinearOrder) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.Nonempty.map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.map.h4 : ¬∀ {α β : Type} {f : α ↪ β} {s : Finset α}, (Finset.map f s).Nonempty := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.eq_iff_card_le_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_iff_card_le_of_subset.h3 : Not
      (∀ {α : Type} {s t : Finset α}, Iff (@LE.le Nat instLENat (@Finset.card α t) (@Finset.card α s)) (@Eq (Finset α) s t)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Multiset.card_lt_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.card_lt_card.h3 : ¬∀ {α : Type} {s t : Multiset α}, s.card < t.card := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.card_le_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.card_le_card.h3 : ¬∀ {α : Type} {s t : Multiset α}, s.card ≤ t.card := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Multiset.Le.subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Le.subset.h3 : ¬∀ {α : Type} {s t : Multiset α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- Finset.card_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_cons.h3 : Not (∀ {α : Type} {s : Finset α} {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- CovBy.finset_val, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CovBy.finset_val.h3 : ¬∀ {α : Type} {s t : Finset α}, s.val ⋖ t.val := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- CovBy.card_multiset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CovBy.card_multiset.h3 : ¬∀ {α : Type} {s t : Multiset α}, s.card ⋖ t.card := fun hc_h => absurd (@hc_h (ℕ) ((0 : Multiset Nat) : Multiset ℕ) ((0 : Multiset Nat) : Multiset ℕ)) (by
  simp)

-- CovBy.exists_finset_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CovBy.exists_finset_cons.h3 : ¬∀ {α : Type} {s t : Finset α}, ∃ (a : α) (ha : a ∉ s), Finset.cons a s ha = t := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.exists_mem_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_mem_ne.h2 : ¬∀ {α : Type} {s : Finset α} (a : α), ∃ b ∈ s, b ≠ a := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.card_le_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_le_card.h3 : Not (∀ {α : Type} {s t : Finset α}, @LE.le Nat instLENat (@Finset.card α s) (@Finset.card α t)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.eq_of_veq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_veq.h3 : Not (∀ {α : Type} {s t : Finset α}, @Eq (Finset α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Finset.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ext.h3 : Not (∀ {α : Type} {s₁ s₂ : Finset α}, @Eq (Finset α) s₁ s₂) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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

-- Multiset.revzip_powersetAux, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.revzip_powersetAux.h3 : ¬∀ {α : Type} {l : List α} ⦃x : Multiset α × Multiset α⦄, x.1 + x.2 = ↑l := fun hc_h => absurd (@hc_h (ℕ) ([0]) ((0, 0))) (by
  decide +kernel)

-- Computation.of_think_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.of_think_mem.h3 : ¬∀ {α : Type} {s : Computation α} {a : α}, a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- Computation.get_thinkN, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.get_thinkN.h2 : ¬∀ {α : Type} (s : Computation α) (n : ℕ), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- Computation.of_thinkN_terminates, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.of_thinkN_terminates.h3 : ¬∀ {α : Type} (s : Computation α) (n : ℕ), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- Computation.terminates_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.terminates_of_mem.h3 : ¬∀ {α : Type} {s : Computation α} {a : α}, s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- Stream'.Seq.head_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.head_eq_some.h3 : ¬∀ {α : Type} {s : Stream'.Seq α} {x : α}, s = Stream'.Seq.cons x s.tail := fun hc_h => absurd (@hc_h (ℕ) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ) (0)) (by
  simp)

-- Finset.Nonempty.dens_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.dens_ne_zero.h3 : ¬∀ {α : Type} [inst : Fintype α] {s : Finset α}, s.dens ≠ 0 := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Multiset.Nodup.dedup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.Nodup.dedup.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Multiset α}, s.dedup = s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (({0, 0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.Nonempty.forall_const, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.forall_const.h2 : ¬∀ {α : Type} {s : Finset α} {p : Prop}, (∀ x ∈ s, p) ↔ p := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (False)) (by
  decide +kernel)

-- Finset.ne_empty_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ne_empty_of_mem.h3 : ¬∀ {α : Type} {a : α} {s : Finset α}, s ≠ ∅ := fun hc_h => absurd (@hc_h (ℕ) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.sorted_zero_eq_min', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sorted_zero_eq_min'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, 0 < (s.sort fun (a b : α) => a ≤ b).length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.eq_iff_card_ge_of_superset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_iff_card_ge_of_superset.h3 : Not
      (∀ {α : Type} {s t : Finset α}, Iff (@LE.le Nat instLENat (@Finset.card α t) (@Finset.card α s)) (@Eq (Finset α) t s)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.powersetCard_card_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.powersetCard_card_add.h3 : ¬∀ {α : Type} {n : ℕ} (s : Finset α), Finset.powersetCard (s.card + n) s = ∅ := fun hc_h => absurd (@hc_h (ℕ) (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.toList_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.toList_cons.h3 : Not (∀ {α : Type} {a : α} {s : Finset α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.cons_nonempty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_nonempty.h3 : Not (∀ {α : Type} {s : Finset α} {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.nontrivial_iff_ne_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.nontrivial_iff_ne_singleton.h3 : ¬∀ {α : Type} {s : Finset α} {a : α}, s.Nontrivial ↔ s ≠ {a} := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (0)) (by
  decide +kernel)

-- Finset.Nonempty.eq_singleton_default, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nonempty.eq_singleton_default.h3 : ¬∀ {α : Type} [inst : Unique α] {s : Finset α}, s = {Inhabited.default} := fun hc_h => absurd (@hc_h (Unit) (PUnit.instUnique) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Unit })) (by
  decide +kernel)

-- Finset.cons_val, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.cons_val.h3 : Not (∀ {α : Type} {s : Finset α} {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.subset_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.subset_cons.h3 : Not (∀ {α : Type} {s : Finset α} {a : α}, a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.map_eq_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.map_eq_of_subset.h3 : ¬∀ {α : Type} {s : Finset α} {f : α ↪ α}, Finset.map f s = s := fun hc_h => absurd (@hc_h (Bool) ({ val := {Bool.true}, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool }) ({ toFun := Bool.not, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ Bool })) (by
  decide +kernel)

-- Finset.disjUnion_val, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjUnion_val.h3 : Not (∀ {α : Type} (s t : Finset α), @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.disjUnion_comm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.disjUnion_comm.h3 : Not (∀ {α : Type} (s t : Finset α), @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α) s t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.attach_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.attach_cons.h3 : Not (∀ {α : Type} (a : α) (s : Finset α), a ∉ s) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Sym.coe_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.coe_mk.h3 : ¬∀ {α : Type} {n : ℕ} (s : Multiset α), s.card = n := fun hc_h => absurd (@hc_h (ℕ) (1) ((0 : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Finset.max'_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_mem.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.max_mem_image_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max_mem_image_coe.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, s.max ∈ Finset.image WithBot.some s := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.ofDual_min', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.ofDual_min'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset αᵒᵈ}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕᵒᵈ })) (by
  decide +kernel)

-- Cycle.chain_of_pairwise, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.chain_of_pairwise.h3 : ¬∀ {α : Type} {r : α → α → Prop} {s : Cycle α}, Cycle.Chain r s := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ((([0] : List Nat) : Cycle Nat) : Cycle ℕ)) (by
  simp)

-- Finset.sym2_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sym2_mono.h3 : Not
      (∀ {α : Type} {s t : Finset α},
        @LE.le (Finset (Sym2 α))
          (@Preorder.toLE (Finset (Sym2 α))
            (@PartialOrder.toPreorder (Finset (Sym2 α)) (@Finset.instPartialOrder (Sym2 α))))
          (@Finset.sym2 α s) (@Finset.sym2 α t)) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
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

-- Finset.max'_eq_sorted_last, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max'_eq_sorted_last.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.max_of_nonempty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.max_of_nonempty.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, ∃ (a : α), s.max = ↑a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.eq_univ_of_forall, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_univ_of_forall.h3 : ¬∀ {α : Type} [inst : Fintype α] {s : Finset α}, s = Finset.univ := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset Bool })) (by
  decide +kernel)

-- Finset.min_of_nonempty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min_of_nonempty.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, ∃ (a : α), s.min = ↑a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  simp)

-- Finset.min_mem_image_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min_mem_image_coe.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {s : Finset α}, s.min ∈ Finset.image WithTop.some s := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Finset.min'_eq_inf', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.min'_eq_inf'.h3 : ¬∀ {α : Type} [inst : LinearOrder α] (s : Finset α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ })) (by
  decide +kernel)

-- Multiset.eq_zero_of_subset_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_zero_of_subset_zero.h2 : ¬∀ {α : Type} {s : Multiset α}, s = 0 := fun hc_h => absurd (@hc_h (ℕ) (({0} : Multiset Nat) : Multiset ℕ)) (by
  decide +kernel)

-- Cycle.length_nontrivial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cycle.length_nontrivial.h2 : ¬∀ {α : Type} {s : Cycle α}, 2 ≤ s.length := fun hc_h => absurd (@hc_h (ℕ) (∅)) (by
  decide +kernel)

-- Computation.eq_thinkN', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.eq_thinkN'.h2 : ¬∀ {α : Type} (s : Computation α), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default)) (by
  nofun)

-- Computation.results_of_terminates, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.results_of_terminates.h2 : ¬∀ {α : Type} (s : Computation α), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default)) (by
  nofun)

-- Computation.get_promises, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Computation.get_promises.h2 : ¬∀ {α : Type} (s : Computation α), s.Terminates := fun hc_h => absurd (@hc_h (ℕ) (Inhabited.default)) (by
  nofun)

-- Stream'.Seq.head_eq_none, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.head_eq_none.h2 : ¬∀ {α : Type} {s : Stream'.Seq α}, s = Stream'.Seq.nil := fun hc_h => absurd (@hc_h (ℕ) (Stream'.Seq.cons 0 Stream'.Seq.nil : Stream'.Seq ℕ)) (by
  simp)

-- Stream'.Seq.length'_of_not_terminates, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.Seq.length'_of_not_terminates.h2 : ¬∀ {α : Type} {s : Stream'.Seq α}, s.length' = ⊤ := fun hc_h => absurd (@hc_h (ℕ) ((Stream'.Seq.nil : Stream'.Seq Nat) : Stream'.Seq ℕ)) (by
  simp)

