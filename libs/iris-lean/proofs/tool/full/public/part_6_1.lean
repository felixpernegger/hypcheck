import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- Iris.Option.elim_ne, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Iris.Option.elim_ne.h11.inst : ¬(fun (a b : Nat) => a < b) ((Option.some Iris.DFrac.discard).elim 0 fun (a : Iris.DFrac) => 0)
        ((Option.some Iris.DFrac.discard).elim 1 fun (a : Iris.DFrac) => 0) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Iris.Option.elim_ne.h11.prem0 : (fun (a b : Nat) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Iris.Option.elim_ne.h11.prem1 : Iris.OFE.Dist 0 (Option.some Iris.DFrac.discard) (Option.some Iris.DFrac.discard) := by
  rfl
theorem HypCheckProof.Iris.Option.elim_ne.h11 : ¬∀ {α : Type} [inst : Iris.OFE α] {β : Type} (R : β → β → Prop) {f g : α → β} {d d' : β} {x y : Option α} {n : Nat},
        R d d' → Iris.OFE.Dist n x y → R (x.elim d f) (y.elim d' g) := fun hc_h => HypCheckProof.Iris.Option.elim_ne.h11.inst (@hc_h (Iris.DFrac) (Iris.DFrac.instCMRADFrac.toOFE) (Nat) (fun (a b : Nat) => a < b) (fun (a : Iris.DFrac) => 0) (fun (a : Iris.DFrac) => 0) (0) (1) (Option.some Iris.DFrac.discard) (Option.some Iris.DFrac.discard) (0) HypCheckProof.Iris.Option.elim_ne.h11.prem0 HypCheckProof.Iris.Option.elim_ne.h11.prem1)

-- Iris.Option.elim_ne, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.elim_ne.h12 : ¬∀ {α : Type} [inst : Iris.OFE α] {β : Type} (R : β → β → Prop) {f g : α → β} {d d' : β} {x y : Option α} {n : Nat},
        (∀ (x y : α), Iris.OFE.Dist n x y → R (f x) (g y)) → Iris.OFE.Dist n x y → R (x.elim d f) (y.elim d' g) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun (a : Iris.DFrac) => 0) (fun (a : Iris.DFrac) => 1) (0) (0) (Option.none) (Option.none) (0) (by
  simp) (by
  rfl)) (by
  decide +kernel)

-- Iris.Option.elim_ne, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Iris.Option.elim_ne.h13.inst : Not
      ((fun (a b : Nat) => @LE.le Nat instLENat a b)
        (@Option.elim Iris.DFrac Nat (@Option.none Iris.DFrac) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          fun (a : Iris.DFrac) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Option.elim Iris.DFrac Nat (@Option.some Iris.DFrac Iris.DFrac.discard)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) fun (a : Iris.DFrac) =>
          @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Iris.Option.elim_ne.h13.prem0 : ∀ (x y : Iris.DFrac),
      @Iris.OFE.Dist Iris.DFrac (@Iris.ORA.toOFE Iris.DFrac (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x y →
        (fun (a b : Nat) => @LE.le Nat instLENat a b)
          ((fun (a : Iris.DFrac) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
          ((fun (a : Iris.DFrac) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) y) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Iris.Option.elim_ne.h13.prem1 : (fun (a b : Nat) => @LE.le Nat instLENat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Iris.Option.elim_ne.h13 : Not
      (∀ {α : Type} [inst : Iris.OFE α] {β : Type} (R : β → β → Prop) {f g : α → β} {d d' : β} {x y : Option α} {n : Nat},
        (∀ (x y : α), @Iris.OFE.Dist α inst n x y → R (f x) (g y)) →
          R d d' → R (@Option.elim α β x d f) (@Option.elim α β y d' g)) := fun hc_h => HypCheckProof.Iris.Option.elim_ne.h13.inst (@hc_h (Iris.DFrac) (@Iris.ORA.toOFE Iris.DFrac (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac)) (Nat) (fun (a b : Nat) => @LE.le Nat instLENat a b) (fun (a : Iris.DFrac) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a : Iris.DFrac) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Option.none Iris.DFrac) (@Option.some Iris.DFrac Iris.DFrac.discard) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Iris.Option.elim_ne.h13.prem0 HypCheckProof.Iris.Option.elim_ne.h13.prem1)

-- Iris.Ordered.OrderNR.ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderNR.ne.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x x' y y' : α},
        Iris.OFE.Dist n y y' → x ≼ₒ*{n} y → x' ≼ₒ*{n} y' := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl) (by
  rfl)) (by
  nofun)

-- Iris.Ordered.OrderNR.ne, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderNR.ne.h9 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x x' y y' : α},
        Iris.OFE.Dist n x x' → x ≼ₒ*{n} y → x' ≼ₒ*{n} y' := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl) (by
  rfl)) (by
  nofun)

-- Iris.Ordered.OrderNR.ne, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderNR.ne.h10 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x x' y y' : α},
        Iris.OFE.Dist n x x' → Iris.OFE.Dist n y y' → x' ≼ₒ*{n} y' := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl) (by
  rfl)) (by
  nofun)

-- Iris.Std.LawfulBigOp.trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.trans.h4 : ¬∀ {PROP : Type} (f : PROP → PROP → PROP) {unit : outParam PROP} {eq : outParam (PROP → PROP → Prop)} {a b c : PROP},
        eq a b → eq b c → eq a c := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (Bool.false) (fun (a : Bool) => if a = Bool.false then fun (b : Bool) => b = Bool.true else fun (b : Bool) => b = Bool.false) (Bool.false) (Bool.true) (Bool.false) (by
  rfl) (by
  rfl)) (by
  simp)

-- Iris.UFracAuth.ord, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.UFracAuth.ord.h8 : ¬∀ {A : Type} [inst : Iris.ORA A] [inst_1 : Iris.ORA.Discrete A] [inst_2 : Iris.IncOrd A] {q p : Iris.Qp} {a b : A},
        Option.some b ≼ₒ Option.some a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ _ ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.dist_prod_ext, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_prod_ext.h9 : ¬∀ {α β : Type} {n : Nat} [inst : Iris.OFE α] [inst_1 : Iris.OFE β] {x₁ x₂ : α} {y₁ y₂ : β},
        Iris.OFE.Dist n y₁ y₂ → Iris.OFE.Dist n (x₁, y₁) (x₂, y₂) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (0) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.OFE.dist_prod_ext, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_prod_ext.h10 : ¬∀ {α β : Type} {n : Nat} [inst : Iris.OFE α] [inst_1 : Iris.OFE β] {x₁ x₂ : α} {y₁ y₂ : β},
        Iris.OFE.Dist n x₁ x₂ → Iris.OFE.Dist n (x₁, y₁) (x₂, y₂) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (0) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.mapIdx_ne, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.mapIdx_ne.h10 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst_1 : Iris.OFE β] {n : Nat} {f g : Nat → α → β},
        (∀ (i : Nat) (a b : α), Iris.OFE.Dist n a b → Iris.OFE.Dist n (f i a) (g i b)) →
          ∀ {l k : List α}, Iris.OFE.Dist n (List.mapIdx f l) (List.mapIdx g k) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (0) (fun (a : Nat) (a_1 : Iris.DFrac) => Iris.DFrac.discard) (fun (a : Nat) (a_1 : Iris.DFrac) => Iris.DFrac.discard) (by
  simp) ([]) ([Iris.DFrac.discard])) (by
  nofun)

-- Iris.list_fmap_ne, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.list_fmap_ne.h10 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst_1 : Iris.OFE β] {n : Nat} {f g : α → β},
        (∀ {a b : α}, Iris.OFE.Dist n a b → Iris.OFE.Dist n (f a) (g b)) →
          ∀ {l k : List α}, Iris.OFE.Dist n (List.map f l) (List.map g k) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (0) (fun (a : Iris.DFrac) => Iris.DFrac.discard) (fun (a : Iris.DFrac) => Iris.DFrac.discard) (by
  simp) ([]) ([Iris.DFrac.discard])) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_dist, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_dist.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {Φ Ψ : Nat → A → M} {l : List A} {n : Nat},
        (∀ {i : Nat} {x : A}, l[i]? = Option.some x → Iris.OFE.Dist n (Φ i x) (Ψ i x)) → Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard) (fun (a a_1 : Nat) => Iris.DFrac.discard) ([]) (0) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_eq_of_perm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_eq_of_perm.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : A → M) {l₁ l₂ : List A},
        l₁.Perm l₂ → Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a : Nat) => Iris.DFrac.discard) ([]) ([]) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Mra.toMra_rel_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Mra.toMra_rel_injective.h3 : Not
      (∀ {α : Type} {R : α → α → Prop} (S : α → α → Prop),
        (∀ {a b : α}, R a b → R b a → S a b) →
          ∀ {a b : α}, @Eq (@Iris.Mra α R) (@Iris.Mra.toMra α R a) (@Iris.Mra.toMra α R b) → S a b) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) (by
  omega) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iris.Mra.toMra_rel_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Mra.toMra_rel_injective.h4 : Not
      (∀ {α : Type} {R : α → α → Prop} (S : α → α → Prop),
        (∀ {a : α}, R a a) → ∀ {a b : α}, @Eq (@Iris.Mra α R) (@Iris.Mra.toMra α R a) (@Iris.Mra.toMra α R b) → S a b) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a ≤ b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) (by
  simp) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iris.Mra.toMra_rel_injective, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Mra.toMra_rel_injective.h7 : ¬∀ {α : Type} {R : α → α → Prop} (S : α → α → Prop),
        (∀ {a : α}, R a a) → (∀ {a b : α}, R a b → R b a → S a b) → ∀ {a b : α}, S a b := fun hc_h => absurd (@hc_h (Nat) (fun a b => a ≤ b : Nat → Nat → Prop) (fun a b => a ≤ b : Nat → Nat → Prop) (by
  simp) (by
  omega) (1) (0)) (by
  decide +kernel)

-- Iris.OFE.equiv_prod_ext, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.equiv_prod_ext.h8 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst : Iris.OFE β] {x₁ x₂ : α} {y₁ y₂ : β}, y₁ = y₂ → (x₁, y₁) = (x₂, y₂) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) _ (Iris.DFrac.discard : Iris.DFrac) rfl) (by
  decide +kernel)

-- Iris.OFE.equiv_prod_ext, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.equiv_prod_ext.h9 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst : Iris.OFE β] {x₁ x₂ : α} {y₁ y₂ : β}, x₁ = x₂ → (x₁, y₁) = (x₂, y₂) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) rfl) (by
  decide +kernel)

-- Iris.ORA.pcore_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_mono.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {cx : α} [inst_1 : Iris.OrdInc α] {x y : α},
        Iris.PCore.pcore x = Option.some cx → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ cx ≼ cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.ORA.ordN_of_ordN_of_dist, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.ordN_of_ordN_of_dist.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {a b c : α}, Iris.OFE.Dist n b c → a ≼ₒ{n} c := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.ORA.ordN_of_dist_of_ordN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.ordN_of_dist_of_ordN.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {a b c : α}, Iris.OFE.Dist n a b → a ≼ₒ{n} c := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.ORA.incN_of_dist_of_incN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.incN_of_dist_of_incN.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {a b c : α}, Iris.OFE.Dist n a b → a ≼{n} c := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Std.LawfulBigOp.symm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.symm.h4 : ¬∀ {PROP : Type} (f : PROP → PROP → PROP) {unit : outParam PROP} {eq : outParam (PROP → PROP → Prop)} {a b : PROP},
        eq a b → eq b a := fun hc_h => absurd (@hc_h (Nat) (fun a b => a - b : Nat → Nat → Nat) (0) (fun (a n : Nat) => n = 0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iris.Option.validN_of_ordN_validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.validN_of_ordN_validN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Option.some b ≼ₒ{n} Option.some a → ✓{n} b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Option.validN_of_ordN_validN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.validN_of_ordN_validN.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, ✓{n} a → ✓{n} b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.validN_of_ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_of_ord.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Ordered.Order.validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.Order.validN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Ordered.OrderNR.validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderNR.validN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Ordered.OrderNR.validN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderNR.validN.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, x ≼ₒ*{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- FromMathlib.Relation.TransGen.trans_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Relation.TransGen.trans_left.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, FromMathlib.Relation.ReflTransGen r b c → Relation.TransGen r a c := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- FromMathlib.Relation.TransGen.trans_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Relation.TransGen.trans_left.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, Relation.TransGen r a b → Relation.TransGen r a c := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (1) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- List.Forall₂.symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.symm.h2 : ¬∀ {α : Type} {R : α → α → Prop} {l k : List α}, List.Forall₂ R l k → List.Forall₂ R k l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) ([0]) ([1]) (by
  decide)) (by
  decide +kernel)

-- List.Forall₂.symm, hypothesis 5: necessary
/- FAILED: 3:3: `simp` made no progress | 3:3: `simp` made no progress | 3:3: `simp` made no progress | 3:3: `simp` made no progress | 7:245: don't know how to synthesize implicit argument `b`
  @h5.prem0 (?m.11 hc_h) (?m.12 hc_h)
context:
hc_h : ∀ {α : Type} {R : α → α → Prop}, (∀ {a b : α}, R a b → R b a) → ∀ {l k : List α}, List.Forall₂ R k l
a✝ b✝ : Bool
⊢ Bool | 8:255: don't know how to synthesize implicit argument `b`
  @h5.prem0 (?m.6 hc_h) (?m.7 hc_h)
context:
hc_h : ∀ {α : Type} {R : α → α → Prop}, (∀ {a b : α}, R a b → R b a) → ∀ {l k : List α}, List.Forall₂ R k l
a✝ b✝ : Bool
⊢ Bool | 7:245: don't know how to synthesize implicit argument `b`
  @h5.prem0 (?m.11 hc_h) (?m.12 hc_h)
context:
hc_h : ∀ {α : Type} {R : α → α → Prop}, (∀ {a b : α}, R a b → R b a) → ∀ {l k : List α}, List.Forall₂ R k l
a✝ b✝ : Bool
⊢ Bool | 8:255: don't know how to synthesize implicit argument `b`
  @h5.prem0 (?m.6 hc_h) (?m.7 hc_h)
context:
hc_h : ∀ {α : Type} {R : α → α → Prop}, (∀ {a b : α}, R a b → R b a) → ∀ {l k : List α}, List.Forall₂ R k l
a✝ b✝ : Bool
⊢ Bool
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.symm.h5 : ¬∀ {α : Type} {R : α → α → Prop}, (∀ {a b : α}, R a b → R b a) → ∀ {l k : List α}, List.Forall₂ R k l := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) ([]) ([Bool.false])) (by
  decide +kernel)
-/

-- Iris.ORA.valid_mapN, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.valid_mapN.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α}, ✓ x → ✓ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.valid_mapN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.valid_mapN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α}, (∀ (n : Nat), ✓{n} x → ✓{n} y) → ✓ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  simp)) (by
  nofun)

-- Iris.Option.some_mk_ordN, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_mk_ordN.h9 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {n : Nat} {a₁ a₂ : α} {b₁ b₂ : β},
        Option.some a₁ ≼ₒ{n} Option.some a₂ ∧ Option.some b₁ ≼ₒ{n} Option.some b₂ := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.discrete_inc_r, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.discrete_inc_r.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α} [HD : Iris.OFE.DiscreteE y], x ≼ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) _) (by
  nofun)

-- Iris.Option.isSome_mono_ord, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_mono_ord.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {ma mb : Option α}, ma.isSome = Bool.true → mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Option.some Iris.DFrac.discard) (Option.none) (by
  decide)) (by
  decide +kernel)

-- Iris.Option.isSome_mono_ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_mono_ord.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {ma mb : Option α}, ma ≼ₒ mb → mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Option.none) (Option.none) (by
  rfl)) (by
  decide +kernel)

-- Iris.Option.some_mk_incN, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_mk_incN.h9 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {n : Nat} {a₁ a₂ : α} {b₁ b₂ : β},
        Option.some a₁ ≼{n} Option.some a₂ ∧ Option.some b₁ ≼{n} Option.some b₂ := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.valid_of_ord, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.valid_of_ord.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α}, ✓ y → ✓ x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.inc_of_inc0, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.inc_of_inc0.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] [inst_1 : Iris.OFE.Discrete α] {x y : α}, x ≼ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_append_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_append_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : Nat → A → M) (l₁ l₂ : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard) ([]) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_consZ_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_consZ_right.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : Int → A → M) (x : A) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a : Int) (a_1 : Nat) => Iris.DFrac.discard) (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Option.some_op_ordN_snd, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_op_ordN_snd.h8 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst : Iris.ORA β] {n : Nat} {x y : α × β} {c : Option (α × β)},
        Option.some x.snd • Option.map Prod.snd c ≼ₒ{n} Option.some y.snd := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (0) ((Iris.DFrac.discard, Iris.DFrac.discard)) ((Iris.DFrac.discard, Iris.DFrac.own 1)) (Option.none)) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_take_drop_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_take_drop_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : Nat → A → M) (l : List A) (n : Nat),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard) ([]) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Option.some_mk_inc, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_mk_inc.h8 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {a₁ a₂ : α} {b₁ b₂ : β},
        Option.some a₁ ≼ Option.some a₂ ∧ Option.some b₁ ≼ Option.some b₂ := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.op_monoN_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_monoN_left.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y : α} (z : α), x • z ≼{n} y • z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.Prod.ordNR_fst, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.ordNR_fst.h7 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {n : Nat} {x y : α × β}, x.fst ≼ₒ*{n} y.fst := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (0) ((Iris.DFrac.discard, Iris.DFrac.discard)) ((Iris.DFrac.own 1, Iris.DFrac.discard))) (by
  nofun)

-- Iris.Algebra.MonoidOps.op_assoc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.MonoidOps.op_assoc.h4 : ¬∀ {M : Type} {inst : Iris.OFE M} {op : M → M → M} {unit : outParam M} {a b c : M}, op (op a b) c = op a (op b c) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a : Iris.DFrac) =>
      if a = Iris.DFrac.discard then fun (a : Iris.DFrac) => Iris.DFrac.own 1
      else fun (a : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.op_monoN_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_monoN_right.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y : α} (z : α), z • x ≼{n} z • y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.ProgramLogic.set_append_set_append, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ProgramLogic.set_append_set_append.h7 : ¬∀ {Expr : Type} {tp : List Expr} {n : Nat} {a b : Expr} {efs₁ efs₂ : List Expr},
        (tp.set n a ++ efs₁).set n b ++ efs₂ = tp.set n b ++ (efs₁ ++ efs₂) := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0) (0) ([1]) ([])) (by
  decide +kernel)

-- Iris.ORA.op_right_dist, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_right_dist.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} (x : α) {y z : α}, Iris.OFE.Dist n (x • y) (x • z) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Prod.ordNR_snd, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.ordNR_snd.h7 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst : Iris.ORA β] {n : Nat} {x y : α × β}, x.snd ≼ₒ*{n} y.snd := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (0) ((Iris.DFrac.discard, Iris.DFrac.discard)) ((Iris.DFrac.discard, Iris.DFrac.own 1))) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_singleton_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_singleton_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : Nat → A → M) (a : A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Prod.validN_snd, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.validN_snd.h6 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst : Iris.ORA β] {n : Nat} {x : α × β}, ✓{n} x.snd := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (0) ((Iris.DFrac.discard, Iris.DFrac.ownDiscard 1))) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_const_unit_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_const_unit_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {l : List A}, Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.IncludedN.succ, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IncludedN.succ.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y : α}, x ≼{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.incN_of_inc, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.incN_of_inc.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] (n : Nat) {x y : α}, x ≼{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Ordered.ordN_succ, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.ordN_succ.h6 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.Ordered α] {n : Nat} {x y : α}, x ≼ₒ{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.some_ordN_some_of_dist, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_ordN_some_of_dist.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Option.some a ≼ₒ{n} Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ProofMode.NatCancel.nat_cancel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ProofMode.NatCancel.nat_cancel.h5 : ¬∀ {n m : Nat} {n' m' : outParam Nat} {stuck : outParam Bool}, n' + m = n + m' := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (Bool.false)) (by
  decide +kernel)

-- Iris.Option.join_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.join_ne.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {x y : Option (Option α)} {n : Nat}, Iris.OFE.Dist n x.join y.join := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Option.none) (Option.some (Option.some Iris.DFrac.discard)) (0)) (by
  simp)

-- Iris.Option.dist_or_incN_of_some_incN_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.dist_or_incN_of_some_incN_some.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Iris.OFE.Dist n a b ∨ a ≼{n} b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- LawfulAddLE.le_iff_exists_add, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.LawfulAddLE.le_iff_exists_add.h3.inst : ¬(2 % 2 ≤ 0 % 2 ↔ ∃ (z : Nat), 0 = 2 + z) := by
  omega
theorem HypCheckProof.LawfulAddLE.le_iff_exists_add.h3 : ¬∀ {α : Type} {inst : Add α} {inst_1 : LE α} {x y : α}, x ≤ y ↔ ∃ (z : α), y = x + z := fun hc_h => HypCheckProof.LawfulAddLE.le_iff_exists_add.h3.inst (@hc_h (Nat) (instAddNat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (2) (0))

-- Iris.Option.exists_of_some_ordN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exists_of_some_ordN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a : α} {mb : Option α},
        ∃ (b : α), mb = Option.some b ∧ Option.some a ≼ₒ{n} Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Option.none)) (by
  simp)

-- Iris.MaxPrefixList.toMaxPrefixList_ordN_aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MaxPrefixList.toMaxPrefixList_ordN_aux.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {l1 l2 : List α}, Iris.OFE.Dist n l2 (l1 ++ List.drop l1.length l2) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) ([Iris.DFrac.discard]) ([])) (by
  nofun)

-- Iris.ORA.op?_mono_left_ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op?_mono_left_ord.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α} (mz : Option α), x •? mz ≼ₒ y •? mz := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Option.none)) (by
  nofun)

-- Iris.ExclAuth.agreeN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ExclAuth.agreeN.h5 : ¬∀ {A : Type} [inst : Iris.OFE A] {n : Nat} {a b : A}, Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Agree.toAgree_injN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Agree.toAgree_injN.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {a b : α}, Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Agree.Raw.toAgree_injN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Agree.Raw.toAgree_injN.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {a b : α}, Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- FracAuth.agree, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.agree.h5 : ¬∀ {A : Type} [inst : Iris.ORA A] {dq : Iris.DFrac} {a b : A}, a = b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.list_flatten_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.list_flatten_ne.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {l k : List (List α)}, Iris.OFE.Dist n l.flatten k.flatten := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) ([]) ([[Iris.DFrac.discard]])) (by
  nofun)

-- Iris.Valid.validN_succ, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Valid.validN_succ.h5 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.Valid α] {x : α} {n : Nat}, ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toValid) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (0)) (by
  nofun)

-- Iris.Algebra.MonoidOps.op_right_id, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.MonoidOps.op_right_id.h5 : ¬∀ {M : Type} [inst : Iris.OFE M] {unit : M} {op : M → M → M} {a : M}, op a unit = a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ProgramLogic.getElem?_set_append_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ProgramLogic.getElem?_set_append_self.h5 : ¬∀ {Expr : Type} {tp : List Expr} {n : Nat} {a : Expr} {efs : List Expr}, (tp.set n a ++ efs)[n]? = Option.some a := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0) ([])) (by
  decide +kernel)

-- Iris.Prod.valid_fst, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.valid_fst.h5 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {x : α × β}, ✓ x.fst := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) ((Iris.DFrac.ownDiscard 1, Iris.DFrac.discard))) (by
  nofun)

-- Iris.UFracAuth.agree, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.UFracAuth.agree.h5 : ¬∀ {A : Type} [inst : Iris.ORA A] {p : Iris.Qp} {a b : A}, a = b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.OFE.dist_some_inv_l', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_some_inv_l'.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {my : Option α} {x : α},
        ∃ (x' : α), Option.some x' = my ∧ Iris.OFE.Dist n x x' := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Option.none) (Iris.DFrac.discard : Iris.DFrac)) (by
  simp)

-- Iris.OFE.equiv_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.equiv_some.h4 : ¬∀ {α : Type} [inst : Iris.OFE α] {o : Option α} {y : α}, ∃ (z : α), o = Option.some z ∧ z = y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Option.none) (Iris.DFrac.discard : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ProofMode.IsCons.is_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ProofMode.IsCons.is_cons.h4 : ¬∀ {α : Type} {l : List α} {x : outParam α} {xs : outParam (List α)}, l = x :: xs := fun hc_h => absurd (@hc_h (Nat) ([]) (0) ([])) (by
  decide +kernel)

-- Iris.ORA.pcore_op_right', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_right'.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x cx : α}, x • cx = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Option.eq_none_of_ordN_none, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.eq_none_of_ordN_none.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {ma : Option α}, ma = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Option.some Iris.DFrac.discard)) (by
  decide +kernel)

-- Iris.OFE.equiv_ext_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.equiv_ext_left.h4 : ¬∀ {α : Type} {β : Type} {x y : α}, x = y := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (1)) (by
  decide +kernel)

-- Iris.ORA.valid_op_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.valid_op_right.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] (x y : α), ✓ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.equiv_inl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.equiv_inl.h4 : Not (∀ {α β : Type} {x y : α}, @Eq (Sum α β) (@Sum.inl α β x) (@Sum.inl α β y)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- FromMathlib.Relation.TransGen.to_reflTransGen, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Relation.TransGen.to_reflTransGen.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, FromMathlib.Relation.ReflTransGen r a b := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (1) (0)) (by
  nofun)

-- Iris.ORA.pcore_op_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_self.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {cx : α}, cx • cx = cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Agree.Raw.sameElems_of_dist, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Agree.Raw.sameElems_of_dist.h4 : ¬∀ {α : Type} [inst : Iris.OFE α] {x y : Iris.Agree.Raw α}, x.SameElems y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) ({ car := [Iris.DFrac.discard], not_nil := of_decide_eq_true (id (Eq.refl Bool.true)) : Iris.Agree.Raw Iris.DFrac }) ({ car := [Iris.DFrac.own 1], not_nil := of_decide_eq_true (id (Eq.refl Bool.true)) : Iris.Agree.Raw Iris.DFrac })) (by
  nofun)

-- Iris.Option.isSome_of_some_inc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_of_some_inc.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} {mb : Option α}, mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Option.none)) (by
  decide +kernel)

-- Iris.FrameFractionalQp.frame_fractional_qp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.FrameFractionalQp.frame_fractional_qp.h3 : ¬∀ {qR qP : Iris.Qp} {r : outParam Iris.Qp}, qP = qR + r := fun hc_h => absurd (@hc_h ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }))) (by
  decide +kernel)

-- coinfinite_exists_next, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.coinfinite_exists_next.h3 : ¬∀ {K V : Type} {f : K → Option V}, ∃ (k : K), f k = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (some : Nat → Option Nat)) (by
  simp)

-- Iris.HeapLang.loc_add_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.HeapLang.loc_add_inj.h3 : ¬∀ {l : Iris.HeapLang.Loc} {i j : Int}, i = j := fun hc_h => absurd (@hc_h ({ n := 0 : Iris.HeapLang.Loc }) (0) (1)) (by
  decide +kernel)

-- Iris.Option.some_core_id, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_core_id.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] (a : α), Iris.ORA.CoreId (Option.some a) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  exact fun hc_c =>
    absurd (hc_c.core_id)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.ORA.instCoreIdCore, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.instCoreIdCore.h2 : ¬∀ {α : Type} [inst : Iris.ORA α] (y : α), Iris.ORA.CoreId (Iris.PCore.core y) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  exact fun hc_c =>
    absurd (hc_c.core_id)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- PredInfinite.exists_ge, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PredInfinite.exists_ge.h1 : ¬∀ {P : Nat → Prop} (N : Nat), ∃ (k : Nat), N ≤ k ∧ P k := fun hc_h => absurd (@hc_h (fun n => n = 0 : Nat → Prop) (1)) (by
  simp)

-- Iris.UFrac.le_of_ord, hypothesis 2: necessary
/- FAILED: 2:258: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (0 < 1 / 2) = true
in the application
  id (Eq.refl true) | 53:14: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (0 < 1 / 2) = true
in the application
  id (Eq.refl true) | 3:12: Tactic `decide` failed to reduce
  @decide (¬1 ≤ 1 / 2) instDecidableNot
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `instDecidableNot`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 20:12: Tactic `decide` failed to reduce
  @decide (¬1 ≤ 1 / 2) instDecidableNot
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `instDecidableNot`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 3:49: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (0 < 1 / 2) = true
in the application
  id (Eq.refl true) | 54:20: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (0 < 1 / 2) = true
in the application
  id (Eq.refl true) | 3:92: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 19:81: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.UFrac.le_of_ord.h2 : ¬∀ {x y : Iris.UFrac}, x.frac ≤ y.frac := fun hc_h => absurd (@hc_h ({ frac := (⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }) : Iris.UFrac }) ({ frac := (⟨1 / 2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }) : Iris.UFrac })) (by
  (simp <;> decide))
-/

