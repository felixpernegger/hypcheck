import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- List.Forall₂.takeD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.takeD.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β} {l : List α} {k : List β},
        List.Forall₂ R l k → ∀ (n : Nat), List.Forall₂ R (List.takeD n l a) (List.takeD n k b) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) ([]) ([]) (by
  decide) (1)) (by
  decide +kernel)

-- List.Forall₂.takeD, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Forall₂.takeD.h8.inst : ¬List.Forall₂ (fun (a b : Nat) => a < b) (List.takeD 1 [] 0) (List.takeD 1 [0] 1) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Forall₂.takeD.h8.prem0 : (fun (a b : Nat) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.Forall₂.takeD.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β},
        R a b → ∀ {l : List α} {k : List β} (n : Nat), List.Forall₂ R (List.takeD n l a) (List.takeD n k b) := fun hc_h => HypCheckProof.List.Forall₂.takeD.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => a < b) (0) (1) HypCheckProof.List.Forall₂.takeD.h8.prem0 ([]) ([0]) (1))

-- Iris.list_fmap_dist_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.list_fmap_dist_inj.h6 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst_1 : Iris.OFE β] {n : Nat} {f : α → β} {l k : List α},
        Iris.OFE.Dist n (List.map f l) (List.map f k) → Iris.OFE.Dist n l k := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (0) (fun (a : Iris.DFrac) => Iris.DFrac.discard) ([Iris.DFrac.discard]) ([Iris.DFrac.own 1]) (by
  rfl)) (by
  nofun)

-- Iris.modify_ne, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.modify_ne.h9 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {f g : α → α},
        (∀ (a b : α), Iris.OFE.Dist n a b → Iris.OFE.Dist n (f a) (g b)) →
          ∀ (i : Nat) {l k : List α}, Iris.OFE.Dist n (l.modify i f) (k.modify i g) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (fun (a : Iris.DFrac) => Iris.DFrac.discard) (fun (a : Iris.DFrac) => Iris.DFrac.discard) (by
  simp) (0) ([]) ([Iris.DFrac.discard])) (by
  nofun)

-- LeftCancelAdd.cancel_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.LeftCancelAdd.cancel_right.h7 : Not
      (∀ {α : Type} {x₁ x₂ : α} {y : α} [inst : Add α] [inst_1 : @LeftCancelAdd α inst]
        [inst : @Std.Commutative α (@Add.add α inst)], @Eq α x₁ x₂) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instAddNat) (@LeftCancelAdd.mk (Nat) (instAddNat) (by (try dsimp only);   (intros; omega))) (@Std.Commutative.mk (Nat) (@Add.add Nat instAddNat) (by (try dsimp only);   grind))) (by
  decide +kernel)

-- Iris.repeat_dist, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.repeat_dist.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] (f g : α → α) [inst_1 : Iris.OFE.NonExpansive f] {n : Nat} (k : Nat) (z : α),
        Iris.OFE.Dist n (Nat.repeat f k z) (Nat.repeat g k z) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a : Iris.DFrac) => Iris.DFrac.discard) (fun (a : Iris.DFrac) => Iris.DFrac.own 1) _ (0) (1) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.incN_of_incN_of_dist, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.incN_of_incN_of_dist.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {a b c : α}, Iris.OFE.Dist n b c → a ≼{n} c := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Std.ExtTreeMap.getElem?_mergeWith', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_mergeWith'.h3 : Not
      (∀ {K V : Type} [inst : Ord K] [inst_1 : @Std.LawfulEqOrd K inst] {f : K → V → V → V} {k : K}
        {t₁ t₂ : Std.ExtTreeMap K V (@Ord.compare K inst)}, @Std.TransOrd K inst) := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (@Std.LawfulEqCmp.mk (Nat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (fun (a a_1 b : Nat) => @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a_1 b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Std.ExtTreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat))
      (@Ord.compare Nat
        (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt))) (@Std.ExtTreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat))
      (@Ord.compare Nat
        (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.OFE.Dist.lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.lt.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] {m n : Nat} {x y : α}, m < n → Iris.OFE.Dist m x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (1) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.Ordered.OrderR.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderR.trans.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {x y z : α}, y ≼ₒ* z → x ≼ₒ* z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Ordered.OrderR.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderR.trans.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {x y z : α}, x ≼ₒ* y → x ≼ₒ* z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.OFE.dist_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_lt.h6 : ¬∀ {α : Type} [self : Iris.OFE α] {n : Nat} {x y : α} {m : Nat}, m < n → Iris.OFE.Dist m x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (1) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (0) (by
  decide)) (by
  nofun)

-- Iris.SbiUnfold.biEntails_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.SbiUnfold.biEntails_iff.h6 : ¬∀ {PROP : Type} [inst : Iris.Sbi PROP] {P Q : PROP} {Pi Qi : Nat → Prop}
        [hQ : Iris.SbiUnfold Iris.SbiUnfoldClosure.downClosed Q Qi], P ⊣⊢ Q ↔ ∀ (n : Nat), Pi n ↔ Qi n := fun hc_h => absurd (@hc_h (Iris.SiProp : Type) (Iris.instSbiSiProp) ({ holds := fun _ => False, closed := fun h _ => h } : Iris.SiProp) ({ holds := fun _ => False, closed := fun h _ => h } : Iris.SiProp) (fun n => n = 0 : Nat → Prop) (fun _ => False : Nat → Prop) _) (by
  simp)

-- Iris.OFE.Discrete.discrete, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Discrete.discrete.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst : Iris.OFE.Discrete α] {n : Nat} {x y : α}, x = y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) _ (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.validN_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_of_lt.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n n' : Nat} {x : α}, n' < n → ✓{n'} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (1) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.ORA.none_of_excl_valid_op, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.none_of_excl_valid_op.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α} {my : Option α}, ✓{n} x •? my → my = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Option.some Iris.DFrac.discard) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Iris.ORA.none_of_excl_valid_op, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.none_of_excl_valid_op.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α} [inst : Iris.ORA.Exclusive x] {my : Option α}, my = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.own 1 : Iris.DFrac) _ (Option.some Iris.DFrac.discard)) (by
  decide +kernel)

-- Iris.Included.validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Included.validN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- FracAuth.dfrac_valid, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.dfrac_valid.h4 : ¬∀ {A : Type} [inst : Iris.ORA A] {dq : Iris.DFrac} {a : A}, ✓ a → ✓ (●F{dq} a) • ◯F a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- FromMathlib.Nodup.filterMap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Nodup.filterMap.h4 : ¬∀ {α β : Type} {l : List α} {f : α → Option β}, l.Nodup → (List.filterMap f l).Nodup := fun hc_h => absurd (@hc_h (Bool) (Nat) ([Bool.false, Bool.true]) (fun (a : Bool) => Option.some 0) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.Nodup.filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Nodup.filterMap.h5 : ¬∀ {α β : Type} {l : List α} {f : α → Option β},
        (∀ (a a' : α) (b : β), b ∈ f a → b ∈ f a' → a = a') → (List.filterMap f l).Nodup := fun hc_h => absurd (@hc_h (Nat) (Nat) ([0, 0]) (some : Nat → Option Nat) (by
  simp)) (by
  decide +kernel)

-- Iris.Std.mem_singleton_extTreeSet, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.mem_singleton_extTreeSet.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {x y : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Std.mem_singleton_extTreeSet, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.mem_singleton_extTreeSet.h3 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.TransCmp α cmp] {x y : α},
        Iff
          (@Membership.mem α (Std.ExtTreeSet α cmp) (@Std.ExtTreeSet.instMembershipOfTransCmp α cmp inst)
            (@Singleton.singleton α (Std.ExtTreeSet α cmp) (@Std.ExtTreeSet.instSingletonOfTransCmp α cmp inst) y) x)
          (@Eq α x y)) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.true)) (by
  decide +kernel)

-- Iris.ORA.id_free_r, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.id_free_r.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α}, ✓ x → ¬x • y = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Iris.ORA.not_valid_of_excl_inc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.not_valid_of_excl_inc.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} [inst_1 : Iris.ORA.Exclusive x] {y : α}, ¬✓ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) _ (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_mapIdx_pair_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_mapIdx_pair_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {B : Type} (Φ : B → A → M) (f : Nat → B) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (Nat) (fun (a a_1 : Nat) => Iris.DFrac.discard) (fun n => n + 1 : Nat → Nat) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.ORA.pcore_valid, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_valid.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x cx : α}, ✓ x → ✓ cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.id_free_l, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.id_free_l.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α}, ✓ x → ¬y • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Iris.ORA.core_op_mono, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.core_op_mono.h2 : ¬∀ {α : Type} [inst : Iris.ORA α] [inst_1 : Iris.OrdInc α] (x y : α), Iris.PCore.core x ≼ Iris.PCore.core (x • y) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.Option.valid_of_ord_valid, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.valid_of_ord_valid.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, Option.some b ≼ₒ Option.some a → ✓ b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Option.valid_of_ord_valid, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.valid_of_ord_valid.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, ✓ a → ✓ b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_op_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_op_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ Ψ : Nat → A → M) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard) (fun (a a_1 : Nat) => Iris.DFrac.discard) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_snoc_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_snoc_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : Nat → A → M) (l : List A) (a : A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard) ([]) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_filter_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_filter_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (φ : A → Bool) (Φ : A → M) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun n => n % 2 == 0 : Nat → Bool) (fun (a : Nat) => Iris.DFrac.discard) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Option.some_mk_ord, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_mk_ord.h8 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {a₁ a₂ : α} {b₁ b₂ : β},
        Option.some a₁ ≼ₒ Option.some a₂ ∧ Option.some b₁ ≼ₒ Option.some b₂ := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.dist_inr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_inr.h7 : Not
      (∀ {α β : Type} [inst : Iris.OFE α] [inst_1 : Iris.OFE β] {n : Nat} {x y : β},
        @Iris.OFE.Dist (Sum α β) (@Iris.OFE.instSum α β inst inst_1) n (@Sum.inr α β x) (@Sum.inr α β y)) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (@Iris.ORA.toOFE Iris.DFrac (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac)) (@Iris.ORA.toOFE Iris.DFrac (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.Option.bind_equiv, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Option.bind_equiv.h7 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst : Iris.OFE β] {x : Option α} {f g : α → Option β}, x.bind f = x.bind g := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (Option.some Iris.DFrac.discard) (fun (a : Iris.DFrac) => Option.none) (fun (a : Iris.DFrac) => Option.some Iris.DFrac.discard)) (by
  decide +kernel)

-- Iris.Std.LawfulBigOp.assoc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.assoc.h4 : ¬∀ {PROP : Type} {f : PROP → PROP → PROP} {unit : outParam PROP} {eq : outParam (PROP → PROP → Prop)} {a b c : PROP},
        eq (f (f a b) c) (f a (f b c)) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a - b : Nat → Nat → Nat) (0) (fun (a n : Nat) => n = 0) (1) (0) (0)) (by
  decide +kernel)

-- Iris.OFE.dist_snd, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_snd.h7 : ¬∀ {α β : Type} {n : Nat} [inst : Iris.OFE α] [inst : Iris.OFE β] {x y : α × β}, Iris.OFE.Dist n x.snd y.snd := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (0) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) ((Iris.DFrac.discard, Iris.DFrac.discard)) ((Iris.DFrac.discard, Iris.DFrac.own 1))) (by
  nofun)

-- Iris.OFE.dist_fst, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_fst.h7 : ¬∀ {α β : Type} {n : Nat} [inst : Iris.OFE α] [inst_1 : Iris.OFE β] {x y : α × β}, Iris.OFE.Dist n x.fst y.fst := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (0) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) ((Iris.DFrac.discard, Iris.DFrac.discard)) ((Iris.DFrac.own 1, Iris.DFrac.discard))) (by
  nofun)

-- FracAuth.auth_dfrac_op_validN, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.auth_dfrac_op_validN.h7 : ¬∀ {A : Type} [inst : Iris.ORA A] {n : Nat} {dq1 dq2 : Iris.DFrac} {a b : A}, ✓ dq1 • dq2 ∧ Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Algebra.MonoidOps.op_left_comm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.MonoidOps.op_left_comm.h4 : ¬∀ {M : Type} [inst : Iris.OFE M] {unit : M} {op : M → M → M} {a b c : M}, op a (op b c) = op b (op a c) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (fun (a : Iris.DFrac) =>
      if a = Iris.DFrac.discard then fun (a : Iris.DFrac) => Iris.DFrac.discard
      else fun (a : Iris.DFrac) => Iris.DFrac.own 1) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Ordered.OrderN.succ, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderN.succ.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x y : α}, x ≼ₒ{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.op_mono_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_mono_right.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {x y : α} (z : α), z • x ≼ z • y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.Ordered.OrderN.ordNR, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderN.ordNR.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x y : α}, x ≼ₒ*{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- FracAuth.agreeN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.agreeN.h6 : ¬∀ {A : Type} [inst : Iris.ORA A] {n : Nat} {dq : Iris.DFrac} {a b : A}, Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- List.Forall₂.drop, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.drop.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l : List α} {k : List β} (m : Nat), List.Forall₂ R (List.drop m l) (List.drop m k) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([0]) (0)) (by
  decide +kernel)

-- FracAuth.auth_dfrac_op_valid, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.auth_dfrac_op_valid.h6 : ¬∀ {A : Type} [inst : Iris.ORA A] {dq1 dq2 : Iris.DFrac} {a b : A}, ✓ dq1 • dq2 ∧ a = b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  simp)

-- Iris.Ordered.Order.ordN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.Order.ordN.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x y : α}, x ≼ₒ{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.inc0_of_incN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.inc0_of_incN.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y : α}, x ≼{0} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- List.exists_of_forall₂_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_of_forall₂_cons.h6 : ¬∀ {α α_1 : Type} {R : α → α_1 → Prop} {l₁ : List α} {l₂ : List α_1} {x : α},
        ∃ (y : α_1), ∃ (l₂' : List α_1), l₂ = y :: l₂' ∧ R x y ∧ List.Forall₂ R l₁ l₂' := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([]) (0)) (by
  simp)

-- Iris.Ordered.OrderNR.succ, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderNR.succ.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x y : α}, x ≼ₒ*{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.UFracAuth.agreeN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.UFracAuth.agreeN.h6 : ¬∀ {A : Type} [inst : Iris.ORA A] {n : Nat} {p : Iris.Qp} {a b : A}, Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Std.LawfulBigOp.comm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.comm.h4 : ¬∀ {PROP : Type} {f : PROP → PROP → PROP} {unit : outParam PROP} {eq : outParam (PROP → PROP → Prop)} {a b : PROP},
        eq (f a b) (f b a) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a - b : Nat → Nat → Nat) (0) (fun (a n : Nat) => n = 0) (0) (1)) (by
  decide +kernel)

-- Iris.Option.some_incN_some_of_dist, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_incN_some_of_dist.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Option.some a ≼{n} Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.some_ordN_some_of_dist_or_ordN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_ordN_some_of_dist_or_ordN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Option.some a ≼ₒ{n} Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.some_incN_some_of_incN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_incN_some_of_incN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Option.some a ≼{n} Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.op_mono_left_ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_mono_left_ord.h5 : ¬∀ {α : Type} [self : Iris.ORA α] {x y : α} (z : α), x • z ≼ₒ y • z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- LawfulAddLT.lt_iff_exists_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.LawfulAddLT.lt_iff_exists_add.h3 : ¬∀ {α : Type} {inst : Add α} {inst_1 : LT α} {x y : α}, x < y ↔ ∃ (z : α), y = x + z := fun hc_h => absurd (@hc_h (Nat) (instAddNat) (instLTNat) (0) (0)) (by
  simp)

-- Iris.ORA.validN_op_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_op_right.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α} {y : α}, ✓{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.dist_of_some_dist_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.dist_of_some_dist_some.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, Iris.OFE.Dist n x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Std.LawfulBigOp.right_id, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.right_id.h5 : ¬∀ {PROP : Type} {f : PROP → PROP → PROP} {unit : PROP} {eq : PROP → PROP → Prop} {a : PROP}, eq (f a unit) a := fun hc_h => absurd (@hc_h (Nat) (fun a b => a - b : Nat → Nat → Nat) (0) (fun a b => a < b : Nat → Nat → Prop) (0)) (by
  decide +kernel)

-- Iris.Std.LawfulBigOp.left_id, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.left_id.h4 : ¬∀ {PROP : Type} {f : PROP → PROP → PROP} {unit : outParam PROP} {eq : outParam (PROP → PROP → Prop)} {a : PROP},
        eq (f unit a) a := fun hc_h => absurd (@hc_h (Nat) (fun a b => a - b : Nat → Nat → Nat) (0) (fun (a n : Nat) => n = 0) (1)) (by
  decide +kernel)

-- Iris.Option.some_inc_some_of_inc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_inc_some_of_inc.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, Option.some a ≼ Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.pcore_l, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_l.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x cx : α}, cx • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.Valid.validN, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.Valid.validN.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {n : Nat}, ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (0)) (by
  nofun)

-- Iris.Agree.Raw.mem_of_forall_dist, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Agree.Raw.mem_of_forall_dist.h4 : ¬∀ {α : Type} [inst : Iris.OFE α] {a : α} {l : List α}, a ∈ l := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) ([])) (by
  decide +kernel)

-- Iris.ORA.pcore_op_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_left.h4 : ¬∀ {α : Type} [self : Iris.ORA α] {x cx : α}, cx • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Option.eq_none_of_op_eq_none_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.eq_none_of_op_eq_none_right.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : Option α} {y : Option α}, y = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Option.none) (Option.some Iris.DFrac.discard)) (by
  decide +kernel)

-- Iris.Option.eq_none_of_op_eq_none_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.eq_none_of_op_eq_none_left.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : Option α} {y : Option α}, x = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Option.some Iris.DFrac.discard) (Option.none)) (by
  decide +kernel)

-- Iris.Option.eq_or_inc_of_some_inc_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.eq_or_inc_of_some_inc_some.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, a = b ∨ a ≼ b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Std.Idempotent.idem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.Idempotent.idem.h3 : ¬∀ {α : Type} {R : Iris.Std.Relation α} {f : α → α → α} {x : α}, R (f x x) x := fun hc_h => absurd (@hc_h (Nat) (fun (a n : Nat) => n = 0) (fun a b => a - b : Nat → Nat → Nat) (1)) (by
  decide +kernel)

-- Iris.ORA.valid0_of_validN, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.valid0_of_validN.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α}, ✓{0} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.pcore_op_left_L, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_left_L.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x cx : α}, cx • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.pcore_op_right_L, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_right_L.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x cx : α}, x • cx = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ValidAt.le_rfl, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Iris.ValidAt.le_rfl.h3.der.{u_1} : ∀ {M : Type u_1} [inst : Iris.UORA M] {n : Nat} {v : @Iris.ValidAt M inst n}, @LE.le Nat instLENat n n := by
  (intros; omega)
theorem HypCheckProof.Iris.ValidAt.le_rfl.h3.{u_1} : ∀ {M : Type u_1} [inst : Iris.UORA M] {n : Nat} {v : @Iris.ValidAt M inst n},
      @Eq (@Iris.ValidAt M inst n) (@Iris.ValidAt.le M inst n n (@HypCheckProof.Iris.ValidAt.le_rfl.h3.der M inst n v) v) v := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Iris.ValidAt.le_rfl hc_x0 hc_x1 hc_x2 (@HypCheckProof.Iris.ValidAt.le_rfl.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Iris.IsTotal.total, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IsTotal.total.h3 : ¬∀ {α : Type} {inst : Iris.OFE α} {inst_1 : Iris.PCore α} (x : α), ∃ (cx : α), Iris.PCore.pcore x = Option.some cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toPCore) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.some_inc_some_of_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_inc_some_of_eq.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, Option.some a ≼ Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.CoreId.of_pcore_eq_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.CoreId.of_pcore_eq_some.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {y : α}, Iris.ORA.CoreId y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  exact fun hc_c =>
    absurd (hc_c.core_id)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Std.LawfulFiniteMap.NoDupKeys_noDup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulFiniteMap.NoDupKeys_noDup.h3 : ¬∀ {K V : Type} {L : List (K × V)}, L.Nodup := fun hc_h => absurd (@hc_h (Nat) (Nat) ([(0, 0), (0, 0)])) (by
  decide +kernel)

-- Vector.toList_ofList, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toList_ofList.h3 : ¬∀ {α : Type} {n : Nat} {l : List α}, l.length = n := fun hc_h => absurd (@hc_h (Nat) (0) ([0])) (by
  decide +kernel)

-- Iris.ORA.op_core, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_core.h2 : ¬∀ {α : Type} [inst : Iris.ORA α] (x : α), x • Iris.PCore.core x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Agree.Raw.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Agree.Raw.ext.h3 : ¬∀ {α : Type} {x y : Iris.Agree.Raw α}, x = y := fun hc_h => absurd (@hc_h (Nat) ({ car := [0], not_nil := of_decide_eq_true (id (Eq.refl Bool.true)) : Iris.Agree.Raw Nat }) ({ car := [1], not_nil := of_decide_eq_true (id (Eq.refl Bool.true)) : Iris.Agree.Raw Nat })) (by
  simp)

-- Iris.DiscreteO.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.DiscreteO.ext.h3 : ¬∀ {α : Type} {x y : Iris.DiscreteO α}, x = y := fun hc_h => absurd (@hc_h (Nat) ({ car := 0 : Iris.DiscreteO Nat }) ({ car := 1 : Iris.DiscreteO Nat })) (by
  simp)

-- Iris.ORA.core_op_L, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.core_op_L.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α}, Iris.PCore.core x • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.CoreId.core_id, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.CoreId.core_id.h3 : ¬∀ {α : Type} {inst : Iris.ORA α} {x : α}, Iris.PCore.pcore x = Option.some x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.IsUnit.unit_valid, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IsUnit.unit_valid.h3 : ¬∀ {α : Type} {inst : Iris.ORA α} {ε : α}, ✓ ε := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac)) (by
  nofun)

-- Rat.mul_div_cancel_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mul_div_cancel_left.h2 : ¬∀ {a b : Rat}, a * (b / a) = b := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Iris.HeapLang.Loc.fresh_fresh, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.HeapLang.Loc.fresh_fresh.h2 : ¬∀ (ls : List Iris.HeapLang.Loc) {i : Int}, ¬Iris.HeapLang.Loc.fresh ls + i ∈ ls := fun hc_h => absurd (@hc_h ([{ n := 0 : Iris.HeapLang.Loc }]) (-1)) (by
  decide +kernel)

-- Iris.MonoNat.lb_op_le_l, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MonoNat.lb_op_le_l.h2 : ¬∀ (n n' : Iris.MaxNat), (◯MN n) = (◯MN n') • ◯MN n := fun hc_h => absurd (@hc_h ({ toNat := 0 : Iris.MaxNat }) ({ toNat := 1 : Iris.MaxNat })) (by
  nofun)

-- Iris.MonoZ.lb_mono_ord, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MonoZ.lb_mono_ord.h2 : ¬∀ (n1 n2 : Iris.MaxInt), (◯MZ n1) ≼ₒ ◯MZ n2 := fun hc_h => absurd (@hc_h ({ toInt := 0 : Iris.MaxInt }) ({ toInt := -1 : Iris.MaxInt })) (by
  nofun)

-- List.mem_le_foldr_max, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_le_foldr_max.h2 : ¬∀ (x : Int) (L : List Int), x ≤ List.foldr Max.max 0 L := fun hc_h => absurd (@hc_h (1) ([])) (by
  decide +kernel)

-- Iris.DFrac.valid_own_op, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.DFrac.valid_own_op.h2 : ¬∀ {dq : Iris.DFrac} {q : Iris.Qp}, q.val < 1 := fun hc_h => absurd (@hc_h (Iris.DFrac.discard : Iris.DFrac) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }))) (by
  decide +kernel)

