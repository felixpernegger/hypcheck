import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- List.Forall₂.set, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.set.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β} {l : List α} {k : List β},
        List.Forall₂ R l k → ∀ (i : Nat), List.Forall₂ R (l.set i a) (k.set i b) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) ([0]) ([1]) (by
  decide) (0)) (by
  decide +kernel)

-- List.Forall₂.set, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Forall₂.set.h8.inst : ¬List.Forall₂ (fun (a b : Nat) => a < b) ([].set 0 0) ([0].set 0 1) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Forall₂.set.h8.prem0 : (fun (a b : Nat) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.Forall₂.set.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β},
        R a b → ∀ {l : List α} {k : List β} (i : Nat), List.Forall₂ R (l.set i a) (k.set i b) := fun hc_h => HypCheckProof.List.Forall₂.set.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => a < b) (0) (1) HypCheckProof.List.Forall₂.set.h8.prem0 ([]) ([0]) (0))

-- FracAuth.includedN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.includedN.h8 : ¬∀ {A : Type} [inst : Iris.ORA A] [inst_1 : Iris.OrdInc A] {n : Nat} {dq : Iris.DFrac} {q : Iris.Qp} {a b : A},
        Option.some b ≼{n} Option.some a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (0) (Iris.DFrac.discard : Iris.DFrac) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- List.Forall₂.append, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.append.h7 : ¬∀ {α α_1 : Type} {R : α → α_1 → Prop} {l₁ l₁' : List α} {l₂ l₂' : List α_1},
        List.Forall₂ R l₁' l₂' → List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂') := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([]) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Forall₂.append, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.append.h8 : ¬∀ {α α_1 : Type} {R : α → α_1 → Prop} {l₁ l₁' : List α} {l₂ l₂' : List α_1},
        List.Forall₂ R l₁ l₂ → List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂') := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([]) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- FracAuth.ordN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.ordN.h8 : ¬∀ {A : Type} [inst : Iris.ORA A] [inst_1 : Iris.IncOrd A] {n : Nat} {dq : Iris.DFrac} {q : Iris.Qp} {a b : A},
        Option.some b ≼ₒ{n} Option.some a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (0) (Iris.DFrac.discard : Iris.DFrac) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.UFracAuth.ordN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.UFracAuth.ordN.h8 : ¬∀ {A : Type} [inst : Iris.ORA A] [inst_1 : Iris.IncOrd A] {n : Nat} {p q : Iris.Qp} {a b : A},
        Option.some b ≼ₒ{n} Option.some a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (0) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Ordered.OrderN.le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderN.le.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n n' : Nat} {x y : α}, n' ≤ n → x ≼ₒ{n'} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.CMRAData.pcore_op_mono_of_pcore_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.CMRAData.pcore_op_mono_of_pcore_mono.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] [inst_2 : Iris.PCore α],
        (∀ {x y cx : α},
            x ≼ y → Iris.PCore.pcore x = Option.some cx → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ cx ≼ cy) →
          ∀ {x cx : α} (y : α), ∃ (cy : α), Iris.PCore.pcore (x • y) = Option.some (cx • cy) := fun hc_h => absurd (@hc_h (Iris.Qp : Type) (Iris.instCMRAQp.toOFE) (Iris.instCMRAQp.toOp) (Iris.instCMRAQp.toPCore) (by
  simp) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }))) (by
  simp)

-- Iris.ORA.incN_of_incN_le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.incN_of_incN_le.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n n' : Nat} {x y : α}, n' ≤ n → x ≼{n'} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.ORA.discrete_inc_l, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.discrete_inc_l.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α} [HD : Iris.OFE.DiscreteE x], ✓{0} y → x ≼ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) _ (by
  rfl)) (by
  nofun)

-- Iris.Valid.validN_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Valid.validN_ne.h6 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.Valid α] {n : Nat} {x y : α}, ✓{n} x → ✓{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toValid) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Valid.validN_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Valid.validN_ne.h7 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.Valid α] {n : Nat} {x y : α}, Iris.OFE.Dist n x y → ✓{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toValid) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.filter_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.filter_ne.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {p : α → Bool},
        (∀ (a b : α), Iris.OFE.Dist n a b → p a = p b) →
          ∀ {l k : List α}, Iris.OFE.Dist n (List.filter p l) (List.filter p k) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (fun (a : Iris.DFrac) => Bool.true) (by
  simp) ([]) ([Iris.DFrac.discard])) (by
  nofun)

-- Iris.OFE.dist_some_inv_r, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_some_inv_r.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {mx my : Option α} {y : α},
        my = Option.some y → ∃ (x : α), mx = Option.some x ∧ Iris.OFE.Dist n x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Option.none) _ (Iris.DFrac.discard : Iris.DFrac) rfl) (by
  simp)

-- Iris.OFE.dist_some_inv_r, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_some_inv_r.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {mx my : Option α} {y : α},
        Iris.OFE.Dist n mx my → ∃ (x : α), mx = Option.some x ∧ Iris.OFE.Dist n x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Option.none) (Option.none) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  simp)

-- Iris.OFE.Dist.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.trans.h6 : ¬∀ {α : Type} {y z : α} [inst : Iris.OFE α] {n : Nat} {x : α}, Iris.OFE.Dist n y z → Iris.OFE.Dist n x z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.OFE.Dist.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.trans.h7 : ¬∀ {α : Type} {y z : α} [inst : Iris.OFE α] {n : Nat} {x : α}, Iris.OFE.Dist n x y → Iris.OFE.Dist n x z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.ORA.pcore_ne', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_ne'.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y cx : α},
        Iris.PCore.pcore x = Option.some cx → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ Iris.OFE.Dist n cx cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  decide)) (by
  (have _i : ∀ (α : Type) [BEq α] [LawfulBEq α], DecidableEq α := @instDecidableEqOfLawfulBEq; decide))

-- Iris.ORA.pcore_ne', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_ne'.h7 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y cx : α},
        Iris.OFE.Dist n x y → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ Iris.OFE.Dist n cx cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.OFE.Dist.le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.le.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] {m n : Nat} {x y : α}, m ≤ n → Iris.OFE.Dist m x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.Prod.instCoreIdPair, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.instCoreIdPair.h6 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {x : α} {y : β} [inst_2 : Iris.ORA.CoreId y],
        Iris.ORA.CoreId (x, y) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) _) (by
  exact fun hc_c =>
    absurd (hc_c.core_id)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Prod.instCoreIdPair, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.instCoreIdPair.h7 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {x : α} {y : β} [inst_2 : Iris.ORA.CoreId x],
        Iris.ORA.CoreId (x, y) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) _) (by
  exact fun hc_c =>
    absurd (hc_c.core_id)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Ordered.OrderN.validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderN.validN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.MaxPrefixList.toMaxPrefixList_op_validN_aux, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MaxPrefixList.toMaxPrefixList_op_validN_aux.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {l1 l2 : List α},
        l1.length ≤ l2.length → Iris.OFE.Dist n l2 (l1 ++ List.drop l1.length l2) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) ([Iris.DFrac.discard]) ([Iris.DFrac.own 1]) (by
  decide)) (by
  nofun)

-- Iris.ORA.pcore_mono_ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_mono_ord.h5 : ¬∀ {α : Type} [self : Iris.ORA α] {x y cx : α},
        Iris.PCore.pcore x = Option.some cx → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ cx ≼ₒ cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.MonoList.prefix_getElem?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MonoList.prefix_getElem?.h5 : ¬∀ {α : Type} {l1 l2 : List α} {i : Nat} {a : α}, l1[i]? = Option.some a → l2[i]? = Option.some a := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Iris.MonoList.prefix_getElem?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MonoList.prefix_getElem?.h6 : ¬∀ {α : Type} {l1 l2 : List α} {i : Nat} {a : α}, l1 <+: l2 → l2[i]? = Option.some a := fun hc_h => absurd (@hc_h (Nat) ([]) ([]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.Relation.TransGen.head', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Relation.TransGen.head'.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, FromMathlib.Relation.ReflTransGen r b c → Relation.TransGen r a c := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- FromMathlib.Relation.TransGen.head', hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.FromMathlib.Relation.TransGen.head'.h6.inst : ¬Relation.TransGen (fun (a b : Nat) => a < b) 0 0 := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.FromMathlib.Relation.TransGen.head'.h6.prem0 : (fun (a b : Nat) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.FromMathlib.Relation.TransGen.head'.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, r a b → Relation.TransGen r a c := fun hc_h => HypCheckProof.FromMathlib.Relation.TransGen.head'.h6.inst (@hc_h (Nat) (fun (a b : Nat) => a < b) (0) (1) (0) HypCheckProof.FromMathlib.Relation.TransGen.head'.h6.prem0)

-- Iris.Option.isSome_monoN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_monoN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {ma mb : Option α}, ma.isSome = Bool.true → mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Option.some Iris.DFrac.discard) (Option.none) (by
  decide)) (by
  decide +kernel)

-- Iris.Option.isSome_monoN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_monoN.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {ma mb : Option α}, ma ≼{n} mb → mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Option.none) (Option.none) (by
  rfl)) (by
  decide +kernel)

-- FromMathlib.Nodup.map_on, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Nodup.map_on.h4 : ¬∀ {α β : Type} {l : List α} {f : α → β}, l.Nodup → (List.map f l).Nodup := fun hc_h => absurd (@hc_h (Nat) (Nat) ([0, 1]) (fun _ => 0 : Nat → Nat) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.Nodup.map_on, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.FromMathlib.Nodup.map_on.h5.inst : ¬(List.map (fun (n : Nat) => n + 1) [0, 0]).Nodup := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.FromMathlib.Nodup.map_on.h5.prem0 : ∀ (x : Nat), x ∈ [0, 0] → ∀ (y : Nat), y ∈ [0, 0] → (fun (n : Nat) => n + 1) x = (fun (n : Nat) => n + 1) y → x = y := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.FromMathlib.Nodup.map_on.h5 : ¬∀ {α β : Type} {l : List α} {f : α → β},
        (∀ (x : α), x ∈ l → ∀ (y : α), y ∈ l → f x = f y → x = y) → (List.map f l).Nodup := fun hc_h => HypCheckProof.FromMathlib.Nodup.map_on.h5.inst (@hc_h (Nat) (Nat) ([0, 0]) (fun (n : Nat) => n + 1) HypCheckProof.FromMathlib.Nodup.map_on.h5.prem0)

-- List.nodup_map_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_map_of_injective.h4 : ¬∀ {A B : Type} {f : A → B} {l : List A}, l.Nodup → (List.map f l).Nodup := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun _ => 0 : Nat → Nat) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- Iris.Option.exclusive_some_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exclusive_some_left.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} {mb : Option α}, ✓ Option.some a • mb → mb = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Option.some Iris.DFrac.discard) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Iris.Option.exclusive_some_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exclusive_some_left.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} [inst : Iris.ORA.Exclusive a] {mb : Option α}, mb = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) _ (Option.some Iris.DFrac.discard)) (by
  decide +kernel)

-- Iris.Option.isSome_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_mono.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {ma mb : Option α}, ma.isSome = Bool.true → mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Option.some Iris.DFrac.discard) (Option.none) (by
  decide)) (by
  decide +kernel)

-- Iris.Option.isSome_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_mono.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {ma mb : Option α}, ma ≼ mb → mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Option.none) (Option.none) (by
  rfl)) (by
  decide +kernel)

-- Iris.Option.exclusive_some_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exclusive_some_right.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} {mb : Option α}, ✓ mb • Option.some a → mb = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Option.some Iris.DFrac.discard) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Iris.Option.exclusive_some_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exclusive_some_right.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} [inst : Iris.ORA.Exclusive a] {mb : Option α}, mb = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) _ (Option.some Iris.DFrac.discard)) (by
  decide +kernel)

-- Iris.list_fmap_ext_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.list_fmap_ext_ne.h8 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst : Iris.OFE β] {n : Nat} {f g : α → β} {l : List α},
        Iris.OFE.Dist n (List.map f l) (List.map g l) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (0) (fun (a : Iris.DFrac) => Iris.DFrac.discard) (fun (a : Iris.DFrac) => Iris.DFrac.own 1) ([Iris.DFrac.discard])) (by
  nofun)

-- Iris.ORA.opM_left_dist, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.opM_left_dist.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y : α} (z : Option α),
        Iris.OFE.Dist n (x •? z) (y •? z) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Option.none)) (by
  nofun)

-- Iris.cons_dist_inj, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.cons_dist_inj.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {x y : α} {l k : List α}, Iris.OFE.Dist n x y ∧ Iris.OFE.Dist n l k := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) ([]) ([Iris.DFrac.discard])) (by
  nofun)

-- Iris.OFE.Dist.op_r, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.op_r.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y z : α}, Iris.OFE.Dist n (x • y) (x • z) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.ord0_of_ordN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.ord0_of_ordN.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x y : α}, x ≼ₒ{0} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.op?_monoN_left_ord, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op?_monoN_left_ord.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α} (mz : Option α), x •? mz ≼ₒ{n} y •? mz := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Option.none)) (by
  nofun)

-- Iris.DFracAgree.mk_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.DFracAgree.mk_inj.h6 : ¬∀ {A : Type} [inst : Iris.OFE A] {d₁ d₂ : Iris.DFrac} {a₁ a₂ : A}, d₁ = d₂ ∧ a₁ = a₂ := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Std.Associative.assoc, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.Associative.assoc.h3 : ¬∀ {α : Type} {R : Iris.Std.Relation α} {f : α → α → α} {x y z : α}, R (f (f x y) z) (f x (f y z)) := fun hc_h => absurd (@hc_h (Nat) (fun (a n : Nat) => n = 0) (fun a b => a - b : Nat → Nat → Nat) (1) (0) (0)) (by
  decide +kernel)

-- Iris.Std.Commutative.comm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.Commutative.comm.h4 : ¬∀ {α β : Type} {R : Iris.Std.Relation α} {f : β → β → α} {x y : β}, R (f x y) (f y x) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun (a n : Nat) => n = 0) (fun a b => a - b : Nat → Nat → Nat) (0) (1)) (by
  decide +kernel)

-- List.Forall₂.getElem?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.getElem?.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l : List α} {k : List β} (i : Nat), Option.Forall₂ R l[i]? k[i]? := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([0]) (0)) (by
  nofun)

-- Iris.OFE.dist_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_some.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {mx : Option α} {y : α}, ∃ (z : α), mx = Option.some z ∧ Iris.OFE.Dist n y z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Option.none) (Iris.DFrac.discard : Iris.DFrac)) (by
  simp)

-- Iris.Agree.Raw.map'_sameElems, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Agree.Raw.map'_sameElems.h5 : ¬∀ {α β : Type} {f : α → β} {x y : Iris.Agree.Raw α}, (Iris.Agree.Raw.map' f x).SameElems (Iris.Agree.Raw.map' f y) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n + 1 : Nat → Nat) ({ car := [0], not_nil := of_decide_eq_true (id (Eq.refl Bool.true)) : Iris.Agree.Raw Nat }) ({ car := [1], not_nil := of_decide_eq_true (id (Eq.refl Bool.true)) : Iris.Agree.Raw Nat })) (by
  nofun)

-- Iris.Option.some_incN_some_of_dist_or_incN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_incN_some_of_dist_or_incN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Option.some a ≼{n} Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.Dist.of_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.of_eq.h5 : ¬∀ {α : Type} {n : Nat} [inst : Iris.OFE α] {x y : α}, Iris.OFE.Dist n x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (0) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- List.Forall₂.of_getElem?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.of_getElem?.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l : List α} {k : List β}, List.Forall₂ R l k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([0])) (by
  decide +kernel)

-- Iris.ORA.op_mono_right_ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_mono_right_ord.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α} (z : α), z • x ≼ₒ z • y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.GenMap.validN_singleton_map_in, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.GenMap.validN_singleton_map_in.h5 : ¬∀ (β : Type) [inst : Iris.ORA β] (x : Nat) (y : β) (n : Nat), ✓{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (0)) (by
  nofun)

-- Iris.Option.some_ordN_some_of_ordN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_ordN_some_of_ordN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Option.some a ≼ₒ{n} Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Excl.excl_dist_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Excl.excl_dist_inj.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {a b : α} {n : Nat}, Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (0)) (by
  nofun)

-- Iris.Option.isSome_of_some_incN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_of_some_incN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a : α} {mb : Option α}, mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Option.none)) (by
  decide +kernel)

-- FromMathlib.Relation.ReflTransGen.cases_head, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Relation.ReflTransGen.cases_head.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, a = b ∨ ∃ (c : α), r a c ∧ FromMathlib.Relation.ReflTransGen r c b := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) (Bool.false) (Bool.true)) (by
  simp)

-- IdentityFree.id_free, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IdentityFree.id_free.h2 : ¬∀ {α : Type} {inst : Add α} {a b : α}, ¬Add.add a b = a := fun hc_h => absurd (@hc_h (Nat) (instAddNat) (0) (0)) (by
  decide +kernel)

-- Iris.Option.some_inc_some_of_eq_or_inc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_inc_some_of_eq_or_inc.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, Option.some a ≼ Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.pcore_op_self', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_self'.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {cx : α}, cx • cx = cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.pcore_idem_L, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_idem_L.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {cx : α}, Iris.PCore.pcore cx = Option.some cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Option.some_ord_some_of_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_ord_some_of_eq.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, Option.some a ≼ₒ Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.forall₂_eq_of_forall₂_dist, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.forall₂_eq_of_forall₂_dist.h4 : ¬∀ {α : Type} [inst : Iris.OFE α] {l k : List α}, l = k := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) ([]) ([Iris.DFrac.discard])) (by
  decide +kernel)

-- Iris.ORA.valid_op_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.valid_op_left.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {y : α}, ✓ x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.Option.validN_op_unit, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.validN_op_unit.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : Option α}, ✓{n} x • Iris.UORA.unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Option.some (Iris.DFrac.ownDiscard 1))) (by
  nofun)

-- Iris.SiProp.internalEq_soundness, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.SiProp.internalEq_soundness.h4 : ¬∀ {A : Type} [inst : Iris.OFE A] {x y : A}, x = y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.MaxPrefixList.toMaxPrefixList_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MaxPrefixList.toMaxPrefixList_inj.h4 : ¬∀ {α : Type} [inst : Iris.OFE α] {l1 l2 : List α}, l1 = l2 := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) ([]) ([Iris.DFrac.discard])) (by
  decide +kernel)

-- Nat.repeat_fixed, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.repeat_fixed.h3 : ¬∀ {α : Type} (f : α → α) {x : α} (k : Nat), x = Nat.repeat f k x := fun hc_h => absurd (@hc_h (Nat) (fun n => n + 1 : Nat → Nat) (0) (1)) (by
  decide +kernel)

-- Iris.MonoList.map_mk_prefix, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MonoList.map_mk_prefix.h3 : ¬∀ {α : Type} {l1 l2 : List α}, l1 <+: l2 := fun hc_h => absurd (@hc_h (Nat) ([0]) ([])) (by
  decide +kernel)

-- Iris.MonoList.map_mk_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MonoList.map_mk_inj.h3 : ¬∀ {α : Type} {l1 l2 : List α}, l1 = l2 := fun hc_h => absurd (@hc_h (Nat) ([]) ([0])) (by
  decide +kernel)

-- Iris.DiscreteO.eqv_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.DiscreteO.eqv_inj.h3 : ¬∀ {α : Type} {x y : α}, x = y := fun hc_h => absurd (@hc_h (Nat) (0) (1)) (by
  decide +kernel)

-- Iris.HeapLang.Loc.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.HeapLang.Loc.ext.h2 : ¬∀ {x y : Iris.HeapLang.Loc}, x = y := fun hc_h => absurd (@hc_h ({ n := 0 : Iris.HeapLang.Loc }) ({ n := 1 : Iris.HeapLang.Loc })) (by
  decide +kernel)

-- Iris.HeapLang.ProphId.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.HeapLang.ProphId.ext.h2 : ¬∀ {x y : Iris.HeapLang.ProphId}, x = y := fun hc_h => absurd (@hc_h ({ n := 0 : Iris.HeapLang.ProphId }) ({ n := 1 : Iris.HeapLang.ProphId })) (by
  decide +kernel)

-- Iris.UFrac.le_of_inc, hypothesis 2: necessary
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
theorem HypCheckProof.Iris.UFrac.le_of_inc.h2 : ¬∀ {x y : Iris.UFrac}, x.frac ≤ y.frac := fun hc_h => absurd (@hc_h ({ frac := (⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }) : Iris.UFrac }) ({ frac := (⟨1 / 2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }) : Iris.UFrac })) (by
  (simp <;> decide))
-/

