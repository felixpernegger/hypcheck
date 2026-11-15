import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- FromMathlib.Pairwise.forall, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Pairwise.forall.h3 : ¬∀ {α : Type} {l : List α} {R : α → α → Prop},
        List.Pairwise (fun (x1 x2 : α) => x1 ≠ x2) l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, b ∈ l → a ≠ b → R a b := fun hc_h => absurd (@hc_h (Nat) ([0, 1]) (fun a b => a < b : Nat → Nat → Prop) (by
  decide) (1) (by
  decide) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.Pairwise.forall, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.FromMathlib.Pairwise.forall.h4.gneg.{u_1} : ∀ {α : Type u_1} {l : List α} {R : α → α → Prop},
      (∀ {a b : α}, R a b ↔ a ≠ b) →
        ¬List.Pairwise (fun (x1 x2 : α) => x1 ≠ x2) l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, b ∈ l → a ≠ b → R a b := by
  (intros; simp_all; done)
theorem HypCheckProof.FromMathlib.Pairwise.forall.h4.{u_1} : ∀ {α : Type u_1} {l : List α} {R : α → α → Prop},
      (∀ {a b : α}, R a b ↔ a ≠ b) → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, b ∈ l → a ≠ b → R a b := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @FromMathlib.Pairwise.forall hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5 hc_x6 hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.FromMathlib.Pairwise.forall.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5 hc_x6 hc_x7 hc_x8 hc_x9)

-- FromMathlib.Pairwise.forall, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.FromMathlib.Pairwise.forall.h6.gneg.{u_1} : ∀ {α : Type u_1} {l : List α} {R : α → α → Prop},
      (∀ {a b : α}, R a b ↔ a ≠ b) →
        List.Pairwise (fun (x1 x2 : α) => x1 ≠ x2) l → ∀ ⦃a : α⦄, ¬a ∈ l → ∀ ⦃b : α⦄, b ∈ l → a ≠ b → R a b := by
  (intros; simp_all; done)
theorem HypCheckProof.FromMathlib.Pairwise.forall.h6.{u_1} : ∀ {α : Type u_1} {l : List α} {R : α → α → Prop},
      (∀ {a b : α}, R a b ↔ a ≠ b) → List.Pairwise (fun (x1 x2 : α) => x1 ≠ x2) l → ∀ ⦃a b : α⦄, b ∈ l → a ≠ b → R a b := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @FromMathlib.Pairwise.forall hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.FromMathlib.Pairwise.forall.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn hc_x7 hc_x8 hc_x9)

-- FromMathlib.Pairwise.forall, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.FromMathlib.Pairwise.forall.h8.gneg.{u_1} : ∀ {α : Type u_1} {l : List α} {R : α → α → Prop},
      (∀ {a b : α}, R a b ↔ a ≠ b) →
        List.Pairwise (fun (x1 x2 : α) => x1 ≠ x2) l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, ¬b ∈ l → a ≠ b → R a b := by
  (intros; simp_all; done)
theorem HypCheckProof.FromMathlib.Pairwise.forall.h8.{u_1} : ∀ {α : Type u_1} {l : List α} {R : α → α → Prop},
      (∀ {a b : α}, R a b ↔ a ≠ b) →
        List.Pairwise (fun (x1 x2 : α) => x1 ≠ x2) l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, a ≠ b → R a b := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x9
  exact Classical.byCases (fun hc_h => @FromMathlib.Pairwise.forall hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_h hc_x9) (fun hc_hn => @HypCheckProof.FromMathlib.Pairwise.forall.h8.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_hn hc_x9)

-- FromMathlib.Pairwise.forall, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Pairwise.forall.h9 : ¬∀ {α : Type} {l : List α} {R : α → α → Prop},
        (∀ {a b : α}, R a b ↔ a ≠ b) →
          List.Pairwise (fun (x1 x2 : α) => x1 ≠ x2) l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, b ∈ l → R a b := fun hc_h => absurd (@hc_h (Nat) ([0]) (fun a b => a ≠ b : Nat → Nat → Prop) (by
  rfl) (by
  decide) (0) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.inj_on_of_nodup_map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.inj_on_of_nodup_map.h4 : ¬∀ {α β : Type} {f : α → β} {l : List α} ⦃x : α⦄, x ∈ l → ∀ ⦃y : α⦄, y ∈ l → f x = f y → x = y := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun _ => 0 : Nat → Nat) ([0, 1]) (0) (by
  decide) (1) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- FromMathlib.inj_on_of_nodup_map, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.inj_on_of_nodup_map.h6 : ¬∀ {α β : Type} {f : α → β} {l : List α}, (List.map f l).Nodup → ∀ ⦃x y : α⦄, y ∈ l → f x = f y → x = y := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun _ => 0 : Nat → Nat) ([0]) (by
  decide) (1) (0) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- FromMathlib.inj_on_of_nodup_map, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.inj_on_of_nodup_map.h8 : ¬∀ {α β : Type} {f : α → β} {l : List α}, (List.map f l).Nodup → ∀ ⦃x : α⦄, x ∈ l → ∀ ⦃y : α⦄, f x = f y → x = y := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun _ => 0 : Nat → Nat) ([0]) (by
  decide) (0) (by
  decide) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- FromMathlib.inj_on_of_nodup_map, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.inj_on_of_nodup_map.h9 : ¬∀ {α β : Type} {f : α → β} {l : List α}, (List.map f l).Nodup → ∀ ⦃x : α⦄, x ∈ l → ∀ ⦃y : α⦄, y ∈ l → x = y := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n + 1 : Nat → Nat) ([0, 1]) (by
  decide) (0) (by
  decide) (1) (by
  decide)) (by
  decide +kernel)

-- Iris.Prod.map_ne, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.map_ne.h12 : ¬∀ {A A' B B' : Type} [inst : Iris.OFE A'] [inst_1 : Iris.OFE B'] {n : Nat} {x : A × B} {f f' : A → A'} {g g' : B → B'},
        (∀ (a : B), Iris.OFE.Dist n (g a) (g' a)) → Iris.OFE.Dist n (Prod.map f g x) (Prod.map f' g' x) := fun hc_h => absurd (@hc_h (Nat) (Iris.DFrac : Type) (Nat) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (0) ((0, 0)) (fun (a : Nat) => Iris.DFrac.discard) (fun (a : Nat) => Iris.DFrac.own 1) (fun (a : Nat) => Iris.DFrac.discard) (fun (a : Nat) => Iris.DFrac.discard) (by
  simp)) (by
  nofun)

-- Iris.Prod.map_ne, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.map_ne.h13 : ¬∀ {A A' B B' : Type} [inst : Iris.OFE A'] [inst_1 : Iris.OFE B'] {n : Nat} {x : A × B} {f f' : A → A'} {g g' : B → B'},
        (∀ (a : A), Iris.OFE.Dist n (f a) (f' a)) → Iris.OFE.Dist n (Prod.map f g x) (Prod.map f' g' x) := fun hc_h => absurd (@hc_h (Nat) (Iris.DFrac : Type) (Nat) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (0) ((0, 0)) (fun (a : Nat) => Iris.DFrac.discard) (fun (a : Nat) => Iris.DFrac.discard) (fun (a : Nat) => Iris.DFrac.discard) (fun (a : Nat) => Iris.DFrac.own 1) (by
  simp)) (by
  nofun)

-- Iris.Option.dist_of_ord_exclusive, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.dist_of_ord_exclusive.h7 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} [inst_1 : Iris.OrdInc α] [inst_2 : Iris.ORA.Exclusive a] {n : Nat} {b : α},
        ✓{n} b → Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) _ _ (0) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Nat.repeat_rel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.repeat_rel.h2 : ¬∀ {α : Type} {R : α → α → Prop} {f g : α → α},
        (∀ {x y : α}, R x y → R (f x) (f y)) →
          (∀ (z : α), R (f z) (g z)) → ∀ (k : Nat) (z : α), R (Nat.repeat f k z) (Nat.repeat g k z) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun n => n : Nat → Nat) (fun n => n + 1 : Nat → Nat) (by
  simp) (by
  simp) (0) (0)) (by
  decide +kernel)

-- Nat.repeat_rel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.repeat_rel.h6 : ¬∀ {α : Type} {R : α → α → Prop},
        Equivalence R →
          ∀ {f g : α → α},
            (∀ {x y : α}, R x y → R (f x) (f y)) → ∀ (k : Nat) (z : α), R (Nat.repeat f k z) (Nat.repeat g k z) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a = b : Nat → Nat → Prop) ((@Equivalence.mk (Nat) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega)))) (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat) (by
  simp) (1) (0)) (by
  decide +kernel)

-- FracAuth.included, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.included.h8 : ¬∀ {A : Type} [inst : Iris.ORA A] {q : Iris.Qp} [inst_1 : Iris.ORA.Discrete A] [inst_2 : Iris.OrdInc A]
        {dq : Iris.DFrac} {a b : A}, Option.some b ≼ Option.some a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) _ _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- FracAuth.ord, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.ord.h8 : ¬∀ {A : Type} [inst : Iris.ORA A] {q : Iris.Qp} [inst_1 : Iris.ORA.Discrete A] [inst_2 : Iris.IncOrd A]
        {dq : Iris.DFrac} {a b : A}, Option.some b ≼ₒ Option.some a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) _ _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.UFracAuth.included, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.UFracAuth.included.h8 : ¬∀ {A : Type} [inst : Iris.ORA A] [inst_1 : Iris.ORA.Discrete A] [inst_2 : Iris.OrdInc A] {q p : Iris.Qp} {a b : A},
        Option.some b ≼ Option.some a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ _ ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- List.Forall₂.inserts, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.inserts.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {k₁ : List α} {k₂ : List β} {l₁ : List α} {l₂ : List β},
        List.Forall₂ R l₁ l₂ → ∀ (i : Nat), List.Forall₂ R (List.inserts i k₁ l₁) (List.inserts i k₂ l₂) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([0]) ([0]) ([1]) (by
  decide) (0)) (by
  decide +kernel)

-- List.Forall₂.inserts, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.inserts.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {k₁ : List α} {k₂ : List β},
        List.Forall₂ R k₁ k₂ →
          ∀ {l₁ : List α} {l₂ : List β} (i : Nat), List.Forall₂ R (List.inserts i k₁ l₁) (List.inserts i k₂ l₂) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([]) (by
  decide) ([]) ([0]) (0)) (by
  decide +kernel)

-- Iris.Option.dist_of_inc_exclusive, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.dist_of_inc_exclusive.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} [inst_1 : Iris.ORA.Exclusive a] {n : Nat} {b : α},
        ✓{n} b → Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) _ (0) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.OFE.Dist.opM, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.opM.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x₁ x₂ : α} {y₁ y₂ : Option α},
        Iris.OFE.Dist n y₁ y₂ → Iris.OFE.Dist n (x₁ •? y₁) (x₂ •? y₂) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Option.none) (Option.none) (by
  rfl)) (by
  nofun)

-- Iris.OFE.Dist.opM, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.opM.h9 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x₁ x₂ : α} {y₁ y₂ : Option α},
        Iris.OFE.Dist n x₁ x₂ → Iris.OFE.Dist n (x₁ •? y₁) (x₂ •? y₂) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Option.none) (Option.some (Iris.DFrac.own 1)) (by
  rfl)) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {Φ Ψ : Nat → A → M} {l : List A},
        (∀ {i : Nat} {x : A}, l[i]? = Option.some x → Φ i x = Ψ i x) → Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard) (fun (a a_1 : Nat) => Iris.DFrac.discard) ([]) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.OFE.dist_pointwise_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_pointwise_lt.h7 : ¬∀ {β α : Type} [inst : Iris.OFE β] {n m : Nat} {f g : α → β},
        (∀ (a : α), Iris.OFE.DistLater n (f a) (g a)) → ∀ (a : α), Iris.OFE.Dist m (f a) (g a) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (0) (0) (fun (a : Nat) => Iris.DFrac.discard) (fun (a : Nat) => Iris.DFrac.own 1) (by
  simp) (0)) (by
  nofun)

-- Iris.OFE.dist_pointwise_lt, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_pointwise_lt.h8 : ¬∀ {β α : Type} [inst : Iris.OFE β] {n m : Nat} {f g : α → β}, m < n → ∀ (a : α), Iris.OFE.Dist m (f a) (g a) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (1) (0) (fun (a : Nat) => Iris.DFrac.discard) (fun (a : Nat) => Iris.DFrac.own 1) (by
  decide) (0)) (by
  nofun)

-- Iris.Std.Antisymmetric.antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.Antisymmetric.antisymm.h3 : ¬∀ {α : Type} {R : Iris.Std.Relation α} {S : outParam (Iris.Std.Relation α)} {x y : α}, S x y → S y x → R x y := fun hc_h => absurd (@hc_h (Nat) (fun (a x : Nat) => False) (fun (a n : Nat) => n = 0) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iris.Std.Antisymmetric.antisymm, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.Antisymmetric.antisymm.h6 : ¬∀ {α : Type} {R : Iris.Std.Relation α} {S : outParam (Iris.Std.Relation α)} [self : Iris.Std.Antisymmetric R S]
        {x y : α}, S y x → R x y := fun hc_h => absurd (@hc_h (Nat) (fun (a n : Nat) => n = 0) (fun (a n : Nat) => n = 0) (@Iris.Std.Antisymmetric.mk (Nat) (fun (a n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (a n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by (try dsimp only);   (intros; omega))) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iris.Std.Antisymmetric.antisymm, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.Antisymmetric.antisymm.h7 : ¬∀ {α : Type} {R : Iris.Std.Relation α} {S : outParam (Iris.Std.Relation α)} [self : Iris.Std.Antisymmetric R S]
        {x y : α}, S x y → R x y := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => if a = Bool.false then fun (b : Bool) => b = Bool.false else fun (b : Bool) => b = Bool.true) (fun (a b : Bool) => b = Bool.true) (@Iris.Std.Antisymmetric.mk (Bool) (fun (a : Bool) =>
      @ite (Bool → Prop) (@Eq Bool a Bool.false) (instDecidableEqBool a Bool.false)
        (fun (b : Bool) => @Eq Bool b Bool.false) fun (b : Bool) => @Eq Bool b Bool.true) (fun (a b : Bool) => @Eq Bool b Bool.true) (by (try dsimp only);   (intros; simp_all; done))) (Bool.false) (Bool.true) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- List.Forall₂.modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.modify.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {f : α → α} {g : β → β} {l : List α} {k : List β},
        List.Forall₂ R l k → ∀ (i : Nat), List.Forall₂ R (l.modify i f) (k.modify i g) := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun (a : Bool) (n : Nat) => n = 0) (not : Bool → Bool) (fun n => n + 1 : Nat → Nat) ([Bool.false]) ([0]) (by
  decide) (0)) (by
  decide +kernel)

-- List.Forall₂.modify, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.modify.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {f : α → α} {g : β → β},
        (∀ {a : α} {b : β}, R a b → R (f a) (g b)) →
          ∀ {l : List α} {k : List β} (i : Nat), List.Forall₂ R (l.modify i f) (k.modify i g) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) (by
  simp) ([]) ([0]) (0)) (by
  decide +kernel)

-- Iris.Std.LawfulBigOp.congr_r, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.congr_r.h7.inst : ¬(fun (a b : Nat) => a < b) ((fun (a b : Nat) => a - b) 0 0) ((fun (a b : Nat) => a - b) 0 1) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.congr_r.h7.prem0 : (fun (a b : Nat) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Iris.Std.LawfulBigOp.congr_r.h7 : ¬∀ {PROP : Type} {f : PROP → PROP → PROP} {unit : PROP} {eq : PROP → PROP → Prop} {b b' a : PROP},
        eq b b' → eq (f a b) (f a b') := fun hc_h => HypCheckProof.Iris.Std.LawfulBigOp.congr_r.h7.inst (@hc_h (Nat) (fun (a b : Nat) => a - b) (0) (fun (a b : Nat) => a < b) (0) (1) (0) HypCheckProof.Iris.Std.LawfulBigOp.congr_r.h7.prem0)

-- Iris.Std.LawfulBigOp.congr_r, hypothesis 8: necessary
/- FAILED: 3:549: simp_all made no progress | 4:772: simp_all made no progress | 3:549: simp_all made no progress | 4:772: simp_all made no progress | 5:572: simp_all made no progress | 13:849: simp_all made no progress | 5:572: simp_all made no progress | 13:849: simp_all made no progress
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.congr_r.h8 : ¬∀ {PROP : Type} {f : PROP → PROP → PROP} {unit : PROP} {eq : PROP → PROP → Prop} {b b' a : PROP}
        [inst : Iris.Std.LawfulBigOp f unit eq], eq (f a b) (f a b') := fun hc_h => absurd (@hc_h (Nat) (fun a b => a + b : Nat → Nat → Nat) (0) (fun a b => a = b : Nat → Nat → Prop) (0) (1) (0) (@Iris.Std.LawfulBigOp.mk (Nat) (fun (a b : Nat) => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; simp_all <;> omega)) (by (try dsimp only);   (intros; simp_all <;> omega)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done)))) (by
  decide +kernel)
-/

-- Iris.IncludedN.le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IncludedN.le.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n n' : Nat} {x y : α}, n' ≤ n → x ≼{n'} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.OFE.DistLater.dist_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.DistLater.dist_lt.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] {m n : Nat} {x y : α}, m < n → Iris.OFE.Dist m x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (1) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.OFE.DistLater.dist_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.DistLater.dist_lt.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] {m n : Nat} {x y : α}, Iris.OFE.DistLater n x y → Iris.OFE.Dist m x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  simp)) (by
  nofun)

-- Iris.OrdInc.ord_inc, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OrdInc.ord_inc.h7 : ¬∀ {α : Type} {inst : Iris.OFE α} {inst_1 : Iris.Op α} {inst_2 : Iris.Ordered α} [self : Iris.OrdInc α] {x y : α}, x ≼ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (Iris.DFrac.instCMRADFrac.toOrdered) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.some_ordN_some_of_dist_opM, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_ordN_some_of_dist_opM.h7 : ¬∀ {α : Type} [inst : Iris.ORA α] [inst_1 : Iris.IncOrd α] {n : Nat} {x y : α} {mz : Option α},
        Option.some y ≼ₒ{n} Option.some x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Option.none)) (by
  nofun)

-- Iris.OFE.dist_some_inv_l, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_some_inv_l.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {mx my : Option α} {x : α},
        mx = Option.some x → ∃ (y : α), my = Option.some y ∧ Iris.OFE.Dist n x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) _ (Option.none) (Iris.DFrac.discard : Iris.DFrac) rfl) (by
  simp)

-- Iris.OFE.dist_some_inv_l, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_some_inv_l.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {mx my : Option α} {x : α},
        Iris.OFE.Dist n mx my → ∃ (y : α), my = Option.some y ∧ Iris.OFE.Dist n x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Option.none) (Option.none) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  simp)

-- Iris.IncOrd.inc_ord, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IncOrd.inc_ord.h7 : ¬∀ {α : Type} {inst : Iris.OFE α} {inst_1 : Iris.Op α} {inst_2 : Iris.Ordered α} [self : Iris.IncOrd α] {x y : α},
        x ≼ₒ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (Iris.DFrac.instCMRADFrac.toOrdered) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.not_valid_of_exclN_inc, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.not_valid_of_exclN_inc.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α} [inst_1 : Iris.ORA.Exclusive x] {y : α}, ¬✓{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.own 1 : Iris.DFrac) _ (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- LeftCancelAdd.cancel_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.LeftCancelAdd.cancel_left.h6 : ¬∀ {α : Type} {inst : Add α} [self : LeftCancelAdd α] {x₁ x₂ : α} {y : α}, x₁ = x₂ := fun hc_h => absurd (@hc_h (Nat) (instAddNat) (@LeftCancelAdd.mk (Nat) (instAddNat) (by (try dsimp only);   (intros; omega))) (0) (1) (0)) (by
  decide +kernel)

-- Iris.ORA.validN_of_incN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_of_incN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.valid_of_inc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.valid_of_inc.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α}, ✓ y → ✓ x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Option.valid_of_inc_valid, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.valid_of_inc_valid.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, Option.some b ≼ Option.some a → ✓ b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Option.valid_of_inc_valid, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.valid_of_inc_valid.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, ✓ a → ✓ b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Std.LawfulPartialMap.zipWith_comm, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Iris.Std.LawfulPartialMap.zipWith_comm.h9.gneg.{u_1, u_2, u_3} : ∀ {K : Type u_3} {V : Type u_1} {M : Type u_1 → Type u_2} [inst : Iris.Std.LawfulPartialMap M K] {V' V'' : Type u_1}
      {f : V → V' → V''} {m₁ : M V} {m₂ : M V'},
      (¬∀ (v : V) (v' : V'), f v v' = f v v') → Iris.Std.PartialMap.zipWith f m₁ m₂ = Iris.Std.PartialMap.zipWith f m₁ m₂ := by
  (intros; simp_all; done)
theorem HypCheckProof.Iris.Std.LawfulPartialMap.zipWith_comm.h9.{u_1, u_2, u_3} : ∀ {K : Type u_3} {V : Type u_1} {M : Type u_1 → Type u_2} [inst : Iris.Std.LawfulPartialMap M K] {V' V'' : Type u_1}
      {f : V → V' → V''} {m₁ : M V} {m₂ : M V'}, Iris.Std.PartialMap.zipWith f m₁ m₂ = Iris.Std.PartialMap.zipWith f m₁ m₂ := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact Classical.byCases (fun hc_h => @Iris.Std.LawfulPartialMap.zipWith_comm hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h) (fun hc_hn => @HypCheckProof.Iris.Std.LawfulPartialMap.zipWith_comm.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Iris.Std.LawfulPartialMap.zipWith_comm.h9.derivable.{u_1, u_2, u_3} : ∀ {K : Type u_3} {V : Type u_1} {M : Type u_1 → Type u_2} [inst : Iris.Std.LawfulPartialMap M K] {V' V'' : Type u_1}
      {f : V → V' → V''} {m₁ : M V} {m₂ : M V'} (v : V) (v' : V'), f v v' = f v v' := by
  (intros; simp_all; done)

-- Iris.Algebra.BigOpL.bigOpL_comm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_comm.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {B : Type} (Φ : Nat → A → Nat → B → M) (l₁ : List A)
        (l₂ : List B), Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (Nat) (fun (a a_1 a_2 a_3 : Nat) => Iris.DFrac.discard) ([]) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_map_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_map_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {B : Type} (h : A → B) (Φ : Nat → B → M) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (Nat) (fun n => n + 1 : Nat → Nat) (fun (a a_1 : Nat) => Iris.DFrac.discard) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_filterMap_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_filterMap_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {B : Type} (h : A → Option B) (Φ : B → M) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (Nat) (fun _ => none : Nat → Option Nat) (fun (a : Nat) => Iris.DFrac.discard) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.HeapLang.Loc.add_le_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.HeapLang.Loc.add_le_mono.h4 : ¬∀ {l₁ l₂ : Iris.HeapLang.Loc} {i₁ i₂ : Int}, i₁ ≤ i₂ → l₁ + i₁ ≤ l₂ + i₂ := fun hc_h => absurd (@hc_h ({ n := 1 : Iris.HeapLang.Loc }) ({ n := 0 : Iris.HeapLang.Loc }) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Iris.HeapLang.Loc.add_le_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.HeapLang.Loc.add_le_mono.h5 : ¬∀ {l₁ l₂ : Iris.HeapLang.Loc} {i₁ i₂ : Int}, l₁ ≤ l₂ → l₁ + i₁ ≤ l₂ + i₂ := fun hc_h => absurd (@hc_h ({ n := 0 : Iris.HeapLang.Loc }) ({ n := 0 : Iris.HeapLang.Loc }) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Iris.ORA.pcore_ord_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_ord_self.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x cx : α} [inst_1 : Iris.Increasing x], cx ≼ₒ x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) _) (by
  nofun)

-- Iris.ORA.op_core_right_of_inc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_core_right_of_inc.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α} [inst_1 : Iris.ORA.CoreId x], x • y = y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) _) (by
  decide +kernel)

-- Iris.Algebra.BigOpL.bigOpL_nil, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_nil.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : Nat → A → M), Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.OFE.equiv_fst, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.equiv_fst.h6 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst : Iris.OFE β] {x y : α × β}, x.fst = y.fst := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) ((Iris.DFrac.discard, Iris.DFrac.discard)) ((Iris.DFrac.own 1, Iris.DFrac.discard))) (by
  decide +kernel)

-- Iris.Ordered.OrderNR.op_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderNR.op_left.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α} (z : α), x • z ≼ₒ*{n} y • z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.Included.incN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Included.incN.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y : α}, x ≼{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- List.Forall₂.take, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.take.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l : List α} {k : List β} (m : Nat), List.Forall₂ R (List.take m l) (List.take m k) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([0]) (1)) (by
  decide +kernel)

-- List.Forall₂.replicate, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.replicate.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β} (m : Nat), List.Forall₂ R (List.replicate m a) (List.replicate m b) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) (1)) (by
  decide +kernel)

-- Iris.ORA.validN_op_opM_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_op_opM_right.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α} {y : α} {mz : Option α}, ✓{n} y •? mz := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Option.some (Iris.DFrac.own 1))) (by
  nofun)

-- Iris.ORA.op_mono_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_mono_left.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {x y : α} (z : α), x • z ≼ y • z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.equiv_snd, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.equiv_snd.h6 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst : Iris.OFE β] {x y : α × β}, x.snd = y.snd := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) ((Iris.DFrac.discard, Iris.DFrac.discard)) ((Iris.DFrac.discard, Iris.DFrac.own 1))) (by
  decide +kernel)

-- Iris.Std.bigOp_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.bigOp_cons.h6 : ¬∀ {PROP : Type} {eq : PROP → PROP → Prop} {P : PROP} {Ps : List PROP} {f : PROP → PROP → PROP} {unit : PROP},
        eq (Iris.Std.bigOp f unit (P :: Ps)) (f P (Iris.Std.bigOp f unit Ps)) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) ([]) (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide +kernel)

-- Iris.Algebra.MonoidOps.op_comm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.MonoidOps.op_comm.h4 : ¬∀ {M : Type} {inst : Iris.OFE M} {op : M → M → M} {unit : outParam M} {a b : M}, op a b = op b a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a : Iris.DFrac) =>
      if a = Iris.DFrac.discard then fun (a : Iris.DFrac) => Iris.DFrac.discard
      else fun (a : Iris.DFrac) => Iris.DFrac.own 1) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.OFE.eq_dist_1, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.eq_dist_1.h4 : ¬∀ {α : Type} [self : Iris.OFE α] {x y : α} (n : Nat), Iris.OFE.Dist n x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (0)) (by
  nofun)

-- FromMathlib.Int.land_of_nonneg_of_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Int.land_of_nonneg_of_nonneg.h2 : ¬∀ {m n : Int}, 0 ≤ n → m &&& n = ↑(m.natAbs &&& n.natAbs) := fun hc_h => absurd (@hc_h (-1) (2) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.Int.land_of_nonneg_of_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Int.land_of_nonneg_of_nonneg.h3 : ¬∀ {m n : Int}, 0 ≤ m → m &&& n = ↑(m.natAbs &&& n.natAbs) := fun hc_h => absurd (@hc_h (2) (-1) (by
  decide)) (by
  decide +kernel)

-- Iris.MaxPrefixList.toMaxPrefixList_dist_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MaxPrefixList.toMaxPrefixList_dist_inj.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {l1 l2 : List α}, Iris.OFE.Dist n l1 l2 := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) ([]) ([Iris.DFrac.discard])) (by
  nofun)

-- Iris.MaxPrefixList.toMaxPrefixList_incN_aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MaxPrefixList.toMaxPrefixList_incN_aux.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {l1 l2 : List α}, Iris.OFE.Dist n l2 (l1 ++ List.drop l1.length l2) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) ([Iris.DFrac.discard]) ([])) (by
  nofun)

-- Eq.dist, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Eq.dist.h5 : ¬∀ {α : Type} {n : Nat} [inst : Iris.OFE α] {x y : α}, Iris.OFE.Dist n x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (0) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.pcore_ordN_pcore, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.pcore_ordN_pcore.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, Iris.PCore.pcore x ≼ₒ{n} Iris.PCore.pcore y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Ordered.OrderR.op_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderR.op_left.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α} (z : α), x • z ≼ₒ* y • z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.Csum.instCoreIdInr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Csum.instCoreIdInr.h5 : Not
      (∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {b : β},
        @Iris.ORA.CoreId (Iris.Csum α β) (@Iris.Csum.instORA α β inst inst_1) (@Iris.Csum.inr α β b)) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac) (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Algebra.MonoidOps.op_left_id, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.MonoidOps.op_left_id.h4 : ¬∀ {M : Type} {inst : Iris.OFE M} {op : M → M → M} {unit : outParam M} {a : M}, op unit a = a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.OFE.distLater_soundness, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.distLater_soundness.h4 : ¬∀ {α : Type} [inst : Iris.OFE α] {x y : α}, x = y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.pcore_op_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_right.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x cx : α}, x • cx = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Option.pcore_ord_pcore, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.pcore_ord_pcore.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α}, Iris.PCore.pcore x ≼ₒ Iris.PCore.pcore y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Agree.toAgree_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Agree.toAgree_inj.h4 : ¬∀ {α : Type} [inst : Iris.OFE α] {a b : α}, a = b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ExclAuth.agree, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ExclAuth.agree.h4 : ¬∀ {A : Type} [inst : Iris.OFE A] {a b : A}, a = b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.valid_opM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.valid_opM.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {my : Option α}, ✓ x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Option.none)) (by
  nofun)

-- InfiniteType.enum_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.InfiniteType.enum_inj.h4 : ¬∀ {T : Type} [self : InfiniteType T] (n m : Nat), n = m := fun hc_h => absurd (@hc_h (Nat) (instInfiniteTypeNat) (0) (1)) (by
  decide +kernel)

-- Iris.GenMap.singleton_map_none, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.GenMap.singleton_map_none.h4 : ¬∀ {β : Type} {x : Nat} {y : β} {x' : Nat}, (Iris.GenMap.singleton x y).car x' = Option.none := fun hc_h => absurd (@hc_h (Nat) (0) (0) (0)) (by
  decide +kernel)

-- Iris.ORA.pcore_idem', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_idem'.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {cx : α}, Iris.PCore.pcore cx = Option.some cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Option.some_ord_some_of_eq_or_ord, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_ord_some_of_eq_or_ord.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, Option.some a ≼ₒ Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.pcore_inc_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_inc_self.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x cx : α}, cx ≼ x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Agree.exact, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Agree.exact.h3 : ¬∀ {α : Type} {x y : Iris.Agree.Raw α}, x.SameElems y := fun hc_h => absurd (@hc_h (Nat) ({ car := [0], not_nil := of_decide_eq_true (id (Eq.refl Bool.true)) : Iris.Agree.Raw Nat }) ({ car := [1], not_nil := of_decide_eq_true (id (Eq.refl Bool.true)) : Iris.Agree.Raw Nat })) (by
  nofun)

-- Iris.DFrac.valid_op_own, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.DFrac.valid_op_own.h2 : ¬∀ {dq : Iris.DFrac} {q : Iris.Qp}, q.val < 1 := fun hc_h => absurd (@hc_h (Iris.DFrac.discard : Iris.DFrac) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }))) (by
  decide +kernel)

