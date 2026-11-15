import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- Iris.bigOpL_dist_2, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.bigOpL_dist_2.h6 : ¬∀ {M α : Type} [inst : Iris.OFE M] [inst_1 : Iris.OFE α] {op : M → M → M} {unit : M} {n : Nat} {l1 l2 : List α},
        Iris.OFE.Dist n l1 l2 →
          ∀ {f g : Nat → α → M},
            (∀ {k : Nat} {y1 y2 : α},
                l1[k]? = Option.some y1 →
                  l2[k]? = Option.some y2 → Iris.OFE.Dist n y1 y2 → Iris.OFE.Dist n (f k y1) (g k y2)) →
              Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (0) ([]) ([]) (by
  rfl) (fun (a : Nat) (a_1 : Iris.DFrac) => Iris.DFrac.discard) (fun (a : Nat) (a_1 : Iris.DFrac) => Iris.DFrac.discard) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_proper_2, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_proper_2.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} [inst_1 : Iris.OFE A] {Φ Ψ : Nat → A → M}
        {l₁ l₂ : List A},
        l₁.length = l₂.length →
          (∀ {k : Nat} {y₁ y₂ : A}, l₁[k]? = Option.some y₁ → l₂[k]? = Option.some y₂ → Φ k y₁ = Ψ k y₂) →
            Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a : Nat) (a_1 : Iris.DFrac) => Iris.DFrac.discard) (fun (a : Nat) (a_1 : Iris.DFrac) => Iris.DFrac.discard) ([]) ([]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.SbiUnfold.closed, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.SbiUnfold.closed.h9 : ¬∀ {PROP : Type} {inst : Iris.Sbi PROP} {clo : Iris.SbiUnfoldClosure} (P : PROP) {Pi : outParam (Nat → Prop)}
        [self : Iris.SbiUnfold clo P Pi] {n₁ n₂ : Nat}, clo = Iris.SbiUnfoldClosure.downClosed → n₂ ≤ n₁ → Pi n₂ := fun hc_h => absurd (@hc_h (Iris.SiProp : Type) (Iris.instSbiSiProp) _ ({ holds := fun _ => False, closed := fun h _ => h } : Iris.SiProp) (fun _ => False : Nat → Prop) _ (0) (0) rfl (by
  decide)) (by
  decide +kernel)

-- Iris.Ordered.ordN_ne, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.ordN_ne.h10 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.Ordered α] {n : Nat} {x x' y y' : α},
        Iris.OFE.Dist n x x' → Iris.OFE.Dist n y y' → x' ≼ₒ{n} y' := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl) (by
  rfl)) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_zip_op_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_zip_op_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {B : Type} {l₁ : List A} {l₂ : List B} {Φ : Nat → A → M}
        {Ψ : Nat → B → M}, l₁.length = l₂.length → Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (Nat) ([]) ([]) (fun (a a_1 : Nat) => Iris.DFrac.discard) (fun (a a_1 : Nat) => Iris.DFrac.discard) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.ORA.pcore_monoN', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_monoN'.h7 : ¬∀ {α : Type} [inst : Iris.ORA α] [inst_1 : Iris.OrdInc α] {n : Nat} {x y cx : α},
        Iris.OFE.Dist n (Iris.PCore.pcore x) (Option.some cx) → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ cx ≼{n} cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Option.map_ne, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.map_ne.h10 : ¬∀ {α : Type} [inst : Iris.OFE α] {β : Type} [inst_1 : Iris.OFE β] {f g : α → β} {x y : Option α} {n : Nat},
        (∀ (x y : α), Iris.OFE.Dist n x y → Iris.OFE.Dist n (f x) (g y)) → Iris.OFE.Dist n (Option.map f x) (Option.map g y) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a : Iris.DFrac) => Iris.DFrac.discard) (fun (a : Iris.DFrac) => Iris.DFrac.discard) (Option.none) (Option.some Iris.DFrac.discard) (0) (by
  simp)) (by
  simp)

-- Iris.Prod.map_ext, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.map_ext.h9 : ¬∀ {A A' B B' : Type} {x : A × B} {f f' : A → A'} {g g' : B → B'},
        (∀ (a : B), g a = g' a) → Prod.map f g x = Prod.map f' g' x := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (Nat) ((0, 0)) (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) (by
  simp)) (by
  decide +kernel)

-- Iris.Prod.map_ext, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.map_ext.h10 : ¬∀ {A A' B B' : Type} {x : A × B} {f f' : A → A'} {g g' : B → B'},
        (∀ (a : A), f a = f' a) → Prod.map f g x = Prod.map f' g' x := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (Nat) ((0, 0)) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) (fun _ => 0 : Nat → Nat) (by
  simp)) (by
  decide +kernel)

-- List.Forall₂.getD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.getD.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β} {l : List α} {k : List β},
        List.Forall₂ R l k → ∀ (i : Nat), R (l.getD i a) (k.getD i b) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) ([]) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- List.Forall₂.getD, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Forall₂.getD.h8.inst : ¬(fun (a b : Nat) => a < b) ([].getD 0 0) ([0].getD 0 1) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Forall₂.getD.h8.prem0 : (fun (a b : Nat) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.Forall₂.getD.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β},
        R a b → ∀ {l : List α} {k : List β} (i : Nat), R (l.getD i a) (k.getD i b) := fun hc_h => HypCheckProof.List.Forall₂.getD.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => a < b) (0) (1) HypCheckProof.List.Forall₂.getD.h8.prem0 ([]) ([0]) (0))

-- Iris.Algebra.BigOpL.bigOpL_eq_of_forall_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_eq_of_forall_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {Φ Ψ : Nat → A → M} {l : List A},
        (∀ {i : Nat} {x : A}, Φ i x = Ψ i x) → Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard) (fun (a a_1 : Nat) => Iris.DFrac.discard) ([]) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.ORA.pcore_mono', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_mono'.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] [inst_1 : Iris.OrdInc α] {x y cx : α},
        Iris.PCore.pcore x = Option.some cx → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ cx ≼ cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.UFracAuth.includedN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.UFracAuth.includedN.h8 : ¬∀ {A : Type} [inst : Iris.ORA A] [inst_1 : Iris.OrdInc A] {n : Nat} {p q : Iris.Qp} {a b : A},
        Option.some b ≼{n} Option.some a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (0) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Std.LawfulBigOp.congr_l, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.congr_l.h4 : ¬∀ {PROP : Type} {f : PROP → PROP → PROP} {unit : outParam PROP} {eq : outParam (PROP → PROP → Prop)} {a a' b : PROP},
        eq a a' → eq (f a b) (f a' b) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a + b : Nat → Nat → Nat) (0) (fun (a n : Nat) => n = 0) (0) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iris.Option.eqv_of_inc_exclusive, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.eqv_of_inc_exclusive.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} [inst_1 : Iris.ORA.Exclusive a] {b : α}, ✓ b → a = b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) _ (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- List.Forall₂.imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.imp.h4 : ¬∀ {α β : Type} {R S : α → β → Prop} {l : List α} {k : List β}, List.Forall₂ R l k → List.Forall₂ S l k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a ≤ b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) ([0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Forall₂.imp, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.imp.h7 : ¬∀ {α β : Type} {R S : α → β → Prop},
        (∀ {a : α} {b : β}, R a b → S a b) → ∀ {l : List α} {k : List β}, List.Forall₂ S l k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) (by
  simp) ([]) ([0])) (by
  decide +kernel)

-- Iris.ORA.id_freeN_r, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.id_freeN_r.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n n' : Nat} {x y : α}, ✓{n} x → ¬Iris.OFE.Dist n' (x • y) x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.pcore_monoN_ord', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_monoN_ord'.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y cx : α},
        Iris.OFE.Dist n (Iris.PCore.pcore x) (Option.some cx) →
          ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ cx ≼ₒ{n} cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.SbiUnfold.entails_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.SbiUnfold.entails_iff.h6 : Not
      (∀ {PROP : Type} [inst : Iris.Sbi PROP] {P Q : PROP} {Pi Qi : Nat → Prop}
        [hQ : @Iris.SbiUnfold PROP inst Iris.SbiUnfoldClosure.notClosed Q Qi],
        Iff (@Iris.BI.BIBase.Entails PROP (@Iris.BI.toBIBase PROP (@Iris.Sbi.toBI PROP inst)) P Q)
          (∀ (n : Nat), Pi n → Qi n)) := fun hc_h => absurd (@hc_h (Iris.SiProp : Type) (Iris.instSbiSiProp) ({ holds := fun _ => False, closed := fun h _ => h } : Iris.SiProp) ({ holds := fun _ => False, closed := fun h _ => h } : Iris.SiProp) (fun n => n = 0 : Nat → Prop) (fun _ => False : Nat → Prop) _) (by
  simp)

-- Iris.IncludedN.validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IncludedN.validN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Ordered.OrderR.validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderR.validN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Ordered.OrderR.validN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderR.validN.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, x ≼ₒ* y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Option.exclusiveN_some_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exclusiveN_some_left.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a : α} {mb : Option α}, ✓{n} Option.some a • mb → mb = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Option.some Iris.DFrac.discard) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Iris.Option.exclusiveN_some_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exclusiveN_some_left.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a : α} [inst : Iris.ORA.Exclusive a] {mb : Option α}, mb = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.own 1 : Iris.DFrac) _ (Option.some Iris.DFrac.discard)) (by
  decide +kernel)

-- Iris.ORA.pcore_mono_ord', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_mono_ord'.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y cx : α},
        Iris.PCore.pcore x = Option.some cx → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ cx ≼ₒ cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.Option.exclusiveN_some_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exclusiveN_some_right.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a : α} {mb : Option α}, ✓{n} mb • Option.some a → mb = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Option.some Iris.DFrac.discard) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Iris.Option.exclusiveN_some_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exclusiveN_some_right.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a : α} [inst : Iris.ORA.Exclusive a] {mb : Option α}, mb = Option.none := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.own 1 : Iris.DFrac) _ (Option.some Iris.DFrac.discard)) (by
  decide +kernel)

-- FracAuth.dfrac_validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.dfrac_validN.h5 : ¬∀ {A : Type} [inst : Iris.ORA A] {dq : Iris.DFrac} {n : Nat} {a : A}, ✓{n} a → ✓{n} (●F{dq} a) • ◯F a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (0) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- FromMathlib.Relation.ReflTransGen.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Relation.ReflTransGen.trans.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α},
        FromMathlib.Relation.ReflTransGen r b c → FromMathlib.Relation.ReflTransGen r a c := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (1) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- FromMathlib.Relation.ReflTransGen.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Relation.ReflTransGen.trans.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α},
        FromMathlib.Relation.ReflTransGen r a b → FromMathlib.Relation.ReflTransGen r a c := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (1) (1) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- FromMathlib.Relation.TransGen.head, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.FromMathlib.Relation.TransGen.head.h6.inst : ¬Relation.TransGen (fun (a b : Nat) => a < b) 0 0 := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.FromMathlib.Relation.TransGen.head.h6.prem0 : (fun (a b : Nat) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.FromMathlib.Relation.TransGen.head.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, r a b → Relation.TransGen r a c := fun hc_h => HypCheckProof.FromMathlib.Relation.TransGen.head.h6.inst (@hc_h (Nat) (fun (a b : Nat) => a < b) (0) (1) (0) HypCheckProof.FromMathlib.Relation.TransGen.head.h6.prem0)

-- Iris.ORA.Discrete.discrete_ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.Discrete.discrete_ord.h5 : ¬∀ {α : Type} {inst : Iris.ORA α} [self : Iris.ORA.Discrete α] {x y : α}, x ≼ₒ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.Discrete.discrete_0, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Discrete.discrete_0.h5 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.OFE.Discrete α] {x y : α}, x = y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Std.insert_eq_singleton_union_extTreeSet, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.insert_eq_singleton_union_extTreeSet.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {ps : Std.ExtTreeSet α cmp} {p : α},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.CMRA.ord_of_ord0, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.CMRA.ord_of_ord0.h5 : ¬∀ {α : Type} [inst : Iris.CMRA α] [inst_1 : Iris.OFE.Discrete α] {x y : α}, x ≼ₒ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_cons.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : Nat → A → M) (a : A) («as» : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a a_1 : Nat) => Iris.DFrac.discard) (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_zipIdxInt_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_zipIdxInt_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : A × Int → M) (n : Int) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a : Nat × Int) => Iris.DFrac.discard) (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_zipIdx_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_zipIdx_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : A × Nat → M) (n : Nat) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a : Nat × Nat) => Iris.DFrac.discard) (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Algebra.BigOpL.bigOpL_consZ_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_consZ_left.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} (Φ : Int → A → M) (x : A) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (fun (a : Int) (a_1 : Nat) => Iris.DFrac.discard) (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.ORA.Discrete.discrete_valid, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.Discrete.discrete_valid.h4 : ¬∀ {α : Type} {inst : Iris.ORA α} [self : Iris.ORA.Discrete α] {x : α}, ✓ x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (Iris.DFrac.ownDiscard 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.op_left_dist, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_left_dist.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y : α} (z : α), Iris.OFE.Dist n (x • z) (y • z) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.dist_inl, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.dist_inl.h7 : Not
      (∀ {α β : Type} [inst : Iris.OFE α] [inst_1 : Iris.OFE β] {n : Nat} {x y : α},
        @Iris.OFE.Dist (Sum α β) (@Iris.OFE.instSum α β inst inst_1) n (@Sum.inl α β x) (@Sum.inl α β y)) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (@Iris.ORA.toOFE Iris.DFrac (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac)) (@Iris.ORA.toOFE Iris.DFrac (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Prod.validN_fst, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.validN_fst.h6 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {n : Nat} {x : α × β}, ✓{n} x.fst := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) (0) ((Iris.DFrac.ownDiscard 1, Iris.DFrac.discard))) (by
  nofun)

-- Iris.Ordered.OrderR.ordNR, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderR.ordNR.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] (n : Nat) {x y : α}, x ≼ₒ*{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.op_monoN_left_ord, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_monoN_left_ord.h6 : ¬∀ {α : Type} [self : Iris.ORA α] {n : Nat} {x y : α} (z : α), x • z ≼ₒ{n} y • z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.validN_op_opM_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_op_opM_left.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α} {y : α} {mz : Option α}, ✓{n} x •? mz := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Option.some (Iris.DFrac.own 1))) (by
  nofun)

-- Iris.ORA.incN_of_incN_succ, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.incN_of_incN_succ.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y : α}, x ≼{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.some_inc_some_of_dist_opM, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_inc_some_of_dist_opM.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α} {mz : Option α}, Option.some y ≼{n} Option.some x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Option.none)) (by
  nofun)

-- FromMathlib.Int.xor_of_nonneg_of_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Int.xor_of_nonneg_of_nonneg.h2 : ¬∀ {m n : Int}, 0 ≤ n → m ^^^ n = ↑(m.natAbs ^^^ n.natAbs) := fun hc_h => absurd (@hc_h (-1) (0) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.Int.xor_of_nonneg_of_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Int.xor_of_nonneg_of_nonneg.h3 : ¬∀ {m n : Int}, 0 ≤ m → m ^^^ n = ↑(m.natAbs ^^^ n.natAbs) := fun hc_h => absurd (@hc_h (0) (-1) (by
  decide)) (by
  decide +kernel)

-- Iris.Prod.valid_snd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Prod.valid_snd.h5 : ¬∀ {α β : Type} [inst : Iris.ORA α] [inst : Iris.ORA β] {x : α × β}, ✓ x.snd := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.instCMRADFrac.toORA) ((Iris.DFrac.discard, Iris.DFrac.ownDiscard 1))) (by
  nofun)

-- Iris.ORA.pcore_order_op, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_order_op.h4 : ¬∀ {α : Type} [self : Iris.ORA α] {x cx : α} (y : α),
        ∃ (cxy : α), Iris.PCore.pcore (x • y) = Option.some cxy ∧ cx ≼ₒ cxy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.dist_or_ordN_of_some_ordN_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.dist_or_ordN_of_some_ordN_some.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Iris.OFE.Dist n a b ∨ a ≼ₒ{n} b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.Dist.symm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.symm.h5 : ¬∀ {α : Type} {y : α} [inst : Iris.OFE α] {n : Nat} {x : α}, Iris.OFE.Dist n y x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Std.LeftId.left_id, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LeftId.left_id.h4 : ¬∀ {α : Type} {R : Iris.Std.Relation α} {i : α} {f : α → α → α} {x : α}, R (f i x) x := fun hc_h => absurd (@hc_h (Nat) (fun (a n : Nat) => n = 0) (0) (fun a b => a - b : Nat → Nat → Nat) (1)) (by
  decide +kernel)

-- List.Forall₂.reverse, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.reverse.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l : List α} {k : List β}, List.Forall₂ R l.reverse k.reverse := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([0])) (by
  decide +kernel)

-- Iris.MonoList.lb_dist_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MonoList.lb_dist_inj.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {l1 l2 : List α}, Iris.OFE.Dist n l1 l2 := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) ([]) ([Iris.DFrac.discard])) (by
  nofun)

-- List.Forall₂.length_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.length_eq.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l : List α} {k : List β}, l.length = k.length := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([0])) (by
  decide +kernel)

-- List.Forall₂.getLast?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.getLast?.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l : List α} {k : List β}, Option.Forall₂ R l.getLast? k.getLast? := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([0])) (by
  nofun)

-- Iris.OFE.eq_dist_2, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.eq_dist_2.h4 : ¬∀ {α : Type} [self : Iris.OFE α] {x y : α}, x = y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.pcore_op_left', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_left'.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x cx : α}, cx • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Option.eq_or_ord_of_some_ord_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.eq_or_ord_of_some_ord_some.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, a = b ∨ a ≼ₒ b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Option.isSome_of_some_ord, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_of_some_ord.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} {mb : Option α}, mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Option.none)) (by
  decide +kernel)

-- Iris.ORA.pcore_eq_core, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_eq_core.h3 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.PCore α] (x : α), Iris.PCore.pcore x = Option.some (Iris.PCore.core x) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toPCore) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.OFE.equiv_inr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.equiv_inr.h4 : Not (∀ {β α : Type} {x y : β}, @Eq (Sum α β) (@Sum.inr α β x) (@Sum.inr α β y)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Iris.MonoList.lb_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MonoList.lb_inj.h4 : ¬∀ {α : Type} [inst : Iris.OFE α] {l1 l2 : List α}, l1 = l2 := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) ([]) ([Iris.DFrac.discard])) (by
  decide +kernel)

-- Iris.Valid.Valid.validN, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Valid.Valid.validN.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {n : Nat}, ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (0)) (by
  nofun)

-- Iris.Option.some_ord_some_of_ord, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_ord_some_of_ord.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, Option.some a ≼ₒ Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ProofMode.IsApp.is_app, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ProofMode.IsApp.is_app.h4 : ¬∀ {α : Type} {l : List α} {l1 l2 : outParam (List α)}, l = l1 ++ l2 := fun hc_h => absurd (@hc_h (Nat) ([]) ([]) ([0])) (by
  decide +kernel)

-- Iris.ORA.pcore_idemp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_idemp.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {cx : α}, Iris.PCore.pcore cx = Option.some cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.DiscreteO.dist_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.DiscreteO.dist_inj.h4 : ¬∀ {α : Type} {x y : α} {n : Nat}, x = y := fun hc_h => absurd (@hc_h (Nat) (0) (1) (0)) (by
  decide +kernel)

-- Iris.Std.TCEq.to_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.TCEq.to_eq.h3 : ¬∀ {α : Type} {a b : α}, a = b := fun hc_h => absurd (@hc_h (Nat) (0) (1)) (by
  decide +kernel)

-- FromMathlib.Nodup.filter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Nodup.filter.h3 : ¬∀ {α : Type} (p : α → Bool) {l : List α}, (List.filter p l).Nodup := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([0, 0])) (by
  decide +kernel)

-- Iris.IsUnit.pcore_unit, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IsUnit.pcore_unit.h3 : ¬∀ {α : Type} {inst : Iris.ORA α} {ε : α}, Iris.PCore.pcore ε = Option.some ε := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.core_op_core, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.core_op_core.h2 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α}, Iris.PCore.core x • Iris.PCore.core x = Iris.PCore.core x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.op_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_self.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] (x : α), x • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Frac.le_of_inc, hypothesis 2: necessary
/- FAILED: 2:209: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (0 < 1 / 2) = true
in the application
  id (Eq.refl true) | 44:10: Application type mismatch: The argument
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
  | Int.negSucc i => isFalse ⋯ | 12:12: Tactic `decide` failed to reduce
  @decide (¬1 ≤ 1 / 2) instDecidableNot
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `instDecidableNot`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 3:39: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (0 < 1 / 2) = true
in the application
  id (Eq.refl true) | 48:14: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (0 < 1 / 2) = true
in the application
  id (Eq.refl true) | 2:268: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 13:75: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Frac.le_of_inc.h2 : ¬∀ {p q : Iris.Qp}, p ≤ q := fun hc_h => absurd (@hc_h ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1 / 2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }))) (by
  (simp <;> decide))
-/

-- Iris.Qp.val_divide_even, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Qp.val_divide_even.h2 : ¬∀ (q : Iris.Qp) (n : Nat), 0 < n := fun hc_h => absurd (@hc_h ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (0)) (by
  decide +kernel)

-- Iris.ProofMode.TCSideCondition.sidecondition, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ProofMode.TCSideCondition.sidecondition.h1 : ¬∀ {φ : Prop}, φ := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

