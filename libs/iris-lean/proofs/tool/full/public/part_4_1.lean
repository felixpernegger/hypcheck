import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- Iris.ORA.incN_ne, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.incN_ne.h10 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x x' y y' : α},
        Iris.OFE.Dist n x x' → Iris.OFE.Dist n y y' → x' ≼{n} y' := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl) (by
  rfl)) (by
  nofun)

-- List.Forall₂.map, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.map.h8 : ¬∀ {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ} {l : List α} {k : List β},
        List.Forall₂ R l k → List.Forall₂ S (List.map f l) (List.map g k) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (Nat) (fun a b => a ≤ b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) ([0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Forall₂.map, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.map.h11 : ¬∀ {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ},
        (∀ {a : α} {b : β}, R a b → S (f a) (g b)) →
          ∀ {l : List α} {k : List β}, List.Forall₂ S (List.map f l) (List.map g k) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) (by
  simp) ([]) ([0])) (by
  decide +kernel)

-- Iris.Std.LawfulPartialMap.noDupKeys_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulPartialMap.noDupKeys_inj.h6 : ¬∀ {K V : Type} {k : K} {v v' : V} {L : List (K × V)}, (k, v) ∈ L → (k, v') ∈ L → v = v' := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (0) (1) ([(0, 0), (0, 1)]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Iris.Option.eqv_of_ord_exclusive, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.eqv_of_ord_exclusive.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} [inst_1 : Iris.OrdInc α] [inst_2 : Iris.ORA.Exclusive a] {b : α}, ✓ b → a = b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) _ _ (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Iris.OFE.Dist.op, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.op.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x x' y y' : α},
        Iris.OFE.Dist n y y' → Iris.OFE.Dist n (x • y) (x' • y') := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.OFE.Dist.op, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.op.h9 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x x' y y' : α},
        Iris.OFE.Dist n x x' → Iris.OFE.Dist n (x • y) (x' • y') := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- List.Forall₂.trans, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.trans.h2 : ¬∀ {α : Type} {R : α → α → Prop} {l k m : List α}, List.Forall₂ R l k → List.Forall₂ R k m → List.Forall₂ R l m := fun hc_h => absurd (@hc_h (Nat) (fun a b => a ≠ b : Nat → Nat → Prop) ([0]) ([1]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Forall₂.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.trans.h6 : ¬∀ {α : Type} {R : α → α → Prop},
        (∀ {a b c : α}, R a b → R b c → R a c) → ∀ {l k m : List α}, List.Forall₂ R k m → List.Forall₂ R l m := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (by
  omega) ([0]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Forall₂.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.trans.h7 : ¬∀ {α : Type} {R : α → α → Prop},
        (∀ {a b c : α}, R a b → R b c → R a c) → ∀ {l k m : List α}, List.Forall₂ R l k → List.Forall₂ R l m := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (by
  omega) ([]) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.List.forall₂_zip, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.List.forall₂_zip.h5 : ¬∀ {α α_1 : Type} {R : α → α_1 → Prop} {l₁ : List α} {l₂ : List α_1} {a : α} {b : α_1}, (a, b) ∈ l₁.zip l₂ → R a b := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([0]) ([0]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.List.forall₂_zip, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.List.forall₂_zip.h8 : ¬∀ {α α_1 : Type} {R : α → α_1 → Prop} {l₁ : List α} {l₂ : List α_1}, List.Forall₂ R l₁ l₂ → ∀ {a : α} {b : α_1}, R a b := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([]) (by
  decide) (0) (0)) (by
  decide +kernel)

-- Iris.ORA.ordN_of_ordN_le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.ordN_of_ordN_le.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n n' : Nat} {x y : α}, n' ≤ n → x ≼ₒ{n'} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- List.Forall₂.filter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.filter.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool} {l : List α} {k : List β},
        List.Forall₂ R l k → List.Forall₂ R (List.filter p l) (List.filter q k) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun n => n % 2 == 0 : Nat → Bool) (fun n => n % 2 == 0 : Nat → Bool) ([0]) ([1]) (by
  decide)) (by
  decide +kernel)

-- List.Forall₂.filter, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.filter.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool},
        (∀ {a : α} {b : β}, R a b → p a = q b) →
          ∀ {l : List α} {k : List β}, List.Forall₂ R (List.filter p l) (List.filter q k) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a = b : Nat → Nat → Prop) (fun n => n % 2 == 0 : Nat → Bool) (fun n => n % 2 == 0 : Nat → Bool) (by
  simp) ([]) ([0])) (by
  decide +kernel)

-- Option.Forall₂.getD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.Forall₂.getD.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β} {o : Option α} {o' : Option β},
        Option.Forall₂ R o o' → R (o.getD a) (o'.getD b) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) (Option.none) (Option.none) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Option.Forall₂.getD, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Option.Forall₂.getD.h8.inst : ¬(fun (a b : Nat) => a < b) (Option.none.getD 0) ((Option.some 0).getD 1) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Option.Forall₂.getD.h8.prem0 : (fun (a b : Nat) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Option.Forall₂.getD.h8 : ¬∀ {α β : Type} {R : α → β → Prop} {a : α} {b : β}, R a b → ∀ {o : Option α} {o' : Option β}, R (o.getD a) (o'.getD b) := fun hc_h => HypCheckProof.Option.Forall₂.getD.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => a < b) (0) (1) HypCheckProof.Option.Forall₂.getD.h8.prem0 (Option.none) (Option.some 0))

-- Iris.OrdInc.ordN_incN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OrdInc.ordN_incN.h8 : ¬∀ {α : Type} {inst : Iris.OFE α} {inst_1 : Iris.Op α} {inst_2 : Iris.Ordered α} [self : Iris.OrdInc α] {n : Nat}
        {x y : α}, x ≼{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (Iris.DFrac.instCMRADFrac.toOrdered) _ (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.Ordered.OrderNR.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderNR.trans.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x y z : α}, y ≼ₒ*{n} z → x ≼ₒ*{n} z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Ordered.OrderNR.trans, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.OrderNR.trans.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x y z : α}, x ≼ₒ*{n} y → x ≼ₒ*{n} z := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.IncOrd.incN_ordN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IncOrd.incN_ordN.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] [inst_2 : Iris.Ordered α] [inst_3 : Iris.IncOrd α] {n : Nat}
        {x y : α}, x ≼ₒ{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (Iris.DFrac.instCMRADFrac.toOrdered) _ (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.PCore.pcore_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.PCore.pcore_ne.h7 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.PCore α] {n : Nat} {x y cx : α},
        Iris.PCore.pcore x = Option.some cx → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ Iris.OFE.Dist n cx cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toPCore) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  decide)) (by
  (have _i : ∀ (α : Type) [BEq α] [LawfulBEq α], DecidableEq α := @instDecidableEqOfLawfulBEq; decide))

-- Iris.PCore.pcore_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.PCore.pcore_ne.h8 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.PCore α] {n : Nat} {x y cx : α},
        Iris.OFE.Dist n x y → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ Iris.OFE.Dist n cx cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toPCore) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Relation.Iterate.head, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Iterate.head.h6 : ¬∀ {α : Type} {r : α → α → Prop} {n : Nat} {b c a : α}, Relation.Iterate r n b c → Relation.Iterate r (n + 1) a c := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) (0) (0) (by
  simp)) (by
  nofun)

-- Relation.Iterate.head, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.Iterate.head.h7.inst : ¬Relation.Iterate (fun (a b : Nat) => a < b) (0 + 1) 0 0 := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.Iterate.head.h7.prem0 : (fun (a b : Nat) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Relation.Iterate.head.h7 : ¬∀ {α : Type} {r : α → α → Prop} {n : Nat} {b c a : α}, r a b → Relation.Iterate r (n + 1) a c := fun hc_h => HypCheckProof.Relation.Iterate.head.h7.inst (@hc_h (Nat) (fun (a b : Nat) => a < b) (0) (1) (0) (0) HypCheckProof.Relation.Iterate.head.h7.prem0)

-- Iris.ORA.pcore_monoN_ord, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_monoN_ord.h6 : ¬∀ {α : Type} [self : Iris.ORA α] {n : Nat} {x y cx : α},
        Iris.PCore.pcore x = Option.some cx → ∃ (cy : α), Iris.PCore.pcore y = Option.some cy ∧ cx ≼ₒ{n} cy := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.ORA.id_freeN_l, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.id_freeN_l.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n n' : Nat} {x y : α}, ✓{n} x → ¬Iris.OFE.Dist n' (y • x) x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.validN_ne', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_ne'.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} x → ✓{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.validN_ne', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_ne'.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, Iris.OFE.Dist n x y → ✓{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Option.validN_of_incN_validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.validN_of_incN_validN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, Option.some b ≼{n} Option.some a → ✓{n} b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Option.validN_of_incN_validN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.validN_of_incN_validN.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a b : α}, ✓{n} a → ✓{n} b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Option.isSome_monoN_ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_monoN_ord.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {ma mb : Option α}, ma.isSome = Bool.true → mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Option.some Iris.DFrac.discard) (Option.none) (by
  decide)) (by
  decide +kernel)

-- Iris.Option.isSome_monoN_ord, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_monoN_ord.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {ma mb : Option α}, ma ≼ₒ{n} mb → mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Option.none) (Option.none) (by
  rfl)) (by
  decide +kernel)

-- Iris.OFE.Discrete.discrete_n, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Discrete.discrete_n.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.OFE.Discrete α] {n : Nat} {x y : α}, Iris.OFE.Dist n x y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) _ (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Nat.repeat_ind, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.repeat_ind.h3 : ¬∀ {α : Type} (f : α → α) {P : α → Prop} {x : α}, P x → ∀ (k : Nat), P (Nat.repeat f k x) := fun hc_h => absurd (@hc_h (Nat) (fun n => n + 1 : Nat → Nat) (fun n => n = 0 : Nat → Prop) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1)) (by
  decide +kernel)

-- Nat.repeat_ind, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.repeat_ind.h5 : ¬∀ {α : Type} (f : α → α) {P : α → Prop}, (∀ (x : α), P x → P (f x)) → ∀ {x : α} (k : Nat), P (Nat.repeat f k x) := fun hc_h => absurd (@hc_h (Nat) (fun n => n + 1 : Nat → Nat) (fun _ => False : Nat → Prop) (by
  simp) (0) (0)) (by
  decide +kernel)

-- Iris.ORA.pcore_op_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_mono.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] [inst_1 : Iris.OrdInc α] {x cx : α} (y : α),
        ∃ (cy : α), Iris.PCore.pcore (x • y) = Option.some (cx • cy) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.validN_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_of_le.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n n' : Nat} {x : α}, n' ≤ n → ✓{n'} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  decide)) (by
  nofun)

-- Iris.ORA.validN_of_ordN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_of_ordN.h5 : ¬∀ {α : Type} [self : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.pcore_validN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_validN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x cx : α}, ✓{n} x → ✓{n} cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.ORA.validN_of_inc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_of_inc.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α}, ✓{n} y → ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- FromMathlib.Relation.ReflTransGen.head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Relation.ReflTransGen.head.h5 : ¬∀ {α : Type} {r : α → α → Prop} {b c a : α},
        FromMathlib.Relation.ReflTransGen r b c → FromMathlib.Relation.ReflTransGen r a c := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- FromMathlib.Relation.ReflTransGen.head, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.FromMathlib.Relation.ReflTransGen.head.h6.inst : ¬FromMathlib.Relation.ReflTransGen (fun (a b : Nat) => a < b) 1 0 := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.FromMathlib.Relation.ReflTransGen.head.h6.prem0 : (fun (a b : Nat) => a < b) 1 2 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.FromMathlib.Relation.ReflTransGen.head.h6 : ¬∀ {α : Type} {r : α → α → Prop} {b c a : α}, r a b → FromMathlib.Relation.ReflTransGen r a c := fun hc_h => HypCheckProof.FromMathlib.Relation.ReflTransGen.head.h6.inst (@hc_h (Nat) (fun (a b : Nat) => a < b) (2) (0) (1) HypCheckProof.FromMathlib.Relation.ReflTransGen.head.h6.prem0)

-- Iris.ORA.IdFree.id_free0_r, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.IdFree.id_free0_r.h3 : ¬∀ {α : Type} {inst : Iris.ORA α} {x : α} (y : α), ✓{0} x → ¬Iris.OFE.Dist 0 (x • y) x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Iris.Algebra.BigOpL.bigOpL_flatMap_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.BigOpL.bigOpL_flatMap_eq.h5 : ¬∀ {M A : Type} [inst : Iris.OFE M] {op : M → M → M} {unit : M} {B : Type} (h : A → List B) (Φ : B → M) (l : List A),
        Iris.Algebra.MonoidOps op unit := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Nat) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a a_1 : Iris.DFrac) => Iris.DFrac.discard) (Iris.DFrac.discard : Iris.DFrac) (Nat) (fun _ => [] : Nat → List Nat) (fun (a : Nat) => Iris.DFrac.discard) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.op_left_id (a := (Iris.DFrac.own 1 : Iris.DFrac)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.OFE.DiscreteE.discrete, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.DiscreteE.discrete.h5 : ¬∀ {α : Type} {inst : Iris.OFE α} {x : α} [self : Iris.OFE.DiscreteE x] {y : α}, x = y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) _ (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.op_core_left_of_inc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_core_left_of_inc.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α} [inst_1 : Iris.ORA.CoreId x], y • x = y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) _) (by
  decide +kernel)

-- Iris.OFE.Option.bind_dist, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Option.bind_dist.h8 : ¬∀ {α β : Type} {n : Nat} [inst : Iris.OFE α] [inst : Iris.OFE β] {x : Option α} {f g : α → Option β},
        Iris.OFE.Dist n (x.bind f) (x.bind g) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (0) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (Option.some Iris.DFrac.discard) (fun (a : Iris.DFrac) => Option.none) (fun (a : Iris.DFrac) => Option.some Iris.DFrac.discard)) (by
  simp)

-- Iris.Option.map_forall₂, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.map_forall₂.h7 : ¬∀ {α β : Type} [inst : Iris.OFE α] [inst : Iris.OFE β] (f : α → β) {o1 o2 : Option α},
        Option.map f o1 = Option.map f o2 := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOFE) (fun (a : Iris.DFrac) => Iris.DFrac.discard) (Option.none) (Option.some Iris.DFrac.discard)) (by
  decide +kernel)

-- Iris.SiProp.closed, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.SiProp.closed.h3 : ¬∀ (self : Iris.SiProp) {n₁ n₂ : Nat}, n₂ ≤ n₁ → self.holds n₂ := fun hc_h => absurd (@hc_h ({ holds := fun _ => False, closed := fun h _ => h } : Iris.SiProp) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Iris.DFracAgree.mk_injN, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.DFracAgree.mk_injN.h7 : ¬∀ {A : Type} [inst : Iris.OFE A] {n : Nat} {d₁ d₂ : Iris.DFrac} {a₁ a₂ : A},
        Iris.OFE.Dist n d₁ d₂ ∧ Iris.OFE.Dist n a₁ a₂ := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.OFE.Dist.op_l, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.op_l.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y z : α}, Iris.OFE.Dist n (x • z) (y • z) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.opM_right_dist, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.opM_right_dist.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} (x : α) {y z : Option α},
        Iris.OFE.Dist n (x •? y) (x •? z) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Option.none) (Option.some (Iris.DFrac.own 1))) (by
  nofun)

-- Iris.ORA.op_monoN_right_ord, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_monoN_right_ord.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x y : α} (z : α), z • x ≼ₒ{n} z • y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.opM_ne_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.opM_ne_right.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α} {y₁ y₂ : Option α}, Iris.OFE.Dist n (x •? y₁) (x •? y₂) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Option.none) (Option.some (Iris.DFrac.own 1))) (by
  nofun)

-- Iris.cons_dist_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.cons_dist_eq.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {l k : List α} {y : α},
        ∃ (x : α), ∃ (l' : List α), Iris.OFE.Dist n x y ∧ Iris.OFE.Dist n l' k ∧ l = x :: l' := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) ([]) ([]) (Iris.DFrac.discard : Iris.DFrac)) (by
  simp)

-- List.Forall₂.eraseIdx, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.eraseIdx.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {l : List α} {k : List β} (i : Nat), List.Forall₂ R (l.eraseIdx i) (k.eraseIdx i) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) ([0]) (1)) (by
  decide +kernel)

-- Iris.Ordered.ordN_of_ord, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.ordN_of_ord.h6 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.Ordered α] {x y : α} (n : Nat), x ≼ₒ{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (0)) (by
  nofun)

-- Iris.ORA.ordN_of_ordN_succ, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.ordN_of_ordN_succ.h6 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {n : Nat} {x y : α}, x ≼ₒ{n} y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.validN_op_l, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_op_l.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α} {y : α}, ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.toAgree.inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.toAgree.inj.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {a1 a2 : α} {n : Nat}, Iris.OFE.Dist n a1 a2 := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (0)) (by
  nofun)

-- Iris.Ordered.Order.ordR, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Ordered.Order.ordR.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Ordered α] {x y : α}, x ≼ₒ* y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOrdered) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.validN_op_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_op_left.h5 : ¬∀ {α : Type} [self : Iris.ORA α] {n : Nat} {x : α} {y : α}, ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- FromMathlib.Int.lor_of_nonneg_of_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Int.lor_of_nonneg_of_nonneg.h2 : ¬∀ {m n : Int}, 0 ≤ n → m ||| n = ↑(m.natAbs ||| n.natAbs) := fun hc_h => absurd (@hc_h (-1) (0) (by
  decide)) (by
  decide +kernel)

-- FromMathlib.Int.lor_of_nonneg_of_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Int.lor_of_nonneg_of_nonneg.h3 : ¬∀ {m n : Int}, 0 ≤ m → m ||| n = ↑(m.natAbs ||| n.natAbs) := fun hc_h => absurd (@hc_h (0) (-1) (by
  decide)) (by
  decide +kernel)

-- Iris.Std.LeftAbsorb.left_absorb, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LeftAbsorb.left_absorb.h4 : ¬∀ {α : Type} {R : Iris.Std.Relation α} {i : α} {f : α → α → α} {x : α}, R (f i x) i := fun hc_h => absurd (@hc_h (Nat) (fun (a n : Nat) => n = 0) (1) (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide +kernel)

-- Iris.Std.RightAbsorb.right_absorb, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.RightAbsorb.right_absorb.h4 : ¬∀ {α : Type} {R : Iris.Std.Relation α} {i : α} {f : α → α → α} {x : α}, R (f x i) i := fun hc_h => absurd (@hc_h (Nat) (fun (a n : Nat) => n = 0) (1) (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide +kernel)

-- Iris.Std.RightId.right_id, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.RightId.right_id.h4 : ¬∀ {α : Type} {R : Iris.Std.Relation α} {i : α} {f : α → α → α} {x : α}, R (f x i) x := fun hc_h => absurd (@hc_h (Nat) (fun (a n : Nat) => n = 0) (0) (fun a b => a - b : Nat → Nat → Nat) (1)) (by
  decide +kernel)

-- Iris.PCore.pcore_idem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.PCore.pcore_idem.h5 : ¬∀ {α : Type} {inst : Iris.OFE α} [self : Iris.PCore α] {x : α} {cx : α}, Iris.PCore.pcore cx = Option.some cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toPCore) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Csum.instCoreIdInl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Csum.instCoreIdInl.h5 : Not
      (∀ {α β : Type} [inst : Iris.ORA α] [inst_1 : Iris.ORA β] {a : α},
        @Iris.ORA.CoreId (Iris.Csum α β) (@Iris.Csum.instORA α β inst inst_1) (@Iris.Csum.inl α β a)) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac : Type) (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac) (@Iris.CMRA.toORA Iris.DFrac Iris.DFrac.instCMRADFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.length_dist, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.length_dist.h5 : ¬∀ {α : Type} [inst : Iris.OFE α] {n : Nat} {l k : List α}, l.length = k.length := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (0) ([]) ([Iris.DFrac.discard])) (by
  decide +kernel)

-- Iris.Option.isSome_of_some_ordN, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.isSome_of_some_ordN.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {a : α} {mb : Option α}, mb.isSome = Bool.true := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Option.none)) (by
  decide +kernel)

-- Rat.div_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.div_pos.h2 : ¬∀ {a b : Rat}, 0 < b → 0 < a / b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Rat.div_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.div_pos.h3 : ¬∀ {a b : Rat}, 0 < a → 0 < a / b := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Iris.ORA.validN_opM, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.validN_opM.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {n : Nat} {x : α} {my : Option α}, ✓{n} x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Option.none)) (by
  nofun)

-- Iris.Std.LawfulBigOp.refl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.LawfulBigOp.refl.h4 : ¬∀ {PROP : Type} (f : PROP → PROP → PROP) {unit : outParam PROP} {eq : outParam (PROP → PROP → Prop)} {a : PROP}, eq a a := fun hc_h => absurd (@hc_h (Nat) (fun a b => a - b : Nat → Nat → Nat) (0) (fun (a n : Nat) => n = 0) (1)) (by
  decide +kernel)

-- Iris.ORA.pcore_op_self_L, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.pcore_op_self_L.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α} {cx : α}, cx • cx = cx := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.OFE.equiv_ext_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.equiv_ext_right.h4 : ¬∀ {β : Type} {α : Type} {x y : β}, x = y := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (1)) (by
  decide +kernel)

-- Iris.IsUnit.unit_left_id, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IsUnit.unit_left_id.h3 : ¬∀ {α : Type} {inst : Iris.ORA α} {ε x : α}, ε • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Relation.Iterate.once, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Iterate.once.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.Iterate r 1 a b := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0)) (by
  nofun)

-- Iris.Option.exists_of_some_ord, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.exists_of_some_ord.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a : α} {mb : Option α},
        ∃ (b : α), mb = Option.some b ∧ Option.some a ≼ₒ Option.some b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Option.none)) (by
  simp)

-- FromMathlib.List.Nodup.of_map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.List.Nodup.of_map.h4 : ¬∀ {α β : Type} (f : α → β) {l : List α}, l.Nodup := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n + 1 : Nat → Nat) ([0, 0])) (by
  decide +kernel)

-- FromMathlib.Relation.ReflTransGen.single, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FromMathlib.Relation.ReflTransGen.single.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, FromMathlib.Relation.ReflTransGen r a b := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (1) (0)) (by
  nofun)

-- Iris.ORA.core_op_mono_ord, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.core_op_mono_ord.h2 : ¬∀ {α : Type} [inst : Iris.ORA α] (x y : α), Iris.PCore.core x ≼ₒ Iris.PCore.core (x • y) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

-- Iris.Excl.excl_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Excl.excl_inj.h4 : ¬∀ {α : Type} [inst : Iris.OFE α] {a b : α}, a = b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Option.option_core_id, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.option_core_id.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] (ma : Option α), Iris.ORA.CoreId ma := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Option.some (Iris.DFrac.own 1))) (by
  exact fun hc_c =>
    absurd (hc_c.core_id)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iris.Option.some_core, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.some_core.h2 : ¬∀ {α : Type} [inst : Iris.ORA α] (a : α), Option.some (Iris.PCore.core a) = Iris.PCore.core (Option.some a) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.core_op, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.core_op.h2 : ¬∀ {α : Type} [inst : Iris.ORA α] (x : α), Iris.PCore.core x • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.core_id_dup_L, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.core_id_dup_L.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α}, x • x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- List.Forall₂.rfl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.rfl.h2 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.Forall₂ R l l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) ([0])) (by
  decide +kernel)

-- List.Forall₂.refl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.refl.h2 : ¬∀ {α : Type} {R : α → α → Prop} (l : List α), List.Forall₂ R l l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) ([0])) (by
  decide +kernel)

-- Iris.Algebra.TimeReceipt.le_of_auth_op_frag_valid, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Algebra.TimeReceipt.le_of_auth_op_frag_valid.h3 : ¬∀ {m n₁ n₂ : Nat}, n₁ + n₂ ≤ m := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Iris.ORA.core_op_core_L, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.core_op_core_L.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α}, Iris.PCore.core x • Iris.PCore.core x = Iris.PCore.core x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.ORA.op_core_L, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_core_L.h3 : ¬∀ {α : Type} [inst : Iris.ORA α] {x : α}, x • Iris.PCore.core x = x := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  decide +kernel)

-- Iris.Frac.le_of_ord, hypothesis 2: necessary
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
theorem HypCheckProof.Iris.Frac.le_of_ord.h2 : ¬∀ {p q : Iris.Qp}, p ≤ q := fun hc_h => absurd (@hc_h ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ((⟨1 / 2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q }))) (by
  (simp <;> decide))
-/

-- Iris.MonoZ.lb_op_le_l, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.MonoZ.lb_op_le_l.h2 : ¬∀ (n n' : Iris.MaxInt), (◯MZ n) = (◯MZ n') • ◯MZ n := fun hc_h => absurd (@hc_h ({ toInt := 0 : Iris.MaxInt }) ({ toInt := 1 : Iris.MaxInt })) (by
  nofun)

-- Iris.SiProp.pure_soundness, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.SiProp.pure_soundness.h1 : ¬∀ {φ : Prop}, φ := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

