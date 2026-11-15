import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- List.Forall₂.map, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.map.h8 : ¬∀ {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ} {l : List α} {k : List β},
        List.Forall₂ R l k → List.Forall₂ S (List.map f l) (List.map g k) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (Nat) (fun a b => a ≤ b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) (fun n => n + 1 : Nat → Nat) (fun n => n + 1 : Nat → Nat) ([0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- Iris.ORA.discrete_inc_l, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.discrete_inc_l.h6 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α} [HD : Iris.OFE.DiscreteE x], ✓{0} y → x ≼ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) _ (by
  rfl)) (by
  nofun)

-- Iris.IncOrd.inc_ord, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.IncOrd.inc_ord.h7 : ¬∀ {α : Type} {inst : Iris.OFE α} {inst_1 : Iris.Op α} {inst_2 : Iris.Ordered α} [self : Iris.IncOrd α] {x y : α},
        x ≼ₒ y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (Iris.DFrac.instCMRADFrac.toOrdered) _ (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- List.nodup_map_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_map_of_injective.h4 : ¬∀ {A B : Type} {f : A → B} {l : List A}, l.Nodup → (List.map f l).Nodup := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun _ => 0 : Nat → Nat) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- Iris.OFE.Dist.op_l, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.OFE.Dist.op_l.h7 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {x y z : α}, Iris.OFE.Dist n (x • z) (y • z) := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

