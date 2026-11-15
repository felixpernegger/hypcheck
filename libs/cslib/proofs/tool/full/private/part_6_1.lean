import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.mem_outSuffixes, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Turing.MultiTapeTM.mem_outSuffixes.h8.inst : [Bool.false] ∉
      Turing.MultiTapeTM.outSuffixes
        { toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }
        (fun (n : ℕ) => n % 2 == 0) ∅ [] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Turing.MultiTapeTM.mem_outSuffixes.h8.prem0 : [Bool.false] <:+
      { toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }
        ((fun (n : ℕ) => n % 2 == 0) 1) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Turing.MultiTapeTM.mem_outSuffixes.h8 : ¬∀ {α β : Type} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out w : List Bool} {a : α},
        w <:+ encOut (f a) → w ∈ Turing.MultiTapeTM.outSuffixes encOut f S out := fun hc_h => HypCheckProof.Turing.MultiTapeTM.mem_outSuffixes.h8.inst (@hc_h (ℕ) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (fun (n : ℕ) => n % 2 == 0) (∅) ([]) ([Bool.false]) (1) HypCheckProof.Turing.MultiTapeTM.mem_outSuffixes.h8.prem0)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.mem_outSuffixes, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.mem_outSuffixes.h9 : ¬∀ {α β : Type} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out w : List Bool} {a : α},
        a ∈ S → w ∈ Turing.MultiTapeTM.outSuffixes encOut f S out := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (fun n => n % 2 == 0 : ℕ → Bool) ({0} : Finset ℕ) ([]) ([Bool.false]) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.encodedFun_enc, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.encodedFun_enc.h8 : ¬∀ {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out : List Bool} {a : α},
        Turing.MultiTapeTM.encodedFun encIn encOut f S out (encIn a) = encOut (f a) := fun hc_h => absurd (@hc_h (Bool) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (not : Bool → Bool) (∅ : Finset Bool) ([]) (Bool.false)) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.suffix_out_mem_outSuffixes, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.suffix_out_mem_outSuffixes.h7 : ¬∀ {α β : Type} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out w : List Bool},
        w ∈ Turing.MultiTapeTM.outSuffixes encOut f S out := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (fun n => n % 2 == 0 : ℕ → Bool) (∅ : Finset ℕ) ([]) ([Bool.false])) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.length_le_sup_of_mem_encPrefixes, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.length_le_sup_of_mem_encPrefixes.h7 : ¬∀ {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {p : List Bool},
        p.length ≤ S.sup fun (a : α) => (encIn a).length + (encOut (f a)).length := fun hc_h => absurd (@hc_h (Bool) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (not : Bool → Bool) (∅ : Finset Bool) ([Bool.false])) (by
  decide +kernel)

-- _private.Cslib.Computability.Circuit.Boolean.Lupanov.0.Cslib.Circuits.Boolean.Lupanov.error_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.error_le.h2 : ¬∀ (c n : ℕ), 3 * n.log2 ≤ n → c * n ^ 2 * 2 ^ (n - 3 * n.log2) ≤ 2 ^ n := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.0.Cslib.Query.finPrefix_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Query.finPrefix_injective.h2 : ¬∀ {n : ℕ} {α : Type}, ↑n ≤ Cardinal.mk α := fun hc_h => absurd (@hc_h (3) (Bool)) (by
  norm_num)

