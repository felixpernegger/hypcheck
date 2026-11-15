import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.suffix_mem_outSuffixes, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.suffix_mem_outSuffixes.h8 : ¬∀ {α β : Type} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out v w : List Bool},
        v <:+ w → v ∈ Turing.MultiTapeTM.outSuffixes encOut f S out := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (fun n => n % 2 == 0 : ℕ → Bool) (∅ : Finset ℕ) ([]) ([Bool.false]) ([Bool.false]) (by
  decide)) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.suffix_mem_outSuffixes, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.suffix_mem_outSuffixes.h9 : ¬∀ {α β : Type} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out v w : List Bool},
        w ∈ Turing.MultiTapeTM.outSuffixes encOut f S out → v ∈ Turing.MultiTapeTM.outSuffixes encOut f S out := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (fun n => n % 2 == 0 : ℕ → Bool) (∅ : Finset ℕ) ([]) ([Bool.false]) ([]) (by
  decide)) (by
  decide +kernel)

