import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.Cslib.Computability.Automata.NA.Concat.0.Cslib.Automata.NA.concat_lift_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.NA.concat_lift_left.h9 : ¬∀ {Symbol State1 State2 : Type} {na1 : Cslib.Automata.NA.FinAcc State1 Symbol} {na2 : Cslib.Automata.NA State2 Symbol}
        {s₁ : State1} {xs : List Symbol} {s₂ : State1} {ss : List State1},
        (Cslib.Automata.NA.concat na1 na2).Execution (Sum.inl s₁) xs (Sum.inl s₂) (List.map Sum.inl ss) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.NA.FinAcc ℕ ℕ }) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b, start := {n : ℕ | n = 0} : Cslib.Automata.NA ℕ ℕ }) (0) ([]) (0) ([])) (by
  nofun)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.encodedFun_enc_of_notMem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.encodedFun_enc_of_notMem.h8 : ¬∀ {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out : List Bool} {a : α},
        Turing.MultiTapeTM.encodedFun encIn encOut f S out (encIn a) = out := fun hc_h => absurd (@hc_h (Bool) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (not : Bool → Bool) ({true} : Finset Bool) ([]) (Bool.true)) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.tail_mem_outSuffixes, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.tail_mem_outSuffixes.h7 : ¬∀ {α β : Type} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out w : List Bool},
        w.tail ∈ Turing.MultiTapeTM.outSuffixes encOut f S out := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (fun n => n % 2 == 0 : ℕ → Bool) (∅ : Finset ℕ) ([]) ([Bool.false, Bool.true])) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.encOut_mem_outSuffixes, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.encOut_mem_outSuffixes.h6 : ¬∀ {α β : Type} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out : List Bool} (a : α),
        encOut (f a) ∈ Turing.MultiTapeTM.outSuffixes encOut f S out := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (fun n => n % 2 == 0 : ℕ → Bool) (∅ : Finset ℕ) ([]) (0)) (by
  decide +kernel)

