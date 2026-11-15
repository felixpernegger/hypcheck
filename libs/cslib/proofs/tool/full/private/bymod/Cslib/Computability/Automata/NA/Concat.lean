import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Cslib.Computability.Automata.NA.Concat.0.Cslib.Automata.NA.concat_lift_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.NA.concat_lift_left.h9 : ¬∀ {Symbol State1 State2 : Type} {na1 : Cslib.Automata.NA.FinAcc State1 Symbol} {na2 : Cslib.Automata.NA State2 Symbol}
        {s₁ : State1} {xs : List Symbol} {s₂ : State1} {ss : List State1},
        (Cslib.Automata.NA.concat na1 na2).Execution (Sum.inl s₁) xs (Sum.inl s₂) (List.map Sum.inl ss) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.NA.FinAcc ℕ ℕ }) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b, start := {n : ℕ | n = 0} : Cslib.Automata.NA ℕ ℕ }) (0) ([]) (0) ([])) (by
  nofun)

