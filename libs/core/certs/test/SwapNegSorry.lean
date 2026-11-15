/-! SwapCheck negative test: a `sorry` in a certificate must be rejected. -/
axiom SwapNegSorry.swap32 : @System.Platform.getNumBits = fun _ => ⟨32, Or.inl rfl⟩
theorem SwapNegSorry.bad : System.Platform.numBits = 64 := sorry
