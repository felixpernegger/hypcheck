/-! SwapCheck negative test: `native_decide` (`Lean.ofReduceBool`) must be rejected. -/
axiom SwapNegNative.s : @System.Platform.getNumBits = fun _ => ⟨32, Or.inl rfl⟩
theorem SwapNegNative.bad : System.Platform.numBits = 64 ∨ True := Or.inr (by native_decide)
