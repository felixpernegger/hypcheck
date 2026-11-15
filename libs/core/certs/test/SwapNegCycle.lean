/-! SwapCheck negative test: a swap value that mentions the swapped constant must be rejected. -/
axiom SwapNegCycle.s : @System.Platform.getNumBits = fun u => System.Platform.getNumBits u
theorem SwapNegCycle.t : System.Platform.numBits = System.Platform.numBits := rfl
theorem SwapNegCycle.u : System.Platform.getNumBits () = System.Platform.getNumBits () := by
  rw [SwapNegCycle.s]
