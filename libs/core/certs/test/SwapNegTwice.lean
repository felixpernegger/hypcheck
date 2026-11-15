/-! SwapCheck negative test: two swaps of one constant would prove `False`; must be rejected. -/
axiom SwapNegTwice.s32 : @System.Platform.getNumBits = fun _ => ⟨32, Or.inl rfl⟩
axiom SwapNegTwice.s64 : @System.Platform.getNumBits = fun _ => ⟨64, Or.inr rfl⟩
theorem SwapNegTwice.bad : False := by
  have h := congrArg (fun f => (f ()).val) (SwapNegTwice.s32.symm.trans SwapNegTwice.s64)
  simp at h
