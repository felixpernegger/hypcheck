/-! SwapCheck positive test: `numBits = 32` holds once `getNumBits` is swapped to return 32. -/

axiom SwapToy.swap32 : @System.Platform.getNumBits = fun _ => ⟨32, Or.inl rfl⟩

theorem SwapToy.numBits_eq : System.Platform.numBits = 32 := by
  unfold System.Platform.numBits; rw [SwapToy.swap32]

theorem SwapToy.usize_size : USize.size = 4294967296 := by
  rw [USize.size, SwapToy.numBits_eq]
