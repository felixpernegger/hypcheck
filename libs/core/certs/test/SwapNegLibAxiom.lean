import Lake
/-! SwapCheck negative test: swapping `Lake.OpaqueConfigTarget` conflicts with the library axiom
`Lake.OpaqueConfigTarget.def`; without a re-proof `Lake.OpaqueConfigTarget.def.swapProof` the
certificate must be rejected. -/
axiom SwapNegLibAxiom.s : @Lake.OpaqueConfigTarget = fun _ => Empty
theorem SwapNegLibAxiom.t : Lake.OpaqueConfigTarget .anonymous = Empty := by rw [SwapNegLibAxiom.s]
