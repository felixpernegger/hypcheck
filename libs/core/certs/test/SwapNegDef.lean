/-! SwapCheck negative test: only opaque constants may be swapped. -/
axiom SwapNegDef.s : @Nat.succ = fun _ => 0
theorem SwapNegDef.bad : (1 : Nat) = 0 := by
  have := congrArg (fun f => f 0) SwapNegDef.s; exact this
