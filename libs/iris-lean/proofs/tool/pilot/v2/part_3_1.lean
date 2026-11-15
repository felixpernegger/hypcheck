import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- Iris.GenMap.singleton_map_none, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.GenMap.singleton_map_none.h4 : ¬∀ {β : Type} {x : Nat} {y : β} {x' : Nat}, (Iris.GenMap.singleton x y).car x' = Option.none := fun hc_h => absurd (@hc_h (Nat) (0) (0) (0)) (by
  decide +kernel)

-- Iris.HeapLang.loc_add_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.HeapLang.loc_add_inj.h3 : ¬∀ {l : Iris.HeapLang.Loc} {i j : Int}, i = j := fun hc_h => absurd (@hc_h ({ n := 0 : Iris.HeapLang.Loc }) (0) (1)) (by
  decide +kernel)

