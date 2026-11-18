import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.CombinatorialGames.Nimber.Field.0.Nimber.add_ne_zero_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.add_ne_zero_of_lt.h2 : ¬∀ {a b : Nimber.{0}}, Ne.{2} (HAdd.hAdd.{1, 1, 1} a b) 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- _private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.numeric_lower, hypothesis 1: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.numeric_lower.h1.gneg.{u} : ∀ (x : Dyadic), ¬IGame.Numeric.{u} ↑x → IGame.Numeric.{u} ↑x.lower := by
  (intros; infer_instance)
theorem HypCheckProof.Dyadic.numeric_lower.h1.{u} : ∀ (x : Dyadic), IGame.Numeric.{u} ↑x.lower := by
  intro hc_x0
  exact Classical.byCases (fun hc_h => @Dyadic.numeric_lower hc_x0 hc_h) (fun hc_hn => @HypCheckProof.Dyadic.numeric_lower.h1.gneg hc_x0 hc_hn)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.numeric_lower.h1.derivable.{u} : ∀ (x : Dyadic), IGame.Numeric.{u} ↑x := by
  (intros; infer_instance)

