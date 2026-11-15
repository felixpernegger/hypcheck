import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.List.Lex.0.List.Lex.asymm.aux, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.asymm.aux.h2 : ¬∀ {α : Type} (r : α → α → Prop) (x x_1 : List α), List.Lex r x x_1 → List.Lex r x_1 x → False := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([0]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.asymm.aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.asymm.aux.h5 : ¬∀ {α : Type} (r : α → α → Prop) [inst : Std.Asymm r] (x x_1 : List α), List.Lex r x_1 x → False := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.asymm.aux, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.asymm.aux.h6 : ¬∀ {α : Type} (r : α → α → Prop) [inst : Std.Asymm r] (x x_1 : List α), List.Lex r x x_1 → False := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.isOrderConnected.aux, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.isOrderConnected.aux.h7 : ¬∀ {α : Type} (r : α → α → Prop) [inst : IsOrderConnected α r] [inst : Std.Trichotomous r] (x x_1 x_2 : List α),
        List.Lex r x x_1 ∨ List.Lex r x_1 x_2 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ _ ([]) ([]) ([])) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.trichotomous.aux, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.trichotomous.aux.h2 : ¬∀ {α : Type} (r : α → α → Prop) (x x_1 : List α), ¬List.Lex r x x_1 → ¬List.Lex r x_1 x → x = x_1 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) ([0]) ([1]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.trichotomous.aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.trichotomous.aux.h5 : ¬∀ {α : Type} (r : α → α → Prop) [inst : Std.Trichotomous r] (x x_1 : List α), ¬List.Lex r x_1 x → x = x_1 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.List.Lex.0.List.Lex.trichotomous.aux, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.trichotomous.aux.h6 : ¬∀ {α : Type} (r : α → α → Prop) [inst : Std.Trichotomous r] (x x_1 : List α), ¬List.Lex r x x_1 → x = x_1 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([0]) ([]) (by
  decide)) (by
  decide +kernel)

