import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/
-- _private.Iris.Std.GenSets.0.Iris.Std.FiniteSet.foldl_cons_comm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.FiniteSet.foldl_cons_comm.h3 : ¬∀ {A β : Type} {f : β → A → β} (l : List A) (init : β) (a : A), List.foldl f (f init a) l = f (List.foldl f init l) a := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun (a : Bool) (n : Nat) => n % 2 == 0) ([0]) (Bool.false) (1)) (by
  decide +kernel)

-- _private.Iris.Std.GenSets.0.Iris.Std.FiniteSet.foldl_perm, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.FiniteSet.foldl_perm.h6 : ¬∀ {A β : Type} {f : β → A → β},
        (∀ (b : β) (x y : A), f (f b x) y = f (f b y) x) →
          ∀ {l₁ l₂ : List A} (init : β), List.foldl f init l₁ = List.foldl f init l₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => a - b : Nat → Nat → Nat) (by
  grind) ([]) ([1]) (1)) (by
  decide +kernel)

