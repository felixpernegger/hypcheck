import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.mem_encPrefixes, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.mem_encPrefixes.h5 : ¬∀ {α : Type} {encIn : α ↪ List Bool} {S : Finset α} {p : List Bool} {a : α},
        p <+: encIn a → p ∈ Turing.MultiTapeTM.encPrefixes encIn S := fun hc_h => absurd (@hc_h (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (∅ : Finset Bool) ([Bool.false]) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.mem_encPrefixes, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.mem_encPrefixes.h6 : ¬∀ {α : Type} {encIn : α ↪ List Bool} {S : Finset α} {p : List Bool} {a : α},
        a ∈ S → p ∈ Turing.MultiTapeTM.encPrefixes encIn S := fun hc_h => absurd (@hc_h (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) ({true} : Finset Bool) ([Bool.false]) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.prefix_mem_encPrefixes, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.prefix_mem_encPrefixes.h5 : ¬∀ {α : Type} {encIn : α ↪ List Bool} {S : Finset α} {p q : List Bool},
        q <+: p → q ∈ Turing.MultiTapeTM.encPrefixes encIn S := fun hc_h => absurd (@hc_h (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (∅ : Finset Bool) ([Bool.false]) ([Bool.false]) (by
  decide)) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.prefix_mem_encPrefixes, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.prefix_mem_encPrefixes.h6 : ¬∀ {α : Type} {encIn : α ↪ List Bool} {S : Finset α} {p q : List Bool},
        p ∈ Turing.MultiTapeTM.encPrefixes encIn S → q ∈ Turing.MultiTapeTM.encPrefixes encIn S := fun hc_h => absurd (@hc_h (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (∅ : Finset Bool) ([]) ([Bool.false]) (by
  decide)) (by
  decide +kernel)

-- _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.0.Turing.MultiTapeTM.reaches_write, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.reaches_write.h7 : ¬∀ {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {S : Finset α} {out : List Bool} (a a : α),
        a ∉ S → encOut (f a) = out := fun hc_h => absurd (@hc_h (Bool) (Bool) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) ({ toFun := fun (b : Bool) => [b, b], inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ List Bool }) (not : Bool → Bool) (∅ : Finset Bool) ([]) (Bool.false)) (by
  decide +kernel)

-- _private.Cslib.Computability.Circuit.Boolean.Lupanov.0.Cslib.Circuits.Boolean.Lupanov.mainTerm_le, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.mainTerm_le.h2.gneg : ∀ (P n : ℕ),
      ¬5 * n.log2 < n →
        (P + 1) * (5 * n.log2) ≤ n →
          P * n * ((2 ^ (3 * n.log2) / (n - 5 * n.log2) + 1) * 2 ^ (n - 3 * n.log2)) ≤
            (P + 1) * 2 ^ n + (P + 1) * n * 2 ^ (n - 3 * n.log2) := by
  (intros; grind)
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.mainTerm_le.h2 : ∀ (P n : ℕ),
      (P + 1) * (5 * n.log2) ≤ n →
        P * n * ((2 ^ (3 * n.log2) / (n - 5 * n.log2) + 1) * 2 ^ (n - 3 * n.log2)) ≤
          (P + 1) * 2 ^ n + (P + 1) * n * 2 ^ (n - 3 * n.log2) := by
  intro hc_x0 hc_x1 hc_x3
  exact Classical.byCases (fun hc_h => @Cslib.Circuits.Boolean.Lupanov.mainTerm_le hc_x0 hc_x1 hc_h hc_x3) (fun hc_hn => @HypCheckProof.Cslib.Circuits.Boolean.Lupanov.mainTerm_le.h2.gneg hc_x0 hc_x1 hc_hn hc_x3)

-- _private.Cslib.Computability.Circuit.Boolean.Lupanov.0.Cslib.Circuits.Boolean.Lupanov.mainTerm_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.mainTerm_le.h3 : ¬∀ (P n : ℕ),
        5 * n.log2 < n →
          P * n * ((2 ^ (3 * n.log2) / (n - 5 * n.log2) + 1) * 2 ^ (n - 3 * n.log2)) ≤
            (P + 1) * 2 ^ n + (P + 1) * n * 2 ^ (n - 3 * n.log2) := fun hc_h => absurd (@hc_h (1) (32) (by
  decide)) (by
  decide +kernel)

-- _private.Cslib.Computability.Circuit.Boolean.LupanovConstruction.0.Cslib.Circuits.Boolean.Lupanov.table_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.table_eq.h4 : ¬∀ {k d s : ℕ} (f : Cslib.BooleanFunction (k + d)), Cslib.Circuits.Boolean.Lupanov.table f s = f := fun hc_h => absurd (@hc_h (0) (0) (0) (fun (a : Cslib.BitString (0 + 0)) => Bool.true)) (by
  decide +kernel)

-- _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.0.Cslib.Query.finPrefix_natEmbedding_finVal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Query.finPrefix_natEmbedding_finVal.h2 : ¬∀ {n : ℕ} {α : Type} (i : Fin n), ↑n ≤ Cardinal.mk α := fun hc_h => absurd (@hc_h (3) (Bool) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3))) (by
  norm_num)

-- _private.Cslib.Foundations.Semantics.LTS.ExampleTermination.0.Cslib.LTS.Example.successorLTS_transGen_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Example.successorLTS_transGen_lt.h2 : ¬∀ {n m : ℕ}, n < m := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- _private.Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas.0.Cslib.Query.mergeSort_bound, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Query.mergeSort_bound.h1 : ¬∀ (n : ℕ),
        (n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n / 2 * Nat.clog 2 (n / 2) + ((n + 1) / 2 + n / 2)) ≤ n * Nat.clog 2 n := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

