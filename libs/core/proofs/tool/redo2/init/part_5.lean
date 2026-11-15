import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Vector.getElem_swap_of_ne, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.getElem_swap_of_ne.h9 : ¬∀ {α : Type} {n k : Nat} {xs : Vector α n} {i j : Nat} {hi : i < n} {hj : j < n} {hk : k < n},
        k ≠ j → (xs.swap i j hi hj)[k] = xs[k] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (2) (0) (#v[0, 1]) (0) (1) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide)

-- Vector.getElem_swap_of_ne, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.getElem_swap_of_ne.h10 : ¬∀ {α : Type} {n k : Nat} {xs : Vector α n} {i j : Nat} {hi : i < n} {hj : j < n} {hk : k < n},
        k ≠ i → (xs.swap i j hi hj)[k] = xs[k] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (2) (0) (#v[0, 1]) (1) (0) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide)

-- Array.getElem_swap_of_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_swap_of_ne.h7 : ¬∀ {α : Type} {k : Nat} {xs : Array α} {i j : Nat} {hi : i < xs.size} {hj : j < xs.size},
        k ≠ i → k ≠ j → k < (xs.swap i j hi hj).size := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (1) (#[0]) (0) (0) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide)

-- Array.getElem_swap_of_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_swap_of_ne.h8 : ¬∀ {α : Type} {k : Nat} {xs : Array α} {i j : Nat} {hi : i < xs.size} {hj : j < xs.size}
        {h : k < (xs.swap i j hi hj).size}, k ≠ j → GetElem.getElem (xs.swap i j hi hj) k h = GetElem.getElem xs k (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (0) (#[0, 1]) (0) (1) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide)

-- Array.getElem_swap_of_ne, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_swap_of_ne.h9 : ¬∀ {α : Type} {k : Nat} {xs : Array α} {i j : Nat} {hi : i < xs.size} {hj : j < xs.size}
        {h : k < (xs.swap i j hi hj).size}, k ≠ i → GetElem.getElem (xs.swap i j hi hj) k h = GetElem.getElem xs k (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (0) (#[0, 1]) (1) (0) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide)

-- List.maxIdxOn_eq_iff_eq_maxOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maxIdxOn_eq_iff_eq_maxOn.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [inst_3 : Std.IsLinearPreorder β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat},
        List.maxIdxOn f xs h = i ↔
          ∃ (hi : i < xs.length), xs[i] = List.maxOn f xs h ∧ ∀ (j : Nat) (hj : j < i), f xs[j] < f (List.maxOn f xs h) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (fun (a b : Nat) => (a % 2).decLe (b % 2)) (instLTNat) (@Std.IsLinearPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (fun n => n + 1 : Nat → Nat) ([1, 0]) hc_k0 (1)) (by
  decide)

-- List.max_map, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.max_map.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : Max β] [inst_3 : Std.IsLinearPreorder β] {xs : List α}
        {f : α → β} (h : xs ≠ []), (List.map f xs).max (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = f (List.maxOn f xs h) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (⟨fun a b => a - b⟩ : Max Nat) _ ([0, 1]) (fun n => n + 1 : Nat → Nat) hc_k0) (by
  decide)

-- Vector.getElem_replace_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.getElem_replace_of_ne.h2 : ¬∀ {α : Type} [inst : BEq α] {n : Nat} {a b : α} {xs : Vector α n} {i : Nat} {h : i < n},
        xs[i] ≠ a → (xs.replace a b)[i] = xs[i] := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (1) (0) (0) (#v[1]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- Vector.getElem_replace_of_ne, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.getElem_replace_of_ne.h9 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {n : Nat} {a b : α} {xs : Vector α n} {i : Nat} {h : i < n},
        (xs.replace a b)[i] = xs[i] := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (instBEqOfDecidableEq) _ (1) (0) (1) (#v[0]) (0) hc_k0) (by
  decide +kernel)

-- Vector.set_eraseIdx_le, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Vector.set_eraseIdx_le.h4.{u_1} : ∀ {α : Type u_1} {n : Nat} {xs : Vector α n} {i j : Nat} {a : α}, i ≤ j → j < n - 1 → i < n := by
  (intros; omega)

-- Vector.set_eraseIdx_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.set_eraseIdx_le.h7 : ¬∀ {α : Type} {n : Nat} {xs : Vector α n} {i : Nat} {w : i < n} {j : Nat} {a : α} (hj : j < n - 1),
        (xs.eraseIdx i w).set j a hj = (xs.set (j + 1) a (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)).eraseIdx i w := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (2) (#v[0, 0]) (1) hc_k0 (0) (1) hc_k1) (by
  decide +kernel)

-- Array.foldl_induction, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.foldl_induction.h5 : ¬∀ {α β : Type} {as : Array α} (motive : Nat → β → Prop) {init : β} {f : β → α → β},
        (∀ (i : Fin as.size) (b : β), motive (↑i) b → motive (↑i + 1) (f b as[i])) → motive as.size (Array.foldl f init as) := fun hc_h => absurd (@hc_h (Nat) (Nat) (#[]) (fun a b => a < b : Nat → Nat → Prop) (0) (fun a b => a - b : Nat → Nat → Nat) (by
  grind)) (by
  decide)

-- List.filterRevM_toArray', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.filterRevM_toArray'.h4 : ¬∀ {m : Type → Type} {α : Type} {start : Nat} [inst : Monad m] {l : List α} {p : α → m Bool},
        start = l.length → Array.filterRevM p l.toArray start = List.toArray <$> List.filterRevM p l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) ([0].length) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) ([0]) (fun (a : Nat) => (0, Bool.false)) rfl) (by
  decide)

-- Vector.replace_replicate_self, hypothesis 2: necessary
/- FAILED: 12:100: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.88 = true) = true
in the application
  id (Eq.refl true) | 3:25: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 3:167: `grind` has failed, use `+verbose` to obtain diagnostic information | 10:120: `grind` has failed, use `+verbose` to obtain diagnostic information | 12:100: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.94 = true) = true
in the application
  id (Eq.refl true) | 151:35: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 3:2: Tactic `decide` failed to reduce
  @decide (¬(0 < 1 → (Vector.replicate 1 1).replace 1 0 = Vector.cast ⋯ (#v[0] ++ Vector.replicate (1 - 1) 1)))
    instDecidableNot
to `true` or `false`.

Reduction got stuck at
  match (Vector.replicate 1 1).toArray.replace 1 0 with
  | { toList := [] } =>
    match (#v[0] ++ Vector.replicate (1 - 1) 1).toArray with
    | { toList := [] } => isTrue ⋯
    | { toList := head :: tail } => isFalse ⋯
  | { toList := a :: as } =>
    match (#v[0] ++ Vector.replicate  | 46:120: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.replace_replicate_self.h2 : ¬∀ {α : Type} [inst : BEq α] {n : Nat} {b a : α} (h : 0 < n),
        (Vector.replicate n a).replace a b =
          Vector.cast
            ((fun {n : Nat} (h : 0 < n) =>
                Decidable.byContradiction fun (a : ¬1 + (n - 1) = n) =>
                  (fun {n : Nat} (h : 0 < n) (a : ¬1 + (n - 1) = n) =>
                      Or.elim (Nat.lt_or_gt_of_ne a)
                        (fun (h₁ : 1 + (n - 1) < n) =>
                          Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                            (fun (h₁_1 : 1 ≤ n ∧ ↑(n - 1) = ↑n - ↑1) =>
                              Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                                (Lean.Omega.Constraint.combine_sat'
                                  (Lean.Omega.tidy_sat
                                    (Lean.Omega.Constraint.addEquality_sat
                                      (Eq.trans
                                        (Eq.symm
                                          (Eq.trans
                                            (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)
                                              (Eq.trans
                                                (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                                  (id (Eq.refl ↑1)))
                                                (Eq.symm
                                                  (Lean.Omega.LinearCombo.sub_eval
                                                    { coeffs := [1] : Lean.Omega.LinearCombo }
                                                    { const := 1 : Lean.Omega.LinearCombo }
                                                    (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                                { const := -1, coeffs := [1] : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                        (Int.sub_eq_zero_of_eq h₁_1.right))))
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq
                                      (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₁)))
                                      (Eq.trans
                                        (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                          (Eq.trans
                                            (Lean.Omega.Int.add_congr
                                              (Eq.trans (Int.natCast_add 1 (n - 1))
                                                (Eq.trans
                                                  (Lean.Omega.Int.add_congr (id (Eq.refl ↑1))
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.add_eval { const := 1 : Lean.Omega.LinearCombo }
                                                      { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                              (id (Eq.refl 1)))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.add_eval
                                                { const := 1, coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                                { const := 1 : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                            { const := 2, coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)]))))))))
                            fun (h₂ : n < 1 ∧ ↑(n - 1) = 0) =>
                            Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                              (Lean.Omega.Constraint.combine_sat'
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq
                                      (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂.left)))
                                      (Eq.trans
                                        (Lean.Omega.Int.sub_congr (id (Eq.refl ↑1))
                                          (Eq.trans
                                            (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                              (id (Eq.refl 1)))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.add_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                                { const := 1 : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.sub_eval { const := 1 : Lean.Omega.LinearCombo }
                                            { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))))
                                (Lean.Omega.Constraint.addInequality_sat
                                  (le_of_le_of_eq
                                    (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h)))
                                    (Eq.trans
                                      (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                        (id (Eq.refl (↑0 + 1))))
                                      (Eq.symm
                                        (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                          { const := 1 : Lean.Omega.LinearCombo }
                                          (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)]))))))))
                        fun (h₂ : 1 + (n - 1) > n) =>
                        Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                          (fun (h₁ : 1 ≤ n ∧ ↑(n - 1) = ↑n - ↑1) =>
                            Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                              (Lean.Omega.Constraint.combine_sat'
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.Constraint.addEquality_sat
                                    (Eq.trans
                                      (Eq.symm
                                        (Eq.trans
                                          (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)
                                            (Eq.trans
                                              (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                                (id (Eq.refl ↑1)))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                                  { const := 1 : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                          (Eq.symm
                                            (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                              { const := -1, coeffs := [1] : Lean.Omega.LinearCombo }
                                              (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                      (Int.sub_eq_zero_of_eq h₁.right))))
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.Constraint.addInequality_sat
                                    (le_of_le_of_eq
                                      (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂)))
                                      (Eq.trans
                                        (Lean.Omega.Int.sub_congr
                                          (Eq.trans (Int.natCast_add 1 (n - 1))
                                            (Eq.trans
                                              (Lean.Omega.Int.add_congr (id (Eq.refl ↑1))
                                                (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.add_eval { const := 1 : Lean.Omega.LinearCombo }
                                                  { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                          (Eq.trans
                                            (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                              (id (Eq.refl 1)))
                                            (Eq.symm
                                              (Lean.Omega.LinearCombo.add_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                                { const := 1 : Lean.Omega.LinearCombo }
                                                (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                        (Eq.symm
                                          (Lean.Omega.LinearCombo.sub_eval
                                            { const := 1, coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                            { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                            (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))))))
                          fun (h₂ : n < 1 ∧ ↑(n - 1) = 0) =>
                          Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                            (Lean.Omega.Constraint.combine_sat'
                              (Lean.Omega.tidy_sat
                                (Lean.Omega.Constraint.addInequality_sat
                                  (le_of_le_of_eq
                                    (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂.left)))
                                    (Eq.trans
                                      (Lean.Omega.Int.sub_congr (id (Eq.refl ↑1))
                                        (Eq.trans
                                          (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                            (id (Eq.refl 1)))
                                          (Eq.symm
                                            (Lean.Omega.LinearCombo.add_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                              { const := 1 : Lean.Omega.LinearCombo }
                                              (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))
                                      (Eq.symm
                                        (Lean.Omega.LinearCombo.sub_eval { const := 1 : Lean.Omega.LinearCombo }
                                          { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                          (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)])))))))
                              (Lean.Omega.Constraint.addInequality_sat
                                (le_of_le_of_eq
                                  (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h)))
                                  (Eq.trans
                                    (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                      (id (Eq.refl (↑0 + 1))))
                                    (Eq.symm
                                      (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                        { const := 1 : Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList [↑n, ↑(n - 1)]))))))))
                    h a)
              h)
            (#v[b] ++ Vector.replicate (n - 1) a) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) (1) (0) (1) hc_k0) (by
  decide +kernel)
-/

-- List.zipWithM'_eq_mapM_id_zipWith, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.zipWithM'_eq_mapM_id_zipWith.h5 : ¬∀ {α β γ : Type} {m : Type → Type} [inst : Monad m] {f : α → β → m γ} {as : List α} {bs : List β},
        List.zipWithM' f as bs = List.mapM id (List.zipWith f as bs) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) ([0]) ([0])) (by
  decide)

-- List.scanlM_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.scanlM_cons.h7 : Not
      (∀ {m : Type → Type} {α β : Type} {init : α} {x : β} {xs : List β} [inst : Monad m] {f : α → β → m α},
        @Eq (m (List α)) (@List.scanlM m α β inst f init (@List.cons β x xs))
          (@Bind.bind m (@Monad.toBind m inst) α (List α) (f init x) fun (__do_lift : α) =>
            @Bind.bind m (@Monad.toBind m inst) (List α) (List α) (@List.scanlM m α β inst f __do_lift xs)
              fun (__do_lift : List α) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List α) (@List.cons α init __do_lift))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun (a a_1 : Nat) =>
      @Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide)

-- List.mapM_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mapM_cons.h6 : Not
      (∀ {m : Type → Type} {α β : Type} {a : α} {l : List α} [inst : Monad m] {f : α → m β},
        @Eq (m (List β)) (@List.mapM m inst α β f (@List.cons α a l))
          (@Bind.bind m (@Monad.toBind m inst) β (List β) (f a) fun (__do_lift : β) =>
            @Bind.bind m (@Monad.toBind m inst) (List β) (List β) (@List.mapM m inst α β f l) fun (__do_lift_1 : List β) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List β)
                (@List.cons β __do_lift __do_lift_1))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun (a : Nat) =>
      @Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide)

-- List.filterMapM_toArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.filterMapM_toArray.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {l : List α} {f : α → m (Option β)},
        Array.filterMapM f l.toArray = List.toArray <$> List.filterMapM f l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) ([]) (fun (a : Nat) => (0, Option.none))) (by
  decide)

-- List.mapM_eq_reverse_foldlM_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mapM_eq_reverse_foldlM_cons.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {f : α → m β} {l : List α},
        List.mapM f l = List.reverse <$> List.foldlM (fun (acc : List β) (a : α) => (fun (x : β) => x :: acc) <$> f a) [] l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, 0)) ([])) (by
  decide)

-- List.mapM_toArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mapM_toArray.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {f : α → m β} {l : List α},
        Array.mapM f l.toArray = List.toArray <$> List.mapM f l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, 0)) ([])) (by
  decide +kernel)

-- List.ofFnM_pure_comp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ofFnM_pure_comp.h3 : Not
      (∀ {m : Type → Type} {α : Type} [inst : Monad m] {n : Nat} {f : Fin n → α},
        @Eq (m (List α))
          (@List.ofFnM m α n inst
            (@Function.comp (Fin n) α (m α) (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) α) f))
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List α) (@List.ofFn α n f))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
      @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide)

-- Vector.ofFnM_succ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.ofFnM_succ.h4 : Not
      (∀ {m : Type → Type} {α : Type} {n : Nat} [inst : Monad m]
        {f :
          Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            m α},
        @Eq
          (m
            (Vector α
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@Vector.ofFnM m α
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            inst f)
          (@Bind.bind m (@Monad.toBind m inst) (Vector α n)
            (Vector α
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Vector.ofFnM m α n inst fun (i : Fin n) => f (@Fin.castSucc n i)) fun (as : Vector α n) =>
            @Bind.bind m (@Monad.toBind m inst) α
              (Vector α
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (f (Fin.last n)) fun (a : α) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                (Vector α
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Vector.push α n as a))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun
        (a :
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide +kernel)

-- List.toList_iterM, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toList_iterM.h3 : ¬∀ {m : Type → Type} [inst : Monad m] {β : Type} {l : List β}, (l.iterM m).toList = Pure.pure l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (Nat) ([])) (by
  decide)

