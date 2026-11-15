import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- List.le_maxIdxOn_of_apply_getElem_lt_apply_getElem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_maxIdxOn_of_apply_getElem_lt_apply_getElem.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [inst_3 : Std.IsLinearPreorder β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat} (hi : i < xs.length),
        (∀ (j : Nat) (x : j < i), f xs[j] < f xs[i]) → i ≤ List.maxIdxOn f xs h := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (fun (a b : Nat) => (a % 2).decLe (b % 2)) (instLTNat) (@Std.IsLinearPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (fun n => n + 1 : Nat → Nat) ([0, 1]) hc_k0 (1) hc_k1 hc_k2) (by
  decide)

-- List.maxOn_eq_max, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maxOn_eq_max.h5 : ¬∀ {α β : Type} [inst : Max α] [inst_1 : LE α] [inst_2 : DecidableLE α] [inst_3 : LE β] [inst_4 : DecidableLE β]
        {f : α → β} {l : List α} {h : l ≠ []}, (∀ (a b : α), f a ≤ f b ↔ a ≤ b) → List.maxOn f l h = l.max h := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (⟨fun a b => a - b⟩ : Max Nat) (instLENat) (Nat.decLe) (instLENat) (Nat.decLe) (fun n => n + 1 : Nat → Nat) ([0, 1]) hc_k0 hc_k1) (by
  (simp <;> decide))

-- List.maxOn_eq_max, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maxOn_eq_max.h11 : ¬∀ {α β : Type} [inst : Max α] [inst_1 : LE α] [inst_2 : DecidableLE α] [inst_3 : Std.LawfulOrderLeftLeaningMax α]
        [inst_4 : LE β] [inst_5 : DecidableLE β] {f : α → β} {l : List α} {h : l ≠ []}, List.maxOn f l h = l.max h := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (Nat.instMax) (instLENat) (Nat.decLe) _ (instLENat) (Nat.decLe) (fun _ => 0 : Nat → Nat) ([0, 1]) hc_k0) (by
  decide)

-- List.minIdxOn_eq_iff_eq_minOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minIdxOn_eq_iff_eq_minOn.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [inst_3 : Std.IsLinearPreorder β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat},
        List.minIdxOn f xs h = i ↔
          ∃ (hi : i < xs.length), xs[i] = List.minOn f xs h ∧ ∀ (j : Nat) (hj : j < i), f (List.minOn f xs h) < f xs[j] := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (fun (a b : Nat) => (a % 2).decLe (b % 2)) (instLTNat) (@Std.IsLinearPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (fun n => n + 1 : Nat → Nat) ([0, 1]) hc_k0 (1)) (by
  decide)

-- List.minIdxOn_eq_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minIdxOn_eq_iff.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [inst_3 : Std.IsLinearPreorder β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat},
        List.minIdxOn f xs h = i ↔
          ∃ (h : i < xs.length),
            (∀ (j : Nat) (x : j < xs.length), f xs[i] ≤ f xs[j]) ∧ ∀ (j : Nat) (x : j < i), f xs[i] < f xs[j] := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (fun (a b : Nat) => (a % 2).decLe (b % 2)) (instLTNat) (@Std.IsLinearPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (fun n => n + 1 : Nat → Nat) ([0, 1]) hc_k0 (1)) (by
  decide)

-- Vector.insertIdx_eraseIdx_of_ge, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.insertIdx_eraseIdx_of_ge.h8 : ¬∀ {α : Type} {a : α} {n i j : Nat} {xs : Vector α n} (w₁ : i < n) (w₂ : j ≤ n - 1),
        (xs.eraseIdx i w₁).insertIdx j a w₂ = Vector.cast (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) ((xs.insertIdx (j + 1) a (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)).eraseIdx i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (0) (2) (1) (0) (#v[0, 1]) hc_k0 hc_k1) (by
  decide +kernel)

-- Array.insertIdx_eraseIdx_of_ge, hypothesis 7: necessary
/- FAILED: 11:100: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.77 = true) = true
in the application
  id (Eq.refl true) | 20:20: Function expected at
  (fun {α} {i j} {as} w₁ w₂ a =>
      Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
        (fun h₁ =>
          Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl true)))
            (Lean.Omega.Constraint.combine_sat'
              (Lean.Omega.tidy_sat
                (Lean.Omega.Constraint.addInequality_sat
                  (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le w₂))
                    (Eq.trans
                    | 3:293: `grind` has failed, use `+verbose` to obtain diagnostic information | 11:116: `grind` has failed, use `+verbose` to obtain diagnostic information | 11:100: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.114 = true) = true
in the application
  id (Eq.refl true) | 130:33: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 3:266: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 35:71: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.insertIdx_eraseIdx_of_ge.h7 : ¬∀ {α : Type} {a : α} {i j : Nat} {as : Array α} (w₁ : i < as.size) (w₂ : j ≤ (as.eraseIdx i w₁).size),
        (as.eraseIdx i w₁).insertIdx j a w₂ =
          (as.insertIdx (j + 1) a
                ((fun {α : Type} {i j : Nat} {as : Array α} (w₁ : i < as.size) (w₂ : j ≤ (as.eraseIdx i w₁).size) =>
                    Decidable.byContradiction fun (a : ¬j + 1 ≤ as.size) =>
                      (fun {α : Type} {i j : Nat} {as : Array α} (w₁ : i < as.size) (w₂ : j ≤ as.size - 1)
                            (a : ¬j + 1 ≤ as.size) =>
                          Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                            (fun (h₁ : 1 ≤ as.size ∧ ↑(as.size - 1) = ↑as.size - ↑1) =>
                              Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                                (Lean.Omega.Constraint.combine_sat'
                                  (Lean.Omega.tidy_sat
                                    (Lean.Omega.Constraint.addInequality_sat
                                      (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le w₂))
                                        (Eq.trans
                                          (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                            (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2))
                                          (Eq.symm
                                            (Lean.Omega.LinearCombo.sub_eval
                                              { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                              { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                              (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))))
                                  (Lean.Omega.tidy_sat
                                    (Lean.Omega.combo_sat'
                                      { lowerBound := Option.some 1, upperBound := Option.some 1 : Lean.Omega.Constraint }
                                      { lowerBound := Option.none, upperBound := Option.some 0 : Lean.Omega.Constraint }
                                      (-1) [1, 0, 0, -1] 1 [1, 0, -1]
                                      (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])
                                      (Lean.Omega.tidy_sat
                                        (Lean.Omega.Constraint.addEquality_sat
                                          (Eq.trans
                                            (Eq.symm
                                              (Eq.trans
                                                (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                                  (Eq.trans
                                                    (Lean.Omega.Int.sub_congr
                                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0) (id (Eq.refl ↑1)))
                                                    (Eq.symm
                                                      (Lean.Omega.LinearCombo.sub_eval
                                                        { coeffs := [1] : Lean.Omega.LinearCombo }
                                                        { const := 1 : Lean.Omega.LinearCombo }
                                                        (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                                (Eq.symm
                                                  (Lean.Omega.LinearCombo.sub_eval
                                                    { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                    { const := -1, coeffs := [1] : Lean.Omega.LinearCombo }
                                                    (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                            (Int.sub_eq_zero_of_eq h₁.right))))
                                      (Lean.Omega.tidy_sat
                                        (Lean.Omega.Constraint.addInequality_sat
                                          (le_of_le_of_eq
                                            (Int.sub_nonneg_of_le
                                              (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt (Nat.lt_of_not_le a))))
                                            (Eq.trans
                                              (Lean.Omega.Int.sub_congr
                                                (Eq.trans (Int.natCast_add j 1)
                                                  (Eq.trans
                                                    (Lean.Omega.Int.add_congr
                                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2) (id (Eq.refl ↑1)))
                                                    (Eq.symm
                                                      (Lean.Omega.LinearCombo.add_eval
                                                        { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                        { const := 1 : Lean.Omega.LinearCombo }
                                                        (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                                (Eq.trans
                                                  (Lean.Omega.Int.add_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0) (id (Eq.refl 1)))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.add_eval
                                                      { coeffs := [1] : Lean.Omega.LinearCombo }
                                                      { const := 1 : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.sub_eval
                                                  { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                  { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))))))))
                            fun (h₂ : as.size < 1 ∧ ↑(as.size - 1) = 0) =>
                            Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                              (Lean.Omega.Constraint.combine_sat'
                                (Lean.Omega.Constraint.addInequality_sat
                                  (le_of_le_of_eq (Int.natCast_nonneg i)
                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)))
                                (Lean.Omega.tidy_sat
                                  (Lean.Omega.combo_sat'
                                    { lowerBound := Option.some 0, upperBound := Option.some 0 : Lean.Omega.Constraint }
                                    { lowerBound := Option.some 1, upperBound := Option.none : Lean.Omega.Constraint } (-1)
                                    [1] 1 [1, -1] (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])
                                    (Lean.Omega.Constraint.combine_sat'
                                      (Lean.Omega.tidy_sat
                                        (Lean.Omega.Constraint.addInequality_sat
                                          (le_of_le_of_eq
                                            (Int.sub_nonneg_of_le
                                              (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂.left)))
                                            (Eq.trans
                                              (Lean.Omega.Int.sub_congr (id (Eq.refl ↑1))
                                                (Eq.trans
                                                  (Lean.Omega.Int.add_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0) (id (Eq.refl 1)))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.add_eval
                                                      { coeffs := [1] : Lean.Omega.LinearCombo }
                                                      { const := 1 : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.sub_eval { const := 1 : Lean.Omega.LinearCombo }
                                                  { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))))
                                      (Lean.Omega.Constraint.addInequality_sat
                                        (le_of_le_of_eq (Int.natCast_nonneg as.size)
                                          (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0))))
                                    (Lean.Omega.Constraint.addInequality_sat
                                      (le_of_le_of_eq
                                        (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt w₁)))
                                        (Eq.trans
                                          (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                            (Eq.trans
                                              (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)
                                                (id (Eq.refl 1)))
                                              (Eq.symm
                                                (Lean.Omega.LinearCombo.add_eval
                                                  { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                                  { const := 1 : Lean.Omega.LinearCombo }
                                                  (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                          (Eq.symm
                                            (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                              { const := 1, coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                              (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)]))))))))))
                        w₁ (Eq.mp (congrArg (LE.le j) (Array.size_eraseIdx i w₁)) w₂) a)
                  w₁ w₂)).eraseIdx
            i
            ((fun {α : Type} {a : α} {i j : Nat} {as : Array α} (w₁ : i < as.size) (w₂ : j ≤ (as.eraseIdx i w₁).size) =>
                Eq.mpr
                  (id
                    (congrArg (LT.lt i)
                      (Array.size_insertIdx
                        ((fun {α : Type} {i j : Nat} {as : Array α} (w₁ : i < as.size) (w₂ : j ≤ (as.eraseIdx i w₁).size) =>
                            Decidable.byContradiction fun (a : ¬j + 1 ≤ as.size) =>
                              (fun {α : Type} {i j : Nat} {as : Array α} (w₁ : i < as.size) (w₂ : j ≤ as.size - 1)
                                    (a : ¬j + 1 ≤ as.size) =>
                                  Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                                    (fun (h₁ : 1 ≤ as.size ∧ ↑(as.size - 1) = ↑as.size - ↑1) =>
                                      Lean.Omega.Constraint.not_sat'_of_isImpossible
                                        (of_decide_eq_true (id (Eq.refl Bool.true)))
                                        (Lean.Omega.Constraint.combine_sat'
                                          (Lean.Omega.tidy_sat
                                            (Lean.Omega.Constraint.addInequality_sat
                                              (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le w₂))
                                                (Eq.trans
                                                  (Lean.Omega.Int.sub_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.sub_eval
                                                      { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                      { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))))
                                          (Lean.Omega.tidy_sat
                                            (Lean.Omega.combo_sat'
                                              { lowerBound := Option.some 1, upperBound := Option.some 1 :
                                                Lean.Omega.Constraint }
                                              { lowerBound := Option.none, upperBound := Option.some 0 :
                                                Lean.Omega.Constraint }
                                              (-1) [1, 0, 0, -1] 1 [1, 0, -1]
                                              (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])
                                              (Lean.Omega.tidy_sat
                                                (Lean.Omega.Constraint.addEquality_sat
                                                  (Eq.trans
                                                    (Eq.symm
                                                      (Eq.trans
                                                        (Lean.Omega.Int.sub_congr
                                                          (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                                          (Eq.trans
                                                            (Lean.Omega.Int.sub_congr
                                                              (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                                              (id (Eq.refl ↑1)))
                                                            (Eq.symm
                                                              (Lean.Omega.LinearCombo.sub_eval
                                                                { coeffs := [1] : Lean.Omega.LinearCombo }
                                                                { const := 1 : Lean.Omega.LinearCombo }
                                                                (Lean.Omega.Coeffs.ofList
                                                                  [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                                        (Eq.symm
                                                          (Lean.Omega.LinearCombo.sub_eval
                                                            { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                                            { const := -1, coeffs := [1] : Lean.Omega.LinearCombo }
                                                            (Lean.Omega.Coeffs.ofList
                                                              [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                                    (Int.sub_eq_zero_of_eq h₁.right))))
                                              (Lean.Omega.tidy_sat
                                                (Lean.Omega.Constraint.addInequality_sat
                                                  (le_of_le_of_eq
                                                    (Int.sub_nonneg_of_le
                                                      (Int.add_one_le_of_lt
                                                        (Lean.Omega.Int.ofNat_lt_of_lt (Nat.lt_of_not_le a))))
                                                    (Eq.trans
                                                      (Lean.Omega.Int.sub_congr
                                                        (Eq.trans (Int.natCast_add j 1)
                                                          (Eq.trans
                                                            (Lean.Omega.Int.add_congr
                                                              (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                                              (id (Eq.refl ↑1)))
                                                            (Eq.symm
                                                              (Lean.Omega.LinearCombo.add_eval
                                                                { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                                { const := 1 : Lean.Omega.LinearCombo }
                                                                (Lean.Omega.Coeffs.ofList
                                                                  [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                                        (Eq.trans
                                                          (Lean.Omega.Int.add_congr
                                                            (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                                            (id (Eq.refl 1)))
                                                          (Eq.symm
                                                            (Lean.Omega.LinearCombo.add_eval
                                                              { coeffs := [1] : Lean.Omega.LinearCombo }
                                                              { const := 1 : Lean.Omega.LinearCombo }
                                                              (Lean.Omega.Coeffs.ofList
                                                                [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                                      (Eq.symm
                                                        (Lean.Omega.LinearCombo.sub_eval
                                                          { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                                          { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                                          (Lean.Omega.Coeffs.ofList
                                                            [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))))))))
                                    fun (h₂ : as.size < 1 ∧ ↑(as.size - 1) = 0) =>
                                    Lean.Omega.Constraint.not_sat'_of_isImpossible
                                      (of_decide_eq_true (id (Eq.refl Bool.true)))
                                      (Lean.Omega.Constraint.combine_sat'
                                        (Lean.Omega.Constraint.addInequality_sat
                                          (le_of_le_of_eq (Int.natCast_nonneg i)
                                            (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)))
                                        (Lean.Omega.tidy_sat
                                          (Lean.Omega.combo_sat'
                                            { lowerBound := Option.some 0, upperBound := Option.some 0 :
                                              Lean.Omega.Constraint }
                                            { lowerBound := Option.some 1, upperBound := Option.none :
                                              Lean.Omega.Constraint }
                                            (-1) [1] 1 [1, -1] (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])
                                            (Lean.Omega.Constraint.combine_sat'
                                              (Lean.Omega.tidy_sat
                                                (Lean.Omega.Constraint.addInequality_sat
                                                  (le_of_le_of_eq
                                                    (Int.sub_nonneg_of_le
                                                      (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂.left)))
                                                    (Eq.trans
                                                      (Lean.Omega.Int.sub_congr (id (Eq.refl ↑1))
                                                        (Eq.trans
                                                          (Lean.Omega.Int.add_congr
                                                            (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                                            (id (Eq.refl 1)))
                                                          (Eq.symm
                                                            (Lean.Omega.LinearCombo.add_eval
                                                              { coeffs := [1] : Lean.Omega.LinearCombo }
                                                              { const := 1 : Lean.Omega.LinearCombo }
                                                              (Lean.Omega.Coeffs.ofList
                                                                [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                                      (Eq.symm
                                                        (Lean.Omega.LinearCombo.sub_eval
                                                          { const := 1 : Lean.Omega.LinearCombo }
                                                          { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                                          (Lean.Omega.Coeffs.ofList
                                                            [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))))
                                              (Lean.Omega.Constraint.addInequality_sat
                                                (le_of_le_of_eq (Int.natCast_nonneg as.size)
                                                  (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0))))
                                            (Lean.Omega.Constraint.addInequality_sat
                                              (le_of_le_of_eq
                                                (Int.sub_nonneg_of_le
                                                  (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt w₁)))
                                                (Eq.trans
                                                  (Lean.Omega.Int.sub_congr
                                                    (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                                    (Eq.trans
                                                      (Lean.Omega.Int.add_congr
                                                        (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1) (id (Eq.refl 1)))
                                                      (Eq.symm
                                                        (Lean.Omega.LinearCombo.add_eval
                                                          { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                                          { const := 1 : Lean.Omega.LinearCombo }
                                                          (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)])))))
                                                  (Eq.symm
                                                    (Lean.Omega.LinearCombo.sub_eval
                                                      { coeffs := [1] : Lean.Omega.LinearCombo }
                                                      { const := 1, coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                                      (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑j, ↑(as.size - 1)]))))))))))
                                w₁ (Eq.mp (congrArg (LE.le j) (Array.size_eraseIdx i w₁)) w₂) a)
                          w₁ w₂))))
                  (Decidable.byContradiction fun (a : ¬i < as.size + 1) =>
                    (fun {α : Type} {i j : Nat} {as : Array α} (w₁ : i < as.size) (a : ¬i < as.size + 1) =>
                        Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                          (Lean.Omega.Constraint.combine_sat'
                            (Lean.Omega.tidy_sat
                              (Lean.Omega.Constraint.addInequality_sat
                                (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt a)))
                                  (Eq.trans
                                    (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)
                                      (Eq.trans (Int.natCast_add as.size 1)
                                        (Eq.trans
                                          (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                            (id (Eq.refl ↑1)))
                                          (Eq.symm
                                            (Lean.Omega.LinearCombo.add_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                              { const := 1 : Lean.Omega.LinearCombo }
                                              (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑(as.eraseIdx i w₁).size, ↑j]))))))
                                    (Eq.symm
                                      (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                        { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑(as.eraseIdx i w₁).size, ↑j])))))))
                            (Lean.Omega.Constraint.addInequality_sat
                              (le_of_le_of_eq
                                (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt w₁)))
                                (Eq.trans
                                  (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                    (Eq.trans
                                      (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)
                                        (id (Eq.refl 1)))
                                      (Eq.symm
                                        (Lean.Omega.LinearCombo.add_eval { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                          { const := 1 : Lean.Omega.LinearCombo }
                                          (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑(as.eraseIdx i w₁).size, ↑j])))))
                                  (Eq.symm
                                    (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                      { const := 1, coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                      (Lean.Omega.Coeffs.ofList [↑as.size, ↑i, ↑(as.eraseIdx i w₁).size, ↑j]))))))))
                      w₁ a))
              w₁ w₂) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (0) (1) (0) (#[0, 1]) hc_k0 hc_k1) (by
  decide +kernel)
-/

-- Vector.toArray_mapM, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toArray_mapM.h5 : ¬∀ {m : Type → Type} {α β : Type} {n : Nat} [inst : Monad m] {f : α → m β} {xs : Vector α n},
        Vector.toArray <$> Vector.mapM f xs = Array.mapM f xs.toArray := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, 0)) (#v[])) (by
  decide +kernel)

-- List.flatMapM_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.flatMapM_cons.h6 : Not
      (∀ {m : Type → Type} {α β : Type} {a : α} {l : List α} [inst : Monad m] {f : α → m (List β)},
        @Eq (m (List β)) (@List.flatMapM m inst α β f (@List.cons α a l))
          (@Bind.bind m (@Monad.toBind m inst) (List β) (List β) (f a) fun (bs : List β) =>
            @Bind.bind m (@Monad.toBind m inst) (List β) (List β) (@List.flatMapM m inst α β f l)
              fun (__do_lift : List β) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List β)
                (@HAppend.hAppend (List β) (List β) (List β) (@instHAppendOfAppend (List β) (@List.instAppend β)) bs
                  __do_lift))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun (a : Nat) => @Prod.mk Nat (List Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))) (by
  decide)

-- List.scanrM_reverse, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.scanrM_reverse.h6 : ¬∀ {m : Type → Type} {α β : Type} {init : β} {as : List α} [inst : Monad m] {f : α → β → m β},
        List.scanrM f init as.reverse = List.reverse <$> List.scanlM (flip f) init as := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ([]) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0))) (by
  decide)

-- Array.forM_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.forM_congr.h5 : ¬∀ {m : Type → Type} {α : Type} [inst : Monad m] {as bs : Array α} {f : α → m PUnit}, ForM.forM as f = ForM.forM bs f := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (instMonadOption) (#[]) (#[0]) (fun (a : Nat) => Option.none)) (by
  decide)

-- Array.toList_mapIdxM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.toList_mapIdxM.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {xs : Array α} {f : Nat → α → m β},
        Array.toList <$> Array.mapIdxM f xs = List.mapIdxM f xs.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (#[]) (fun (a a_1 : Nat) => (0, 0))) (by
  decide)

-- List.forM_toArray', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forM_toArray'.h6 : ¬∀ {m : Type → Type} {α : Type} {stop : Nat} [inst : Monad m] (l : List α) (f : α → m PUnit),
        Array.forM f l.toArray 0 stop = l.forM f := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (0) (instMonadOption) ([0]) (fun (a : Nat) => Option.none)) (by
  decide)

-- Array.mapM_eq_mapM_toList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.mapM_eq_mapM_toList.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {f : α → m β} {xs : Array α},
        Array.mapM f xs = List.toArray <$> List.mapM f xs.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, 0)) (#[])) (by
  decide +kernel)

-- List.idxOf?_eq_some_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf?_eq_some_iff.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α} {a : α} {i : Nat},
        List.idxOf? a l = Option.some i ↔ ∃ (h : i < l.length), l[i] = a ∧ ∀ (j : Nat) (x : j < i), ¬l[j] = a := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) (1) (0)) (by
  decide)

-- Array.map_toList_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.map_toList_inj.h3 : ¬∀ {m : Type → Type} {α : Type} [inst : Monad m] {xs ys : m (Array α)},
        Array.toList <$> xs = Array.toList <$> ys ↔ xs = ys := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) ({ pure := some, bind := Option.bind, map := fun _ _ => none } : Monad Option) (Option.none) (Option.some #[])) (by
  decide)

-- Array.toList_filterRevM, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.toList_filterRevM.h3 : ¬∀ {m : Type → Type} {α : Type} [inst : Monad m] {xs : Array α} {p : α → m Bool},
        Array.toList <$> Array.filterRevM p xs = List.filterRevM p xs.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (#[]) (fun (a : Nat) => (0, Bool.false))) (by
  decide)

-- List.ofFnM_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ofFnM_zero.h3 : ¬∀ {m : Type → Type} {α : Type} [inst : Monad m] {f : Fin 0 → m α}, List.ofFnM f = Pure.pure [] := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Fin 0) => (0, 0))) (by
  decide)

