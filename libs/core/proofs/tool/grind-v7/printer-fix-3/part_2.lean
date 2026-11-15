import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.inst : ¬1 • 1 ≤ 0 • 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem0 : 0 ≤ 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem1 : 1 ≤ 1 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M]
        [inst_3 : Lean.Grind.OrderedAdd M] {k₁ k₂ : Nat} {x y : M}, k₁ ≤ k₂ → x ≤ y → k₁ • x ≤ k₂ • y := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => b ≤ a : LE Nat }) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) (@Lean.Grind.OrderedAdd.mk (Nat) (@instHAdd Nat
      (@Lean.Grind.AddCommMonoid.toAdd Nat
        (@Lean.Grind.NatModule.toAddCommMonoid Nat
          (@Lean.Grind.Semiring.toNatModule Nat (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat))))) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) (@Std.IsPreorder.mk Nat (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a)
      (fun (a : Nat) =>
        @Decidable.byContradiction (@LE.le Nat instLENat a a) (a.decLe a) fun (a_1 : Not (@LE.le Nat instLENat a a)) =>
          (fun (a : Nat) (a_2 : Not (@LE.le Nat instLENat a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le (@Nat.cast Int instNatCastInt a)
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt (@Nat.cast Int instNatCastInt a) (@Nat.cast Int instNatCastInt a)
                          (@Lean.Omega.Int.ofNat_lt_of_lt a a (@Nat.lt_of_not_le a a a_2))))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr (@Nat.cast Int instNatCastInt a)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                            (@Nat.cast Int instNatCastInt a)
                            (@Lean.Omega.LinearCombo.coordinate_eval_0 (@Nat.cast Int instNatCastInt a) (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr (@Nat.cast Int instNatCastInt a)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                                (@Nat.cast Int instNatCastInt a)
                                (@Lean.Omega.LinearCombo.coordinate_eval_0 (@Nat.cast Int instNatCastInt a)
                                  (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int (@Nat.cast Int instNatCastInt a) (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Nat) (a_1 : @LE.le Nat instLENat b a) (a_2 : @LE.le Nat instLENat c b) =>
      @Decidable.byContradiction (@LE.le Nat instLENat c a) (c.decLe a) fun (a_3 : Not (@LE.le Nat instLENat c a)) =>
        (fun (a b c : Nat) (a_4 : @LE.le Nat instLENat b a) (a_5 : @LE.le Nat instLENat c b)
              (a_6 : Not (@LE.le Nat instLENat c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList
                (@List.cons Int (@Nat.cast Int instNatCastInt a)
                  (@List.cons Int (@Nat.cast Int instNatCastInt b)
                    (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList
                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList
                    (@List.cons Int (@Nat.cast Int instNatCastInt a)
                      (@List.cons Int (@Nat.cast Int instNatCastInt b)
                        (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList
                      (@List.cons Int (@Nat.cast Int instNatCastInt a)
                        (@List.cons Int (@Nat.cast Int instNatCastInt b)
                          (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList
                        (@List.cons Int (@Nat.cast Int instNatCastInt a)
                          (@List.cons Int (@Nat.cast Int instNatCastInt b)
                            (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
                          (@Nat.cast Int instNatCastInt b))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int (@Nat.cast Int instNatCastInt a)
                              (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                        Int.instLEInt
                        (@Int.sub_nonneg_of_le (@Nat.cast Int instNatCastInt a) (@Nat.cast Int instNatCastInt b)
                          (@Lean.Omega.Int.ofNat_le_of_le b a a_4))
                        (@Eq.trans Int
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
                            (@Nat.cast Int instNatCastInt b))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr (@Nat.cast Int instNatCastInt a)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                            (@Nat.cast Int instNatCastInt b)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                              (@Nat.cast Int instNatCastInt a)
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 (@Nat.cast Int instNatCastInt a)
                                (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                              (@Nat.cast Int instNatCastInt b)
                              (@Lean.Omega.LinearCombo.coordinate_eval_1 (@Nat.cast Int instNatCastInt a)
                                (@Nat.cast Int instNatCastInt b)
                                (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList
                        (@List.cons Int (@Nat.cast Int instNatCastInt a)
                          (@List.cons Int (@Nat.cast Int instNatCastInt b)
                            (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList
                          (@List.cons Int (@Nat.cast Int instNatCastInt a)
                            (@List.cons Int (@Nat.cast Int instNatCastInt b)
                              (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt c)
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le (@Nat.cast Int instNatCastInt c)
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt (@Nat.cast Int instNatCastInt a) (@Nat.cast Int instNatCastInt c)
                              (@Lean.Omega.Int.ofNat_lt_of_lt a c (@Nat.lt_of_not_le c a a_6))))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt c)
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr (@Nat.cast Int instNatCastInt c)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                                (@Nat.cast Int instNatCastInt c)
                                (@Lean.Omega.LinearCombo.coordinate_eval_2 (@Nat.cast Int instNatCastInt a)
                                  (@Nat.cast Int instNatCastInt b) (@Nat.cast Int instNatCastInt c) (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@Nat.cast Int instNatCastInt a)
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                          (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                          (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr (@Nat.cast Int instNatCastInt a)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                          (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                          (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                          (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                            (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                                    (@Nat.cast Int instNatCastInt a)
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 (@Nat.cast Int instNatCastInt a)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                            (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                              (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                          (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                          (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                            (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                          (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                            (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                          (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                        (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                    (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                      (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList
                    (@List.cons Int (@Nat.cast Int instNatCastInt a)
                      (@List.cons Int (@Nat.cast Int instNatCastInt b)
                        (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt b)
                      (@Nat.cast Int instNatCastInt c))
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList
                        (@List.cons Int (@Nat.cast Int instNatCastInt a)
                          (@List.cons Int (@Nat.cast Int instNatCastInt b)
                            (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                    Int.instLEInt
                    (@Int.sub_nonneg_of_le (@Nat.cast Int instNatCastInt b) (@Nat.cast Int instNatCastInt c)
                      (@Lean.Omega.Int.ofNat_le_of_le c b a_5))
                    (@Eq.trans Int
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt b)
                        (@Nat.cast Int instNatCastInt c))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int (@Nat.cast Int instNatCastInt a)
                              (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int (@Nat.cast Int instNatCastInt a)
                              (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList
                          (@List.cons Int (@Nat.cast Int instNatCastInt a)
                            (@List.cons Int (@Nat.cast Int instNatCastInt b)
                              (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr (@Nat.cast Int instNatCastInt b)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int (@Nat.cast Int instNatCastInt a)
                              (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                        (@Nat.cast Int instNatCastInt c)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int (@Nat.cast Int instNatCastInt a)
                              (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                          (@Nat.cast Int instNatCastInt b)
                          (@Lean.Omega.LinearCombo.coordinate_eval_1 (@Nat.cast Int instNatCastInt a)
                            (@Nat.cast Int instNatCastInt b)
                            (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                          (@Nat.cast Int instNatCastInt c)
                          (@Lean.Omega.LinearCombo.coordinate_eval_2 (@Nat.cast Int instNatCastInt a)
                            (@Nat.cast Int instNatCastInt b) (@Nat.cast Int instNatCastInt c) (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int (@Nat.cast Int instNatCastInt a)
                              (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int (@Nat.cast Int instNatCastInt a)
                                (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                  (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int (@Nat.cast Int instNatCastInt a)
                              (@List.cons Int (@Nat.cast Int instNatCastInt b)
                                (@List.cons Int (@Nat.cast Int instNatCastInt c) (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (by (try dsimp only);   (intros; omega))) (0) (1) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem0 HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem1)

