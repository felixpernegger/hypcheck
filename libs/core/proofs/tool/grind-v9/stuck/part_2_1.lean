import Init

noncomputable instance HypCheckDec.ppolyNonNeg (p : Lean.Grind.CommRing.PPoly) : Decidable p.NonNeg :=
  Lean.Grind.CommRing.PPoly.rec (motive := fun p => Decidable p.NonNeg)
    (fun k => (inferInstance : Decidable (0 ≤ k)))
    (fun k _ _ _ ih => @instDecidableAnd (0 ≤ k) _ inferInstance ih) p
noncomputable instance HypCheckDec.ppolyDeg (B D : Nat) (p : Lean.Grind.CommRing.PPoly) : Decidable (p.Deg B D) :=
  Lean.Grind.CommRing.PPoly.rec (motive := fun p => Decidable (p.Deg B D))
    (fun _ => isTrue trivial)
    (fun _ _ v _ ih => @instDecidableAnd (Lean.Grind.CommRing.PPoly.dsum B v ≤ D) _ (Nat.decLe _ _) ih) p
noncomputable instance HypCheckDec.polyNonnegCoeffs (p : Lean.Grind.CommRing.Poly) : Decidable p.NonnegCoeffs :=
  Lean.Grind.CommRing.Poly.rec (motive := fun p => Decidable p.NonnegCoeffs)
    (fun c => if h : c ≥ 0 then isTrue (.num c h) else isFalse (fun hc => by cases hc; contradiction))
    (fun a m p ih => if h : a ≥ 0 then
        (match ih with
         | isTrue hp => isTrue (.add a m p h hp)
         | isFalse hp => isFalse (fun hc => by cases hc; contradiction))
      else isFalse (fun hc => by cases hc; contradiction)) p
noncomputable instance HypCheckDec.polyNonnegList (ps : List Lean.Grind.CommRing.Poly) : Decidable (Lean.Grind.CommRing.Poly.NonnegList ps) :=
  List.rec (motive := fun ps => Decidable (Lean.Grind.CommRing.Poly.NonnegList ps)) (isTrue trivial)
    (fun p _ ih => @instDecidableAnd p.NonnegCoeffs _ inferInstance ih) ps
noncomputable instance HypCheckDec.klistAllZero {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (ls : Lean.Grind.CommRing.KList) : Decidable (ls.AllZero ctx) :=
  Lean.Grind.CommRing.KList.rec (motive := fun ls => Decidable (ls.AllZero ctx)) (isTrue trivial)
    (fun _ _ q _ ih => @instDecidableAnd (q.denote ctx = 0) _ inferInstance ih) ls
noncomputable instance HypCheckDec.mlistAllZero {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (ls : Lean.Grind.CommRing.MList) : Decidable (ls.AllZero ctx) :=
  Lean.Grind.CommRing.MList.rec (motive := fun ls => Decidable (ls.AllZero ctx)) (isTrue trivial)
    (fun _ q _ ih => @instDecidableAnd (q.denote ctx = 0) _ inferInstance ih) ls
noncomputable instance HypCheckDec.invAtomsOk {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (l : Lean.Grind.CommRing.InvAtoms) : Decidable (Lean.Grind.CommRing.InvAtoms.ok ctx l) :=
  List.rec (motive := fun l => Decidable (Lean.Grind.CommRing.InvAtoms.ok ctx l)) (isTrue trivial)
    (fun yx _ ih => @instDecidableAnd (yx.2.denote ctx * yx.1.denote ctx = 1) _ inferInstance ih) l
noncomputable instance HypCheckDec.invVarsOk {α : Type} [Lean.Grind.Field α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (invs : Lean.Grind.CommRing.InvVars) : Decidable (invs.ok ctx) :=
  (inferInstance : Decidable (invs.denoteVars ctx = invs.denoteInvs))
noncomputable instance HypCheckDec.ppolyDegList (B D : Nat) (ps : List Lean.Grind.CommRing.PPoly) : Decidable (Lean.Grind.CommRing.PPoly.DegList B D ps) :=
  (inferInstance : Decidable (∀ p ∈ ps, p.Deg B D))


/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.CommRing.PPoly.mulMonN_k_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.mulMonN_k_spec.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Nat → α) (nrm : Int → Int) (B D₁ D₂ : Nat),
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B →
          ∀ (k : Int) (d v : Nat),
            @LE.le Nat instLENat (Lean.Grind.CommRing.PPoly.dsum B v) D₁ →
              @LT.lt Nat instLTNat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) D₁ D₂) B →
                ∀ (p : Lean.Grind.CommRing.PPoly),
                  Lean.Grind.CommRing.PPoly.Deg B D₂ p →
                    And
                      (@Eq α
                        (@Lean.Grind.CommRing.PPoly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx B
                          (Lean.Grind.CommRing.PPoly.mulMonN_k nrm k d v p))
                        (@HMul.hMul α α α
                          (@instHMul α
                            (@Lean.Grind.Semiring.toMul α
                              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                          (@HMul.hMul α α α
                            (@instHMul α
                              (@Lean.Grind.Semiring.toMul α
                                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                            (@Lean.Grind.CommRing.PPoly.monDenote α
                              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) ctx B
                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v))
                          (@Lean.Grind.CommRing.PPoly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx B p)))
                      (Lean.Grind.CommRing.PPoly.Deg B (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) D₁ D₂)
                        (Lean.Grind.CommRing.PPoly.mulMonN_k nrm k d v p))) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (fun i => (i : Int) + 2 : Nat → Int) (fun (a : Int) => @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide +kernel) (by
  decide) (.num 0 : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.toPPAcc_k_spec, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toPPAcc_k_spec.h8 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Nat → α) (B : Nat),
        1 < B →
          ∀ (e : Lean.Grind.CommRing.Expr) (D : Nat) (acc : Lean.Grind.CommRing.PPoly),
            D < B →
              Lean.Grind.CommRing.PPoly.Deg B D acc →
                Lean.Grind.CommRing.PPoly.denote ctx B (Lean.Grind.CommRing.Expr.toPPAcc_k B e acc) =
                    Lean.Grind.CommRing.Expr.denoteF ctx e + Lean.Grind.CommRing.PPoly.denote ctx B acc ∧
                  Lean.Grind.CommRing.PPoly.Deg B D (Lean.Grind.CommRing.Expr.toPPAcc_k B e acc) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (fun i => (i : Int) + 2 : Nat → Int) (2) (by
  decide) (.var 0 : Lean.Grind.CommRing.Expr) (0) (.num 0 : Lean.Grind.CommRing.PPoly) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.toPPAcc_k_spec, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toPPAcc_k_spec.h10 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Nat → α) (B : Nat),
        1 < B →
          ∀ (e : Lean.Grind.CommRing.Expr) (D : Nat) (acc : Lean.Grind.CommRing.PPoly),
            e.degB_k ≤ D →
              D < B →
                Lean.Grind.CommRing.PPoly.denote ctx B (Lean.Grind.CommRing.Expr.toPPAcc_k B e acc) =
                    Lean.Grind.CommRing.Expr.denoteF ctx e + Lean.Grind.CommRing.PPoly.denote ctx B acc ∧
                  Lean.Grind.CommRing.PPoly.Deg B D (Lean.Grind.CommRing.Expr.toPPAcc_k B e acc) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (fun i => (i : Int) + 2 : Nat → Int) (2) (by
  decide) (.num 0 : Lean.Grind.CommRing.Expr) (0) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.toPPQ_spec, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toPPQ_spec.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (f : Nat → α) (K B : Nat),
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B →
          ∀ (invs : Lean.Grind.CommRing.InvVars) (e : Lean.Grind.CommRing.Expr),
            @LT.lt Nat instLTNat (Lean.Grind.CommRing.Expr.degQB_k invs e) B →
              And
                (@Eq α
                  (@Lean.Grind.CommRing.PPoly.denote α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))
                    f B (@Prod.fst Lean.Grind.CommRing.PPoly Nat (Lean.Grind.CommRing.Expr.toPPQ B invs e)))
                  (@HMul.hMul α α α
                    (@instHMul α
                      (@Lean.Grind.Semiring.toMul α
                        (@Lean.Grind.CommSemiring.toSemiring α
                          (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                    (@Nat.cast α
                      (@Lean.Grind.Semiring.natCast α
                        (@Lean.Grind.CommSemiring.toSemiring α
                          (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                      (@Prod.snd Lean.Grind.CommRing.PPoly Nat (Lean.Grind.CommRing.Expr.toPPQ B invs e)))
                    (@Lean.Grind.CommRing.Expr.denoteF α
                      (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) f e)))
                (And
                  (Lean.Grind.CommRing.PPoly.Deg B (Lean.Grind.CommRing.Expr.degQB_k invs e)
                    (@Prod.fst Lean.Grind.CommRing.PPoly Nat (Lean.Grind.CommRing.Expr.toPPQ B invs e)))
                  (And
                    (@Ne Nat (@Prod.snd Lean.Grind.CommRing.PPoly Nat (Lean.Grind.CommRing.Expr.toPPQ B invs e))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (And
                      (@Eq Int
                        (Lean.Grind.CommRing.PPoly.kron
                          (@HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow))
                            (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) K)
                          (@Prod.fst Lean.Grind.CommRing.PPoly Nat (Lean.Grind.CommRing.Expr.toPPQ B invs e)))
                        (@Prod.fst Int Nat (Lean.Grind.CommRing.Expr.kronQ_k K B invs e)))
                      (And
                        (@Eq Nat (@Prod.snd Lean.Grind.CommRing.PPoly Nat (Lean.Grind.CommRing.Expr.toPPQ B invs e))
                          (@Prod.snd Int Nat (Lean.Grind.CommRing.Expr.kronQ_k K B invs e)))
                        (And
                          (@LE.le Nat instLENat
                            (@Prod.fst Lean.Grind.CommRing.PPoly Nat (Lean.Grind.CommRing.Expr.toPPQ B invs e)).norm1
                            (@Prod.fst Nat Nat (Lean.Grind.CommRing.Expr.majQ_k invs e)))
                          (@Eq Nat (@Prod.snd Lean.Grind.CommRing.PPoly Nat (Lean.Grind.CommRing.Expr.toPPQ B invs e))
                            (@Prod.snd Nat Nat (Lean.Grind.CommRing.Expr.majQ_k invs e))))))))) := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (fun i => (i : Rat) + 2 : Nat → Rat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide) (@List.cons (Prod Lean.Grind.CommRing.Var Nat)
      (@Prod.mk Lean.Grind.CommRing.Var Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) (.var 0 : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.Deg.mulTL, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.mulTL.h6 : ¬∀ {B D₁ D₂ : Nat},
        1 < B →
          ∀ {p q : Lean.Grind.CommRing.PPoly},
            Lean.Grind.CommRing.PPoly.Deg B D₂ q → D₁ + D₂ < B → Lean.Grind.CommRing.PPoly.Deg B (D₁ + D₂) (p.mulTL q) := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) (.num 0 : Lean.Grind.CommRing.PPoly) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.Deg.mulTL, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.mulTL.h7 : ¬∀ {B D₁ D₂ : Nat},
        1 < B →
          ∀ {p q : Lean.Grind.CommRing.PPoly},
            Lean.Grind.CommRing.PPoly.Deg B D₁ p → D₁ + D₂ < B → Lean.Grind.CommRing.PPoly.Deg B (D₁ + D₂) (p.mulTL q) := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (.num 0 : Lean.Grind.CommRing.PPoly) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.toTL_spec, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toTL_spec.h7 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (X : Int) {B : Nat},
        1 < B →
          ∀ (e : Lean.Grind.CommRing.Expr),
            e.degB_k < B →
              (Lean.Grind.CommRing.Expr.toTL B e).NonNeg ∧
                Lean.Grind.CommRing.PPoly.Deg B e.degB_k (Lean.Grind.CommRing.Expr.toTL B e) ∧
                  Lean.Grind.CommRing.PPoly.denoteSN (Lean.Grind.CommRing.Var.denote ctx) B
                        (Lean.Grind.CommRing.Expr.toTL B e) =
                      Lean.Grind.CommRing.Expr.denoteS ctx e ∧
                    Lean.Grind.CommRing.PPoly.kron X (Lean.Grind.CommRing.Expr.toTL B e) =
                        Lean.Grind.CommRing.Expr.denoteF (fun (i : Nat) => X ^ B ^ i) e ∧
                      (Lean.Grind.CommRing.Expr.toTL B e).norm1 ≤ e.majorant_k := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (0) (2) (by
  decide) (.neg (.var 0) : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.toTL_spec, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toTL_spec.h8 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (X : Int) {B : Nat},
        1 < B →
          ∀ (e : Lean.Grind.CommRing.Expr),
            e.semi_k = Bool.true →
              (Lean.Grind.CommRing.Expr.toTL B e).NonNeg ∧
                Lean.Grind.CommRing.PPoly.Deg B e.degB_k (Lean.Grind.CommRing.Expr.toTL B e) ∧
                  Lean.Grind.CommRing.PPoly.denoteSN (Lean.Grind.CommRing.Var.denote ctx) B
                        (Lean.Grind.CommRing.Expr.toTL B e) =
                      Lean.Grind.CommRing.Expr.denoteS ctx e ∧
                    Lean.Grind.CommRing.PPoly.kron X (Lean.Grind.CommRing.Expr.toTL B e) =
                        Lean.Grind.CommRing.Expr.denoteF (fun (i : Nat) => X ^ B ^ i) e ∧
                      (Lean.Grind.CommRing.Expr.toTL B e).norm1 ≤ e.majorant_k := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.branch 1 (.leaf 1) (.leaf 2) : Lean.RArray Int) (0) (2) (by
  decide) (.mul (.var 0) (.var 0) : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.Deg.powTL, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.powTL.h4 : ¬∀ {B D : Nat},
        1 < B → ∀ {p : Lean.Grind.CommRing.PPoly} (k : Nat), D * k < B → Lean.Grind.CommRing.PPoly.Deg B (D * k) (p.powTL k) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) (1) (by
  decide)) (by
  decide +kernel)

