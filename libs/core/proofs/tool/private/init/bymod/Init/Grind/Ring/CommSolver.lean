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
-- _private.Init.Grind.Ring.CommSolver.0.Lean.Grind.CommRing.of_mod_eq_0, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.CommRing.of_mod_eq_0.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] {a : Int} {c : Nat},
        @Eq Int (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) a (@Nat.cast Int instNatCastInt c))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) a)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ring.CommSolver.0.Lean.Grind.CommRing.of_mod_eq_0, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.CommRing.of_mod_eq_0.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] {a : Int} {c : Nat},
        @Eq α
            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) (@Nat.cast Int instNatCastInt c))
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
          @Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) a)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ring.CommSolver.0.Lean.Grind.CommRing.le_of_blt_false, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_blt_false.h2 : ¬∀ {a b : Nat}, b ≤ a := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- _private.Init.Grind.Ring.CommSolver.0.Lean.Grind.CommRing.eq_of_blt_false, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_blt_false.h2 : ¬∀ {a b : Nat}, b.blt a = Bool.false → a = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ring.CommSolver.0.Lean.Grind.CommRing.eq_of_blt_false, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_blt_false.h3 : ¬∀ {a b : Nat}, a.blt b = Bool.false → a = b := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

