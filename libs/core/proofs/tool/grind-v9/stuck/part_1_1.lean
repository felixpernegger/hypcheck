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

-- Lean.Grind.CommRing.PPoly.mulMon_k_spec, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.mulMon_k_spec.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Nat → α) (B D₁ D₂ : Nat),
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B →
          ∀ (k : Int) (d v : Nat),
            @LT.lt Nat instLTNat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) D₁ D₂) B →
              ∀ (p : Lean.Grind.CommRing.PPoly),
                Lean.Grind.CommRing.PPoly.Deg B D₂ p →
                  And
                    (@Eq α
                      (@Lean.Grind.CommRing.PPoly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx B
                        (Lean.Grind.CommRing.PPoly.mulMon_k k d v p))
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
                      (Lean.Grind.CommRing.PPoly.mulMon_k k d v p))) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (fun i => (i : Int) + 2 : Nat → Int) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide) (.num 1 : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_mul_of_terms, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_mul_of_terms.h9 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx b = Lean.Grind.CommRing.Poly.denoteS ctx pb ∧ pb.NonnegCoeffs →
          ts = pa.mulTerms_k pb →
            p = Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k ts →
              Lean.Grind.CommRing.Expr.denoteS ctx (a.mul b) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.var 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) _ (.num 0 : Lean.Grind.CommRing.Poly) (by
  decide) rfl (by
  rfl)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_mul_of_terms, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_mul_of_terms.h10 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Poly.denoteS ctx pa ∧ pa.NonnegCoeffs →
          ts = pa.mulTerms_k pb →
            p = Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k ts →
              Lean.Grind.CommRing.Expr.denoteS ctx (a.mul b) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.var 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) _ (.num 0 : Lean.Grind.CommRing.Poly) (by
  decide) rfl (by
  rfl)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_mul_of_terms, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_mul_of_terms.h11 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Poly.denoteS ctx pa ∧ pa.NonnegCoeffs →
          Lean.Grind.CommRing.Expr.denoteS ctx b = Lean.Grind.CommRing.Poly.denoteS ctx pb ∧ pb.NonnegCoeffs →
            p = Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k ts →
              Lean.Grind.CommRing.Expr.denoteS ctx (a.mul b) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) ([Lean.Grind.CommRing.Poly.add 1
        (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num 0)]) _ (by
  decide) (by
  decide) rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_mul_of_terms, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_mul_of_terms.h12 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Poly.denoteS ctx pa ∧ pa.NonnegCoeffs →
          Lean.Grind.CommRing.Expr.denoteS ctx b = Lean.Grind.CommRing.Poly.denoteS ctx pb ∧ pb.NonnegCoeffs →
            ts = pa.mulTerms_k pb →
              Lean.Grind.CommRing.Expr.denoteS ctx (a.mul b) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) _ (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  decide) (by
  decide) rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_pow_succ_of_terms, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_pow_succ_of_terms.h9 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (k : Nat) (pa q : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx (a.pow k) = Lean.Grind.CommRing.Poly.denoteS ctx q ∧ q.NonnegCoeffs →
          ts = pa.mulTerms_k q →
            p = Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k ts →
              Lean.Grind.CommRing.Expr.denoteS ctx (a.pow (k + 1)) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.var 0 : Lean.Grind.CommRing.Expr) (0) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) _ (.num 0 : Lean.Grind.CommRing.Poly) (by
  decide) rfl (by
  rfl)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_pow_succ_of_terms, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_pow_succ_of_terms.h10 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (k : Nat) (pa q : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Poly.denoteS ctx pa ∧ pa.NonnegCoeffs →
          ts = pa.mulTerms_k q →
            p = Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k ts →
              Lean.Grind.CommRing.Expr.denoteS ctx (a.pow (k + 1)) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.var 0 : Lean.Grind.CommRing.Expr) (0) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) _ (.num 0 : Lean.Grind.CommRing.Poly) (by
  decide) rfl (by
  rfl)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_pow_succ_of_terms, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_pow_succ_of_terms.h11 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (k : Nat) (pa q : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Poly.denoteS ctx pa ∧ pa.NonnegCoeffs →
          Lean.Grind.CommRing.Expr.denoteS ctx (a.pow k) = Lean.Grind.CommRing.Poly.denoteS ctx q ∧ q.NonnegCoeffs →
            p = Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k ts →
              Lean.Grind.CommRing.Expr.denoteS ctx (a.pow (k + 1)) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (0) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) ([Lean.Grind.CommRing.Poly.add 1
        (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num 0)]) _ (by
  decide) (by
  decide) rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_pow_succ_of_terms, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_pow_succ_of_terms.h12 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (k : Nat) (pa q : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Poly.denoteS ctx pa ∧ pa.NonnegCoeffs →
          Lean.Grind.CommRing.Expr.denoteS ctx (a.pow k) = Lean.Grind.CommRing.Poly.denoteS ctx q ∧ q.NonnegCoeffs →
            ts = pa.mulTerms_k q →
              Lean.Grind.CommRing.Expr.denoteS ctx (a.pow (k + 1)) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (0) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) _ (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  decide) (by
  decide) rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.sumsPP_k_spec, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sumsPP_k_spec.h9 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Nat → α) (B : Nat),
        1 < B →
          ∀ (e : Lean.Grind.CommRing.Expr) (D : Nat) (s : Bool) (acc : List Lean.Grind.CommRing.PPoly),
            D < B →
              Lean.Grind.CommRing.PPoly.DegList B D acc →
                Lean.Grind.CommRing.PPoly.denoteList ctx B (Lean.Grind.CommRing.Expr.sumsPP_k B e s acc) =
                    Bool.rec (Lean.Grind.CommRing.Expr.denoteF ctx e) (-Lean.Grind.CommRing.Expr.denoteF ctx e) s +
                      Lean.Grind.CommRing.PPoly.denoteList ctx B acc ∧
                  Lean.Grind.CommRing.PPoly.DegList B D (Lean.Grind.CommRing.Expr.sumsPP_k B e s acc) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (fun i => (i : Int) + 2 : Nat → Int) (2) (by
  decide) (.var 0 : Lean.Grind.CommRing.Expr) (0) (Bool.false) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.Deg.mulTermTL, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.mulTermTL.h8 : ¬∀ {B D₁ D₂ : Nat},
        1 < B →
          ∀ {q : Lean.Grind.CommRing.PPoly} (k : Int) (d v : Nat),
            Lean.Grind.CommRing.PPoly.Deg B D₂ q →
              D₁ + D₂ < B → Lean.Grind.CommRing.PPoly.Deg B (D₁ + D₂) (Lean.Grind.CommRing.PPoly.mulTermTL k d v q) := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (.num 0 : Lean.Grind.CommRing.PPoly) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_add_of, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_add_of.h8 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx b = Lean.Grind.CommRing.Poly.denoteS ctx pb ∧ pb.NonnegCoeffs →
          p = pa.combine_k pb →
            Lean.Grind.CommRing.Expr.denoteS ctx (a.add b) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) _ (by
  decide) rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_add_of, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_add_of.h9 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Poly.denoteS ctx pa ∧ pa.NonnegCoeffs →
          p = pa.combine_k pb →
            Lean.Grind.CommRing.Expr.denoteS ctx (a.add b) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) _ (by
  decide) rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_add_of, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_add_of.h10 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Poly.denoteS ctx pa ∧ pa.NonnegCoeffs →
          Lean.Grind.CommRing.Expr.denoteS ctx b = Lean.Grind.CommRing.Poly.denoteS ctx pb ∧ pb.NonnegCoeffs →
            Lean.Grind.CommRing.Expr.denoteS ctx (a.add b) = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.powPP_k_spec, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.powPP_k_spec.h8 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Nat → α) (B : Nat),
        1 < B →
          ∀ (a : Lean.Grind.CommRing.Expr) (k : Nat) (p : Lean.Grind.CommRing.PPoly),
            a.degB_k * k < B →
              Lean.Grind.CommRing.PPoly.denote ctx B (Lean.Grind.CommRing.Expr.powPP_k B a k p) =
                  Lean.Grind.CommRing.Expr.denoteF ctx a ^ k ∧
                Lean.Grind.CommRing.PPoly.Deg B (a.degB_k * k) (Lean.Grind.CommRing.Expr.powPP_k B a k p) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (fun i => (i : Int) + 2 : Nat → Int) (2) (by
  decide) (.add (.var 0) (.var 1) : Lean.Grind.CommRing.Expr) (1) (.num 0 : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PSumTree.leaf_zero, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PSumTree.leaf_zero.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat)
        (p : Lean.Grind.CommRing.Poly) (P : Lean.Grind.CommRing.PPoly),
        P = Lean.Grind.CommRing.Poly.toPP_k B p →
          Lean.Grind.CommRing.Poly.denote ctx p = 0 →
            Lean.Grind.CommRing.PPoly.denote (Lean.Grind.CommRing.Var.denote ctx) B P = 0 ∧
              Lean.Grind.CommRing.PPoly.Deg B p.maxDeg_k P := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 0 : Lean.RArray Int) (0) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) _ rfl (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PSumTree.leaf_zero, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PSumTree.leaf_zero.h8 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat)
        (p : Lean.Grind.CommRing.Poly) (P : Lean.Grind.CommRing.PPoly),
        Bool.rec Bool.false (p.maxDeg_k.blt B) (Nat.blt 1 B) = Bool.true →
          P = Lean.Grind.CommRing.Poly.toPP_k B p →
            Lean.Grind.CommRing.PPoly.denote (Lean.Grind.CommRing.Var.denote ctx) B P = 0 ∧
              Lean.Grind.CommRing.PPoly.Deg B p.maxDeg_k P := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (2) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) _ (by
  decide) rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.powLeafSB_k_nonneg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.powLeafSB_k_nonneg.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (k : Nat) {p : Lean.Grind.CommRing.Poly},
        Lean.Grind.CommRing.Poly.denoteS ctx p = Lean.Grind.CommRing.Expr.denoteS ctx a →
          (a.powLeafSB_k k p).NonnegCoeffs ∧
            Lean.Grind.CommRing.Poly.denoteS ctx (a.powLeafSB_k k p) = Lean.Grind.CommRing.Expr.denoteS ctx a ^ k := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 0 : Lean.RArray Int) (.add (.var 0) (.var 1) : Lean.Grind.CommRing.Expr) (1) (.num (-1) : Lean.Grind.CommRing.Poly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.powLeafSB_k_nonneg, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.powLeafSB_k_nonneg.h7 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (k : Nat) {p : Lean.Grind.CommRing.Poly},
        p.NonnegCoeffs →
          (a.powLeafSB_k k p).NonnegCoeffs ∧
            Lean.Grind.CommRing.Poly.denoteS ctx (a.powLeafSB_k k p) = Lean.Grind.CommRing.Expr.denoteS ctx a ^ k := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.add (.var 0) (.var 1) : Lean.Grind.CommRing.Expr) (1) (.num 0 : Lean.Grind.CommRing.Poly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.mulTerms_k_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.mulTerms_k_nonneg.h5 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ : Lean.Grind.CommRing.Poly),
        p₂.NonnegCoeffs →
          Lean.Grind.CommRing.Poly.NonnegList (p₁.mulTerms_k p₂) ∧
            Lean.Grind.CommRing.Poly.denoteSList ctx (p₁.mulTerms_k p₂) =
              Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num (-1) : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.mulTerms_k_nonneg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.mulTerms_k_nonneg.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ : Lean.Grind.CommRing.Poly),
        p₁.NonnegCoeffs →
          Lean.Grind.CommRing.Poly.NonnegList (p₁.mulTerms_k p₂) ∧
            Lean.Grind.CommRing.Poly.denoteSList ctx (p₁.mulTerms_k p₂) =
              Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.combine_k_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.combine_k_nonneg.h5 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) {a b : Lean.Grind.CommRing.Poly},
        b.NonnegCoeffs →
          (a.combine_k b).NonnegCoeffs ∧
            Lean.Grind.CommRing.Poly.denoteS ctx (a.combine_k b) =
              Lean.Grind.CommRing.Poly.denoteS ctx a + Lean.Grind.CommRing.Poly.denoteS ctx b := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num (-1) : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.combine_k_nonneg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.combine_k_nonneg.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) {a b : Lean.Grind.CommRing.Poly},
        a.NonnegCoeffs →
          (a.combine_k b).NonnegCoeffs ∧
            Lean.Grind.CommRing.Poly.denoteS ctx (a.combine_k b) =
              Lean.Grind.CommRing.Poly.denoteS ctx a + Lean.Grind.CommRing.Poly.denoteS ctx b := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.mulB_k_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.mulB_k_nonneg.h5 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        {p₁ p₂ : Lean.Grind.CommRing.Poly},
        p₂.NonnegCoeffs →
          (p₁.mulB_k p₂).NonnegCoeffs ∧
            Lean.Grind.CommRing.Poly.denoteS ctx (p₁.mulB_k p₂) =
              Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num (-1) : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.mulB_k_nonneg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.mulB_k_nonneg.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        {p₁ p₂ : Lean.Grind.CommRing.Poly},
        p₁.NonnegCoeffs →
          (p₁.mulB_k p₂).NonnegCoeffs ∧
            Lean.Grind.CommRing.Poly.denoteS ctx (p₁.mulB_k p₂) =
              Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.toPP_k_spec, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.toPP_k_spec.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) {B : Nat},
        1 < B →
          ∀ (p : Lean.Grind.CommRing.Poly),
            Lean.Grind.CommRing.PPoly.denote (Lean.Grind.CommRing.Var.denote ctx) B (Lean.Grind.CommRing.Poly.toPP_k B p) =
                Lean.Grind.CommRing.Poly.denote ctx p ∧
              Lean.Grind.CommRing.PPoly.Deg B p.maxDeg_k (Lean.Grind.CommRing.Poly.toPP_k B p) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.branch 1 (.leaf 1) (.leaf 2) : Lean.RArray Int) (2) (by
  decide) (.add 1 (.mult ⟨0, 2⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.DegList.cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.DegList.cons.h4 : ¬∀ {B D : Nat} {p : Lean.Grind.CommRing.PPoly} {ps : List Lean.Grind.CommRing.PPoly},
        Lean.Grind.CommRing.PPoly.DegList B D ps → Lean.Grind.CommRing.PPoly.DegList B D (p :: ps) := fun hc_h => absurd (@hc_h (2) (0) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) ([]) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.mulTermTL, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.mulTermTL.h4 : ¬∀ {q : Lean.Grind.CommRing.PPoly} {k : Int} {d v : Nat}, 0 ≤ k → (Lean.Grind.CommRing.PPoly.mulTermTL k d v q).NonNeg := fun hc_h => absurd (@hc_h (.num (-1) : Lean.Grind.CommRing.PPoly) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.mulTermTL, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.mulTermTL.h5 : ¬∀ {q : Lean.Grind.CommRing.PPoly} {k : Int} {d v : Nat},
        q.NonNeg → (Lean.Grind.CommRing.PPoly.mulTermTL k d v q).NonNeg := fun hc_h => absurd (@hc_h (.num 1 : Lean.Grind.CommRing.PPoly) (-1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.Deg.append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.append.h4 : ¬∀ {B D : Nat} {p q : Lean.Grind.CommRing.PPoly},
        Lean.Grind.CommRing.PPoly.Deg B D q → Lean.Grind.CommRing.PPoly.Deg B D (p.append q) := fun hc_h => absurd (@hc_h (2) (0) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) (.num 0 : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.Deg.append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.append.h5 : ¬∀ {B D : Nat} {p q : Lean.Grind.CommRing.PPoly},
        Lean.Grind.CommRing.PPoly.Deg B D p → Lean.Grind.CommRing.PPoly.Deg B D (p.append q) := fun hc_h => absurd (@hc_h (2) (0) (.num 0 : Lean.Grind.CommRing.PPoly) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.combineN_k_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.combineN_k_spec.h4 : ¬∀ {α : Type} [inst : Lean.Grind.Ring α] (ctx : Nat → α) (nrm : Int → Int) (B D : Nat)
        (p₁ p₂ : Lean.Grind.CommRing.PPoly),
        Lean.Grind.CommRing.PPoly.denote ctx B (Lean.Grind.CommRing.PPoly.combineN_k nrm p₁ p₂) =
            Lean.Grind.CommRing.PPoly.denote ctx B p₁ + Lean.Grind.CommRing.PPoly.denote ctx B p₂ ∧
          (Lean.Grind.CommRing.PPoly.Deg B D p₁ →
            Lean.Grind.CommRing.PPoly.Deg B D p₂ →
              Lean.Grind.CommRing.PPoly.Deg B D (Lean.Grind.CommRing.PPoly.combineN_k nrm p₁ p₂)) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (fun i => (i : Int) + 2 : Nat → Int) (fun (a : Int) => 0) (0) (0) (.num 0 : Lean.Grind.CommRing.PPoly) (.num 1 : Lean.Grind.CommRing.PPoly)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.addConstN_k_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.addConstN_k_spec.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] (ctx : Nat → α) (nrm : Int → Int) (B D : Nat) (p : Lean.Grind.CommRing.PPoly)
        (k : Int),
        And
          (@Eq α (@Lean.Grind.CommRing.PPoly.denote α inst ctx B (Lean.Grind.CommRing.PPoly.addConstN_k nrm p k))
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst)))
              (@Lean.Grind.CommRing.PPoly.denote α inst ctx B p) (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k)))
          (Lean.Grind.CommRing.PPoly.Deg B D p →
            Lean.Grind.CommRing.PPoly.Deg B D (Lean.Grind.CommRing.PPoly.addConstN_k nrm p k))) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (fun i => (i : Int) + 2 : Nat → Int) (fun (a : Int) => @OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.PPoly) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_eq_of_toPolySX, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_eq_of_toPolySX.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (e : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx e = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (Bool.false) (.num 0 : Lean.Grind.CommRing.Expr) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.mulTL, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.mulTL.h2 : ¬∀ {p q : Lean.Grind.CommRing.PPoly}, q.NonNeg → (p.mulTL q).NonNeg := fun hc_h => absurd (@hc_h (.num (-1) : Lean.Grind.CommRing.PPoly) (.num 1 : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.mulTL, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.mulTL.h3 : ¬∀ {p q : Lean.Grind.CommRing.PPoly}, p.NonNeg → (p.mulTL q).NonNeg := fun hc_h => absurd (@hc_h (.num 1 : Lean.Grind.CommRing.PPoly) (.num (-1) : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.scale, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.scale.h2 : ¬∀ {p : Lean.Grind.CommRing.PPoly} {k : Int}, 0 ≤ k → (Lean.Grind.CommRing.PPoly.scale k p).NonNeg := fun hc_h => absurd (@hc_h (.num (-1) : Lean.Grind.CommRing.PPoly) (1) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.scale, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.scale.h3 : ¬∀ {p : Lean.Grind.CommRing.PPoly} {k : Int}, p.NonNeg → (Lean.Grind.CommRing.PPoly.scale k p).NonNeg := fun hc_h => absurd (@hc_h (.num 1 : Lean.Grind.CommRing.PPoly) (-1) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.append, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.append.h2 : ¬∀ {p q : Lean.Grind.CommRing.PPoly}, q.NonNeg → (p.append q).NonNeg := fun hc_h => absurd (@hc_h (.num (-1) : Lean.Grind.CommRing.PPoly) (.num 0 : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.append, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.append.h3 : ¬∀ {p q : Lean.Grind.CommRing.PPoly}, p.NonNeg → (p.append q).NonNeg := fun hc_h => absurd (@hc_h (.num 0 : Lean.Grind.CommRing.PPoly) (.num (-1) : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.denoteS_pow_one_of, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_pow_one_of.h5 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (pa : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.Expr.denoteS ctx (a.pow 1) = Lean.Grind.CommRing.Poly.denoteS ctx pa ∧ pa.NonnegCoeffs := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.powB_k_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.powB_k_nonneg.h5 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) {p : Lean.Grind.CommRing.Poly}
        (k : Nat),
        (p.powB_k k).NonnegCoeffs ∧
          Lean.Grind.CommRing.Poly.denoteS ctx (p.powB_k k) = Lean.Grind.CommRing.Poly.denoteS ctx p ^ k := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num (-1) : Lean.Grind.CommRing.Poly) (1)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.addConst, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.addConst.h2 : ¬∀ {q : Lean.Grind.CommRing.PPoly} {k : Int}, 0 ≤ k → (Lean.Grind.CommRing.PPoly.append.addConst q k).NonNeg := fun hc_h => absurd (@hc_h (.num (-1) : Lean.Grind.CommRing.PPoly) (0) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.addConst, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.addConst.h3 : ¬∀ {q : Lean.Grind.CommRing.PPoly} {k : Int}, q.NonNeg → (Lean.Grind.CommRing.PPoly.append.addConst q k).NonNeg := fun hc_h => absurd (@hc_h (.num 0 : Lean.Grind.CommRing.PPoly) (-1) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.Deg.scale, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.scale.h4 : ¬∀ {B D : Nat} {p : Lean.Grind.CommRing.PPoly} (k : Int),
        Lean.Grind.CommRing.PPoly.Deg B D (Lean.Grind.CommRing.PPoly.scale k p) := fun hc_h => absurd (@hc_h (2) (0) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) (0)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.Deg.addConst, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.addConst.h4 : ¬∀ {B D : Nat} {q : Lean.Grind.CommRing.PPoly} (k : Int),
        Lean.Grind.CommRing.PPoly.Deg B D (Lean.Grind.CommRing.PPoly.append.addConst q k) := fun hc_h => absurd (@hc_h (2) (0) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) (0)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.removeCode, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.removeCode.h1 : ¬∀ {p : Lean.Grind.CommRing.PPoly} (c : Nat), (Lean.Grind.CommRing.PPoly.removeCode c p).NonNeg := fun hc_h => absurd (@hc_h (.num (-1) : Lean.Grind.CommRing.PPoly) (1)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.NonNeg.powTL, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.powTL.h1 : ¬∀ {p : Lean.Grind.CommRing.PPoly} (k : Nat), (p.powTL k).NonNeg := fun hc_h => absurd (@hc_h (.num (-1) : Lean.Grind.CommRing.PPoly) (1)) (by
  decide +kernel)

