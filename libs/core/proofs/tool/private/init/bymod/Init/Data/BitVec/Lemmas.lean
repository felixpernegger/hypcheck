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
-- _private.Init.Data.BitVec.Lemmas.0.BitVec.toNat_signExtend_of_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.toNat_signExtend_of_le.h3 : ¬∀ {w : Nat} (x : BitVec w) {v : Nat},
        (BitVec.signExtend v x).toNat = x.toNat + if x.msb = Bool.true then 2 ^ v - 2 ^ w else 0 := fun hc_h => absurd (@hc_h (1) (1#1) (0)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.clzAuxRec_eq_log2, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.clzAuxRec_eq_log2.h3 : ¬∀ {w n : Nat} {x : BitVec w}, x.clzAuxRec n = BitVec.ofNat w (if x.toNat = 0 then w else w - (x.toNat.log2 + 1)) := fun hc_h => absurd (@hc_h (2) (0) (2#2)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.mul_mod_add_lt, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.mul_mod_add_lt.h4 : ¬∀ {a b s w : Nat}, b < 2 ^ s → a * 2 ^ s % 2 ^ w + b < 2 ^ w := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.mul_mod_add_lt, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.mul_mod_add_lt.h5 : ¬∀ {a b s w : Nat}, s ≤ w → a * 2 ^ s % 2 ^ w + b < 2 ^ w := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt, hypothesis 2: removable
/- FAILED: 6:73: unexpected identifier after decimal point; consider parenthesizing the number | 10:73: unexpected identifier after decimal point; consider parenthesizing the number | 6:73: unexpected identifier after decimal point; consider parenthesizing the number | 10:73: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt.h2.gneg : ∀ {w v : Nat}, ¬w ≤ v → ∀ {x : BitVec w}, w < v → (BitVec.signExtend v x).toInt = x.toInt := by
  (intros; omega)
theorem HypCheckProof.BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt.h2 : ∀ {w v : Nat} {x : BitVec w}, w < v → (BitVec.signExtend v x).toInt = x.toInt := by
  intro hc_x0 hc_x1 hc_x3 hc_x4
  exact Classical.byCases (fun hc_h => @_private.Init.Data.BitVec.Lemmas.0.BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt hc_x0 hc_x1 hc_h hc_x3 hc_x4) (fun hc_hn => @HypCheckProof.BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt.h2.gneg hc_x0 hc_x1 hc_hn hc_x3 hc_x4)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt.h2.derivable : ∀ {w v : Nat} {x : BitVec w}, w < v → w ≤ v := by
  (intros; omega)
-/

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.lt_two_pow_of_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.lt_two_pow_of_le.h3 : ¬∀ {x m n : Nat}, m ≤ n → x < 2 ^ n := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.lt_two_pow_of_le, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.lt_two_pow_of_le.h4 : ¬∀ {x m n : Nat}, x < 2 ^ m → x < 2 ^ n := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.or_eq_add_of_lt_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.or_eq_add_of_lt_of_dvd.h3 : ¬∀ {a b s : Nat}, 2 ^ s ∣ a → a ||| b = a + b := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.or_eq_add_of_lt_of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.or_eq_add_of_lt_of_dvd.h4 : ¬∀ {a b s : Nat}, b < 2 ^ s → a ||| b = a + b := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.Nat.sub_mul_eq_mod_of_lt_of_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.Nat.sub_mul_eq_mod_of_lt_of_le.h3 : ¬∀ {w n i : Nat}, i < w * (n + 1) → i - w * n = i % w := fun hc_h => absurd (@hc_h (2) (1) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.Nat.sub_mul_eq_mod_of_lt_of_le, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.Nat.sub_mul_eq_mod_of_lt_of_le.h4 : ¬∀ {w n i : Nat}, w * n ≤ i → i - w * n = i % w := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.toNat_div_two_pow_lt, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.toNat_div_two_pow_lt.h4 : ¬∀ {w : Nat} (x : BitVec w) {s t : Nat}, x.toNat / 2 ^ s < 2 ^ t := fun hc_h => absurd (@hc_h (1) (1#1) (0) (0)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.Int.ofNat_sub_ofNat_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.Int.ofNat_sub_ofNat_of_lt.h2 : Not
      (∀ {n m : Nat},
        @Eq Int
          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt n)
            (@Nat.cast Int instNatCastInt m))
          (@Neg.neg Int Int.instNegInt
            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
              (@Nat.cast Int instNatCastInt
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  n))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Lemmas.0.BitVec.reverse_clz_eq_trailingZeros, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.reverse_clz_eq_trailingZeros.h2 : ¬∀ {w : Nat} {x : BitVec w}, x.reverse.clz.toNat = x.toNat.trailingZeros := fun hc_h => absurd (@hc_h (1) (0#1)) (by
  decide +kernel)

