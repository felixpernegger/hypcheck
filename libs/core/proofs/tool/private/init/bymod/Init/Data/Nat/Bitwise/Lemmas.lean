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
-- _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.trailingZerosBits_rec_irrel, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.trailingZerosBits_rec_irrel.h3 : ¬∀ {n k k' : Nat},
        n ≤ k' →
          Nat.rec (motive := fun (x : Nat) => Nat → Nat) (fun (x : Nat) => 0)
              (fun (x : Nat) (ih : Nat → Nat) (n : Nat) =>
                Bool.rec 0 (Bool.rec 0 (ih (n / 2)).succ ((n % 2).beq 0)) (Nat.ble 2 n))
              k n =
            Nat.rec (motive := fun (x : Nat) => Nat → Nat) (fun (x : Nat) => 0)
              (fun (x : Nat) (ih : Nat → Nat) (n : Nat) =>
                Bool.rec 0 (Bool.rec 0 (ih (n / 2)).succ ((n % 2).beq 0)) (Nat.ble 2 n))
              k' n := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.trailingZerosBits_rec_irrel, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.trailingZerosBits_rec_irrel.h4 : ¬∀ {n k k' : Nat},
        n ≤ k →
          Nat.rec (motive := fun (x : Nat) => Nat → Nat) (fun (x : Nat) => 0)
              (fun (x : Nat) (ih : Nat → Nat) (n : Nat) =>
                Bool.rec 0 (Bool.rec 0 (ih (n / 2)).succ ((n % 2).beq 0)) (Nat.ble 2 n))
              k n =
            Nat.rec (motive := fun (x : Nat) => Nat → Nat) (fun (x : Nat) => 0)
              (fun (x : Nat) (ih : Nat → Nat) (n : Nat) =>
                Bool.rec 0 (Bool.rec 0 (ih (n / 2)).succ ((n % 2).beq 0)) (Nat.ble 2 n))
              k' n := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.div_two_le_of_lt_two, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.div_two_le_of_lt_two.h2 : ¬∀ {m n : Nat}, m / 2 < 2 ^ n := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.trailingZerosBits_two_pow_mul, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.trailingZerosBits_two_pow_mul.h1 : ¬∀ {n : Nat} (k : Nat), Nat.trailingZerosBits (2 ^ k * n) = Nat.trailingZerosBits n + k := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.trailingZerosBits_mod_two_pow, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.trailingZerosBits_mod_two_pow.h2 : ¬∀ {n k : Nat}, Nat.trailingZerosBits (n % 2 ^ k) = Nat.trailingZerosBits n := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.trailingZerosBits_two_mul, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.trailingZerosBits_two_mul.h1 : ¬∀ {n : Nat}, Nat.trailingZerosBits (2 * n) = Nat.trailingZerosBits n + 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.trailingZerosBits_eq_zero_of_mod_eq, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.trailingZerosBits_eq_zero_of_mod_eq.h1 : ¬∀ {n : Nat}, Nat.trailingZerosBits n = 0 := fun hc_h => absurd (@hc_h (2)) (by
  decide +kernel)

-- _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.trailingZeros_rec_eq_bits, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.trailingZeros_rec_eq_bits.h2 : ¬∀ {n fuel : Nat},
        Nat.rec (motive := fun (x : Nat) => Nat → Nat) (fun (x : Nat) => 0)
            (fun (x : Nat) (ih : Nat → Nat) (n : Nat) =>
              Bool.rec
                (Bool.rec (Nat.trailingZerosBits (Nat.land 18446744073709551615 n)) ((ih (n >>> 64)).add 64)
                  ((Nat.land 18446744073709551615 n).beq 0))
                0 (n.beq 0))
            fuel n =
          Nat.trailingZerosBits n := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- _private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.two_mul_sub_one, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.two_mul_sub_one.h1 : ¬∀ {n : Nat}, (2 * n - 1) % 2 = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

