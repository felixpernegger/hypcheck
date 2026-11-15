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
-- _private.Init.Data.Nat.ToString.0.Nat.toDigitsCore_eq_of_lt_fuel, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.toDigitsCore_eq_of_lt_fuel.h5 : ¬∀ {b n fuel₁ fuel₂ : Nat} {cs : List Char},
        n < fuel₁ → n < fuel₂ → b.toDigitsCore fuel₁ n cs = b.toDigitsCore fuel₂ n cs := fun hc_h => absurd (@hc_h (1) (1) (2) (3) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.ToString.0.Nat.toDigitsCore_eq_of_lt_fuel, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.toDigitsCore_eq_of_lt_fuel.h6 : ¬∀ {b n fuel₁ fuel₂ : Nat} {cs : List Char}, 1 < b → n < fuel₂ → b.toDigitsCore fuel₁ n cs = b.toDigitsCore fuel₂ n cs := fun hc_h => absurd (@hc_h (2) (0) (0) (1) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.ToString.0.Nat.toDigitsCore_eq_of_lt_fuel, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.toDigitsCore_eq_of_lt_fuel.h7 : ¬∀ {b n fuel₁ fuel₂ : Nat} {cs : List Char}, 1 < b → n < fuel₁ → b.toDigitsCore fuel₁ n cs = b.toDigitsCore fuel₂ n cs := fun hc_h => absurd (@hc_h (2) (0) (1) (0) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.ToString.0.Nat.toDigitsCore_toDigitsCore, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.toDigitsCore_toDigitsCore.h8 : ¬∀ {b n d fuel nf df : Nat} {cs : List Char},
        1 < b →
          d < b →
            b * n + d < fuel →
              n < nf → d < df → b.toDigitsCore nf n (b.toDigitsCore df d cs) = b.toDigitsCore fuel (b * n + d) cs := fun hc_h => absurd (@hc_h (2) (0) (0) (1) (1) (1) ([]) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.ToString.0.Nat.isDigit_of_mem_toDigitsCore, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.isDigit_of_mem_toDigitsCore.h5 : ¬∀ {b : Nat} {cs : List Char} {c : Char} {fuel n : Nat},
        0 < b → b ≤ 10 → c ∈ b.toDigitsCore fuel n cs → c.isDigit = Bool.true := fun hc_h => absurd (@hc_h (1) (['a']) ('a') (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.ToString.0.Nat.isDigit_of_mem_toDigitsCore, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.isDigit_of_mem_toDigitsCore.h6 : ¬∀ {b : Nat} {cs : List Char} {c : Char} {fuel n : Nat},
        (c ∈ cs → c.isDigit = Bool.true) → b ≤ 10 → c ∈ b.toDigitsCore fuel n cs → c.isDigit = Bool.true := fun hc_h => absurd (@hc_h (0) ([]) ('a') (1) (10) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.ToString.0.Nat.isDigit_of_mem_toDigitsCore, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.isDigit_of_mem_toDigitsCore.h7 : ¬∀ {b : Nat} {cs : List Char} {c : Char} {fuel n : Nat},
        (c ∈ cs → c.isDigit = Bool.true) → 0 < b → c ∈ b.toDigitsCore fuel n cs → c.isDigit = Bool.true := fun hc_h => absurd (@hc_h (11) ([]) ('a') (1) (10) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.ToString.0.Nat.isDigit_of_mem_toDigitsCore, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.isDigit_of_mem_toDigitsCore.h8 : ¬∀ {b : Nat} {cs : List Char} {c : Char} {fuel n : Nat},
        (c ∈ cs → c.isDigit = Bool.true) → 0 < b → b ≤ 10 → c.isDigit = Bool.true := fun hc_h => absurd (@hc_h (1) ([]) ('a') (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.ToString.0.Nat.toDigitsCore_of_lt_base, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.toDigitsCore_of_lt_base.h4 : ¬∀ {b n fuel : Nat} {cs : List Char}, n < fuel → b.toDigitsCore fuel n cs = n.digitChar :: cs := fun hc_h => absurd (@hc_h (1) (1) (2) ([]) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Nat.ToString.0.Nat.toDigitsCore_of_lt_base, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.toDigitsCore_of_lt_base.h5 : ¬∀ {b n fuel : Nat} {cs : List Char}, n < b → b.toDigitsCore fuel n cs = n.digitChar :: cs := fun hc_h => absurd (@hc_h (1) (0) (0) ([]) (by
  decide)) (by
  decide +kernel)

