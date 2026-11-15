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
-- _private.Init.Data.Range.Polymorphic.SInt.0.HasModel.toNat_toInt_add_one_sub_toInt, hypothesis 3: removable
/- FAILED: 3:70: expected token | 10:102: expected token | 3:70: expected token | 10:102: expected token
set_option maxHeartbeats 1000 in
theorem HypCheckProof.HasModel.toNat_toInt_add_one_sub_toInt.h3.gneg : ∀ {n : Nat} {lo hi : BitVec n},
      ¬n > 0 → (hi.toInt + 1 - lo.toInt).toNat = (BitVec.Signed.rotate✝ hi).toNat + 1 - (BitVec.Signed.rotate✝ lo).toNat := by
  (intros; grind)
theorem HypCheckProof.HasModel.toNat_toInt_add_one_sub_toInt.h3 : ∀ {n : Nat} {lo hi : BitVec n},
      (hi.toInt + 1 - lo.toInt).toNat = (BitVec.Signed.rotate✝ hi).toNat + 1 - (BitVec.Signed.rotate✝ lo).toNat := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @HasModel.toNat_toInt_add_one_sub_toInt hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.HasModel.toNat_toInt_add_one_sub_toInt.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)
-/

-- _private.Init.Data.Range.Polymorphic.SInt.0.HasModel.toNat_two_pow_sub_one_sub_toInt, hypothesis 2: removable
/- FAILED: 2:173: expected token | 14:51: expected token | 2:173: expected token | 14:51: expected token
set_option maxHeartbeats 1000 in
theorem HypCheckProof.HasModel.toNat_two_pow_sub_one_sub_toInt.h2.gneg : ∀ {n : Nat} {lo : BitVec n}, ¬n > 0 → (2 ^ (n - 1) - lo.toInt).toNat = 2 ^ n - (BitVec.Signed.rotate✝ lo).toNat := by
  (intros; grind)
theorem HypCheckProof.HasModel.toNat_two_pow_sub_one_sub_toInt.h2 : ∀ {n : Nat} {lo : BitVec n}, (2 ^ (n - 1) - lo.toInt).toNat = 2 ^ n - (BitVec.Signed.rotate✝ lo).toNat := by
  intro hc_x0 hc_x1
  exact Classical.byCases (fun hc_h => @HasModel.toNat_two_pow_sub_one_sub_toInt hc_x0 hc_x1 hc_h) (fun hc_hn => @HypCheckProof.HasModel.toNat_two_pow_sub_one_sub_toInt.h2.gneg hc_x0 hc_x1 hc_hn)
-/

