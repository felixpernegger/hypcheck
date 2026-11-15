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
-- _private.Init.Grind.Ordered.Field.0.Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] [inst_5 : Lean.Grind.OrderedRing R] {a b c : R}, a * b⁻¹ < c → c * b < a := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (0) (0) (1) (by
  decide +kernel)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Field.0.Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] [inst_5 : Lean.Grind.OrderedRing R] {a b c : R}, a ≤ b * c → b ≤ a * c⁻¹ := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (0) (1) (0) (by
  decide +kernel)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Field.0.Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] [inst_5 : Lean.Grind.OrderedRing R] {a b c : R}, a * b ≤ c → a ≤ c * b⁻¹ := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (1) (0) (0) (by
  decide +kernel)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Field.0.Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] [inst_5 : Lean.Grind.OrderedRing R] {a b c : R}, a * b < c → a < c * b⁻¹ := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (0) (0) (1) (by
  decide +kernel)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Field.0.Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt, hypothesis 11: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt.h11 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] [inst_5 : Lean.Grind.OrderedRing R] {a b c : R}, 0 < b → a < c * b⁻¹ := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Field.0.Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] [inst_5 : Lean.Grind.OrderedRing R] {a b c : R}, a ≤ b * c⁻¹ → b ≤ a * c := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (0) (1) (0) (by
  decide +kernel)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Field.0.Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] [inst_5 : Lean.Grind.OrderedRing R] {a b c : R}, a * b < c → c * b⁻¹ < a := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (0) (0) (1) (by
  decide +kernel)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Field.0.Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv, hypothesis 11: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv.h11 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] [inst_5 : Lean.Grind.OrderedRing R] {a b c : R}, 0 < c → a * c < b := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Field.0.Lean.Grind.Field.IsOrdered.mul_inv_le_iff_le_mul, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_le_iff_le_mul.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] [inst_5 : Lean.Grind.OrderedRing R] (a c : R) {b : R}, a * b⁻¹ ≤ c ↔ a ≤ c * b := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (1) (0) (0)) (by
  decide +kernel)

