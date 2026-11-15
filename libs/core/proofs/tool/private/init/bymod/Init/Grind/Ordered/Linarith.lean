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
-- _private.Init.Grind.Ordered.Linarith.0.Lean.Grind.Linarith.lt_add_lt, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_add_lt.h9 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        [inst_4 : Std.IsPreorder α] [inst_5 : Lean.Grind.OrderedAdd α] {a b : α}, b < 0 → a + b < 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Ring.toIntModule) (Int.instLEInt) (Int.instLTInt) _ _ _ (1) (-1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Linarith.0.Lean.Grind.Linarith.lt_add_lt, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_add_lt.h10 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        [inst_4 : Std.IsPreorder α] [inst_5 : Lean.Grind.OrderedAdd α] {a b : α}, a < 0 → a + b < 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Ring.toIntModule) (Int.instLEInt) (Int.instLTInt) _ _ _ (-1) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Linarith.0.Lean.Grind.Linarith.le_add_lt, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Linarith.le_add_lt.h9 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        [inst_4 : Std.IsPreorder α] [inst_5 : Lean.Grind.OrderedAdd α] {a b : α}, b < 0 → a + b < 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Ring.toIntModule) (Int.instLEInt) (Int.instLTInt) _ _ _ (1) (-1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Linarith.0.Lean.Grind.Linarith.le_add_lt, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Linarith.le_add_lt.h10 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        [inst_4 : Std.IsPreorder α] [inst_5 : Lean.Grind.OrderedAdd α] {a b : α}, a ≤ 0 → a + b < 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Ring.toIntModule) (Int.instLEInt) (Int.instLTInt) _ _ _ (0) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Linarith.0.Lean.Grind.Linarith.le_add_le, hypothesis 3: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Lean.Grind.Linarith.le_add_le.h3.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Lean.Grind.Linarith.le_add_le.h3.prem0 : @LT.lt Int Int.instLTInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Lean.Grind.Linarith.le_add_le.h3.prem1 : @LT.lt Int Int.instLTInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.le_add_le.h3 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] {a b : α},
        @LE.le α inst_1 a
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @LE.le α inst_1 b
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @Std.IsPreorder α inst_1) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_add_le.h3.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Linarith.le_add_le.h3.prem0 HypCheckProof.Lean.Grind.Linarith.le_add_le.h3.prem1)

-- _private.Init.Grind.Ordered.Linarith.0.Lean.Grind.Linarith.le_add_le, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Linarith.le_add_le.h7 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : Std.IsPreorder α]
        [inst_3 : Lean.Grind.OrderedAdd α] {a b : α}, b ≤ 0 → a + b ≤ 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Ring.toIntModule) (Int.instLEInt) _ _ (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Grind.Ordered.Linarith.0.Lean.Grind.Linarith.le_add_le, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Lean.Grind.Linarith.le_add_le.h8 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : Std.IsPreorder α]
        [inst_3 : Lean.Grind.OrderedAdd α] {a b : α}, a ≤ 0 → a + b ≤ 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Ring.toIntModule) (Int.instLEInt) _ _ (0) (1) (by
  decide)) (by
  decide +kernel)

