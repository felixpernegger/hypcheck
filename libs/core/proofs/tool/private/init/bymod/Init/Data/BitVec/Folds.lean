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
-- _private.Init.Data.BitVec.Folds.0.BitVec.iunfoldr.eq_test, hypothesis 6: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.BitVec.iunfoldr.eq_test.h6.inst : ¬BitVec.iunfoldr (fun (a : Fin 0) (a_1 : Nat) => (0, Bool.false)) 0 =
        ((fun (n : Nat) => n + 1) 0, BitVec.truncate 0 0#0) := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.BitVec.iunfoldr.eq_test.h6.prem0 : ∀ (i : Fin 0),
      (fun (a : Fin 0) (a_1 : Nat) => (0, Bool.false)) i ((fun (n : Nat) => n + 1) ↑i) =
        ((fun (n : Nat) => n + 1) (↑i + 1), (0#0).getLsbD ↑i) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.BitVec.iunfoldr.eq_test.h6 : ¬∀ {w : Nat} {α : Type} {f : Fin w → α → α × Bool} (state : Nat → α) (value : BitVec w) (a : α),
        (∀ (i : Fin w), f i (state ↑i) = (state (↑i + 1), value.getLsbD ↑i)) →
          BitVec.iunfoldr f a = (state w, BitVec.truncate w value) := fun hc_h => HypCheckProof.BitVec.iunfoldr.eq_test.h6.inst (@hc_h (0) (Nat) (fun (a : Fin 0) (a_1 : Nat) => (0, Bool.false)) (fun (n : Nat) => n + 1) (0#0) (0) HypCheckProof.BitVec.iunfoldr.eq_test.h6.prem0)

-- _private.Init.Data.BitVec.Folds.0.BitVec.iunfoldr.eq_test, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.iunfoldr.eq_test.h7 : ¬∀ {w : Nat} {α : Type} {f : Fin w → α → α × Bool} (state : Nat → α) (value : BitVec w) (a : α),
        state 0 = a → BitVec.iunfoldr f a = (state w, BitVec.truncate w value) := fun hc_h => absurd (@hc_h (1) (Nat) (fun (a : Fin 1) (a_1 : Nat) => (0, Bool.false)) (fun n => n + 1 : Nat → Nat) (0#1) _ rfl) (by
  decide +kernel)

