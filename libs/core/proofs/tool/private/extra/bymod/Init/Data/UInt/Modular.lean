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
-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_go_spec, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.UInt64.invMod?_go_spec.h1.gneg : ∀ (modulus : UInt64),
      ¬modulus ≠ 0 →
        ∀ (a oldR r oldS s : Nat),
          oldS < modulus.toNat →
            s < modulus.toNat →
              oldS * a % modulus.toNat = oldR % modulus.toNat →
                s * a % modulus.toNat = r % modulus.toNat →
                  match UInt64.invMod?.go modulus oldR r oldS s with
                  | (gcd, inverse) =>
                    gcd = oldR.gcd r ∧ inverse < modulus.toNat ∧ inverse * a % modulus.toNat = oldR.gcd r % modulus.toNat := by
  (intros; simp_all; done)
theorem HypCheckProof.UInt64.invMod?_go_spec.h1 : ∀ (modulus : UInt64) (a oldR r oldS s : Nat),
      oldS < modulus.toNat →
        s < modulus.toNat →
          oldS * a % modulus.toNat = oldR % modulus.toNat →
            s * a % modulus.toNat = r % modulus.toNat →
              match UInt64.invMod?.go modulus oldR r oldS s with
              | (gcd, inverse) =>
                gcd = oldR.gcd r ∧ inverse < modulus.toNat ∧ inverse * a % modulus.toNat = oldR.gcd r % modulus.toNat := by
  intro hc_x0 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @UInt64.invMod?_go_spec hc_x0 hc_h hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.UInt64.invMod?_go_spec.h1.gneg hc_x0 hc_hn hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.UInt64.invMod?_go_spec.h1.derivable : ∀ (modulus : UInt64) (a oldR r oldS s : Nat),
      oldS < modulus.toNat →
        s < modulus.toNat →
          oldS * a % modulus.toNat = oldR % modulus.toNat → s * a % modulus.toNat = r % modulus.toNat → modulus ≠ 0 := by
  (intros; grind)

-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_eq_some_spec, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.UInt64.invMod?_eq_some_spec.h3.gneg : ∀ {a modulus x : UInt64},
      ¬modulus ≠ 0 →
        a.invMod? modulus = Option.some x → x.toNat < modulus.toNat ∧ a.toNat * x.toNat % modulus.toNat = 1 % modulus.toNat := by
  (intros; simp_all; done)
theorem HypCheckProof.UInt64.invMod?_eq_some_spec.h3 : ∀ {a modulus x : UInt64},
      a.invMod? modulus = Option.some x → x.toNat < modulus.toNat ∧ a.toNat * x.toNat % modulus.toNat = 1 % modulus.toNat := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @UInt64.invMod?_eq_some_spec hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.UInt64.invMod?_eq_some_spec.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)

