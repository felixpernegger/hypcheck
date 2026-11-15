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
-- _private.Init.Data.Array.DecidableEq.0.Array.rel_of_isEqvAux, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.rel_of_isEqvAux.h4 : ¬∀ {α : Type} {r : α → α → Bool} {xs ys : Array α} {i : Nat}, i ≤ xs.size → ∀ {j : Nat}, j < i → xs.size = ys.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (#[0]) (#[]) (1) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Array.DecidableEq.0.Array.rel_of_isEqvAux, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.rel_of_isEqvAux.h6 : ¬∀ {α : Type} {r : α → α → Bool} {xs ys : Array α}, xs.size = ys.size → ∀ {i j : Nat}, j < i → i ≤ xs.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (#[]) (#[]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Array.DecidableEq.0.Array.rel_of_isEqvAux, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.rel_of_isEqvAux.h7 : ¬∀ {α : Type} {r : α → α → Bool} {xs ys : Array α} (hsz : xs.size = ys.size) {i : Nat} (hi : i ≤ xs.size) {j : Nat}
        (hj : j < i), r xs[j] ys[j] = Bool.true := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (#[0]) (#[0]) hc_k0 (1) hc_k1 (0) hc_k2) (by
  decide +kernel)

-- _private.Init.Data.Array.DecidableEq.0.Array.rel_of_isEqvAux, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.rel_of_isEqvAux.h9 : ¬∀ {α : Type} {r : α → α → Bool} {xs ys : Array α} (hsz : xs.size = ys.size) {i : Nat} (hi : i ≤ xs.size),
        xs.isEqvAux ys hsz r i hi = Bool.true → ∀ {j : Nat}, j < i := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (#[]) (#[]) hc_k0 (0) hc_k1 hc_k2 (0)) (by
  decide +kernel)

-- _private.Init.Data.Array.DecidableEq.0.Array.isEqvAux_of_rel, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.isEqvAux_of_rel.h4 : ¬∀ {α : Type} {r : α → α → Bool} {xs ys : Array α} {i : Nat}, i ≤ xs.size → xs.size = ys.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (#[]) (#[0]) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Array.DecidableEq.0.Array.isEqvAux_of_rel, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.isEqvAux_of_rel.h6 : ¬∀ {α : Type} {r : α → α → Bool} {xs ys : Array α}, xs.size = ys.size → ∀ {i : Nat}, i ≤ xs.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (#[]) (#[]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1)) (by
  decide +kernel)

-- _private.Init.Data.Array.DecidableEq.0.Array.isEqvAux_of_rel, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.isEqvAux_of_rel.h7 : ¬∀ {α : Type} {r : α → α → Bool} {xs ys : Array α} (hsz : xs.size = ys.size) {i : Nat} (hi : i ≤ xs.size),
        xs.isEqvAux ys hsz r i hi = Bool.true := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (#[0]) (#[0]) hc_k0 (1) hc_k1) (by
  decide +kernel)

-- _private.Init.Data.Array.DecidableEq.0.Array.isEqvAux_self, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.isEqvAux_self.h2 : ¬∀ {α : Type} (r : α → α → Bool) (xs : Array α) (i : Nat) (h : i ≤ xs.size), xs.isEqvAux xs rfl r i h = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (#[0]) (1) hc_k0) (by
  decide +kernel)

-- _private.Init.Data.Array.DecidableEq.0.Array.isEqvAux_self, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.isEqvAux_self.h5 : ¬∀ {α : Type} (r : α → α → Bool), (∀ (a : α), r a a = Bool.true) → ∀ (xs : Array α) (i : Nat), i ≤ xs.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => a ≤ b : Nat → Nat → Bool) (by
  simp) (#[]) (1)) (by
  decide +kernel)

-- _private.Init.Data.Array.DecidableEq.0.Array.rel_of_isEqv, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.rel_of_isEqv.h4 : ¬∀ {α : Type} {r : α → α → Bool} {xs ys : Array α},
        ∃ (h : xs.size = ys.size), ∀ (i : Nat) (h' : i < xs.size), r xs[i] ys[i] = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (#[]) (#[0])) (by
  decide +kernel)

