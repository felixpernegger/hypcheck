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
-- _private.Init.Data.List.ToArray.0.List.idxAuxOf_toArray, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.idxAuxOf_toArray.h6 : ¬∀ {α : Type} {l' : List α} [inst : BEq α] (a : α) (l : List α) (j : Nat) (h : l'.length + j = l.length),
        l.toArray.idxOfAux a j = List.findFinIdx?.go (fun (x : α) => x == a) l l' j h := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) ([0]) (instBEqOfDecidableEq) (0) ([1]) (0) hc_k0) (by
  decide +kernel)

-- _private.Init.Data.List.ToArray.0.List.idxAuxOf_toArray, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.idxAuxOf_toArray.h7 : ¬∀ {α : Type} {l' : List α} [inst : BEq α] (a : α) (l : List α) (j : Nat), l' = List.drop j l → l'.length + j = l.length := fun hc_h => absurd (@hc_h (Nat) _ (instBEqOfDecidableEq) (0) ([]) (1) rfl) (by
  decide +kernel)

-- _private.Init.Data.List.ToArray.0.List.findFinIdx?_loop_toArray, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.findFinIdx?_loop_toArray.h5 : ¬∀ {α : Type} {l' : List α} {p : α → Bool} {j : Nat} {l : List α}, l' = List.drop j l → l'.length + j = l.length := fun hc_h => absurd (@hc_h (Nat) _ (fun n => n % 2 == 0 : Nat → Bool) (1) ([]) rfl) (by
  decide +kernel)

-- _private.Init.Data.List.ToArray.0.List.findFinIdx?_loop_toArray, hypothesis 6: necessary
/- FAILED: 3:30: expected token | 5:87: expected token | 3:30: expected token | 5:87: expected token | 3:30: expected token | 16:34: expected token | 3:30: expected token | 16:34: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.findFinIdx?_loop_toArray.h6 : ¬∀ {α : Type} {l' : List α} {p : α → Bool} {j : Nat} {l : List α} {h : l'.length + j = l.length},
        Array.findFinIdx?.loop✝ p l.toArray j = List.findFinIdx?.go p l l' j h := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) ([0]) (fun n => n % 2 == 0 : Nat → Bool) (0) ([1]) hc_k0) (by
  decide +kernel)
-/

-- _private.Init.Data.List.ToArray.0.List.findSomeRevM?_find_toArray, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.findSomeRevM?_find_toArray.h8 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] [inst : LawfulMonad m] (f : α → m (Option β)) (l : List α) (i : Nat),
        i ≤ l.toArray.size := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (instMonadOption) _ (fun (a : Nat) => Option.none) ([]) (1)) (by
  decide +kernel)

-- _private.Init.Data.List.ToArray.0.List.insertIdx_loop_toArray, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.insertIdx_loop_toArray.h4 : ¬∀ {α : Type} (i : Nat) (l : List α) (j : Nat), i ≤ j → j < l.toArray.size := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.List.ToArray.0.List.insertIdx_loop_toArray, hypothesis 5: necessary
/- FAILED: 3:28: expected token | 4:44: expected token | 3:28: expected token | 4:44: expected token | 3:28: expected token | 10:32: expected token | 3:28: expected token | 10:32: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.insertIdx_loop_toArray.h5 : ¬∀ {α : Type} (i : Nat) (l : List α) (j : Nat) (hj : j < l.toArray.size),
        Array.insertIdx.loop✝ i l.toArray (⟨j, hj⟩ : Fin l.toArray.size) =
          (List.take i l ++ l[j] :: List.drop i (List.take j l) ++ List.drop (j + 1) l).toArray := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (1) ([0]) (0) hc_k0) (by
  decide +kernel)
-/

