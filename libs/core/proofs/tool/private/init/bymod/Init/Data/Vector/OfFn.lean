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
-- _private.Init.Data.Vector.OfFn.0.Vector.ofFnM_go_succ, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.ofFnM_go_succ.h6 : Not
      (∀ {m : Type → Type} {α : Type} {i : Nat} {xs : Array α} {n : Nat} [inst : Monad m]
        {f :
          Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            m α}
        (hi : autoParam (@LE.le Nat instLENat i n) Vector.ofFnM_go_succ._auto_5) {h : @Eq Nat (@Array.size α xs) i},
        @Eq
          (m
            (Vector α
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@Vector.ofFnM.go m α
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            inst f i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) xs h)
          (@Bind.bind m (@Monad.toBind m inst) (Vector α n)
            (Vector α
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Vector.ofFnM.go m α n inst (fun (i : Fin n) => f (@Fin.castSucc n i)) i hi xs h) fun (as : Vector α n) =>
            @Bind.bind m (@Monad.toBind m inst) α
              (Vector α
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (f (Fin.last n)) fun (a : α) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                (Vector α
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Vector.push α n as a))) := fun hc_h => absurd (fun hc_k0 => @hc_h (fun α => Nat × α : Type → Type) (Nat) _ (@List.toArray Nat (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun
        (a :
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) hc_k0 rfl) (by
  decide +kernel)

-- _private.Init.Data.Vector.OfFn.0.Vector.ofFnM_go_succ, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.ofFnM_go_succ.h8 : ¬∀ {m : Type → Type} {α : Type} {i : Nat} {xs : Array α} {n : Nat} [inst : Monad m] [inst : LawfulMonad m]
        {f : Fin (n + 1) → m α} {h : xs.size = i}, i ≤ n := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) _ (#[0]) (0) (instMonadOption) _ (fun (a : Fin (0 + 1)) => Option.none) rfl) (by
  decide +kernel)

-- _private.Init.Data.Vector.OfFn.0.Vector.ofFnM_go_succ, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.ofFnM_go_succ.h9 : ¬∀ {m : Type → Type} {α : Type} {i : Nat} {xs : Array α} {n : Nat} [inst : Monad m] [inst : LawfulMonad m]
        {f : Fin (n + 1) → m α}, autoParam (i ≤ n) Vector.ofFnM_go_succ._auto_5 → xs.size = i := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (0) (#[0]) (0) (instMonadOption) _ (fun (a : Fin (0 + 1)) => Option.none) (by
  decide)) (by
  decide +kernel)

