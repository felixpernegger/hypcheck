import Std

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
-- _private.Std.Data.Internal.List.Associative.0.Std.Internal.List.getValueCast?_eq_getEntry?, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Internal.List.getValueCast?_eq_getEntry?.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l : List ((a : α) × β a)} {a : α}, LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) (0)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- _private.Std.Data.Internal.List.Associative.0.Std.Internal.List.min_eq_left, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Internal.List.min_eq_left.h5 : Not
      (∀ {α : Type} {β : α → Type} [inst : Ord α] {p q : @Sigma α fun (a : α) => β a},
        @Eq (@Sigma α fun (a : α) => β a)
          (@Min.min (@Sigma α fun (a : α) => β a) (@Std.Internal.List.minSigmaOfOrd α β inst) p q) p) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide +kernel)

-- _private.Std.Data.Internal.List.Associative.0.Std.Internal.List.min_eq_left_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Internal.List.min_eq_left_of_lt.h5 : Not
      (∀ {α : Type} {β : α → Type} [inst : Ord α] {p q : @Sigma α fun (a : α) => β a},
        @Eq (@Sigma α fun (a : α) => β a)
          (@Min.min (@Sigma α fun (a : α) => β a) (@Std.Internal.List.minSigmaOfOrd α β inst) p q) p) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide +kernel)

-- _private.Std.Data.Internal.List.Associative.0.Std.Internal.List.Option.eq_get_iff_some_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Internal.List.Option.eq_get_iff_some_eq.h2 : ¬∀ {α : Type} {o : Option α} {k : α}, o.isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Option.none) (0)) (by
  decide +kernel)

-- _private.Std.Data.Internal.List.Associative.0.Std.Internal.List.Option.get_eq_iff_eq_some, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Internal.List.Option.get_eq_iff_eq_some.h2 : ¬∀ {α : Type} {o : Option α} {k : α}, o.isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Option.none) (0)) (by
  decide +kernel)

