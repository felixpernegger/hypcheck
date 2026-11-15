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
-- _private.Std.Http.Data.URI.Encoding.0.Std.Http.URI.IsAllowedEncodedQueryChars.push, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Http.URI.IsAllowedEncodedQueryChars.push.h3 : ¬∀ {r : UInt8 → Bool} {c : UInt8} {bs : ByteArray},
        Std.Http.URI.isEncodedQueryChar r c = Bool.true → Std.Http.URI.IsAllowedEncodedQueryChars r (bs.push c) := fun hc_h => absurd (@hc_h (fun (a : UInt8) => if a = UInt8.ofNat 0 then Bool.false else Bool.true) (UInt8.ofNat 1) ({ data := #[UInt8.ofNat 0] : ByteArray }) (by
  decide)) (by
  decide +kernel)

-- _private.Std.Http.Data.URI.Encoding.0.Std.Http.URI.IsAllowedEncodedQueryChars.push, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Http.URI.IsAllowedEncodedQueryChars.push.h4 : ¬∀ {r : UInt8 → Bool} {c : UInt8} {bs : ByteArray},
        Std.Http.URI.IsAllowedEncodedQueryChars r bs → Std.Http.URI.IsAllowedEncodedQueryChars r (bs.push c) := fun hc_h => absurd (@hc_h (fun (a : UInt8) => Bool.false) (UInt8.ofNat 0) ({ data := #[] : ByteArray }) (by
  decide +kernel)) (by
  decide +kernel)

-- _private.Std.Http.Data.URI.Encoding.0.Std.Http.URI.IsAllowedEncodedChars.push, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Http.URI.IsAllowedEncodedChars.push.h3 : ¬∀ {r : UInt8 → Bool} {c : UInt8} {bs : ByteArray},
        Std.Http.URI.isEncodedChar r c = Bool.true → Std.Http.URI.IsAllowedEncodedChars r (bs.push c) := fun hc_h => absurd (@hc_h (fun (a : UInt8) => if a = UInt8.ofNat 0 then Bool.false else Bool.true) (UInt8.ofNat 1) ({ data := #[UInt8.ofNat 0] : ByteArray }) (by
  decide)) (by
  decide +kernel)

-- _private.Std.Http.Data.URI.Encoding.0.Std.Http.URI.IsAllowedEncodedChars.push, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Http.URI.IsAllowedEncodedChars.push.h4 : ¬∀ {r : UInt8 → Bool} {c : UInt8} {bs : ByteArray},
        Std.Http.URI.IsAllowedEncodedChars r bs → Std.Http.URI.IsAllowedEncodedChars r (bs.push c) := fun hc_h => absurd (@hc_h (fun (a : UInt8) => Bool.false) (UInt8.ofNat 0) ({ data := #[] : ByteArray }) (by
  decide +kernel)) (by
  decide +kernel)

-- _private.Std.Http.Data.URI.Encoding.0.Std.Http.URI.isHexDigit_isEncodedQueryChar, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Http.URI.isHexDigit_isEncodedQueryChar.h2 : ¬∀ {r : UInt8 → Bool} {c : UInt8}, Std.Http.URI.isEncodedQueryChar r c = Bool.true := fun hc_h => absurd (@hc_h (fun (a : UInt8) => Bool.false) (UInt8.ofNat 0)) (by
  decide +kernel)

-- _private.Std.Http.Data.URI.Encoding.0.Std.Http.URI.isHexDigit_isEncodedChar, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Http.URI.isHexDigit_isEncodedChar.h2 : ¬∀ {r : UInt8 → Bool} {c : UInt8}, Std.Http.URI.isEncodedChar r c = Bool.true := fun hc_h => absurd (@hc_h (fun (a : UInt8) => Bool.false) (UInt8.ofNat 0)) (by
  decide +kernel)

-- _private.Std.Http.Data.URI.Encoding.0.Std.Http.URI.hexDigit_isHexDigit, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Http.URI.hexDigit_isHexDigit.h1 : ¬∀ {x : UInt8}, Std.Http.Internal.Char.isHexDigitByte (Std.Http.URI.hexDigit x) = Bool.true := fun hc_h => absurd (@hc_h (UInt8.ofNat 16)) (by
  decide +kernel)

