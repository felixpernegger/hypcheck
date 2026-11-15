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
-- _private.Init.Data.String.Lemmas.Lossy.0.String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte, hypothesis 3: necessary
/- FAILED: 5:105: expected token | 18:51: expected token | 6:42: expected token | 10:51: expected token | 2:126: expected token | 4:37: expected token | 2:126: expected token | 4:37: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte.h3 : ¬∀ {b : ByteArray} {i j : Nat},
        j ≤ b.size →
          (∀ (k : Nat) (hk : k < b.size), i ≤ k → k < j → b[k].isUTF8ContinuationByte = Bool.true) →
            (∀ (h : j < b.size), ¬b[j].isUTF8ContinuationByte = Bool.true) → String.skipContinuationBytes✝ b i = j := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (1) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte, hypothesis 4: necessary
/- FAILED: 5:105: expected token | 18:51: expected token | 6:42: expected token | 10:51: expected token | 2:126: expected token | 4:37: expected token | 2:126: expected token | 4:37: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte.h4 : ¬∀ {b : ByteArray} {i j : Nat},
        i ≤ j →
          (∀ (k : Nat) (hk : k < b.size), i ≤ k → k < j → b[k].isUTF8ContinuationByte = Bool.true) →
            (∀ (h : j < b.size), ¬b[j].isUTF8ContinuationByte = Bool.true) → String.skipContinuationBytes✝ b i = j := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (0) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte, hypothesis 5: necessary
/- FAILED: 5:105: expected token | 12:51: expected token | 6:42: expected token | 8:51: expected token | 2:126: expected token | 4:37: expected token | 2:126: expected token | 4:37: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte.h5 : ¬∀ {b : ByteArray} {i j : Nat},
        i ≤ j →
          j ≤ b.size →
            (∀ (h : j < b.size), ¬b[j].isUTF8ContinuationByte = Bool.true) → String.skipContinuationBytes✝ b i = j := fun hc_h => absurd (@hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (0) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some, hypothesis 5: necessary
/- FAILED: 3:44: expected token | 5:45: expected token | 3:44: expected token | 5:45: expected token | 2:107: expected token | 4:32: expected token | 2:107: expected token | 4:32: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some.h5 : ¬∀ {b : ByteArray} {i : Nat} {acc : String} {c : Char},
        i < b.size → String.fromUTF8Lossy.go✝ b i acc = String.fromUTF8Lossy.go✝ b (i + c.utf8Size) (acc.push c) := fun hc_h => absurd (@hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (0) ("") ('a') (by
  decide)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none, hypothesis 3: necessary
/- FAILED: 4:33: expected token | 5:45: expected token | 4:33: expected token | 5:45: expected token | 2:107: expected token | 4:32: expected token | 2:107: expected token | 4:32: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none.h3 : ¬∀ {b : ByteArray} {i : Nat} {acc : String},
        b.utf8DecodeChar? i = Option.none →
          String.fromUTF8Lossy.go✝ b i acc =
            String.fromUTF8Lossy.go✝ b (String.skipContinuationBytes✝ b (i + 1)) (acc.push '�') := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (0) ("") (by
  decide)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none, hypothesis 4: necessary
/- FAILED: 4:33: expected token | 5:45: expected token | 4:33: expected token | 5:45: expected token | 2:107: expected token | 4:32: expected token | 2:107: expected token | 4:32: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none.h4 : ¬∀ {b : ByteArray} {i : Nat} {acc : String},
        i < b.size →
          String.fromUTF8Lossy.go✝ b i acc =
            String.fromUTF8Lossy.go✝ b (String.skipContinuationBytes✝ b (i + 1)) (acc.push '�') := fun hc_h => absurd (@hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (0) ("") (by
  decide)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.skipContinuationBytes_of_isUTF8ContinuationByte, hypothesis 3: necessary
/- FAILED: 2:153: expected token | 5:47: expected token | 2:153: expected token | 5:47: expected token | 2:116: expected token | 4:37: expected token | 2:116: expected token | 4:37: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.skipContinuationBytes_of_isUTF8ContinuationByte.h3 : ¬∀ {b : ByteArray} {i : Nat}, i < b.size → String.skipContinuationBytes✝ b i = String.skipContinuationBytes✝ b (i + 1) := fun hc_h => absurd (@hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (0) (by
  decide)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.fromUTF8Lossy.go_of_not_lt, hypothesis 3: necessary
/- FAILED: 2:129: expected token | 2:145: expected token | 2:129: expected token | 2:145: expected token | 2:90: expected token | 4:32: expected token | 2:90: expected token | 4:32: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.fromUTF8Lossy.go_of_not_lt.h3 : ¬∀ {b : ByteArray} {i : Nat} {acc : String}, String.fromUTF8Lossy.go✝ b i acc = acc := fun hc_h => absurd (@hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (0) ("")) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.fromUTF8Lossy_of_utf8DecodeChar?_eq_none, hypothesis 1: necessary
/- FAILED: 5:97: expected token | 9:56: expected token | 5:97: expected token | 9:56: expected token | 5:78: expected token | 7:43: expected token | 5:78: expected token | 7:43: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.fromUTF8Lossy_of_utf8DecodeChar?_eq_none.h1 : ¬∀ {b : ByteArray},
        b.utf8DecodeChar? 0 = Option.none →
          String.fromUTF8Lossy b =
            String.singleton '�' ++ String.fromUTF8Lossy (b.extract (String.skipContinuationBytes✝ b 1) b.size) := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (by
  decide)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.fromUTF8Lossy_of_utf8DecodeChar?_eq_none, hypothesis 2: necessary
/- FAILED: 5:97: expected token | 8:56: expected token | 5:97: expected token | 8:56: expected token | 6:43: expected token | 19:43: expected token | 6:43: expected token | 19:43: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.fromUTF8Lossy_of_utf8DecodeChar?_eq_none.h2 : ¬∀ {b : ByteArray},
        0 < b.size →
          String.fromUTF8Lossy b =
            String.singleton '�' ++ String.fromUTF8Lossy (b.extract (String.skipContinuationBytes✝ b 1) b.size) := fun hc_h => absurd (@hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (by
  decide)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Lossy.0.String.skipContinuationBytes_le_size, hypothesis 2: necessary
/- FAILED: 2:122: expected token | 2:148: expected token | 2:122: expected token | 2:148: expected token | 2:98: expected token | 4:37: expected token | 2:98: expected token | 4:37: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.skipContinuationBytes_le_size.h2 : ¬∀ {b : ByteArray} {i : Nat}, String.skipContinuationBytes✝ b i ≤ b.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (1)) (by
  decide +kernel)
-/

