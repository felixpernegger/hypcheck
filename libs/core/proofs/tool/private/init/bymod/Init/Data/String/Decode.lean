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
-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.helper₆, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.helper₆.h4 : ¬∀ {c : Char} {o : Option Char} {b : BitVec 32}, c.val.toBitVec = b → o.isSome = Bool.true → o = Option.some c := fun hc_h => absurd (@hc_h ('a') (Option.some '0') _ rfl (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.helper₆, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.helper₆.h5 : ¬∀ {c : Char} {o : Option Char} {b : BitVec 32},
        c.val.toBitVec = b → (∀ (d : Char), o = Option.some d → d.val.toBitVec = b) → o = Option.some c := fun hc_h => absurd (@hc_h ('a') (Option.none) _ rfl (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.toBitVec_val_assemble₁, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.toBitVec_val_assemble₁.h3 : ¬∀ {w : UInt8} {h : ByteArray.utf8DecodeChar?.parseFirstByte w = ByteArray.utf8DecodeChar?.FirstByte.done} {c : Char},
        c.val.toBitVec = BitVec.setWidth 32 w.toBitVec := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (by
  rfl) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₄_eq_some_middle, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₄_eq_some_middle.h5 : ¬∀ {w x : UInt8} {y : UInt8} {z : UInt8} {c : Char}, y.isUTF8ContinuationByte = Bool.true := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.utf8Size_assemble₄, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.utf8Size_assemble₄.h5 : ¬∀ {w x y z : UInt8} {c : Char}, c.utf8Size = 4 := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₄_eq_some_left, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₄_eq_some_left.h5 : ¬∀ {w : UInt8} {x : UInt8} {y z : UInt8} {c : Char}, x.isUTF8ContinuationByte = Bool.true := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_append_eq_assemble₂, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_append_eq_assemble₂.h2 : ¬∀ {l : List UInt8} {b : ByteArray}, l.length = 2 := fun hc_h => absurd (@hc_h ([]) ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_append_eq_assemble₂, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_append_eq_assemble₂.h3 : ¬∀ {l : List UInt8} {b : ByteArray} (hl : l.length = 2),
        (l.toByteArray ++ b).utf8DecodeChar? 0 = ByteArray.utf8DecodeChar?.assemble₂ l[0] l[1] := fun hc_h => absurd (fun hc_k0 => @hc_h ([UInt8.ofNat 0, UInt8.ofNat 1]) ({ data := #[] : ByteArray }) hc_k0) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_append_eq_assemble₄, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_append_eq_assemble₄.h2 : ¬∀ {l : List UInt8} {b : ByteArray}, l.length = 4 := fun hc_h => absurd (@hc_h ([]) ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₄_eq_some_right, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₄_eq_some_right.h5 : ¬∀ {w x y : UInt8} {z : UInt8} {c : Char}, z.isUTF8ContinuationByte = Bool.true := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_append_eq_assemble₃, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_append_eq_assemble₃.h2 : ¬∀ {l : List UInt8} {b : ByteArray}, l.length = 3 := fun hc_h => absurd (@hc_h ([]) ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_append_eq_assemble₃, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_append_eq_assemble₃.h3 : ¬∀ {l : List UInt8} {b : ByteArray} (hl : l.length = 3),
        (l.toByteArray ++ b).utf8DecodeChar? 0 = ByteArray.utf8DecodeChar?.assemble₃ l[0] l[1] l[2] := fun hc_h => absurd (fun hc_k0 => @hc_h ([UInt8.ofNat 0, UInt8.ofNat 1, UInt8.ofNat 2]) ({ data := #[] : ByteArray }) hc_k0) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₃_eq_some_left, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₃_eq_some_left.h4 : ¬∀ {w : UInt8} {x : UInt8} {y : UInt8} {c : Char}, x.isUTF8ContinuationByte = Bool.true := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.utf8Size_assemble₃, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.utf8Size_assemble₃.h4 : ¬∀ {w x y : UInt8} {c : Char}, c.utf8Size = 3 := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.helper₂, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.helper₂.h4 : ¬∀ {w' : Nat} (w : Nat) (b : BitVec (w' + w)) {v : BitVec w'}, b = v ++ BitVec.extractLsb' 0 w b := fun hc_h => absurd (@hc_h (1) (0) (0#1) (1#1)) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.le_val_assemble₂, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.le_val_assemble₂.h3 : ¬∀ {w x : UInt8} {c : Char}, 128 ≤ c.val := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_eq_assemble₁, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_eq_assemble₁.h1 : ¬∀ {b : ByteArray}, 1 ≤ b.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.utf8Size_assemble₂, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.utf8Size_assemble₂.h3 : ¬∀ {w x : UInt8} {c : Char}, c.utf8Size = 2 := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₂_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₂_eq_some.h3 : ¬∀ {w : UInt8} {x : UInt8} {c : Char}, x.isUTF8ContinuationByte = Bool.true := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_eq_assemble₄, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_eq_assemble₄.h1 : ¬∀ {b : ByteArray}, 4 ≤ b.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8Size_le_of_utf8DecodeChar?_eq_some, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8Size_le_of_utf8DecodeChar?_eq_some.h2 : ¬∀ {b : ByteArray} {c : Char}, c.utf8Size ≤ b.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three.h1 : ¬∀ {c : Char}, c.utf8Size = 3 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_four, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_four.h1 : ¬∀ {c : Char}, c.utf8Size = 4 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two.h1 : ¬∀ {c : Char}, c.utf8Size = 2 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_two, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_two.h1 : ¬∀ {c : Char},
        List.map UInt8.toBitVec (String.utf8EncodeChar c) =
          [6#3 ++ BitVec.extractLsb' 6 5 c.val.toBitVec, 2#2 ++ BitVec.extractLsb' 0 6 c.val.toBitVec] := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_three, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_three.h1 : ¬∀ {c : Char}, c.utf8Size = 3 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four.h1 : ¬∀ {c : Char}, c.utf8Size = 4 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_three_of_utf8Size_eq_four, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_three_of_utf8Size_eq_four.h1 : ¬∀ {c : Char}, c.utf8Size = 4 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_two, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_two.h1 : ¬∀ {c : Char}, c.utf8Size = 2 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_threeMore, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_threeMore.h1 : ¬∀ {b : UInt8}, b.toBitVec = 30#5 ++ BitVec.setWidth 3 b.toBitVec := fun hc_h => absurd (@hc_h (UInt8.ofNat 0)) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_twoMore, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_twoMore.h1 : ¬∀ {b : UInt8}, b.toBitVec = 14#4 ++ BitVec.setWidth 4 b.toBitVec := fun hc_h => absurd (@hc_h (UInt8.ofNat 0)) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_three, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_three.h1 : ¬∀ {c : Char}, c.utf8Size = 3 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_oneMore, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_oneMore.h1 : ¬∀ {b : UInt8}, b.toBitVec = 6#3 ++ BitVec.setWidth 5 b.toBitVec := fun hc_h => absurd (@hc_h (UInt8.ofNat 0)) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three.h1 : ¬∀ {c : Char}, c.utf8Size = 3 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four.h1 : ¬∀ {c : Char}, c.utf8Size = 4 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar_extract_congr_of_le, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar_extract_congr_of_le.h4 : ¬∀ {bytes : ByteArray} (i j j' : Nat) {h' : ((bytes.extract i j').utf8DecodeChar? 0).isSome = Bool.true},
        j ≤ j' → ((bytes.extract i j).utf8DecodeChar? 0).isSome = Bool.true := fun hc_h => absurd (@hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.le_val_assemble₄, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.le_val_assemble₄.h5 : ¬∀ {w x y z : UInt8} {c : Char}, 65535 < c.val := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_append_eq_assemble₁, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_append_eq_assemble₁.h2 : ¬∀ {l : List UInt8} {b : ByteArray}, l.length = 1 := fun hc_h => absurd (@hc_h ([]) ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.toBitVec_val_assemble₄, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.toBitVec_val_assemble₄.h5 : ¬∀ {w x y z : UInt8} (c : Char),
        c.val.toBitVec =
          BitVec.setWidth 32
            (BitVec.setWidth 3 w.toBitVec ++ BitVec.setWidth 6 x.toBitVec ++ BitVec.setWidth 6 y.toBitVec ++
              BitVec.setWidth 6 z.toBitVec) := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.toBitVec_val_assemble₃, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.toBitVec_val_assemble₃.h4 : ¬∀ {w x y : UInt8} (c : Char),
        c.val.toBitVec =
          BitVec.setWidth 32 (BitVec.setWidth 4 w.toBitVec ++ BitVec.setWidth 6 x.toBitVec ++ BitVec.setWidth 6 y.toBitVec) := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.le_val_assemble₃, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.le_val_assemble₃.h4 : ¬∀ {w x y : UInt8} {c : Char}, 2048 ≤ c.val := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₃_eq_some_right, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_of_assemble₃_eq_some_right.h4 : ¬∀ {w x : UInt8} {y : UInt8} {c : Char}, y.isUTF8ContinuationByte = Bool.true := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.toBitVec_val_assemble₂, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.toBitVec_val_assemble₂.h3 : ¬∀ {w x : UInt8} (c : Char),
        c.val.toBitVec = BitVec.setWidth 32 (BitVec.setWidth 5 w.toBitVec ++ BitVec.setWidth 6 x.toBitVec) := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 0) ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_eq_assemble₂, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_eq_assemble₂.h1 : ¬∀ {b : ByteArray}, 2 ≤ b.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_eq_assemble₂, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_eq_assemble₂.h2 : ¬∀ {b : ByteArray} (hb : 2 ≤ b.size), b.utf8DecodeChar? 0 = ByteArray.utf8DecodeChar?.assemble₂ b[0] b[1] := fun hc_h => absurd (fun hc_k0 => @hc_h ({ data := #[UInt8.ofNat 0, UInt8.ofNat 1] : ByteArray }) hc_k0) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.utf8DecodeChar?_eq_assemble₃, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.utf8DecodeChar?_eq_assemble₃.h1 : ¬∀ {b : ByteArray}, 3 ≤ b.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.Nat.add_two_pow_eq_or_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Nat.add_two_pow_eq_or_of_lt.h2 : ¬∀ {b : Nat} (i a : Nat), b + 2 ^ i * a = b ||| 2 ^ i * a := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four.h1 : ¬∀ {c : Char}, c.utf8Size = 4 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three.h1 : ¬∀ {c : Char}, c.utf8Size = 3 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.helper₅, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.helper₅.h1 : ¬∀ {w : UInt8}, w < 128 := fun hc_h => absurd (@hc_h (UInt8.ofNat 128)) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four.h1 : ¬∀ {c : Char}, c.utf8Size = 4 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_four, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ByteArray.utf8DecodeChar?.isUTF8ContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_four.h1 : ¬∀ {c : Char}, c.utf8Size = 4 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_four, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_four.h1 : ¬∀ {c : Char},
        List.map UInt8.toBitVec (String.utf8EncodeChar c) =
          [30#5 ++ BitVec.extractLsb' 18 3 c.val.toBitVec, 2#2 ++ BitVec.extractLsb' 12 6 c.val.toBitVec,
            2#2 ++ BitVec.extractLsb' 6 6 c.val.toBitVec, 2#2 ++ BitVec.extractLsb' 0 6 c.val.toBitVec] := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_three, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_three.h1 : ¬∀ {c : Char},
        List.map UInt8.toBitVec (String.utf8EncodeChar c) =
          [14#4 ++ BitVec.extractLsb' 12 4 c.val.toBitVec, 2#2 ++ BitVec.extractLsb' 6 6 c.val.toBitVec,
            2#2 ++ BitVec.extractLsb' 0 6 c.val.toBitVec] := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two.h1 : ¬∀ {c : Char}, c.utf8Size = 2 := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- _private.Init.Data.String.Decode.0.Char.toBitVec_val_of_utf8Size_eq_four, hypothesis 1: removable
/- FAILED: 6:73: unexpected identifier after decimal point; consider parenthesizing the number | 19:73: unexpected identifier after decimal point; consider parenthesizing the number | 6:73: unexpected identifier after decimal point; consider parenthesizing the number | 19:73: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Char.toBitVec_val_of_utf8Size_eq_four.h1.gneg : ∀ {c : Char}, ¬c.utf8Size = 4 → c.val.toBitVec = BitVec.setWidth 32 (BitVec.extractLsb' 0 21 c.val.toBitVec) := by
  (intros; grind)
theorem HypCheckProof.Char.toBitVec_val_of_utf8Size_eq_four.h1 : ∀ {c : Char}, c.val.toBitVec = BitVec.setWidth 32 (BitVec.extractLsb' 0 21 c.val.toBitVec) := by
  intro hc_x0
  exact Classical.byCases (fun hc_h => @_private.Init.Data.String.Decode.0.Char.toBitVec_val_of_utf8Size_eq_four hc_x0 hc_h) (fun hc_hn => @HypCheckProof.Char.toBitVec_val_of_utf8Size_eq_four.h1.gneg hc_x0 hc_hn)
-/

