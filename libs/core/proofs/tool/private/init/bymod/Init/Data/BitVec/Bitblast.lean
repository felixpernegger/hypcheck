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
-- _private.Init.Data.BitVec.Bitblast.0.BitVec.extractLsb'_extractAndExtendAux, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.extractLsb'_extractAndExtendAux.h6 : ¬∀ {w : Nat} {i : Nat} {k len : Nat} {x : BitVec w} (acc : BitVec (k * len)),
        (∀ (i : Nat), i < k → BitVec.extractLsb' (i * len) len acc = BitVec.setWidth len (BitVec.extractLsb' i 1 x)) → k ≤ w := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0#0) (0#0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.extractLsb'_extractAndExtendAux, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.extractLsb'_extractAndExtendAux.h7 : ¬∀ {w i k len : Nat} {x : BitVec w} (acc : BitVec (k * len)) (hle : k ≤ w),
        BitVec.extractLsb' (i * len) len (BitVec.extractAndExtendAux k len x acc hle) =
          BitVec.setWidth len (BitVec.extractLsb' i 1 x) := fun hc_h => absurd (fun hc_k0 => @hc_h (1) (0) (1) (1) (0#1) (1#1) hc_k0) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.getLsbD_extractAndExtend_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.getLsbD_extractAndExtend_of_lt.h5 : ¬∀ {w k v pos : Nat} {x : BitVec w},
        (BitVec.extractAndExtend v x).getLsbD (pos * v + k) = (BitVec.extractAndExtendBit pos v x).getLsbD k := fun hc_h => absurd (@hc_h (2) (1) (1) (0) (2#2)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.Nat.mul_add_le_mul_of_succ_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.Nat.mul_add_le_mul_of_succ_le.h3 : ¬∀ {a b c : Nat}, a * b + b ≤ c * b := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.Nat.div_add_eq_left_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.Nat.div_add_eq_left_of_lt.h3 : ¬∀ {x y z : Nat}, y < z → 0 < z → (x + y) / z = x / z := fun hc_h => absurd (@hc_h (1) (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.Nat.div_add_eq_left_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.Nat.div_add_eq_left_of_lt.h4 : ¬∀ {x y z : Nat}, z ∣ x → 0 < z → (x + y) / z = x / z := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.Nat.div_add_eq_left_of_lt, hypothesis 5: removable
/- FAILED: 6:75: unexpected identifier after decimal point; consider parenthesizing the number | 17:75: unexpected identifier after decimal point; consider parenthesizing the number | 6:75: unexpected identifier after decimal point; consider parenthesizing the number | 17:75: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.BitVec.Nat.div_add_eq_left_of_lt.h5.gneg : ∀ {x y z : Nat}, z ∣ x → y < z → ¬0 < z → (x + y) / z = x / z := by
  (intros; omega)
theorem HypCheckProof.BitVec.Nat.div_add_eq_left_of_lt.h5 : ∀ {x y z : Nat}, z ∣ x → y < z → (x + y) / z = x / z := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact Classical.byCases (fun hc_h => @_private.Init.Data.BitVec.Bitblast.0.BitVec.Nat.div_add_eq_left_of_lt hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h) (fun hc_hn => @HypCheckProof.BitVec.Nat.div_add_eq_left_of_lt.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.BitVec.Nat.div_add_eq_left_of_lt.h5.derivable : ∀ {x y z : Nat}, z ∣ x → y < z → 0 < z := by
  (intros; omega)
-/

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.addRecAux_eq_of, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.addRecAux_eq_of.h5 : ¬∀ {len w len' : Nat} {x : BitVec (len * w)} {y : BitVec (len' * w)},
        (∀ (i : Nat),
            i < (len' + 1) / 2 →
              BitVec.extractLsb' (i * w) w x =
                BitVec.extractLsb' (2 * i * w) w y + BitVec.extractLsb' ((2 * i + 1) * w) w y) →
          BitVec.addRecAux x len 0#w = BitVec.addRecAux y len' 0#w := fun hc_h => absurd (@hc_h (1) (1) (0) (1#1) (0#0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.addRecAux_eq_of, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.addRecAux_eq_of.h6 : ¬∀ {len w len' : Nat} {x : BitVec (len * w)} {y : BitVec (len' * w)},
        len = (len' + 1) / 2 → BitVec.addRecAux x len 0#w = BitVec.addRecAux y len' 0#w := fun hc_h => absurd (@hc_h (1) (1) (1) (0#1) (1#1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.addRecAux_append_extractLsb', hypothesis 4: removable
/- FAILED: 13:75: unexpected identifier after decimal point; consider parenthesizing the number | 147:75: unexpected identifier after decimal point; consider parenthesizing the number | 13:75: unexpected identifier after decimal point; consider parenthesizing the number | 147:75: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.BitVec.addRecAux_append_extractLsb'.h4.gneg : ∀ {len w : Nat} {hcast : w + (len - 1) * w = len * w} {x : BitVec (len * w)},
      ¬0 < len →
        BitVec.addRecAux
            (BitVec.cast hcast (BitVec.extractLsb' ((len - 1) * w) w x ++ BitVec.extractLsb' 0 ((len - 1) * w) x)) len 0#w =
          BitVec.extractLsb' ((len - 1) * w) w x + BitVec.addRecAux (BitVec.extractLsb' 0 ((len - 1) * w) x) (len - 1) 0#w := by
  (intros; grind)
theorem HypCheckProof.BitVec.addRecAux_append_extractLsb'.h4 : ∀ {len w : Nat} {hcast : w + (len - 1) * w = len * w} {x : BitVec (len * w)},
      BitVec.addRecAux
          (BitVec.cast hcast (BitVec.extractLsb' ((len - 1) * w) w x ++ BitVec.extractLsb' 0 ((len - 1) * w) x)) len 0#w =
        BitVec.extractLsb' ((len - 1) * w) w x + BitVec.addRecAux (BitVec.extractLsb' 0 ((len - 1) * w) x) (len - 1) 0#w := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact Classical.byCases (fun hc_h => @_private.Init.Data.BitVec.Bitblast.0.BitVec.addRecAux_append_extractLsb' hc_x0 hc_x1 hc_x2 hc_x3 hc_h) (fun hc_hn => @HypCheckProof.BitVec.addRecAux_append_extractLsb'.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn)
-/

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.two_mul_add_sub_lt_of_lt_of_lt_two, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.two_mul_add_sub_lt_of_lt_of_lt_two.h3 : ¬∀ {a x y : Nat}, y < 2 → 2 * a + y - x < x := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.two_mul_add_sub_lt_of_lt_of_lt_two, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.two_mul_add_sub_lt_of_lt_of_lt_two.h4 : ¬∀ {a x y : Nat}, a < x → 2 * a + y - x < x := fun hc_h => absurd (@hc_h (0) (1) (2) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.extractLsb'_addRecAux_of_le, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.extractLsb'_addRecAux_of_le.h5 : ¬∀ {len w r k : Nat} {x : BitVec (len * w)},
        BitVec.addRecAux (BitVec.extractLsb' 0 (k * w) x) r 0#w = BitVec.addRecAux x r 0#w := fun hc_h => absurd (@hc_h (1) (1) (1) (0) (1#1)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.extractAndExtendAux_zero, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.extractAndExtendAux_zero.h5 : ¬∀ {w k len : Nat} {x : BitVec w} {acc : BitVec (k * len)}, w = k := fun hc_h => absurd (@hc_h (0) (1) (0) (0#0) (0#0)) (by
  decide +kernel)

-- _private.Init.Data.BitVec.Bitblast.0.BitVec.testBit_limit, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.BitVec.testBit_limit.h2 : ¬∀ {x i : Nat}, x.testBit i = Decidable.decide (x ≥ 2 ^ i) := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

