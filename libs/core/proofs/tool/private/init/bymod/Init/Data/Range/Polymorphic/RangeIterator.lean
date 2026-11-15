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
-- _private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.Rxo.List.length_filter_strict_mono, hypothesis 6: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h6.inst : ¬(List.filter (fun (n : Nat) => n % 2 == 0) []).length < (List.filter (fun (x : Nat) => Bool.true) []).length := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h6.prem0 : ∀ (a : Nat), (fun (n : Nat) => n % 2 == 0) a = Bool.true → (fun (x : Nat) => Bool.true) a = Bool.true := by
  simp
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h6.prem1 : ¬(fun (n : Nat) => n % 2 == 0) 1 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h6.prem2 : (fun (x : Nat) => Bool.true) 1 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h6 : ¬∀ {α : Type} {l : List α} {P Q : α → Bool} {a : α},
        (∀ (a : α), P a = Bool.true → Q a = Bool.true) →
          ¬P a = Bool.true → Q a = Bool.true → (List.filter P l).length < (List.filter Q l).length := fun hc_h => HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h6.inst (@hc_h (Nat) ([]) (fun (n : Nat) => n % 2 == 0) (fun (x : Nat) => Bool.true) (1) HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h6.prem0 HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h6.prem1 HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h6.prem2)

-- _private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.Rxo.List.length_filter_strict_mono, hypothesis 7: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h7.inst : ¬(List.filter (fun (n : Nat) => n % 2 == 0) [0]).length < (List.filter (fun (n : Nat) => n % 2 == 0) [0]).length := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h7.prem0 : ∀ (a : Nat), (fun (n : Nat) => n % 2 == 0) a = Bool.true → (fun (n : Nat) => n % 2 == 0) a = Bool.true := by
  simp
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h7.prem1 : 0 ∈ [0] := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h7.prem2 : (fun (n : Nat) => n % 2 == 0) 0 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h7 : ¬∀ {α : Type} {l : List α} {P Q : α → Bool} {a : α},
        (∀ (a : α), P a = Bool.true → Q a = Bool.true) →
          a ∈ l → Q a = Bool.true → (List.filter P l).length < (List.filter Q l).length := fun hc_h => HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h7.inst (@hc_h (Nat) ([0]) (fun (n : Nat) => n % 2 == 0) (fun (n : Nat) => n % 2 == 0) (0) HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h7.prem0 HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h7.prem1 HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h7.prem2)

-- _private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.Rxo.List.length_filter_strict_mono, hypothesis 8: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h8.inst : ¬(List.filter (fun (n : Nat) => n % 2 == 0) [1]).length < (List.filter (fun (n : Nat) => n % 2 == 0) [1]).length := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h8.prem0 : ∀ (a : Nat), (fun (n : Nat) => n % 2 == 0) a = Bool.true → (fun (n : Nat) => n % 2 == 0) a = Bool.true := by
  simp
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h8.prem1 : 1 ∈ [1] := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h8.prem2 : ¬(fun (n : Nat) => n % 2 == 0) 1 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h8 : ¬∀ {α : Type} {l : List α} {P Q : α → Bool} {a : α},
        (∀ (a : α), P a = Bool.true → Q a = Bool.true) →
          a ∈ l → ¬P a = Bool.true → (List.filter P l).length < (List.filter Q l).length := fun hc_h => HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h8.inst (@hc_h (Nat) ([1]) (fun (n : Nat) => n % 2 == 0) (fun (n : Nat) => n % 2 == 0) (1) HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h8.prem0 HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h8.prem1 HypCheckProof.Std.Rxo.List.length_filter_strict_mono.h8.prem2)

-- _private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.Rxo.List.Sublist.filter_mono, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Rxo.List.Sublist.filter_mono.h4 : ¬∀ {α : Type} {l : List α} {P Q : α → Bool}, (List.filter P l).Sublist (List.filter Q l) := fun hc_h => absurd (@hc_h (Nat) ([0]) (fun n => n % 2 == 0 : Nat → Bool) (fun _ => false : Nat → Bool)) (by
  decide +kernel)

-- _private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.Rxc.List.length_filter_strict_mono, hypothesis 6: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h6.inst : ¬(List.filter (fun (n : Nat) => n % 2 == 0) []).length < (List.filter (fun (x : Nat) => Bool.true) []).length := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h6.prem0 : ∀ (a : Nat), (fun (n : Nat) => n % 2 == 0) a = Bool.true → (fun (x : Nat) => Bool.true) a = Bool.true := by
  simp
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h6.prem1 : ¬(fun (n : Nat) => n % 2 == 0) 1 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h6.prem2 : (fun (x : Nat) => Bool.true) 1 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h6 : ¬∀ {α : Type} {l : List α} {P Q : α → Bool} {a : α},
        (∀ (a : α), P a = Bool.true → Q a = Bool.true) →
          ¬P a = Bool.true → Q a = Bool.true → (List.filter P l).length < (List.filter Q l).length := fun hc_h => HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h6.inst (@hc_h (Nat) ([]) (fun (n : Nat) => n % 2 == 0) (fun (x : Nat) => Bool.true) (1) HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h6.prem0 HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h6.prem1 HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h6.prem2)

-- _private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.Rxc.List.length_filter_strict_mono, hypothesis 7: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h7.inst : ¬(List.filter (fun (n : Nat) => n % 2 == 0) [0]).length < (List.filter (fun (n : Nat) => n % 2 == 0) [0]).length := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h7.prem0 : ∀ (a : Nat), (fun (n : Nat) => n % 2 == 0) a = Bool.true → (fun (n : Nat) => n % 2 == 0) a = Bool.true := by
  simp
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h7.prem1 : 0 ∈ [0] := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h7.prem2 : (fun (n : Nat) => n % 2 == 0) 0 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h7 : ¬∀ {α : Type} {l : List α} {P Q : α → Bool} {a : α},
        (∀ (a : α), P a = Bool.true → Q a = Bool.true) →
          a ∈ l → Q a = Bool.true → (List.filter P l).length < (List.filter Q l).length := fun hc_h => HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h7.inst (@hc_h (Nat) ([0]) (fun (n : Nat) => n % 2 == 0) (fun (n : Nat) => n % 2 == 0) (0) HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h7.prem0 HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h7.prem1 HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h7.prem2)

-- _private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.Rxc.List.length_filter_strict_mono, hypothesis 8: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h8.inst : ¬(List.filter (fun (n : Nat) => n % 2 == 0) [1]).length < (List.filter (fun (n : Nat) => n % 2 == 0) [1]).length := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h8.prem0 : ∀ (a : Nat), (fun (n : Nat) => n % 2 == 0) a = Bool.true → (fun (n : Nat) => n % 2 == 0) a = Bool.true := by
  simp
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h8.prem1 : 1 ∈ [1] := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h8.prem2 : ¬(fun (n : Nat) => n % 2 == 0) 1 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h8 : ¬∀ {α : Type} {l : List α} {P Q : α → Bool} {a : α},
        (∀ (a : α), P a = Bool.true → Q a = Bool.true) →
          a ∈ l → ¬P a = Bool.true → (List.filter P l).length < (List.filter Q l).length := fun hc_h => HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h8.inst (@hc_h (Nat) ([1]) (fun (n : Nat) => n % 2 == 0) (fun (n : Nat) => n % 2 == 0) (1) HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h8.prem0 HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h8.prem1 HypCheckProof.Std.Rxc.List.length_filter_strict_mono.h8.prem2)

-- _private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.Rxc.List.Sublist.filter_mono, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Rxc.List.Sublist.filter_mono.h4 : ¬∀ {α : Type} {l : List α} {P Q : α → Bool}, (List.filter P l).Sublist (List.filter Q l) := fun hc_h => absurd (@hc_h (Nat) ([0]) (fun n => n % 2 == 0 : Nat → Bool) (fun _ => false : Nat → Bool)) (by
  decide +kernel)

