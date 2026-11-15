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
-- _private.Init.Data.Range.Polymorphic.Lemmas.0.Std.eq_of_pairwise_lt_of_mem_iff_mem, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.eq_of_pairwise_lt_of_mem_iff_mem.h2 : ¬∀ {α : Type} {lt : α → α → Prop} {l l' : List α},
        List.Pairwise lt l → List.Pairwise lt l' → (∀ (a : α), a ∈ l ↔ a ∈ l') → l = l' := fun hc_h => absurd (@hc_h (Nat) (fun a b => a ≤ b : Nat → Nat → Prop) ([0]) ([0, 0]) (by
  decide) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- _private.Init.Data.Range.Polymorphic.Lemmas.0.Std.eq_of_pairwise_lt_of_mem_iff_mem, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.eq_of_pairwise_lt_of_mem_iff_mem.h5 : ¬∀ {α : Type} {lt : α → α → Prop} [asymm : Std.Asymm lt] {l l' : List α},
        List.Pairwise lt l' → (∀ (a : α), a ∈ l ↔ a ∈ l') → l = l' := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) _ ([0, 0]) ([0]) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- _private.Init.Data.Range.Polymorphic.Lemmas.0.Std.eq_of_pairwise_lt_of_mem_iff_mem, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.eq_of_pairwise_lt_of_mem_iff_mem.h6 : ¬∀ {α : Type} {lt : α → α → Prop} [asymm : Std.Asymm lt] {l l' : List α},
        List.Pairwise lt l → (∀ (a : α), a ∈ l ↔ a ∈ l') → l = l' := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) _ ([0]) ([0, 0]) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- _private.Init.Data.Range.Polymorphic.Lemmas.0.Std.eq_of_pairwise_lt_of_mem_iff_mem, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.eq_of_pairwise_lt_of_mem_iff_mem.h7 : ¬∀ {α : Type} {lt : α → α → Prop} [asymm : Std.Asymm lt] {l l' : List α},
        List.Pairwise lt l → List.Pairwise lt l' → l = l' := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) _ ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Range.Polymorphic.Lemmas.0.Std.Internal.iter_roc_eq_iter_rcc_of_isSome_succ?, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Internal.iter_roc_eq_iter_rcc_of_isSome_succ?.h6 : ¬∀ {α : Type} [inst : LE α] [inst : Std.PRange.UpwardEnumerable α] [inst_1 : Std.PRange.LawfulUpwardEnumerable α]
        {lo : α} {hi : α}, (Std.PRange.UpwardEnumerable.succ? lo).isSome = Bool.true := fun hc_h => absurd (@hc_h (Fin 2 : Type) (instLEFin) (Fin.instUpwardEnumerable) _ ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- _private.Init.Data.Range.Polymorphic.Lemmas.0.Std.Internal.iter_roo_eq_iter_rco_of_isSome_succ?, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Internal.iter_roo_eq_iter_rco_of_isSome_succ?.h6 : ¬∀ {α : Type} [inst : LT α] [inst : Std.PRange.UpwardEnumerable α] [inst_1 : Std.PRange.LawfulUpwardEnumerable α]
        {lo : α} {hi : α}, (Std.PRange.UpwardEnumerable.succ? lo).isSome = Bool.true := fun hc_h => absurd (@hc_h (Fin 2 : Type) (instLTFin) (Fin.instUpwardEnumerable) _ ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- _private.Init.Data.Range.Polymorphic.Lemmas.0.Std.Internal.iter_roi_eq_iter_rci_of_isSome_succ?, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Internal.iter_roi_eq_iter_rci_of_isSome_succ?.h4 : ¬∀ {α : Type} [inst : Std.PRange.UpwardEnumerable α] [inst_1 : Std.PRange.LawfulUpwardEnumerable α] {lo : α},
        (Std.PRange.UpwardEnumerable.succ? lo).isSome = Bool.true := fun hc_h => absurd (@hc_h (Fin 2 : Type) (Fin.instUpwardEnumerable) _ ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

