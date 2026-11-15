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
-- _private.Init.Data.Array.Lemmas.0.Array.foldl_induction.go, hypothesis 5: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldl_induction.go.h5.inst : Not
      ((fun (a b : Nat) => @LT.lt Nat instLTNat a b)
        (@Array.size Nat
          (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
        (@Array.foldlM.loop Nat Nat Id Id.instMonad
          (fun (a b : Nat) => @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b)
          (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
          (@Array.size Nat
            (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
          (Nat.le_refl
            (@Array.size Nat
              (@List.toArray Nat
                (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldl_induction.go.h5.prem0 : @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Array.size Nat
        (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))) := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldl_induction.go.h5.prem1 : @LE.le Nat instLENat
      (@Array.size Nat
        (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldl_induction.go.h5.prem2 : (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Array.foldl_induction.go.h5 : Not
      (∀ {α β : Type} {as : Array α} (motive : Nat → β → Prop) {f : β → α → β} {i j : Nat} {b : β},
        @LE.le Nat instLENat j (@Array.size α as) →
          @LE.le Nat instLENat (@Array.size α as) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i j) →
            motive j b →
              motive (@Array.size α as)
                (@Array.foldlM.loop α β Id Id.instMonad f as (@Array.size α as) (Nat.le_refl (@Array.size α as)) i j b)) := fun hc_h => HypCheckProof.Array.foldl_induction.go.h5.inst (@hc_h (Nat) (Nat) (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))) (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (fun (a b : Nat) => @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Array.foldl_induction.go.h5.prem0 HypCheckProof.Array.foldl_induction.go.h5.prem1 HypCheckProof.Array.foldl_induction.go.h5.prem2)

-- _private.Init.Data.Array.Lemmas.0.Array.foldl_induction.go, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldl_induction.go.h9 : Not
      (∀ {α β : Type} {as : Array α} (motive : Nat → β → Prop) {f : β → α → β},
        (∀ (i : Fin (@Array.size α as)) (b : β),
            motive (@Fin.val (@Array.size α as) i) b →
              motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val (@Array.size α as) i)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (f b (GetElem.getElem as i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)))) →
          ∀ {i j : Nat} {b : β},
            @LE.le Nat instLENat (@Array.size α as) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i j) →
              motive j b →
                motive (@Array.size α as) (@Array.foldlM.loop α β Id Id.instMonad f as (@Array.size α as) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) i j b)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@List.toArray Nat (@List.nil Nat)) (fun a b => a = b : Nat → Nat → Prop) (fun a b => a - b : Nat → Nat → Nat) (by
  grind) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.Array.Lemmas.0.Array.foldl_induction.go, hypothesis 10: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldl_induction.go.h10.inst : Not
      ((fun (a b : Nat) => @LT.lt Nat instLTNat a b)
        (@Array.size Nat
          (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))))
        (@Array.foldlM.loop Nat Nat Id Id.instMonad
          (fun (a b : Nat) => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a b)
          (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))
          (@Array.size Nat
            (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))))
          (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldl_induction.go.h10.prem0 : ∀
      (i :
        Fin
          (@Array.size Nat
            (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))))
      (b : Nat),
      @LT.lt Nat instLTNat
          (@Fin.val
            (@Array.size Nat
              (@List.toArray Nat
                (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))))
            i)
          b →
        (fun (a b : Nat) => @LT.lt Nat instLTNat a b)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@Fin.val
              (@Array.size Nat
                (@List.toArray Nat
                  (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))))
              i)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          ((fun (a b : Nat) => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a b) b
            (GetElem.getElem
              (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))
              i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind))) := by
  simp
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldl_induction.go.h10.prem1 : @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Array.size Nat
        (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))) := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldl_induction.go.h10.prem2 : (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Array.foldl_induction.go.h10 : Not
      (∀ {α β : Type} {as : Array α} (motive : Nat → β → Prop) {f : β → α → β},
        (∀ (i : Fin (@Array.size α as)) (b : β),
            motive (@Fin.val (@Array.size α as) i) b →
              motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val (@Array.size α as) i)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (f b (GetElem.getElem as i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)))) →
          ∀ {i j : Nat} {b : β},
            @LE.le Nat instLENat j (@Array.size α as) →
              motive j b →
                motive (@Array.size α as) (@Array.foldlM.loop α β Id Id.instMonad f as (@Array.size α as) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) i j b)) := fun hc_h => HypCheckProof.Array.foldl_induction.go.h10.inst (@hc_h (Nat) (Nat) (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))) (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (fun (a b : Nat) => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a b) HypCheckProof.Array.foldl_induction.go.h10.prem0 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Array.foldl_induction.go.h10.prem1 HypCheckProof.Array.foldl_induction.go.h10.prem2)

-- _private.Init.Data.Array.Lemmas.0.Array.foldl_induction.go, hypothesis 11: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldl_induction.go.h11 : Not
      (∀ {α β : Type} {as : Array α} (motive : Nat → β → Prop) {f : β → α → β},
        (∀ (i : Fin (@Array.size α as)) (b : β),
            motive (@Fin.val (@Array.size α as) i) b →
              motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val (@Array.size α as) i)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (f b (GetElem.getElem as i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)))) →
          ∀ {i j : Nat} {b : β},
            @LE.le Nat instLENat j (@Array.size α as) →
              @LE.le Nat instLENat (@Array.size α as) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i j) →
                motive (@Array.size α as) (@Array.foldlM.loop α β Id Id.instMonad f as (@Array.size α as) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) i j b)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@List.toArray Nat (@List.nil Nat)) (fun a b => a < b : Nat → Nat → Prop) (fun a b => a - b : Nat → Nat → Nat) (by
  grind) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Array.Lemmas.0.Array.toList_reverse.go, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Array.toList_reverse.go.h5.{u_1} : ∀ {α : Type u_1} {xs : Array α} (as : Array α) (i j : Nat),
      i + j + 1 = xs.size →
        as.size = xs.size →
          (∀ (k : Nat), as.toList[k]? = if i ≤ k ∧ k ≤ j then xs.toList[k]? else xs.toList.reverse[k]?) →
            ∀ (k : Nat), j < as.size := by
  (intros; omega)

-- _private.Init.Data.Array.Lemmas.0.Array.toList_reverse.go, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.toList_reverse.go.h8 : ¬∀ {α : Type} {xs : Array α} (as : Array α) (i j : Nat) (hj : j < as.size),
        i + j + 1 = xs.size →
          as.size = xs.size →
            ∀ (k : Nat), (Array.reverse.loop as i (⟨j, hj⟩ : Fin as.size)).toList[k]? = xs.toList.reverse[k]? := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (#[0]) (#[1]) (0) (0) hc_k0 hc_k1 hc_k2 (0)) (by
  decide +kernel)

-- _private.Init.Data.Array.Lemmas.0.Array.getElem_ofFn_go, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.getElem_ofFn_go.h6 : ¬∀ {n : Nat} {α : Type} {f : Fin n → α} {acc : Array α} {i k : Nat}, k < acc.size + i → i ≤ n := fun hc_h => absurd (@hc_h (0) (Nat) (fun (a : Fin 0) => 0) (#[]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Array.Lemmas.0.Array.getElem_ofFn_go, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.getElem_ofFn_go.h7 : ¬∀ {n : Nat} {α : Type} {f : Fin n → α} {acc : Array α} {i k : Nat}, i ≤ n → k < acc.size + i := fun hc_h => absurd (@hc_h (0) (Nat) (fun (a : Fin 0) => 0) (#[]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Array.Lemmas.0.Array.getElem_shrink_loop, hypothesis 4: necessary
/- FAILED: 2:117: expected token | 2:156: expected token | 2:117: expected token | 2:156: expected token | 2:81: expected token | 5:29: expected token | 2:81: expected token | 5:29: expected token
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.getElem_shrink_loop.h4 : ¬∀ {α : Type} {xs : Array α} {n i : Nat}, i < (Array.shrink.loop✝ n xs).size := fun hc_h => absurd (@hc_h (Nat) (#[]) (0) (0)) (by
  decide +kernel)
-/

-- _private.Init.Data.Array.Lemmas.0.Array.beq_of_beq_singleton, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.beq_of_beq_singleton.h4 : ¬∀ {α : Type} [inst : BEq α] {a b : α}, (a == b) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) (0) (1)) (by
  decide +kernel)

-- _private.Init.Data.Array.Lemmas.0.Array.foldr_induction.go, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldr_induction.go.h5 : Not
      (∀ {α β : Type} {as : Array α} (motive : Nat → β → Prop) {f : α → β → β} {i : Nat} {b : β}
        (hi : @LE.le Nat instLENat i (@Array.size α as)),
        motive i b →
          motive (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Array.foldrM.fold α β Id Id.instMonad f as (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i hi b)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))) (fun a b => a < b : Nat → Nat → Prop) (fun a b => a - b : Nat → Nat → Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) hc_k0 hc_k1) (by
  decide +kernel)

-- _private.Init.Data.Array.Lemmas.0.Array.foldr_induction.go, hypothesis 8: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldr_induction.go.h8.inst : Not
      (@LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Array.size Nat (@List.toArray Nat (@List.nil Nat)))) := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldr_induction.go.h8.prem0 : ∀ (i : Fin (@Array.size Nat (@List.toArray Nat (@List.nil Nat)))) (b : Nat),
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@Fin.val (@Array.size Nat (@List.toArray Nat (@List.nil Nat))) i)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          b →
        (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (@Fin.val (@Array.size Nat (@List.toArray Nat (@List.nil Nat))) i)
          ((fun (a b : Nat) => @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b)
            (GetElem.getElem (@List.toArray Nat (@List.nil Nat)) i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) b) := by
  grind
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.foldr_induction.go.h8.prem1 : (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Array.foldr_induction.go.h8 : Not
      (∀ {α β : Type} {as : Array α} (motive : Nat → β → Prop) {f : α → β → β},
        (∀ (i : Fin (@Array.size α as)) (b : β),
            motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val (@Array.size α as) i)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                b →
              motive (@Fin.val (@Array.size α as) i) (f (GetElem.getElem as i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) b)) →
          ∀ {i : Nat} {b : β}, motive i b → @LE.le Nat instLENat i (@Array.size α as)) := fun hc_h => HypCheckProof.Array.foldr_induction.go.h8.inst (@hc_h (Nat) (Nat) (@List.toArray Nat (@List.nil Nat)) (fun (a b : Nat) => @LT.lt Nat instLTNat a b) (fun (a b : Nat) => @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b) HypCheckProof.Array.foldr_induction.go.h8.prem0 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) HypCheckProof.Array.foldr_induction.go.h8.prem1)

-- _private.Init.Data.Array.Lemmas.0.Array.foldr_induction.go, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldr_induction.go.h9 : Not
      (∀ {α β : Type} {as : Array α} (motive : Nat → β → Prop) {f : α → β → β},
        (∀ (i : Fin (@Array.size α as)) (b : β),
            motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val (@Array.size α as) i)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                b →
              motive (@Fin.val (@Array.size α as) i) (f (GetElem.getElem as i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) b)) →
          ∀ {i : Nat} {b : β} (hi : @LE.le Nat instLENat i (@Array.size α as)),
            motive (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@Array.foldrM.fold α β Id Id.instMonad f as (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i hi
                b)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Bool) (@List.toArray Nat (@List.nil Nat)) (fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (fun (a : Nat) => Bool.not) hc_k0 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Bool.false) hc_k1) (by
  decide +kernel)

-- _private.Init.Data.Array.Lemmas.0.Array.mapM_eq_foldlM.aux, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.mapM_eq_foldlM.aux.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {f : α → m β} {xs : Array α} (i : Nat) (bs : Array β),
        Array.mapM.map f xs i bs = List.foldlM (fun (bs : Array β) (a : α) => bs.push <$> f a) bs (List.drop i xs.toList) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, 0)) (#[0]) (0) (#[])) (by
  decide +kernel)

-- _private.Init.Data.Array.Lemmas.0.Array.size_ofFn_go, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.size_ofFn_go.h5 : ¬∀ {α : Type} {n : Nat} {f : Fin n → α} {i : Nat} {acc : Array α}, i ≤ n := fun hc_h => absurd (@hc_h (Nat) (0) (fun (a : Fin 0) => 0) (1) (#[])) (by
  decide +kernel)

