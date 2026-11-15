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
-- _private.Std.Data.ExtDHashMap.Lemmas.0.Std.ExtDHashMap.union_mk, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.ExtDHashMap.union_mk.h4 : Not
      (∀ {α : Type} {x : BEq α} {x_1 : Hashable α} {β : α → Type} [inst : @LawfulHashable α x x_1]
        {m₁ m₂ : @Std.DHashMap α β x x_1}, @EquivBEq α x) := fun hc_h => absurd (@hc_h (Bool) (⟨fun _ _ => false⟩ : BEq Bool) (instHashableBool) (fun (a : Bool) => Nat) (@LawfulHashable.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.false) (instHashableBool) (by (try dsimp only);   decide)) (@Std.DHashMap.ofList Bool (fun (a : Bool) => Nat) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.false) instHashableBool
      (@List.nil (@Sigma Bool fun (a : Bool) => Nat))) (@Std.DHashMap.ofList Bool (fun (a : Bool) => Nat) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.false) instHashableBool
      (@List.nil (@Sigma Bool fun (a : Bool) => Nat)))) (by
  exact fun hc_c =>
    absurd (hc_c.toReflBEq.rfl (a := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- _private.Std.Data.ExtDHashMap.Lemmas.0.Std.ExtDHashMap.union_mk, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.ExtDHashMap.union_mk.h5 : Not
      (∀ {α : Type} {x : BEq α} {x_1 : Hashable α} {β : α → Type} [inst : @EquivBEq α x] {m₁ m₂ : @Std.DHashMap α β x x_1},
        @LawfulHashable α x x_1) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (instHashableNat) (fun (a : Nat) => Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) (@Std.DHashMap.ofList Nat (fun (a : Nat) => Nat)
      (@BEq.mk Nat fun (a b : Nat) =>
        @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      instHashableNat (@List.nil (@Sigma Nat fun (a : Nat) => Nat))) (@Std.DHashMap.ofList Nat (fun (a : Nat) => Nat)
      (@BEq.mk Nat fun (a b : Nat) =>
        @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      instHashableNat (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))) (by
  exact fun hc_c =>
    absurd
      (hc_c.hash_eq (0 : Nat) (1 : Nat)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- _private.Std.Data.ExtDHashMap.Lemmas.0.Std.ExtDHashMap.Const.insertMany_list_mk, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.ExtDHashMap.Const.insertMany_list_mk.h4 : Not
      (∀ {α : Type} {x : BEq α} {x_1 : Hashable α} {β : Type} [inst : @LawfulHashable α x x_1]
        {m : @Std.DHashMap α (fun (x : α) => β) x x_1} {l : List (Prod α β)}, @EquivBEq α x) := fun hc_h => absurd (@hc_h (Bool) (⟨fun _ _ => false⟩ : BEq Bool) (instHashableBool) (Nat) (@LawfulHashable.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.false) (instHashableBool) (by (try dsimp only);   decide)) (@Std.DHashMap.ofList Bool (fun (x : Bool) => Nat) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.false) instHashableBool
      (@List.nil (@Sigma Bool fun (a : Bool) => Nat))) (@List.nil (Prod Bool Nat))) (by
  exact fun hc_c =>
    absurd (hc_c.toReflBEq.rfl (a := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- _private.Std.Data.ExtDHashMap.Lemmas.0.Std.ExtDHashMap.Const.insertMany_list_mk, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.ExtDHashMap.Const.insertMany_list_mk.h5 : Not
      (∀ {α : Type} {x : BEq α} {x_1 : Hashable α} {β : Type} [inst : @EquivBEq α x]
        {m : @Std.DHashMap α (fun (x : α) => β) x x_1} {l : List (Prod α β)}, @LawfulHashable α x x_1) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (instHashableNat) (Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) (@Std.DHashMap.ofList Nat (fun (x : Nat) => Nat)
      (@BEq.mk Nat fun (a b : Nat) =>
        @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      instHashableNat (@List.nil (@Sigma Nat fun (a : Nat) => Nat))) ([] : List (Prod Nat Nat))) (by
  exact fun hc_c =>
    absurd
      (hc_c.hash_eq (0 : Nat) (1 : Nat)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- _private.Std.Data.ExtDHashMap.Lemmas.0.Std.ExtDHashMap.insertMany_list_mk, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.ExtDHashMap.insertMany_list_mk.h5 : Not
      (∀ {α : Type} {x : BEq α} {x_1 : Hashable α} {β : α → Type} [inst : @EquivBEq α x] {m : @Std.DHashMap α β x x_1}
        {l : List (@Sigma α fun (a : α) => β a)}, @LawfulHashable α x x_1) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (instHashableNat) (fun (a : Nat) => Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) (@Std.DHashMap.ofList Nat (fun (a : Nat) => Nat)
      (@BEq.mk Nat fun (a b : Nat) =>
        @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      instHashableNat (@List.nil (@Sigma Nat fun (a : Nat) => Nat))) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by
  exact fun hc_c =>
    absurd
      (hc_c.hash_eq (0 : Nat) (1 : Nat)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- _private.Std.Data.ExtDHashMap.Lemmas.0.Std.ExtDHashMap.Const.insertManyIfNewUnit_list_mk, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.ExtDHashMap.Const.insertManyIfNewUnit_list_mk.h3 : Not
      (∀ {α : Type} {x : BEq α} {x_1 : Hashable α} [inst : @LawfulHashable α x x_1]
        {m : @Std.DHashMap α (fun (x : α) => Unit) x x_1} {l : List α}, @EquivBEq α x) := fun hc_h => absurd (@hc_h (Bool) (⟨fun _ _ => false⟩ : BEq Bool) (instHashableBool) (@LawfulHashable.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.false) (instHashableBool) (by (try dsimp only);   decide)) (@Std.DHashMap.ofList Bool (fun (x : Bool) => Unit) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.false) instHashableBool
      (@List.nil (@Sigma Bool fun (a : Bool) => Unit))) (@List.nil Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.toReflBEq.rfl (a := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- _private.Std.Data.ExtDHashMap.Lemmas.0.Std.ExtDHashMap.Const.insertManyIfNewUnit_list_mk, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.ExtDHashMap.Const.insertManyIfNewUnit_list_mk.h4 : Not
      (∀ {α : Type} {x : BEq α} {x_1 : Hashable α} [inst : @EquivBEq α x] {m : @Std.DHashMap α (fun (x : α) => Unit) x x_1}
        {l : List α}, @LawfulHashable α x x_1) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (instHashableNat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) (@Std.DHashMap.ofList Nat (fun (x : Nat) => Unit)
      (@BEq.mk Nat fun (a b : Nat) =>
        @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      instHashableNat (@List.nil (@Sigma Nat fun (a : Nat) => Unit))) (@List.nil Nat)) (by
  exact fun hc_c =>
    absurd
      (hc_c.hash_eq (0 : Nat) (1 : Nat)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

