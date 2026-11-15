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

-- Std.Internal.List.getValueCast?_insertList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast?_insertList_of_mem.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              ∀ {v : β k},
                List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
                  (⟨k, v⟩ : (a : α) × β a) ∈ toInsert → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (by
  decide) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
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

-- Std.Internal.List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem.h10 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' : α},
        (k == k') = Bool.true →
          ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertListIfNewUnit l toInsert) = Bool.true},
            Std.Internal.List.containsKey k l = Bool.false →
              k ∈ toInsert → Std.Internal.List.getKey k' (Std.Internal.List.insertListIfNewUnit l toInsert) h = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([0, 1]) (1) (1) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.Internal.List.minKeyD_eq_iff_mem_and_forall, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_eq_iff_mem_and_forall.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km fallback : α},
            Std.Internal.List.minKeyD l fallback = km ↔
              Std.Internal.List.containsKey km l = Bool.true ∧
                ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0) (0)) (by
  (simp <;> decide))

-- Std.DTreeMap.Raw.minKey!_alter_eq_self, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Raw.minKey!_alter_eq_self.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst_1 : Inhabited α],
        t.WF →
          ∀ {k : α} {f : Option (β k) → Option (β k)},
            (t.alter k f).minKey! = k ↔ (f (t.get? k)).isSome = Bool.true ∧ ∀ (k' : α), k' ∈ t → (cmp k k').isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.Raw.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instInhabitedNat) (by
  ((repeat
        (first
          | apply Std.TreeSet.Raw.WF.mk
          | apply Std.TreeMap.Raw.WF.mk
          | apply Std.DTreeMap.Raw.WF.mk));
    (first
      |
        exact
          @Std.DTreeMap.Internal.Impl.WF.insertMany _ _ (id _) _ (id _) _ _ _
            (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _)
      |
        exact
          @Std.DTreeMap.Internal.Impl.WF.constInsertMany _ (id _) _ _ (id _) _ _ _
            (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _)
      |
        exact
          @Std.DTreeMap.Internal.Impl.WF.constInsertManyIfNewUnit _ (id _) _ (id _) _ _ _
            (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _)
      | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _)))) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  simp +ground +decide [Std.DTreeMap.Raw.minKey!, Std.DTreeMap.Raw.alter, Std.DTreeMap.Raw.get?,
    Std.DTreeMap.Raw.instMembership, Std.DTreeMap.Internal.Impl.minKey!, Std.DTreeMap.Raw.inner,
    Std.DTreeMap.Internal.Impl.alter!, Std.DTreeMap.Internal.Impl.get?, Std.DTreeMap.Raw.contains,
    Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.Internal.Impl.below,
    Std.DTreeMap.Internal.Impl.brecOn.go])

-- Std.Internal.List.minKey_eraseKey_eq_iff_beq_minKey_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_eraseKey_eq_iff_beq_minKey_eq_false.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α}, (Std.Internal.List.eraseKey k l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getD_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] {l : List (α × β)} {k : α} {fallback : β},
        (List.map Prod.fst l).contains k = Bool.false →
          Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.insertMany t l) k fallback =
            Std.ExtDTreeMap.Const.getD t k fallback := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (1) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKey_modifyKey, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_modifyKey.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {k : α} {k' : α} {f : β k → β k} (l : List ((a : α) × β a)),
        Std.Internal.List.DistinctKeys l → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) (fun n => n + 1 : Nat → Nat) ([]) (by
  simp)) (by
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

-- Std.Internal.List.getKey_modifyKey, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_modifyKey.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {k k' : α} {f : β k → β k}
        (l : List ((a : α) × β a)),
        Std.Internal.List.DistinctKeys l → Std.Internal.List.containsKey k' (Std.Internal.List.modifyKey k f l) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ (0) (0) (fun n => n + 1 : Nat → Nat) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.containsKey_filter_containsKey_eq_false_of_containsKey_eq_false_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.containsKey_filter_containsKey_eq_false_of_containsKey_eq_false_right.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l₁ l₂ : List ((a : α) × β a)} {hl₁ : Std.Internal.List.DistinctKeys l₁}
        {k : α},
        Std.Internal.List.containsKey k l₂ = Bool.false →
          Std.Internal.List.containsKey k
              (List.filter (fun (p : (a : α) × β a) => Std.Internal.List.containsKey p.fst l₂) l₁) =
            Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a != b⟩ : BEq Nat) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getValueCast?_of_insertList, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast?_of_insertList.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l toInsert : List ((a : α) × β a)} {k : α},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.DistinctKeys toInsert → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([]) (0) (by
  simp) (by
  simp)) (by
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

-- Std.ExtDTreeMap.getKey!_diff_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_diff_of_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.ExtDTreeMap α β cmp} [inst : Inhabited α]
        [inst_1 : Std.TransCmp cmp] {k : α}, (t₁ \ t₂).getKey! k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (instInhabitedNat) _ (1)) (by
  decide +kernel)

-- Std.ExtTreeMap.getKey_maxKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_maxKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp], t ≠ ∅ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.Internal.List.getValueCast!_eq_default, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast!_eq_default.h7 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
        [inst_2 : Inhabited (β a)], Std.Internal.List.getValueCast! a l = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (instBEqOfDecidableEq) _ ([(⟨Bool.false, 1⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (instInhabitedNat)) (by
  decide +kernel)

-- Std.ExtDTreeMap.minKeyD_le_minKeyD_erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.minKeyD_le_minKeyD_erase.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} {k fallback : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.getValueCast_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_mem.h6 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l : List ((a : α) × β a)} {a : α},
        Std.Internal.List.containsKey a l = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) (0)) (by
  decide +kernel)

-- Std.ExtDTreeMap.le_minKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.le_minKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Internal.Impl.some_minEntry_eq_minEntry?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.some_minEntry_eq_minEntry?.h3 : ¬∀ {α : Type} {β : α → Type} {l : Std.DTreeMap.Internal.Impl α β}, l.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (Std.DTreeMap.Internal.Impl.ofList [])) (by
  decide +kernel)

