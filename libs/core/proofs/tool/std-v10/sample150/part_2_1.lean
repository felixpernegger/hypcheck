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

-- Std.ExtTreeMap.getD_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h11.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0), (0, 1)]).getD 0 0 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h11.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h11 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α}, cmp k k' = Ordering.eq → ∀ {v fallback : β}, (k, v) ∈ l → (t.insertMany l).getD k' fallback = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h11.prem0 (0) (0) HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h11.prem1)

-- Std.DTreeMap.Internal.Impl.Const.get!_insertMany!_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.Const.get!_insertMany!_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {instOrd : Ord α} {β : Type} {t : Std.DTreeMap.Internal.Impl α fun (x : α) => β} [inst : Std.TransOrd α]
        [inst : BEq α] [inst_1 : Inhabited β],
        t.WF →
          ∀ {l : List (α × β)} {k : α},
            (List.map Prod.fst l).contains k = Bool.false →
              Std.DTreeMap.Internal.Impl.Const.get! (Std.DTreeMap.Internal.Impl.Const.insertMany! t l).val k =
                Std.DTreeMap.Internal.Impl.Const.get! t k := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) (Nat) (Std.DTreeMap.Internal.Impl.ofList []) _ (⟨fun a b => a != b⟩ : BEq Nat) (instInhabitedNat) (by
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
      | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _)))) ([(0, 1)]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.mem_of_mem_insertMany_list, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.mem_of_mem_insertMany_list.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getEntry?_insertList_of_contains_eq_true, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getEntry?_insertList_of_contains_eq_true.h9 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @EquivBEq α inst]
        {l toInsert : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Std.Internal.List.DistinctKeys α β inst l →
          @List.Pairwise (@Sigma α fun (a : α) => β a)
              (fun (a b : @Sigma α fun (a : α) => β a) =>
                @Eq Bool (@BEq.beq α inst (@Sigma.fst α (fun (a : α) => β a) a) (@Sigma.fst α (fun (a : α) => β a) b))
                  Bool.false)
              toInsert →
            @Eq (Option (@Sigma α fun (a : α) => β a))
              (@Std.Internal.List.getEntry? α β inst k (@Std.Internal.List.insertList α β inst l toInsert))
              (@Std.Internal.List.getEntry? α β inst k toInsert)) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKey_of_perm, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_of_perm.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : PartialEquivBEq α] {l l' : List ((a : α) × β a)} {a : α}
        {h' : Std.Internal.List.containsKey a l = Bool.true}, Std.Internal.List.DistinctKeys l → l.Perm l' := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([]) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.getValueCast_filter_not_contains, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_filter_not_contains.h8 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ : List ((a : α) × β a)} {l₂ : List α} {k : α},
        Std.Internal.List.DistinctKeys l₁ →
          ∀ {h₂ : Std.Internal.List.containsKey k l₁ = Bool.true},
            Std.Internal.List.containsKey k (List.filter (fun (p : (a : α) × β a) => !l₂.contains p.fst) l₁) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([0]) (0) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.maxKey?_le_maxKey?_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.maxKey?_le_maxKey?_insert.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} {k : α} {v : β k} {km kmi : α},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.minKey!_alter_eq_self, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.minKey!_alter_eq_self.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Std.LawfulEqCmp cmp] [inst_2 : Inhabited α] {k : α} {f : Option (β k) → Option (β k)},
        (t.alter k f).minKey! = k ↔ (f (t.get? k)).isSome = Bool.true ∧ ∀ (k' : α), k' ∈ t → (cmp k k').isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instInhabitedNat) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  simp +ground +decide [Std.ExtDTreeMap.minKey!, Std.ExtDTreeMap.alter, Std.ExtDTreeMap.get?,
    Std.ExtDTreeMap.instMembershipOfTransCmp, Std.ExtDTreeMap.lift, Std.DTreeMap.minKey!, Std.ExtDTreeMap.mk,
    Std.DTreeMap.alter, Std.DTreeMap.get?, Std.ExtDTreeMap.contains, Std.DTreeMap.isSetoid, Std.ExtDTreeMap.inner,
    Std.DTreeMap.Internal.Impl.minKey!, Std.DTreeMap.inner, Std.DTreeMap.Internal.Impl.SizedBalancedTree.impl,
    Std.DTreeMap.Internal.Impl.size, Std.DTreeMap.Internal.Impl.alter, Std.DTreeMap.Internal.Impl.get?,
    Std.DTreeMap.contains, Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.contains])

-- Std.ExtDTreeMap.Const.size_insertManyIfNewUnit_list, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.size_insertManyIfNewUnit_list.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.size_insertManyIfNewUnit_list.h3.prem0 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.size_insertManyIfNewUnit_list.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] {l : List α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.size_insertManyIfNewUnit_list.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([]) HypCheckProof.Std.ExtDTreeMap.Const.size_insertManyIfNewUnit_list.h3.prem0)

-- Std.ExtDTreeMap.getD_inter_of_not_mem_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_inter_of_not_mem_left.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.ExtDTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        {k : α} {fallback : β k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get!_diff_of_not_mem_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_diff_of_not_mem_left.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.ExtDTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        {k : α} [inst : Inhabited (β k)], Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (instInhabitedNat)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.Raw.getElem_alter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Raw.getElem_alter.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp},
        t.WF → ∀ {k k' : α} {f : Option β → Option β} {hc : k' ∈ t.alter k f}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.Raw.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (by
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
      | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _)))) (0) (0) (fun (a : Option Nat) => Option.some 0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.Raw.getKey_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Raw.getKey_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap.Raw α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp], t.WF → ∀ {k : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.Raw.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (by
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
      | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _)))) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Internal.Impl.minKey_eq_minKey, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.minKey_eq_minKey.h8 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : Std.DTreeMap.Internal.Impl α β}, l.Ordered → l.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (Std.DTreeMap.Internal.Impl.ofList []) (by
  simp_all +ground +decide [Std.DTreeMap.Internal.Impl.isEmpty])) (by
  decide +kernel)

-- Std.ExtTreeMap.getKey_maxKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_maxKey?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} {km : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtTreeMap.getD_diff_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getD_diff_of_mem_right.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {fallback : β}, (t₁ \ t₂).getD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtTreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.get_modify, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_modify.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} {k k' : α} {f : β → β},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (fun n => n + 1 : Nat → Nat)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtTreeMap.mem_insertManyIfNewUnit_list, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.mem_insertManyIfNewUnit_list.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List α} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([]) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.Const.maxKey_alter_eq_self, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.maxKey_alter_eq_self.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {f : Option β → Option β}, Std.ExtDTreeMap.Const.alter t k f ≠ ∅ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

-- Std.Internal.List.isEmpty_filter_not_contains_map_fst_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.isEmpty_filter_not_contains_map_fst_left.h6 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l₁ l₂ : List ((a : α) × β a)},
        (List.filter (fun (p : (a : α) × β a) => !(List.map Sigma.fst l₂).contains p.fst) l₁).isEmpty = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([])) (by
  decide +kernel)

-- Std.ExtTreeSet.get!_eq_default, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeSet.get!_eq_default.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Inhabited α] {a : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Internal.Impl.getEntryGE?_eq_find?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Internal.Impl.getEntryGE?_eq_find?.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] {t : Std.DTreeMap.Internal.Impl α β},
        t.Ordered →
          ∀ {k : α},
            Std.DTreeMap.Internal.Impl.getEntryGE? k t =
              List.find? (fun (e : (a : α) × β a) => (Ord.compare e.fst k).isGE) t.toListModel := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (Std.DTreeMap.Internal.Impl.inner 2 0 0 Std.DTreeMap.Internal.Impl.leaf Std.DTreeMap.Internal.Impl.leaf) (by
  simp_all +ground +decide [Std.DTreeMap.Internal.Impl.getEntryGE?, Std.DTreeMap.Internal.Impl.toListModel,
    Std.DTreeMap.Internal.Impl.getEntryGE?.go, Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.below,
    Std.DTreeMap.Internal.Impl.brecOn.go]) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Raw.Const.size_unitOfList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Raw.Const.size_unitOfList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α},
        (Std.DTreeMap.Raw.Const.unitOfList l cmp).size = l.length := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true])) (by
  decide +kernel)

-- Std.ExtTreeMap.getKey?_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_filterMap.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} {f : α → β → Option γ} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun (a x : Nat) => Option.none) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Tactic.BVDecide.LRAT.Internal.State.get?_add_one_of_getElem_eq_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Tactic.BVDecide.LRAT.Internal.State.get?_add_one_of_getElem_eq_some.h4 : Not
      (∀ {c : Std.Sat.CNF.Clause Nat} {s : Std.Tactic.BVDecide.LRAT.Internal.State} {i : Nat},
        @LT.lt Nat instLTNat i (@Array.size (Option (Std.Sat.CNF.Clause Nat)) s.formula) →
          @Eq (Option (Std.Sat.CNF.Clause Nat))
            (s.get?
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some (Std.Sat.CNF.Clause Nat) c)) := fun hc_h => absurd (@hc_h (@Std.Sat.CNF.Clause.mk Nat (@List.toArray Nat (@List.nil Nat))
      { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }
      (@of_decide_eq_true
        (@Eq Nat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
          (@Array.size Nat (@List.toArray Nat (@List.nil Nat))))
        (instDecidableEqNat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
          (@Array.size Nat (@List.toArray Nat (@List.nil Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Eq Nat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                (@Array.size Nat (@List.toArray Nat (@List.nil Nat))))
              (instDecidableEqNat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                (@Array.size Nat (@List.toArray Nat (@List.nil Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ (i : Nat) (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size),
          Or
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
        (@Nat.decidableBallLT { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
          (fun (i : Nat) (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
            Or
              (@Eq UInt8
                (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                  ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
              (@Eq UInt8
                (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                  ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
          fun (n : Nat) (h : @LT.lt Nat instLTNat n { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
          @instDecidableOr
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (instDecidableEqUInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
            (instDecidableEqUInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ (i : Nat) (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size),
                Or
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                    (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                    (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
              (@Nat.decidableBallLT { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                (fun (i : Nat)
                    (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
                  Or
                    (@Eq UInt8
                      (@GetElem.getElem ByteArray Nat UInt8
                        (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                        ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i
                        h)
                      (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                    (@Eq UInt8
                      (@GetElem.getElem ByteArray Nat UInt8
                        (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                        ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i
                        h)
                      (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
                fun (n : Nat)
                  (h : @LT.lt Nat instLTNat n { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
                @instDecidableOr
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                    (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                    (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
                  (instDecidableEqUInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                    (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                  (instDecidableEqUInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                    (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ({
      formula :=
        @List.toArray (Option (Std.Sat.CNF.Clause Nat))
          (@List.cons (Option (Std.Sat.CNF.Clause Nat)) (@Option.none (Std.Sat.CNF.Clause Nat))
            (@List.nil (Option (Std.Sat.CNF.Clause Nat)))) :
      Std.Tactic.BVDecide.LRAT.Internal.State }) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getEntry?_replaceEntry_of_containsKey_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getEntry?_replaceEntry_of_containsKey_eq_false.h7 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l : List ((a : α) × β a)} {a k : α} {v : β k},
        Std.Internal.List.getEntry? a (Std.Internal.List.replaceEntry k v l) = Std.Internal.List.getEntry? a l := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (1)) (by
  decide +kernel)

-- Std.ExtDTreeMap.insertIfNew_ne_empty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.insertIfNew_ne_empty.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} {k : α} {v : β k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.replaceEntry_of_containsKey_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.replaceEntry_of_containsKey_eq_false.h6 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k},
        Std.Internal.List.replaceEntry k v l = l := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1)) (by
  decide +kernel)

-- Std.Internal.List.containsKey_insertListIfNew, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.containsKey_insertListIfNew.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l toInsert : List ((a : α) × β a)} {k : α},
        Std.Internal.List.containsKey k (Std.Internal.List.insertListIfNew l toInsert) =
          (Std.Internal.List.containsKey k l || (List.map Sigma.fst toInsert).contains k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (1)) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKey!_empty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_empty.h3 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {a : α} [inst : Inhabited α], Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (0) (instInhabitedNat)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

