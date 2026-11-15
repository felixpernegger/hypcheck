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

-- Std.Internal.List.getValue_insertListConst_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue_insertListConst_of_mem.h11 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              ∀ {v : β},
                (k, v) ∈ toInsert →
                  ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertListConst l toInsert) = Bool.true},
                    Std.Internal.List.getValue k' (Std.Internal.List.insertListConst l toInsert) h = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([(0, 0), (0, 1)]) hc_k0 _ (0) (beq_self_eq_true _) (0) hc_k1 hc_k2) (by
  (simp <;> decide))

-- Std.Internal.List.getValue_insertListConst_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue_insertListConst_of_mem.h12 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              ∀ {v : β},
                List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
                  ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertListConst l toInsert) = Bool.true},
                    Std.Internal.List.getValue k' (Std.Internal.List.insertListConst l toInsert) h = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([(0, 0)]) hc_k0 _ (0) (beq_self_eq_true _) (1) hc_k1 hc_k2) (by
  (simp <;> decide))

-- Std.ExtDTreeMap.get_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get_insertMany_list_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_insertMany_list_of_mem.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → ∀ {h' : k' ∈ t.insertMany l}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtDTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_compare (a := (Bool.false : Bool)) (b := (Bool.true : Bool))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α} {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → ∀ {h' : k' ∈ t.insertMany l}, cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.get_insertMany_list_of_mem, hypothesis 12: necessary
/- FAILED: 10:56: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 40:18: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    α | 7:180: `grind` has failed, use `+verbose` to obtain diagnostic information | 32:140: `grind` has failed, use `+verbose` to obtain diagnostic information | 18:56: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = Nat | 77:18: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 22:180: `grind` has failed, use `+verbose` to obtain diagnostic information | 99:140: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_insertMany_list_of_mem.h12 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          ∀ {h' : k' ∈ t.insertMany l},
            (t.insertMany l).get k' h' =
              cast
                ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                      (k_eq : cmp k k' = Ordering.eq) =>
                    (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k'
                      (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                  k_eq)
                v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) hc_k0 (1) hc_k1 hc_k2) (by
  decide +kernel)
-/

-- Std.Internal.List.getValue!_insertListConst_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue!_insertListConst_of_mem.h11 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited β] {l : List ((_ : α) × β)}
        {toInsert : List (α × β)} {k k' : α} {v : β},
        Std.Internal.List.DistinctKeys l →
          List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
            (k, v) ∈ toInsert → Std.Internal.List.getValue! k' (Std.Internal.List.insertListConst l toInsert) = v := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) ([(0, 1)]) (0) (1) (1) (by
  simp) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getValue!_insertListConst_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue!_insertListConst_of_mem.h12 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited β] {l : List ((_ : α) × β)}
        {toInsert : List (α × β)} {k k' : α} {v : β},
        Std.Internal.List.DistinctKeys l →
          (k == k') = Bool.true →
            (k, v) ∈ toInsert → Std.Internal.List.getValue! k' (Std.Internal.List.insertListConst l toInsert) = v := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) ([(0, 0), (0, 1)]) _ (0) (0) (by
  simp) (beq_self_eq_true _) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getValue!_insertListConst_of_mem, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue!_insertListConst_of_mem.h13 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited β] {l : List ((_ : α) × β)}
        {toInsert : List (α × β)} {k k' : α} {v : β},
        Std.Internal.List.DistinctKeys l →
          (k == k') = Bool.true →
            List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
              Std.Internal.List.getValue! k' (Std.Internal.List.insertListConst l toInsert) = v := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) ([]) _ (0) (1) (by
  simp) (beq_self_eq_true _) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.minKey?_insertEntry_le_minKey?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_le_minKey?.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {v : β k}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km : α} {kmi : α}, Std.Internal.List.minKey? l = Option.some km → Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey?_insertEntry_le_minKey?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_le_minKey?.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {v : β k}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km : α} {kmi : α}, Std.Internal.List.minKey? l = Option.some km → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey?_insertEntry_le_minKey?, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_le_minKey?.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)} (hl : Std.Internal.List.DistinctKeys l) {km kmi : α},
        (Std.Internal.List.minKey? (Std.Internal.List.insertEntry k v l)).get
              (Std.Internal.List.isSome_minKey?_insertEntry hl) =
            kmi →
          (Ord.compare kmi km).isLE = Bool.true := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (1) (0) ([]) hc_k0 (0) (1) hc_k1) (by
  (simp <;> decide))

-- Std.Internal.List.minKey?_insertEntry_le_minKey?, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_le_minKey?.h13 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km kmi : α}, Std.Internal.List.minKey? l = Option.some km → (Ord.compare kmi km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.maxKey?_le_maxKey?_insertEntryIfNew, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_maxKey?_insertEntryIfNew.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {v : β k}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km : α} {kmi : α}, Std.Internal.List.maxKey? l = Option.some km → Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey?_le_maxKey?_insertEntryIfNew, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_maxKey?_insertEntryIfNew.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {v : β k}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km : α} {kmi : α}, Std.Internal.List.maxKey? l = Option.some km → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey?_le_maxKey?_insertEntryIfNew, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_maxKey?_insertEntryIfNew.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)} (hd : Std.Internal.List.DistinctKeys l) {km kmi : α},
        (Std.Internal.List.maxKey? (Std.Internal.List.insertEntryIfNew k v l)).get
              (Std.Internal.List.isSome_maxKey?_insertEntryIfNew hd) =
            kmi →
          (Ord.compare km kmi).isLE = Bool.true := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) ([]) hc_k0 (1) (0) hc_k1) (by
  (simp <;> decide))

-- Std.Internal.List.maxKey?_le_maxKey?_insertEntryIfNew, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_maxKey?_insertEntryIfNew.h13 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km kmi : α}, Std.Internal.List.maxKey? l = Option.some km → (Ord.compare km kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getValueD_insertListConst_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueD_insertListConst_of_mem.h11 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k k' : α}
        {v fallback : β},
        Std.Internal.List.DistinctKeys l →
          List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
            (k, v) ∈ toInsert → Std.Internal.List.getValueD k' (Std.Internal.List.insertListConst l toInsert) fallback = v := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([(0, 0)]) (0) (1) (0) (1) (by
  simp) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getValueD_insertListConst_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueD_insertListConst_of_mem.h12 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k k' : α}
        {v fallback : β},
        Std.Internal.List.DistinctKeys l →
          (k == k') = Bool.true →
            (k, v) ∈ toInsert → Std.Internal.List.getValueD k' (Std.Internal.List.insertListConst l toInsert) fallback = v := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([(0, 0), (0, 1)]) _ (0) (0) (0) (by
  simp) (beq_self_eq_true _) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getValueD_insertListConst_of_mem, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueD_insertListConst_of_mem.h13 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k k' : α}
        {v fallback : β},
        Std.Internal.List.DistinctKeys l →
          (k == k') = Bool.true →
            List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
              Std.Internal.List.getValueD k' (Std.Internal.List.insertListConst l toInsert) fallback = v := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([]) _ (0) (0) (1) (by
  simp) (beq_self_eq_true _) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.Const.maxKey?_modifyKey_beq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey?_modifyKey_beq.h3 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {f : β → β} {km : α} {kmm : α}
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.maxKey? l = Option.some km → Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (fun n => n + 1 : Nat → Nat) (0) (0) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) (by
  simp) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.Const.maxKey?_modifyKey_beq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey?_modifyKey_beq.h5 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {f : β → β} {km : α} {kmm : α}
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.maxKey? l = Option.some km → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (fun n => n + 1 : Nat → Nat) (0) (0) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.Const.maxKey?_modifyKey_beq, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey?_modifyKey_beq.h12 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α] {k : α}
        {f : β → β} {km : α} {kmm : α} {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.maxKey? l = Option.some km := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (fun n => n + 1 : Nat → Nat) (0) (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.Const.maxKey?_modifyKey_beq, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey?_modifyKey_beq.h13 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α] {k : α}
        {f : β → β} {km kmm : α} {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.maxKey? l = Option.some km → (kmm == km) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (fun n => n + 1 : Nat → Nat) (0) (1) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.insertList_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.insertList_congr.h8 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @EquivBEq α inst]
        {l1 l2 l3 l4 : List (@Sigma α fun (a : α) => β a)},
        @List.Perm (@Sigma α fun (a : α) => β a) l2 l4 →
          @Std.Internal.List.DistinctKeys α β inst l1 →
            @Std.Internal.List.DistinctKeys α β inst l2 →
              @Std.Internal.List.DistinctKeys α β inst l3 →
                @List.Perm (@Sigma α fun (a : α) => β a) (@Std.Internal.List.insertList α β inst l1 l2)
                  (@Std.Internal.List.insertList α β inst l3 l4)) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.insertList_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.insertList_congr.h9 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @EquivBEq α inst]
        {l1 l2 l3 l4 : List (@Sigma α fun (a : α) => β a)},
        @List.Perm (@Sigma α fun (a : α) => β a) l1 l3 →
          @Std.Internal.List.DistinctKeys α β inst l1 →
            @Std.Internal.List.DistinctKeys α β inst l2 →
              @Std.Internal.List.DistinctKeys α β inst l3 →
                @List.Perm (@Sigma α fun (a : α) => β a) (@Std.Internal.List.insertList α β inst l1 l2)
                  (@Std.Internal.List.insertList α β inst l3 l4)) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Std.ExtDTreeMap.get_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_ofList_of_mem.h3 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get_ofList_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_ofList_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → ∀ {h : k' ∈ Std.ExtDTreeMap.ofList l cmp}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_compare (a := (Bool.false : Bool)) (b := (Bool.true : Bool))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst_1 : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → ∀ {h : k' ∈ Std.ExtDTreeMap.ofList l cmp}, cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.get_ofList_of_mem, hypothesis 11: necessary
/- FAILED: 10:56: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 25:18: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    α | 7:206: `grind` has failed, use `+verbose` to obtain diagnostic information | 18:140: `grind` has failed, use `+verbose` to obtain diagnostic information | 18:56: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = Nat | 57:18: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 22:206: `grind` has failed, use `+verbose` to obtain diagnostic information | 65:140: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_ofList_of_mem.h11 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst_1 : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          ∀ {h : k' ∈ Std.ExtDTreeMap.ofList l cmp},
            (Std.ExtDTreeMap.ofList l cmp).get k' h =
              cast
                ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                      (k_eq : cmp k k' = Ordering.eq) =>
                    (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k'
                      (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                  k_eq)
                v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) hc_k0 (1) hc_k1 hc_k2) (by
  decide +kernel)
-/

-- Std.Internal.List.getKey_insertList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              k ∈ List.map Sigma.fst toInsert →
                ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertList l toInsert) = Bool.true},
                  Std.Internal.List.getKey k' (Std.Internal.List.insertList l toInsert) h = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) hc_k0 (0) (1) hc_k1 hc_k2 hc_k3) (by
  (simp <;> decide))

-- Std.Internal.List.getKey_insertList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_mem.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              k ∈ List.map Sigma.fst toInsert →
                ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertList l toInsert) = Bool.true},
                  Std.Internal.List.getKey k' (Std.Internal.List.insertList l toInsert) h = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) hc_k0 (0) (0) hc_k1 hc_k2 hc_k3) (by
  (simp <;> decide))

-- Std.Internal.List.getKey_insertList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_mem.h11 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
                ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertList l toInsert) = Bool.true},
                  Std.Internal.List.getKey k' (Std.Internal.List.insertList l toInsert) h = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) hc_k0 (1) (1) hc_k1 hc_k2 hc_k3) (by
  (simp <;> decide))

-- Std.Internal.List.getKeyD_insertList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKeyD_insertList_of_mem.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' fallback : α},
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              k ∈ List.map Sigma.fst toInsert →
                Std.Internal.List.getKeyD k' (Std.Internal.List.insertList l toInsert) fallback = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKeyD_insertList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKeyD_insertList_of_mem.h11 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' fallback : α},
            (k == k') = Bool.true →
              k ∈ List.map Sigma.fst toInsert →
                Std.Internal.List.getKeyD k' (Std.Internal.List.insertList l toInsert) fallback = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (0) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKeyD_insertList_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKeyD_insertList_of_mem.h12 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @EquivBEq α inst]
        {l toInsert : List (@Sigma α fun (a : α) => β a)},
        @Std.Internal.List.DistinctKeys α β inst l →
          ∀ {k k' fallback : α},
            @Eq Bool (@BEq.beq α inst k k') Bool.true →
              @List.Pairwise (@Sigma α fun (a : α) => β a)
                  (fun (a b : @Sigma α fun (a : α) => β a) =>
                    @Eq Bool (@BEq.beq α inst (@Sigma.fst α (fun (a : α) => β a) a) (@Sigma.fst α (fun (a : α) => β a) b))
                      Bool.false)
                  toInsert →
                @Eq α (@Std.Internal.List.getKeyD α β inst k' (@Std.Internal.List.insertList α β inst l toInsert) fallback)
                  k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (by
  simp) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (beq_self_eq_true _) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.minKeyD_alterKey_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_alterKey_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : Option (β k) → Option (β k)} {fallback : α}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKeyD_alterKey_eq_self, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_alterKey_eq_self.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option (β k) → Option (β k)} {fallback : α},
            Std.Internal.List.minKeyD (Std.Internal.List.alterKey k f l) fallback = k ↔
              (f (Std.Internal.List.getValueCast? k l)).isSome = Bool.true ∧
                ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k k').isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.maxKeyD_alterKey_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_alterKey_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : Option (β k) → Option (β k)} {fallback : α}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKeyD_alterKey_eq_self, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_alterKey_eq_self.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option (β k) → Option (β k)} {fallback : α},
            Std.Internal.List.maxKeyD (Std.Internal.List.alterKey k f l) fallback = k ↔
              (f (Std.Internal.List.getValueCast? k l)).isSome = Bool.true ∧
                ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k' k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none) (0)) (by
  (simp <;> decide))

-- Std.ExtDTreeMap.Const.get_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h4.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h4.prem0 (0) HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h4.prem2)

-- Std.ExtDTreeMap.Const.get_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            (k, v) ∈ l →
              ∀ {h' : k' ∈ Std.ExtDTreeMap.Const.insertMany t l},
                Std.ExtDTreeMap.Const.get (Std.ExtDTreeMap.Const.insertMany t l) k' h' = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) hc_k0 (0) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.get_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              ∀ {h' : k' ∈ Std.ExtDTreeMap.Const.insertMany t l},
                Std.ExtDTreeMap.Const.get (Std.ExtDTreeMap.Const.insertMany t l) k' h' = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (0) hc_k0 (1) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtDTreeMap.get!_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_ofList_of_mem.h3 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k} [inst : Inhabited (β k')],
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (instInhabitedNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get!_ofList_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_ofList_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k} [inst : Inhabited (β k')],
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (instInhabitedNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_compare (a := (Bool.false : Bool)) (b := (Bool.true : Bool))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get!_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} {v : β k} [inst : Inhabited (β k')],
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (instInhabitedNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.get!_ofList_of_mem, hypothesis 12: necessary
/- FAILED: 9:54: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 22:16: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    α | 7:162: `grind` has failed, use `+verbose` to obtain diagnostic information | 14:138: `grind` has failed, use `+verbose` to obtain diagnostic information | 11:54: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.56 k_eq✝ 0 | 35:16: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:189: `grind` has failed, use `+verbose` to obtain diagnostic information | 39:138: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_ofList_of_mem.h12 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst_1 : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k} [inst_2 : Inhabited (β k')],
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (Std.ExtDTreeMap.ofList l cmp).get! k' =
            cast
              ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                    (k_eq : cmp k k' = Ordering.eq) =>
                  (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                k_eq)
              v := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([]) (0) (0) hc_k0 (1) (instInhabitedNat) hc_k1) (by
  decide +kernel)
-/

-- Std.ExtTreeMap.getElem_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h4.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h4.prem0 (0) HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h4.prem2)

-- Std.ExtTreeMap.getElem_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α}, cmp k k' = Ordering.eq → ∀ {v : β}, (k, v) ∈ l → ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l)[k'] = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) hc_k0 (0) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtTreeMap.getElem_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_insertMany_list_of_mem.h11 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l)[k'] = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (0) hc_k0 (1) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.Internal.List.minKey?_le_minKey?_eraseKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_le_minKey?_eraseKey.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {km : α} {kme : α}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.minKey? (Std.Internal.List.eraseKey k l) = Option.some kme → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (2) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey?_le_minKey?_eraseKey, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_le_minKey?_eraseKey.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {km : α} {kme : α} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.minKey? (Std.Internal.List.eraseKey k l) = Option.some kme := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.minKey?_le_minKey?_eraseKey, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_le_minKey?_eraseKey.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k km kme : α} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.minKey? (Std.Internal.List.eraseKey k l) = Option.some kme →
            (Ord.compare km kme).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (1) (1) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getValueCast?_insertList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast?_insertList_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} {v : β k},
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              (⟨k, v⟩ : (a : α) × β a) ∈ toInsert → (k == k') = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getValueCast?_insertList_of_mem, hypothesis 12: necessary
/- FAILED: 10:60: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 22:22: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α | 8:217: `grind` has failed, use `+verbose` to obtain diagnostic information | 17:163: `grind` has failed, use `+verbose` to obtain diagnostic information | 6:52: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.7 0 | 17:14: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) Nat | 2:277: `grind` has failed, use `+verbose` to obtain diagnostic information | 43:163: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast?_insertList_of_mem.h12 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} (k_beq : (k == k') = Bool.true) {v : β k},
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              Std.Internal.List.getValueCast? k' (Std.Internal.List.insertList l toInsert) =
                Option.some
                  (cast
                    ((fun {α : Type} {β : α → Type} [BEq α] [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
                        (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
                      k_beq)
                    v) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([]) (by
  simp) (0) _ (beq_self_eq_true _) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

-- Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([0]) (0) (0) HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α}
        {h' : k' ∈ t.insertManyIfNewUnit l},
        ¬k ∈ t →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertManyIfNewUnit l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0, 1]) (0) (1) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : Std.TransCmp cmp] {l : List α}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {h' : k' ∈ t.insertManyIfNewUnit l},
            ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (t.insertManyIfNewUnit l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.Internal.List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' : α},
        (k == k') = Bool.true →
          ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertListIfNewUnit l toInsert) = Bool.true},
            Std.Internal.List.containsKey k l = Bool.false →
              List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
                k ∈ toInsert → Std.Internal.List.getKey k' (Std.Internal.List.insertListIfNewUnit l toInsert) h = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 hc_k4 => @hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([]) ([1, 0]) (1) (1) hc_k0 hc_k1 hc_k2 hc_k3 hc_k4) (by
  decide +kernel)

-- Std.Internal.List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem.h7 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' : α}
        {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertListIfNewUnit l toInsert) = Bool.true},
        Std.Internal.List.containsKey k l = Bool.false →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
            k ∈ toInsert → Std.Internal.List.getKey k' (Std.Internal.List.insertListIfNewUnit l toInsert) h = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0, 1]) (0) (1) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.Internal.List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem.h11 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' : α},
        (k == k') = Bool.true →
          ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertListIfNewUnit l toInsert) = Bool.true},
            Std.Internal.List.containsKey k l = Bool.false →
              List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
                Std.Internal.List.getKey k' (Std.Internal.List.insertListIfNewUnit l toInsert) h = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([0]) (1) (1) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.Internal.List.containsKey_of_length_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.containsKey_of_length_eq.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l₁ l₂ : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l₁ →
          Std.Internal.List.DistinctKeys l₂ →
            l₂.length = l₁.length →
              (∀ (a : α), Std.Internal.List.containsKey a l₁ = Bool.true → Std.Internal.List.containsKey a l₂ = Bool.true) →
                ∀ (a : α), Std.Internal.List.containsKey a l₂ = Bool.true → Std.Internal.List.containsKey a l₁ = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @Decidable.decide (@LE.le Nat instLENat a b) (a.decLe b)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @Decidable.decide (@LE.le Nat instLENat a b) (a.decLe b)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.containsKey_of_length_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.containsKey_of_length_eq.h8 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l₁ l₂ : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l₁ →
          Std.Internal.List.DistinctKeys l₂ →
            (∀ (a : α), Std.Internal.List.containsKey a l₁ = Bool.true → Std.Internal.List.containsKey a l₂ = Bool.true) →
              ∀ (a : α), Std.Internal.List.containsKey a l₂ = Bool.true → Std.Internal.List.containsKey a l₁ = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  simp) (by
  simp) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.containsKey_of_length_eq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.containsKey_of_length_eq.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l₁ l₂ : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l₁ →
          Std.Internal.List.DistinctKeys l₂ →
            l₂.length = l₁.length →
              ∀ (a : α), Std.Internal.List.containsKey a l₂ = Bool.true → Std.Internal.List.containsKey a l₁ = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.containsKey_of_length_eq, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.containsKey_of_length_eq.h11 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l₁ l₂ : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l₁ →
          Std.Internal.List.DistinctKeys l₂ →
            l₂.length = l₁.length →
              (∀ (a : α), Std.Internal.List.containsKey a l₁ = Bool.true → Std.Internal.List.containsKey a l₂ = Bool.true) →
                ∀ (a : α), Std.Internal.List.containsKey a l₁ = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([]) (by
  simp) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) (0)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h4.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} {fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h4.prem0 (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h4.prem2)

-- Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h8.inst : ¬Std.ExtDTreeMap.Const.getD
          (Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0)]) 1 1 =
        0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h8.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α} {v fallback : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.insertMany t l) k' fallback = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (0) (1) HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h8.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h8.prem1)

-- Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h11.inst : ¬Std.ExtDTreeMap.Const.getD
          (Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0), (0, 1)])
          0 0 =
        0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h11.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β}, (k, v) ∈ l → Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.insertMany t l) k' fallback = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h11.prem0 (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h11.prem1)

-- Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h12.inst : ¬Std.ExtDTreeMap.Const.getD
          (Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) []) 0 1 =
        0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h12.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h12.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h12 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.insertMany t l) k' fallback = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h12.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h12.prem0 (0) (1) HypCheckProof.Std.ExtDTreeMap.Const.getD_insertMany_list_of_mem.h12.prem1)

-- Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h4.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} [inst : Inhabited β]
        {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h4.prem0 (0) HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h4.prem2)

-- Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h9.inst : ¬Std.ExtDTreeMap.Const.get!
          (Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 1)]) 1 =
        1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h9.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 1)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h9.prem1 : (0, 1) ∈ [(0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : Inhabited β] {l : List (α × β)} {k k' : α} {v : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → Std.ExtDTreeMap.Const.get! (Std.ExtDTreeMap.Const.insertMany t l) k' = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h9.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([(0, 1)]) (0) (1) (1) HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h9.prem0 HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h9.prem1)

-- Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h11.inst : ¬Std.ExtDTreeMap.Const.get!
          (Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0), (0, 1)])
          0 =
        0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h11.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : Inhabited β] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, (k, v) ∈ l → Std.ExtDTreeMap.Const.get! (Std.ExtDTreeMap.Const.insertMany t l) k' = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h11.prem0 (0) HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h11.prem1)

-- Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h12.inst : ¬Std.ExtDTreeMap.Const.get!
          (Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) []) 0 =
        1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h12.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h12.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h12 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : Inhabited β] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              Std.ExtDTreeMap.Const.get! (Std.ExtDTreeMap.Const.insertMany t l) k' = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h12.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h12.prem0 (1) HypCheckProof.Std.ExtDTreeMap.Const.get!_insertMany_list_of_mem.h12.prem1)

-- Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} {l : List α} {k k' : α}
        {fallback : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([0]) (0) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst : Not
      (@Eq Nat
        (@Std.ExtDTreeMap.getKeyD Nat (fun (x : Nat) => Unit) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd
          (@Std.ExtDTreeMap.Const.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instTransOrd (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 : Not
      (@Membership.mem Nat (Std.ExtDTreeMap Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtDTreeMap.instMembershipOfTransCmp Nat (fun (x : Nat) => Unit)
          (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd)
        (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
          fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2 : @Membership.mem Nat (List Nat) (@List.instMembership Nat)
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : @Std.TransCmp α cmp]
        {l : List α} {k k' fallback : α},
        Not
            (@Membership.mem α (Std.ExtDTreeMap α (fun (x : α) => Unit) cmp)
              (@Std.ExtDTreeMap.instMembershipOfTransCmp α (fun (x : α) => Unit) cmp inst) t k) →
          @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
            @Membership.mem α (List α) (@List.instMembership α) l k →
              @Eq α
                (@Std.ExtDTreeMap.getKeyD α (fun (x : α) => Unit) cmp inst
                  (@Std.ExtDTreeMap.Const.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k' fallback)
                k) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2)

-- Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtDTreeMap.getKeyD Nat (fun (x : Nat) => Unit) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd
          (@Std.ExtDTreeMap.Const.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instTransOrd (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil Nat))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 : Not
      (@Membership.mem Nat (Std.ExtDTreeMap Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtDTreeMap.instMembershipOfTransCmp Nat (fun (x : Nat) => Unit)
          (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd)
        (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
          fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : @Std.TransCmp α cmp]
        {l : List α} {k k' fallback : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          Not
              (@Membership.mem α (Std.ExtDTreeMap α (fun (x : α) => Unit) cmp)
                (@Std.ExtDTreeMap.instMembershipOfTransCmp α (fun (x : α) => Unit) cmp inst) t k) →
            @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
              @Eq α
                (@Std.ExtDTreeMap.getKeyD α (fun (x : α) => Unit) cmp inst
                  (@Std.ExtDTreeMap.Const.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k' fallback)
                k) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2)

-- Std.ExtDTreeMap.getKey_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} {l : List ((a : α) × β a)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
            k ∈ List.map Sigma.fst l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.getKey_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_insertMany_list_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Sigma.fst l → ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtDTreeMap.get_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_insertMany_list_of_contains_eq_false.h4 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.LawfulEqCmp α cmp]
        [inst : BEq α] [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Std.TransCmp α cmp) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get_insertMany_list_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_insertMany_list_of_contains_eq_false.h7 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : @Std.LawfulEqCmp α cmp] [inst_2 : BEq α] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst_2 (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          ∀
            {h' :
              @Membership.mem α (Std.ExtDTreeMap α β cmp) (@Std.ExtDTreeMap.instMembershipOfTransCmp α β cmp inst)
                (@Std.ExtDTreeMap.insertMany α β cmp inst (List (@Sigma α fun (a : α) => β a))
                  (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
                    (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
                      (@List.instMembership (@Sigma α fun (a : α) => β a)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
                  t l)
                k},
            @Std.LawfulBEqCmp α inst_2 cmp) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat)
      (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
        (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
      fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Std.LawfulEqCmp cmp] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α}
        {h' : k ∈ t.insertMany l}, (List.map Sigma.fst l).contains k = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.get_insertMany_list_of_contains_eq_false, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get_insertMany_list_of_contains_eq_false.h11 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : @Std.LawfulEqCmp α cmp] [inst_2 : BEq α] [inst_3 : @Std.LawfulBEqCmp α inst_2 cmp]
        {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst_2 (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Membership.mem α (Std.ExtDTreeMap α β cmp) (@Std.ExtDTreeMap.instMembershipOfTransCmp α β cmp inst)
            (@Std.ExtDTreeMap.insertMany α β cmp inst (List (@Sigma α fun (a : α) => β a))
              (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
                (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
                  (@List.instMembership (@Sigma α fun (a : α) => β a)))
                (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
              t l)
            k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ _ (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.get?_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get?_ofList_of_mem.h3 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get?_ofList_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get?_ofList_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_compare (a := (Bool.false : Bool)) (b := (Bool.true : Bool))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get?_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get?_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.get?_ofList_of_mem, hypothesis 11: necessary
/- FAILED: 10:56: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 22:18: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    α | 7:175: `grind` has failed, use `+verbose` to obtain diagnostic information | 14:159: `grind` has failed, use `+verbose` to obtain diagnostic information | 12:56: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.56 k_eq✝ 0 | 36:18: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:202: `grind` has failed, use `+verbose` to obtain diagnostic information | 40:159: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get?_ofList_of_mem.h11 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst_1 : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (Std.ExtDTreeMap.ofList l cmp).get? k' =
            Option.some
              (cast
                ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                      (k_eq : cmp k k' = Ordering.eq) =>
                    (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k'
                      (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                  k_eq)
                v) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([]) (0) (0) hc_k0 (0) hc_k1) (by
  decide +kernel)
-/

-- Std.Internal.List.maxKey_alterKey_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_alterKey_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : Option (β k) → Option (β k)}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey_alterKey_eq_self, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_alterKey_eq_self.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option (β k) → Option (β k)}, (Std.Internal.List.alterKey k f l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  decide +kernel)

-- Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : Inhabited α] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) ([0]) (0) (0) HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst : Not
      (@Eq Nat
        (@Std.ExtTreeMap.getKey! Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
          instInhabitedNat
          (@Std.ExtTreeMap.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
            (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 : Not
      (@Membership.mem Nat (Std.ExtTreeMap Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtTreeMap.instMembershipOfTransCmp Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd)
        (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2 : @Membership.mem Nat (List Nat) (@List.instMembership Nat)
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : Inhabited α] {l : List α} {k k' : α},
        Not (@Membership.mem α (Std.ExtTreeMap α Unit cmp) (@Std.ExtTreeMap.instMembershipOfTransCmp α Unit cmp inst) t k) →
          @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
            @Membership.mem α (List α) (@List.instMembership α) l k →
              @Eq α
                (@Std.ExtTreeMap.getKey! α Unit cmp inst inst_1
                  (@Std.ExtTreeMap.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                k) := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2)

-- Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : Std.TransCmp cmp] [inst_1 : Inhabited α]
        {l : List α} {k k' : α}, cmp k k' = Ordering.eq → ¬k ∈ t → k ∈ l → (t.insertManyIfNewUnit l).getKey! k' = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtTreeMap.getKey! Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
          instInhabitedNat
          (@Std.ExtTreeMap.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
            (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil Nat))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 : Not
      (@Membership.mem Nat (Std.ExtTreeMap Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtTreeMap.instMembershipOfTransCmp Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd)
        (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : Inhabited α] {l : List α} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          Not
              (@Membership.mem α (Std.ExtTreeMap α Unit cmp) (@Std.ExtTreeMap.instMembershipOfTransCmp α Unit cmp inst) t
                k) →
            @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
              @Eq α
                (@Std.ExtTreeMap.getKey! α Unit cmp inst inst_1
                  (@Std.ExtTreeMap.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                k) := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 HypCheckProof.Std.ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2)

-- Std.ExtTreeMap.getKey_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h4.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h4.prem0 HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h4.prem2)

-- Std.ExtTreeMap.getKey_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_insertMany_list_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
            ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(Bool.false, 0)]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} {l : List α} {k k' : α} {fallback : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([0]) (0) (0) (0) HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.inst : ¬((Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [0]).getD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem0 : ¬0 ∈ Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α}
        {k k' fallback : α},
        ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).getD k' fallback = k := fun hc_h => HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (1) (1) HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem0 HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem1 HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem2)

-- Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α}
        {k k' fallback : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).getD k' fallback = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtTreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.false) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.inst : ¬((Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany []).getD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem1 : ¬0 ∈ Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem2 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α}
        {k k' fallback : α},
        cmp k k' = Ordering.eq →
          ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (t.insertMany l).getD k' fallback = k := fun hc_h => HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) (1) HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem0 HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem1 HypCheckProof.Std.ExtTreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem2)

-- Std.Internal.List.minKey_modifyKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_modifyKey.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {k : α} {f : β k → β k} {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (0) (fun n => n + 1 : Nat → Nat) ([]) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey_modifyKey, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_modifyKey.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] {k : α} {f : β k → β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → (Std.Internal.List.modifyKey k f l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ (0) (fun n => n + 1 : Nat → Nat) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.minKey?_le_of_containsKey, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_le_of_containsKey.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {km : α}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.containsKey k l = Bool.true → Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey?_le_of_containsKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_le_of_containsKey.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {km : α}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.containsKey k l = Bool.true → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey?_le_of_containsKey, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_le_of_containsKey.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {k : α} {km : α} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.containsKey k l = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.minKey?_le_of_containsKey, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_le_of_containsKey.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k km : α} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.containsKey k l = Bool.true → (Ord.compare km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (1) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.minKey!_eraseKey_eq_of_beq_minKey!_eq_false, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_eraseKey_eq_of_beq_minKey!_eq_false.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α},
            (Std.Internal.List.eraseKey k l).isEmpty = Bool.false →
              Std.Internal.List.minKey! (Std.Internal.List.eraseKey k l) = Std.Internal.List.minKey! l := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.maxKey!_eq_iff_mem_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey!_eq_iff_mem_and_forall.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          l.isEmpty = Bool.false →
            ∀ {km : α},
              Std.Internal.List.maxKey! l = km ↔
                Std.Internal.List.containsKey km l = Bool.true ∧
                  ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (instOrdBool) _ (⟨fun _ _ => true⟩ : BEq Bool) _ (instInhabitedBool) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Bool) (fun (a : Bool) => Nat) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (@List.cons (@Sigma Bool fun (a : Bool) => (fun (a : Bool) => Nat) a)
      (@Sigma.mk Bool (fun (a : Bool) => (fun (a : Bool) => Nat) a) Bool.false
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Bool fun (a : Bool) => (fun (a : Bool) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (Bool.false)) (by
  decide +kernel)

-- Std.Internal.List.maxKey!_eq_iff_mem_and_forall, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey!_eq_iff_mem_and_forall.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] [inst_5 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km : α},
            Std.Internal.List.maxKey! l = km ↔
              Std.Internal.List.containsKey km l = Bool.true ∧
                ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ (instInhabitedNat) ([]) (by
  simp) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' fallback : α},
        (k == k') = Bool.true →
          Std.Internal.List.containsKey k l = Bool.false →
            List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
              k ∈ toInsert → Std.Internal.List.getKeyD k' (Std.Internal.List.insertListIfNewUnit l toInsert) fallback = k := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([]) ([1, 0]) (1) (1) (0) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem.h8 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' fallback : α},
        Std.Internal.List.containsKey k l = Bool.false →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
            k ∈ toInsert → Std.Internal.List.getKeyD k' (Std.Internal.List.insertListIfNewUnit l toInsert) fallback = k := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0]) (0) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem.h10 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' fallback : α},
        (k == k') = Bool.true →
          Std.Internal.List.containsKey k l = Bool.false →
            k ∈ toInsert → Std.Internal.List.getKeyD k' (Std.Internal.List.insertListIfNewUnit l toInsert) fallback = k := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([0, 1]) (1) (1) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem.h11 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' fallback : α},
        (k == k') = Bool.true →
          Std.Internal.List.containsKey k l = Bool.false →
            List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
              Std.Internal.List.getKeyD k' (Std.Internal.List.insertListIfNewUnit l toInsert) fallback = k := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([]) _ (0) (1) (beq_self_eq_true _) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.minKeyD_eq_iff_mem_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_eq_iff_mem_and_forall.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          l.isEmpty = Bool.false →
            ∀ {km fallback : α},
              Std.Internal.List.minKeyD l fallback = km ↔
                Std.Internal.List.containsKey km l = Bool.true ∧
                  ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a != b⟩ : BEq Nat) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.maxKey?_le_of_containsKey, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_of_containsKey.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {km : α}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.containsKey k l = Bool.true → Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey?_le_of_containsKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_of_containsKey.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {km : α}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.containsKey k l = Bool.true → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey?_le_of_containsKey, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_of_containsKey.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {k : α} {km : α} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.containsKey k l = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.maxKey?_le_of_containsKey, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_of_containsKey.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k km : α} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.containsKey k l = Bool.true → (Ord.compare k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (1) (0) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.Const.maxKey_modifyKey_eq_maxKey, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey_modifyKey_eq_maxKey.h11 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst : Std.LawfulEqOrd α] {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : β → β}, (Std.Internal.List.Const.modifyKey k f l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.Internal.List.maxKeyD_eraseKey_eq_of_beq_maxKeyD_eq_false, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_eraseKey_eq_of_beq_maxKeyD_eq_false.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k fallback : α},
            (Std.Internal.List.eraseKey k l).isEmpty = Bool.false →
              Std.Internal.List.maxKeyD (Std.Internal.List.eraseKey k l) fallback = Std.Internal.List.maxKeyD l fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.Const.minKeyD_alterKey_eq_self, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKeyD_alterKey_eq_self.h10 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option β → Option β} {fallback : α},
            Std.Internal.List.minKeyD (Std.Internal.List.Const.alterKey k f l) fallback = k ↔
              (f (Std.Internal.List.getValue? k l)).isSome = Bool.true ∧
                ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k k').isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0) (fun (a : Option Nat) => Option.none) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.minKey?_insertEntryIfNew_le_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_le_self.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {kmi : α} {v : β k}
        {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) (0) ([]) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey?_insertEntryIfNew_le_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_le_self.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {kmi : α} {v : β k}
        {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) (0) ([]) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey?_insertEntryIfNew_le_self, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_le_self.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k kmi : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → (Ord.compare kmi k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (1) (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKey!_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Inhabited α]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
            k ∈ List.map Sigma.fst l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.getKey!_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Inhabited α] {l : List ((a : α) × β a)} {k k' : α},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Sigma.fst l → (t.insertMany l).getKey! k' = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKey!_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Inhabited α] {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq → k ∈ List.map Sigma.fst l → (t.insertMany l).getKey! k' = k := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtDTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a), (⟨Bool.true, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKey!_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtDTreeMap.getKey! Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd instInhabitedNat
          (@Std.ExtDTreeMap.insertMany Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instTransOrd (List (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))
            (@instForInOfForIn' Id (List (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))
              (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
              (@inferInstance
                (Membership (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
                  (List (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)))
                (@List.instMembership (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
                Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h11.prem1 : @List.Pairwise (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (fun (a b : @Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a) =>
        Not
          (@Eq Ordering
            ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
              (@Sigma.fst Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) a)
              (@Sigma.fst Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) b))
            Ordering.eq))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h11 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : Inhabited α] {l : List (@Sigma α fun (a : α) => β a)} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (@Sigma α fun (a : α) => β a)
              (fun (a b : @Sigma α fun (a : α) => β a) =>
                Not
                  (@Eq Ordering (cmp (@Sigma.fst α (fun (a : α) => β a) a) (@Sigma.fst α (fun (a : α) => β a) b))
                    Ordering.eq))
              l →
            @Eq α
              (@Std.ExtDTreeMap.getKey! α β cmp inst inst_1
                (@Std.ExtDTreeMap.insertMany α β cmp inst (List (@Sigma α fun (a : α) => β a))
                  (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
                    (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
                      (@List.instMembership (@Sigma α fun (a : α) => β a)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
                  t l)
                k')
              k) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h11.prem0 HypCheckProof.Std.ExtDTreeMap.getKey!_insertMany_list_of_mem.h11.prem1)

-- Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} {l : List ((a : α) × β a)}
        {k k' : α} {fallback : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
            k ∈ List.map Sigma.fst l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {l : List ((a : α) × β a)} {k k' fallback : α},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Sigma.fst l → (t.insertMany l).getKeyD k' fallback = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtDTreeMap.getKeyD Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd
          (@Std.ExtDTreeMap.insertMany Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instTransOrd (List (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))
            (@instForInOfForIn' Id (List (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))
              (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
              (@inferInstance
                (Membership (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
                  (List (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)))
                (@List.instMembership (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
                Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem.h11.prem1 : @List.Pairwise (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (fun (a b : @Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a) =>
        Not
          (@Eq Ordering
            ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
              (@Sigma.fst Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) a)
              (@Sigma.fst Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) b))
            Ordering.eq))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem.h11 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        {l : List (@Sigma α fun (a : α) => β a)} {k k' fallback : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (@Sigma α fun (a : α) => β a)
              (fun (a b : @Sigma α fun (a : α) => β a) =>
                Not
                  (@Eq Ordering (cmp (@Sigma.fst α (fun (a : α) => β a) a) (@Sigma.fst α (fun (a : α) => β a) b))
                    Ordering.eq))
              l →
            @Eq α
              (@Std.ExtDTreeMap.getKeyD α β cmp inst
                (@Std.ExtDTreeMap.insertMany α β cmp inst (List (@Sigma α fun (a : α) => β a))
                  (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
                    (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
                      (@List.instMembership (@Sigma α fun (a : α) => β a)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
                  t l)
                k' fallback)
              k) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem.h11.prem0 HypCheckProof.Std.ExtDTreeMap.getKeyD_insertMany_list_of_mem.h11.prem1)

-- Std.ExtDTreeMap.Const.get!_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h3.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h3.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst : Inhabited β],
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h3.prem0 (0) (instInhabitedNat) HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h3.prem1 HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h3.prem2)

-- Std.ExtDTreeMap.Const.get!_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h7.inst : ¬Std.ExtDTreeMap.Const.get! (Std.ExtDTreeMap.Const.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) 1 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 1)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h7.prem1 : (0, 1) ∈ [(0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α} {v : β}
        [inst_1 : Inhabited β],
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → Std.ExtDTreeMap.Const.get! (Std.ExtDTreeMap.Const.ofList l cmp) k' = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([(0, 1)]) (0) (1) (1) (instInhabitedNat) HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h7.prem0 HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h7.prem1)

-- Std.ExtDTreeMap.Const.get!_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h10.inst : ¬Std.ExtDTreeMap.Const.get! (Std.ExtDTreeMap.Const.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b) 0 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h10.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst_1 : Inhabited β],
            (k, v) ∈ l → Std.ExtDTreeMap.Const.get! (Std.ExtDTreeMap.Const.ofList l cmp) k' = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h10.prem0 (0) (instInhabitedNat) HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h10.prem1)

-- Std.ExtDTreeMap.Const.get!_ofList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h11.inst : ¬Std.ExtDTreeMap.Const.get! (Std.ExtDTreeMap.Const.ofList [] fun (a b : Nat) => Ord.compare a b) 0 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst_1 : Inhabited β],
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              Std.ExtDTreeMap.Const.get! (Std.ExtDTreeMap.Const.ofList l cmp) k' = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h11.prem0 (1) (instInhabitedNat) HypCheckProof.Std.ExtDTreeMap.Const.get!_ofList_of_mem.h11.prem1)

-- Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h4.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} [inst : Inhabited α]
        {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h4.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h4.prem2)

-- Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h9.inst : ¬(Std.ExtDTreeMap.Const.insertMany
              (Std.ExtDTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) [(0, 0)]).getKey!
          1 =
        0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h9.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h9.prem1 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : Inhabited α] {l : List (α × β)} {k k' : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l → (Std.ExtDTreeMap.Const.insertMany t l).getKey! k' = k := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h9.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([(0, 0)]) (0) (1) HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h9.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h9.prem1)

-- Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtDTreeMap.getKey! Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd instInhabitedNat
          (@Std.ExtDTreeMap.Const.insertMany Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat Nat.instTransOrd
            (List (Prod Nat Nat))
            (@instForInOfForIn' Id (List (Prod Nat Nat)) (Prod Nat Nat)
              (@inferInstance (Membership (Prod Nat Nat) (List (Prod Nat Nat))) (@List.instMembership (Prod Nat Nat)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod Nat Nat) Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (Prod Nat Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h11.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h11 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : @Std.TransCmp α cmp] [inst_1 : Inhabited α] {l : List (Prod α β)} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α
              (@Std.ExtDTreeMap.getKey! α (fun (x : α) => β) cmp inst inst_1
                (@Std.ExtDTreeMap.Const.insertMany α cmp β inst (List (Prod α β))
                  (@instForInOfForIn' Id (List (Prod α β)) (Prod α β)
                    (@inferInstance (Membership (Prod α β) (List (Prod α β))) (@List.instMembership (Prod α β)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod α β) Id.instMonad))
                  t l)
                k')
              k) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h11.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertMany_list_of_mem.h11.prem1)

-- Std.ExtTreeMap.getKey!_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h4.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Inhabited α] {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h4.prem0 HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h4.prem2)

-- Std.ExtTreeMap.getKey!_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtTreeMap.getKey! Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
          instInhabitedNat
          (@Std.ExtTreeMap.insertMany Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
            (List (Prod Nat Nat))
            (@instForInOfForIn' Id (List (Prod Nat Nat)) (Prod Nat Nat)
              (@inferInstance (Membership (Prod Nat Nat) (List (Prod Nat Nat))) (@List.instMembership (Prod Nat Nat)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod Nat Nat) Id.instMonad))
            (@Std.ExtTreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (Prod Nat Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h11.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h11 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : Inhabited α] {l : List (Prod α β)} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α
              (@Std.ExtTreeMap.getKey! α β cmp inst inst_1
                (@Std.ExtTreeMap.insertMany α β cmp inst (List (Prod α β))
                  (@instForInOfForIn' Id (List (Prod α β)) (Prod α β)
                    (@inferInstance (Membership (Prod α β) (List (Prod α β))) (@List.instMembership (Prod α β)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod α β) Id.instMonad))
                  t l)
                k')
              k) := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtTreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h11.prem0 HypCheckProof.Std.ExtTreeMap.getKey!_insertMany_list_of_mem.h11.prem1)

-- Std.Internal.List.Const.maxKeyD_alterKey_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKeyD_alterKey_eq_self.h5 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option β → Option β},
            (Std.Internal.List.Const.alterKey k f l).isEmpty = Bool.false →
              ∀ {fallback : α},
                Std.Internal.List.maxKeyD (Std.Internal.List.Const.alterKey k f l) fallback = k ↔
                  (f (Std.Internal.List.getValue? k l)).isSome = Bool.true ∧
                    ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k' k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (⟨fun a b => a != b⟩ : BEq Nat) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (0) (fun (a : Option Nat) => Option.none) (by
  decide) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.Const.maxKeyD_alterKey_eq_self, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKeyD_alterKey_eq_self.h10 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option β → Option β} {fallback : α},
            Std.Internal.List.maxKeyD (Std.Internal.List.Const.alterKey k f l) fallback = k ↔
              (f (Std.Internal.List.getValue? k l)).isSome = Bool.true ∧
                ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k' k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0) (fun (a : Option Nat) => Option.none) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.maxKey!_modifyKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey!_modifyKey.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : β k → β k}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (instInhabitedNat) ([]) (by
  simp) (0) (fun n => n + 1 : Nat → Nat)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.Const.beqModel_congr, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.beqModel_congr.h10 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : BEq β] {l₁ l₂ l₃ l₄ : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l₂ →
          l₂.Perm l₄ → Std.Internal.List.Const.beqModel l₁ l₂ = Std.Internal.List.Const.beqModel l₃ l₄ := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ (instBEqOfDecidableEq) ([]) ([]) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ([]) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.Const.beqModel_congr, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.beqModel_congr.h11 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : BEq β] {l₁ l₂ l₃ l₄ : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l₂ →
          l₁.Perm l₃ → Std.Internal.List.Const.beqModel l₁ l₂ = Std.Internal.List.Const.beqModel l₃ l₄ := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ (instBEqOfDecidableEq) ([]) ([]) ([]) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.minKeyD_insertEntryIfNew_le_minKeyD, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntryIfNew_le_minKeyD.h8 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {v : β k} {fallback : α},
            (Ord.compare (Std.Internal.List.minKeyD (Std.Internal.List.insertEntryIfNew k v l) fallback)
                  (Std.Internal.List.minKeyD l fallback)).isLE =
              Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (1) (0) (0)) (by
  decide +kernel)

-- Std.Internal.List.minKey!_insertEntryIfNew_of_isEmpty, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntryIfNew_of_isEmpty.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.minKey! (Std.Internal.List.insertEntryIfNew k v l) = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) (1) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.minKey!_insertEntry_le_minKey!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntry_le_minKey!.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Inhabited α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          l.isEmpty = Bool.false →
            ∀ {k : α} {v : β k},
              (Ord.compare (Std.Internal.List.minKey! (Std.Internal.List.insertEntry k v l))
                    (Std.Internal.List.minKey! l)).isLE =
                Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (instInhabitedNat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (0)) (by
  decide +kernel)

-- Std.Internal.List.minKey!_insertEntry_le_minKey!, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntry_le_minKey!.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {v : β k},
            (Ord.compare (Std.Internal.List.minKey! (Std.Internal.List.insertEntry k v l))
                  (Std.Internal.List.minKey! l)).isLE =
              Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) (by
  simp) (1) (0)) (by
  decide +kernel)

-- Std.Internal.List.Const.maxKey!_modifyKey, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey!_modifyKey.h11 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : β → β},
            Std.Internal.List.maxKey! (Std.Internal.List.Const.modifyKey k f l) =
              if (Std.Internal.List.maxKey! l == k) = Bool.true then k else Std.Internal.List.maxKey! l := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => .eq⟩ : Ord Bool) (@Std.TransCmp.mk (Bool) (@Ord.compare Bool (@Ord.mk Bool fun (x x_1 : Bool) => Ordering.eq)) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (⟨fun _ _ => true⟩ : BEq Bool) (@Std.LawfulBEqCmp.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (@Ord.compare Bool (@Ord.mk Bool fun (x x_1 : Bool) => Ordering.eq)) (by (try dsimp only);   decide)) (instInhabitedBool) ([]) (by
  simp) (Bool.true) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.Internal.List.minKey!_modifyKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_modifyKey.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : β k → β k}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (instInhabitedNat) ([]) (by
  simp) (0) (fun n => n + 1 : Nat → Nat)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.self_le_maxKey?_insertEntryIfNew, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.self_le_maxKey?_insertEntryIfNew.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {kmi : α} {v : β k}
        {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) (0) ([]) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.self_le_maxKey?_insertEntryIfNew, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.self_le_maxKey?_insertEntryIfNew.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {kmi : α} {v : β k}
        {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) (0) ([]) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.self_le_maxKey?_insertEntryIfNew, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.self_le_maxKey?_insertEntryIfNew.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k kmi : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → (Ord.compare k kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (1) (0) (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.Const.minKey!_modifyKey_eq_minKey!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey!_modifyKey_eq_minKey!.h5 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        [inst_4 : Inhabited α] {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : β → β},
            Std.Internal.List.minKey! (Std.Internal.List.Const.modifyKey k f l) = Std.Internal.List.minKey! l := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (instInhabitedNat) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (1) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.Internal.List.minKeyD_modifyKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_modifyKey.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : β k → β k} {fallback : α}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ ([]) (by
  simp) (0) (fun n => n + 1 : Nat → Nat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.self_le_maxKey?_insertEntry, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.self_le_maxKey?_insertEntry.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {v : β k}
        {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → ∀ {kmi : α}, Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ([]) (by
  simp) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.self_le_maxKey?_insertEntry, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.self_le_maxKey?_insertEntry.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {v : β k}
        {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → ∀ {kmi : α}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) ([]) (by
  simp) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.self_le_maxKey?_insertEntry, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.self_le_maxKey?_insertEntry.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {kmi : α}, (Ord.compare k kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (1) (0) ([]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.Internal.List.maxKeyD_le_maxKeyD_insertEntryIfNew, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_le_maxKeyD_insertEntryIfNew.h8 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {v : β k} {fallback : α},
            (Ord.compare (Std.Internal.List.maxKeyD l fallback)
                  (Std.Internal.List.maxKeyD (Std.Internal.List.insertEntryIfNew k v l) fallback)).isLE =
              Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0) (0) (1)) (by
  decide +kernel)

-- Std.Internal.List.maxKeyD_le_maxKeyD_insertEntry, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_le_maxKeyD_insertEntry.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          l.isEmpty = Bool.false →
            ∀ {k : α} {v : β k} {fallback : α},
              (Ord.compare (Std.Internal.List.maxKeyD l fallback)
                    (Std.Internal.List.maxKeyD (Std.Internal.List.insertEntry k v l) fallback)).isLE =
                Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (0) (0)) (by
  decide +kernel)

-- Std.Internal.List.maxKeyD_le_maxKeyD_insertEntry, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_le_maxKeyD_insertEntry.h8 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {v : β k} {fallback : α},
            (Ord.compare (Std.Internal.List.maxKeyD l fallback)
                  (Std.Internal.List.maxKeyD (Std.Internal.List.insertEntry k v l) fallback)).isLE =
              Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0) (0) (1)) (by
  decide +kernel)

-- Std.Internal.List.Const.minKey!_alterKey_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey!_alterKey_eq_self.h5 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Inhabited α]
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option β → Option β},
            (Std.Internal.List.Const.alterKey k f l).isEmpty = Bool.false →
              (Std.Internal.List.minKey! (Std.Internal.List.Const.alterKey k f l) = k ↔
                (f (Std.Internal.List.getValue? k l)).isSome = Bool.true ∧
                  ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k k').isLE = Bool.true) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (⟨fun a b => a != b⟩ : BEq Nat) (instInhabitedNat) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (0) (fun (a : Option Nat) => Option.none) (by
  decide)) (by
  (simp <;> decide))

-- Std.Internal.List.Const.minKey!_alterKey_eq_self, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey!_alterKey_eq_self.h11 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option β → Option β},
            Std.Internal.List.minKey! (Std.Internal.List.Const.alterKey k f l) = k ↔
              (f (Std.Internal.List.getValue? k l)).isSome = Bool.true ∧
                ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k k').isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) (by
  simp) (0) (fun (a : Option Nat) => Option.none)) (by
  (simp <;> decide))

-- Std.Internal.List.getValue_insertList_of_contains_eq_false_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue_insertList_of_contains_eq_false_left.h3 : ¬∀ {α β : Type} [inst : BEq α] {l toInsert : List ((_ : α) × β)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert →
            Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true →
              Std.Internal.List.containsKey k l = Bool.false → EquivBEq α := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([]) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) (0) (by
  simp) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @Decidable.decide (@LE.le Nat instLENat a b) (a.decLe b)) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toPartialEquivBEq.symm (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.getValue_insertList_of_contains_eq_false_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue_insertList_of_contains_eq_false_left.h9 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((_ : α) × β)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert →
            Std.Internal.List.containsKey k l = Bool.false →
              Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([]) (0) (by
  simp) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getValue_insertList_of_contains_eq_false_left, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue_insertList_of_contains_eq_false_left.h10 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((_ : α) × β)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert →
            Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true →
              Std.Internal.List.containsKey k l = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ([]) (0) (by
  simp) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.minKey_eq_iff_mem_and_forall, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_eq_iff_mem_and_forall.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst : Std.LawfulEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {km : α}, l.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.Internal.List.maxKey_eraseKey_eq_of_beq_maxKey_eq_false, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_eraseKey_eq_of_beq_maxKey_eq_false.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {he : (Std.Internal.List.eraseKey k l).isEmpty = Bool.false}, Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey_eraseKey_eq_of_beq_maxKey_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_eraseKey_eq_of_beq_maxKey_eq_false.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {he : (Std.Internal.List.eraseKey k l).isEmpty = Bool.false}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (2) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey_eraseKey_eq_of_beq_maxKey_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_eraseKey_eq_of_beq_maxKey_eq_false.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α}, (Std.Internal.List.eraseKey k l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.Internal.List.maxKey_eraseKey_eq_of_beq_maxKey_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_eraseKey_eq_of_beq_maxKey_eq_false.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)} (hd : Std.Internal.List.DistinctKeys l) {k : α}
        {he : (Std.Internal.List.eraseKey k l).isEmpty = Bool.false},
        Std.Internal.List.maxKey (Std.Internal.List.eraseKey k l) he =
          Std.Internal.List.maxKey l (Std.Internal.List.isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) hc_k0 (1) hc_k1) (by
  (simp <;> decide))

-- Std.Internal.List.getKey_insertList_of_contains_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_contains_right.h8 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)} {k : α},
        Std.Internal.List.DistinctKeys l →
          ∀ {m : Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true}
            (contains : Std.Internal.List.containsKey k toInsert = Bool.true),
            Std.Internal.List.getKey k (Std.Internal.List.insertList l toInsert) m =
              Std.Internal.List.getKey k toInsert contains := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) hc_k0 hc_k1 hc_k2) (by
  (simp <;> decide))

-- Std.Internal.List.getKey_insertList_of_contains_right, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_contains_right.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert →
            ∀ {m : Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true},
              Std.Internal.List.containsKey k toInsert = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([]) (0) (by
  simp) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKey_minKey?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_minKey?.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {km : α} {hc : Std.Internal.List.containsKey km l = Bool.true}, Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.getKey_minKey?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_minKey?.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km : α} {hc : Std.Internal.List.containsKey km l = Bool.true}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.getKey_minKey?, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_minKey?.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {km : α}, Std.Internal.List.containsKey km l = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.ExtTreeMap.getKey_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h3.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h3.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h3 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h3.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h3.prem0 HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h3.prem2)

-- Std.ExtTreeMap.getKey_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getKey_ofList_of_mem.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
            ∀ {h' : k' ∈ Std.ExtTreeMap.ofList l cmp}, (Std.ExtTreeMap.ofList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(Bool.false, 0)]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.Internal.List.getKey_insertList_of_contains_eq_false_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_contains_eq_false_left.h3 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] {l toInsert : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Std.Internal.List.DistinctKeys α β inst l →
          @Std.Internal.List.DistinctKeys α β inst toInsert →
            @Eq Bool (@Std.Internal.List.containsKey α β inst k (@Std.Internal.List.insertList α β inst l toInsert))
                Bool.true →
              @Eq Bool (@Std.Internal.List.containsKey α β inst k l) Bool.false → @EquivBEq α inst) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  simp) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @Decidable.decide (@LE.le Nat instLENat a b) (a.decLe b)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.toPartialEquivBEq.symm (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.getKey_insertList_of_contains_eq_false_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_contains_eq_false_left.h8 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)} {k : α},
        Std.Internal.List.DistinctKeys l →
          ∀ (contains : Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true)
            (not_contains : Std.Internal.List.containsKey k l = Bool.false),
            Std.Internal.List.getKey k (Std.Internal.List.insertList l toInsert) contains =
              Std.Internal.List.getKey k toInsert
                (Std.Internal.List.contains_of_contains_insertList_of_contains_eq_false_left contains not_contains) := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) hc_k0 hc_k1 hc_k2) (by
  (simp <;> decide))

-- Std.Internal.List.getKey_insertList_of_contains_eq_false_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_contains_eq_false_left.h9 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @EquivBEq α inst]
        {l toInsert : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Std.Internal.List.DistinctKeys α β inst l →
          @Std.Internal.List.DistinctKeys α β inst toInsert →
            @Eq Bool (@Std.Internal.List.containsKey α β inst k l) Bool.false →
              @Eq Bool (@Std.Internal.List.containsKey α β inst k (@Std.Internal.List.insertList α β inst l toInsert))
                Bool.true) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  simp) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKey_insertList_of_contains_eq_false_left, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_contains_eq_false_left.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert →
            Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true →
              Std.Internal.List.containsKey k l = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([]) (0) (by
  simp) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getValue_insertList_of_contains_right, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue_insertList_of_contains_right.h9 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((_ : α) × β)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert →
            ∀ {h : Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true},
              Std.Internal.List.containsKey k toInsert = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ([]) (0) (by
  simp) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([0]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.inst : Not
      (@Eq (Option Nat)
        (@Std.ExtDTreeMap.getKey? Nat (fun (x : Nat) => Unit) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd
          (@Std.ExtDTreeMap.Const.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instTransOrd (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem0 : Not
      (@Membership.mem Nat (Std.ExtDTreeMap Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtDTreeMap.instMembershipOfTransCmp Nat (fun (x : Nat) => Unit)
          (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd)
        (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
          fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem1 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem2 : @Membership.mem Nat (List Nat) (@List.instMembership Nat)
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : @Std.TransCmp α cmp]
        {l : List α} {k k' : α},
        Not
            (@Membership.mem α (Std.ExtDTreeMap α (fun (x : α) => Unit) cmp)
              (@Std.ExtDTreeMap.instMembershipOfTransCmp α (fun (x : α) => Unit) cmp inst) t k) →
          @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
            @Membership.mem α (List α) (@List.instMembership α) l k →
              @Eq (Option α)
                (@Std.ExtDTreeMap.getKey? α (fun (x : α) => Unit) cmp inst
                  (@Std.ExtDTreeMap.Const.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                (@Option.some α k)) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem2)

-- Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.inst : Not
      (@Eq (Option Nat)
        (@Std.ExtDTreeMap.getKey? Nat (fun (x : Nat) => Unit) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd
          (@Std.ExtDTreeMap.Const.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instTransOrd (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil Nat))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem1 : Not
      (@Membership.mem Nat (Std.ExtDTreeMap Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtDTreeMap.instMembershipOfTransCmp Nat (fun (x : Nat) => Unit)
          (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd)
        (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
          fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem2 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : @Std.TransCmp α cmp]
        {l : List α} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          Not
              (@Membership.mem α (Std.ExtDTreeMap α (fun (x : α) => Unit) cmp)
                (@Std.ExtDTreeMap.instMembershipOfTransCmp α (fun (x : α) => Unit) cmp inst) t k) →
            @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
              @Eq (Option α)
                (@Std.ExtDTreeMap.getKey? α (fun (x : α) => Unit) cmp inst
                  (@Std.ExtDTreeMap.Const.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                (@Option.some α k)) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem2)

-- Std.Internal.List.getKey_maxKey?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_maxKey?.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {km : α} {hc : Std.Internal.List.containsKey km l = Bool.true}, Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.getKey_maxKey?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_maxKey?.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km : α} {hc : Std.Internal.List.containsKey km l = Bool.true}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.getKey_maxKey?, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_maxKey?.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {km : α}, Std.Internal.List.containsKey km l = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.Internal.List.getValueCast_insertList_of_contains_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_insertList_of_contains_right.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l toInsert : List ((a : α) × β a)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert →
            Std.Internal.List.containsKey k toInsert = Bool.true →
              ∀ {h : Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true}, LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (by
  simp) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
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

-- Std.Internal.List.getValueCast_insertList_of_contains_right, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_insertList_of_contains_right.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert →
            ∀ {h : Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true},
              Std.Internal.List.containsKey k toInsert = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([]) (0) (by
  simp) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.Const.maxKey_alterKey_eq_self, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey_alterKey_eq_self.h10 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option β → Option β}, (Std.Internal.List.Const.alterKey k f l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

-- Std.Internal.List.minKey!_eq_iff_getKey?_eq_self_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_eq_iff_getKey?_eq_self_and_forall.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Inhabited α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          l.isEmpty = Bool.false →
            ∀ {km : α},
              Std.Internal.List.minKey! l = km ↔
                Std.Internal.List.getKey? km l = Option.some km ∧
                  ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a != b⟩ : BEq Nat) (instInhabitedNat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.minKey!_eq_iff_getKey?_eq_self_and_forall, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_eq_iff_getKey?_eq_self_and_forall.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km : α},
            Std.Internal.List.minKey! l = km ↔
              Std.Internal.List.getKey? km l = Option.some km ∧
                ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) (by
  simp) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.getEntry?_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getEntry?_of_mem.h5 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : PartialEquivBEq α] {l : List ((a : α) × β a)} {k k' : α},
        (k == k') = Bool.true →
          ∀ {v : β k},
            (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.Internal.List.getEntry? k' l = Option.some (⟨k, v⟩ : (a : α) × β a) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (1) (1) (by
  decide) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getEntry?_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getEntry?_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : PartialEquivBEq α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} {v : β k},
            (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.Internal.List.getEntry? k' l = Option.some (⟨k, v⟩ : (a : α) × β a) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getEntry?_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getEntry?_of_mem.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : PartialEquivBEq α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true → ∀ {v : β k}, Std.Internal.List.getEntry? k' l = Option.some (⟨k, v⟩ : (a : α) × β a) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) (by
  simp) (0) _ (beq_self_eq_true _) (0)) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_insertMany_list_of_contains_eq_false.h4 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : BEq α]
        [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Std.TransCmp α cmp) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_insertMany_list_of_contains_eq_false.h6 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : BEq α] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst_1 (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          ∀
            {h' :
              @Membership.mem α (Std.ExtDTreeMap α β cmp) (@Std.ExtDTreeMap.instMembershipOfTransCmp α β cmp inst)
                (@Std.ExtDTreeMap.insertMany α β cmp inst (List (@Sigma α fun (a : α) => β a))
                  (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
                    (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
                      (@List.instMembership (@Sigma α fun (a : α) => β a)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
                  t l)
                k},
            @Std.LawfulBEqCmp α inst_1 cmp) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat)
      (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
        (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
      fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α} {h' : k ∈ t.insertMany l},
        (List.map Sigma.fst l).contains k = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_insertMany_list_of_contains_eq_false.h10 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : BEq α] [inst_2 : @Std.LawfulBEqCmp α inst_1 cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst_1 (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Membership.mem α (Std.ExtDTreeMap α β cmp) (@Std.ExtDTreeMap.instMembershipOfTransCmp α β cmp inst)
            (@Std.ExtDTreeMap.insertMany α β cmp inst (List (@Sigma α fun (a : α) => β a))
              (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
                (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
                  (@List.instMembership (@Sigma α fun (a : α) => β a)))
                (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
              t l)
            k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.mem_of_mem_insertMany_list, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.mem_of_mem_insertMany_list.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([]) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.Const.mem_of_mem_insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.mem_of_mem_insertMany_list.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] {l : List (α × β)} {k : α},
        k ∈ Std.ExtDTreeMap.Const.insertMany t l → (List.map Prod.fst l).contains k = Bool.false → k ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.mem_of_mem_insertMany_list, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.mem_of_mem_insertMany_list.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        k ∈ Std.ExtDTreeMap.Const.insertMany t l → k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h4.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h4.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h4.prem2)

-- Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h8.inst : ¬(Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0)]).getKey? 1 =
        Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h8.prem1 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l → (Std.ExtDTreeMap.Const.insertMany t l).getKey? k' = Option.some k := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h8.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h8.prem1)

-- Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h10.inst : Not
      (@Eq (Option Nat)
        (@Std.ExtDTreeMap.getKey? Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd
          (@Std.ExtDTreeMap.Const.insertMany Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat Nat.instTransOrd
            (List (Prod Nat Nat))
            (@instForInOfForIn' Id (List (Prod Nat Nat)) (Prod Nat Nat)
              (@inferInstance (Membership (Prod Nat Nat) (List (Prod Nat Nat))) (@List.instMembership (Prod Nat Nat)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod Nat Nat) Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (Prod Nat Nat)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h10.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h10 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : @Std.TransCmp α cmp] {l : List (Prod α β)} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq (Option α)
              (@Std.ExtDTreeMap.getKey? α (fun (x : α) => β) cmp inst
                (@Std.ExtDTreeMap.Const.insertMany α cmp β inst (List (Prod α β))
                  (@instForInOfForIn' Id (List (Prod α β)) (Prod α β)
                    (@inferInstance (Membership (Prod α β) (List (Prod α β))) (@List.instMembership (Prod α β)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod α β) Id.instMonad))
                  t l)
                k')
              (@Option.some α k)) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h10.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey?_insertMany_list_of_mem.h10.prem1)

-- Std.ExtDTreeMap.Const.getKey!_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h3.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h3.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Inhabited α] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) (instInhabitedNat) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h3.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h3.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h3.prem2)

-- Std.ExtDTreeMap.Const.getKey!_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h10.inst : Not
      (@Eq Nat
        (@Std.ExtDTreeMap.getKey! Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd instInhabitedNat
          (@Std.ExtDTreeMap.Const.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) =>
            @Ord.compare Nat instOrdNat a b)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h10.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h10 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : @Std.TransCmp α cmp] [inst_1 : Inhabited α]
        {l : List (Prod α β)} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α
              (@Std.ExtDTreeMap.getKey! α (fun (x : α) => β) cmp inst inst_1 (@Std.ExtDTreeMap.Const.ofList α β l cmp) k')
              k) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) _ (instInhabitedNat) (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h10.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_ofList_of_mem.h10.prem1)

