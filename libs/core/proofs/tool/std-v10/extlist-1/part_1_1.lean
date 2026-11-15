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

-- Std.ExtDTreeMap.get?_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get?_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get?_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get?_insertMany_list_of_mem.h11 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α}
        {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.get?_insertMany_list_of_mem, hypothesis 14: necessary
/- FAILED: 11:56: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 31:18: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    α | 8:161: `grind` has failed, use `+verbose` to obtain diagnostic information | 23:159: `grind` has failed, use `+verbose` to obtain diagnostic information | 12:56: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.63 k_eq✝ 0 | 46:18: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 8:132: `grind` has failed, use `+verbose` to obtain diagnostic information | 59:159: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get?_insertMany_list_of_mem.h14 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Std.LawfulEqCmp cmp] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)}
        {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (t.insertMany l).get? k' =
            Option.some
              (cast
                ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                      (k_eq : cmp k k' = Ordering.eq) =>
                    (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k'
                      (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                  k_eq)
                v) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instBEqOfDecidableEq) _ ([]) (0) (0) hc_k0 (0) hc_k1) (by
  decide +kernel)
-/

-- Std.Internal.List.getValueCast_insertList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_insertList_of_mem.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              ∀ (v : β k),
                List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
                  (⟨k, v⟩ : (a : α) × β a) ∈ toInsert →
                    ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertList l toInsert) = Bool.true},
                      LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (by
  decide) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
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

-- Std.Internal.List.getValueCast_insertList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_insertList_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} (v : β k),
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              (⟨k, v⟩ : (a : α) × β a) ∈ toInsert →
                ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertList l toInsert) = Bool.true},
                  (k == k') = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getValueCast_insertList_of_mem, hypothesis 12: necessary
/- FAILED: 10:60: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 25:22: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α | 9:207: `grind` has failed, use `+verbose` to obtain diagnostic information | 22:144: `grind` has failed, use `+verbose` to obtain diagnostic information | 14:56: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = Nat | 49:18: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) Nat | 2:84: typeclass instance problem is stuck
  BEq ?m.1

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `BEq` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresol | 44:3: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_insertList_of_mem.h12 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} (k_beq : (k == k') = Bool.true) (v : β k),
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertList l toInsert) = Bool.true},
                Std.Internal.List.getValueCast k' (Std.Internal.List.insertList l toInsert) h =
                  cast
                    ((fun {α : Type} {β : α → Type} [BEq α] [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
                        (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
                      k_beq)
                    v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) hc_k0 (0) _ (beq_self_eq_true _) (1) hc_k1 hc_k2) (by
  (simp <;> decide))
-/

-- Std.Internal.List.minKey?_insertEntryIfNew_le_minKey?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_le_minKey?.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {v : β k}
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

-- Std.Internal.List.minKey?_insertEntryIfNew_le_minKey?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_le_minKey?.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {v : β k}
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

-- Std.Internal.List.minKey?_insertEntryIfNew_le_minKey?, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_le_minKey?.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)} (hl : Std.Internal.List.DistinctKeys l) {km kmi : α},
        (Std.Internal.List.minKey? (Std.Internal.List.insertEntryIfNew k v l)).get
              (Std.Internal.List.isSome_minKey?_insertEntryIfNew hl) =
            kmi →
          (Ord.compare kmi km).isLE = Bool.true := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (1) (0) ([]) hc_k0 (0) (1) hc_k1) (by
  (simp <;> decide))

-- Std.Internal.List.minKey?_insertEntryIfNew_le_minKey?, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntryIfNew_le_minKey?.h13 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km kmi : α}, Std.Internal.List.minKey? l = Option.some km → (Ord.compare kmi km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.maxKey?_le_maxKey?_insertEntry, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_maxKey?_insertEntry.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {v : β k}
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

-- Std.Internal.List.maxKey?_le_maxKey?_insertEntry, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_maxKey?_insertEntry.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {v : β k}
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

-- Std.Internal.List.maxKey?_le_maxKey?_insertEntry, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_maxKey?_insertEntry.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)} (hd : Std.Internal.List.DistinctKeys l) {km kmi : α},
        (Std.Internal.List.maxKey? (Std.Internal.List.insertEntry k v l)).get
              (Std.Internal.List.isSome_maxKey?_insertEntry hd) =
            kmi →
          (Ord.compare km kmi).isLE = Bool.true := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) ([]) hc_k0 (1) (0) hc_k1) (by
  (simp <;> decide))

-- Std.Internal.List.maxKey?_le_maxKey?_insertEntry, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_le_maxKey?_insertEntry.h13 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km kmi : α}, Std.Internal.List.maxKey? l = Option.some km → (Ord.compare km kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.Const.minKey?_modifyKey_beq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey?_modifyKey_beq.h3 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {f : β → β} {km : α} {kmm : α}
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.minKey? l = Option.some km → Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (fun n => n + 1 : Nat → Nat) (0) (0) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) (by
  simp) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.Const.minKey?_modifyKey_beq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey?_modifyKey_beq.h5 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {f : β → β} {km : α} {kmm : α}
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.minKey? l = Option.some km → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (fun n => n + 1 : Nat → Nat) (0) (0) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
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

-- Std.Internal.List.Const.minKey?_modifyKey_beq, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey?_modifyKey_beq.h12 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α] {k : α}
        {f : β → β} {km : α} {kmm : α} {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.minKey? l = Option.some km := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (fun n => n + 1 : Nat → Nat) (0) (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.Const.minKey?_modifyKey_beq, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey?_modifyKey_beq.h13 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α] {k : α}
        {f : β → β} {km kmm : α} {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.minKey? l = Option.some km → (kmm == km) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (fun n => n + 1 : Nat → Nat) (0) (1) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getValueCast!_insertList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast!_insertList_of_mem.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              ∀ (v : β k) [inst_1 : Inhabited (β k')],
                List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
                  (⟨k, v⟩ : (a : α) × β a) ∈ toInsert → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (by
  decide) (0) (instInhabitedNat) (by
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

-- Std.Internal.List.getValueCast!_insertList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast!_insertList_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} (v : β k) [inst_2 : Inhabited (β k')],
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              (⟨k, v⟩ : (a : α) × β a) ∈ toInsert → (k == k') = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1) (0) (instInhabitedNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getValueCast!_insertList_of_mem, hypothesis 13: necessary
/- FAILED: 9:58: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 22:20: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α | 8:204: `grind` has failed, use `+verbose` to obtain diagnostic information | 17:142: `grind` has failed, use `+verbose` to obtain diagnostic information | 8:56: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.62 k_beq✝ 0 | 35:18: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) Nat | 5:192: `grind` has failed, use `+verbose` to obtain diagnostic information | 43:142: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast!_insertList_of_mem.h13 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} (k_beq : (k == k') = Bool.true) (v : β k) [inst_2 : Inhabited (β k')],
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              Std.Internal.List.getValueCast! k' (Std.Internal.List.insertList l toInsert) =
                cast
                  ((fun {α : Type} {β : α → Type} [BEq α] [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
                      (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
                    k_beq)
                  v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([]) hc_k0 (0) (0) hc_k1 (1) (instInhabitedNat) hc_k2) (by
  (simp <;> decide))
-/

-- Std.Internal.List.getValueCastD_insertList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCastD_insertList_of_mem.h3 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              ∀ {v : β k} {fallback : β k'},
                List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
                  (⟨k, v⟩ : (a : α) × β a) ∈ toInsert → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (by
  decide) (0) (0) (by
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

-- Std.Internal.List.getValueCastD_insertList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCastD_insertList_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} {v : β k} {fallback : β k'},
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              (⟨k, v⟩ : (a : α) × β a) ∈ toInsert → (k == k') = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getValueCastD_insertList_of_mem, hypothesis 13: necessary
/- FAILED: 9:58: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 22:20: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) α | 8:213: `grind` has failed, use `+verbose` to obtain diagnostic information | 17:142: `grind` has failed, use `+verbose` to obtain diagnostic information | 8:56: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.62 k_beq✝ 0 | 35:18: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  (?m.5 == ?m.6) = true
of sort `Prop` in the application
  (fun {α} {β} [BEq α] [LawfulBEq α] {k k'} k_beq => (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (eq_of_beq k_beq)) Nat | 5:194: `grind` has failed, use `+verbose` to obtain diagnostic information | 44:142: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCastD_insertList_of_mem.h13 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} (k_beq : (k == k') = Bool.true) {v : β k} {fallback : β k'},
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              Std.Internal.List.getValueCastD k' (Std.Internal.List.insertList l toInsert) fallback =
                cast
                  ((fun {α : Type} {β : α → Type} [BEq α] [LawfulBEq α] {k k' : α} (k_beq : (k == k') = Bool.true) =>
                      (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (LawfulBEq.eq_of_beq k_beq))
                    k_beq)
                  v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([]) hc_k0 (0) (0) hc_k1 (0) (1) hc_k2) (by
  (simp <;> decide))
-/

-- Std.ExtDTreeMap.get!_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k} [inst : Inhabited (β k')],
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (instInhabitedNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.get!_insertMany_list_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_insertMany_list_of_mem.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k} [inst : Inhabited (β k')],
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtDTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
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

-- Std.ExtDTreeMap.get!_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α} {v : β k} [inst : Inhabited (β k')],
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (instInhabitedNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.get!_insertMany_list_of_mem, hypothesis 13: necessary
/- FAILED: 10:54: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 30:16: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    α | 7:148: `grind` has failed, use `+verbose` to obtain diagnostic information | 22:138: `grind` has failed, use `+verbose` to obtain diagnostic information | 11:54: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.63 k_eq✝ 0 | 45:16: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:205: `grind` has failed, use `+verbose` to obtain diagnostic information | 57:138: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_insertMany_list_of_mem.h13 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k}
        [inst_2 : Inhabited (β k')],
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (t.insertMany l).get! k' =
            cast
              ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                    (k_eq : cmp k k' = Ordering.eq) =>
                  (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                k_eq)
              v := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ ([]) (0) (0) hc_k0 (1) (instInhabitedNat) hc_k1) (by
  decide +kernel)
-/

-- Std.ExtDTreeMap.getD_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k} {fallback : β k'},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.getD_insertMany_list_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_insertMany_list_of_mem.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k} {fallback : β k'},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtDTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (0) (by
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

-- Std.ExtDTreeMap.getD_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α} {v : β k} {fallback : β k'},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.getD_insertMany_list_of_mem, hypothesis 13: necessary
/- FAILED: 10:54: invalid `▸` notation, expected result type of cast is 
  β✝ k✝ = β✝ k'✝
however, the equality 
  e_a
of type 
  a = a_1
does not contain the expected result type on either the left or the right hand side | 30:16: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    α | 7:157: `grind` has failed, use `+verbose` to obtain diagnostic information | 22:138: `grind` has failed, use `+verbose` to obtain diagnostic information | 11:54: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.63 k_eq✝ 0 | 46:16: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:207: `grind` has failed, use `+verbose` to obtain diagnostic information | 58:138: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_insertMany_list_of_mem.h13 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k}
        {fallback : β k'},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (t.insertMany l).getD k' fallback =
            cast
              ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                    (k_eq : cmp k k' = Ordering.eq) =>
                  (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                k_eq)
              v := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ ([]) (0) (0) hc_k0 (0) (1) hc_k1) (by
  decide +kernel)
-/

-- Std.ExtTreeMap.getElem?_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h4.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h4.prem0 (0) HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h4.prem2)

-- Std.ExtTreeMap.getElem?_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h10.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0)])[1]? = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h10.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h10.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] [inst_1 : BEq α]
        [inst_2 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k k' : α} {v : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → (t.insertMany l)[k']? = Option.some v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h10.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (1) (0) HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h10.prem0 HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h10.prem1)

-- Std.ExtTreeMap.getElem?_insertMany_list_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h12.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0), (0, 1)])[0]? = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h12.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h12.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h12 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] [inst_1 : BEq α]
        [inst_2 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq → ∀ {v : β}, (k, v) ∈ l → (t.insertMany l)[k']? = Option.some v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h12.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h12.prem0 (0) HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h12.prem1)

-- Std.ExtTreeMap.getElem?_insertMany_list_of_mem, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h13.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [])[0]? = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h13.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h13.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h13 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] [inst_1 : BEq α]
        [inst_2 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (t.insertMany l)[k']? = Option.some v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h13.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h13.prem0 (0) HypCheckProof.Std.ExtTreeMap.getElem?_insertMany_list_of_mem.h13.prem1)

-- Std.Internal.List.getKey_insertListConst_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertListConst_of_mem.h9 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
              k ∈ List.map Prod.fst toInsert →
                ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertListConst l toInsert) = Bool.true},
                  Std.Internal.List.getKey k' (Std.Internal.List.insertListConst l toInsert) h = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([(⟨1, 0⟩ : (_ : Nat) × Nat)]) ([(0, 0)]) hc_k0 (0) (1) hc_k1 hc_k2 hc_k3) (by
  (simp <;> decide))

-- Std.Internal.List.getKey_insertListConst_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertListConst_of_mem.h11 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
                ∀ {h : Std.Internal.List.containsKey k' (Std.Internal.List.insertListConst l toInsert) = Bool.true},
                  Std.Internal.List.getKey k' (Std.Internal.List.insertListConst l toInsert) h = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([(0, 0)]) hc_k0 (1) (1) hc_k1 hc_k2 hc_k3) (by
  (simp <;> decide))

-- Std.Internal.List.getValue?_insertListConst_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue?_insertListConst_of_mem.h9 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α} {v : β},
            List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
              (k, v) ∈ toInsert →
                Std.Internal.List.getValue? k' (Std.Internal.List.insertListConst l toInsert) = Option.some v := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([(0, 0)]) (by
  simp) (0) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getValue?_insertListConst_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue?_insertListConst_of_mem.h11 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              ∀ {v : β},
                (k, v) ∈ toInsert →
                  Std.Internal.List.getValue? k' (Std.Internal.List.insertListConst l toInsert) = Option.some v := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([(0, 0), (0, 1)]) (by
  simp) _ (0) (beq_self_eq_true _) (0) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getValue?_insertListConst_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValue?_insertListConst_of_mem.h12 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              ∀ {v : β},
                List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
                  Std.Internal.List.getValue? k' (Std.Internal.List.insertListConst l toInsert) = Option.some v := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([]) (by
  simp) _ (0) (beq_self_eq_true _) (0) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.maxKey!_alterKey_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey!_alterKey_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : Option (β k) → Option (β k)}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (instInhabitedNat) ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey!_alterKey_eq_self, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey!_alterKey_eq_self.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] [inst_5 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option (β k) → Option (β k)},
            Std.Internal.List.maxKey! (Std.Internal.List.alterKey k f l) = k ↔
              (f (Std.Internal.List.getValueCast? k l)).isSome = Bool.true ∧
                ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k' k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ (instInhabitedNat) ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  (simp <;> decide))

-- Std.Internal.List.getKey!_insertList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey!_insertList_of_mem.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited α]
        {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              k ∈ List.map Sigma.fst toInsert → Std.Internal.List.getKey! k' (Std.Internal.List.insertList l toInsert) = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKey!_insertList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey!_insertList_of_mem.h11 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited α]
        {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              k ∈ List.map Sigma.fst toInsert → Std.Internal.List.getKey! k' (Std.Internal.List.insertList l toInsert) = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) (instInhabitedNat) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKey!_insertList_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey!_insertList_of_mem.h12 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @EquivBEq α inst] [inst_2 : Inhabited α]
        {l toInsert : List (@Sigma α fun (a : α) => β a)},
        @Std.Internal.List.DistinctKeys α β inst l →
          ∀ {k k' : α},
            @Eq Bool (@BEq.beq α inst k k') Bool.true →
              @List.Pairwise (@Sigma α fun (a : α) => β a)
                  (fun (a b : @Sigma α fun (a : α) => β a) =>
                    @Eq Bool (@BEq.beq α inst (@Sigma.fst α (fun (a : α) => β a) a) (@Sigma.fst α (fun (a : α) => β a) b))
                      Bool.false)
                  toInsert →
                @Eq α (@Std.Internal.List.getKey! α β inst inst_2 k' (@Std.Internal.List.insertList α β inst l toInsert)) k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (instInhabitedNat) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (by
  simp) _ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (beq_self_eq_true _) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.minKey!_alterKey_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_alterKey_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : Option (β k) → Option (β k)}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (instInhabitedNat) ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey!_alterKey_eq_self, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_alterKey_eq_self.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] [inst_5 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option (β k) → Option (β k)},
            Std.Internal.List.minKey! (Std.Internal.List.alterKey k f l) = k ↔
              (f (Std.Internal.List.getValueCast? k l)).isSome = Bool.true ∧
                ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k k').isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ (instInhabitedNat) ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  (simp <;> decide))

-- Std.Internal.List.getKey!_insertListConst_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey!_insertListConst_of_mem.h10 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited α] {l : List ((_ : α) × β)}
        {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
              k ∈ List.map Prod.fst toInsert →
                Std.Internal.List.getKey! k' (Std.Internal.List.insertListConst l toInsert) = k := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ (instInhabitedNat) ([(⟨1, 0⟩ : (_ : Nat) × Nat)]) ([(0, 0)]) (by
  simp) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKey!_insertListConst_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey!_insertListConst_of_mem.h12 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited α] {l : List ((_ : α) × β)}
        {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
                Std.Internal.List.getKey! k' (Std.Internal.List.insertListConst l toInsert) = k := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) ([]) (by
  simp) _ (1) (beq_self_eq_true _) (by
  decide)) (by
  decide +kernel)

-- Std.ExtDTreeMap.getD_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_ofList_of_mem.h3 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k} {fallback : β k'},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.getD_ofList_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_ofList_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k} {fallback : β k'},
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (0) (by
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

-- Std.ExtDTreeMap.getD_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} {v : β k} {fallback : β k'},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.getD_ofList_of_mem, hypothesis 12: necessary
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
    α | 7:171: `grind` has failed, use `+verbose` to obtain diagnostic information | 14:138: `grind` has failed, use `+verbose` to obtain diagnostic information | 11:54: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.56 k_eq✝ 0 | 36:16: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:191: `grind` has failed, use `+verbose` to obtain diagnostic information | 40:138: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_ofList_of_mem.h12 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst_1 : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k} {fallback : β k'},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (Std.ExtDTreeMap.ofList l cmp).getD k' fallback =
            cast
              ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                    (k_eq : cmp k k' = Ordering.eq) =>
                  (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                k_eq)
              v := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([]) (0) (0) hc_k0 (0) (1) hc_k1) (by
  decide +kernel)
-/

-- Std.Internal.List.maxKey?_eraseKey_le_maxKey?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_eraseKey_le_maxKey?.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {km : α} {kme : α}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.maxKey? (Std.Internal.List.eraseKey k l) = Option.some kme → Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (1) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey?_eraseKey_le_maxKey?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_eraseKey_le_maxKey?.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {km : α} {kme : α}
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.maxKey? (Std.Internal.List.eraseKey k l) = Option.some kme → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (2) (0) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
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

-- Std.Internal.List.maxKey?_eraseKey_le_maxKey?, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_eraseKey_le_maxKey?.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {km : α} {kme : α} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.maxKey? (Std.Internal.List.eraseKey k l) = Option.some kme := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.maxKey?_eraseKey_le_maxKey?, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey?_eraseKey_le_maxKey?.h12 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k km kme : α} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.maxKey? (Std.Internal.List.eraseKey k l) = Option.some kme →
            (Ord.compare kme km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) (1) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKeyD_insertListConst_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKeyD_insertListConst_of_mem.h10 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' fallback : α},
            List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
              k ∈ List.map Prod.fst toInsert →
                Std.Internal.List.getKeyD k' (Std.Internal.List.insertListConst l toInsert) fallback = k := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([(0, 0)]) (by
  simp) (0) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKeyD_insertListConst_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKeyD_insertListConst_of_mem.h12 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' fallback : α},
            (k == k') = Bool.true →
              List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
                Std.Internal.List.getKeyD k' (Std.Internal.List.insertListConst l toInsert) fallback = k := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([]) (by
  simp) _ (0) (1) (beq_self_eq_true _) (by
  decide)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([0]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        {l : List α} {k k' : α} {h' : k' ∈ Std.ExtDTreeMap.Const.insertManyIfNewUnit t l},
        ¬k ∈ t →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
            k ∈ l → (Std.ExtDTreeMap.Const.insertManyIfNewUnit t l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0, 1]) (0) (1) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {h' : k' ∈ Std.ExtDTreeMap.Const.insertManyIfNewUnit t l},
            ¬k ∈ t →
              List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
                (Std.ExtDTreeMap.Const.insertManyIfNewUnit t l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtDTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([0]) (0) (0) HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α}
        {h' : k' ∈ t.insertMany l},
        ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0, 1]) (0) (1) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {h' : k' ∈ t.insertMany l},
            List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtTreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.false) (Bool.false) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeSet.get_insertMany_list_of_not_mem_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {h' : k' ∈ t.insertMany l},
            ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (t.insertMany l).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtTreeSet.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.Internal.List.getKey?_insertList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey?_insertList_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            List.Pairwise (fun (a b : (a : α) × β a) => (a.fst == b.fst) = Bool.false) toInsert →
              k ∈ List.map Sigma.fst toInsert →
                Std.Internal.List.getKey? k' (Std.Internal.List.insertList l toInsert) = Option.some k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKey?_insertList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey?_insertList_of_mem.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              k ∈ List.map Sigma.fst toInsert →
                Std.Internal.List.getKey? k' (Std.Internal.List.insertList l toInsert) = Option.some k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKey?_insertList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey?_insertList_of_mem.h11 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @EquivBEq α inst]
        {l toInsert : List (@Sigma α fun (a : α) => β a)},
        @Std.Internal.List.DistinctKeys α β inst l →
          ∀ {k k' : α},
            @Eq Bool (@BEq.beq α inst k k') Bool.true →
              @List.Pairwise (@Sigma α fun (a : α) => β a)
                  (fun (a b : @Sigma α fun (a : α) => β a) =>
                    @Eq Bool (@BEq.beq α inst (@Sigma.fst α (fun (a : α) => β a) a) (@Sigma.fst α (fun (a : α) => β a) b))
                      Bool.false)
                  toInsert →
                @Eq (Option α) (@Std.Internal.List.getKey? α β inst k' (@Std.Internal.List.insertList α β inst l toInsert))
                  (@Option.some α k)) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (by
  simp) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (beq_self_eq_true _) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.Const.minKey_modifyKey_eq_minKey, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey_modifyKey_eq_minKey.h11 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst : Std.LawfulEqOrd α] {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : β → β}, (Std.Internal.List.Const.modifyKey k f l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : Inhabited α]
        {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) ([0]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst : Not
      (@Eq Nat
        (@Std.ExtDTreeMap.getKey! Nat (fun (x : Nat) => Unit) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd instInhabitedNat
          (@Std.ExtDTreeMap.Const.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instTransOrd (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 : Not
      (@Membership.mem Nat (Std.ExtDTreeMap Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtDTreeMap.instMembershipOfTransCmp Nat (fun (x : Nat) => Unit)
          (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd)
        (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
          fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2 : @Membership.mem Nat (List Nat) (@List.instMembership Nat)
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : Inhabited α] {l : List α} {k k' : α},
        Not
            (@Membership.mem α (Std.ExtDTreeMap α (fun (x : α) => Unit) cmp)
              (@Std.ExtDTreeMap.instMembershipOfTransCmp α (fun (x : α) => Unit) cmp inst) t k) →
          @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
            @Membership.mem α (List α) (@List.instMembership α) l k →
              @Eq α
                (@Std.ExtDTreeMap.getKey! α (fun (x : α) => Unit) cmp inst inst_1
                  (@Std.ExtDTreeMap.Const.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                k) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2)

-- Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtDTreeMap.getKey! Nat (fun (x : Nat) => Unit) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd instInhabitedNat
          (@Std.ExtDTreeMap.Const.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instTransOrd (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil Nat))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 : Not
      (@Membership.mem Nat (Std.ExtDTreeMap Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtDTreeMap.instMembershipOfTransCmp Nat (fun (x : Nat) => Unit)
          (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd)
        (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
          fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α (fun (x : α) => Unit) cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : Inhabited α] {l : List α} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          Not
              (@Membership.mem α (Std.ExtDTreeMap α (fun (x : α) => Unit) cmp)
                (@Std.ExtDTreeMap.instMembershipOfTransCmp α (fun (x : α) => Unit) cmp inst) t k) →
            @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
              @Eq α
                (@Std.ExtDTreeMap.getKey! α (fun (x : α) => Unit) cmp inst inst_1
                  (@Std.ExtDTreeMap.Const.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                k) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2)

-- Std.ExtDTreeMap.Const.get_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h3.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h3.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h3.prem0 (0) HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h3.prem1 HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h3.prem2)

-- Std.ExtDTreeMap.Const.get_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            (k, v) ∈ l →
              ∀ {h : k' ∈ Std.ExtDTreeMap.Const.ofList l cmp},
                Std.ExtDTreeMap.Const.get (Std.ExtDTreeMap.Const.ofList l cmp) k' h = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) _ ([(0, 0), (0, 1)]) (0) (0) hc_k0 (0) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.get_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_ofList_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              ∀ {h : k' ∈ Std.ExtDTreeMap.Const.ofList l cmp},
                Std.ExtDTreeMap.Const.get (Std.ExtDTreeMap.Const.ofList l cmp) k' h = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) _ ([(0, 0)]) (0) (0) hc_k0 (1) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h4.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h4.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h4.prem2)

-- Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l →
            ∀ {h' : k' ∈ Std.ExtDTreeMap.Const.insertMany t l}, (Std.ExtDTreeMap.Const.insertMany t l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
            ∀ {h' : k' ∈ Std.ExtDTreeMap.Const.insertMany t l}, (Std.ExtDTreeMap.Const.insertMany t l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(Bool.false, 0)]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.Internal.List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem.h2 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : Inhabited α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' : α},
        (k == k') = Bool.true →
          Std.Internal.List.containsKey k l = Bool.false →
            List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
              k ∈ toInsert → Std.Internal.List.getKey! k' (Std.Internal.List.insertListIfNewUnit l toInsert) = k := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) (instInhabitedNat) ([]) ([1, 0]) (1) (1) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem.h8 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited α] {l : List ((_ : α) × Unit)}
        {toInsert : List α} {k k' : α},
        Std.Internal.List.containsKey k l = Bool.false →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
            k ∈ toInsert → Std.Internal.List.getKey! k' (Std.Internal.List.insertListIfNewUnit l toInsert) = k := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) ([1]) (1) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem.h10 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited α] {l : List ((_ : α) × Unit)}
        {toInsert : List α} {k k' : α},
        (k == k') = Bool.true →
          Std.Internal.List.containsKey k l = Bool.false →
            k ∈ toInsert → Std.Internal.List.getKey! k' (Std.Internal.List.insertListIfNewUnit l toInsert) = k := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) (instInhabitedNat) ([]) ([0, 1]) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem.h11 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] [inst_2 : Inhabited α] {l : List ((_ : α) × Unit)}
        {toInsert : List α} {k k' : α},
        (k == k') = Bool.true →
          Std.Internal.List.containsKey k l = Bool.false →
            List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
              Std.Internal.List.getKey! k' (Std.Internal.List.insertListIfNewUnit l toInsert) = k := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) ([]) _ (1) (beq_self_eq_true _) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.ExtTreeMap.getElem!_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h4.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst : Inhabited β],
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h4.prem0 (0) (instInhabitedNat) HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h4.prem2)

-- Std.ExtTreeMap.getElem!_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h8.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 1)])[1]! = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 1)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h8.prem1 : (0, 1) ∈ [(0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α} {v : β} [inst_1 : Inhabited β],
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → (t.insertMany l)[k']! = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 1)]) (0) (1) (1) (instInhabitedNat) HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h8.prem0 HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h8.prem1)

-- Std.ExtTreeMap.getElem!_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h11.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0), (0, 1)])[0]! = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h11.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h11 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α}, cmp k k' = Ordering.eq → ∀ {v : β} [inst_1 : Inhabited β], (k, v) ∈ l → (t.insertMany l)[k']! = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h11.prem0 (0) (instInhabitedNat) HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h11.prem1)

-- Std.ExtTreeMap.getElem!_insertMany_list_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h12.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [])[0]! = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h12.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h12.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h12 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst_1 : Inhabited β],
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (t.insertMany l)[k']! = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h12.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h12.prem0 (1) (instInhabitedNat) HypCheckProof.Std.ExtTreeMap.getElem!_insertMany_list_of_mem.h12.prem1)

-- Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} {l : List α} {k k' : α} {fallback : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([0]) (0) (0) (0) HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst : Not
      (@Eq Nat
        (@Std.ExtTreeMap.getKeyD Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
          (@Std.ExtTreeMap.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
            (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 : Not
      (@Membership.mem Nat (Std.ExtTreeMap Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtTreeMap.instMembershipOfTransCmp Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd)
        (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2 : @Membership.mem Nat (List Nat) (@List.instMembership Nat)
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : @Std.TransCmp α cmp] {l : List α}
        {k k' fallback : α},
        Not (@Membership.mem α (Std.ExtTreeMap α Unit cmp) (@Std.ExtTreeMap.instMembershipOfTransCmp α Unit cmp inst) t k) →
          @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
            @Membership.mem α (List α) (@List.instMembership α) l k →
              @Eq α
                (@Std.ExtTreeMap.getKeyD α Unit cmp inst
                  (@Std.ExtTreeMap.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k' fallback)
                k) := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2)

-- Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtTreeMap.getKeyD Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
          (@Std.ExtTreeMap.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
            (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil Nat))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 : Not
      (@Membership.mem Nat (Std.ExtTreeMap Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtTreeMap.instMembershipOfTransCmp Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd)
        (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : @Std.TransCmp α cmp] {l : List α}
        {k k' fallback : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          Not
              (@Membership.mem α (Std.ExtTreeMap α Unit cmp) (@Std.ExtTreeMap.instMembershipOfTransCmp α Unit cmp inst) t
                k) →
            @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
              @Eq α
                (@Std.ExtTreeMap.getKeyD α Unit cmp inst
                  (@Std.ExtTreeMap.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k' fallback)
                k) := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 HypCheckProof.Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2)

-- Std.ExtTreeMap.getD_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h4.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} {fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h4.prem0 (0) (0) HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h4.prem2)

-- Std.ExtTreeMap.getD_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h8.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0)]).getD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h8.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α} {v fallback : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → (t.insertMany l).getD k' fallback = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (0) (1) HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h8.prem0 HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h8.prem1)

-- Std.ExtTreeMap.getD_insertMany_list_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h12.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany []).getD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h12.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h12.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h12 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (t.insertMany l).getD k' fallback = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h12.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h12.prem0 (0) (1) HypCheckProof.Std.ExtTreeMap.getD_insertMany_list_of_mem.h12.prem1)

-- Std.ExtTreeMap.getElem_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h3.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h3.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h3 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h3.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h3.prem0 (0) HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h3.prem2)

-- Std.ExtTreeMap.getElem_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, (k, v) ∈ l → ∀ {h : k' ∈ Std.ExtTreeMap.ofList l cmp}, (Std.ExtTreeMap.ofList l cmp)[k'] = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ ([(0, 0), (0, 1)]) (0) (0) hc_k0 (0) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtTreeMap.getElem_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeMap.getElem_ofList_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              ∀ {h : k' ∈ Std.ExtTreeMap.ofList l cmp}, (Std.ExtTreeMap.ofList l cmp)[k'] = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ ([(0, 0)]) (0) (0) hc_k0 (1) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Inhabited α] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) ([0]) (0) (0) HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h8.inst : ¬((Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [1]).get! 0 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h8.prem0 : ¬1 ∈ Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h8.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [1] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h8.prem2 : 1 ∈ [1] := by
  decide
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Inhabited α]
        {l : List α} {k k' : α},
        ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get! k' = k := fun hc_h => HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([1]) (1) (0) HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h8.prem0 HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h8.prem1 HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h8.prem2)

-- Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Inhabited α]
        {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get! k' = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtTreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) ([Bool.false]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h11.inst : ¬((Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany []).get! 1 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 1 1 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h11.prem1 : ¬1 ∈ Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h11.prem2 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] [inst_1 : Inhabited α]
        {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (t.insertMany l).get! k' = k := fun hc_h => HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([]) (1) (1) HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h11.prem0 HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h11.prem1 HypCheckProof.Std.ExtTreeSet.get!_insertMany_list_of_not_mem_of_mem.h11.prem2)

-- Std.Internal.List.maxKey!_eraseKey_eq_of_beq_maxKey!_eq_false, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey!_eraseKey_eq_of_beq_maxKey!_eq_false.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α},
            (Std.Internal.List.eraseKey k l).isEmpty = Bool.false →
              Std.Internal.List.maxKey! (Std.Internal.List.eraseKey k l) = Std.Internal.List.maxKey! l := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.getKey?_insertListConst_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey?_insertListConst_of_mem.h9 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
              k ∈ List.map Prod.fst toInsert →
                Std.Internal.List.getKey? k' (Std.Internal.List.insertListConst l toInsert) = Option.some k := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([(0, 0)]) (by
  simp) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKey?_insertListConst_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey?_insertListConst_of_mem.h11 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × β)} {toInsert : List (α × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k k' : α},
            (k == k') = Bool.true →
              List.Pairwise (fun (a b : α × β) => (a.fst == b.fst) = Bool.false) toInsert →
                Std.Internal.List.getKey? k' (Std.Internal.List.insertListConst l toInsert) = Option.some k := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ ([]) ([]) (by
  simp) _ (0) (beq_self_eq_true _) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.maxKeyD_eq_iff_mem_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_eq_iff_mem_and_forall.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          l.isEmpty = Bool.false →
            ∀ {km fallback : α},
              Std.Internal.List.maxKeyD l fallback = km ↔
                Std.Internal.List.containsKey km l = Bool.true ∧
                  ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (instOrdBool) _ (⟨fun _ _ => true⟩ : BEq Bool) _ ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Bool) (fun (a : Bool) => Nat) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (@List.cons (@Sigma Bool fun (a : Bool) => (fun (a : Bool) => Nat) a)
      (@Sigma.mk Bool (fun (a : Bool) => (fun (a : Bool) => Nat) a) Bool.false
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Bool fun (a : Bool) => (fun (a : Bool) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Std.Internal.List.maxKeyD_eq_iff_mem_and_forall, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_eq_iff_mem_and_forall.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km fallback : α},
            Std.Internal.List.maxKeyD l fallback = km ↔
              Std.Internal.List.containsKey km l = Bool.true ∧
                ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.maxKey_modifyKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_modifyKey.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {k : α} {f : β k → β k} {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (0) (fun n => n + 1 : Nat → Nat) ([]) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.maxKey_modifyKey, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_modifyKey.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] {k : α} {f : β k → β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → (Std.Internal.List.modifyKey k f l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ (0) (fun n => n + 1 : Nat → Nat) ([]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.minKey_alterKey_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_alterKey_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : Option (β k) → Option (β k)}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey_alterKey_eq_self, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_alterKey_eq_self.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option (β k) → Option (β k)}, (Std.Internal.List.alterKey k f l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  decide +kernel)

-- Std.Internal.List.minKeyD_eraseKey_eq_of_beq_minKeyD_eq_false, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_eraseKey_eq_of_beq_minKeyD_eq_false.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k fallback : α},
            (Std.Internal.List.eraseKey k l).isEmpty = Bool.false →
              Std.Internal.List.minKeyD (Std.Internal.List.eraseKey k l) fallback = Std.Internal.List.minKeyD l fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.minKey!_eq_iff_mem_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_eq_iff_mem_and_forall.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          l.isEmpty = Bool.false →
            ∀ {km : α},
              Std.Internal.List.minKey! l = km ↔
                Std.Internal.List.containsKey km l = Bool.true ∧
                  ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a != b⟩ : BEq Nat) _ (instInhabitedNat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.minKey!_eq_iff_mem_and_forall, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_eq_iff_mem_and_forall.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Std.LawfulEqOrd α] [inst_5 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {km : α},
            Std.Internal.List.minKey! l = km ↔
              Std.Internal.List.containsKey km l = Bool.true ∧
                ∀ (k : α), Std.Internal.List.containsKey k l = Bool.true → (Ord.compare km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ (instInhabitedNat) ([]) (by
  simp) (0)) (by
  (simp <;> decide))

-- Std.Internal.List.minKeyD_insertEntry_of_isEmpty, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntry_of_isEmpty.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {fallback : α}, Std.Internal.List.minKeyD (Std.Internal.List.insertEntry k v l) fallback = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (1) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.Internal.List.Const.maxKeyD_modifyKey, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKeyD_modifyKey.h10 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : β → β} {fallback : α},
            Std.Internal.List.maxKeyD (Std.Internal.List.Const.modifyKey k f l) fallback =
              if (Std.Internal.List.maxKeyD l fallback == k) = Bool.true then k else Std.Internal.List.maxKeyD l fallback := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => .eq⟩ : Ord Bool) (@Std.TransCmp.mk (Bool) (@Ord.compare Bool (@Ord.mk Bool fun (x x_1 : Bool) => Ordering.eq)) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (⟨fun _ _ => true⟩ : BEq Bool) (@Std.LawfulBEqCmp.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (@Ord.compare Bool (@Ord.mk Bool fun (x x_1 : Bool) => Ordering.eq)) (by (try dsimp only);   decide)) ([]) (by
  simp) (Bool.false) (fun n => n + 1 : Nat → Nat) (Bool.true)) (by
  decide +kernel)

-- Std.ExtDTreeMap.getD_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_insertMany_list_of_contains_eq_false.h4 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.LawfulEqCmp α cmp]
        [inst : BEq α] [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α}
        {fallback : β k},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Std.TransCmp α cmp) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.getD_insertMany_list_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_insertMany_list_of_contains_eq_false.h5 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst : BEq α] [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α}
        {fallback : β k},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Std.LawfulEqCmp α cmp) := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.ExtDTreeMap.ofList Bool (fun (a : Bool) => Nat) (@List.nil (@Sigma Bool fun (a : Bool) => Nat))
      fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (⟨fun _ _ => true⟩ : BEq Bool) (@Std.LawfulBEqCmp.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (@List.nil (@Sigma Bool fun (a : Bool) => (fun (a : Bool) => Nat) a)) (Bool.false) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
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

-- Std.ExtDTreeMap.getD_insertMany_list_of_contains_eq_false, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getD_insertMany_list_of_contains_eq_false.h11 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : Std.LawfulEqCmp cmp] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α}
        {fallback : β k}, (t.insertMany l).getD k fallback = t.getD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getD_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h3.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h3.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} {fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h3.prem0 (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h3.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h3.prem2)

-- Std.ExtDTreeMap.Const.getD_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h7.inst : ¬Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h7.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α}
        {v fallback : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.ofList l cmp) k' fallback = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([(0, 0)]) (0) (1) (0) (1) HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h7.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h7.prem1)

-- Std.ExtDTreeMap.Const.getD_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h10.inst : ¬Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b) 0 0 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h10.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β}, (k, v) ∈ l → Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.ofList l cmp) k' fallback = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h10.prem0 (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h10.prem1)

-- Std.ExtDTreeMap.Const.getD_ofList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h11.inst : ¬Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.ofList [] fun (a b : Nat) => Ord.compare a b) 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              Std.ExtDTreeMap.Const.getD (Std.ExtDTreeMap.Const.ofList l cmp) k' fallback = v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h11.prem0 (0) (1) HypCheckProof.Std.ExtDTreeMap.Const.getD_ofList_of_mem.h11.prem1)

-- Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h4.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h4.prem0 (0) HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h4.prem2)

-- Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h8.inst : ¬Std.ExtDTreeMap.Const.get?
          (Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0)]) 1 =
        Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h8.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α} {v : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → Std.ExtDTreeMap.Const.get? (Std.ExtDTreeMap.Const.insertMany t l) k' = Option.some v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (0) HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h8.prem0 HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h8.prem1)

-- Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h10.inst : ¬Std.ExtDTreeMap.Const.get?
          (Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0), (0, 1)])
          0 =
        Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h10.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β}, (k, v) ∈ l → Std.ExtDTreeMap.Const.get? (Std.ExtDTreeMap.Const.insertMany t l) k' = Option.some v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h10.prem0 (0) HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h10.prem1)

-- Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h11.inst : ¬Std.ExtDTreeMap.Const.get?
          (Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) []) 0 =
        Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              Std.ExtDTreeMap.Const.get? (Std.ExtDTreeMap.Const.insertMany t l) k' = Option.some v := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h11.prem0 (0) HypCheckProof.Std.ExtDTreeMap.Const.get?_insertMany_list_of_mem.h11.prem1)

-- Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h4.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} {l : List (α × β)}
        {k k' : α} {fallback : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h4.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h4.prem2)

-- Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.inst : ¬(Std.ExtDTreeMap.Const.insertMany (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0)]).getKeyD 1
          1 =
        0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.prem1 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' fallback : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l → (Std.ExtDTreeMap.Const.insertMany t l).getKeyD k' fallback = k := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (1) HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.prem1)

-- Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtDTreeMap.getKeyD Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd
          (@Std.ExtDTreeMap.Const.insertMany Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat Nat.instTransOrd
            (List (Prod Nat Nat))
            (@instForInOfForIn' Id (List (Prod Nat Nat)) (Prod Nat Nat)
              (@inferInstance (Membership (Prod Nat Nat) (List (Prod Nat Nat))) (@List.instMembership (Prod Nat Nat)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod Nat Nat) Id.instMonad))
            (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (Prod Nat Nat)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h11 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : @Std.TransCmp α cmp] {l : List (Prod α β)} {k k' fallback : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α
              (@Std.ExtDTreeMap.getKeyD α (fun (x : α) => β) cmp inst
                (@Std.ExtDTreeMap.Const.insertMany α cmp β inst (List (Prod α β))
                  (@instForInOfForIn' Id (List (Prod α β)) (Prod α β)
                    (@inferInstance (Membership (Prod α β) (List (Prod α β))) (@List.instMembership (Prod α β)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod α β) Id.instMonad))
                  t l)
                k' fallback)
              k) := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) (@Std.ExtDTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.prem1)

-- Std.ExtDTreeMap.get!_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.get!_insertMany_list_of_contains_eq_false.h4 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.LawfulEqCmp α cmp]
        [inst : BEq α] [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α}
        [inst_2 : Inhabited (β k)],
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Std.TransCmp α cmp) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instInhabitedNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtTreeMap.getElem!_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h3.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h3.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h3 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst : Inhabited β],
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h3.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h3.prem0 (0) (instInhabitedNat) HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h3.prem2)

-- Std.ExtTreeMap.getElem!_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h7.inst : ¬(Std.ExtTreeMap.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b)[1]! = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 1)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h7.prem1 : (0, 1) ∈ [(0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α} {v : β}
        [inst_1 : Inhabited β],
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → (Std.ExtTreeMap.ofList l cmp)[k']! = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h7.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([(0, 1)]) (0) (1) (1) (instInhabitedNat) HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h7.prem0 HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h7.prem1)

-- Std.ExtTreeMap.getElem!_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h10.inst : ¬(Std.ExtTreeMap.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b)[0]! = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h10.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq → ∀ {v : β} [inst_1 : Inhabited β], (k, v) ∈ l → (Std.ExtTreeMap.ofList l cmp)[k']! = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h10.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h10.prem0 (0) (instInhabitedNat) HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h10.prem1)

-- Std.ExtTreeMap.getElem!_ofList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h11.inst : ¬(Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b)[0]! = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h11 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst_1 : Inhabited β],
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (Std.ExtTreeMap.ofList l cmp)[k']! = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h11.prem0 (1) (instInhabitedNat) HypCheckProof.Std.ExtTreeMap.getElem!_ofList_of_mem.h11.prem1)

-- Std.ExtTreeMap.getD_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h3.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h3.prem2 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h3 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} {fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h3.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h3.prem0 (0) (0) HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h3.prem2)

-- Std.ExtTreeMap.getD_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h7.inst : ¬(Std.ExtTreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b).getD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h7.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α} {v fallback : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → (Std.ExtTreeMap.ofList l cmp).getD k' fallback = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h7.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (0) (1) HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h7.prem0 HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h7.prem1)

-- Std.ExtTreeMap.getD_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h10.inst : ¬(Std.ExtTreeMap.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b).getD 0 0 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h10.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq → ∀ {v fallback : β}, (k, v) ∈ l → (Std.ExtTreeMap.ofList l cmp).getD k' fallback = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h10.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h10.prem0 (0) (0) HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h10.prem1)

-- Std.ExtTreeMap.getD_ofList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h11.inst : ¬(Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).getD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h11 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (Std.ExtTreeMap.ofList l cmp).getD k' fallback = v := fun hc_h => HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h11.prem0 (0) (1) HypCheckProof.Std.ExtTreeMap.getD_ofList_of_mem.h11.prem1)

-- Std.ExtTreeMap.getKeyD_insertMany_list_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h4.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h4.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h4.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h4.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} {l : List (α × β)} {k k' : α} {fallback : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h4.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([(0, 0)]) (0) (0) (0) HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h4.prem0 HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h4.prem1 HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h4.prem2)

-- Std.ExtTreeMap.getKeyD_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h9.inst : ¬((Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0)]).getKeyD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h9.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h9.prem1 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' fallback : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l → (t.insertMany l).getKeyD k' fallback = k := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h9.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (1) HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h9.prem0 HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h9.prem1)

-- Std.ExtTreeMap.getKeyD_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.ExtTreeMap.getKeyD Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
          (@Std.ExtTreeMap.insertMany Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
            (List (Prod Nat Nat))
            (@instForInOfForIn' Id (List (Prod Nat Nat)) (Prod Nat Nat)
              (@inferInstance (Membership (Prod Nat Nat) (List (Prod Nat Nat))) (@List.instMembership (Prod Nat Nat)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod Nat Nat) Id.instMonad))
            (@Std.ExtTreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (Prod Nat Nat)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h11.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h11 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        {l : List (Prod α β)} {k k' fallback : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α
              (@Std.ExtTreeMap.getKeyD α β cmp inst
                (@Std.ExtTreeMap.insertMany α β cmp inst (List (Prod α β))
                  (@instForInOfForIn' Id (List (Prod α β)) (Prod α β)
                    (@inferInstance (Membership (Prod α β) (List (Prod α β))) (@List.instMembership (Prod α β)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod α β) Id.instMonad))
                  t l)
                k' fallback)
              k) := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtTreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h11.prem0 HypCheckProof.Std.ExtTreeMap.getKeyD_insertMany_list_of_mem.h11.prem1)

-- Std.Internal.List.minKeyD_insertEntry_le_minKeyD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntry_le_minKeyD.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          l.isEmpty = Bool.false →
            ∀ {k : α} {v : β k} {fallback : α},
              (Ord.compare (Std.Internal.List.minKeyD (Std.Internal.List.insertEntry k v l) fallback)
                    (Std.Internal.List.minKeyD l fallback)).isLE =
                Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (0) (0)) (by
  decide +kernel)

-- Std.Internal.List.minKeyD_insertEntry_le_minKeyD, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntry_le_minKeyD.h8 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {v : β k} {fallback : α},
            (Ord.compare (Std.Internal.List.minKeyD (Std.Internal.List.insertEntry k v l) fallback)
                  (Std.Internal.List.minKeyD l fallback)).isLE =
              Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (1) (0) (0)) (by
  decide +kernel)

-- Std.Internal.List.minKey!_insertEntry_of_isEmpty, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntry_of_isEmpty.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → Std.Internal.List.minKey! (Std.Internal.List.insertEntry k v l) = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) (1) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.Const.minKeyD_modifyKey_eq_minKeyD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKeyD_modifyKey_eq_minKeyD.h5 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : β → β} {fallback : α},
            Std.Internal.List.minKeyD (Std.Internal.List.Const.modifyKey k f l) fallback =
              Std.Internal.List.minKeyD l fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (1) (fun n => n + 1 : Nat → Nat) (0)) (by
  decide +kernel)

-- Std.Internal.List.Const.maxKey!_modifyKey_eq_maxKey!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey!_modifyKey_eq_maxKey!.h5 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        [inst_4 : Inhabited α] {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : β → β},
            Std.Internal.List.maxKey! (Std.Internal.List.Const.modifyKey k f l) = Std.Internal.List.maxKey! l := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (instInhabitedNat) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (1) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.Internal.List.Const.maxKey!_alterKey_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey!_alterKey_eq_self.h5 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Inhabited α]
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option β → Option β},
            (Std.Internal.List.Const.alterKey k f l).isEmpty = Bool.false →
              (Std.Internal.List.maxKey! (Std.Internal.List.Const.alterKey k f l) = k ↔
                (f (Std.Internal.List.getValue? k l)).isSome = Bool.true ∧
                  ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k' k).isLE = Bool.true) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (⟨fun a b => a != b⟩ : BEq Nat) (instInhabitedNat) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (0) (fun (a : Option Nat) => Option.none) (by
  decide)) (by
  (simp <;> decide))

-- Std.Internal.List.Const.maxKey!_alterKey_eq_self, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKey!_alterKey_eq_self.h11 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option β → Option β},
            Std.Internal.List.maxKey! (Std.Internal.List.Const.alterKey k f l) = k ↔
              (f (Std.Internal.List.getValue? k l)).isSome = Bool.true ∧
                ∀ (k' : α), Std.Internal.List.containsKey k' l = Bool.true → (Ord.compare k' k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) (by
  simp) (0) (fun (a : Option Nat) => Option.none)) (by
  (simp <;> decide))

-- Std.Internal.List.maxKey!_le_maxKey!_insertEntry, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey!_le_maxKey!_insertEntry.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Inhabited α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          l.isEmpty = Bool.false →
            ∀ {k : α} {v : β k},
              (Ord.compare (Std.Internal.List.maxKey! l)
                    (Std.Internal.List.maxKey! (Std.Internal.List.insertEntry k v l))).isLE =
                Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (instInhabitedNat) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (0)) (by
  decide +kernel)

-- Std.Internal.List.maxKey!_le_maxKey!_insertEntry, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey!_le_maxKey!_insertEntry.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {v : β k},
            (Ord.compare (Std.Internal.List.maxKey! l)
                  (Std.Internal.List.maxKey! (Std.Internal.List.insertEntry k v l))).isLE =
              Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => compare b a⟩ : Ord Nat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) (by
  simp) (1) (0)) (by
  decide +kernel)

-- Std.Internal.List.Const.maxKeyD_modifyKey_eq_maxKeyD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.maxKeyD_modifyKey_eq_maxKeyD.h5 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : β → β} {fallback : α},
            Std.Internal.List.maxKeyD (Std.Internal.List.Const.modifyKey k f l) fallback =
              Std.Internal.List.maxKeyD l fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (1) (fun n => n + 1 : Nat → Nat) (0)) (by
  decide +kernel)

-- Std.Internal.List.minKeyD_insertEntryIfNew_of_isEmpty, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKeyD_insertEntryIfNew_of_isEmpty.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {fallback : α}, Std.Internal.List.minKeyD (Std.Internal.List.insertEntryIfNew k v l) fallback = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (1) (0) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.Internal.List.maxKeyD_modifyKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_modifyKey.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α} {f : β k → β k} {fallback : α}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ ([]) (by
  simp) (0) (fun n => n + 1 : Nat → Nat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.beqModel_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.beqModel_congr.h3 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : (k : α) → BEq (β k)]
        {l₁ l₂ l₃ l₄ : List (@Sigma α fun (a : α) => β a)},
        @Std.Internal.List.DistinctKeys α β inst l₂ →
          @List.Perm (@Sigma α fun (a : α) => β a) l₁ l₃ →
            @List.Perm (@Sigma α fun (a : α) => β a) l₂ l₄ → @LawfulBEq α inst) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (fun (k : Nat) => @instBEqOfDecidableEq Nat instDecidableEqNat) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (by
  simp) (by
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

-- Std.Internal.List.beqModel_congr, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.beqModel_congr.h10 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @LawfulBEq α inst] [inst_2 : (k : α) → BEq (β k)]
        {l₁ l₂ l₃ l₄ : List (@Sigma α fun (a : α) => β a)},
        @Std.Internal.List.DistinctKeys α β inst l₂ →
          @List.Perm (@Sigma α fun (a : α) => β a) l₂ l₄ →
            @Eq Bool (@Std.Internal.List.beqModel α β inst inst_1 inst_2 l₁ l₂)
              (@Std.Internal.List.beqModel α β inst inst_1 inst_2 l₃ l₄)) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (fun (k : Nat) => @instBEqOfDecidableEq Nat instDecidableEqNat) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.beqModel_congr, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.beqModel_congr.h11 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @LawfulBEq α inst] [inst_2 : (k : α) → BEq (β k)]
        {l₁ l₂ l₃ l₄ : List (@Sigma α fun (a : α) => β a)},
        @Std.Internal.List.DistinctKeys α β inst l₂ →
          @List.Perm (@Sigma α fun (a : α) => β a) l₁ l₃ →
            @Eq Bool (@Std.Internal.List.beqModel α β inst inst_1 inst_2 l₁ l₂)
              (@Std.Internal.List.beqModel α β inst inst_1 inst_2 l₃ l₄)) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (fun (k : Nat) => @instBEqOfDecidableEq Nat instDecidableEqNat) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.minKey!_insertEntryIfNew_le_minKey!, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey!_insertEntryIfNew_le_minKey!.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {v : β k},
            (Ord.compare (Std.Internal.List.minKey! (Std.Internal.List.insertEntryIfNew k v l))
                  (Std.Internal.List.minKey! l)).isLE =
              Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) (by
  simp) (1) (0)) (by
  decide +kernel)

-- Std.Internal.List.maxKey!_le_maxKey!_insertEntryIfNew, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey!_le_maxKey!_insertEntryIfNew.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {v : β k},
            (Ord.compare (Std.Internal.List.maxKey! l)
                  (Std.Internal.List.maxKey! (Std.Internal.List.insertEntryIfNew k v l))).isLE =
              Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => compare b a⟩ : Ord Nat) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) (by
  simp) (1) (0)) (by
  decide +kernel)

-- Std.Internal.List.minKey?_insertEntry_le_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_le_self.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {k : α} {v : β k}
        {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → ∀ {kmi : α}, Std.TransOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Ord.compare Nat
      (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) ([]) (by
  simp) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey?_insertEntry_le_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_le_self.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {k : α} {v : β k}
        {l : List ((a : α) × β a)}, Std.Internal.List.DistinctKeys l → ∀ {kmi : α}, Std.LawfulBEqOrd α := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) ([]) (by
  simp) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Internal.List.minKey?_insertEntry_le_self, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey?_insertEntry_le_self.h11 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {k : α} {v : β k} {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {kmi : α}, (Ord.compare kmi k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ (0) (0) ([]) (by
  simp) (1)) (by
  decide +kernel)

-- Std.Internal.List.Const.minKey!_modifyKey, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey!_modifyKey.h11 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst_4 : Inhabited α] {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : β → β},
            Std.Internal.List.minKey! (Std.Internal.List.Const.modifyKey k f l) =
              if (Std.Internal.List.minKey! l == k) = Bool.true then k else Std.Internal.List.minKey! l := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => .eq⟩ : Ord Bool) (@Std.TransCmp.mk (Bool) (@Ord.compare Bool (@Ord.mk Bool fun (x x_1 : Bool) => Ordering.eq)) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (⟨fun _ _ => true⟩ : BEq Bool) (@Std.LawfulBEqCmp.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (@Ord.compare Bool (@Ord.mk Bool fun (x x_1 : Bool) => Ordering.eq)) (by (try dsimp only);   decide)) (instInhabitedBool) ([]) (by
  simp) (Bool.true) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKey_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_ofList_of_mem.h3 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
            k ∈ List.map Sigma.fst l → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.getKey_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_ofList_of_mem.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Sigma.fst l →
            ∀ {h' : k' ∈ Std.ExtDTreeMap.ofList l cmp}, (Std.ExtDTreeMap.ofList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKey_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          k ∈ List.map Sigma.fst l →
            ∀ {h' : k' ∈ Std.ExtDTreeMap.ofList l cmp}, (Std.ExtDTreeMap.ofList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a), (⟨Bool.true, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.ExtDTreeMap.getKey_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.getKey_ofList_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
            ∀ {h' : k' ∈ Std.ExtDTreeMap.ofList l cmp}, (Std.ExtDTreeMap.ofList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.Internal.List.getValueCast_insertList_of_contains_eq_false_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_insertList_of_contains_eq_false_left.h3 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] {l toInsert : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Std.Internal.List.DistinctKeys α β inst l →
          @Std.Internal.List.DistinctKeys α β inst toInsert →
            @Eq Bool (@Std.Internal.List.containsKey α β inst k (@Std.Internal.List.insertList α β inst l toInsert))
                Bool.true →
              @Eq Bool (@Std.Internal.List.containsKey α β inst k l) Bool.false → @LawfulBEq α inst) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
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

-- Std.Internal.List.getValueCast_insertList_of_contains_eq_false_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_insertList_of_contains_eq_false_left.h9 : Not
      (∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : @LawfulBEq α inst]
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

-- Std.Internal.List.getValueCast_insertList_of_contains_eq_false_left, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getValueCast_insertList_of_contains_eq_false_left.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l toInsert : List ((a : α) × β a)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert →
            Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true →
              Std.Internal.List.containsKey k l = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([]) (0) (by
  simp) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey_ofList_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h3.prem1 : List.Pairwise
      (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a.fst b.fst = Ordering.eq)
      [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h3.prem2 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → k ∈ List.map Prod.fst l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Nat) ([(0, 0)]) (0) (0) HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h3.prem0 HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h3.prem1 HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h3.prem2)

-- Std.ExtDTreeMap.Const.getKey_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_ofList_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
            ∀ {h' : k' ∈ Std.ExtDTreeMap.Const.ofList l cmp}, (Std.ExtDTreeMap.Const.ofList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(Bool.false, 0)]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.Internal.List.maxKey_of_perm, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_of_perm.h8 : Not
      (∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : @Std.TransOrd α inst] [inst_2 : BEq α]
        [inst : @Std.LawfulBEqOrd α inst_2 inst] {l l' : List (@Sigma α fun (a : α) => β a)},
        @Std.Internal.List.DistinctKeys α β inst_2 l →
          @List.Perm (@Sigma α fun (a : α) => β a) l l' →
            @Eq Bool (@List.isEmpty (@Sigma α fun (a : α) => β a) l) Bool.false) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.maxKey_of_perm, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_of_perm.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {l l' : List ((a : α) × β a)} {hl : l.isEmpty = Bool.false}, Std.Internal.List.DistinctKeys l → l.Perm l' := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.getKey_insertList_of_contains_left_of_contains_right_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey_insertList_of_contains_left_of_contains_right_eq_false.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {l toInsert : List ((a : α) × β a)} {k : α}
        {m : Std.Internal.List.containsKey k (Std.Internal.List.insertList l toInsert) = Bool.true},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.DistinctKeys toInsert → Std.Internal.List.containsKey k l = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.perm_of_beqModel, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.perm_of_beqModel.h10 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : LawfulBEq α] [inst_2 : (k : α) → BEq (β k)]
        [inst_3 : ∀ (k : α), LawfulBEq (β k)] {l₁ l₂ : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l₁ → Std.Internal.List.DistinctKeys l₂ → l₁.Perm l₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ (fun (k : Nat) => instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.minKey_eraseKey_eq_of_beq_minKey_eq_false, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_eraseKey_eq_of_beq_minKey_eq_false.h3 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqOrd α] {l : List ((a : α) × β a)},
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

-- Std.Internal.List.minKey_eraseKey_eq_of_beq_minKey_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_eraseKey_eq_of_beq_minKey_eq_false.h5 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] {l : List ((a : α) × β a)},
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

-- Std.Internal.List.minKey_eraseKey_eq_of_beq_minKey_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_eraseKey_eq_of_beq_minKey_eq_false.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {k : α}, (Std.Internal.List.eraseKey k l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.Internal.List.minKey_eraseKey_eq_of_beq_minKey_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_eraseKey_eq_of_beq_minKey_eq_false.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)} (hd : Std.Internal.List.DistinctKeys l) {k : α}
        {he : (Std.Internal.List.eraseKey k l).isEmpty = Bool.false},
        Std.Internal.List.minKey (Std.Internal.List.eraseKey k l) he =
          Std.Internal.List.minKey l (Std.Internal.List.isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) hc_k0 (0) hc_k1) (by
  (simp <;> decide))

-- Std.Internal.List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' : α},
        (k == k') = Bool.true →
          Std.Internal.List.containsKey k l = Bool.false →
            List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
              k ∈ toInsert → Std.Internal.List.getKey? k' (Std.Internal.List.insertListIfNewUnit l toInsert) = Option.some k := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([]) ([1, 0]) (1) (1) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem.h7 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' : α},
        Std.Internal.List.containsKey k l = Bool.false →
          List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
            k ∈ toInsert → Std.Internal.List.getKey? k' (Std.Internal.List.insertListIfNewUnit l toInsert) = Option.some k := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0]) (0) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem.h9 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' : α},
        (k == k') = Bool.true →
          Std.Internal.List.containsKey k l = Bool.false →
            k ∈ toInsert → Std.Internal.List.getKey? k' (Std.Internal.List.insertListIfNewUnit l toInsert) = Option.some k := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ([]) ([0, 1]) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem.h10 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : EquivBEq α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k k' : α},
        (k == k') = Bool.true →
          Std.Internal.List.containsKey k l = Bool.false →
            List.Pairwise (fun (a b : α) => (a == b) = Bool.false) toInsert →
              Std.Internal.List.getKey? k' (Std.Internal.List.insertListIfNewUnit l toInsert) = Option.some k := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([]) _ (0) (beq_self_eq_true _) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.minKey_of_perm, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_of_perm.h8 : Not
      (∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : @Std.TransOrd α inst] [inst_2 : BEq α]
        [inst : @Std.LawfulBEqOrd α inst_2 inst] {l l' : List (@Sigma α fun (a : α) => β a)},
        @Std.Internal.List.DistinctKeys α β inst_2 l →
          @List.Perm (@Sigma α fun (a : α) => β a) l l' →
            @Eq Bool (@List.isEmpty (@Sigma α fun (a : α) => β a) l) Bool.false) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.minKey_of_perm, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.minKey_of_perm.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {l l' : List ((a : α) × β a)} {hl : l.isEmpty = Bool.false}, Std.Internal.List.DistinctKeys l → l.Perm l' := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) ([]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp)) (by
  decide +kernel)

-- Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([0]) (0) (0) HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.inst : Not
      (@Eq (Option Nat)
        (@Std.ExtTreeMap.getKey? Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
          (@Std.ExtTreeMap.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
            (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem0 : Not
      (@Membership.mem Nat (Std.ExtTreeMap Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtTreeMap.instMembershipOfTransCmp Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd)
        (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem1 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem2 : @Membership.mem Nat (List Nat) (@List.instMembership Nat)
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : @Std.TransCmp α cmp] {l : List α}
        {k k' : α},
        Not (@Membership.mem α (Std.ExtTreeMap α Unit cmp) (@Std.ExtTreeMap.instMembershipOfTransCmp α Unit cmp inst) t k) →
          @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
            @Membership.mem α (List α) (@List.instMembership α) l k →
              @Eq (Option α)
                (@Std.ExtTreeMap.getKey? α Unit cmp inst
                  (@Std.ExtTreeMap.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                (@Option.some α k)) := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem0 HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem1 HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem2)

-- Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.inst : Not
      (@Eq (Option Nat)
        (@Std.ExtTreeMap.getKey? Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
          (@Std.ExtTreeMap.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat.instTransOrd
            (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil Nat))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem1 : Not
      (@Membership.mem Nat (Std.ExtTreeMap Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.ExtTreeMap.instMembershipOfTransCmp Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          Nat.instTransOrd)
        (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem2 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeMap α Unit cmp} [inst : @Std.TransCmp α cmp] {l : List α}
        {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          Not
              (@Membership.mem α (Std.ExtTreeMap α Unit cmp) (@Std.ExtTreeMap.instMembershipOfTransCmp α Unit cmp inst) t
                k) →
            @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
              @Eq (Option α)
                (@Std.ExtTreeMap.getKey? α Unit cmp inst
                  (@Std.ExtTreeMap.insertManyIfNewUnit α cmp inst (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                (@Option.some α k)) := fun hc_h => HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.ExtTreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem0 HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem1 HypCheckProof.Std.ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem2)

-- Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h3.inst : ¬Std.TransCmp fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h3.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h3.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) a b = Ordering.eq)
      [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h3.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → Std.TransCmp cmp := fun hc_h => HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h3.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) ([0]) (0) (0) HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h3.prem0 HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h3.prem1 HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h3.prem2)

-- Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.inst : ¬((Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [0]).get? 1 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem0 : ¬0 ∈ Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        ¬k ∈ t →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get? k' = Option.some k := fun hc_h => HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (1) HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem0 HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem1 HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem2)

-- Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get? k' = Option.some k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtTreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.inst : ¬((Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany []).get? 0 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem1 : ¬0 ∈ Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem2 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.ExtTreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (t.insertMany l).get? k' = Option.some k := fun hc_h => HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.ExtTreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem0 HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem1 HypCheckProof.Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem2)

-- Std.Internal.List.DistinctKeys.eq_of_mem_of_beq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.DistinctKeys.eq_of_mem_of_beq.h7 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {a b : (a : α) × β a} {l : List ((a : α) × β a)},
        b ∈ l → (a.fst == b.fst) = Bool.true → Std.Internal.List.DistinctKeys l → a = b := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ((⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)) ((⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide)))) (by
  decide +kernel)

-- Std.Internal.List.DistinctKeys.eq_of_mem_of_beq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.DistinctKeys.eq_of_mem_of_beq.h8 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {a b : (a : α) × β a} {l : List ((a : α) × β a)},
        a ∈ l → (a.fst == b.fst) = Bool.true → Std.Internal.List.DistinctKeys l → a = b := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@EquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@ReflBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)))) ((⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)) ((⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide)))) (by
  decide +kernel)

-- Std.Internal.List.DistinctKeys.eq_of_mem_of_beq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.DistinctKeys.eq_of_mem_of_beq.h9 : ¬∀ {α : Type} {β : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {a b : (a : α) × β a} {l : List ((a : α) × β a)},
        a ∈ l → b ∈ l → Std.Internal.List.DistinctKeys l → a = b := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ ((⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)) ((⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.maxKey_eq_iff_mem_and_forall, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKey_eq_iff_mem_and_forall.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        [inst : Std.LawfulEqOrd α] {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l → ∀ {km : α}, l.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ _ ([]) (by
  simp) (0)) (by
  decide +kernel)

-- Std.Internal.List.head?_keys, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.head?_keys.h10 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : Std.LawfulEqOrd α] [inst_3 : LE α]
        [inst_4 : Std.LawfulOrderOrd α] [inst_5 : Min α] [inst_6 : Std.LawfulOrderLeftLeaningMin α]
        (l : List ((a : α) × β a)), (Std.Internal.List.keys l).head? = Std.Internal.List.minKey? l := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ _ (instLENat) _ (instMinNat) _ ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)])) (by
  decide +kernel)

-- Std.Internal.List.Const.perm_of_beqModel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.perm_of_beqModel.h3 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : BEq β] [inst_2 : LawfulBEq β] {l₁ l₂ : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l₁ →
          Std.Internal.List.DistinctKeys l₂ → Std.Internal.List.Const.beqModel l₁ l₂ = Bool.true → l₁.Perm l₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) ([(⟨1, 0⟩ : (_ : Nat) × Nat)]) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (by (try dsimp only);   decide))) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.Const.perm_of_beqModel, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.perm_of_beqModel.h10 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : LawfulBEq α] [inst_2 : BEq β] [inst_3 : LawfulBEq β]
        {l₁ l₂ : List ((_ : α) × β)}, Std.Internal.List.DistinctKeys l₁ → Std.Internal.List.DistinctKeys l₂ → l₁.Perm l₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ (instBEqOfDecidableEq) _ ([]) ([(⟨0, 0⟩ : (_ : Nat) × Nat)]) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.containsKey_of_containsKey_filterMap', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.containsKey_of_containsKey_filterMap'.h4 : ¬∀ {α : Type} {β γ : α → Type} [inst : BEq α] {f : (a : α) × β a → Option ((a : α) × γ a)},
        (∀ (p : (a : α) × β a), Option.all (fun (x : (a : α) × γ a) => x.fst == p.fst) (f p) = Bool.true) →
          ∀ {l : List ((a : α) × β a)} {k : α},
            Std.Internal.List.DistinctKeys l →
              Std.Internal.List.containsKey k (List.filterMap f l) = Bool.true →
                Std.Internal.List.containsKey k l = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a : Nat) => Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) (fun (a : (a : Nat) × (fun (a : Nat) => Nat) a) => Option.some (⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)) (by
  simp) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) ((@Std.Internal.List.DistinctKeys.mk (Nat) (fun (a : Nat) => Nat) (@BEq.mk Nat fun (a b : Nat) => @Decidable.decide (@LE.le Nat instLENat a b) (a.decLe b)) (@List.cons (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (@Sigma.mk Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a))) (by (try dsimp only);   decide))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.containsKey_of_containsKey_filterMap', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.containsKey_of_containsKey_filterMap'.h6 : ¬∀ {α : Type} {β γ : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {f : (a : α) × β a → Option ((a : α) × γ a)}
        {l : List ((a : α) × β a)} {k : α},
        Std.Internal.List.DistinctKeys l →
          Std.Internal.List.containsKey k (List.filterMap f l) = Bool.true → Std.Internal.List.containsKey k l = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ (fun (a : (a : Nat) × (fun (a : Nat) => Nat) a) => Option.some (⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)) ([(⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.Internal.List.containsKey_of_containsKey_filterMap', hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.containsKey_of_containsKey_filterMap'.h10 : ¬∀ {α : Type} {β γ : α → Type} [inst : BEq α] [inst_1 : EquivBEq α] {f : (a : α) × β a → Option ((a : α) × γ a)},
        (∀ (p : (a : α) × β a), Option.all (fun (x : (a : α) × γ a) => x.fst == p.fst) (f p) = Bool.true) →
          ∀ {l : List ((a : α) × β a)} {k : α},
            Std.Internal.List.DistinctKeys l → Std.Internal.List.containsKey k l = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a : Nat) => Nat) (instBEqOfDecidableEq) _ (fun (a : (a : Nat) × (fun (a : Nat) => Nat) a) => Option.none) (by
  simp) ([]) (0) (by
  simp)) (by
  decide +kernel)

-- Std.Internal.List.maxKeyD_eraseKey_le_maxKeyD, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.maxKeyD_eraseKey_le_maxKeyD.h9 : ¬∀ {α : Type} {β : α → Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst_3 : Std.LawfulBEqOrd α]
        {l : List ((a : α) × β a)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k fallback : α},
            (Ord.compare (Std.Internal.List.maxKeyD (Std.Internal.List.eraseKey k l) fallback)
                  (Std.Internal.List.maxKeyD l fallback)).isLE =
              Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (by
  simp) (0) (1)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_contains_eq_false.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([]) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.Const.getKey_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false →
          ∀ {h' : k ∈ Std.ExtDTreeMap.Const.insertMany t l}, Std.LawfulBEqCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.Const.getKey_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α}
        {h' : k ∈ Std.ExtDTreeMap.Const.insertMany t l}, (List.map Prod.fst l).contains k = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.getKey_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.getKey_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → k ∈ Std.ExtDTreeMap.Const.insertMany t l := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.ExtDTreeMap.mem_of_mem_insertMany_list, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.mem_of_mem_insertMany_list.h4 : Not
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

-- Std.ExtDTreeMap.mem_of_mem_insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.mem_of_mem_insertMany_list.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : BEq α] {l : List ((a : α) × β a)} {k : α},
        k ∈ t.insertMany l → (List.map Sigma.fst l).contains k = Bool.false → k ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.ExtDTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.true) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.mem_of_mem_insertMany_list, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.mem_of_mem_insertMany_list.h9 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst_1 : BEq α] [inst_2 : @Std.LawfulBEqCmp α inst_1 cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst_1 (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Membership.mem α (Std.ExtDTreeMap α β cmp) (@Std.ExtDTreeMap.instMembershipOfTransCmp α β cmp inst) t k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (@Std.ExtDTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.mem_of_mem_insertMany_list, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.mem_of_mem_insertMany_list.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.ExtDTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α}, k ∈ t.insertMany l → k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.get_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_contains_eq_false.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp} [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([]) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.Const.get_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false →
          ∀ {h' : k ∈ Std.ExtDTreeMap.Const.insertMany t l}, Std.LawfulBEqCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.ExtDTreeMap.Const.get_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α}
        {h' : k ∈ Std.ExtDTreeMap.Const.insertMany t l}, (List.map Prod.fst l).contains k = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.ExtDTreeMap.Const.get_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ExtDTreeMap.Const.get_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.ExtDTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → k ∈ Std.ExtDTreeMap.Const.insertMany t l := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.ExtDTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.Internal.List.Const.minKey_alterKey_eq_self, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Internal.List.Const.minKey_alterKey_eq_self.h10 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] [inst_2 : BEq α] [inst : Std.LawfulBEqOrd α]
        {l : List ((_ : α) × β)},
        Std.Internal.List.DistinctKeys l →
          ∀ {k : α} {f : Option β → Option β}, (Std.Internal.List.Const.alterKey k f l).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (instBEqOfDecidableEq) _ ([]) (by
  simp) (0) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

