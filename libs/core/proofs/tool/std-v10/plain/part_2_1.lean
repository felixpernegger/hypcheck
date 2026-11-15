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

-- Std.DTreeMap.get?_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_insertMany_list_of_mem.h11 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α}
        {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.get?_insertMany_list_of_mem, hypothesis 14: necessary
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
    α | 7:161: `grind` has failed, use `+verbose` to obtain diagnostic information | 23:159: `grind` has failed, use `+verbose` to obtain diagnostic information | 12:56: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.61 k_eq✝ 0 | 46:18: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:215: `grind` has failed, use `+verbose` to obtain diagnostic information | 58:159: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_insertMany_list_of_mem.h14 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α}
        (k_eq : cmp k k' = Ordering.eq) {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (t.insertMany l).get? k' =
            Option.some
              (cast
                ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                      (k_eq : cmp k k' = Ordering.eq) =>
                    (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k'
                      (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                  k_eq)
                v) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instBEqOfDecidableEq) _ ([]) (0) (0) hc_k0 (0) hc_k1) (by
  decide +kernel)
-/

-- Std.DTreeMap.get!_insertMany_list_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_insertMany_list_of_mem.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β k} [inst : Inhabited (β k')],
            List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (⟨k, v⟩ : (a : α) × β a) ∈ l → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
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

-- Std.DTreeMap.get!_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α} {v : β k} [inst : Inhabited (β k')],
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (instInhabitedNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.get!_insertMany_list_of_mem, hypothesis 13: necessary
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
  Nat = ?m.61 k_eq✝ 0 | 45:16: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:202: `grind` has failed, use `+verbose` to obtain diagnostic information | 56:138: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_insertMany_list_of_mem.h13 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k}
        [inst_1 : Inhabited (β k')],
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (t.insertMany l).get! k' =
            cast
              ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                    (k_eq : cmp k k' = Ordering.eq) =>
                  (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                k_eq)
              v := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ ([]) (0) (0) hc_k0 (1) (instInhabitedNat) hc_k1) (by
  decide +kernel)
-/

-- Std.TreeMap.getElem?_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h10.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0)])[1]? = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h10.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h10.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k k' : α} {v : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → (t.insertMany l)[k']? = Option.some v := fun hc_h => HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h10.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (1) (0) HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h10.prem0 HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h10.prem1)

-- Std.TreeMap.getElem?_insertMany_list_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h12.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0), (0, 1)])[0]? = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h12.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h12.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h12 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq → ∀ {v : β}, (k, v) ∈ l → (t.insertMany l)[k']? = Option.some v := fun hc_h => HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h12.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h12.prem0 (0) HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h12.prem1)

-- Std.TreeMap.getElem?_insertMany_list_of_mem, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h13.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [])[0]? = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h13.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h13.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h13 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (t.insertMany l)[k']? = Option.some v := fun hc_h => HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h13.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (0) HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h13.prem0 (0) HypCheckProof.Std.TreeMap.getElem?_insertMany_list_of_mem.h13.prem1)

-- Std.DTreeMap.get!_ofList_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_ofList_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
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

-- Std.DTreeMap.get!_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} {v : β k} [inst : Inhabited (β k')],
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (instInhabitedNat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.get!_ofList_of_mem, hypothesis 12: necessary
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
    α | 7:159: `grind` has failed, use `+verbose` to obtain diagnostic information | 14:138: `grind` has failed, use `+verbose` to obtain diagnostic information | 11:54: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.55 k_eq✝ 0 | 35:16: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:186: `grind` has failed, use `+verbose` to obtain diagnostic information | 38:138: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_ofList_of_mem.h12 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k} [inst_1 : Inhabited (β k')],
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (Std.DTreeMap.ofList l cmp).get! k' =
            cast
              ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                    (k_eq : cmp k k' = Ordering.eq) =>
                  (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                k_eq)
              v := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([]) (0) (0) hc_k0 (1) (instInhabitedNat) hc_k1) (by
  decide +kernel)
-/

-- Std.DTreeMap.getD_ofList_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_ofList_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
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

-- Std.DTreeMap.getD_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} {v : β k} {fallback : β k'},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.getD_ofList_of_mem, hypothesis 12: necessary
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
    α | 7:168: `grind` has failed, use `+verbose` to obtain diagnostic information | 14:138: `grind` has failed, use `+verbose` to obtain diagnostic information | 11:54: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.55 k_eq✝ 0 | 36:16: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:188: `grind` has failed, use `+verbose` to obtain diagnostic information | 39:138: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_ofList_of_mem.h12 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k} {fallback : β k'},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (Std.DTreeMap.ofList l cmp).getD k' fallback =
            cast
              ((fun {α : Type} {β : α → Type} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] {k k' : α}
                    (k_eq : cmp k k' = Ordering.eq) =>
                  (fun (a a_1 : α) (e_a : a = a_1) => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
                k_eq)
              v := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([]) (0) (0) hc_k0 (0) (1) hc_k1) (by
  decide +kernel)
-/

-- Std.TreeMap.getElem_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_insertMany_list_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α}, cmp k k' = Ordering.eq → ∀ {v : β}, (k, v) ∈ l → ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l)[k'] = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) hc_k0 (0) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.TreeMap.getElem_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_insertMany_list_of_mem.h11 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l)[k'] = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (0) hc_k0 (1) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.TreeSet.get_insertMany_list_of_not_mem_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_insertMany_list_of_not_mem_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α}
        {h' : k' ∈ t.insertMany l},
        ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0, 1]) (0) (1) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.TreeSet.get_insertMany_list_of_not_mem_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_insertMany_list_of_not_mem_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {h' : k' ∈ t.insertMany l},
            List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.false) (Bool.false) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.TreeSet.get_insertMany_list_of_not_mem_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_insertMany_list_of_not_mem_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → ∀ {h' : k' ∈ t.insertMany l}, ¬k ∈ t → k ∈ l → (t.insertMany l).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.TreeSet.get_insertMany_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_insertMany_list_of_not_mem_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {h' : k' ∈ t.insertMany l},
            ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (t.insertMany l).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.inst : ¬((Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [0]).getD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem0 : ¬0 ∈ Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α}
        {k k' fallback : α},
        ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).getD k' fallback = k := fun hc_h => HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (1) (1) HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem0 HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem1 HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h8.prem2)

-- Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α}
        {k k' fallback : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).getD k' fallback = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.false) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.inst : ¬((Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany []).getD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem1 : ¬0 ∈ Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem2 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α}
        {k k' fallback : α},
        cmp k k' = Ordering.eq →
          ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (t.insertMany l).getD k' fallback = k := fun hc_h => HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) (1) HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem0 HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem1 HypCheckProof.Std.TreeSet.getD_insertMany_list_of_not_mem_of_mem.h11.prem2)

-- Std.TreeMap.getD_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h8.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0)]).getD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h8.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α} {v fallback : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → (t.insertMany l).getD k' fallback = v := fun hc_h => HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (0) (1) HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h8.prem0 HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h8.prem1)

-- Std.TreeMap.getD_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h11.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0), (0, 1)]).getD 0 0 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h11.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h11 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α}, cmp k k' = Ordering.eq → ∀ {v fallback : β}, (k, v) ∈ l → (t.insertMany l).getD k' fallback = v := fun hc_h => HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h11.prem0 (0) (0) HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h11.prem1)

-- Std.TreeMap.getD_insertMany_list_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h12.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany []).getD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h12.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h12.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h12 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (t.insertMany l).getD k' fallback = v := fun hc_h => HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h12.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h12.prem0 (0) (1) HypCheckProof.Std.TreeMap.getD_insertMany_list_of_mem.h12.prem1)

-- Std.TreeMap.getElem!_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h8.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 1)])[1]! = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 1)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h8.prem1 : (0, 1) ∈ [(0, 1)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α} {v : β} [inst : Inhabited β],
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (k, v) ∈ l → (t.insertMany l)[k']! = v := fun hc_h => HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 1)]) (0) (1) (1) (instInhabitedNat) HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h8.prem0 HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h8.prem1)

-- Std.TreeMap.getElem!_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h11.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0), (0, 1)])[0]! = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h11.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h11 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α}, cmp k k' = Ordering.eq → ∀ {v : β} [inst : Inhabited β], (k, v) ∈ l → (t.insertMany l)[k']! = v := fun hc_h => HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h11.prem0 (0) (instInhabitedNat) HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h11.prem1)

-- Std.TreeMap.getElem!_insertMany_list_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h12.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [])[0]! = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h12.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h12.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h12 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst : Inhabited β],
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (t.insertMany l)[k']! = v := fun hc_h => HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h12.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h12.prem0 (1) (instInhabitedNat) HypCheckProof.Std.TreeMap.getElem!_insertMany_list_of_mem.h12.prem1)

-- Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst : Not
      (@Eq Nat
        (@Std.TreeMap.getKey! Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) instInhabitedNat
          (@Std.TreeMap.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.TreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 : Not
      (@Membership.mem Nat (Std.TreeMap Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.instMembership Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2 : @Membership.mem Nat (List Nat) (@List.instMembership Nat)
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : @Std.TransCmp α cmp] [inst : Inhabited α]
        {l : List α} {k k' : α},
        Not (@Membership.mem α (Std.TreeMap α Unit cmp) (@Std.TreeMap.instMembership α Unit cmp) t k) →
          @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
            @Membership.mem α (List α) (@List.instMembership α) l k →
              @Eq α
                (@Std.TreeMap.getKey! α Unit cmp inst
                  (@Std.TreeMap.insertManyIfNewUnit α cmp (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                k) := fun hc_h => HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem0 HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem1 HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h8.prem2)

-- Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {l : List α} {k k' : α}, cmp k k' = Ordering.eq → ¬k ∈ t → k ∈ l → (t.insertManyIfNewUnit l).getKey! k' = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.TreeMap.getKey! Nat Unit (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) instInhabitedNat
          (@Std.TreeMap.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.TreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil Nat))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 : Not
      (@Membership.mem Nat (Std.TreeMap Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.instMembership Nat Unit fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : @Std.TransCmp α cmp] [inst : Inhabited α]
        {l : List α} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          Not (@Membership.mem α (Std.TreeMap α Unit cmp) (@Std.TreeMap.instMembership α Unit cmp) t k) →
            @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
              @Eq α
                (@Std.TreeMap.getKey! α Unit cmp inst
                  (@Std.TreeMap.insertManyIfNewUnit α cmp (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                k) := fun hc_h => HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Unit (@List.nil (Prod Nat Unit)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem0 HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem1 HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem.h11.prem2)

-- Std.TreeMap.getKey_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_insertMany_list_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
            ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(Bool.false, 0)]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_ofList_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            (k, v) ∈ l →
              ∀ {h : k' ∈ Std.DTreeMap.Const.ofList l cmp},
                Std.DTreeMap.Const.get (Std.DTreeMap.Const.ofList l cmp) k' h = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) _ ([(0, 0), (0, 1)]) (0) (0) hc_k0 (0) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_ofList_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              ∀ {h : k' ∈ Std.DTreeMap.Const.ofList l cmp},
                Std.DTreeMap.Const.get (Std.DTreeMap.Const.ofList l cmp) k' h = v := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) _ ([(0, 0)]) (0) (0) hc_k0 (1) hc_k1 hc_k2) (by
  decide +kernel)

-- Std.DTreeMap.getKey_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insertMany_list_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Sigma.fst l → ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a), (⟨1, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.DTreeMap.getKey_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq → k ∈ List.map Sigma.fst l → ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a), (⟨Bool.true, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.DTreeMap.getKey_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insertMany_list_of_mem.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
            ∀ {h' : k' ∈ t.insertMany l}, (t.insertMany l).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h8.inst : ¬Std.DTreeMap.Const.getD
          (Std.DTreeMap.Const.insertMany (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0)]) 1 1 =
        0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h8.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {l : List (α × β)} {k k' : α} {v fallback : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → Std.DTreeMap.Const.getD (Std.DTreeMap.Const.insertMany t l) k' fallback = v := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (0) (1) HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h8.prem0 HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h8.prem1)

-- Std.DTreeMap.Const.getD_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h11.inst : ¬Std.DTreeMap.Const.getD
          (Std.DTreeMap.Const.insertMany (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0), (0, 1)]) 0 0 =
        0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h11.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β}, (k, v) ∈ l → Std.DTreeMap.Const.getD (Std.DTreeMap.Const.insertMany t l) k' fallback = v := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h11.prem0 (0) (0) HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h11.prem1)

-- Std.DTreeMap.Const.getD_insertMany_list_of_mem, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h12.inst : ¬Std.DTreeMap.Const.getD (Std.DTreeMap.Const.insertMany (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [])
          0 1 =
        0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h12.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h12.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h12 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              Std.DTreeMap.Const.getD (Std.DTreeMap.Const.insertMany t l) k' fallback = v := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h12.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h12.prem0 (0) (1) HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_mem.h12.prem1)

-- Std.DTreeMap.get?_ofList_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_ofList_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
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

-- Std.DTreeMap.get?_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (⟨k, v⟩ : (a : α) × β a) ∈ l → cmp k k' = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.get?_ofList_of_mem, hypothesis 11: necessary
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
    α | 7:172: `grind` has failed, use `+verbose` to obtain diagnostic information | 14:159: `grind` has failed, use `+verbose` to obtain diagnostic information | 12:56: Type mismatch
  e_a ▸ Eq.refl (β a)
has type
  β a_1 = β a_1
but is expected to have type
  Nat = ?m.55 k_eq✝ 0 | 36:18: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 ?m.5 ?m.6 = Ordering.eq
of sort `Prop` in the application
  (fun {α} {β} {cmp} [Std.LawfulEqCmp cmp] {k k'} k_eq =>
      (fun a a_1 e_a => e_a ▸ Eq.refl (β a)) k k' (Std.LawfulEqCmp.compare_eq_iff_eq.mp k_eq))
    Nat | 7:199: `grind` has failed, use `+verbose` to obtain diagnostic information | 39:159: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_ofList_of_mem.h11 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = Ordering.eq) {v : β k},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (Std.DTreeMap.ofList l cmp).get? k' =
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

-- Std.TreeMap.getKey!_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertMany_list_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.TreeMap.getKey! Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) instInhabitedNat
          (@Std.TreeMap.insertMany Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (List (Prod Nat Nat))
            (@instForInOfForIn' Id (List (Prod Nat Nat)) (Prod Nat Nat)
              (@inferInstance (Membership (Prod Nat Nat) (List (Prod Nat Nat))) (@List.instMembership (Prod Nat Nat)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod Nat Nat) Id.instMonad))
            (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (Prod Nat Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertMany_list_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertMany_list_of_mem.h11.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getKey!_insertMany_list_of_mem.h11 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : @Std.TransCmp α cmp] [inst : Inhabited α]
        {l : List (Prod α β)} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α
              (@Std.TreeMap.getKey! α β cmp inst
                (@Std.TreeMap.insertMany α β cmp (List (Prod α β))
                  (@instForInOfForIn' Id (List (Prod α β)) (Prod α β)
                    (@inferInstance (Membership (Prod α β) (List (Prod α β))) (@List.instMembership (Prod α β)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod α β) Id.instMonad))
                  t l)
                k')
              k) := fun hc_h => HypCheckProof.Std.TreeMap.getKey!_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (instInhabitedNat) (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.TreeMap.getKey!_insertMany_list_of_mem.h11.prem0 HypCheckProof.Std.TreeMap.getKey!_insertMany_list_of_mem.h11.prem1)

-- Std.TreeMap.getD_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h7.inst : ¬(Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b).getD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h7.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α} {v fallback : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → (Std.TreeMap.ofList l cmp).getD k' fallback = v := fun hc_h => HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h7.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (0) (1) HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h7.prem0 HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h7.prem1)

-- Std.TreeMap.getD_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h10.inst : ¬(Std.TreeMap.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b).getD 0 0 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h10.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq → ∀ {v fallback : β}, (k, v) ∈ l → (Std.TreeMap.ofList l cmp).getD k' fallback = v := fun hc_h => HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h10.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h10.prem0 (0) (0) HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h10.prem1)

-- Std.TreeMap.getD_ofList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h11.inst : ¬(Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).getD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h11 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v fallback : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (Std.TreeMap.ofList l cmp).getD k' fallback = v := fun hc_h => HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h11.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h11.prem0 (0) (1) HypCheckProof.Std.TreeMap.getD_ofList_of_mem.h11.prem1)

-- Std.DTreeMap.get!_insertMany_list_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_insertMany_list_of_contains_eq_false.h5 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst : BEq α] [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α}
        [inst_2 : Inhabited (β k)],
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Std.LawfulEqCmp α cmp) := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.DTreeMap.ofList Bool (fun (a : Bool) => Nat) (@List.nil (@Sigma Bool fun (a : Bool) => Nat)) fun (x x_1 : Bool) =>
      Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (⟨fun _ _ => true⟩ : BEq Bool) (@Std.LawfulBEqCmp.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (@List.nil (@Sigma Bool fun (a : Bool) => (fun (a : Bool) => Nat) a)) (Bool.false) (instInhabitedNat) (by
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

-- Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.inst : ¬(Std.DTreeMap.Const.insertMany (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) [(0, 0)]).getKeyD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.prem1 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {l : List (α × β)} {k k' fallback : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l → (Std.DTreeMap.Const.insertMany t l).getKeyD k' fallback = k := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (1) HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.prem0 HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h9.prem1)

-- Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.inst : Not
      (@Eq Nat
        (@Std.DTreeMap.getKeyD Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.Const.insertMany Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat (List (Prod Nat Nat))
            (@instForInOfForIn' Id (List (Prod Nat Nat)) (Prod Nat Nat)
              (@inferInstance (Membership (Prod Nat Nat) (List (Prod Nat Nat))) (@List.instMembership (Prod Nat Nat)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod Nat Nat) Id.instMonad))
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (Prod Nat Nat)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h11 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : @Std.TransCmp α cmp] {l : List (Prod α β)} {k k' fallback : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α
              (@Std.DTreeMap.getKeyD α (fun (x : α) => β) cmp
                (@Std.DTreeMap.Const.insertMany α cmp β (List (Prod α β))
                  (@instForInOfForIn' Id (List (Prod α β)) (Prod α β)
                    (@inferInstance (Membership (Prod α β) (List (Prod α β))) (@List.instMembership (Prod α β)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod α β) Id.instMonad))
                  t l)
                k' fallback)
              k) := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.prem0 HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_mem.h11.prem1)

-- Std.DTreeMap.Const.get!_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h7.inst : ¬Std.DTreeMap.Const.get! (Std.DTreeMap.Const.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) 1 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 1)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h7.prem1 : (0, 1) ∈ [(0, 1)] := by
  decide
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α} {v : β}
        [inst : Inhabited β],
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → Std.DTreeMap.Const.get! (Std.DTreeMap.Const.ofList l cmp) k' = v := fun hc_h => HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([(0, 1)]) (0) (1) (1) (instInhabitedNat) HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h7.prem0 HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h7.prem1)

-- Std.DTreeMap.Const.get!_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h10.inst : ¬Std.DTreeMap.Const.get! (Std.DTreeMap.Const.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b) 0 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h10.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst : Inhabited β], (k, v) ∈ l → Std.DTreeMap.Const.get! (Std.DTreeMap.Const.ofList l cmp) k' = v := fun hc_h => HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h10.prem0 (0) (instInhabitedNat) HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h10.prem1)

-- Std.DTreeMap.Const.get!_ofList_of_mem, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h11.inst : ¬Std.DTreeMap.Const.get! (Std.DTreeMap.Const.ofList [] fun (a b : Nat) => Ord.compare a b) 0 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h11.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h11.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β} [inst : Inhabited β],
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              Std.DTreeMap.Const.get! (Std.DTreeMap.Const.ofList l cmp) k' = v := fun hc_h => HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h11.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([]) (0) (0) HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h11.prem0 (1) (instInhabitedNat) HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_mem.h11.prem1)

-- Std.DTreeMap.getD_insertMany_list_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_insertMany_list_of_contains_eq_false.h5 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst : BEq α] [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α}
        {fallback : β k},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Std.LawfulEqCmp α cmp) := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.DTreeMap.ofList Bool (fun (a : Bool) => Nat) (@List.nil (@Sigma Bool fun (a : Bool) => Nat)) fun (x x_1 : Bool) =>
      Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (⟨fun _ _ => true⟩ : BEq Bool) (@Std.LawfulBEqCmp.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (@List.nil (@Sigma Bool fun (a : Bool) => (fun (a : Bool) => Nat) a)) (Bool.false) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
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

-- Std.DTreeMap.getD_insertMany_list_of_contains_eq_false, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_insertMany_list_of_contains_eq_false.h11 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α}
        {fallback : β k}, (t.insertMany l).getD k fallback = t.getD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey_ofList_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
            ∀ {h' : k' ∈ Std.DTreeMap.Const.ofList l cmp}, (Std.DTreeMap.Const.ofList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(Bool.false, 0)]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.inst : ¬((Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [0]).get? 1 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem0 : ¬0 ∈ Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem2 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        ¬k ∈ t →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get? k' = Option.some k := fun hc_h => HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (1) HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem0 HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem1 HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h7.prem2)

-- Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (t.insertMany l).get? k' = Option.some k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → ¬k ∈ t → k ∈ l → (t.insertMany l).get? k' = Option.some k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.inst : ¬((Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany []).get? 0 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem1 : ¬0 ∈ Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem2 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          ¬k ∈ t → List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (t.insertMany l).get? k' = Option.some k := fun hc_h => HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem0 HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem1 HypCheckProof.Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem.h10.prem2)

-- Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.inst : Not
      (@Eq (Option Nat)
        (@Std.DTreeMap.getKey? Nat (fun (x : Nat) => Unit) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.Const.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem0 : Not
      (@Membership.mem Nat (Std.DTreeMap Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.DTreeMap.instMembership Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
          @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem1 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem2 : @Membership.mem Nat (List Nat) (@List.instMembership Nat)
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : @Std.TransCmp α cmp]
        {l : List α} {k k' : α},
        Not
            (@Membership.mem α (Std.DTreeMap α (fun (x : α) => Unit) cmp)
              (@Std.DTreeMap.instMembership α (fun (x : α) => Unit) cmp) t k) →
          @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
            @Membership.mem α (List α) (@List.instMembership α) l k →
              @Eq (Option α)
                (@Std.DTreeMap.getKey? α (fun (x : α) => Unit) cmp
                  (@Std.DTreeMap.Const.insertManyIfNewUnit α cmp (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                (@Option.some α k)) := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem0 HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem1 HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h7.prem2)

-- Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → ¬k ∈ t → k ∈ l → (Std.DTreeMap.Const.insertManyIfNewUnit t l).getKey? k' = Option.some k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.inst : Not
      (@Eq (Option Nat)
        (@Std.DTreeMap.getKey? Nat (fun (x : Nat) => Unit) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.Const.insertManyIfNewUnit Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil Nat))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem1 : Not
      (@Membership.mem Nat (Std.DTreeMap Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.DTreeMap.instMembership Nat (fun (x : Nat) => Unit) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
          @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem2 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : @Std.TransCmp α cmp]
        {l : List α} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          Not
              (@Membership.mem α (Std.DTreeMap α (fun (x : α) => Unit) cmp)
                (@Std.DTreeMap.instMembership α (fun (x : α) => Unit) cmp) t k) →
            @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
              @Eq (Option α)
                (@Std.DTreeMap.getKey? α (fun (x : α) => Unit) cmp
                  (@Std.DTreeMap.Const.insertManyIfNewUnit α cmp (List α)
                    (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                      (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                    t l)
                  k')
                (@Option.some α k)) := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Unit) (@List.nil (@Sigma Nat fun (a : Nat) => Unit)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem0 HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem1 HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem.h10.prem2)

-- Std.DTreeMap.Equiv.forIn_eq, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.forIn_eq.h12 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} {δ : Type} {m : Type → Type}
        [inst : Std.TransCmp cmp] [inst : Monad m] [inst_1 : LawfulMonad m] {b : δ}
        {f : (a : α) × β a → δ → m (ForInStep δ)}, ForIn.forIn t₁ b f = ForIn.forIn t₂ b f := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) _ (instMonadOption) _ (0) (fun (a : (a : Nat) × (fun (a : Nat) => Nat) a) (a_1 : Nat) => Option.none)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.foldlM_eq, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.foldlM_eq.h12 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type}
        [inst : Std.TransCmp cmp] [inst : Monad m] [inst_1 : LawfulMonad m] {f : δ → α → β → m δ} {init : δ},
        Std.TreeMap.foldlM f init t₁ = Std.TreeMap.foldlM f init t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) _ (instMonadOption) _ (fun (a a_1 x : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h7.inst : ¬(Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b)[1]? = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h7.prem1 : (0, 0) ∈ [(0, 0)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α} {v : β},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          (k, v) ∈ l → (Std.TreeMap.ofList l cmp)[k']? = Option.some v := fun hc_h => HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h7.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (0) HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h7.prem0 HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h7.prem1)

-- Std.TreeMap.getElem?_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h9.inst : ¬(Std.TreeMap.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b)[0]? = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h9.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h9.prem1 : (0, 0) ∈ [(0, 0), (0, 1)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq → ∀ {v : β}, (k, v) ∈ l → (Std.TreeMap.ofList l cmp)[k']? = Option.some v := fun hc_h => HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h9.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([(0, 0), (0, 1)]) (0) (0) HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h9.prem0 (0) HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h9.prem1)

-- Std.TreeMap.getElem?_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h10.inst : ¬(Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b)[0]? = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h10.prem1 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        cmp k k' = Ordering.eq →
          ∀ {v : β},
            List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
              (Std.TreeMap.ofList l cmp)[k']? = Option.some v := fun hc_h => HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h10.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h10.prem0 (0) HypCheckProof.Std.TreeMap.getElem?_ofList_of_mem.h10.prem1)

-- Std.TreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_insertMany_list_of_contains_eq_false.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : BEq α] [inst_1 : Std.LawfulBEqCmp cmp]
        {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → ∀ {h' : k ∈ t.insertMany l}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([]) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → ∀ {h' : k ∈ t.insertMany l}, Std.LawfulBEqCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α} {h' : k ∈ t.insertMany l},
        (List.map Prod.fst l).contains k = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → k ∈ t.insertMany l := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getElem_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_insertMany_list_of_contains_eq_false.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : BEq α] [inst_1 : Std.LawfulBEqCmp cmp]
        {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → ∀ {h' : k ∈ t.insertMany l}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([]) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → ∀ {h' : k ∈ t.insertMany l}, Std.LawfulBEqCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α} {h' : k ∈ t.insertMany l},
        (List.map Prod.fst l).contains k = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getElem_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → k ∈ t.insertMany l := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h8.inst : ¬(Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b).getKeyD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h8.prem1 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' fallback : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l → (Std.TreeMap.ofList l cmp).getKeyD k' fallback = k := fun hc_h => HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) (1) HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h8.prem0 HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h8.prem1)

-- Std.TreeMap.getKeyD_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h10.inst : Not
      (@Eq Nat
        (@Std.TreeMap.getKeyD Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h10.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h10 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} [inst : @Std.TransCmp α cmp] {l : List (Prod α β)} {k k' fallback : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α (@Std.TreeMap.getKeyD α β cmp (@Std.TreeMap.ofList α β l cmp) k' fallback) k) := fun hc_h => HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h10.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h10.prem0 HypCheckProof.Std.TreeMap.getKeyD_ofList_of_mem.h10.prem1)

-- Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Inhabited α] {l : List α} {k : α},
        ¬k ∈ t → l.contains k = Bool.false → (t.insertManyIfNewUnit l).getKey! k = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) (instInhabitedBool) ([Bool.true]) (Bool.false) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] [inst : Inhabited α] {l : List α} {k : α},
        ¬k ∈ t → (t.insertManyIfNewUnit l).getKey! k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([1]) (1) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_insertMany_list_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h8.inst : ¬((Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0)]).getKey? 1 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h8.prem1 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {l : List (α × β)}
        {k k' : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l → (t.insertMany l).getKey? k' = Option.some k := fun hc_h => HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([(0, 0)]) (0) (1) HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h8.prem0 HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h8.prem1)

-- Std.TreeMap.getKey?_insertMany_list_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h10.inst : Not
      (@Eq (Option Nat)
        (@Std.TreeMap.getKey? Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeMap.insertMany Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (List (Prod Nat Nat))
            (@instForInOfForIn' Id (List (Prod Nat Nat)) (Prod Nat Nat)
              (@inferInstance (Membership (Prod Nat Nat) (List (Prod Nat Nat))) (@List.instMembership (Prod Nat Nat)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod Nat Nat) Id.instMonad))
            (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.nil (Prod Nat Nat)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h10.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h10 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : @Std.TransCmp α cmp] {l : List (Prod α β)}
        {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq (Option α)
              (@Std.TreeMap.getKey? α β cmp
                (@Std.TreeMap.insertMany α β cmp (List (Prod α β))
                  (@instForInOfForIn' Id (List (Prod α β)) (Prod α β)
                    (@inferInstance (Membership (Prod α β) (List (Prod α β))) (@List.instMembership (Prod α β)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod α β) Id.instMonad))
                  t l)
                k')
              (@Option.some α k)) := fun hc_h => HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h10.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h10.prem0 HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_mem.h10.prem1)

-- Std.TreeSet.get!_insertMany_list_of_not_mem_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_insertMany_list_of_not_mem_of_contains_eq_false.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Inhabited α] {l : List α} {k : α},
        ¬k ∈ t → l.contains k = Bool.false → (t.insertMany l).get! k = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) (instInhabitedBool) ([Bool.true]) (Bool.false) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get!_insertMany_list_of_not_mem_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_insertMany_list_of_not_mem_of_contains_eq_false.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] [inst_2 : Inhabited α] {l : List α} {k : α},
        l.contains k = Bool.false → (t.insertMany l).get! k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([]) (1) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get!_insertMany_list_of_not_mem_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_insertMany_list_of_not_mem_of_contains_eq_false.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] [inst : Inhabited α] {l : List α} {k : α},
        ¬k ∈ t → (t.insertMany l).get! k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([1]) (1) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.mem_of_mem_insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_insertMany_list.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List ((a : α) × β a)} {k : α},
        k ∈ t.insertMany l → (List.map Sigma.fst l).contains k = Bool.false → k ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.true) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.mem_of_mem_insertMany_list, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_insertMany_list.h9 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst : BEq α] [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Membership.mem α (Std.DTreeMap α β cmp) (@Std.DTreeMap.instMembership α β cmp) t k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.mem_of_mem_insertMany_list, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_insertMany_list.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α}, k ∈ t.insertMany l → k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.get!_ofList_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_ofList_of_contains_eq_false.h4 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : @Std.TransCmp α cmp] [inst : BEq α]
        [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α} [inst_2 : Inhabited (β k)],
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Std.LawfulEqCmp α cmp) := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (⟨fun _ _ => true⟩ : BEq Bool) (@Std.LawfulBEqCmp.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (@List.nil (@Sigma Bool fun (a : Bool) => (fun (a : Bool) => Nat) a)) (Bool.false) (instInhabitedNat) (by
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

-- Std.DTreeMap.Const.getKey!_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_ofList_of_mem.h10.inst : Not
      (@Eq Nat
        (@Std.DTreeMap.getKey! Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          instInhabitedNat
          (@Std.DTreeMap.Const.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_ofList_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_ofList_of_mem.h10.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_ofList_of_mem.h10 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : @Std.TransCmp α cmp] [inst : Inhabited α]
        {l : List (Prod α β)} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α (@Std.DTreeMap.getKey! α (fun (x : α) => β) cmp inst (@Std.DTreeMap.Const.ofList α β l cmp) k') k) := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKey!_ofList_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) _ (instInhabitedNat) (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.DTreeMap.Const.getKey!_ofList_of_mem.h10.prem0 HypCheckProof.Std.DTreeMap.Const.getKey!_ofList_of_mem.h10.prem1)

-- Std.DTreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insertMany_list_of_contains_eq_false.h4 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : BEq α]
        [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          ∀
            {h' :
              @Membership.mem α (Std.DTreeMap α β cmp) (@Std.DTreeMap.instMembership α β cmp)
                (@Std.DTreeMap.insertMany α β cmp (List (@Sigma α fun (a : α) => β a))
                  (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
                    (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
                      (@List.instMembership (@Sigma α fun (a : α) => β a)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
                  t l)
                k},
            @Std.TransCmp α cmp) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat)
      (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
        (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
      fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@instBEqOfDecidableEq Nat instDecidableEqNat) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insertMany_list_of_contains_eq_false.h6 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst : BEq α] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          ∀
            {h' :
              @Membership.mem α (Std.DTreeMap α β cmp) (@Std.DTreeMap.instMembership α β cmp)
                (@Std.DTreeMap.insertMany α β cmp (List (@Sigma α fun (a : α) => β a))
                  (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
                    (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
                      (@List.instMembership (@Sigma α fun (a : α) => β a)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
                  t l)
                k},
            @Std.LawfulBEqCmp α inst cmp) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat)
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

-- Std.DTreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst_1 : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α} {h' : k ∈ t.insertMany l},
        (List.map Sigma.fst l).contains k = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.getKey_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insertMany_list_of_contains_eq_false.h10 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst : BEq α] [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Membership.mem α (Std.DTreeMap α β cmp) (@Std.DTreeMap.instMembership α β cmp)
            (@Std.DTreeMap.insertMany α β cmp (List (@Sigma α fun (a : α) => β a))
              (@instForInOfForIn' Id (List (@Sigma α fun (a : α) => β a)) (@Sigma α fun (a : α) => β a)
                (@inferInstance (Membership (@Sigma α fun (a : α) => β a) (List (@Sigma α fun (a : α) => β a)))
                  (@List.instMembership (@Sigma α fun (a : α) => β a)))
                (@List.instForIn'InferInstanceMembershipOfMonad Id (@Sigma α fun (a : α) => β a) Id.instMonad))
              t l)
            k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@instBEqOfDecidableEq Nat instDecidableEqNat) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.get?_insertMany_list_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_insertMany_list_of_contains_eq_false.h5 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst : BEq α] [inst_1 : @Std.LawfulBEqCmp α inst cmp] {l : List (@Sigma α fun (a : α) => β a)} {k : α},
        @Eq Bool (@List.contains α inst (@List.map (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a) l) k)
            Bool.false →
          @Std.LawfulEqCmp α cmp) := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.DTreeMap.ofList Bool (fun (a : Bool) => Nat) (@List.nil (@Sigma Bool fun (a : Bool) => Nat)) fun (x x_1 : Bool) =>
      Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (⟨fun _ _ => true⟩ : BEq Bool) (@Std.LawfulBEqCmp.mk (Bool) (@BEq.mk Bool fun (x x_1 : Bool) => Bool.true) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (@List.nil (@Sigma Bool fun (a : Bool) => (fun (a : Bool) => Nat) a)) (Bool.false) (by
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

-- Std.DTreeMap.get?_insertMany_list_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_insertMany_list_of_contains_eq_false.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst_1 : BEq α] {l : List ((a : α) × β a)} {k : α},
        (List.map Sigma.fst l).contains k = Bool.false → (t.insertMany l).get? k = t.get? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (⟨fun a b => a != b⟩ : BEq Nat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.get?_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst_1 : BEq α] [inst_2 : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α},
        (t.insertMany l).get? k = t.get? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)}
        {k k' fallback : α},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Sigma.fst l → (Std.DTreeMap.ofList l cmp).getKeyD k' fallback = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)}
        {k k' fallback : α},
        cmp k k' = Ordering.eq → k ∈ List.map Sigma.fst l → (Std.DTreeMap.ofList l cmp).getKeyD k' fallback = k := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a), (⟨Bool.true, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_mem.h10.inst : Not
      (@Eq Nat
        (@Std.DTreeMap.getKeyD Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat)
            (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) fun (a b : Nat) =>
            @Ord.compare Nat instOrdNat a b)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_mem.h10.prem1 : @List.Pairwise (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (fun (a b : @Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a) =>
        Not
          (@Eq Ordering
            ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
              (@Sigma.fst Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) a)
              (@Sigma.fst Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) b))
            Ordering.eq))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_mem.h10 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : @Std.TransCmp α cmp]
        {l : List (@Sigma α fun (a : α) => β a)} {k k' fallback : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (@Sigma α fun (a : α) => β a)
              (fun (a b : @Sigma α fun (a : α) => β a) =>
                Not
                  (@Eq Ordering (cmp (@Sigma.fst α (fun (a : α) => β a) a) (@Sigma.fst α (fun (a : α) => β a) b))
                    Ordering.eq))
              l →
            @Eq α (@Std.DTreeMap.getKeyD α β cmp (@Std.DTreeMap.ofList α β l cmp) k' fallback) k) := fun hc_h => HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_mem.h10.inst (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_mem.h10.prem0 HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_mem.h10.prem1)

-- Std.DTreeMap.Const.get_insertMany_list_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_insertMany_list_of_contains_eq_false.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → ∀ {h' : k ∈ Std.DTreeMap.Const.insertMany t l}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instBEqOfDecidableEq) (@Std.LawfulBEqCmp.mk (Nat) (@instBEqOfDecidableEq Nat instDecidableEqNat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) ([]) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → ∀ {h' : k ∈ Std.DTreeMap.Const.insertMany t l}, Std.LawfulBEqCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α}
        {h' : k ∈ Std.DTreeMap.Const.insertMany t l}, (List.map Prod.fst l).contains k = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → k ∈ Std.DTreeMap.Const.insertMany t l := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKeyD_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h8.inst : ¬(Std.DTreeMap.Const.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b).getKeyD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h8.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h8.prem1 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' fallback : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l → (Std.DTreeMap.Const.ofList l cmp).getKeyD k' fallback = k := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([(0, 0)]) (0) (1) (1) HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h8.prem0 HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h8.prem1)

-- Std.DTreeMap.Const.getKeyD_ofList_of_mem, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h10.inst : Not
      (@Eq Nat
        (@Std.DTreeMap.getKeyD Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.Const.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h10.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h10.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h10 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : @Std.TransCmp α cmp] {l : List (Prod α β)}
        {k k' fallback : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq α (@Std.DTreeMap.getKeyD α (fun (x : α) => β) cmp (@Std.DTreeMap.Const.ofList α β l cmp) k' fallback) k) := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h10.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) _ (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h10.prem0 HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_mem.h10.prem1)

-- Std.TreeSet.Equiv.foldrM_eq, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.foldrM_eq.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} {δ : Type} {m : Type → Type}
        [inst : Std.TransCmp cmp] [inst : Monad m] [inst_1 : LawfulMonad m] {f : α → δ → m δ} {init : δ},
        Std.TreeSet.foldrM f init t₁ = Std.TreeSet.foldrM f init t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) _ (instMonadOption) _ (fun (a x : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey_unitOfList_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey_unitOfList_of_mem.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
          k ∈ l → ∀ {h' : k' ∈ Std.DTreeMap.Const.unitOfList l cmp}, (Std.DTreeMap.Const.unitOfList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ ([0, 1]) (0) (1) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey_unitOfList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey_unitOfList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          k ∈ l → ∀ {h' : k' ∈ Std.DTreeMap.Const.unitOfList l cmp}, (Std.DTreeMap.Const.unitOfList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey_unitOfList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey_unitOfList_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
            ∀ {h' : k' ∈ Std.DTreeMap.Const.unitOfList l cmp}, (Std.DTreeMap.Const.unitOfList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.TreeMap.getKey_unitOfList_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_unitOfList_of_mem.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
          k ∈ l → ∀ {h' : k' ∈ Std.TreeMap.unitOfList l cmp}, (Std.TreeMap.unitOfList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ ([0, 1]) (0) (1) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.TreeMap.getKey_unitOfList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_unitOfList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          k ∈ l → ∀ {h' : k' ∈ Std.TreeMap.unitOfList l cmp}, (Std.TreeMap.unitOfList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.TreeMap.getKey_unitOfList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_unitOfList_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
            ∀ {h' : k' ∈ Std.TreeMap.unitOfList l cmp}, (Std.TreeMap.unitOfList l cmp).getKey k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.TreeSet.get_ofList_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_ofList_of_mem.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
          k ∈ l → ∀ {h' : k' ∈ Std.TreeSet.ofList l cmp}, (Std.TreeSet.ofList l cmp).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ ([0, 1]) (0) (1) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.TreeSet.get_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_ofList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → k ∈ l → ∀ {h' : k' ∈ Std.TreeSet.ofList l cmp}, (Std.TreeSet.ofList l cmp).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.TreeSet.get_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_ofList_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
            ∀ {h' : k' ∈ Std.TreeSet.ofList l cmp}, (Std.TreeSet.ofList l cmp).get k' h' = k := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false]) (Bool.true) (Bool.false) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey?_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h7.inst : ¬(Std.DTreeMap.Const.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b).getKey? 1 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h7.prem1 : 0 ∈ List.map Prod.fst [(0, 0)] := by
  decide
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] {l : List (α × β)} {k k' : α},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Prod.fst l → (Std.DTreeMap.Const.ofList l cmp).getKey? k' = Option.some k := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Nat) _ ([(0, 0)]) (0) (1) HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h7.prem0 HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h7.prem1)

-- Std.DTreeMap.Const.getKey?_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h9.inst : Not
      (@Eq (Option Nat)
        (@Std.DTreeMap.getKey? Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.Const.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h9.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h9.prem1 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.nil (Prod Nat Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h9 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : @Std.TransCmp α cmp] {l : List (Prod α β)} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (Prod α β)
              (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
            @Eq (Option α) (@Std.DTreeMap.getKey? α (fun (x : α) => β) cmp (@Std.DTreeMap.Const.ofList α β l cmp) k')
              (@Option.some α k)) := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h9.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) _ (@List.nil (Prod Nat Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h9.prem0 HypCheckProof.Std.DTreeMap.Const.getKey?_ofList_of_mem.h9.prem1)

-- Std.DTreeMap.get_union_of_not_mem_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_union_of_not_mem_left.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        {k : α}, ¬k ∈ t₁ → ∀ {h' : k ∈ t₁ ∪ t₂}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_union_of_not_mem_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_union_of_not_mem_left.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        ¬k ∈ t₁ → ∀ {h' : k ∈ t₁ ∪ t₂}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide) (by
  decide)) (by
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

-- Std.DTreeMap.get_union_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_union_of_not_mem_left.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {h' : k ∈ t₁ ∪ t₂}, ¬k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.get_union_of_not_mem_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_union_of_not_mem_left.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, ¬k ∈ t₁ → k ∈ t₁ ∪ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.get_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.get_eq.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        {k : α} {hk : k ∈ t₁}, t₁.Equiv t₂ → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (by
  decide) (by
  rfl)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Equiv.get_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.get_eq.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {hk : k ∈ t₁}, t₁.Equiv t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide) (by
  rfl)) (by
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

-- Std.DTreeMap.Equiv.get_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.get_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, t₁.Equiv t₂ → k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.get_eq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.get_eq.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {hk : k ∈ t₁}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.size_alter_eq_self_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_alter_eq_self_of_mem.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option (β k) → Option (β k)}, k ∈ t → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none) (by
  decide)) (by
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

-- Std.DTreeMap.size_alter_eq_self_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.size_alter_eq_self_of_mem.h8.inst : Not
      (@Eq Nat
        (@Std.DTreeMap.size Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.alter Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instLawfulEqOrd
            (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            fun (a : Option ((fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) =>
            @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Std.DTreeMap.size Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
            @Ord.compare Nat instOrdNat a b))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.size_alter_eq_self_of_mem.h8.prem0 : @Eq Bool
      (@Option.isSome ((fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        ((fun (a : Option ((fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) =>
            @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Std.DTreeMap.get? Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            Nat.instLawfulEqOrd
            (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.size_alter_eq_self_of_mem.h8 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        [inst : @Std.LawfulEqCmp α cmp] {k : α} {f : Option (β k) → Option (β k)},
        @Eq Bool (@Option.isSome (β k) (f (@Std.DTreeMap.get? α β cmp inst t k))) Bool.true →
          @Eq Nat (@Std.DTreeMap.size α β cmp (@Std.DTreeMap.alter α β cmp inst t k f)) (@Std.DTreeMap.size α β cmp t)) := fun hc_h => HypCheckProof.Std.DTreeMap.size_alter_eq_self_of_mem.h8.inst (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a : Option ((fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) =>
      @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Std.DTreeMap.size_alter_eq_self_of_mem.h8.prem0)

-- Std.DTreeMap.size_alter_eq_self_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_alter_eq_self_of_mem.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {f : Option (β k) → Option (β k)}, k ∈ t → (t.alter k f).size = t.size := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _ (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_ofList_of_mem.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        List.Pairwise (fun (a b : (a : α) × β a) => ¬cmp a.fst b.fst = Ordering.eq) l →
          k ∈ List.map Sigma.fst l → (Std.DTreeMap.ofList l cmp).getKey? k' = Option.some k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_ofList_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List ((a : α) × β a)} {k k' : α},
        cmp k k' = Ordering.eq → k ∈ List.map Sigma.fst l → (Std.DTreeMap.ofList l cmp).getKey? k' = Option.some k := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a), (⟨Bool.true, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.getKey?_ofList_of_mem.h9.inst : Not
      (@Eq (Option Nat)
        (@Std.DTreeMap.getKey? Nat (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat)
            (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) fun (a b : Nat) =>
            @Ord.compare Nat instOrdNat a b)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.getKey?_ofList_of_mem.h9.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.getKey?_ofList_of_mem.h9.prem1 : @List.Pairwise (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)
      (fun (a b : @Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a) =>
        Not
          (@Eq Ordering
            ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
              (@Sigma.fst Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) a)
              (@Sigma.fst Nat (fun (a : Nat) => (fun (a : Nat) => Nat) a) b))
            Ordering.eq))
      (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.getKey?_ofList_of_mem.h9 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : @Std.TransCmp α cmp]
        {l : List (@Sigma α fun (a : α) => β a)} {k k' : α},
        @Eq Ordering (cmp k k') Ordering.eq →
          @List.Pairwise (@Sigma α fun (a : α) => β a)
              (fun (a b : @Sigma α fun (a : α) => β a) =>
                Not
                  (@Eq Ordering (cmp (@Sigma.fst α (fun (a : α) => β a) a) (@Sigma.fst α (fun (a : α) => β a) b))
                    Ordering.eq))
              l →
            @Eq (Option α) (@Std.DTreeMap.getKey? α β cmp (@Std.DTreeMap.ofList α β l cmp) k') (@Option.some α k)) := fun hc_h => HypCheckProof.Std.DTreeMap.getKey?_ofList_of_mem.h9.inst (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@List.nil (@Sigma Nat fun (a : Nat) => (fun (a : Nat) => Nat) a)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.DTreeMap.getKey?_ofList_of_mem.h9.prem0 HypCheckProof.Std.DTreeMap.getKey?_ofList_of_mem.h9.prem1)

-- Std.DTreeMap.Const.getKey!_unitOfList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h7.inst : ¬(Std.DTreeMap.Const.unitOfList [1] fun (a b : Nat) => Ord.compare a b).getKey! 0 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [1] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h7.prem1 : 1 ∈ [1] := by
  decide
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Inhabited α] {l : List α} {k k' : α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
          k ∈ l → (Std.DTreeMap.Const.unitOfList l cmp).getKey! k' = k := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([1]) (1) (0) HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h7.prem0 HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h7.prem1)

-- Std.DTreeMap.Const.getKey!_unitOfList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Inhabited α] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → k ∈ l → (Std.DTreeMap.Const.unitOfList l cmp).getKey! k' = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey!_unitOfList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h9.inst : ¬(Std.DTreeMap.Const.unitOfList [] fun (a b : Nat) => Ord.compare a b).getKey! 1 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h9.prem0 : (fun (a b : Nat) => Ord.compare a b) 1 1 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h9.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Inhabited α] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (Std.DTreeMap.Const.unitOfList l cmp).getKey! k' = k := fun hc_h => HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h9.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([]) (1) (1) HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h9.prem0 HypCheckProof.Std.DTreeMap.Const.getKey!_unitOfList_of_mem.h9.prem1)

-- Std.DTreeMap.equiv_of_beq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.equiv_of_beq.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {m₁ m₂ : Std.DTreeMap α β cmp} [inst : (k : α) → BEq (β k)]
        [inst_1 : Std.LawfulEqCmp cmp] [inst_2 : Std.TransCmp cmp] [inst : ∀ (k : α), LawfulBEq (β k)], m₁.Equiv m₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (fun (k : Nat) => instBEqOfDecidableEq) _ _ _) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_of_mem_insertManyIfNewUnit_list, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_of_mem_insertManyIfNewUnit_list.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List α} {k : α},
        l.contains k = Bool.false → k ∈ Std.DTreeMap.Const.insertManyIfNewUnit t l → k ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([Bool.false]) (Bool.true) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_of_mem_insertManyIfNewUnit_list, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_of_mem_insertManyIfNewUnit_list.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List α} {k : α},
        k ∈ Std.DTreeMap.Const.insertManyIfNewUnit t l → k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_of_mem_insertManyIfNewUnit_list, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_of_mem_insertManyIfNewUnit_list.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst_1 : Std.LawfulBEqCmp cmp] {l : List α} {k : α}, l.contains k = Bool.false → k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List α} {k : α},
        ¬k ∈ t → l.contains k = Bool.false → (Std.DTreeMap.Const.insertManyIfNewUnit t l).getKey? k = Option.none := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([Bool.false]) (Bool.true) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List α} {k : α},
        ¬k ∈ t → (Std.DTreeMap.Const.insertManyIfNewUnit t l).getKey? k = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_unitOfList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h7.inst : ¬(Std.TreeMap.unitOfList [0] fun (a b : Nat) => Ord.compare a b).getKeyD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h7.prem1 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' fallback : α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
          k ∈ l → (Std.TreeMap.unitOfList l cmp).getKeyD k' fallback = k := fun hc_h => HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (1) (1) HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h7.prem0 HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h7.prem1)

-- Std.TreeMap.getKeyD_unitOfList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' fallback : α},
        cmp k k' = Ordering.eq → k ∈ l → (Std.TreeMap.unitOfList l cmp).getKeyD k' fallback = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_unitOfList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h9.inst : ¬(Std.TreeMap.unitOfList [] fun (a b : Nat) => Ord.compare a b).getKeyD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h9.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h9.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' fallback : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (Std.TreeMap.unitOfList l cmp).getKeyD k' fallback = k := fun hc_h => HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h9.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) (1) HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h9.prem0 HypCheckProof.Std.TreeMap.getKeyD_unitOfList_of_mem.h9.prem1)

-- Std.TreeMap.equiv_of_beq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.equiv_of_beq.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {m₁ m₂ : Std.TreeMap α β cmp} [inst : BEq β]
        [inst_1 : Std.TransCmp cmp] [inst_2 : Std.LawfulEqCmp cmp] [inst : LawfulBEq β], m₁.Equiv m₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (instBEqOfDecidableEq) _ _ _) (by
  decide +kernel)

-- Std.TreeMap.mem_of_mem_insertManyIfNewUnit_list, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_insertManyIfNewUnit_list.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        {l : List α} {k : α}, l.contains k = Bool.false → k ∈ t.insertManyIfNewUnit l → k ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([Bool.false]) (Bool.true) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.mem_of_mem_insertManyIfNewUnit_list, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_insertManyIfNewUnit_list.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] {l : List α} {k : α}, k ∈ t.insertManyIfNewUnit l → k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.mem_of_mem_insertManyIfNewUnit_list, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_insertManyIfNewUnit_list.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List α} {k : α}, l.contains k = Bool.false → k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.size_insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.size_insertMany_list.h6.inst : Not
      (@Eq Nat
        (@Std.TreeMap.size Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeMap.insertMany Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (List (Prod Nat Nat))
            (@instForInOfForIn' Id (List (Prod Nat Nat)) (Prod Nat Nat)
              (@inferInstance (Membership (Prod Nat Nat) (List (Prod Nat Nat))) (@List.instMembership (Prod Nat Nat)))
              (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod Nat Nat) Id.instMonad))
            (@Std.TreeMap.ofList Nat Nat
              (@List.cons (Prod Nat Nat)
                (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@List.nil (Prod Nat Nat)))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@List.cons (Prod Nat Nat)
              (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@List.nil (Prod Nat Nat)))))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@Std.TreeMap.size Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@Std.TreeMap.ofList Nat Nat
              (@List.cons (Prod Nat Nat)
                (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@List.nil (Prod Nat Nat)))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b))
          (@List.length (Prod Nat Nat)
            (@List.cons (Prod Nat Nat)
              (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@List.nil (Prod Nat Nat)))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.size_insertMany_list.h6.prem0 : @List.Pairwise (Prod Nat Nat)
      (fun (a b : Prod Nat Nat) =>
        Not
          (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Prod.fst Nat Nat a) (@Prod.fst Nat Nat b))
            Ordering.eq))
      (@List.cons (Prod Nat Nat)
        (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (Prod Nat Nat))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.size_insertMany_list.h6.prem1 : ∀ (a : Nat),
      @Membership.mem Nat (Std.TreeMap Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeMap.instMembership Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeMap.ofList Nat Nat
            (@List.cons (Prod Nat Nat)
              (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@List.nil (Prod Nat Nat)))
            fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          a →
        @Eq Bool
          (@List.contains Nat (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b)
            (@List.map (Prod Nat Nat) Nat (@Prod.fst Nat Nat)
              (@List.cons (Prod Nat Nat)
                (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@List.nil (Prod Nat Nat))))
            a)
          Bool.false := by
  simp
theorem HypCheckProof.Std.TreeMap.size_insertMany_list.h6 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : @Std.TransCmp α cmp] [inst : BEq α]
        {l : List (Prod α β)},
        @List.Pairwise (Prod α β)
            (fun (a b : Prod α β) => Not (@Eq Ordering (cmp (@Prod.fst α β a) (@Prod.fst α β b)) Ordering.eq)) l →
          (∀ (a : α),
              @Membership.mem α (Std.TreeMap α β cmp) (@Std.TreeMap.instMembership α β cmp) t a →
                @Eq Bool (@List.contains α inst (@List.map (Prod α β) α (@Prod.fst α β) l) a) Bool.false) →
            @Eq Nat
              (@Std.TreeMap.size α β cmp
                (@Std.TreeMap.insertMany α β cmp (List (Prod α β))
                  (@instForInOfForIn' Id (List (Prod α β)) (Prod α β)
                    (@inferInstance (Membership (Prod α β) (List (Prod α β))) (@List.instMembership (Prod α β)))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id (Prod α β) Id.instMonad))
                  t l))
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Std.TreeMap.size α β cmp t) (@List.length (Prod α β) l))) := fun hc_h => HypCheckProof.Std.TreeMap.size_insertMany_list.h6.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Nat
      (@List.cons (Prod Nat Nat)
        (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (Prod Nat Nat)))
      fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) (@List.cons (Prod Nat Nat)
      (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (Prod Nat Nat))) HypCheckProof.Std.TreeMap.size_insertMany_list.h6.prem0 HypCheckProof.Std.TreeMap.size_insertMany_list.h6.prem1)

-- Std.TreeMap.size_insertMany_list, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_insertMany_list.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List (α × β)},
        (∀ (a : α), a ∈ t → (List.map Prod.fst l).contains a = Bool.false) → (t.insertMany l).size = t.size + l.length := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0), (0, 1)]) (by
  simp)) (by
  decide +kernel)

-- Std.TreeMap.size_insertMany_list, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.size_insertMany_list.h9.inst : ¬((Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b).insertMany [(0, 0)]).size =
        (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b).size + [(0, 0)].length := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.size_insertMany_list.h9.prem0 : List.Pairwise (fun (a b : Nat × Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a.fst b.fst = Ordering.eq) [(0, 0)] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.size_insertMany_list.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] {l : List (α × β)},
        List.Pairwise (fun (a b : α × β) => ¬cmp a.fst b.fst = Ordering.eq) l → (t.insertMany l).size = t.size + l.length := fun hc_h => HypCheckProof.Std.TreeMap.size_insertMany_list.h9.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) HypCheckProof.Std.TreeMap.size_insertMany_list.h9.prem0)

-- Std.TreeSet.get!_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h7.inst : ¬(Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b).get! 0 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [1] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h7.prem1 : 1 ∈ [1] := by
  decide
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Inhabited α] {l : List α} {k k' : α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (Std.TreeSet.ofList l cmp).get! k' = k := fun hc_h => HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([1]) (1) (0) HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h7.prem0 HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h7.prem1)

-- Std.TreeSet.get!_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Inhabited α] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → k ∈ l → (Std.TreeSet.ofList l cmp).get! k' = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get!_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h9.inst : ¬(Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).get! 1 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h9.prem0 : (fun (a b : Nat) => Ord.compare a b) 1 1 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h9.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : Inhabited α] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (Std.TreeSet.ofList l cmp).get! k' = k := fun hc_h => HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h9.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([]) (1) (1) HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h9.prem0 HypCheckProof.Std.TreeSet.get!_ofList_of_mem.h9.prem1)

-- Std.TreeSet.getD_ofList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h7.inst : ¬(Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b).getD 1 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h7.prem0 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h7.prem1 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' fallback : α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → k ∈ l → (Std.TreeSet.ofList l cmp).getD k' fallback = k := fun hc_h => HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (1) (1) HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h7.prem0 HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h7.prem1)

-- Std.TreeSet.getD_ofList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' fallback : α},
        cmp k k' = Ordering.eq → k ∈ l → (Std.TreeSet.ofList l cmp).getD k' fallback = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.getD_ofList_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h9.inst : ¬(Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b).getD 0 1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h9.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h9.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' fallback : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (Std.TreeSet.ofList l cmp).getD k' fallback = k := fun hc_h => HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h9.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) (1) HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h9.prem0 HypCheckProof.Std.TreeSet.getD_ofList_of_mem.h9.prem1)

-- Std.DTreeMap.Equiv.forM_eq, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.forM_eq.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} {m : Type → Type}
        [inst : Std.TransCmp cmp] [inst : Monad m] [inst_1 : LawfulMonad m] {f : (a : α) × β a → m PUnit},
        ForM.forM t₁ f = ForM.forM t₂ f := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Option : Type → Type) _ (instMonadOption) _ (fun (a : (a : Nat) × (fun (a : Nat) => Nat) a) => Option.none)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List ((a : α) × β a)} {k fallback : α},
        (List.map Sigma.fst l).contains k = Bool.false → (t.insertMany l).getKeyD k fallback = t.getKeyD k fallback := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(⟨Bool.true, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k fallback : α},
        (t.insertMany l).getKeyD k fallback = t.getKeyD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKeyD_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List (α × β)} {k fallback : α},
        (List.map Prod.fst l).contains k = Bool.false →
          (Std.DTreeMap.Const.insertMany t l).getKeyD k fallback = t.getKeyD k fallback := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKeyD_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k fallback : α},
        (Std.DTreeMap.Const.insertMany t l).getKeyD k fallback = t.getKeyD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey?_le_maxKey?_insertIfNew, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey?_le_maxKey?_insertIfNew.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k} {km kmi : α},
        (t.insertIfNew k v).maxKey?.get Std.DTreeMap.isSome_maxKey?_insertIfNew = kmi → (cmp km kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (1) (0) (by
  grind)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey?_le_maxKey?_insertIfNew, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey?_le_maxKey?_insertIfNew.h10 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k} {km kmi : α}, t.maxKey? = Option.some km → (cmp km kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (1) (0) (by
  grind)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst_1 : Inhabited β] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false →
          Std.DTreeMap.Const.get! (Std.DTreeMap.Const.insertMany t l) k = Std.DTreeMap.Const.get! t k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) (instInhabitedNat) ([(Bool.false, 1)]) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] [inst : Inhabited β] {l : List (α × β)} {k : α},
        Std.DTreeMap.Const.get! (Std.DTreeMap.Const.insertMany t l) k = Std.DTreeMap.Const.get! t k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([(0, 1)]) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.compare_minKey?_modify_eq, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.compare_minKey?_modify_eq.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k : α} {f : β → β} {km kmm : α}, t.minKey? = Option.some km → cmp kmm km = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (fun n => n + 1 : Nat → Nat) (0) (1) (by
  grind)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List (α × β)} {k : α} {fallback : β},
        (List.map Prod.fst l).contains k = Bool.false →
          Std.DTreeMap.Const.getD (Std.DTreeMap.Const.insertMany t l) k fallback = Std.DTreeMap.Const.getD t k fallback := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (1) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_insertMany_list_of_contains_eq_false, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insertMany_list_of_contains_eq_false.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α} {fallback : β},
        Std.DTreeMap.Const.getD (Std.DTreeMap.Const.insertMany t l) k fallback = Std.DTreeMap.Const.getD t k fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.Equiv.beq_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.Equiv.beq_congr.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {m₁ m₂ : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : BEq β]
        [inst_1 : Std.TransCmp cmp] {m₃ m₄ : Std.DTreeMap α (fun (x : α) => β) cmp},
        m₂.Equiv m₄ → Std.DTreeMap.Const.beq m₁ m₂ = Std.DTreeMap.Const.beq m₃ m₄ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (instBEqOfDecidableEq) _ (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.Equiv.beq_congr, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.Equiv.beq_congr.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {m₁ m₂ : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : BEq β]
        [inst_1 : Std.TransCmp cmp] {m₃ m₄ : Std.DTreeMap α (fun (x : α) => β) cmp},
        m₁.Equiv m₃ → Std.DTreeMap.Const.beq m₁ m₂ = Std.DTreeMap.Const.beq m₃ m₄ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (instBEqOfDecidableEq) _ (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.compare_maxKey?_modify_eq, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.compare_maxKey?_modify_eq.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {f : β → β}
        {km kmm : α}, t.maxKey? = Option.some km → cmp kmm km = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (fun n => n + 1 : Nat → Nat) (0) (1) (by
  grind)) (by
  decide +kernel)

-- Std.TreeMap.compare_minKey?_modify_eq, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.compare_minKey?_modify_eq.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {f : β → β}
        {km kmm : α}, t.minKey? = Option.some km → cmp kmm km = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (fun n => n + 1 : Nat → Nat) (0) (1) (by
  grind)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.forM_eq, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.forM_eq.h10 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} {m : Type → Type} [inst : Std.TransCmp cmp]
        [inst : Monad m] [inst_1 : LawfulMonad m] {f : α × β → m PUnit}, ForM.forM t₁ f = ForM.forM t₂ f := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Option : Type → Type) _ (instMonadOption) _ (fun (a : Nat × Nat) => Option.none)) (by
  decide +kernel)

-- Std.TreeMap.contains_of_contains_insertIfNew, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.contains_of_contains_insertIfNew.h8.inst : Not
      (@Eq Bool
        (@Std.TreeMap.contains Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        Bool.true) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.contains_of_contains_insertIfNew.h8.prem0 : @Ne Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.contains_of_contains_insertIfNew.h8 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : @Std.TransCmp α cmp] {k a : α} {v : β},
        @Ne Ordering (cmp k a) Ordering.eq → @Eq Bool (@Std.TreeMap.contains α β cmp t a) Bool.true) := fun hc_h => HypCheckProof.Std.TreeMap.contains_of_contains_insertIfNew.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.TreeMap.contains_of_contains_insertIfNew.h8.prem0)

-- Std.TreeMap.contains_of_contains_insertIfNew, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_of_contains_insertIfNew.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α} {v : β},
        (t.insertIfNew k v).contains a = Bool.true → t.contains a = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.get!_union_of_not_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_union_of_not_mem_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α} [inst : Inhabited (β k)], ¬k ∈ t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (by
  decide)) (by
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

-- Std.DTreeMap.contains_alter_of_not_compare_eq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_alter_of_not_compare_eq.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k k' : α} {f : Option (β k) → Option (β k)}, (t.alter k f).contains k' = t.contains k' := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.some 0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_map.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.LawfulEqCmp cmp] {f : α → β → γ} {k : α} {h' : k ∈ Std.DTreeMap.map f t}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (fun a b => a - b : Nat → Nat → Nat) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_map, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_map.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp] {f : α → β → γ} {k : α}, k ∈ Std.DTreeMap.map f t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getD_diff_of_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_diff_of_mem_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β k}, k ∈ t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0) (by
  decide)) (by
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

-- Std.DTreeMap.getD_diff_of_mem_right, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_diff_of_mem_right.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {fallback : β k}, (t₁ \ t₂).getD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.get_alter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_alter.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {k k' : α}
        {f : Option (β k) → Option (β k)} {hc : k' ∈ t.alter k f}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.some 0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_alter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_alter.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {k' : α} {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.get_alter, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_alter.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k k' : α} {f : Option (β k) → Option (β k)}, k' ∈ t.alter k f := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (0) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.none)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false →
          Std.DTreeMap.Const.get? (Std.DTreeMap.Const.insertMany t l) k = Std.DTreeMap.Const.get? t k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        Std.DTreeMap.Const.get? (Std.DTreeMap.Const.insertMany t l) k = Std.DTreeMap.Const.get? t k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKeyD_ofList_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_contains_eq_false.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List (α × β)}
        {k fallback : α},
        (List.map Prod.fst l).contains k = Bool.false → (Std.DTreeMap.Const.ofList l cmp).getKeyD k fallback = fallback := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKeyD_ofList_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_ofList_of_contains_eq_false.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List (α × β)} {k fallback : α}, (Std.DTreeMap.Const.ofList l cmp).getKeyD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getD_union_of_not_mem_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_union_of_not_mem_left.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β k}, ¬k ∈ t₁ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0) (by
  decide)) (by
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

-- Std.DTreeMap.getD_union_of_not_mem_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_union_of_not_mem_left.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {fallback : β k}, (t₁ ∪ t₂).getD k fallback = t₂.getD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_ofList_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_contains_eq_false.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α]
        {l : List ((a : α) × β a)} {k fallback : α},
        (List.map Sigma.fst l).contains k = Bool.false → (Std.DTreeMap.ofList l cmp).getKeyD k fallback = fallback := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(⟨Bool.true, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.false) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_ofList_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_ofList_of_contains_eq_false.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k fallback : α},
        (Std.DTreeMap.ofList l cmp).getKeyD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.get!_inter_of_not_mem_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_inter_of_not_mem_left.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α} [inst : Inhabited (β k)], ¬k ∈ t₁ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (by
  decide)) (by
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

-- Std.TreeMap.getD_ofList_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_contains_eq_false.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List (α × β)} {k : α}
        {fallback : β},
        (List.map Prod.fst l).contains k = Bool.false → (Std.TreeMap.ofList l cmp).getD k fallback = fallback := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (1) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getD_ofList_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_ofList_of_contains_eq_false.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List (α × β)} {k : α} {fallback : β}, (Std.TreeMap.ofList l cmp).getD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_ofList_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_contains_eq_false.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List (α × β)} {k : α}
        [inst_1 : Inhabited β],
        (List.map Prod.fst l).contains k = Bool.false →
          Std.DTreeMap.Const.get! (Std.DTreeMap.Const.ofList l cmp) k = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 1)]) (Bool.true) (instInhabitedNat) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_ofList_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_ofList_of_contains_eq_false.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List (α × β)} {k : α} [inst : Inhabited β],
        Std.DTreeMap.Const.get! (Std.DTreeMap.Const.ofList l cmp) k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) _ (instBEqOfDecidableEq) _ ([(0, 1)]) (0) (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.maxKey?_erase_le_maxKey?, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey?_erase_le_maxKey?.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {km : α} {kme : α},
        (t.erase k).maxKey? = Option.some kme := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0)) (by
  simp)

-- Std.TreeMap.getElem_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_map.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {f : α → β → γ}
        {k : α} {h' : k ∈ Std.TreeMap.map f t}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (fun a b => a - b : Nat → Nat → Nat) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_map, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_map.h9 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {f : α → β → γ} {k : α}, k ∈ Std.TreeMap.map f t := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        {l : List (α × β)} {k : α}, (List.map Prod.fst l).contains k = Bool.false → (t.insertMany l).getKey? k = t.getKey? k := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α}, (t.insertMany l).getKey? k = t.getKey? k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0)) (by
  decide +kernel)

-- Std.TreeMap.contains_of_contains_insert, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.contains_of_contains_insert.h8.inst : Not
      (@Eq Bool
        (@Std.TreeMap.contains Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        Bool.true) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.contains_of_contains_insert.h8.prem0 : @Ne Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.contains_of_contains_insert.h8 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : @Std.TransCmp α cmp] {k a : α} {v : β},
        @Ne Ordering (cmp k a) Ordering.eq → @Eq Bool (@Std.TreeMap.contains α β cmp t a) Bool.true) := fun hc_h => HypCheckProof.Std.TreeMap.contains_of_contains_insert.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.TreeMap.contains_of_contains_insert.h8.prem0)

-- Std.TreeMap.contains_of_contains_insert, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_of_contains_insert.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α} {v : β},
        (t.insert k v).contains a = Bool.true → t.contains a = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.modify, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.modify.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] (k : α) (f : β → β), (t₁.modify k f).Equiv (t₂.modify k f) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ _ (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_unitOfList_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h6.inst : ¬(Std.TreeMap.unitOfList [0] fun (a b : Nat) => Ord.compare a b).getKey? 1 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h6.prem0 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h6.prem1 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
          k ∈ l → (Std.TreeMap.unitOfList l cmp).getKey? k' = Option.some k := fun hc_h => HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h6.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (1) HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h6.prem0 HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h6.prem1)

-- Std.TreeMap.getKey?_unitOfList_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq → k ∈ l → (Std.TreeMap.unitOfList l cmp).getKey? k' = Option.some k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true]) (Bool.true) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_unitOfList_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h8.inst : ¬(Std.TreeMap.unitOfList [] fun (a b : Nat) => Ord.compare a b).getKey? 0 = Option.some 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h8.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h8.prem1 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α} {k k' : α},
        cmp k k' = Ordering.eq →
          List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l →
            (Std.TreeMap.unitOfList l cmp).getKey? k' = Option.some k := fun hc_h => HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ ([]) (0) (0) HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h8.prem0 HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_mem.h8.prem1)

-- Std.DTreeMap.get_modify, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_modify.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {k k' : α}
        {f : β k → β k} {hc : k' ∈ t.modify k f}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {k' : α} {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.get_modify, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_modify.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k k' : α} {f : β k → β k}, k' ∈ t.modify k f := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.alter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.alter.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.Equiv t₂ → ∀ (k : α) (f : Option (β k) → Option (β k)), Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (by
  rfl) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.Equiv.alter, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.alter.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] (k : α) (f : Option (β k) → Option (β k)), (t₁.alter k f).Equiv (t₂.alter k f) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _ (1) (fun (a : Option ((fun (a : Nat) => Nat) 1)) => Option.none)) (by
  decide +kernel)

-- Std.TreeMap.mem_of_mem_insertIfNew, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_insertIfNew.h8.inst : Not
      (@Membership.mem Nat (Std.TreeMap Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.instMembership Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_insertIfNew.h8.prem0 : @Ne Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.mem_of_mem_insertIfNew.h8 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : @Std.TransCmp α cmp] {k a : α} {v : β},
        @Ne Ordering (cmp k a) Ordering.eq →
          @Membership.mem α (Std.TreeMap α β cmp) (@Std.TreeMap.instMembership α β cmp) t a) := fun hc_h => HypCheckProof.Std.TreeMap.mem_of_mem_insertIfNew.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.TreeMap.mem_of_mem_insertIfNew.h8.prem0)

-- Std.TreeMap.mem_of_mem_insertIfNew, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_insertIfNew.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α} {v : β},
        a ∈ t.insertIfNew k v → a ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.diff_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.diff_congr.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ t₄ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₂.Equiv t₄ → (t₁ \ t₂).Equiv (t₃ \ t₄) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.diff_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.diff_congr.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ t₄ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.Equiv t₃ → (t₁ \ t₂).Equiv (t₃ \ t₄) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.size_insertManyIfNewUnit_list, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_insertManyIfNewUnit_list.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List α},
        (∀ (a : α), a ∈ t → l.contains a = Bool.false) → (t.insertManyIfNewUnit l).size = t.size + l.length := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([0, 0]) (by
  simp)) (by
  decide +kernel)

-- Std.TreeMap.getElem_filterMap', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_filterMap'.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {f : α → β → Option γ}
        {k : α} {h : k ∈ Std.TreeMap.filterMap f t}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (fun (a : Nat) => Option.some) (0) (by
  decide +kernel)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_filterMap', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_filterMap'.h6 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → Option γ}
        {k : α} {h : k ∈ Std.TreeMap.filterMap f t}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (Nat) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (fun (a : Bool) => Option.some) (Bool.false) (by
  decide +kernel)) (by
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

-- Std.TreeMap.getElem_filterMap', hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_filterMap'.h9 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {f : α → β → Option γ} {k : α}, k ∈ Std.TreeMap.filterMap f t := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (fun (a x : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.DTreeMap.get!_diff_of_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_diff_of_mem_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α} [inst : Inhabited (β k)], k ∈ t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (by
  decide)) (by
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

-- Std.DTreeMap.minKey?_le_minKey?_erase, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey?_le_minKey?_erase.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {km : α} {kme : α}, (t.erase k).minKey? = Option.some kme := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0)) (by
  simp)

-- Std.TreeSet.size_insertMany_list, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.size_insertMany_list.h5.inst : Not
      (@Eq Nat
        (@Std.TreeSet.size Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeSet.insertMany Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (List Nat)
            (@instForInOfForIn' Id (List Nat) Nat (@inferInstance (Membership Nat (List Nat)) (@List.instMembership Nat))
              (@List.instForIn'InferInstanceMembershipOfMonad Id Nat Id.instMonad))
            (@Std.TreeSet.ofList Nat
              (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) fun (a b : Nat) =>
              @Ord.compare Nat instOrdNat a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@Std.TreeSet.size Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@Std.TreeSet.ofList Nat
              (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) fun (a b : Nat) =>
              @Ord.compare Nat instOrdNat a b))
          (@List.length Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.size_insertMany_list.h5.prem0 : @List.Pairwise Nat
      (fun (a b : Nat) => Not (@Eq Ordering ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) a b) Ordering.eq))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.size_insertMany_list.h5.prem1 : ∀ (a : Nat),
      @Membership.mem Nat (Std.TreeSet Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeSet.instMembership Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeSet.ofList Nat
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) fun (a b : Nat) =>
            @Ord.compare Nat instOrdNat a b)
          a →
        @Eq Bool
          (@List.contains Nat (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) a)
          Bool.false := by
  simp
theorem HypCheckProof.Std.TreeSet.size_insertMany_list.h5 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : @Std.TransCmp α cmp] [inst : BEq α]
        {l : List α},
        @List.Pairwise α (fun (a b : α) => Not (@Eq Ordering (cmp a b) Ordering.eq)) l →
          (∀ (a : α),
              @Membership.mem α (Std.TreeSet α cmp) (@Std.TreeSet.instMembership α cmp) t a →
                @Eq Bool (@List.contains α inst l a) Bool.false) →
            @Eq Nat
              (@Std.TreeSet.size α cmp
                (@Std.TreeSet.insertMany α cmp (List α)
                  (@instForInOfForIn' Id (List α) α (@inferInstance (Membership α (List α)) (@List.instMembership α))
                    (@List.instForIn'InferInstanceMembershipOfMonad Id α Id.instMonad))
                  t l))
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Std.TreeSet.size α cmp t) (@List.length α l))) := fun hc_h => HypCheckProof.Std.TreeSet.size_insertMany_list.h5.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeSet.ofList Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))
      fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@BEq.mk Nat fun (a b : Nat) => @bne Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) HypCheckProof.Std.TreeSet.size_insertMany_list.h5.prem0 HypCheckProof.Std.TreeSet.size_insertMany_list.h5.prem1)

-- Std.TreeSet.size_insertMany_list, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.size_insertMany_list.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : Std.LawfulBEqCmp cmp] {l : List α},
        (∀ (a : α), a ∈ t → l.contains a = Bool.false) → (t.insertMany l).size = t.size + l.length := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([0, 0]) (by
  simp)) (by
  decide +kernel)

-- Std.TreeSet.size_insertMany_list, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.size_insertMany_list.h8.inst : ¬((Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b).insertMany [0]).size =
        (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b).size + [0].length := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.size_insertMany_list.h8.prem0 : List.Pairwise (fun (a b : Nat) => ¬(fun (a b : Nat) => Ord.compare a b) a b = Ordering.eq) [0] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeSet.size_insertMany_list.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst : Std.LawfulBEqCmp cmp] {l : List α},
        List.Pairwise (fun (a b : α) => ¬cmp a b = Ordering.eq) l → (t.insertMany l).size = t.size + l.length := fun hc_h => HypCheckProof.Std.TreeSet.size_insertMany_list.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([0]) HypCheckProof.Std.TreeSet.size_insertMany_list.h8.prem0)

-- Std.DTreeMap.get_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_insert.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {k a : α}
        {v : β k} {h₁ : a ∈ t.insert k v}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_insert.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α}
        {v : β k} {h₁ : a ∈ t.insert k v}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (0) (by
  decide)) (by
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

-- Std.DTreeMap.get_insert, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_insert.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k a : α} {v : β k}, a ∈ t.insert k v := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.size_insertManyIfNewUnit_list, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.size_insertManyIfNewUnit_list.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst_1 : Std.LawfulBEqCmp cmp] {l : List α},
        (∀ (a : α), a ∈ t → l.contains a = Bool.false) →
          (Std.DTreeMap.Const.insertManyIfNewUnit t l).size = t.size + l.length := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([0, 0]) (by
  simp)) (by
  decide +kernel)

-- Std.DTreeMap.get!_diff_of_not_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_diff_of_not_mem_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α} [inst : Inhabited (β k)], ¬k ∈ t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (by
  decide)) (by
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

-- Std.DTreeMap.mem_alter_of_compare_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_alter_of_compare_eq.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k k' : α}
        {f : Option (β k) → Option (β k)}, cmp k k' = Ordering.eq → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none) (by
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

-- Std.DTreeMap.mem_alter_of_compare_eq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_alter_of_compare_eq.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k k' : α} {f : Option (β k) → Option (β k)},
        k' ∈ t.alter k f ↔ (f (t.get? k)).isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1) (fun (a : Option ((fun (a : Nat) => Nat) 0)) => Option.some 0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKeyD_alter_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKeyD_alter_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option (β k) → Option (β k)} {fallback : α}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none) (Bool.false)) (by
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

-- Std.DTreeMap.getD_diff_of_not_mem_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_diff_of_not_mem_left.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β k}, ¬k ∈ t₁ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0) (by
  decide)) (by
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

-- Std.DTreeMap.getD_diff_of_not_mem_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_diff_of_not_mem_left.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {fallback : β k}, (t₁ \ t₂).getD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getD_union_of_not_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_union_of_not_mem_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β k}, ¬k ∈ t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0) (by
  decide)) (by
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

-- Std.DTreeMap.getD_union_of_not_mem_right, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_union_of_not_mem_right.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {fallback : β k}, (t₁ ∪ t₂).getD k fallback = t₁.getD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.mem_of_mem_insertIfNew', hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_insertIfNew'.h8.inst : Not
      (@Membership.mem Nat (Std.DTreeMap Nat (fun (a : Nat) => Nat) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.DTreeMap.instMembership Nat (fun (a : Nat) => Nat) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
          @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_insertIfNew'.h8.prem0 : Not
      (And
        (@Eq Ordering
          ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          Ordering.eq)
        (Not
          (@Membership.mem Nat (Std.DTreeMap Nat (fun (a : Nat) => Nat) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@Std.DTreeMap.instMembership Nat (fun (a : Nat) => Nat) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_insertIfNew'.h8 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        {k a : α} {v : β k},
        Not
            (And (@Eq Ordering (cmp k a) Ordering.eq)
              (Not (@Membership.mem α (Std.DTreeMap α β cmp) (@Std.DTreeMap.instMembership α β cmp) t k))) →
          @Membership.mem α (Std.DTreeMap α β cmp) (@Std.DTreeMap.instMembership α β cmp) t a) := fun hc_h => HypCheckProof.Std.DTreeMap.mem_of_mem_insertIfNew'.h8.inst (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.DTreeMap.mem_of_mem_insertIfNew'.h8.prem0)

-- Std.DTreeMap.mem_of_mem_insertIfNew', hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_insertIfNew'.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α}
        {v : β k}, a ∈ t.insertIfNew k v → a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getD_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getD_eq.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {fallback : β k}, t₁.Equiv t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0) (by
  rfl)) (by
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

-- Std.DTreeMap.Equiv.getD_eq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getD_eq.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {fallback : β k}, t₁.getD k fallback = t₂.getD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.minKey!_alter_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey!_alter_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α} {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.getKey_modify_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_modify_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α} {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.getKey_modify_self, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_modify_self.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst_1 : Inhabited α] {k : α} {f : β k → β k}, k ∈ t.modify k f := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instInhabitedNat) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey?_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → (Std.DTreeMap.Const.insertMany t l).getKey? k = t.getKey? k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey?_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List (α × β)} {k : α},
        (Std.DTreeMap.Const.insertMany t l).getKey? k = t.getKey? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_insertMany_list_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_insertMany_list_of_contains_eq_false.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List ((a : α) × β a)} {k : α},
        (List.map Sigma.fst l).contains k = Bool.false → (t.insertMany l).getKey? k = t.getKey? k := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(⟨Bool.false, 0⟩ : (a : Bool) × (fun (a : Bool) => Nat) a)]) (Bool.true) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_insertMany_list_of_contains_eq_false, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_insertMany_list_of_contains_eq_false.h9 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst : Std.LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α},
        (t.insertMany l).getKey? k = t.getKey? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instBEqOfDecidableEq) _ ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.modify, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.modify.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.Equiv t₂ → ∀ (k : α) (f : β k → β k), Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (by
  rfl) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.Equiv.modify, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.modify.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] (k : α) (f : β k → β k), (t₁.modify k f).Equiv (t₂.modify k f) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _ (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.getD_map_of_getKey?_eq_some, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_map_of_getKey?_eq_some.h11 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited γ]
        {f : α → β → γ} {k k' : α} {fallback : γ},
        (Std.TreeMap.map f t).getD k fallback = (Option.map (f k') t[k]?).getD fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (fun a b => a - b : Nat → Nat → Nat) (0) (1) (0)) (by
  decide +kernel)

-- Std.TreeMap.maxKey_modify_eq_maxKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_modify_eq_maxKey.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {k : α} {f : β → β}
        {he : (t.modify k f).isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.maxKey_modify_eq_maxKey, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_modify_eq_maxKey.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {f : β → β}, (t.modify k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.getElem_union_of_not_mem_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_union_of_not_mem_right.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} {k : α},
        ¬k ∈ t₂ → ∀ {h' : k ∈ t₁ ∪ t₂}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_union_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_union_of_not_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : k ∈ t₁ ∪ t₂}, ¬k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getElem_union_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_union_of_not_mem_right.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        ¬k ∈ t₂ → k ∈ t₁ ∪ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.minKey?_le_of_contains, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey?_le_of_contains.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {km : α},
        t.contains k = Bool.true → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.minKey?_le_of_contains, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey?_le_of_contains.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {km : α},
        t.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeMap.minKey?_le_of_contains, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey?_le_of_contains.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k km : α},
        t.contains k = Bool.true → (cmp km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_eq_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_eq_of_mem.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        k ∈ t → t.getKeyD k fallback = k := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_eq_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_eq_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k fallback : α}, t.getKeyD k fallback = k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryLE_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryLE_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.TreeMap.Equiv.getEntryLE_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryLE_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  simp)) (by
  decide +kernel)

-- Std.TreeMap.getKey_union_of_not_mem_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_union_of_not_mem_right.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} {k : α},
        ¬k ∈ t₂ → ∀ {h' : k ∈ t₁ ∪ t₂}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_union_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_union_of_not_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : k ∈ t₁ ∪ t₂}, ¬k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey_union_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_union_of_not_mem_right.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        ¬k ∈ t₂ → k ∈ t₁ ∪ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.le_maxKey?_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.le_maxKey?_of_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {km : α}, k ∈ t → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.le_maxKey?_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.le_maxKey?_of_mem.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {km : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeMap.le_maxKey?_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.le_maxKey?_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k km : α},
        k ∈ t → (cmp k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare b a : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare b a) _ (0) (1) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.maxKeyD_eq_iff_mem_and_forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKeyD_eq_iff_mem_and_forall.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {km fallback : α},
        t.maxKeyD fallback = km ↔ km ∈ t ∧ ∀ (k : α), k ∈ t → (cmp k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (0)) (by
  simp +ground +decide [Std.TreeMap.maxKeyD, Std.TreeMap.instMembership, Std.DTreeMap.maxKeyD, Std.TreeMap.inner,
    Std.TreeMap.contains, Std.DTreeMap.Internal.Impl.maxKeyD, Std.DTreeMap.inner, Std.DTreeMap.contains,
    Std.DTreeMap.Internal.Impl.contains])

-- Std.TreeMap.getKey?_ofList_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_ofList_of_contains_eq_false.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → (Std.TreeMap.ofList l cmp).getKey? k = Option.none := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_ofList_of_contains_eq_false, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_ofList_of_contains_eq_false.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List (α × β)} {k : α}, (Std.TreeMap.ofList l cmp).getKey? k = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryGE_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryGE_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isGE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.TreeMap.Equiv.getEntryGE_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryGE_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isGE = Bool.true}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  simp)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getKeyLE_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyLE_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.TreeMap.Equiv.getKeyLE_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyLE_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  simp)) (by
  decide +kernel)

-- Std.TreeMap.size_alter_eq_add_one, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.size_alter_eq_add_one.h7.inst : ¬((Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b).alter 0 fun (a : Option Nat) => Option.some 0).size =
        (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b).size + 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.size_alter_eq_add_one.h7.prem0 : ((fun (a : Option Nat) => Option.some 0) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b)[0]?).isSome =
      Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.size_alter_eq_add_one.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option β → Option β}, (f t[k]?).isSome = Bool.true → (t.alter k f).size = t.size + 1 := fun hc_h => HypCheckProof.Std.TreeMap.size_alter_eq_add_one.h7.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (fun (a : Option Nat) => Option.some 0) HypCheckProof.Std.TreeMap.size_alter_eq_add_one.h7.prem0)

-- Std.TreeMap.size_alter_eq_add_one, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_alter_eq_add_one.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option β → Option β}, ¬k ∈ t → (t.alter k f).size = t.size + 1 := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (fun (a : Option Nat) => Option.none) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getKeyLT_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyLT_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.lt := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.TreeMap.Equiv.getKeyLT_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyLT_eq.h8.inst : ¬(Std.TreeMap.ofList [(Bool.false, 0)] fun (a b : Bool) => Ord.compare a b).Equiv
        (Std.TreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyLT_eq.h8.prem0 : ∃ (a : Bool),
      (a ∈ Std.TreeMap.ofList [(Bool.false, 0)] fun (a b : Bool) => Ord.compare a b) ∧
        (fun (a b : Bool) => Ord.compare a b) a Bool.true = Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyLT_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.lt}, t₁.Equiv t₂ := fun hc_h => HypCheckProof.Std.TreeMap.Equiv.getKeyLT_eq.h8.inst (@hc_h (Bool) (Nat) (fun (a b : Bool) => Ord.compare a b) (Std.TreeMap.ofList [(Bool.false, 0)] fun (a b : Bool) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) _ (Bool.true) HypCheckProof.Std.TreeMap.Equiv.getKeyLT_eq.h8.prem0)

-- Std.TreeMap.getKey_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_congr.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k₁ k₂ : α},
        cmp k₁ k₂ = Ordering.eq → k₁ ∈ t → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_congr.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k₁ k₂ : α},
        k₁ ∈ t → cmp k₁ k₂ = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey_congr, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey_congr.h8.inst : Not
      (@Membership.mem Nat (Std.TreeMap Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.instMembership Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getKey_congr.h8.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getKey_congr.h8 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : @Std.TransCmp α cmp] {k₁ k₂ : α},
        @Eq Ordering (cmp k₁ k₂) Ordering.eq →
          @Membership.mem α (Std.TreeMap α β cmp) (@Std.TreeMap.instMembership α β cmp) t k₁) := fun hc_h => HypCheckProof.Std.TreeMap.getKey_congr.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.TreeMap.getKey_congr.h8.prem0)

-- Std.TreeMap.mem_of_mem_union_of_not_mem_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_union_of_not_mem_left.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        ¬k ∈ t₁ → k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.mem_of_mem_union_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_union_of_not_mem_left.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t₁ ∪ t₂ → k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getElem_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_congr.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {a b : α},
        cmp a b = Ordering.eq → ∀ {h' : a ∈ t}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_congr.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a b : α} {h' : a ∈ t},
        cmp a b = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getElem_congr, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem_congr.h8.inst : Not
      (@Membership.mem Nat (Std.TreeMap Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.instMembership Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.getElem_congr.h8.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.getElem_congr.h8 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : @Std.TransCmp α cmp] {a b : α},
        @Eq Ordering (cmp a b) Ordering.eq →
          @Membership.mem α (Std.TreeMap α β cmp) (@Std.TreeMap.instMembership α β cmp) t a) := fun hc_h => HypCheckProof.Std.TreeMap.getElem_congr.h8.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.TreeMap.getElem_congr.h8.prem0)

-- Std.TreeMap.minKeyD_eq_iff_mem_and_forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKeyD_eq_iff_mem_and_forall.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {km fallback : α},
        t.minKeyD fallback = km ↔ km ∈ t ∧ ∀ (k : α), k ∈ t → (cmp km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (0)) (by
  simp +ground +decide [Std.TreeMap.minKeyD, Std.TreeMap.instMembership, Std.DTreeMap.minKeyD, Std.TreeMap.inner,
    Std.TreeMap.contains, Std.DTreeMap.Internal.Impl.minKeyD, Std.DTreeMap.inner, Std.DTreeMap.contains,
    Std.DTreeMap.Internal.Impl.contains])

-- Std.TreeMap.Equiv.entryAtIdx_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.entryAtIdx_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {i : Nat},
        t₁.Equiv t₂ → i < t₁.size := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.entryAtIdx_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.entryAtIdx_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {i : Nat}
        {h' : i < t₁.size}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_ofList_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_contains_eq_false.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false → (Std.TreeMap.ofList l cmp)[k]? = Option.none := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_ofList_of_contains_eq_false, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_ofList_of_contains_eq_false.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List (α × β)} {k : α}, (Std.TreeMap.ofList l cmp)[k]? = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryGT_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryGT_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.gt := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.TreeMap.getKey!_eq_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_eq_of_mem.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, k ∈ t → t.getKey! k = k := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_eq_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_eq_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst : Inhabited α] {k : α}, t.getKey! k = k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeMap.size_alter_eq_self_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.size_alter_eq_self_of_mem.h7.inst : Not
      (@Eq Nat
        (@Std.TreeMap.size Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeMap.alter Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (a : Option Nat) =>
            @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Std.TreeMap.size Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeMap.size_alter_eq_self_of_mem.h7.prem0 : @Eq Bool
      (@Option.isSome Nat
        ((fun (a : Option Nat) => @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@GetElem?.getElem? (Std.TreeMap Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat Nat
            (fun (m : Std.TreeMap Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (a : Nat) =>
              @Membership.mem Nat (Std.TreeMap Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Std.TreeMap.instMembership Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) m a)
            (@Std.TreeMap.instGetElem?Mem Nat Nat fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeMap.size_alter_eq_self_of_mem.h7 : Not
      (∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : @Std.TransCmp α cmp] {k : α}
        {f : Option β → Option β},
        @Eq Bool
            (@Option.isSome β
              (f
                (@GetElem?.getElem? (Std.TreeMap α β cmp) α β
                  (fun (m : Std.TreeMap α β cmp) (a : α) =>
                    @Membership.mem α (Std.TreeMap α β cmp) (@Std.TreeMap.instMembership α β cmp) m a)
                  (@Std.TreeMap.instGetElem?Mem α β cmp) t k)))
            Bool.true →
          @Eq Nat (@Std.TreeMap.size α β cmp (@Std.TreeMap.alter α β cmp t k f)) (@Std.TreeMap.size α β cmp t)) := fun hc_h => HypCheckProof.Std.TreeMap.size_alter_eq_self_of_mem.h7.inst (@hc_h (Nat) (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.TreeMap.ofList Nat Nat (@List.nil (Prod Nat Nat)) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a : Option Nat) => @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Std.TreeMap.size_alter_eq_self_of_mem.h7.prem0)

-- Std.TreeMap.size_alter_eq_self_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_alter_eq_self_of_mem.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option β → Option β}, k ∈ t → (t.alter k f).size = t.size := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (fun (a : Option Nat) => Option.none) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.minKey!_eq_iff_mem_and_forall, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey!_eq_iff_mem_and_forall.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst : Inhabited α] {km : α},
        t.minKey! = km ↔ km ∈ t ∧ ∀ (k : α), k ∈ t → (cmp km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instInhabitedNat) (0)) (by
  simp +ground +decide [Std.TreeMap.minKey!, Std.TreeMap.instMembership, Std.DTreeMap.minKey!, Std.TreeMap.inner,
    Std.TreeMap.contains, Std.DTreeMap.Internal.Impl.minKey!, Std.DTreeMap.inner, Std.DTreeMap.contains,
    Std.DTreeMap.Internal.Impl.contains])

-- Std.TreeSet.Equiv.inter_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.inter_congr.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ t₄ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp],
        t₂.Equiv t₄ → (t₁ ∩ t₂).Equiv (t₃ ∩ t₄) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.inter_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.inter_congr.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ t₄ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp],
        t₁.Equiv t₃ → (t₁ ∩ t₂).Equiv (t₃ ∩ t₄) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get!_ofList_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_contains_eq_false.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] [inst_1 : Inhabited α] {l : List α}
        {k : α}, l.contains k = Bool.false → (Std.TreeSet.ofList l cmp).get! k = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) (instInhabitedBool) ([Bool.true]) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get!_ofList_of_contains_eq_false, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_ofList_of_contains_eq_false.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        [inst : Inhabited α] {l : List α} {k : α}, (Std.TreeSet.ofList l cmp).get! k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (instBEqOfDecidableEq) _ (instInhabitedNat) ([1]) (1)) (by
  decide +kernel)

-- Std.TreeSet.max?_le_max?_insert, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max?_le_max?_insert.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k km kmi : α},
        (t.insert k).max?.get Std.TreeSet.isSome_max?_insert = kmi → (cmp km kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (0) (by
  grind)) (by
  decide +kernel)

-- Std.TreeSet.max?_le_max?_insert, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max?_le_max?_insert.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {km kmi : α},
        t.max? = Option.some km → (cmp km kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (0) (by
  grind)) (by
  decide +kernel)

-- Std.TreeSet.min?_insert_le_min?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min?_insert_le_min?.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k km kmi : α},
        (t.insert k).min?.get Std.TreeSet.isSome_min?_insert = kmi → (cmp kmi km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (1) (0) (1) (by
  grind)) (by
  decide +kernel)

-- Std.TreeSet.min?_insert_le_min?, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min?_insert_le_min?.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {km kmi : α},
        t.min? = Option.some km → (cmp kmi km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (1) (by
  grind)) (by
  decide +kernel)

-- Std.TreeSet.min?_le_min?_erase, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min?_le_min?_erase.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {km : α} {kme : α},
        (t.erase k).min? = Option.some kme := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0)) (by
  simp)

-- Std.DTreeMap.Const.size_alter_eq_sub_one, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_sub_one.h7.inst : Not
      (@Eq Nat
        (@Std.DTreeMap.size Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.Const.alter Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
              (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
                (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) fun (a : Option Nat) => @Option.none Nat))
        (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
          (@Std.DTreeMap.size Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
              (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
                (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_sub_one.h7.prem0 : @Eq Bool
      (@Option.isNone Nat
        ((fun (a : Option Nat) => @Option.none Nat)
          (@Std.DTreeMap.Const.get? Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
              (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
                (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_sub_one.h7 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : @Std.TransCmp α cmp] {k : α} {f : Option β → Option β},
        @Eq Bool (@Option.isNone β (f (@Std.DTreeMap.Const.get? α cmp β t k))) Bool.true →
          @Eq Nat (@Std.DTreeMap.size α (fun (x : α) => β) cmp (@Std.DTreeMap.Const.alter α cmp β t k f))
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@Std.DTreeMap.size α (fun (x : α) => β) cmp t)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => HypCheckProof.Std.DTreeMap.Const.size_alter_eq_sub_one.h7.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
      (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
        (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
      fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (fun (a : Option Nat) => @Option.none Nat) HypCheckProof.Std.DTreeMap.Const.size_alter_eq_sub_one.h7.prem0)

-- Std.DTreeMap.Const.size_alter_eq_sub_one, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_sub_one.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k : α} {f : Option β → Option β}, k ∈ t → (Std.DTreeMap.Const.alter t k f).size = t.size - 1 := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (fun (a : Option Nat) => Option.some 0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constGetEntryGE_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGE_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α}, t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isGE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.constGetEntryGE_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGE_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {h' : ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isGE = Bool.true}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  simp)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_congr.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k₁ k₂ : α},
        cmp k₁ k₂ = Ordering.eq → k₁ ∈ t → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_congr.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k₁ k₂ : α},
        k₁ ∈ t → cmp k₁ k₂ = Ordering.eq := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_congr, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.getKey_congr.h8.inst : Not
      (@Membership.mem Nat (Std.DTreeMap Nat (fun (a : Nat) => Nat) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.DTreeMap.instMembership Nat (fun (a : Nat) => Nat) fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
        (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
          @Ord.compare Nat instOrdNat a b)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.getKey_congr.h8.prem0 : @Eq Ordering
      ((fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Ordering.eq := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.getKey_congr.h8 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.TransCmp α cmp]
        {k₁ k₂ : α},
        @Eq Ordering (cmp k₁ k₂) Ordering.eq →
          @Membership.mem α (Std.DTreeMap α β cmp) (@Std.DTreeMap.instMembership α β cmp) t k₁) := fun hc_h => HypCheckProof.Std.DTreeMap.getKey_congr.h8.inst (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.DTreeMap.getKey_congr.h8.prem0)

-- Std.DTreeMap.get_eq_get!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_eq_get!.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        [inst : Inhabited (β a)] {h : a ∈ t}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (by
  decide)) (by
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

-- Std.DTreeMap.get_eq_get!, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_eq_get!.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {a : α} [inst : Inhabited (β a)], a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (instInhabitedNat)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_ofList_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_ofList_of_contains_eq_false.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List (α × β)} {k : α},
        (List.map Prod.fst l).contains k = Bool.false →
          Std.DTreeMap.Const.get? (Std.DTreeMap.Const.ofList l cmp) k = Option.none := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([(Bool.false, 0)]) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_ofList_of_contains_eq_false, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_ofList_of_contains_eq_false.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List (α × β)} {k : α}, Std.DTreeMap.Const.get? (Std.DTreeMap.Const.ofList l cmp) k = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) _ (instBEqOfDecidableEq) _ ([(0, 0)]) (0)) (by
  decide +kernel)

-- Std.DTreeMap.le_maxKey?_of_contains, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.le_maxKey?_of_contains.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {km : α},
        t.contains k = Bool.true → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.le_maxKey?_of_contains, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.le_maxKey?_of_contains.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {km : α}, t.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.le_maxKey?_of_contains, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.le_maxKey?_of_contains.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k km : α},
        t.contains k = Bool.true → (cmp k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (1) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.get_erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_erase.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {k a : α}
        {h' : a ∈ t.erase k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (1) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_erase, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_erase.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k a : α}, a ∈ t.erase k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.get?_diff_of_not_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_diff_of_not_mem_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α}, ¬k ∈ t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide)) (by
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

-- Std.DTreeMap.get?_diff_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_diff_of_not_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, (t₁ \ t₂).get? k = t₁.get? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.get?_inter_of_not_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_inter_of_not_mem_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α}, ¬k ∈ t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide)) (by
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

-- Std.DTreeMap.get?_inter_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_inter_of_not_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, (t₁ ∩ t₂).get? k = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getEntryGT_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryGT_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.gt := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.getEntryGT_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryGT_eq.h8.inst : ¬(Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b).Equiv
        (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryGT_eq.h8.prem0 : ∃ (a : Bool),
      (a ∈ Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) ∧
        (fun (a b : Bool) => Ord.compare a b) a Bool.false = Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryGT_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.gt}, t₁.Equiv t₂ := fun hc_h => HypCheckProof.Std.DTreeMap.Equiv.getEntryGT_eq.h8.inst (@hc_h (Bool) (fun (a : Bool) => Nat) (fun (a b : Bool) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) _ (Bool.false) HypCheckProof.Std.DTreeMap.Equiv.getEntryGT_eq.h8.prem0)

-- Std.DTreeMap.Equiv.keyAtIdx_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.keyAtIdx_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {i : Nat}, t₁.Equiv t₂ → i < t₁.size := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.keyAtIdx_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.keyAtIdx_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {i : Nat}
        {h' : i < t₁.size}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.size_alter_eq_self_of_not_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_not_mem.h7.inst : Not
      (@Eq Nat
        (@Std.DTreeMap.size Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.Const.alter Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
              (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
                (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (a : Option Nat) => @Option.none Nat))
        (@Std.DTreeMap.size Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
            (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
              (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
            fun (a b : Nat) => @Ord.compare Nat instOrdNat a b))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_not_mem.h7.prem0 : @Eq Bool
      (@Option.isNone Nat
        ((fun (a : Option Nat) => @Option.none Nat)
          (@Std.DTreeMap.Const.get? Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
              (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
                (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_not_mem.h7 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : @Std.TransCmp α cmp] {k : α} {f : Option β → Option β},
        @Eq Bool (@Option.isNone β (f (@Std.DTreeMap.Const.get? α cmp β t k))) Bool.true →
          @Eq Nat (@Std.DTreeMap.size α (fun (x : α) => β) cmp (@Std.DTreeMap.Const.alter α cmp β t k f))
            (@Std.DTreeMap.size α (fun (x : α) => β) cmp t)) := fun hc_h => HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_not_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
      (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
        (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
      fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a : Option Nat) => @Option.none Nat) HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_not_mem.h7.prem0)

-- Std.DTreeMap.Const.size_alter_eq_self_of_not_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_not_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k : α} {f : Option β → Option β}, ¬k ∈ t → (Std.DTreeMap.Const.alter t k f).size = t.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (fun (a : Option Nat) => Option.some 0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_eq_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_eq_of_mem.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α}, k ∈ t → t.getKey! k = k := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_eq_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_eq_of_mem.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst : Inhabited α] {k : α}, t.getKey! k = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.DTreeMap.mem_of_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_get_eq.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k} {w : k ∈ t},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare (a / 2) (b / 2)) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_compare (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.mem_of_get_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_get_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {k : α}
        {v : β k}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyLT_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyLT_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.lt := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.getKeyLT_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyLT_eq.h8.inst : ¬(Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b).Equiv
        (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyLT_eq.h8.prem0 : ∃ (a : Bool),
      (a ∈ Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) ∧
        (fun (a b : Bool) => Ord.compare a b) a Bool.true = Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyLT_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.lt}, t₁.Equiv t₂ := fun hc_h => HypCheckProof.Std.DTreeMap.Equiv.getKeyLT_eq.h8.inst (@hc_h (Bool) (fun (a : Bool) => Nat) (fun (a b : Bool) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) _ (Bool.true) HypCheckProof.Std.DTreeMap.Equiv.getKeyLT_eq.h8.prem0)

-- Std.DTreeMap.Equiv.getEntryLT_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryLT_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.lt := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.getEntryLT_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryLT_eq.h8.inst : ¬(Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b).Equiv
        (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryLT_eq.h8.prem0 : ∃ (a : Bool),
      (a ∈ Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) ∧
        (fun (a b : Bool) => Ord.compare a b) a Bool.true = Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryLT_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.lt}, t₁.Equiv t₂ := fun hc_h => HypCheckProof.Std.DTreeMap.Equiv.getEntryLT_eq.h8.inst (@hc_h (Bool) (fun (a : Bool) => Nat) (fun (a b : Bool) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) _ (Bool.true) HypCheckProof.Std.DTreeMap.Equiv.getEntryLT_eq.h8.prem0)

-- Std.DTreeMap.Const.maxKey_modify_eq_maxKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.maxKey_modify_eq_maxKey.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.LawfulEqCmp cmp] {k : α} {f : β → β} {he : (Std.DTreeMap.Const.modify t k f).isEmpty = Bool.false},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.maxKey_modify_eq_maxKey, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.maxKey_modify_eq_maxKey.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α} {f : β → β}, (Std.DTreeMap.Const.modify t k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.DTreeMap.get_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_inter.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        {k : α} {h_mem : k ∈ t₁ ∩ t₂}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (by
  decide +kernel)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_inter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_inter.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h_mem : k ∈ t₁ ∩ t₂}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide +kernel)) (by
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

-- Std.DTreeMap.get_inter, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_inter.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, k ∈ t₁ ∩ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getEntryGE_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryGE_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isGE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.getEntryGE_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryGE_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isGE = Bool.true}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  simp)) (by
  decide +kernel)

-- Std.DTreeMap.get?_eq_some_get!_of_contains, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_eq_some_get!_of_contains.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        [inst : Inhabited (β a)], t.contains a = Bool.true → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (by
  decide)) (by
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

-- Std.DTreeMap.get?_eq_some_get!_of_contains, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_eq_some_get!_of_contains.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {a : α} [inst_1 : Inhabited (β a)], t.get? a = Option.some (t.get! a) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (instInhabitedNat)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKey_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKey_eq.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} {k : α} {hk : k ∈ t₁},
        t₁.Equiv t₂ → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide) (by
  rfl)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Equiv.getKey_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKey_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKey_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKey_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {hk : k ∈ t₁}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_union_of_not_mem_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_union_of_not_mem_left.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α},
        ¬k ∈ t₁ → ∀ {h' : k ∈ t₁ ∪ t₂}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_union_of_not_mem_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_union_of_not_mem_left.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {h' : k ∈ t₁ ∪ t₂}, ¬k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_union_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_union_of_not_mem_left.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α}, ¬k ∈ t₁ → k ∈ t₁ ∪ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constGetEntryLE_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryLE_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α}, t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.constGetEntryLE_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryLE_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {h' : ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  simp)) (by
  decide +kernel)

-- Std.DTreeMap.get_eq_getD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_eq_getD.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        {fallback : β a} {h : a ∈ t}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0) (by
  decide)) (by
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

-- Std.DTreeMap.get_eq_getD, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_eq_getD.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {a : α} {fallback : β a}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKeyD_eq_iff_mem_and_forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKeyD_eq_iff_mem_and_forall.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {km fallback : α},
        t.maxKeyD fallback = km ↔ km ∈ t ∧ ∀ (k : α), k ∈ t → (cmp k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (0)) (by
  simp +ground +decide [Std.DTreeMap.maxKeyD, Std.DTreeMap.instMembership, Std.DTreeMap.Internal.Impl.maxKeyD,
    Std.DTreeMap.inner, Std.DTreeMap.contains, Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.Internal.Impl.brecOn])

-- Std.DTreeMap.get_union_of_mem_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_union_of_mem_right.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.LawfulEqCmp cmp] {k : α}, k ∈ t₂ → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_union_of_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_union_of_mem_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α}, k ∈ t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide)) (by
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

-- Std.DTreeMap.get_union_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_union_of_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp] {k : α}, k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.size_alter_eq_self_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_mem.h7.inst : Not
      (@Eq Nat
        (@Std.DTreeMap.size Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.Const.alter Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (a : Option Nat) =>
            @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Std.DTreeMap.size Nat (fun (x : Nat) => Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
            @Ord.compare Nat instOrdNat a b))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_mem.h7.prem0 : @Eq Bool
      (@Option.isSome Nat
        ((fun (a : Option Nat) => @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Std.DTreeMap.Const.get? Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
            (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat))
              fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_mem.h7 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : @Std.TransCmp α cmp] {k : α} {f : Option β → Option β},
        @Eq Bool (@Option.isSome β (f (@Std.DTreeMap.Const.get? α cmp β t k))) Bool.true →
          @Eq Nat (@Std.DTreeMap.size α (fun (x : α) => β) cmp (@Std.DTreeMap.Const.alter α cmp β t k f))
            (@Std.DTreeMap.size α (fun (x : α) => β) cmp t)) := fun hc_h => HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_mem.h7.inst (@hc_h (Nat) (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) (Nat) (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) fun (a b : Nat) =>
      @Ord.compare Nat instOrdNat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a : Option Nat) => @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_mem.h7.prem0)

-- Std.DTreeMap.Const.size_alter_eq_self_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.size_alter_eq_self_of_mem.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k : α} {f : Option β → Option β}, k ∈ t → (Std.DTreeMap.Const.alter t k f).size = t.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (fun (a : Option Nat) => Option.none) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyGT_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyGT_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.gt := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.getKeyGT_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyGT_eq.h8.inst : ¬(Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b).Equiv
        (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyGT_eq.h8.prem0 : ∃ (a : Bool),
      (a ∈ Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) ∧
        (fun (a b : Bool) => Ord.compare a b) a Bool.false = Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyGT_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.gt}, t₁.Equiv t₂ := fun hc_h => HypCheckProof.Std.DTreeMap.Equiv.getKeyGT_eq.h8.inst (@hc_h (Bool) (fun (a : Bool) => Nat) (fun (a b : Bool) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) _ (Bool.false) HypCheckProof.Std.DTreeMap.Equiv.getKeyGT_eq.h8.prem0)

-- Std.DTreeMap.get_diff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_diff.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp]
        {k : α} {h_mem : k ∈ t₁ \ t₂}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_diff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_diff.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h_mem : k ∈ t₁ \ t₂}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide)) (by
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

-- Std.DTreeMap.get_diff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_diff.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, k ∈ t₁ \ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyLE_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyLE_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.getKeyLE_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyLE_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  simp)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_eq_of_contains, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_eq_of_contains.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α}, t.contains k = Bool.true → t.getKey! k = k := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_eq_of_contains, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_eq_of_contains.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] [inst : Inhabited α] {k : α}, t.getKey! k = k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getEntryLE_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryLE_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.getEntryLE_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryLE_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  simp)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constGetEntryGT_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGT_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α}, t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.gt := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.DTreeMap.Equiv.constGetEntryGT_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGT_eq.h8.inst : ¬(Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b).Equiv
        (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGT_eq.h8.prem0 : ∃ (a : Bool),
      (a ∈ Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) ∧
        (fun (a b : Bool) => Ord.compare a b) a Bool.false = Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGT_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {h' : ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.gt}, t₁.Equiv t₂ := fun hc_h => HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGT_eq.h8.inst (@hc_h (Bool) (fun (a b : Bool) => Ord.compare a b) (Nat) (Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (a b : Bool) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Bool) => Ord.compare a b) _ (Bool.false) HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGT_eq.h8.prem0)

-- Std.DTreeMap.Equiv.constGet_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGet_eq.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {hk : k ∈ t₁},
        t₁.Equiv t₂ → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide) (by
  rfl)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Equiv.constGet_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGet_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α}, t₁.Equiv t₂ → k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constGet_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGet_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {hk : k ∈ t₁}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.entryAtIdx_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.entryAtIdx_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {i : Nat}, t₁.Equiv t₂ → i < t₁.size := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.entryAtIdx_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.entryAtIdx_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {i : Nat}
        {h' : i < t₁.size}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.get!_eq_default, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_eq_default.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        [inst : Inhabited (β a)], ¬a ∈ t → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (by
  decide)) (by
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

-- Std.DTreeMap.Const.getKeyD_unitOfList_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_unitOfList_of_contains_eq_false.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List α} {k fallback : α},
        l.contains k = Bool.false → (Std.DTreeMap.Const.unitOfList l cmp).getKeyD k fallback = fallback := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([Bool.true]) (Bool.false) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKeyD_unitOfList_of_contains_eq_false, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_unitOfList_of_contains_eq_false.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List α} {k fallback : α}, (Std.DTreeMap.Const.unitOfList l cmp).getKeyD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (instBEqOfDecidableEq) _ ([0]) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.get?_inter_of_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_inter_of_mem_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α}, k ∈ t₂ → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide)) (by
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

-- Std.DTreeMap.get?_inter_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_inter_of_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, (t₁ ∩ t₂).get? k = t₁.get? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getD_eq_fallback, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_eq_fallback.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        {fallback : β a}, ¬a ∈ t → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0) (by
  decide)) (by
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

-- Std.DTreeMap.getD_eq_fallback, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_eq_fallback.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {a : α} {fallback : β a}, t.getD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.mem_of_mem_union_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_union_of_not_mem_right.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        ¬k ∈ t₂ → k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.mem_of_mem_union_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_union_of_not_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t₁ ∪ t₂ → k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constEntryAtIdx_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constEntryAtIdx_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {i : Nat}, t₁.Equiv t₂ → i < t₁.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constEntryAtIdx_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constEntryAtIdx_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {i : Nat} {h' : i < t₁.size}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.get!_of_isEmpty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_of_isEmpty.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        [inst : Inhabited (β a)], t.isEmpty = Bool.true → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (by
  decide)) (by
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

-- Std.TreeMap.getElem!_filterMap_of_getKey?_eq_some, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem!_filterMap_of_getKey?_eq_some.h10 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited γ]
        {f : α → β → Option γ} {k k' : α}, (Std.TreeMap.filterMap f t)[k]! = (t[k]?.bind (f k')).get! := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (fun (a : Nat) => if a = 0 then fun (x : Nat) => Option.none else Option.some) (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.foldr_eq, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.foldr_eq.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} {δ : Type} [inst : Std.TransCmp cmp]
        {f : α → β → δ → δ} {init : δ}, Std.TreeMap.foldr f init t₁ = Std.TreeMap.foldr f init t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Nat) _ (fun (a a_1 b : Nat) => a_1 - b) (1)) (by
  decide +kernel)

-- Std.TreeMap.getKey_insertManyIfNewUnit_list_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_insertManyIfNewUnit_list_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] {l : List α} {k : α}
        {h' : k ∈ t.insertManyIfNewUnit l}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey_alter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_alter.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Inhabited α] {k k' : α}
        {f : Option β → Option β} {hc : k' ∈ t.alter k f}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (0) (0) (fun (a : Option Nat) => Option.some 0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_alter, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_alter.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k k' : α} {f : Option β → Option β}, k' ∈ t.alter k f := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0) (0) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.maxEntry_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.maxEntry_eq.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.Equiv t₂ → t₁.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.maxEntry_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.maxEntry_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        {he : t₁.isEmpty = Bool.false}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getElem!_filter_of_getKey?_eq_some, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem!_filter_of_getKey?_eq_some.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited β]
        {f : α → β → Bool} {k k' : α}, (Std.TreeMap.filter f t)[k]! = (Option.filter (f k') t[k]?).get! := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (fun a b => a < b : Nat → Nat → Bool) (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.of_forall_constGet?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.of_forall_constGet?_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp], t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ _) (by
  decide +kernel)

-- Std.TreeMap.getKey?_unitOfList_of_contains_eq_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_contains_eq_false.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List α} {k : α},
        l.contains k = Bool.false → (Std.TreeMap.unitOfList l cmp).getKey? k = Option.none := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instBEqOfDecidableEq) ([Bool.false]) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_unitOfList_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_unitOfList_of_contains_eq_false.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] [inst : Std.LawfulBEqCmp cmp]
        {l : List α} {k : α}, (Std.TreeMap.unitOfList l cmp).getKey? k = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (instBEqOfDecidableEq) _ ([0]) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey_minKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_minKey?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {km : α} {hc : t.contains km = Bool.true},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_minKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_minKey?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey_minKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_minKey?.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α}
        {hc : t.contains km = Bool.true}, t.getKey km hc = km := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) hc_k0) (by
  decide +kernel)

-- Std.TreeMap.getKey_maxKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_maxKey?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {km : α} {hc : t.contains km = Bool.true},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_maxKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_maxKey?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey_maxKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_maxKey?.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α}
        {hc : t.contains km = Bool.true}, t.getKey km hc = km := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) hc_k0) (by
  decide +kernel)

-- Std.TreeMap.getKey?_eq_some_of_contains, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_eq_some_of_contains.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t.contains k = Bool.true → t.getKey? k = Option.some k := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_eq_some_of_contains, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_eq_some_of_contains.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, t.getKey? k = Option.some k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.of_forall_getKey_eq_of_forall_constGet?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.of_forall_getKey_eq_of_forall_constGet?_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        (∀ (k : α) (hk : k ∈ t₁) (hk' : k ∈ t₂), t₁.getKey k hk = t₂.getKey k hk') → t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (by
  simp)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_eq_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_eq_some.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t → t.getKey? k = Option.some k := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_eq_some, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_eq_some.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, t.getKey? k = Option.some k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.TreeMap.maxKey_eq_iff_mem_and_forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_eq_iff_mem_and_forall.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {km : α}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.get_eq.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} {k : α} {hk : k ∈ t₁}, t₁.Equiv t₂ → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide) (by
  rfl)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.Equiv.get_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.get_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.get_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.get_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {hk : k ∈ t₁},
        t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.max!_eq_iff_mem_and_forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max!_eq_iff_mem_and_forall.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        [inst : Inhabited α] {km : α}, t.max! = km ↔ km ∈ t ∧ ∀ (k : α), k ∈ t → (cmp k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (instInhabitedNat) (0)) (by
  simp +ground +decide [Std.TreeSet.max!, Std.TreeSet.instMembership, Std.TreeMap.maxKey!, Std.TreeSet.inner,
    Std.TreeSet.contains, Std.DTreeMap.maxKey!, Std.TreeMap.inner, Std.TreeMap.contains,
    Std.DTreeMap.Internal.Impl.maxKey!, Std.DTreeMap.inner, Std.DTreeMap.contains])

-- Std.TreeSet.mem_of_mem_union_of_not_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_union_of_not_mem_right.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, ¬k ∈ t₂ → k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.mem_of_mem_union_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_union_of_not_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t₁ ∪ t₂ → k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.getLE_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.getLE_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.TreeSet.Equiv.getLE_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.getLE_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ (cmp a k).isLE = Bool.true}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  simp)) (by
  decide +kernel)

-- Std.TreeSet.maxD_eq_iff_mem_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.maxD_eq_iff_mem_and_forall.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {km fallback : α}, t.maxD fallback = km ↔ km ∈ t ∧ ∀ (k : α), k ∈ t → (cmp k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (0)) (by
  simp +ground +decide [Std.TreeSet.maxD, Std.TreeSet.instMembership, Std.TreeMap.maxKeyD, Std.TreeSet.inner,
    Std.TreeSet.contains, Std.DTreeMap.maxKeyD, Std.TreeMap.inner, Std.TreeMap.contains,
    Std.DTreeMap.Internal.Impl.maxKeyD, Std.DTreeMap.inner, Std.DTreeMap.contains])

-- Std.TreeSet.get_union_of_not_mem_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_union_of_not_mem_left.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} {k : α},
        ¬k ∈ t₁ → ∀ {h' : k ∈ t₁ ∪ t₂}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.get_union_of_not_mem_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_union_of_not_mem_left.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {h' : k ∈ t₁ ∪ t₂},
        ¬k ∈ t₁ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get_union_of_not_mem_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_union_of_not_mem_left.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        ¬k ∈ t₁ → k ∈ t₁ ∪ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.mem_of_mem_insert', hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_insert'.h6.inst : ¬1 ∈ Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_insert'.h6.prem0 : ¬((fun (a b : Nat) => Ord.compare a b) 0 1 = Ordering.eq ∧
        ¬0 ∈ Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeSet.mem_of_mem_insert'.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k a : α},
        ¬(cmp k a = Ordering.eq ∧ ¬k ∈ t) → a ∈ t := fun hc_h => HypCheckProof.Std.TreeSet.mem_of_mem_insert'.h6.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1) HypCheckProof.Std.TreeSet.mem_of_mem_insert'.h6.prem0)

-- Std.TreeSet.mem_of_mem_insert', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_insert'.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k a : α},
        a ∈ t.insert k → a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.getLT_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.getLT_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.Equiv t₂ → ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.lt := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  simp)

-- Std.TreeSet.Equiv.getLT_eq, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.Equiv.getLT_eq.h7.inst : ¬(Std.TreeSet.ofList [Bool.false] fun (a b : Bool) => Ord.compare a b).Equiv
        (Std.TreeSet.ofList [] fun (a b : Bool) => Ord.compare a b) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TreeSet.Equiv.getLT_eq.h7.prem0 : ∃ (a : Bool),
      (a ∈ Std.TreeSet.ofList [Bool.false] fun (a b : Bool) => Ord.compare a b) ∧
        (fun (a b : Bool) => Ord.compare a b) a Bool.true = Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TreeSet.Equiv.getLT_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}
        {h' : ∃ (a : α), a ∈ t₁ ∧ cmp a k = Ordering.lt}, t₁.Equiv t₂ := fun hc_h => HypCheckProof.Std.TreeSet.Equiv.getLT_eq.h7.inst (@hc_h (Bool) (fun (a b : Bool) => Ord.compare a b) (Std.TreeSet.ofList [Bool.false] fun (a b : Bool) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Bool) => Ord.compare a b) _ (Bool.true) HypCheckProof.Std.TreeSet.Equiv.getLT_eq.h7.prem0)

-- Std.TreeSet.min?_le_of_contains, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min?_le_of_contains.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α} {km : α},
        t.contains k = Bool.true → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.min?_le_of_contains, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min?_le_of_contains.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {km : α},
        t.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeSet.min?_le_of_contains, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min?_le_of_contains.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k km : α},
        t.contains k = Bool.true → (cmp km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.getD_eq_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_eq_of_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        k ∈ t → t.getD k fallback = k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.getD_eq_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_eq_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {k fallback : α}, t.getD k fallback = k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.le_max?_of_contains, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.le_max?_of_contains.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α} {km : α},
        t.contains k = Bool.true → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.le_max?_of_contains, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.le_max?_of_contains.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {km : α},
        t.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeSet.le_max?_of_contains, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.le_max?_of_contains.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k km : α},
        t.contains k = Bool.true → (cmp k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (1) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.mem_of_mem_union_of_not_mem_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_union_of_not_mem_left.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, ¬k ∈ t₁ → k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.mem_of_mem_union_of_not_mem_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_union_of_not_mem_left.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t₁ ∪ t₂ → k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.get_get?, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.get_get?.h4.inst : Not (@Std.TransCmp Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.DTreeMap.get_get?.h4.prem0 : @Eq Bool
      (@Option.isSome ((fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Std.DTreeMap.get? Nat (fun (a : Nat) => Nat)
          (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
          (@Std.LawfulEqCmp.mk Nat
            (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
            (@Std.ReflCmp.mk Nat
              (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
              fun {a : Nat} =>
              @of_eq_true
                (@Eq Ordering
                  ((fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) a a)
                  Ordering.eq)
                (@Eq.trans Prop
                  (@Eq Ordering
                    ((fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) a a)
                    Ordering.eq)
                  (@Eq Ordering Ordering.eq Ordering.eq) True
                  (@congrFun' Ordering Prop
                    (@Eq Ordering
                      ((fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) a
                        a))
                    (@Eq Ordering Ordering.eq)
                    (@congrArg Ordering (Ordering → Prop)
                      ((fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) a
                        a)
                      Ordering.eq (@Eq Ordering)
                      (@ite_eq_left_of_eq_true Ordering (@Eq Nat a a) (instDecidableEqNat a a) Ordering.eq Ordering.lt
                        (@eq_self Nat a)))
                    Ordering.eq)
                  (@eq_self Ordering Ordering.eq)))
            fun {a b : Nat}
              (a_1 :
                @Eq Ordering
                  ((fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) a b)
                  Ordering.eq) =>
            @of_eq_true (@Eq Nat a b)
              (@Eq.trans Prop (@Eq Nat a b) (@Eq Nat b b) True
                (@congrFun' Nat Prop (@Eq Nat a) (@Eq Nat b)
                  (@congrArg Nat (Nat → Prop) a b (@Eq Nat)
                    (@id (@Eq Nat a b)
                      (@Eq.mp
                        (@Eq Ordering
                          ((fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
                            a b)
                          Ordering.eq)
                        (@Eq Nat a b)
                        (@Eq.trans Prop
                          (@Eq Ordering (@ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
                            Ordering.eq)
                          (Not (@Eq Nat a b) → @Eq Ordering Ordering.lt Ordering.eq) (@Eq Nat a b)
                          (@ite_eq_left_iff._simp_1 Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
                          (@Eq.trans Prop (Not (@Eq Nat a b) → @Eq Ordering Ordering.lt Ordering.eq)
                            (Not (Not (@Eq Nat a b))) (@Eq Nat a b)
                            (@Eq.trans Prop (Not (@Eq Nat a b) → @Eq Ordering Ordering.lt Ordering.eq)
                              (Not (@Eq Nat a b) → False) (Not (Not (@Eq Nat a b)))
                              (@implies_congr_ctx (Not (@Eq Nat a b)) (Not (@Eq Nat a b))
                                (@Eq Ordering Ordering.lt Ordering.eq) False (@Eq.refl Prop (Not (@Eq Nat a b)))
                                fun (a : Not (@Eq Nat a b)) =>
                                @eq_false' (@Eq Ordering Ordering.lt Ordering.eq)
                                  fun (h : @Eq Ordering Ordering.lt Ordering.eq) =>
                                  @False.elim False
                                    (@noConfusion_of_Nat Ordering Ordering.ctorIdx Ordering.lt Ordering.eq h))
                              (@imp_false._simp_1 (Not (@Eq Nat a b))))
                            (@Decidable.not_not._simp_1 (@Eq Nat a b) (instDecidableEqNat a b))))
                        a_1)))
                  b)
                (@eq_self Nat b)))
          (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat)
            (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
              (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
            fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.DTreeMap.get_get?.h4 : Not
      (∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : @Std.LawfulEqCmp α cmp]
        {a : α} {h : @Eq Bool (@Option.isSome (β a) (@Std.DTreeMap.get? α β cmp inst t a)) Bool.true}, @Std.TransCmp α cmp) := fun hc_h => HypCheckProof.Std.DTreeMap.get_get?.h4.inst (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.DTreeMap.ofList Nat (fun (a : Nat) => Nat)
      (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
        (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
      fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Std.DTreeMap.get_get?.h4.prem0)

-- Std.DTreeMap.get_get?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_get?.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.DTreeMap.get_get?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_get?.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {a : α}, (t.get? a).isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.get?_eq_some_get, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_eq_some_get.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        a ∈ t → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide)) (by
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

-- Std.DTreeMap.get?_eq_some_get, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_eq_some_get.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_filterMap', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_filterMap'.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.LawfulEqCmp cmp] [inst : Inhabited γ] {f : α → β → Option γ} {k : α},
        Std.DTreeMap.Const.get! (Std.DTreeMap.filterMap f t) k = ((Std.DTreeMap.Const.get? t k).bind (f k)).get! := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Bool) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (instInhabitedBool) (fun (a n : Nat) => Option.some (n % 2 == 0)) (0)) (by
  decide +kernel)

-- Std.DTreeMap.get?_eq_none_of_contains_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_eq_none_of_contains_eq_false.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        t.contains a = Bool.false → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide)) (by
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

-- Std.DTreeMap.get?_eq_none_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_eq_none_of_contains_eq_false.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {a : α}, t.get? a = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_eq_some_of_contains, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_eq_some_of_contains.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t.contains k = Bool.true → t.getKey? k = Option.some k := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_eq_some_of_contains, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_eq_some_of_contains.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {k : α}, t.getKey? k = Option.some k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey_alter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey_alter.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Inhabited α]
        {k k' : α} {f : Option β → Option β} {hc : k' ∈ Std.DTreeMap.Const.alter t k f}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (0) (0) (fun (a : Option Nat) => Option.some 0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.getKey_alter, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey_alter.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k k' : α} {f : Option β → Option β}, k' ∈ Std.DTreeMap.Const.alter t k f := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0) (0) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.minEntry_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.minEntry_eq.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.Equiv t₂ → t₁.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.minEntry_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.minEntry_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {he : t₁.isEmpty = Bool.false}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getD_insertIfNew, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_insertIfNew.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α}
        {fallback : β a} {v : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (0) (0)) (by
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

-- Std.DTreeMap.Const.getKey_insertManyIfNewUnit_list_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey_insertManyIfNewUnit_list_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        {l : List α} {k : α} {h' : k ∈ Std.DTreeMap.Const.insertManyIfNewUnit t l}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_minKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_minKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {km : α}
        {hc : t.contains km = Bool.true}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey_minKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_minKey?.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_minKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_minKey?.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α}
        {hc : t.contains km = Bool.true}, t.getKey km hc = km := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) hc_k0) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_map, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_map.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst : Inhabited γ] {f : α → β → γ} {k : α},
        Std.DTreeMap.Const.get! (Std.DTreeMap.map f t) k = (Option.map (f k) (Std.DTreeMap.Const.get? t k)).get! := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Bool) (Bool) (Std.DTreeMap.ofList [(⟨Bool.false, Bool.false⟩ : (_ : Bool) × Bool)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (fun a b => !a || b : Bool → Bool → Bool) (Bool.true)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_maxKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_maxKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {km : α}
        {hc : t.contains km = Bool.true}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey_maxKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_maxKey?.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_maxKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_maxKey?.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α}
        {hc : t.contains km = Bool.true}, t.getKey km hc = km := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) hc_k0) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_eq_get, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_eq_get.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α} {h : a ∈ t}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (by
  decide)) (by
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

-- Std.DTreeMap.Const.get_eq_get, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_eq_get.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp] {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constMinEntry_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constMinEntry_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp], t₁.Equiv t₂ → t₁.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constMinEntry_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constMinEntry_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {he : t₁.isEmpty = Bool.false}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.of_forall_constGet?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.of_forall_constGet?_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp], t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.of_forall_get?_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.of_forall_get?_eq.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide))) (by
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

-- Std.DTreeMap.Equiv.of_forall_get?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.of_forall_get?_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp], t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ _) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_map_of_getKey?_eq_some, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_map_of_getKey?_eq_some.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {f : α → β → γ} {k k' : α},
        Std.DTreeMap.Const.get? (Std.DTreeMap.map f t) k = Option.map (f k') (Std.DTreeMap.Const.get? t k) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (fun a b => a - b : Nat → Nat → Nat) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.get!_insertIfNew, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_insertIfNew.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α}
        [inst : Inhabited (β a)] {v : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (instInhabitedNat) (0)) (by
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

-- Std.DTreeMap.get!_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k k' : α}
        [hi : Inhabited (β k')] {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (instInhabitedNat) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.Equiv.maxKey_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.maxKey_eq.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.Equiv t₂ → t₁.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.maxKey_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.maxKey_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {h' : t₁.isEmpty = Bool.false}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {k' fallback : α} {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.Const.get?_filterMap_of_getKey?_eq_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_filterMap_of_getKey?_eq_some.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Option γ}
        {k k' : α},
        t.getKey? k = Option.some k' →
          Std.DTreeMap.Const.get? (Std.DTreeMap.filterMap f t) k = (Std.DTreeMap.Const.get? t k).bind (f k') := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (fun (a : Nat) => Option.some) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_filterMap_of_getKey?_eq_some, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_filterMap_of_getKey?_eq_some.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {f : α → β → Option γ} {k k' : α},
        Std.DTreeMap.Const.get? (Std.DTreeMap.filterMap f t) k = (Std.DTreeMap.Const.get? t k).bind (f k') := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (fun (a : Nat) => if a = 0 then fun (x : Nat) => Option.none else Option.some) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getD_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k k' : α}
        {fallback : β k'} {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (0) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.Equiv.of_forall_getKey_eq_of_forall_constGet?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.of_forall_getKey_eq_of_forall_constGet?_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp], (∀ (k : α) (hk : k ∈ t₁) (hk' : k ∈ t₂), t₁.getKey k hk = t₂.getKey k hk') → t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (by
  simp)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryGTD_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryGTD_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {fallback : α × β}, t₁.getEntryGTD k fallback = t₂.getEntryGTD k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) ((0, 0))) (by
  decide +kernel)

-- Std.DTreeMap.getD_alter_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_alter_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {fallback : β k} {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.Const.mem_insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_insertMany_list.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List (α × β)} {k : α},
        k ∈ Std.DTreeMap.Const.insertMany t l ↔ k ∈ t ∨ (List.map Prod.fst l).contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(0, 0)]) (1)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_inter_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_inter_of_mem_right.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        (t₁ ∩ t₂).getKeyD k fallback = t₁.getKeyD k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_filterMap.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Option γ} {k : α}
        {h : k ∈ Std.TreeMap.filterMap f t}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun (a : Nat) => Option.some) (0) (by
  decide +kernel)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_filterMap, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_filterMap.h8 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → Option γ}
        {k : α}, k ∈ Std.TreeMap.filterMap f t := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (fun (a x : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.contains_alter_of_not_compare_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.contains_alter_of_not_compare_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k k' : α} {f : Option β → Option β}, (Std.DTreeMap.Const.alter t k f).contains k' = t.contains k' := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.DTreeMap.contains_insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_insertMany_list.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List ((a : α) × β a)} {k : α},
        (t.insertMany l).contains k = (t.contains k || (List.map Sigma.fst l).contains k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getKeyGED_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyGED_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        t₁.getKeyGED k fallback = t₂.getKeyGED k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem!_union_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem!_union_of_not_mem_right.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        [inst : Inhabited β], (t₁ ∪ t₂)[k]! = t₁[k]! := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) _ (0) (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_congr.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k k' : α}, t.getKey! k = t.getKey! k' := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constGetEntryLE!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryLE!_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst : Inhabited (α × β)] {k : α},
        Std.DTreeMap.Const.getEntryLE! t₁ k = Std.DTreeMap.Const.getEntryLE! t₂ k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedProd) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_diff_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_diff_of_not_mem_left.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Inhabited α]
        [inst_1 : Std.TransCmp cmp] {k : α}, (t₁ \ t₂).getKey! k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (instInhabitedNat) _ (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem_alter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_alter.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k k' : α} {f : Option β → Option β}
        {hc : k' ∈ t.alter k f}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (fun (a : Option Nat) => Option.some 0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_alter, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_alter.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k k' : α}
        {f : Option β → Option β}, k' ∈ t.alter k f := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_union_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_union_of_not_mem_right.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        (t₁ ∪ t₂).getKeyD k fallback = t₁.getKeyD k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_diff_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_diff_of_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Inhabited α]
        [inst_1 : Std.TransCmp cmp] {k : α}, (t₁ \ t₂).getKey! k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (instInhabitedNat) _ (1)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_inter_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_inter_of_mem_right.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, (t₁ ∩ t₂).getKey! k = t₁.getKey! k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_filter_of_getKey?_eq_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_filter_of_getKey?_eq_some.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Bool}
        {k k' : α},
        t.getKey? k = Option.some k' →
          Std.DTreeMap.Const.get? (Std.DTreeMap.filter f t) k =
            Option.filter (fun (x : β) => f k' x) (Std.DTreeMap.Const.get? t k) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Bool) (Std.DTreeMap.ofList [(⟨0, Bool.false⟩ : (_ : Nat) × Bool), (⟨1, Bool.false⟩ : (_ : Nat) × Bool)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (fun (a : Nat) => Bool.not) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_filter_of_getKey?_eq_some, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_filter_of_getKey?_eq_some.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {f : α → β → Bool} {k k' : α},
        Std.DTreeMap.Const.get? (Std.DTreeMap.filter f t) k =
          Option.filter (fun (x : β) => f k' x) (Std.DTreeMap.Const.get? t k) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (fun a b => a ≤ b : Nat → Nat → Bool) (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_diff_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_diff_of_not_mem_left.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        (t₁ \ t₂).getKeyD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_congr.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a b : α} {fallback : β}, Std.DTreeMap.Const.getD t a fallback = Std.DTreeMap.Const.getD t b fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryLT!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryLT!_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited (α × β)] {k : α}, t₁.getEntryLT! k = t₂.getEntryLT! k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedProd) (1)) (by
  decide +kernel)

-- Std.DTreeMap.contains_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {k' : α} {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.self_le_maxKey?_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.self_le_maxKey?_insert.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k} {kmi : α},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.self_le_maxKey?_insert, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.self_le_maxKey?_insert.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k} {kmi : α}, (cmp k kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (1) (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_diff_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_diff_of_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {k fallback : α}, (t₁ \ t₂).getKeyD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_union_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_union_of_not_mem_left.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Inhabited α] [inst_1 : Std.TransCmp cmp]
        {k : α}, (t₁ ∪ t₂).getKey! k = t₂.getKey! k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (instInhabitedNat) _ (1)) (by
  decide +kernel)

-- Std.TreeMap.getD_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_congr.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a b : α} {fallback : β},
        t.getD a fallback = t.getD b fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (1)) (by
  decide +kernel)

-- Std.DTreeMap.minKeyD_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKeyD_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : β k → β k} {fallback : α}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun n => n + 1 : Nat → Nat) (Bool.false)) (by
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

-- Std.TreeMap.getD_filter', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_filter'.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → Bool} {k : α}
        {fallback : β}, (Std.TreeMap.filter f t).getD k fallback = (Option.filter (f k) t[k]?).getD fallback := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, Bool.false)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (fun a b => !a || b : Bool → Bool → Bool) (Bool.true) (Bool.true)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getKeyLTD_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyLTD_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        t₁.getKeyLTD k fallback = t₂.getKeyLTD k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (1) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constModify, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constModify.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] (k : α) (f : β → β),
        (Std.DTreeMap.Const.modify t₁ k f).Equiv (Std.DTreeMap.Const.modify t₂ k f) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_inter_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_inter_of_not_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Inhabited α]
        [inst_1 : Std.TransCmp cmp] {k : α}, (t₁ ∩ t₂).getKey! k = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (instInhabitedBool) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.keyAtIdx!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.keyAtIdx!_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {i : Nat}, t₁.keyAtIdx! i = t₂.keyAtIdx! i := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.TreeMap.contains_alter_of_not_compare_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_alter_of_not_compare_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k k' : α}
        {f : Option β → Option β}, (t.alter k f).contains k' = t.contains k' := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_alter_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_alter_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α} {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.get!_alter_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_alter_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        [inst : Inhabited (β k)] {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.TreeMap.Equiv.getEntryGE!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryGE!_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited (α × β)] {k : α}, t₁.getEntryGE! k = t₂.getEntryGE! k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedProd) (0)) (by
  decide +kernel)

-- Std.TreeMap.getD_diff_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_diff_of_mem_right.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {fallback : β},
        (t₁ \ t₂).getD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getKey!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKey!_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, t₁.getKey! k = t₂.getKey! k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeMap.contains_of_contains_map, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_of_contains_map.h8 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → γ} {k : α},
        t.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_alter_of_compare_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_alter_of_compare_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k k' : α} {f : Option β → Option β},
        k' ∈ Std.DTreeMap.Const.alter t k f ↔ (f (Std.DTreeMap.Const.get? t k)).isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.TreeMap.getKey_alter_self, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_alter_self.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α} {f : Option β → Option β}, k ∈ t.alter k f := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

-- Std.DTreeMap.get!_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_erase.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {a : α} [inst : Inhabited (β a)], Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (instInhabitedNat)) (by
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

-- Std.DTreeMap.getKey!_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_congr.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k k' : α}, t.getKey! k = t.getKey! k' := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getD_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getD_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {fallback : β},
        t₁.getD k fallback = t₂.getD k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem_modify, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_modify.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k k' : α} {f : β → β} {hc : k' ∈ t.modify k f},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_modify, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_modify.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k k' : α} {f : β → β},
        k' ∈ t.modify k f := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.insert, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.insert.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] (k : α) (v : β),
        (t₁.insert k v).Equiv (t₂.insert k v) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (1) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_diff_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_diff_of_not_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Inhabited α]
        [inst_1 : Std.TransCmp cmp] {k : α}, (t₁ \ t₂).getKey! k = t₁.getKey! k := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (instInhabitedBool) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getKeyGT!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyGT!_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, t₁.getKeyGT! k = t₂.getKeyGT! k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryGT!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryGT!_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited (α × β)] {k : α}, t₁.getEntryGT! k = t₂.getEntryGT! k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedProd) (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getKeyGTD_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyGTD_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        t₁.getKeyGTD k fallback = t₂.getKeyGTD k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_alter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_alter.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {k' : α} {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.TreeMap.Equiv.getEntryLTD_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryLTD_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {fallback : α × β}, t₁.getEntryLTD k fallback = t₂.getEntryLTD k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (1) ((0, 1))) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.keyAtIdxD_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.keyAtIdxD_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {i : Nat}
        {fallback : α}, t₁.keyAtIdxD i fallback = t₂.keyAtIdxD i fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.self_le_maxKey?_insertIfNew, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.self_le_maxKey?_insertIfNew.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β} {kmi : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.self_le_maxKey?_insertIfNew, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.self_le_maxKey?_insertIfNew.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {v : β} {kmi : α},
        (cmp k kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (1) (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constAlter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constAlter.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] (k : α) (f : Option β → Option β),
        (Std.DTreeMap.Const.alter t₁ k f).Equiv (Std.DTreeMap.Const.alter t₂ k f) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (1) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyGE!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyGE!_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α}, t₁.getKeyGE! k = t₂.getKeyGE! k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyGT!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyGT!_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α}, t₁.getKeyGT! k = t₂.getKeyGT! k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constGetEntryGE!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGE!_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst : Inhabited (α × β)] {k : α},
        Std.DTreeMap.Const.getEntryGE! t₁ k = Std.DTreeMap.Const.getEntryGE! t₂ k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedProd) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getD_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_erase.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {a : α} {fallback : β a}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (0)) (by
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

-- Std.DTreeMap.minKey?_insert_le_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey?_insert_le_self.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k} {kmi : α},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.minKey?_insert_le_self, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey?_insert_le_self.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k} {kmi : α}, (cmp kmi k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.keyAtIdx!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.keyAtIdx!_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {i : Nat}, t₁.keyAtIdx! i = t₂.keyAtIdx! i := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_insert.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k a : α} {v : β}
        {h₁ : a ∈ t.insert k v}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_insert, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_insert.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k a : α} {v : β}, a ∈ t.insert k v := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyD_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyD_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {k fallback : α}, t₁.getKeyD k fallback = t₂.getKeyD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.toList_insert_perm, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.toList_insert_perm.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : BEq α]
        [inst_1 : Std.TransCmp cmp] {k : α} {v : β k},
        (t.insert k v).toList.Perm
          ((⟨k, v⟩ : (a : α) × β a) ::
            List.filter (fun (x : (a : α) × β a) => Decidable.decide ¬(k == x.fst) = Bool.true) t.toList) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (1) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_modify_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_modify_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α} {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.getD_insert_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_insert_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        {fallback b : β a}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0) (0)) (by
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

-- Std.DTreeMap.Const.getD_diff_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_diff_of_not_mem_left.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β}, Std.DTreeMap.Const.getD (t₁ \ t₂) k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.contains_insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_insertMany_list.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : BEq α]
        {l : List (α × β)} {k : α}, (t.insertMany l).contains k = (t.contains k || (List.map Prod.fst l).contains k) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(0, 0)]) (1)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey!_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey!_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α} {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.Const.getD_union_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_union_of_not_mem_right.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β},
        Std.DTreeMap.Const.getD (t₁ ∪ t₂) k fallback = Std.DTreeMap.Const.getD t₁ k fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_union_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_union_of_not_mem_left.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {k fallback : α}, (t₁ ∪ t₂).getKeyD k fallback = t₂.getKeyD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryGED_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryGED_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {fallback : α × β}, t₁.getEntryGED k fallback = t₂.getEntryGED k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) ((0, 1))) (by
  decide +kernel)

-- Std.TreeMap.Equiv.entryAtIdx!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.entryAtIdx!_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited (α × β)] {i : Nat}, t₁.entryAtIdx! i = t₂.entryAtIdx! i := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedProd) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_diff_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_diff_of_not_mem_left.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, (t₁ \ t₂).getKey! k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyLE!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyLE!_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α}, t₁.getKeyLE! k = t₂.getKeyLE! k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyLT!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyLT!_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {k : α}, t₁.getKeyLT! k = t₂.getKeyLT! k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (2)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insert.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k a : α} {v : β k}
        {h₁ : a ∈ t.insert k v}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey_insert, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insert.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α}
        {v : β k}, a ∈ t.insert k v := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constGetEntryGT!_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constGetEntryGT!_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst : Inhabited (α × β)] {k : α},
        Std.DTreeMap.Const.getEntryGT! t₁ k = Std.DTreeMap.Const.getEntryGT! t₂ k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedProd) (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryLED_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryLED_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {fallback : α × β}, t₁.getEntryLED k fallback = t₂.getEntryLED k fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) ((0, 1))) (by
  decide +kernel)

-- Std.TreeMap.getElem!_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem!_congr.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited β]
        {a b : α}, t[a]! = t[b]! := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.minKey?_insert_le_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey?_insert_le_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β} {kmi : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.minKey?_insert_le_self, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey?_insert_le_self.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {v : β} {kmi : α},
        (cmp kmi k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_inter_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_inter_of_not_mem_left.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β}, Std.DTreeMap.Const.getD (t₁ ∩ t₂) k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.self_le_maxKey?_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.self_le_maxKey?_insert.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β} {kmi : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.self_le_maxKey?_insert, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.self_le_maxKey?_insert.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {v : β} {kmi : α},
        (cmp k kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (1) (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyGED_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyGED_eq.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {k fallback : α}, t₁.getKeyGED k fallback = t₂.getKeyGED k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.get!_union, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_union.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        [inst : Inhabited (β k)], Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat)) (by
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

-- Std.TreeMap.getKey_modify_self, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_modify_self.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α} {f : β → β}, k ∈ t.modify k f := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.mem_alter_of_compare_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_alter_of_compare_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k k' : α}
        {f : Option β → Option β}, k' ∈ t.alter k f ↔ (f t[k]?).isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.insertIfNew, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.insertIfNew.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] (k : α)
        (v : β k), (t₁.insertIfNew k v).Equiv (t₂.insertIfNew k v) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.mem_insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_insertMany_list.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List ((a : α) × β a)} {k : α},
        k ∈ t.insertMany l ↔ k ∈ t ∨ (List.map Sigma.fst l).contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_map, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_map.h6 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → γ} {k : α},
        (Std.TreeMap.map f t)[k]? = Option.map (f k) t[k]? := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, Bool.false)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (fun a b => !a || b : Bool → Bool → Bool) (Bool.true)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_union_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_union_of_not_mem_right.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {k fallback : α}, (t₁ ∪ t₂).getKeyD k fallback = t₁.getKeyD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_union_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_union_of_not_mem_left.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst : Inhabited β] {k : α},
        Std.DTreeMap.Const.get! (t₁ ∪ t₂) k = Std.DTreeMap.Const.get! t₂ k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 1⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedNat) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_diff_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_diff_of_not_mem_right.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β},
        Std.DTreeMap.Const.getD (t₁ \ t₂) k fallback = Std.DTreeMap.Const.getD t₁ k fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.isSome_apply_of_mem_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.isSome_apply_of_mem_filterMap.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Option γ} {k : α},
        k ∈ Std.TreeMap.filterMap f t → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun (a : Nat) => Option.some) (0) (by
  decide +kernel)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.isSome_apply_of_mem_filterMap, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.isSome_apply_of_mem_filterMap.h8 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → Option γ}
        {k : α}, k ∈ Std.TreeMap.filterMap f t := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (fun (a x : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.DTreeMap.get!_insert_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_insert_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        [inst : Inhabited (β a)] {b : β a}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat) (0)) (by
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

-- Std.DTreeMap.Const.getD_filter', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_filter'.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {f : α → β → Bool} {k : α} {fallback : β},
        Std.DTreeMap.Const.getD (Std.DTreeMap.filter f t) k fallback =
          (Option.filter (f k) (Std.DTreeMap.Const.get? t k)).getD fallback := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Bool) (Std.DTreeMap.ofList [(⟨Bool.false, Bool.false⟩ : (_ : Bool) × Bool)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (fun a b => !a || b : Bool → Bool → Bool) (Bool.true) (Bool.true)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_insertIfNew, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insertIfNew.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k a : α} {v : β k}
        {h₁ : a ∈ t.insertIfNew k v}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey_insertIfNew, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insertIfNew.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α}
        {v : β k}, a ∈ t.insertIfNew k v := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1) (0)) (by
  decide +kernel)

-- Std.TreeMap.getD_diff_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_diff_of_not_mem_left.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {fallback : β},
        (t₁ \ t₂).getD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_diff_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_diff_of_mem_right.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] [inst : Inhabited β] {k : α}, Std.DTreeMap.Const.get! (t₁ \ t₂) k = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 1⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedNat) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_union_of_not_mem_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_union_of_not_mem_left.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Inhabited α]
        [inst_1 : Std.TransCmp cmp] {k : α}, (t₁ ∪ t₂).getKey! k = t₂.getKey! k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (instInhabitedNat) _ (1)) (by
  decide +kernel)

-- Std.TreeMap.getKey_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_map.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → γ} {k : α}
        {h' : k ∈ Std.TreeMap.map f t}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a - b : Nat → Nat → Nat) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_map, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_map.h8 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → γ} {k : α},
        k ∈ Std.TreeMap.map f t := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.get?_insertIfNew, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_insertIfNew.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {a : α} {v : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (0)) (by
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

-- Std.DTreeMap.Const.getD_inter_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_inter_of_mem_right.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β},
        Std.DTreeMap.Const.getD (t₁ ∩ t₂) k fallback = Std.DTreeMap.Const.getD t₁ k fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.mem_alter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_alter.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {k' : α} {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.Equiv.constEntryAtIdxD_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constEntryAtIdxD_eq.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {i : Nat} {fallback : α × β},
        Std.DTreeMap.Const.entryAtIdxD t₁ i fallback = Std.DTreeMap.Const.entryAtIdxD t₂ i fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) ((0, 1))) (by
  decide +kernel)

-- Std.DTreeMap.getD_diff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_diff.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {fallback : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0)) (by
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

-- Std.TreeMap.contains_of_contains_filterMap, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_of_contains_filterMap.h8 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → Option γ}
        {k : α}, t.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (fun (a x : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_inter_of_not_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_inter_of_not_mem_right.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        (t₁ ∩ t₂).getKeyD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.self_le_maxKey?_insertIfNew, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.self_le_maxKey?_insertIfNew.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k} {kmi : α},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.self_le_maxKey?_insertIfNew, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.self_le_maxKey?_insertIfNew.h8 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k} {kmi : α}, (cmp k kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (1) (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_diff_of_mem_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_diff_of_mem_right.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α} {fallback : β}, Std.DTreeMap.Const.getD (t₁ \ t₂) k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.getKey_maxKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_maxKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.max_eq_iff_mem_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_eq_iff_mem_and_forall.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {km : α}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get?_eq_some_of_contains, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_eq_some_of_contains.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        t.contains k = Bool.true → t.get? k = Option.some k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get?_eq_some_of_contains, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_eq_some_of_contains.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Std.LawfulEqCmp cmp]
        {k : α}, t.get? k = Option.some k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_minKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_minKey.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.get_max?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_max?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {km : α} {hc : t.contains km = Bool.true},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.get_max?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_max?.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get_max?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_max?.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km : α}
        {hc : t.contains km = Bool.true}, t.get km hc = km := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) hc_k0) (by
  decide +kernel)

-- Std.TreeSet.Equiv.of_forall_mem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.of_forall_mem_iff.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp], t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ _) (by
  decide +kernel)

-- Std.TreeSet.max_erase_eq_of_not_compare_eq_max, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_erase_eq_of_not_compare_eq_max.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α} {he : (t.erase k).isEmpty = Bool.false},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.max_erase_eq_of_not_compare_eq_max, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_erase_eq_of_not_compare_eq_max.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        (t.erase k).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey_minKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_minKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.equiv_of_beq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.equiv_of_beq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {m₁ m₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp]
        [inst : Std.LawfulEqCmp cmp], m₁.Equiv m₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ _) (by
  decide +kernel)

-- Std.DTreeMap.maxKey?_alter_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey?_alter_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.getKeyD_maxKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_maxKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {km fallback : α},
        t.maxKey? = Option.some km → t.getKeyD km fallback = km := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (Bool.true) (by
  simp +ground +decide [Std.DTreeMap.getKeyD, Std.DTreeMap.Internal.Impl.getKeyD, Std.DTreeMap.inner,
    Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.below, Std.DTreeMap.Internal.Impl.brecOn.go])) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_maxKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_maxKey?.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {km fallback : α}, t.getKeyD km fallback = km := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.mem_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.mem_iff.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t₁ ↔ k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.get?_union, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_union.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.DTreeMap.Const.get?_inter_of_mem_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_inter_of_mem_right.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α},
        k ∈ t₂ → Std.DTreeMap.Const.get? (t₁ ∩ t₂) k = Std.DTreeMap.Const.get? t₁ k := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_inter_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_inter_of_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α}, Std.DTreeMap.Const.get? (t₁ ∩ t₂) k = Std.DTreeMap.Const.get? t₁ k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_insertManyIfNewUnit_list, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_insertManyIfNewUnit_list.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List α} {k : α},
        k ∈ Std.DTreeMap.Const.insertManyIfNewUnit t l ↔ k ∈ t ∨ l.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKey?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKey?_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.getKey? k = t₂.getKey? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey_le_maxKey_insertIfNew, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_le_maxKey_insertIfNew.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k}
        {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.maxKey_le_maxKey_insertIfNew, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_le_maxKey_insertIfNew.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_of_isEmpty, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_of_isEmpty.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {a : α}, t.getKey! a = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_diff_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_diff_of_mem_right.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ \ t₂).getKey? k = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_eq_some_getD, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_eq_some_getD.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α} {fallback : β}, Std.DTreeMap.Const.get? t a = Option.some (Std.DTreeMap.Const.getD t a fallback) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_eq_default, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_eq_default.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited β] {a : α}, Std.DTreeMap.Const.get! t a = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 1⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedNat) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.Const.minKey_alter_eq_self, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.minKey_alter_eq_self.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k : α} {f : Option β → Option β}, (Std.DTreeMap.Const.alter t k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

-- Std.DTreeMap.get?_inter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_inter.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.DTreeMap.size_le_size_alter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_le_size_alter.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.size_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.Const.mem_toArray_iff_get?_eq_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_toArray_iff_get?_eq_some.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k : α} {v : β}, (k, v) ∈ Std.DTreeMap.Const.toArray t ↔ Std.DTreeMap.Const.get? t k = Option.some v := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) (0)) (by
  decide +kernel)

-- Std.DTreeMap.mem_ofList, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_ofList.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α]
        {l : List ((a : α) × β a)} {k : α}, k ∈ Std.DTreeMap.ofList l cmp ↔ (List.map Sigma.fst l).contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(⟨0, 0⟩ : (a : Nat) × (fun (a : Nat) => Nat) a)]) (1)) (by
  decide +kernel)

-- Std.DTreeMap.get!_eq_get!_get?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_eq_get!_get?.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        [inst : Inhabited (β a)], Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat)) (by
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

-- Std.DTreeMap.Equiv.insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.insertMany_list.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        (l : List ((a : α) × β a)), (t₁.insertMany l).Equiv (t₂.insertMany l) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ ([])) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_eq_get!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_eq_get!.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited β] {a : α}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedNat) (Bool.false)) (by
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

-- Std.DTreeMap.Const.getD_eq_getD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_eq_getD.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α} {fallback : β}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0)) (by
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

-- Std.DTreeMap.minKey_insert_le_minKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_insert_le_minKey.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k}
        {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.minKey_insert_le_minKey, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_insert_le_minKey.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.mem_of_getKey?_eq_some, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_getKey?_eq_some.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {k' : α}, k' ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_diff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_diff.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} {k : α} {h_mem : k ∈ t₁ \ t₂},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey_diff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_diff.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t₁ \ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_toList_iff_get?_eq_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_toList_iff_get?_eq_some.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k : α} {v : β}, (k, v) ∈ Std.DTreeMap.Const.toList t ↔ Std.DTreeMap.Const.get? t k = Option.some v := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_insertManyIfNewUnit_list, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_insertManyIfNewUnit_list.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        [inst : BEq α] {l : List α} {k : α},
        Std.DTreeMap.Const.get? (Std.DTreeMap.Const.insertManyIfNewUnit t l) k =
          if k ∈ t ∨ l.contains k = Bool.true then Option.some () else Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.union_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.union_right.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∪ t₂).Equiv (t₁ ∪ t₃) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_inter.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α}
        {h_mem : k ∈ t₁ ∩ t₂}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide +kernel)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_inter, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_inter.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α}, k ∈ t₁ ∩ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_diff_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_diff_of_not_mem_right.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ \ t₂).getKey? k = t₁.getKey? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_union_of_mem_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_union_of_mem_right.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ : Std.DTreeMap α (fun (x : α) => β) cmp}
        {t₂ : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α}, k ∈ t₂ → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_union_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_union_of_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ : Std.DTreeMap α (fun (x : α) => β) cmp}
        {t₂ : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.find?_toArray_eq_some_iff_get?_eq_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.find?_toArray_eq_some_iff_get?_eq_some.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0)) (by
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

-- Std.DTreeMap.contains_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_congr.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k k' : α},
        t.contains k = t.contains k' := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getThenInsertIfNew?_snd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getThenInsertIfNew?_snd.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0)) (by
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

-- Std.DTreeMap.minKey_insertIfNew_le_minKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_insertIfNew_le_minKey.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k}
        {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.minKey_insertIfNew_le_minKey, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_insertIfNew_le_minKey.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.ordCompare_minKey_modify_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.ordCompare_minKey_modify_eq.h3 : Not
      (∀ {α β : Type} [inst : Ord α] {t : Std.DTreeMap α (fun (x : α) => β) (@Ord.compare α inst)} {k : α} {f : β → β}
        {he :
          @Eq Bool
            (@Std.DTreeMap.isEmpty α (fun (x : α) => β) (@Ord.compare α inst)
              (@Std.DTreeMap.Const.modify α (@Ord.compare α inst) β t k f))
            Bool.false},
        @Std.TransOrd α inst) := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
      (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
        (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
      (@Ord.compare Nat
        (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.ordCompare_minKey_modify_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.ordCompare_minKey_modify_eq.h7 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] {t : Std.DTreeMap α (fun (x : α) => β) Ord.compare} {k : α}
        {f : β → β}, (Std.DTreeMap.Const.modify t k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (Std.DTreeMap.ofList [] Ord.compare) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constInsertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constInsertMany_list.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] (l : List (α × β)),
        (Std.DTreeMap.Const.insertMany t₁ l).Equiv (Std.DTreeMap.Const.insertMany t₂ l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ ([])) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_eq_fallback, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_eq_fallback.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {a fallback : α}, t.getKeyD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getEntryLT?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getEntryLT?_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.getEntryLT? k = t₂.getEntryLT? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (1)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_erase.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k a : α} {h' : a ∈ t.erase k},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (1) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey_erase, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_erase.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α},
        a ∈ t.erase k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.contains_of_contains_erase, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_of_contains_erase.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {a : α}, t.contains a = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey?_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey?_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.getKey?_union_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_union_of_not_mem_right.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∪ t₂).getKey? k = t₁.getKey? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_of_isEmpty, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_of_isEmpty.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α} {fallback : β}, Std.DTreeMap.Const.getD t a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.getKeyLT?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.getKeyLT?_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.getKeyLT? k = t₂.getKeyLT? k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (1)) (by
  decide +kernel)

-- Std.DTreeMap.minKey?_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey?_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.DTreeMap.getKey_union_of_mem_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_union_of_mem_right.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp} {k : α},
        k ∈ t₂ → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey_union_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_union_of_mem_right.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ : Std.DTreeMap α β cmp} {t₂ : Std.DTreeMap α β cmp}
        [inst : Std.TransCmp cmp] {k : α}, k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_eq_getKeyD, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_eq_getKeyD.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}
        {fallback : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_modify_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_modify_self.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {f : β → β}
        {hc : k ∈ Std.DTreeMap.Const.modify t k f}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_modify_self, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_modify_self.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp}
        {k : α} {f : β → β}, k ∈ Std.DTreeMap.Const.modify t k f := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_eq_some_get!_of_contains, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_eq_some_get!_of_contains.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited β] {a : α}, Std.DTreeMap.Const.get? t a = Option.some (Std.DTreeMap.Const.get! t a) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_congr.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a b : α}, Std.DTreeMap.Const.get? t a = Std.DTreeMap.Const.get? t b := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.contains_ofList, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.contains_ofList.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List (α × β)} {k : α},
        (Std.DTreeMap.Const.ofList l cmp).contains k = (List.map Prod.fst l).contains k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(0, 0)]) (1)) (by
  decide +kernel)

-- Std.DTreeMap.get_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_insert_self.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.LawfulEqCmp cmp] {k : α}
        {v : β k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_insert_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_insert_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0)) (by
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

-- Std.DTreeMap.mem_toList_iff_get?_eq_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_toList_iff_get?_eq_some.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0)) (by
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

-- Std.DTreeMap.getKey!_minKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_minKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Inhabited α] {km : α},
        t.minKey? = Option.some km → t.getKey! km = km := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (Bool.true) (by
  simp +ground +decide [Std.DTreeMap.getKey!, Std.DTreeMap.Internal.Impl.getKey!, Std.DTreeMap.inner,
    Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.below, Std.DTreeMap.Internal.Impl.brecOn.go])) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_minKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_minKey?.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {km : α}, t.getKey! km = km := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.erase.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] (k : α),
        (t₁.erase k).Equiv (t₂.erase k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_eq_some_getD_of_contains, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_eq_some_getD_of_contains.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α} {fallback : β}, Std.DTreeMap.Const.get? t a = Option.some (Std.DTreeMap.Const.getD t a fallback) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.minKeyD_eq_iff_getKey?_eq_self_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKeyD_eq_iff_getKey?_eq_self_and_forall.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {km fallback : α},
        t.minKeyD fallback = km ↔ t.getKey? km = Option.some km ∧ ∀ (k : α), k ∈ t → (cmp km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  simp +ground +decide [Std.DTreeMap.minKeyD, Std.DTreeMap.getKey?, Std.DTreeMap.instMembership,
    Std.DTreeMap.Internal.Impl.minKeyD, Std.DTreeMap.inner, Std.DTreeMap.Internal.Impl.getKey?, Std.DTreeMap.contains,
    Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.Internal.Impl.below,
    Std.DTreeMap.Internal.Impl.brecOn.go])

-- Std.DTreeMap.get?_eq_some_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_eq_some_iff.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0)) (by
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

-- Std.DTreeMap.Const.maxKey_modify, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.maxKey_modify.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {f : β → β}
        {he : (Std.DTreeMap.Const.modify t k f).isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.maxKey_modify, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.maxKey_modify.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k : α} {f : β → β}, (Std.DTreeMap.Const.modify t k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.DTreeMap.Const.ordCompare_maxKey_modify_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.ordCompare_maxKey_modify_eq.h3 : Not
      (∀ {α β : Type} [inst : Ord α] {t : Std.DTreeMap α (fun (x : α) => β) (@Ord.compare α inst)} {k : α} {f : β → β}
        {he :
          @Eq Bool
            (@Std.DTreeMap.isEmpty α (fun (x : α) => β) (@Ord.compare α inst)
              (@Std.DTreeMap.Const.modify α (@Ord.compare α inst) β t k f))
            Bool.false},
        @Std.TransOrd α inst) := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (@Std.DTreeMap.ofList Nat (fun (x : Nat) => Nat)
      (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
        (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (@Sigma Nat fun (a : Nat) => Nat)))
      (@Ord.compare Nat
        (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.ordCompare_maxKey_modify_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.ordCompare_maxKey_modify_eq.h7 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] {t : Std.DTreeMap α (fun (x : α) => β) Ord.compare} {k : α}
        {f : β → β}, (Std.DTreeMap.Const.modify t k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (Std.DTreeMap.ofList [] Ord.compare) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.DTreeMap.minKey!_eq_iff_getKey?_eq_self_and_forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey!_eq_iff_getKey?_eq_self_and_forall.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {km : α},
        t.minKey! = km ↔ t.getKey? km = Option.some km ∧ ∀ (k : α), k ∈ t → (cmp km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  simp +ground +decide [Std.DTreeMap.minKey!, Std.DTreeMap.getKey?, Std.DTreeMap.instMembership,
    Std.DTreeMap.Internal.Impl.minKey!, Std.DTreeMap.inner, Std.DTreeMap.Internal.Impl.getKey?, Std.DTreeMap.contains,
    Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.Internal.Impl.below,
    Std.DTreeMap.Internal.Impl.brecOn.go])

-- Std.DTreeMap.get?_diff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_diff.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.DTreeMap.Const.getD_eq_fallback_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_eq_fallback_of_contains_eq_false.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α} {fallback : β}, Std.DTreeMap.Const.getD t a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.diff_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.diff_left.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ \ t₃).Equiv (t₂ \ t₃) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_eq_some_get!, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_eq_some_get!.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited β] {a : α}, Std.DTreeMap.Const.get? t a = Option.some (Std.DTreeMap.Const.get! t a) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.inter_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.inter_right.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₂).Equiv (t₁ ∩ t₃) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_eq_some_getKey!_of_contains, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_eq_some_getKey!_of_contains.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {a : α}, t.getKey? a = Option.some (t.getKey! a) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_of_isEmpty, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_of_isEmpty.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited β] {a : α}, Std.DTreeMap.Const.get! t a = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 1⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedNat) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_minKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_minKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {km fallback : α},
        t.minKey? = Option.some km → t.getKeyD km fallback = km := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (Bool.true) (by
  simp +ground +decide [Std.DTreeMap.getKeyD, Std.DTreeMap.Internal.Impl.getKeyD, Std.DTreeMap.inner,
    Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.below, Std.DTreeMap.Internal.Impl.brecOn.go])) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_minKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_minKey?.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {km fallback : α}, t.getKeyD km fallback = km := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.mem_alter_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_alter_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.get?_erase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_erase.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k a : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.false)) (by
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

-- Std.DTreeMap.minKey?_alter_eq_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey?_alter_eq_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.TreeMap.getKey?_inter_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_inter_of_not_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∩ t₂).getKey? k = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_eq_default_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_eq_default_of_contains_eq_false.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited β] {a : α}, Std.DTreeMap.Const.get! t a = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 1⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedNat) (Bool.false)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_minKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_minKey?.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {km : α}, t.getKey! km = km := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_eq_default_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_eq_default_of_contains_eq_false.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {a : α}, t.getKey! a = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_diff_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_diff_of_not_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ \ t₂).getKey? k = t₁.getKey? k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {l : List α} {k : α}, (Std.DTreeMap.Const.insertManyIfNewUnit t l).getKey! k = t.getKey! k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([1]) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_congr.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k k' : α},
        t.getKey? k = t.getKey? k' := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.union_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.union_left.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∪ t₃).Equiv (t₂ ∪ t₃) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_inter_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_inter_of_not_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α}, Std.DTreeMap.Const.get? (t₁ ∩ t₂) k = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_diff_of_not_mem_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_diff_of_not_mem_left.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp] {k : α}, Std.DTreeMap.Const.get? (t₁ \ t₂) k = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_eq_default, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_eq_default.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α] {a : α}, t.getKey! a = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_eq_fallback, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_eq_fallback.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a fallback : α},
        t.getKeyD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_insertManyIfNewUnit_list_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_insertManyIfNewUnit_list_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] {l : List α}
        {k fallback : α}, (t.insertManyIfNewUnit l).getKeyD k fallback = t.getKeyD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0]) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_of_isEmpty, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_of_isEmpty.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {a fallback : α}, t.getKeyD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryGE?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryGE?_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.getEntryGE? k = t₂.getEntryGE? k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_union_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_union_of_not_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∪ t₂).getKey? k = t₁.getKey? k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_eq_some_getKeyD, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_eq_some_getKeyD.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {a fallback : α}, t.getKey? a = Option.some (t.getKeyD a fallback) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem!_eq_default, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem!_eq_default.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited β]
        {a : α}, t[a]! = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 1)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.compare_maxKey_modify_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.compare_maxKey_modify_eq.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {f : β → β}
        {he : (Std.DTreeMap.Const.modify t k f).isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.compare_maxKey_modify_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.compare_maxKey_modify_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {k : α} {f : β → β}, (Std.DTreeMap.Const.modify t k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.getKey_union_of_mem_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_union_of_mem_right.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ : Std.TreeMap α β cmp} {t₂ : Std.TreeMap α β cmp} {k : α},
        k ∈ t₂ → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_union_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_union_of_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ : Std.TreeMap α β cmp} {t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp]
        {k : α}, k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_filter.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Bool} {k : α}
        {h' : k ∈ Std.TreeMap.filter f t}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a ≤ b : Nat → Nat → Bool) (0) (by
  decide +kernel)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_filter, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_filter.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → Bool} {k : α},
        k ∈ Std.TreeMap.filter f t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (fun a b => a < b : Nat → Nat → Bool) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey_eq_getKeyD, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_eq_getKeyD.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α} {fallback : α},
        a ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeMap.minKey_alter_eq_self, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_alter_eq_self.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option β → Option β}, (t.alter k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (fun (a : Option Nat) => Option.none)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.contains_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.contains_eq.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.contains k = t₂.contains k := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.minKey_modify, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_modify.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {f : β → β}
        {he : (t.modify k f).isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.minKey_modify, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_modify.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {f : β → β},
        (t.modify k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_filter', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_filter'.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {f : α → β → Bool} {k : α},
        (Std.TreeMap.filter f t)[k]? = Option.filter (f k) t[k]? := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, Bool.false)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (fun a b => !a || b : Bool → Bool → Bool) (Bool.true)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_eq_default_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_eq_default_of_contains_eq_false.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {a : α}, t.getKey! a = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_eq_some_getKeyD, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_eq_some_getKeyD.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a fallback : α},
        t.getKey? a = Option.some (t.getKeyD a fallback) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_of_isEmpty, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_of_isEmpty.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a fallback : α},
        t.getKeyD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.mem_union_of_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_union_of_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t₁ ∪ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.get?_insert_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_insert_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0)) (by
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

-- Std.TreeMap.Equiv.contains_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.contains_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.contains k = t₂.contains k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.mem_of_mem_erase, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_of_mem_erase.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_inter_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_inter_of_not_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∩ t₂)[k]? = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getElem?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getElem?_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁[k]? = t₂[k]? := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.mem_of_mem_erase, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_erase.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey_le_maxKey_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_le_maxKey_insert.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k}
        {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.maxKey_le_maxKey_insert, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_le_maxKey_insert.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {v : β k}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.keyAtIdx?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.keyAtIdx?_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {i : Nat},
        t₁.keyAtIdx? i = t₂.keyAtIdx? i := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.size_alter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_alter.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : Option (β k) → Option (β k)}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun (a : Option ((fun (a : Bool) => Nat) Bool.false)) => Option.none)) (by
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

-- Std.DTreeMap.isEmpty_modify, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isEmpty_modify.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}
        {f : β k → β k}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
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

-- Std.TreeMap.mem_union_of_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_union_of_left.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t₁ ∪ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_union_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_union_of_not_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∪ t₂)[k]? = t₁[k]? := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.compare_maxKey_modify_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.compare_maxKey_modify_eq.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {f : β → β}
        {he : (t.modify k f).isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.compare_maxKey_modify_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.compare_maxKey_modify_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {f : β → β},
        (t.modify k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryLE?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryLE?_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.getEntryLE? k = t₂.getEntryLE? k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.diff_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.diff_right.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ \ t₂).Equiv (t₁ \ t₃) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.Equiv.eraseMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.eraseMany_list.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] (l : List α),
        (t₁.eraseMany l).Equiv (t₂.eraseMany l) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ ([])) (by
  decide +kernel)

-- Std.TreeMap.minKey_insertIfNew_of_isEmpty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_insertIfNew_of_isEmpty.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β},
        t.isEmpty = Bool.true → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey!_of_isEmpty, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_of_isEmpty.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {a : α}, t.getKey! a = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(1, 0)] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_inter_of_not_mem_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_inter_of_not_mem_left.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∩ t₂)[k]? = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.maxKey_le_maxKey_insertIfNew, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_le_maxKey_insertIfNew.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β} {he : t.isEmpty = Bool.false},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.maxKey_le_maxKey_insertIfNew, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_le_maxKey_insertIfNew.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {v : β},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeMap.maxKey!_eq_iff_getKey?_eq_self_and_forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey!_eq_iff_getKey?_eq_self_and_forall.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {km : α}, t.maxKey! = km ↔ t.getKey? km = Option.some km ∧ ∀ (k : α), k ∈ t → (cmp k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  simp +ground +decide [Std.TreeMap.maxKey!, Std.TreeMap.getKey?, Std.TreeMap.instMembership, Std.DTreeMap.maxKey!,
    Std.TreeMap.inner, Std.DTreeMap.getKey?, Std.TreeMap.contains, Std.DTreeMap.Internal.Impl.maxKey!, Std.DTreeMap.inner,
    Std.DTreeMap.Internal.Impl.getKey?, Std.DTreeMap.contains, Std.DTreeMap.Internal.Impl.brecOn,
    Std.DTreeMap.Internal.Impl.contains])

-- Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_insertManyIfNewUnit_list_of_mem.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {l : List α} {k : α}, (t.insertManyIfNewUnit l).getKey! k = t.getKey! k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) ([1]) (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_diff_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_diff_of_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ \ t₂)[k]? = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_eq_fallback_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_eq_fallback_of_contains_eq_false.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a fallback : α},
        t.getKeyD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getKeyLE?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getKeyLE?_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.getKeyLE? k = t₂.getKeyLE? k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.any_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.any_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {p : α → β → Bool},
        t₁.any p = t₂.any p := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (fun a b => a ≤ b : Nat → Nat → Bool)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.erase.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] (k : α),
        (t₁.erase k).Equiv (t₂.erase k) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (1)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_maxKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_maxKey?.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {km : α}, t.getKey! km = km := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.inter_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.inter_left.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₃).Equiv (t₂ ∩ t₃) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.maxKey_le_maxKey_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_le_maxKey_insert.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β} {he : t.isEmpty = Bool.false},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.maxKey_le_maxKey_insert, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_le_maxKey_insert.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α} {v : β},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.trans.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeMap α β cmp}, t₂.Equiv t₃ → t₁.Equiv t₃ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.trans.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeMap α β cmp}, t₁.Equiv t₂ → t₁.Equiv t₃ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_inter_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_inter_of_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∩ t₂)[k]? = t₁[k]? := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_maxKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_maxKey?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {km fallback : α},
        t.maxKey? = Option.some km → t.getKeyD km fallback = km := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (Bool.true) (by
  simp +ground +decide [Std.TreeMap.getKeyD, Std.DTreeMap.getKeyD, Std.TreeMap.inner, Std.DTreeMap.Internal.Impl.getKeyD,
    Std.DTreeMap.inner, Std.DTreeMap.Internal.Impl.brecOn])) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_maxKey?, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_maxKey?.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {km fallback : α},
        t.getKeyD km fallback = km := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.insertMany_list, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.insertMany_list.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] (l : List (α × β)),
        (t₁.insertMany l).Equiv (t₂.insertMany l) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ ([])) (by
  decide +kernel)

-- Std.TreeMap.getD_eq_fallback_of_contains_eq_false, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_eq_fallback_of_contains_eq_false.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α} {fallback : β},
        t.getD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.getEntryGT?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.getEntryGT?_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.getEntryGT? k = t₂.getEntryGT? k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare b a : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare b a) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare b a) _ (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem_eq_getElem!, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_eq_getElem!.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited β]
        {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey_eq_getKey!, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_eq_getKey!.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_inter_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_inter_of_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∩ t₂).getKey? k = t₁.getKey? k := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.all_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.all_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {p : α → β → Bool},
        t₁.all p = t₂.all p := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (fun a b => a < b : Nat → Nat → Bool)) (by
  decide +kernel)

-- Std.TreeMap.ordCompare_minKey_modify_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.ordCompare_minKey_modify_eq.h3 : Not
      (∀ {α β : Type} [inst : Ord α] {t : Std.TreeMap α β (@Ord.compare α inst)} {k : α} {f : β → β}
        {he :
          @Eq Bool (@Std.TreeMap.isEmpty α β (@Ord.compare α inst) (@Std.TreeMap.modify α β (@Ord.compare α inst) t k f))
            Bool.false},
        @Std.TransOrd α inst) := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (@Std.TreeMap.ofList Nat Nat
      (@List.cons (Prod Nat Nat)
        (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (Prod Nat Nat)))
      (@Ord.compare Nat
        (@Ord.mk Nat fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.ordCompare_minKey_modify_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.ordCompare_minKey_modify_eq.h7 : ¬∀ {α β : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] {t : Std.TreeMap α β Ord.compare} {k : α} {f : β → β},
        (t.modify k f).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ (Std.TreeMap.ofList [] Ord.compare) (0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.not_mem_inter_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.not_mem_inter_of_not_mem_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}, ¬k ∈ t₁ ∩ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.diff_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.diff_right.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ \ t₂).Equiv (t₁ \ t₃) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.Equiv.mem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.mem_iff.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t₁ ↔ k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.mem_ofList, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_ofList.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List (α × β)} {k : α},
        k ∈ Std.TreeMap.ofList l cmp ↔ (List.map Prod.fst l).contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([(0, 0)]) (1)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.entryAtIdx?_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.entryAtIdx?_eq.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {i : Nat},
        t₁.entryAtIdx? i = t₂.entryAtIdx? i := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.get!_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.get!_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, t₁.get! k = t₂.get! k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeSet.get!_inter_of_mem_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_inter_of_mem_right.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Inhabited α] {k : α},
        k ∈ t₂ → (t₁ ∩ t₂).get! k = t₁.get! k := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [1, 0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (1) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get!_inter_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_inter_of_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, (t₁ ∩ t₂).get! k = t₁.get! k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.getLTD_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.getLTD_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        t₁.getLTD k fallback = t₂.getLTD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (1) (1)) (by
  decide +kernel)

-- Std.TreeSet.get!_inter_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_inter_of_not_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, (t₁ ∩ t₂).get! k = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.false)) (by
  decide +kernel)

-- Std.TreeSet.get!_inter_of_not_mem_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_inter_of_not_mem_left.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, (t₁ ∩ t₂).get! k = Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.false)) (by
  decide +kernel)

-- Std.TreeSet.mem_insertMany_list, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_insertMany_list.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List α}
        {k : α}, k ∈ t.insertMany l ↔ k ∈ t ∨ l.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) (1)) (by
  decide +kernel)

-- Std.TreeSet.getD_inter_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_inter_of_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        (t₁ ∩ t₂).getD k fallback = t₁.getD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.get!_diff_of_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_diff_of_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, (t₁ \ t₂).get! k = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.getLE!_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.getLE!_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, t₁.getLE! k = t₂.getLE! k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeSet.get!_diff_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_diff_of_not_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, (t₁ \ t₂).get! k = t₁.get! k := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.eq) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (instInhabitedBool) (Bool.false)) (by
  decide +kernel)

-- Std.TreeSet.getD_inter_of_not_mem_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_inter_of_not_mem_left.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        (t₁ ∩ t₂).getD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.getD_union_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_union_of_not_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        (t₁ ∪ t₂).getD k fallback = t₁.getD k fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.getD_inter_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_inter_of_not_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k fallback : α},
        (t₁ ∩ t₂).getD k fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.getGE!_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.getGE!_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, t₁.getGE! k = t₂.getGE! k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.getGT!_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.getGT!_eq.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k : α}, t₁.getGT! k = t₂.getGT! k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.TreeSet.get!_congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_congr.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α]
        {k k' : α}, t.get! k = t.get! k' := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.get!_union_of_not_mem_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_union_of_not_mem_right.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Inhabited α] [inst_1 : Std.TransCmp cmp]
        {k : α}, (t₁ ∪ t₂).get! k = t₁.get! k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) (instInhabitedNat) _ (1)) (by
  decide +kernel)

-- Std.DTreeMap.get!_emptyc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get!_emptyc.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {a : α} [inst : Inhabited (β a)],
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (instInhabitedNat)) (by
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

-- Std.DTreeMap.isEmpty_diff_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isEmpty_diff_left.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ \ t₂).isEmpty = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.getKey_minKey!_eq_minKey, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_minKey!_eq_minKey.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α], t.minKey! ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.DTreeMap.not_mem_of_isEmpty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.not_mem_of_isEmpty.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        ¬a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_le.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.minKey!_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey!_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Inhabited α],
        t.isEmpty = Bool.false → t.minKey! ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.minKey!_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey!_mem.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α], t.minKey! ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.minKeyD_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKeyD_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.minKeyD fallback ∈ t := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.TreeMap.minKeyD_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKeyD_mem.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.minKeyD fallback ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_mem.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α (fun (x : α) => Unit) cmp} [inst : Std.TransCmp cmp]
        {l : List α} {k : α}, (Std.DTreeMap.Const.insertManyIfNewUnit t l).getKey? k = t.getKey? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0]) (0)) (by
  decide +kernel)

-- Std.DTreeMap.size_inter_eq_size_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_inter_eq_size_right.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp},
        (∀ (a : α), a ∈ t₂ → a ∈ t₁) → (t₁ ∩ t₂).size = t₂.size := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.size_inter_eq_size_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_inter_eq_size_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₂).size = t₂.size := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_unitOfList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_unitOfList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List α} {k : α},
        k ∈ Std.DTreeMap.Const.unitOfList l cmp ↔ l.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_eq_some_getElem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_eq_some_getElem.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_maxKeyD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_maxKeyD.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.getKey? (t.maxKeyD fallback) = Option.some (t.maxKeyD fallback) := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_maxKeyD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_maxKeyD.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {fallback : α}, t.getKey? (t.maxKeyD fallback) = Option.some (t.maxKeyD fallback) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.contains_of_isEmpty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_of_isEmpty.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        t.contains a = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.minKey_eq_minKey!, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_eq_minKey!.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_unitOfList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_unitOfList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List α} {k : α},
        Std.DTreeMap.Const.get? (Std.DTreeMap.Const.unitOfList l cmp) k =
          if l.contains k = Bool.true then Option.some () else Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) (1)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_of_isEmpty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_of_isEmpty.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        t[a]? = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.minKey_le_minKey_erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_le_minKey_erase.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α}
        {he : (t.erase k).isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.minKey_le_minKey_erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_le_minKey_erase.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t.erase k).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.contains_minKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_minKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {km : α},
        t.minKey? = Option.some km → t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.DTreeMap.contains, Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.inner,
    Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.below, Std.DTreeMap.Internal.Impl.brecOn.go])) (by
  decide +kernel)

-- Std.DTreeMap.contains_minKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_minKey?.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_eq_none_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_eq_none_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α}, Std.DTreeMap.Const.get? t a = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_maxKey!, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_maxKey!.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α], t.maxKey! ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.DTreeMap.minKey?_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey?_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {km : α},
        t.minKey? = Option.some km → km ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.DTreeMap.instMembership, Std.DTreeMap.contains, Std.DTreeMap.Internal.Impl.contains,
    Std.DTreeMap.inner, Std.DTreeMap.Internal.Impl.brecOn])) (by
  decide +kernel)

-- Std.DTreeMap.minKey?_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey?_mem.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        km ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey_erase_eq_iff_not_compare_eq_maxKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_erase_eq_iff_not_compare_eq_maxKey.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α}
        {he : (t.erase k).isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.maxKey_erase_eq_iff_not_compare_eq_maxKey, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_erase_eq_iff_not_compare_eq_maxKey.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t.erase k).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.minKey?_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.minKey?_eq.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.minKey? = t₂.minKey? := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  (simp <;> decide))

-- Std.DTreeMap.maxKey_eq_iff_getKey?_eq_self_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_eq_iff_getKey?_eq_self_and_forall.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey!_minKey, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_minKey.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_eq_none, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_eq_none.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        t.getKey? a = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_minKeyD, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_minKeyD.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {fallback : α}, t.minKeyD fallback ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.size_inter_eq_size_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_inter_eq_size_right.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp},
        (∀ (a : α), a ∈ t₂ → a ∈ t₁) → (t₁ ∩ t₂).size = t₂.size := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.size_inter_eq_size_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_inter_eq_size_right.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₂).size = t₂.size := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.toArray_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.toArray_eq.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.toArray = t₂.toArray := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.Equiv.maxKey?_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.maxKey?_eq.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.maxKey? = t₂.maxKey? := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  simp)

-- Std.DTreeMap.Equiv.constToArray_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constToArray_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp], Std.DTreeMap.Const.toArray t₁ = Std.DTreeMap.Const.toArray t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.getKey_maxKey!_eq_maxKey, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_maxKey!_eq_maxKey.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.maxKey! ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.minKey?_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.minKey?_eq.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.minKey? = t₂.minKey? := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  simp)

-- Std.TreeMap.compare_getKey_self, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.compare_getKey_self.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.constToList_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.constToList_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp], Std.DTreeMap.Const.toList t₁ = Std.DTreeMap.Const.toList t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_minKey!, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_minKey!.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Inhabited α],
        t.isEmpty = Bool.false → t.getKey? t.minKey! = Option.some t.minKey! := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_minKey!, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_minKey!.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α], t.getKey? t.minKey! = Option.some t.minKey! := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.DTreeMap.Const.contains_unitOfList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.contains_unitOfList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List α} {k : α},
        (Std.DTreeMap.Const.unitOfList l cmp).contains k = l.contains k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) (1)) (by
  decide +kernel)

-- Std.TreeMap.mem_keys, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_keys.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t.keys ↔ k ∈ t := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_eq_get?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_eq_get?.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.DTreeMap.getKey?_eq_some_getKey, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_eq_some_getKey.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.contains_maxKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_maxKey?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {km : α},
        t.maxKey? = Option.some km → t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.TreeMap.contains, Std.DTreeMap.contains, Std.TreeMap.inner,
    Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.inner, Std.DTreeMap.Internal.Impl.brecOn])) (by
  decide +kernel)

-- Std.TreeMap.contains_maxKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_maxKey?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey_eq_get_getKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_eq_get_getKey?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {a : α} {h : a ∈ t}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey_eq_get_getKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_eq_get_getKey?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.size_inter_eq_size_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_inter_eq_size_left.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp},
        (∀ (a : α), a ∈ t₁ → a ∈ t₂) → (t₁ ∩ t₂).size = t₁.size := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (by
  decide)) (by
  decide +kernel)

-- Std.TreeMap.size_inter_eq_size_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_inter_eq_size_left.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₂).size = t₁.size := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.maxKey_erase_le_maxKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_erase_le_maxKey.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α}
        {he : (t.erase k).isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.maxKey_erase_le_maxKey, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_erase_le_maxKey.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t.erase k).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKeyD_maxKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKeyD_maxKey.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {fallback : α}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.isEmpty_eq_false_of_isEmpty_erase_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.isEmpty_eq_false_of_isEmpty_erase_eq_false.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.minKey_le_minKey_erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_le_minKey_erase.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {he : (t.erase k).isEmpty = Bool.false},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.minKey_le_minKey_erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_le_minKey_erase.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        (t.erase k).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey_eq_maxKey!, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_eq_maxKey!.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.size_diff_eq_size_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_diff_eq_size_left.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ \ t₂).size = t₁.size := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.minKey_le_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_le_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α}, k ∈ t → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.minKey_le_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_le_of_mem.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_eq_none_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_eq_none_of_contains_eq_false.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        t.getKey? a = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.mem_keysArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_keysArray.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        k ∈ t.keysArray ↔ k ∈ t := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_maxKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_maxKey?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {km : α},
        t.maxKey? = Option.some km → t.getKey? km = Option.some km := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.TreeMap.getKey?, Std.DTreeMap.getKey?, Std.TreeMap.inner, Std.DTreeMap.Internal.Impl.getKey?,
    Std.DTreeMap.inner, Std.DTreeMap.Internal.Impl.brecOn])) (by
  decide +kernel)

-- Std.TreeMap.getKey?_maxKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_maxKey?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.getKey? km = Option.some km := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.le_maxKey_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.le_maxKey_of_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α}, k ∈ t → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.le_maxKey_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.le_maxKey_of_mem.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_eq_get_get?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_eq_get_get?.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {a : α} {h : a ∈ t},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_eq_get_get?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_eq_get_get?.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.get_getKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.get_getKey?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {a : α} {h : (t.getKey? a).isSome = Bool.true},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.get_getKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.get_getKey?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        (t.getKey? a).isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.values_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.values_eq.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t₁.values = t₂.values := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.getKey_maxKey!, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_maxKey!.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.maxKey! ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_minKeyD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_minKeyD.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.getKey? (t.minKeyD fallback) = Option.some (t.minKeyD fallback) := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_minKeyD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_minKeyD.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.getKey? (t.minKeyD fallback) = Option.some (t.minKeyD fallback) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_eq_none_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_eq_none_of_contains_eq_false.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        t[a]? = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getD_emptyc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getD_emptyc.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {a : α} {fallback : β a},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (0)) (by
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

-- Std.DTreeMap.getKey_maxKeyD, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_maxKeyD.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {fallback : α}, t.maxKeyD fallback ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKeyD_minKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_minKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_eq_none, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_eq_none.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        t[a]? = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.values_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.values_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}
        [inst : Std.TransCmp cmp], t₁.values = t₂.values := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.isSome_get?_iff_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isSome_get?_iff_mem.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.TreeMap.getKeyD_maxKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKeyD_maxKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.isEmpty_inter_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.isEmpty_inter_right.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₂).isEmpty = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.get_getElem?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.get_getElem?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {a : α} {h : t[a]?.isSome = Bool.true},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.get_getElem?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.get_getElem?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        t[a]?.isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.le_maxKey_of_contains, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.le_maxKey_of_contains.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α}, t.contains k = Bool.true → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.le_maxKey_of_contains, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.le_maxKey_of_contains.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.keys_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.keys_eq.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.keys = t₂.keys := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.getKey_maxKey!_eq_maxKey, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_maxKey!_eq_maxKey.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α], t.maxKey! ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.DTreeMap.get?_erase_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get?_erase_self.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.TreeMap.le_minKey, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.le_minKey.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem_eq_get_getElem?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_eq_get_getElem?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {a : α} {h : a ∈ t}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem_eq_get_getElem?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_eq_get_getElem?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.get_getKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_getKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {a : α}
        {h : (t.getKey? a).isSome = Bool.true}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.get_getKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.get_getKey?.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        (t.getKey? a).isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_maxKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_maxKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {km : α},
        t.maxKey? = Option.some km → t.getKey? km = Option.some km := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.DTreeMap.getKey?, Std.DTreeMap.Internal.Impl.getKey?, Std.DTreeMap.inner,
    Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.below, Std.DTreeMap.Internal.Impl.brecOn.go])) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_maxKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_maxKey?.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.getKey? km = Option.some km := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.contains_maxKeyD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_maxKeyD.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.contains (t.maxKeyD fallback) = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.contains_maxKeyD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_maxKeyD.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {fallback : α}, t.contains (t.maxKeyD fallback) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_insertManyIfNewUnit_list_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_insertManyIfNewUnit_list_of_mem.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} [inst : Std.TransCmp cmp] {l : List α} {k : α},
        (t.insertManyIfNewUnit l).getKey? k = t.getKey? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ ([0]) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_maxKeyD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_maxKeyD.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.getKey? (t.maxKeyD fallback) = Option.some (t.maxKeyD fallback) := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_maxKeyD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_maxKeyD.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.getKey? (t.maxKeyD fallback) = Option.some (t.maxKeyD fallback) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_unitOfList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_unitOfList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] {l : List α} {k : α},
        (Std.TreeMap.unitOfList l cmp)[k]? = if l.contains k = Bool.true then Option.some () else Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) (1)) (by
  decide +kernel)

-- Std.DTreeMap.minKeyD_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKeyD_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.minKeyD fallback ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.minKeyD_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKeyD_mem.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {fallback : α}, t.minKeyD fallback ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.contains_minKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_minKey?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {km : α},
        t.minKey? = Option.some km → t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.TreeMap.contains, Std.DTreeMap.contains, Std.TreeMap.inner,
    Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.inner, Std.DTreeMap.Internal.Impl.brecOn])) (by
  decide +kernel)

-- Std.TreeMap.contains_minKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_minKey?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.toArray_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.toArray_eq.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp],
        t₁.toArray = t₂.toArray := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.maxKey_eq_maxKey!, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_eq_maxKey!.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.mem_of_mem_keysArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_keysArray.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α}, k ∈ t.keysArray → k ∈ t := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  decide +kernel)) (by
  decide +kernel)

-- Std.TreeMap.mem_of_mem_keysArray, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_of_mem_keysArray.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get!_eq_default_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_eq_default_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α] {a : α},
        t.get! a = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeSet.get_max, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_max.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.Equiv.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.trans.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeSet α cmp}, t₂.Equiv t₃ → t₁.Equiv t₃ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.trans.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeSet α cmp}, t₁.Equiv t₂ → t₁.Equiv t₃ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get!_of_isEmpty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_of_isEmpty.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α] {a : α},
        t.get! a = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeSet.getD_eq_fallback_of_contains_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_eq_fallback_of_contains_eq_false.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {a fallback : α},
        t.getD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.get?_eq_some_get!, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_eq_some_get!.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α] {a : α},
        t.get? a = Option.some (t.get! a) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.TreeSet.min!_eq_iff_get?_eq_self_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min!_eq_iff_get?_eq_self_and_forall.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α] {km : α},
        t.min! = km ↔ t.get? km = Option.some km ∧ ∀ (k : α), k ∈ t → (cmp km k).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  simp +ground +decide [Std.TreeSet.min!, Std.TreeSet.get?, Std.TreeSet.instMembership, Std.TreeMap.minKey!,
    Std.TreeSet.inner, Std.TreeMap.getKey?, Std.TreeSet.contains, Std.DTreeMap.minKey!, Std.TreeMap.inner,
    Std.DTreeMap.getKey?, Std.TreeMap.contains, Std.DTreeMap.Internal.Impl.minKey!, Std.DTreeMap.inner,
    Std.DTreeMap.Internal.Impl.getKey?, Std.DTreeMap.contains])

-- Std.DTreeMap.size_inter_eq_size_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_inter_eq_size_left.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp},
        (∀ (a : α), a ∈ t₁ → a ∈ t₂) → (t₁ ∩ t₂).size = t₁.size := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.size_inter_eq_size_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_inter_eq_size_left.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₂).size = t₁.size := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.get_erase, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_erase.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k a : α} {h' : a ∈ t.erase k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (1) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.get_erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_erase.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k a : α}, a ∈ t.erase k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_get?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_get?.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {a : α}
        {h : (Std.DTreeMap.Const.get? t a).isSome = Bool.true}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get_get?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_get?.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α}, (Std.DTreeMap.Const.get? t a).isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get?_diff_of_not_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_diff_of_not_mem_right.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ \ t₂).get? k = t₁.get? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get_filter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_filter.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {f : α → Bool} {k : α} {h : k ∈ Std.TreeSet.filter f t},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun n => n % 2 == 0 : Nat → Bool) (0) (by
  decide +kernel)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.get_filter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_filter.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {f : α → Bool} {k : α},
        k ∈ Std.TreeSet.filter f t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (fun n => n % 2 == 0 : Nat → Bool) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_eq_some_get, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_eq_some_get.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Std.TransCmp cmp]
        {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get?_eq_some_get!_of_contains, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_eq_some_get!_of_contains.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α] {a : α},
        t.get? a = Option.some (t.get! a) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.TreeSet.not_mem_diff_of_not_mem_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.not_mem_diff_of_not_mem_left.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, ¬k ∈ t₁ \ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.union_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.union_right.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp],
        (t₁ ∪ t₂).Equiv (t₁ ∪ t₃) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.getD_of_isEmpty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_of_isEmpty.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {a fallback : α},
        t.getD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.getD_min?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_min?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {km fallback : α},
        t.min? = Option.some km → t.getD km fallback = km := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (Bool.true) (by
  simp +ground +decide [Std.TreeSet.getD, Std.TreeMap.getKeyD, Std.TreeSet.inner, Std.DTreeMap.getKeyD, Std.TreeMap.inner,
    Std.DTreeMap.Internal.Impl.getKeyD, Std.DTreeMap.inner])) (by
  decide +kernel)

-- Std.TreeSet.getD_min?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_min?.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km fallback : α},
        t.getD km fallback = km := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.diff_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.diff_right.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp],
        (t₁ \ t₂).Equiv (t₁ \ t₃) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.Equiv.mem_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.mem_iff.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t₁ ↔ k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.contains_toArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_toArray.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : BEq α] [inst_1 : Std.TransCmp cmp] {k : α},
        t.toArray.contains k = t.contains k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) _ (1)) (by
  decide +kernel)

-- Std.DTreeMap.contains_maxKey?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_maxKey?.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {km : α},
        t.maxKey? = Option.some km → t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.DTreeMap.contains, Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.inner,
    Std.DTreeMap.Internal.Impl.brecOn, Std.DTreeMap.Internal.Impl.below, Std.DTreeMap.Internal.Impl.brecOn.go])) (by
  decide +kernel)

-- Std.DTreeMap.contains_maxKey?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_maxKey?.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.self_le_max?_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.self_le_max?_insert.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k kmi : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.self_le_max?_insert, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.self_le_max?_insert.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k kmi : α},
        (cmp k kmi).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (1) (0)) (by
  decide +kernel)

-- Std.TreeSet.get_union_of_mem_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_union_of_mem_right.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ : Std.TreeSet α cmp} {t₂ : Std.TreeSet α cmp} {k : α},
        k ∈ t₂ → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.get_union_of_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_union_of_mem_right.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ : Std.TreeSet α cmp} {t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp]
        {k : α}, k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.isEmpty_eq_false_of_isEmpty_erase_eq_false, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isEmpty_eq_false_of_isEmpty_erase_eq_false.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.insert.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] (k : α),
        (t₁.insert k).Equiv (t₂.insert k) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (1)) (by
  decide +kernel)

-- Std.TreeSet.mem_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_congr.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k k' : α}, k ∈ t ↔ k' ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.get?_inter_of_not_mem_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_inter_of_not_mem_left.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∩ t₂).get? k = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get?_diff_of_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_diff_of_mem_right.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ \ t₂).get? k = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.contains_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_congr.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k k' : α},
        t.contains k = t.contains k' := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.inter_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.inter_right.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₂).Equiv (t₁ ∩ t₃) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.Equiv.diff_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.diff_left.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp],
        (t₁ \ t₃).Equiv (t₂ \ t₃) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.Equiv.union_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.union_left.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp],
        (t₁ ∪ t₃).Equiv (t₂ ∪ t₃) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.contains_of_contains_erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_of_contains_erase.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {a : α},
        t.contains a = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.DTreeMap.minKey_le_of_contains, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_le_of_contains.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α},
        t.contains k = Bool.true → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.minKey_le_of_contains, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_le_of_contains.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {k : α},
        t.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.getD_max?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_max?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {km fallback : α},
        t.max? = Option.some km → t.getD km fallback = km := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (Bool.true) (by
  simp +ground +decide [Std.TreeSet.getD, Std.TreeMap.getKeyD, Std.TreeSet.inner, Std.DTreeMap.getKeyD, Std.TreeMap.inner,
    Std.DTreeMap.Internal.Impl.getKeyD, Std.DTreeMap.inner])) (by
  decide +kernel)

-- Std.TreeSet.getD_max?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_max?.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km fallback : α},
        t.getD km fallback = km := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.get?_union_of_not_mem_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_union_of_not_mem_left.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} {k : α}, ¬k ∈ t₁ → (t₁ ∪ t₂).get? k = t₂.get? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [2] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get?_union_of_not_mem_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_union_of_not_mem_left.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∪ t₂).get? k = t₂.get? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.maxD_eq_iff_get?_eq_self_and_forall, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.maxD_eq_iff_get?_eq_self_and_forall.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km fallback : α},
        t.maxD fallback = km ↔ t.get? km = Option.some km ∧ ∀ (k : α), k ∈ t → (cmp k km).isLE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  simp +ground +decide [Std.TreeSet.maxD, Std.TreeSet.get?, Std.TreeSet.instMembership, Std.TreeMap.maxKeyD,
    Std.TreeSet.inner, Std.TreeMap.getKey?, Std.TreeSet.contains, Std.DTreeMap.maxKeyD, Std.TreeMap.inner,
    Std.DTreeMap.getKey?, Std.TreeMap.contains, Std.DTreeMap.Internal.Impl.maxKeyD, Std.DTreeMap.inner,
    Std.DTreeMap.Internal.Impl.getKey?, Std.DTreeMap.contains])

-- Std.TreeSet.mem_of_get?_eq_some, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_get?_eq_some.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α} {k' : α}, k' ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (0)) (by
  decide +kernel)

-- Std.TreeSet.get!_eq_default, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_eq_default.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α] {a : α},
        t.get! a = Inhabited.default := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeSet.get!_max?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_max?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Inhabited α] {km : α},
        t.max? = Option.some km → t.get! km = km := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.true] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (Bool.true) (by
  simp +ground +decide [Std.TreeSet.get!, Std.TreeMap.getKey!, Std.TreeSet.inner, Std.DTreeMap.getKey!, Std.TreeMap.inner,
    Std.DTreeMap.Internal.Impl.getKey!, Std.DTreeMap.inner])) (by
  decide +kernel)

-- Std.TreeSet.get!_max?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_max?.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α] {km : α},
        t.get! km = km := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (1)) (by
  decide +kernel)

-- Std.TreeSet.mem_union_of_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_union_of_right.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t₁ ∪ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.get?_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.get?_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.get? k = t₂.get? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey!_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey!_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Inhabited α],
        t.isEmpty = Bool.false → t.maxKey! ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey!_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey!_mem.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α], t.maxKey! ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeSet.get_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_insert.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k a : α} {h₁ : a ∈ t.insert k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.get_insert, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_insert.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k a : α}, a ∈ t.insert k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.getD_eq_fallback, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_eq_fallback.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {a fallback : α},
        t.getD a fallback = fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.get?_inter_of_mem_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_inter_of_mem_right.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} {k : α}, k ∈ t₂ → (t₁ ∩ t₂).get? k = t₁.get? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get?_inter_of_mem_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_inter_of_mem_right.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        (t₁ ∩ t₂).get? k = t₁.get? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.getGE?_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.getGE?_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.getGE? k = t₂.getGE? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.getGT?_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.getGT?_eq.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        t₁.getGT? k = t₂.getGT? k := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [1] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.isEmpty_inter_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isEmpty_inter_left.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₂).isEmpty = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.minKey_eq_iff_getKey?_eq_self_and_forall, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_eq_iff_getKey?_eq_self_and_forall.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {km : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get_eq_get!, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_eq_get!.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α] {a : α},
        a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat) (0)) (by
  decide +kernel)

-- Std.DTreeMap.isSome_get?_eq_contains, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isSome_get?_eq_contains.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.TreeSet.Equiv.eraseMany_list, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.eraseMany_list.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] (l : List α),
        (t₁.eraseMany l).Equiv (t₂.eraseMany l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _ ([])) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_minKeyD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_minKeyD.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.getKey? (t.minKeyD fallback) = Option.some (t.minKeyD fallback) := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_minKeyD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_minKeyD.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        {fallback : α}, t.getKey? (t.minKeyD fallback) = Option.some (t.minKeyD fallback) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.mem_iff_isSome_get?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_iff_isSome_get?.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.DTreeMap.contains_maxKey!, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_maxKey!.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Inhabited α],
        t.isEmpty = Bool.false → t.contains t.maxKey! = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (by
  decide)) (by
  decide +kernel)

-- Std.DTreeMap.contains_maxKey!, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_maxKey!.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp]
        [inst : Inhabited α], t.contains t.maxKey! = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.DTreeMap.contains_eq_isSome_get?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_eq_isSome_get?.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp] {a : α},
        Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false)) (by
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

-- Std.DTreeMap.foldrM_eq_foldrM_keys, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.foldrM_eq_foldrM_keys.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {δ : Type} {m : Type → Type}
        [inst : Monad m] {f : α → δ → m δ} {init : δ},
        Std.DTreeMap.foldrM (fun (a : α) (x : β a) (d : δ) => f a d) init t = List.foldrM f init t.keys := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_maxKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_maxKey.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {he : t.isEmpty = Bool.false},
        t.getKey? (t.maxKey he) = Option.some (t.maxKey he) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) hc_k0) (by
  decide +kernel)

-- Std.TreeMap.getKey?_maxKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_maxKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.forIn_eq_forIn_keysArray, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.forIn_eq_forIn_keysArray.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {δ : Type} {m : Type → Type}
        [inst : Monad m] {f : α → δ → m (ForInStep δ)} {init : δ},
        (ForIn.forIn t init fun (a : (a : α) × β a) (d : δ) => f a.fst d) = ForIn.forIn t.keysArray init f := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a a_1 : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.TreeMap.minKey_eq_getElem_keysArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_eq_getElem_keysArray.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.minKey_eq_getElem_keysArray, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_eq_getElem_keysArray.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.maxKey_eq_getLast_keys, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_eq_getLast_keys.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.foldlM_eq_foldlM_toArray, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.foldlM_eq_foldlM_toArray.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : δ → α → β → m δ} {init : δ},
        Std.TreeMap.foldlM f init t = Array.foldlM (fun (a : δ) (b : α × β) => f a b.fst b.snd) init t.toArray := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 a_2 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeMap.size_ofList, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_ofList.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List (α × β)},
        (Std.TreeMap.ofList l cmp).size = l.length := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ ([(0, 0), (0, 1)])) (by
  decide +kernel)

-- Std.TreeMap.foldlM_eq_foldlM_toList, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.foldlM_eq_foldlM_toList.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : δ → α → β → m δ} {init : δ},
        Std.TreeMap.foldlM f init t = List.foldlM (fun (a : δ) (b : α × β) => f a b.fst b.snd) init t.toList := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 a_2 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeMap.foldrM_eq_foldrM_toList, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.foldrM_eq_foldrM_toList.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : α → β → δ → m δ} {init : δ},
        Std.TreeMap.foldrM f init t = List.foldrM (fun (a : α × β) (b : δ) => f a.fst a.snd b) init t.toList := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 a_2 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeMap.forIn_eq_forIn_keysArray, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.forIn_eq_forIn_keysArray.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : α → δ → m (ForInStep δ)} {init : δ},
        (ForIn.forIn t init fun (a : α × β) (d : δ) => f a.fst d) = ForIn.forIn t.keysArray init f := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a a_1 : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.DTreeMap.minKey_eq_getElem_keysArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_eq_getElem_keysArray.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {he : t.isEmpty = Bool.false},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.minKey_eq_getElem_keysArray, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_eq_getElem_keysArray.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.foldlM_eq_foldlM_keysArray, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.foldlM_eq_foldlM_keysArray.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : δ → α → m δ} {init : δ},
        Std.TreeMap.foldlM (fun (d : δ) (a : α) (x : β) => f d a) init t = Array.foldlM f init t.keysArray := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeMap.contains_maxKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_maxKey.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {he : t.isEmpty = Bool.false},
        t.contains (t.maxKey he) = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) hc_k0) (by
  decide +kernel)

-- Std.TreeMap.contains_maxKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_maxKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.maxKey_eq_getLast_keys, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_eq_getLast_keys.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Const.forInUncurried_eq_forIn_toList, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.forInUncurried_eq_forIn_toList.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {δ : Type} {m : Type → Type} {β : Type}
        {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Monad m] {f : α × β → δ → m (ForInStep δ)} {init : δ},
        Std.DTreeMap.Const.forInUncurried f init t = ForIn.forIn (Std.DTreeMap.Const.toList t) init f := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Option : Type → Type) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a : Nat × Nat) (a_1 : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.TreeMap.maxKey_eq_back_keysArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_eq_back_keysArray.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.maxKey_eq_back_keysArray, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_eq_back_keysArray.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.foldrM_eq_foldrM_keysArray, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.foldrM_eq_foldrM_keysArray.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {δ : Type} {m : Type → Type}
        [inst : Monad m] {f : α → δ → m δ} {init : δ},
        Std.DTreeMap.foldrM (fun (a : α) (x : β a) (d : δ) => f a d) init t = Array.foldrM f init t.keysArray := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeMap.foldrM_eq_foldrM_toArray, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.foldrM_eq_foldrM_toArray.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : α → β → δ → m δ} {init : δ},
        Std.TreeMap.foldrM f init t = Array.foldrM (fun (a : α × β) (b : δ) => f a.fst a.snd b) init t.toArray := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 a_2 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.DTreeMap.forIn_eq_forIn_toArray, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.forIn_eq_forIn_toArray.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {δ : Type} {m : Type → Type}
        [inst : Monad m] {f : (a : α) × β a → δ → m (ForInStep δ)} {init : δ},
        ForIn.forIn t init f = ForIn.forIn t.toArray init f := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a : (a : Nat) × (fun (a : Nat) => Nat) a) (a_1 : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.TreeMap.foldrM_eq_foldrM_keysArray, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.foldrM_eq_foldrM_keysArray.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : α → δ → m δ} {init : δ},
        Std.TreeMap.foldrM (fun (a : α) (x : β) (d : δ) => f a d) init t = Array.foldrM f init t.keysArray := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.DTreeMap.minKey_eq_head_keys, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_eq_head_keys.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.contains_minKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_minKey.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {he : t.isEmpty = Bool.false},
        t.contains (t.minKey he) = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) hc_k0) (by
  decide +kernel)

-- Std.TreeMap.contains_minKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.contains_minKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.forIn_eq_forIn_toList, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.forIn_eq_forIn_toList.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : α × β → δ → m (ForInStep δ)} {init : δ}, ForIn.forIn t init f = ForIn.forIn t.toList init f := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a : Nat × Nat) (a_1 : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.TreeMap.foldlM_eq_foldlM_keys, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.foldlM_eq_foldlM_keys.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : δ → α → m δ} {init : δ},
        Std.TreeMap.foldlM (fun (d : δ) (a : α) (x : β) => f d a) init t = List.foldlM f init t.keys := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeMap.maxKey?_of_isEmpty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey?_of_isEmpty.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.maxKey? = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [(0, 0), (0, 1)] fun (a b : Nat) => Ord.compare a b) _) (by
  simp)

-- Std.TreeSet.mem_toArray, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_toArray.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t.toArray ↔ k ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.min?_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.min?_eq.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t₁.min? = t₂.min? := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  simp)

-- Std.TreeSet.max_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_le.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.max_eq_iff_getKey?_eq_self_and_forall, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_eq_iff_getKey?_eq_self_and_forall.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.min_insert_le_min, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_insert_le_min.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α} {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.min_insert_le_min, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_insert_le_min.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get_get?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_get?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α} {h : (t.get? k).isSome = Bool.true},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.get_get?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_get?.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        (t.get? k).isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get?_eq_some_get, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_eq_some_get.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {a : α}, a ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get_minD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_minD.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.minD fallback ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.min_le_of_contains, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_le_of_contains.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α}, t.contains k = Bool.true → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.min_le_of_contains, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_le_of_contains.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        t.contains k = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get?_max?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_max?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {km : α},
        t.max? = Option.some km → t.get? km = Option.some km := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.TreeSet.get?, Std.TreeMap.getKey?, Std.TreeSet.inner, Std.DTreeMap.getKey?, Std.TreeMap.inner,
    Std.DTreeMap.Internal.Impl.getKey?, Std.DTreeMap.inner])) (by
  decide +kernel)

-- Std.TreeSet.get?_max?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_max?.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km : α},
        t.get? km = Option.some km := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get_max!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_max!.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.max! ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeSet.contains_min?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_min?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {km : α},
        t.min? = Option.some km → t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.TreeSet.contains, Std.TreeMap.contains, Std.TreeSet.inner, Std.DTreeMap.contains,
    Std.TreeMap.inner, Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.inner])) (by
  decide +kernel)

-- Std.TreeSet.contains_min?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_min?.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get?_max!, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_max!.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Inhabited α],
        t.isEmpty = Bool.false → t.get? t.max! = Option.some t.max! := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.get?_max!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_max!.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.get? t.max! = Option.some t.max! := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeSet.max_le_max_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_le_max_insert.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α} {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.max_le_max_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_le_max_insert.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.le_max_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.le_max_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α}, k ∈ t → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.le_max_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.le_max_of_mem.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.contains_max?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_max?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {km : α},
        t.max? = Option.some km → t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.TreeSet.contains, Std.TreeMap.contains, Std.TreeSet.inner, Std.DTreeMap.contains,
    Std.TreeMap.inner, Std.DTreeMap.Internal.Impl.contains, Std.DTreeMap.inner])) (by
  decide +kernel)

-- Std.TreeSet.contains_max?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_max?.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km : α},
        t.contains km = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.isEmpty_inter_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.isEmpty_inter_left.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp],
        (t₁ ∩ t₂).isEmpty = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.mem_of_mem_toArray, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_toArray.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α}, k ∈ t.toArray → k ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  decide +kernel)) (by
  decide +kernel)

-- Std.TreeSet.mem_of_mem_toArray, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_toArray.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.mem_toList, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_toList.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t.toList ↔ k ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.eq) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.true)) (by
  decide +kernel)

-- Std.TreeSet.min!_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min!_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Inhabited α], t.isEmpty = Bool.false → t.min! ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.min!_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min!_mem.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.min! ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.maxKey?_eq_some_maxKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey?_eq_some_maxKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.foldlM_eq_foldlM_keys, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.foldlM_eq_foldlM_keys.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {δ : Type} {m : Type → Type}
        [inst : Monad m] {f : δ → α → m δ} {init : δ},
        Std.DTreeMap.foldlM (fun (d : δ) (a : α) (x : β a) => f d a) init t = List.foldlM f init t.keys := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeMap.forIn_eq_forIn_keys, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.forIn_eq_forIn_keys.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : α → δ → m (ForInStep δ)} {init : δ},
        (ForIn.forIn t init fun (a : α × β) (d : δ) => f a.fst d) = ForIn.forIn t.keys init f := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a a_1 : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.TreeSet.get!_max, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_max.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeSet.get_max!_eq_max, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get_max!_eq_max.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.max! ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.maxKey_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {he : t.isEmpty = Bool.false}, t.maxKey he ∈ t := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) hc_k0) (by
  decide +kernel)

-- Std.TreeMap.maxKey_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_mem.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.contains_max!, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_max!.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Inhabited α],
        t.isEmpty = Bool.false → t.contains t.max! = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.contains_max!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_max!.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.contains t.max! = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.DTreeMap.forIn_eq_forIn_toList, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.forIn_eq_forIn_toList.h7 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {δ : Type} {m : Type → Type}
        [inst : Monad m] {f : (a : α) × β a → δ → m (ForInStep δ)} {init : δ},
        ForIn.forIn t init f = ForIn.forIn t.toList init f := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a : (a : Nat) × (fun (a : Nat) => Nat) a) (a_1 : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.TreeSet.getD_max, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_max.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey?_of_isEmpty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey?_of_isEmpty.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t.maxKey? = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  (simp <;> decide))

-- Std.TreeSet.mem_of_mem_toList, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_toList.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α}, k ∈ t.toList → k ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.mem_of_mem_toList, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_of_mem_toList.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.max_erase_eq_iff_not_compare_eq_max, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_erase_eq_iff_not_compare_eq_max.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α} {he : (t.erase k).isEmpty = Bool.false},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.max_erase_eq_iff_not_compare_eq_max, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_erase_eq_iff_not_compare_eq_max.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α},
        (t.erase k).isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.get?_minD, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_minD.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.get? (t.minD fallback) = Option.some (t.minD fallback) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.TreeSet.get?_minD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_minD.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.get? (t.minD fallback) = Option.some (t.minD fallback) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.min_le_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_le_of_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α}, k ∈ t → Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.min_le_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_le_of_mem.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.contains_maxD, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_maxD.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.contains (t.maxD fallback) = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.TreeSet.contains_maxD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_maxD.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.contains (t.maxD fallback) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.size_inter_eq_size_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.size_inter_eq_size_right.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp},
        (∀ (a : α), a ∈ t₂ → a ∈ t₁) → (t₁ ∩ t₂).size = t₂.size := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.size_inter_eq_size_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.size_inter_eq_size_right.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], (t₁ ∩ t₂).size = t₂.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.Equiv.beq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.beq.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {m₁ m₂ : Std.TreeSet α cmp}, m₁.Equiv m₂ → (m₁ == m₂) = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (by
  rfl)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.beq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.beq.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {m₁ m₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], (m₁ == m₂) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.get?_min?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_min?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {km : α},
        t.min? = Option.some km → t.get? km = Option.some km := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (by
  simp +ground +decide [Std.TreeSet.get?, Std.TreeMap.getKey?, Std.TreeSet.inner, Std.DTreeMap.getKey?, Std.TreeMap.inner,
    Std.DTreeMap.Internal.Impl.getKey?, Std.DTreeMap.inner])) (by
  decide +kernel)

-- Std.TreeSet.get?_min?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_min?.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {km : α},
        t.get? km = Option.some km := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.maxKey_eq_back_keysArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_eq_back_keysArray.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {he : t.isEmpty = Bool.false},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.maxKey_eq_back_keysArray, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_eq_back_keysArray.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.get?_maxD, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_maxD.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp},
        t.isEmpty = Bool.false → ∀ {fallback : α}, t.get? (t.maxD fallback) = Option.some (t.maxD fallback) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Std.TreeSet.get?_maxD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_maxD.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.get? (t.maxD fallback) = Option.some (t.maxD fallback) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.contains_min!, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_min!.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Inhabited α],
        t.isEmpty = Bool.false → t.contains t.min! = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (by
  decide)) (by
  decide +kernel)

-- Std.TreeSet.contains_min!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_min!.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.contains t.min! = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeSet.getD_min, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_min.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {fallback : α},
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.compare_get_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.compare_get_self.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, k ∈ t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.foldrM_eq_foldrM_toArray, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.foldrM_eq_foldrM_toArray.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {δ : Type} {m : Type → Type} {β : Type}
        {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Monad m] {f : α → β → δ → m δ} {init : δ},
        Std.DTreeMap.foldrM f init t =
          Array.foldrM (fun (a : α × β) (b : δ) => f a.fst a.snd b) init (Std.DTreeMap.Const.toArray t) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (fun α => Nat × α : Type → Type) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 a_2 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeSet.isEmpty_eq_false_of_isEmpty_erase_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.isEmpty_eq_false_of_isEmpty_erase_eq_false.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] {k : α}, t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (0)) (by
  decide +kernel)

-- Std.TreeSet.size_diff_eq_size_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.size_diff_eq_size_left.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], (t₁ \ t₂).size = t₁.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.min_eq_min!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_eq_min!.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp] [inst : Inhabited α],
        t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _ (instInhabitedNat)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_minKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_minKey.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {he : t.isEmpty = Bool.false},
        t.getKey? (t.minKey he) = Option.some (t.minKey he) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) hc_k0) (by
  decide +kernel)

-- Std.TreeMap.getKey?_minKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_minKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.minKey?_of_isEmpty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey?_of_isEmpty.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Std.TransCmp cmp],
        t.minKey? = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) _) (by
  (simp <;> decide))

-- Std.DTreeMap.Const.getKey!_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_filterMap.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Inhabited α]
        {f : α → β → Option γ} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (fun (a x : Nat) => Option.none) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getD_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_filterMap.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Option γ} {k : α} {fallback : γ},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun (a x : Nat) => Option.none) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey!_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_filterMap.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Inhabited α] {f : α → β → Option γ}
        {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (fun (a x : Nat) => Option.none) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.getKeyD_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_filterMap.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Option γ}
        {k fallback : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun (a x : Nat) => Option.none) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.foldlM_eq_foldlM_toList, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.foldlM_eq_foldlM_toList.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : δ → α → m δ} {init : δ}, Std.TreeSet.foldlM f init t = List.foldlM f init t.toList := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeSet.foldrM_eq_foldrM_toList, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.foldrM_eq_foldrM_toList.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : α → δ → m δ} {init : δ}, Std.TreeSet.foldrM f init t = List.foldrM f init t.toList := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.TreeSet.foldrM_eq_foldrM_toArray, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.foldrM_eq_foldrM_toArray.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : α → δ → m δ} {init : δ}, Std.TreeSet.foldrM f init t = Array.foldrM f init t.toArray := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b) (Nat) (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get!_map', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get!_map'.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Inhabited γ]
        {f : α → β → γ} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.forIn_eq_forIn_toArray, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.forIn_eq_forIn_toArray.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {δ : Type} {m : Type → Type} [inst : Monad m]
        {f : α → δ → m (ForInStep δ)} {init : δ}, ForIn.forIn t init f = ForIn.forIn t.toArray init f := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Nat) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a a_1 : Nat) => Option.none) (0)) (by
  decide +kernel)

-- Std.TreeSet.max_eq_getLast_toList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_eq_getLast_toList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.getElem!_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem!_insert_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Inhabited β] {k : α} {v : β},
        (t.insert k v)[k]! = v := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedNat) (Bool.false) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.compare_minKeyD_modify_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.compare_minKeyD_modify_eq.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {f : β → β}
        {fallback : α}, cmp ((Std.DTreeMap.Const.modify t k f).minKeyD fallback) (t.minKeyD fallback) = Ordering.eq := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (fun n => n + 1 : Nat → Nat) (Bool.false)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_filterMap.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Option γ} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun (a x : Nat) => Option.none) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.ordCompare_maxKey!_modify_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.ordCompare_maxKey!_modify_eq.h3 : Not
      (∀ {α β : Type} [inst : Ord α] {t : Std.TreeMap α β (@Ord.compare α inst)} [inst_1 : Inhabited α] {k : α} {f : β → β},
        @Eq Ordering
          (@Ord.compare α inst
            (@Std.TreeMap.maxKey! α β (@Ord.compare α inst) inst_1 (@Std.TreeMap.modify α β (@Ord.compare α inst) t k f))
            (@Std.TreeMap.maxKey! α β (@Ord.compare α inst) inst_1 t))
          Ordering.eq) := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => .lt⟩ : Ord Bool) (@Std.TreeMap.ofList Bool Nat (@List.nil (Prod Bool Nat))
      (@Ord.compare Bool (@Ord.mk Bool fun (x x_1 : Bool) => Ordering.lt))) (instInhabitedBool) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey!_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_filter.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Inhabited α]
        {f : α → β → Bool} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (fun a b => a < b : Nat → Nat → Bool) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get?_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_filterMap.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Option γ}
        {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun (a x : Nat) => Option.none) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get?_map', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_map'.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → γ} {k : α},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.max?_of_isEmpty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max?_of_isEmpty.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.max? = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => Ord.compare a b) _) (by
  simp)

-- Std.TreeSet.contains_max, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_max.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {he : t.isEmpty = Bool.false},
        t.contains (t.max he) = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) hc_k0) (by
  decide +kernel)

-- Std.TreeSet.contains_max, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_max.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey?_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_filterMap.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Option γ}
        {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun (a x : Nat) => Option.none) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.min?_of_isEmpty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min?_of_isEmpty.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.min? = Option.none := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => Ord.compare a b) _) (by
  simp)

-- Std.TreeSet.get?_max, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_max.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {he : t.isEmpty = Bool.false},
        t.get? (t.max he) = Option.some (t.max he) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) hc_k0) (by
  decide +kernel)

-- Std.TreeSet.get?_max, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_max.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.compare_maxKeyD_modify_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.compare_maxKeyD_modify_eq.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {f : β → β} {fallback : α},
        cmp ((t.modify k f).maxKeyD fallback) (t.maxKeyD fallback) = Ordering.eq := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (fun n => n + 1 : Nat → Nat) (Bool.false)) (by
  decide +kernel)

-- Std.TreeMap.getD_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_alter_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {fallback : β} {f : Option β → Option β},
        (t.alter k f).getD k fallback = (f t[k]?).getD fallback := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0) (fun (a : Option Nat) => Option.some 1)) (by
  decide +kernel)

-- Std.TreeMap.ordCompare_minKeyD_modify_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.ordCompare_minKeyD_modify_eq.h3 : Not
      (∀ {α β : Type} [inst : Ord α] {t : Std.TreeMap α β (@Ord.compare α inst)} {k : α} {f : β → β} {fallback : α},
        @Eq Ordering
          (@Ord.compare α inst
            (@Std.TreeMap.minKeyD α β (@Ord.compare α inst) (@Std.TreeMap.modify α β (@Ord.compare α inst) t k f) fallback)
            (@Std.TreeMap.minKeyD α β (@Ord.compare α inst) t fallback))
          Ordering.eq) := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => .lt⟩ : Ord Bool) (@Std.TreeMap.ofList Bool Nat (@List.nil (Prod Bool Nat))
      (@Ord.compare Bool (@Ord.mk Bool fun (x x_1 : Bool) => Ordering.lt))) (Bool.false) (fun n => n + 1 : Nat → Nat) (Bool.false)) (by
  decide +kernel)

-- Std.TreeMap.compare_maxKey!_modify_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.compare_maxKey!_modify_eq.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Inhabited α] {k : α} {f : β → β},
        cmp (t.modify k f).maxKey! t.maxKey! = Ordering.eq := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.getD_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_filter.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Bool} {k : α} {fallback : β},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a < b : Nat → Nat → Bool) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem!_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem!_alter_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} [inst : Inhabited β]
        {f : Option β → Option β}, (t.alter k f)[k]! = (f t[k]?).get! := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (instInhabitedNat) (fun (a : Option Nat) => Option.some 1)) (by
  decide +kernel)

-- Std.TreeSet.get?_min, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_min.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {he : t.isEmpty = Bool.false},
        t.get? (t.min he) = Option.some (t.min he) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) hc_k0) (by
  decide +kernel)

-- Std.TreeSet.get?_min, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_min.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_filterMap.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Option γ}
        {k : α},
        k ∈ Std.DTreeMap.filterMap f t ↔ ∃ (h : k ∈ t), (f (t.getKey k h) (Std.DTreeMap.Const.get t k h)).isSome = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (fun (a : Nat) => Option.some) (0)) (by
  decide +kernel)

-- Std.TreeSet.max_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {he : t.isEmpty = Bool.false}, t.max he ∈ t := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) hc_k0) (by
  decide +kernel)

-- Std.TreeSet.max_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_mem.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.min_eq_get_min?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_eq_get_min?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.min_eq_get_min?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_eq_get_min?.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_insert_self.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {fallback v : β},
        Std.DTreeMap.Const.getD (t.insert k v) k fallback = v := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0) (1)) (by
  decide +kernel)

-- Std.TreeSet.min_eq_getElem_toArray, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_eq_getElem_toArray.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.min_eq_getElem_toArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_eq_getElem_toArray.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeSet.size_ofList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.size_ofList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {l : List α},
        (Std.TreeSet.ofList l cmp).size = l.length := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (@Std.TransCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (@Std.OrientedCmp.mk (Bool) (fun (x x_1 : Bool) => Ordering.eq) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) ([Bool.false, Bool.true])) (by
  decide +kernel)

-- Std.TreeSet.min_eq_head_toList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_eq_head_toList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.TreeMap.getKey!_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey!_filter.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} [inst : Inhabited α] {f : α → β → Bool} {k : α},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (fun a b => a < b : Nat → Nat → Bool) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get?_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_insert.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {a k : α} {v : β},
        Std.DTreeMap.Const.get? (t.insert k v) a =
          if cmp k a = Ordering.eq then Option.some v else Std.DTreeMap.Const.get? t a := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (0) (2) (0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey!_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey!_insert_self.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} [inst : Inhabited α] {a : α} {b : β a},
        (t.insert a b).getKey! a = a := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (Bool.true) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getD_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getD_filter.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Bool} {k : α}
        {fallback : β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a < b : Nat → Nat → Bool) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.ordCompare_minKey!_modify_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.ordCompare_minKey!_modify_eq.h3 : Not
      (∀ {α β : Type} [inst : Ord α] {t : Std.DTreeMap α (fun (x : α) => β) (@Ord.compare α inst)} [inst_1 : Inhabited α]
        {k : α} {f : β → β},
        @Eq Ordering
          (@Ord.compare α inst
            (@Std.DTreeMap.minKey! α (fun (x : α) => β) (@Ord.compare α inst) inst_1
              (@Std.DTreeMap.Const.modify α (@Ord.compare α inst) β t k f))
            (@Std.DTreeMap.minKey! α (fun (x : α) => β) (@Ord.compare α inst) inst_1 t))
          Ordering.eq) := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => .lt⟩ : Ord Bool) (@Std.DTreeMap.ofList Bool (fun (x : Bool) => Nat) (@List.nil (@Sigma Bool fun (a : Bool) => Nat))
      (@Ord.compare Bool (@Ord.mk Bool fun (x x_1 : Bool) => Ordering.lt))) (instInhabitedBool) (Bool.false) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_map', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_map'.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → γ} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getD_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getD_insert_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {fallback v : β},
        (t.insert k v).getD k fallback = v := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKeyD_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKeyD_filter.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Bool}
        {k fallback : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a < b : Nat → Nat → Bool) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.getKey!_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey!_alter_self.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} [inst : Inhabited α]
        {k : α} {f : Option β → Option β},
        (Std.DTreeMap.Const.alter t k f).getKey! k =
          if (f (Std.DTreeMap.Const.get? t k)).isSome = Bool.true then k else Inhabited.default := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (instInhabitedBool) (Bool.true) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_filterMap.h5 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Option γ} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun (a x : Nat) => Option.none) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.Equiv.filterMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.filterMap.h6 : ¬∀ {α β γ : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} (f : α → β → Option γ),
        (Std.TreeMap.filterMap f t₁).Equiv (Std.TreeMap.filterMap f t₂) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (fun (a : Nat) => Option.some)) (by
  decide +kernel)

-- Std.TreeSet.max_eq_get_max?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_eq_get_max?.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {he : t.isEmpty = Bool.false}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.max_eq_get_max?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.max_eq_get_max?.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Std.TransCmp cmp], t.isEmpty = Bool.false := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) _) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {v : β},
        (k, v) ∈ Std.DTreeMap.Const.toList t ↔ t.getKey? k = Option.some k ∧ Std.DTreeMap.Const.get? t k = Option.some v := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0)) (by
  decide +kernel)

-- Std.TreeMap.self_le_maxKey_insertIfNew, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.self_le_maxKey_insertIfNew.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.mem_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_alter_self.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α}
        {f : Option β → Option β}, k ∈ Std.DTreeMap.Const.alter t k f ↔ (f (Std.DTreeMap.Const.get? t k)).isSome = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_filter.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Bool} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a < b : Nat → Nat → Bool) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.minKey_insertIfNew_le_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_insertIfNew_le_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Equiv.congr_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.congr_left.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.DTreeMap α β cmp}, t₁.Equiv t₃ ↔ t₂.Equiv t₃ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.DTreeMap.Const.size_filterMap_eq_size_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.size_filterMap_eq_size_iff.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β γ : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Option γ},
        (Std.DTreeMap.filterMap f t).size = t.size ↔
          ∀ (k : α) (h : k ∈ t), (f (t.getKey k h) (Std.DTreeMap.Const.get t k h)).isSome = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (fun (a : Bool) (x : Nat) => Option.none)) (by
  decide +kernel)

-- Std.DTreeMap.getKey_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey_insert_self.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.getKey?_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_inter.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} {k : α},
        (t₁ ∩ t₂).getKey? k = if k ∈ t₂ then t₁.getKey? k else Option.none := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.contains_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.contains_alter_self.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α}
        {f : Option β → Option β}, (Std.DTreeMap.Const.alter t k f).contains k = (f (Std.DTreeMap.Const.get? t k)).isSome := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.TreeSet.get!_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get!_insert.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} [inst : Inhabited α] {k a : α},
        (t.insert k).get! a = if cmp k a = Ordering.eq ∧ ¬k ∈ t then k else t.get! a := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [1, 0] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (instInhabitedNat) (2) (1)) (by
  decide +kernel)

-- Std.TreeSet.getD_filter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.getD_filter.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {f : α → Bool} {k fallback : α},
        (Std.TreeSet.filter f t).getD k fallback = (Option.filter f (t.get? k)).getD fallback := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun _ => true : Nat → Bool) (0) (1)) (by
  decide +kernel)

-- Std.DTreeMap.minKey_insertIfNew_le_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.minKey_insertIfNew_le_self.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.getKey?_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_alter_self.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α}
        {f : Option β → Option β},
        (Std.DTreeMap.Const.alter t k f).getKey? k =
          if (f (Std.DTreeMap.Const.get? t k)).isSome = Bool.true then Option.some k else Option.none := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.mem_toArray_iff_getKey?_eq_some_and_get?_eq_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_toArray_iff_getKey?_eq_some_and_get?_eq_some.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {v : β},
        (k, v) ∈ Std.DTreeMap.Const.toArray t ↔ t.getKey? k = Option.some k ∧ Std.DTreeMap.Const.get? t k = Option.some v := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_insert_self.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {v : β},
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.mem_filter_key, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_filter_key.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {f : α → Bool} {k : α},
        k ∈ Std.DTreeMap.filter (fun (a : α) (x : β a) => f a) t ↔ ∃ (h : k ∈ t), f (t.getKey k h) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (fun _ => true : Nat → Bool) (0)) (by
  decide +kernel)

-- Std.DTreeMap.mem_insertIfNew_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_insertIfNew_self.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k},
        k ∈ t.insertIfNew k v := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.getKey?_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.getKey?_filter.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Bool}
        {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a < b : Nat → Nat → Bool) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get?_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_filter.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Bool}
        {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a < b : Nat → Nat → Bool) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.mem_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.mem_filter.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Bool}
        {k : α}, k ∈ Std.DTreeMap.filter f t ↔ ∃ (h' : k ∈ t), f (t.getKey k h') (Std.DTreeMap.Const.get t k h') = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Bool) (Std.DTreeMap.ofList [(⟨0, Bool.false⟩ : (_ : Nat) × Bool), (⟨1, Bool.false⟩ : (_ : Nat) × Bool)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (fun (a : Nat) => Bool.not) (0)) (by
  decide +kernel)

-- Std.TreeMap.getKey?_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_alter_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {f : Option β → Option β},
        (t.alter k f).getKey? k = if (f t[k]?).isSome = Bool.true then Option.some k else Option.none := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get?_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_alter_self.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α}
        {f : Option β → Option β},
        Std.DTreeMap.Const.get? (Std.DTreeMap.Const.alter t k f) k = f (Std.DTreeMap.Const.get? t k) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.DTreeMap.getKey?_filter_key, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.getKey?_filter_key.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {f : α → Bool} {k : α},
        (Std.DTreeMap.filter (fun (k : α) (x : β k) => f k) t).getKey? k = Option.filter f (t.getKey? k) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (fun _ => true : Nat → Bool) (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem?_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_filter.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Bool} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a < b : Nat → Nat → Bool) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Const.get?_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get?_insert_self.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {k : α} {v : β},
        Std.DTreeMap.Const.get? (t.insert k v) k = Option.some v := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0)) (by
  decide +kernel)

-- Std.TreeMap.mem_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_alter_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {f : Option β → Option β},
        k ∈ t.alter k f ↔ (f t[k]?).isSome = Bool.true := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.filter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.filter.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp} (f : α → β → Bool),
        (Std.TreeMap.filter f t₁).Equiv (Std.TreeMap.filter f t₂) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (fun a b => a ≤ b : Nat → Nat → Bool)) (by
  decide +kernel)

-- Std.TreeMap.getElem_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_insert_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getKey?_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey?_insert_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β},
        (t.insert k v).getKey? k = Option.some k := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0)) (by
  decide +kernel)

-- Std.TreeMap.mem_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_insert_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, k ∈ t.insert k v := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0)) (by
  decide +kernel)

-- Std.TreeMap.maxKey_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.maxKey_insert.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.self_le_maxKey_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.self_le_maxKey_insert.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.self_le_maxKey_insertIfNew, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.self_le_maxKey_insertIfNew.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.minKey_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.minKey_insert.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.contains_insertIfNew_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.contains_insertIfNew_self.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k},
        (t.insertIfNew k v).contains k = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.congr_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.congr_right.h6 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.DTreeMap α β cmp}, t₃.Equiv t₁ ↔ t₃.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.TreeMap.getKey_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getKey_insert_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem?_insert_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_insert_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, (t.insert k v)[k]? = Option.some v := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0)) (by
  decide +kernel)

-- Std.TreeMap.self_le_maxKey_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.self_le_maxKey_insert.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.maxKey_insertIfNew, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.maxKey_insertIfNew.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {k : α} {v : β k}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.getElem?_alter_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_alter_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {f : Option β → Option β},
        (t.alter k f)[k]? = f t[k]? := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (fun (a : Option Nat) => Option.some 0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.congr_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.congr_right.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ t₃ : Std.TreeMap α β cmp}, t₃.Equiv t₁ ↔ t₃.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.DTreeMap.mem_inter_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.mem_inter_iff.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp} {k : α},
        k ∈ t₁ ∩ t₂ ↔ k ∈ t₁ ∧ k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat), (⟨1, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) =>
      if a = b then Ordering.eq else Ordering.lt) (0)) (by
  decide +kernel)

-- Std.TreeMap.mem_insertIfNew_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.mem_insertIfNew_self.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {k : α} {v : β}, k ∈ t.insertIfNew k v := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false) (0)) (by
  decide +kernel)

-- Std.DTreeMap.isEmpty_filter_key_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isEmpty_filter_key_iff.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {f : α → Bool},
        (Std.DTreeMap.filter (fun (a : α) (x : β a) => f a) t).isEmpty = Bool.true ↔
          ∀ (k : α) (h : k ∈ t), f (t.getKey k h) = Bool.false := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (not : Bool → Bool)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.of_toList_perm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.of_toList_perm.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.TreeMap.isEmpty_diff_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.isEmpty_diff_iff.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp},
        (t₁ \ t₂).isEmpty = Bool.true ↔ ∀ (k : α), k ∈ t₁ → k ∈ t₂ := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt) (Std.TreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.TreeSet.mem_filter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_filter.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {f : α → Bool} {k : α},
        k ∈ Std.TreeSet.filter f t ↔ ∃ (h : k ∈ t), f (t.get k h) = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun _ => true : Nat → Bool) (0)) (by
  decide +kernel)

-- Std.TreeSet.get?_filter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.get?_filter.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {f : α → Bool} {k : α},
        (Std.TreeSet.filter f t).get? k = Option.filter f (t.get? k) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun _ => true : Nat → Bool) (0)) (by
  decide +kernel)

-- Std.TreeSet.contains_union, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_union.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} {k : α},
        (t₁ ∪ t₂).contains k = (t₁.contains k || t₂.contains k) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeSet.ofList [2] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.isEmpty_filter_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.isEmpty_filter_iff.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Bool},
        (Std.DTreeMap.filter f t).isEmpty = Bool.true ↔
          ∀ (k : α) (h : k ∈ t), f (t.getKey k h) (Std.DTreeMap.Const.get t k h) = Bool.false := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (fun (a : Bool) (n : Nat) => n % 2 == 0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.of_toList_perm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.of_toList_perm.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.DTreeMap.isEmpty_diff_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isEmpty_diff_iff.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp},
        (t₁ \ t₂).isEmpty = Bool.true ↔ ∀ (k : α), k ∈ t₁ → k ∈ t₂ := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (Std.DTreeMap.ofList [] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.TreeSet.mem_inter_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.mem_inter_iff.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} {k : α}, k ∈ t₁ ∩ t₂ ↔ k ∈ t₁ ∧ k ∈ t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0)) (by
  decide +kernel)

-- Std.TreeSet.contains_inter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_inter.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp} {k : α},
        (t₁ ∩ t₂).contains k = (t₁.contains k && t₂.contains k) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (Std.TreeSet.ofList [0, 1] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0)) (by
  decide +kernel)

-- Std.TreeMap.getElem_insertManyIfNewUnit_list, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_insertManyIfNewUnit_list.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α Unit cmp} {l : List α} {k : α}, k ∈ t.insertManyIfNewUnit l := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) ([]) (0)) (by
  decide +kernel)

-- Std.DTreeMap.Const.isEmpty_filter_eq_false_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.isEmpty_filter_eq_false_iff.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t : Std.DTreeMap α (fun (x : α) => β) cmp} {f : α → β → Bool},
        (Std.DTreeMap.filter f t).isEmpty = Bool.false ↔
          ∃ (k : α), ∃ (h : k ∈ t), f (t.getKey k h) (Std.DTreeMap.Const.get t k h) = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Nat) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (fun (a : Bool) (n : Nat) => n % 2 == 0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.symm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.symm.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp}, t₂.Equiv t₁ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.TreeMap.keys_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.keys_filter.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Bool}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (fun a b => a < b : Nat → Nat → Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.DTreeMap.Equiv.size_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.size_eq.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.DTreeMap α β cmp}, t₁.size = t₂.size := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.DTreeMap.instPureForInSigmaOfLawfulMonad, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.instPureForInSigmaOfLawfulMonad.h5 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {m : Type → Type} [inst : Monad m],
        Std.Internal.PureForIn m (Std.DTreeMap α β cmp) ((a : α) × β a) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option)) (by
  exact fun hc_c =>
    absurd
      (hc_c.forIn_eq (β := (Nat : Type))
        (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b :
          Std.DTreeMap Nat (fun (a : Nat) => Nat) fun (a b : Nat) => Ord.compare a b)
        (0 : Nat)
        (fun (a : (a : Nat) × (fun (a : Nat) => Nat) a) (a_1 : Nat) => Option.none :
          (a : Nat) × (fun (a : Nat) => Nat) a → Nat → Option (ForInStep Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeMap.size_filter_eq_size_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.size_filter_eq_size_iff.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} {f : α → β → Bool},
        (Std.TreeMap.filter f t).size = t.size ↔ ∀ (k : α) (h : k ∈ t), f (t.getKey k h) t[k] = Bool.true := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 1)] fun (x x_1 : Bool) => Ordering.lt) (fun (a : Bool) (n : Nat) => n % 2 == 0)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.of_toArray_perm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.of_toArray_perm.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.isEmpty_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.isEmpty_eq.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeMap α β cmp}, t₁.isEmpty = t₂.isEmpty := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.DTreeMap.Equiv.of_constToList_perm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Equiv.of_constToList_perm.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {t₁ t₂ : Std.DTreeMap α (fun (x : α) => β) cmp}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Std.DTreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.DTreeMap.ofList [(⟨0, 0⟩ : (_ : Nat) × Nat)] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.DTreeMap.size_filter_key_eq_size_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.size_filter_key_eq_size_iff.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp} {f : α → Bool},
        (Std.DTreeMap.filter (fun (k : α) (x : β k) => f k) t).size = t.size ↔
          ∀ (k : α) (h : k ∈ t), f (t.getKey k h) = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.true, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt) (not : Bool → Bool)) (by
  decide +kernel)

-- Std.TreeMap.Equiv.inner, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.Equiv.inner.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {m₁ m₂ : Std.TreeMap α β cmp}, m₁.inner.Equiv m₂.inner := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeMap.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeMap.ofList [(0, 0)] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.size_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.size_eq.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp}, t₁.size = t₂.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.TreeSet.isEmpty_diff_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.isEmpty_diff_iff.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp},
        (t₁ \ t₂).isEmpty = Bool.true ↔ ∀ (k : α), k ∈ t₁ → k ∈ t₂ := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (Std.TreeSet.ofList [] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.TreeMap.isEmpty_iff_forall_not_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.isEmpty_iff_forall_not_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp}, t.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ t := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.DTreeMap.isEmpty_iff_forall_contains, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isEmpty_iff_forall_contains.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp},
        t.isEmpty = Bool.true ↔ ∀ (a : α), t.contains a = Bool.false := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.of_toArray_perm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.of_toArray_perm.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp}, t₁.Equiv t₂ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.TreeMap.getElem_unitOfList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem_unitOfList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {l : List α} {k : α}, k ∈ Std.TreeMap.unitOfList l cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) ([]) (0)) (by
  decide +kernel)

-- Std.TreeSet.isEmpty_filter_eq_false_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.isEmpty_filter_eq_false_iff.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {f : α → Bool},
        (Std.TreeSet.filter f t).isEmpty = Bool.false ↔ ∃ (k : α), ∃ (h : k ∈ t), f (t.get k h) = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (not : Bool → Bool)) (by
  decide +kernel)

-- Std.TreeSet.min_insert_le_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.min_insert_le_self.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TreeSet.isEmpty_filter_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.isEmpty_filter_iff.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {f : α → Bool},
        (Std.TreeSet.filter f t).isEmpty = Bool.true ↔ ∀ (k : α) (h : k ∈ t), f (t.get k h) = Bool.false := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt) (not : Bool → Bool)) (by
  decide +kernel)

-- Std.TreeMap.isEmpty_eq_false_iff_exists_contains_eq_true, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.isEmpty_eq_false_iff_exists_contains_eq_true.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp},
        t.isEmpty = Bool.false ↔ ∃ (a : α), t.contains a = Bool.true := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.symm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.symm.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t₁ t₂ : Std.TreeSet α cmp}, t₂.Equiv t₁ := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.TreeSet.contains_insert_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.contains_insert_self.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp} {k : α}, (t.insert k).contains k = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [] fun (x x_1 : Bool) => Ordering.lt) (Bool.false)) (by
  decide +kernel)

-- Std.DTreeMap.Const.get_unitOfList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.Const.get_unitOfList.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {l : List α} {k : α}, k ∈ Std.DTreeMap.Const.unitOfList l cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) ([]) (0)) (by
  decide +kernel)

-- Std.TreeMap.isEmpty_eq_false_iff_exists_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.isEmpty_eq_false_iff_exists_mem.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp}, t.isEmpty = Bool.false ↔ ∃ (a : α), a ∈ t := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.DTreeMap.isEmpty_eq_false_iff_exists_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.DTreeMap.isEmpty_eq_false_iff_exists_mem.h4 : ¬∀ {α : Type} {β : α → Type} {cmp : α → α → Ordering} {t : Std.DTreeMap α β cmp},
        t.isEmpty = Bool.false ↔ ∃ (a : α), a ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.DTreeMap.ofList [(⟨Bool.false, 0⟩ : (_ : Bool) × Nat)] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.TreeSet.Equiv.inner, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.Equiv.inner.h4 : ¬∀ {α : Type} {cmp : α → α → Ordering} {m₁ m₂ : Std.TreeSet α cmp}, m₁.inner.Equiv m₂.inner := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Std.TreeSet.ofList [] fun (a b : Nat) => Ord.compare a b) (Std.TreeSet.ofList [0] fun (a b : Nat) => Ord.compare a b)) (by
  decide +kernel)

-- Std.TreeMap.isEmpty_iff_forall_contains, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.isEmpty_iff_forall_contains.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp},
        t.isEmpty = Bool.true ↔ ∀ (a : α), t.contains a = Bool.false := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeMap.ofList [(Bool.false, 0)] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.TreeSet.isEmpty_eq_false_iff_exists_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.isEmpty_eq_false_iff_exists_mem.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp}, t.isEmpty = Bool.false ↔ ∃ (a : α), a ∈ t := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

-- Std.TreeSet.isEmpty_eq_false_iff_exists_contains_eq_true, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeSet.isEmpty_eq_false_iff_exists_contains_eq_true.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} {t : Std.TreeSet α cmp},
        t.isEmpty = Bool.false ↔ ∃ (a : α), t.contains a = Bool.true := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Std.TreeSet.ofList [Bool.false] fun (x x_1 : Bool) => Ordering.lt)) (by
  decide +kernel)

