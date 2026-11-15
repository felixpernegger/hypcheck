import Batteries
-- batteries port: Decidable instances for Batteries predicates (HypCheck `--dec-src`), so that the
-- counterexample search can evaluate them; elaborated after the imports and copied into proofs files.
noncomputable instance HypCheckDec.ltHeadKey {α β} (cmp : α → α → Ordering) (a : α)
    (t : Batteries.AssocList α β) : Decidable (Batteries.AssocList.LTHeadKey cmp a t) :=
  match t with
  | .nil => isTrue trivial
  | .cons x _ _ => (inferInstance : Decidable (cmp a x = .lt))
noncomputable instance HypCheckDec.keysOrdered {α β} (cmp : α → α → Ordering) (t : Batteries.AssocList α β) :
    Decidable (Batteries.AssocList.KeysOrdered cmp t) :=
  Batteries.AssocList.rec (motive := fun t => Decidable (Batteries.AssocList.KeysOrdered cmp t))
    (isTrue trivial)
    (fun a _ t ih => @instDecidableAnd (Batteries.AssocList.LTHeadKey cmp a t) _ inferInstance ih) t
noncomputable instance HypCheckDec.olLTHeadKey {α β} (cmp : α → α → Ordering) (a : α)
    (l : Batteries.OrderedAssocList cmp β) : Decidable (l.LTHeadKey a) :=
  HypCheckDec.ltHeadKey cmp a l.toAssocList
noncomputable instance HypCheckDec.iterValidFor (l r : List Char) (it : String.Legacy.Iterator) :
    Decidable (String.Legacy.Iterator.ValidFor l r it) :=
  decidable_of_iff (it.s = String.ofList (l.reverseAux r) ∧ it.i = ⟨String.utf8Len l⟩)
    ⟨fun ⟨h1, h2⟩ => by cases it; cases h1; cases h2; exact .mk, fun h => by cases h; exact ⟨rfl, rfl⟩⟩
noncomputable instance HypCheckDec.substrValidFor (l m r : List Char) (s : Substring.Raw) :
    Decidable (Substring.Raw.ValidFor l m r s) :=
  decidable_of_iff (s.str = String.ofList (l ++ m ++ r) ∧ s.startPos = ⟨String.utf8Len l⟩ ∧
      s.stopPos = ⟨String.utf8Len l + String.utf8Len m⟩)
    ⟨fun ⟨h1, h2, h3⟩ => by cases s; cases h1; cases h2; cases h3; exact .mk,
     fun h => by cases h; exact ⟨rfl, rfl, rfl⟩⟩
noncomputable instance HypCheckDec.binHeapWF {α} [Ord α] (h : Batteries.BinaryHeap α) :
    Decidable h.WF :=
  inferInstanceAs (Decidable (∀ i : Fin h.size, (∀ _ : 2 * i.val + 1 < h.size,
    (compare h.vector[i] h.vector[2 * i.val + 1]).isGE) ∧ (∀ _ : 2 * i.val + 1 + 1 < h.size,
    (compare h.vector[i] h.vector[2 * i.val + 1 + 1]).isGE)))
noncomputable instance HypCheckDec.pairingNoSibling {α} (s : Batteries.PairingHeapImp.Heap α) :
    Decidable s.NoSibling :=
  match s with
  | .nil => isTrue .nil
  | .node a c .nil => isTrue (.node a c)
  | .node _ _ (.node _ _ _) => isFalse (fun h => by cases h)


/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Batteries.OrderedAssocList.merge_mk_cons_mk_nil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_mk_cons_mk_nil.h2 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.TransCmp α cmp] {β γ δ : Type} {x : α} {y : β}
        {t : Batteries.AssocList α β} {h : @Batteries.AssocList.KeysOrdered α β cmp (@Batteries.AssocList.cons α β x y t)}
        {h' : @Batteries.AssocList.KeysOrdered α γ cmp (@Batteries.AssocList.nil α γ)}
        {f : α → Option β → Option γ → Option δ}, @Std.LawfulEqCmp α cmp) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (Nat) (Bool.false) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Bool Nat) (by
  decide) (by
  decide) (fun (a : Bool) (a_1 a_2 : Option Nat) => @Option.none Nat)) (by
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

-- Batteries.OrderedAssocList.merge_mk_cons_mk_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_mk_cons_mk_nil.h3 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.LawfulEqCmp α cmp] {β γ δ : Type} {x : α} {y : β}
        {t : Batteries.AssocList α β} {h : @Batteries.AssocList.KeysOrdered α β cmp (@Batteries.AssocList.cons α β x y t)}
        {h' : @Batteries.AssocList.KeysOrdered α γ cmp (@Batteries.AssocList.nil α γ)}
        {f : α → Option β → Option γ → Option δ}, @Std.TransCmp α cmp) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat) (by
  decide) (by
  decide) (fun (a : Nat) (a_1 a_2 : Option Nat) => @Option.none Nat)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.merge_mk_cons_mk_nil, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_mk_cons_mk_nil.h10 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.LawfulEqCmp α cmp] [inst : @Std.TransCmp α cmp] {β γ δ : Type}
        {x : α} {y : β} {t : Batteries.AssocList α β}
        {h' : @Batteries.AssocList.KeysOrdered α γ cmp (@Batteries.AssocList.nil α γ)}
        {f : α → Option β → Option γ → Option δ},
        @Batteries.AssocList.KeysOrdered α β cmp (@Batteries.AssocList.cons α β x y t)) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Nat) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)) (by
  decide) (fun (a : Nat) (a_1 a_2 : Option Nat) => @Option.none Nat)) (by
  decide +kernel)

-- Batteries.AssocList.KeysOrdered.orderedMerge, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.orderedMerge.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {l₁ : Batteries.AssocList α β} {β_1 : Type}
        {l₂ : Batteries.AssocList α β_1} {α_1 : Type} {f : α → Option β → Option β_1 → Option α_1}
        [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp],
        Batteries.AssocList.KeysOrdered cmp l₂ →
          Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.orderedMerge cmp f l₁ l₂) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Batteries.AssocList.cons 0 0 (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (Nat) (Batteries.AssocList.nil) (Nat) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.some 0) _ _ (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.KeysOrdered.orderedMerge, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.orderedMerge.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {l₁ : Batteries.AssocList α β} {β_1 : Type}
        {l₂ : Batteries.AssocList α β_1} {α_1 : Type} {f : α → Option β → Option β_1 → Option α_1}
        [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp],
        Batteries.AssocList.KeysOrdered cmp l₁ →
          Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.orderedMerge cmp f l₁ l₂) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Batteries.AssocList.nil) (Nat) (Batteries.AssocList.cons 0 0 (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (Nat) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.some 0) _ _ (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.find?_eq_none_of_ltHeadKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.find?_eq_none_of_ltHeadKey.h5 : ¬∀ {α : Type} {a : α} {β : Type} {l : Batteries.AssocList α β} {cmp : α → α → Ordering} [inst : BEq α]
        [inst_1 : LawfulBEq α],
        Batteries.AssocList.LTHeadKey cmp a l →
          Batteries.AssocList.KeysOrdered cmp l → Batteries.AssocList.find? a l = Option.none := fun hc_h => absurd (@hc_h (Bool) (Bool.false) (Nat) (Batteries.AssocList.cons Bool.false 0 Batteries.AssocList.nil) (fun _ _ => .lt : Bool → Bool → Ordering) (instBEqOfDecidableEq) _ (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.find?_eq_none_of_ltHeadKey, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.find?_eq_none_of_ltHeadKey.h7 : ¬∀ {α : Type} {a : α} {β : Type} {l : Batteries.AssocList α β} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp]
        [inst : BEq α],
        Batteries.AssocList.LTHeadKey cmp a l →
          Batteries.AssocList.KeysOrdered cmp l → Batteries.AssocList.find? a l = Option.none := fun hc_h => absurd (@hc_h (Nat) (0) (Nat) (Batteries.AssocList.cons 1 0 Batteries.AssocList.nil) (fun a b => compare a b : Nat → Nat → Ordering) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.find?_eq_none_of_ltHeadKey, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.find?_eq_none_of_ltHeadKey.h8 : ¬∀ {α : Type} {a : α} {β : Type} {l : Batteries.AssocList α β} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst_1 : LawfulBEq α],
        Batteries.AssocList.KeysOrdered cmp l → Batteries.AssocList.find? a l = Option.none := fun hc_h => absurd (@hc_h (Nat) (0) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (fun a b => compare a b : Nat → Nat → Ordering) _ (instBEqOfDecidableEq) _ (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.find?_eq_none_of_ltHeadKey, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.find?_eq_none_of_ltHeadKey.h9 : ¬∀ {α : Type} {a : α} {β : Type} {l : Batteries.AssocList α β} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp]
        [inst : BEq α] [inst_1 : LawfulBEq α],
        Batteries.AssocList.LTHeadKey cmp a l → Batteries.AssocList.find? a l = Option.none := fun hc_h => absurd (@hc_h (Nat) (0) (Bool) (Batteries.AssocList.cons 1 Bool.false (Batteries.AssocList.cons 0 Bool.false Batteries.AssocList.nil)) (fun a b => compare a b : Nat → Nat → Ordering) _ (instBEqOfDecidableEq) _ (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_eq_find?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_eq_find?.h3 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] [inst_1 : LawfulBEq α]
        (l : Batteries.AssocList α β),
        Batteries.AssocList.KeysOrdered cmp l →
          ∀ (x : α), Batteries.AssocList.orderedFind? cmp l x = Batteries.AssocList.find? x l := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) _ (instBEqOfDecidableEq) _ (Batteries.AssocList.cons Bool.false 0 Batteries.AssocList.nil) (by
  decide) (Bool.true)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_eq_find?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_eq_find?.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : BEq α] [inst_1 : LawfulBEq α]
        (l : Batteries.AssocList α β),
        Batteries.AssocList.KeysOrdered cmp l →
          ∀ (x : α), Batteries.AssocList.orderedFind? cmp l x = Batteries.AssocList.find? x l := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (instBEqOfDecidableEq) _ (Batteries.AssocList.cons 1 Bool.false (Batteries.AssocList.cons 0 Bool.false Batteries.AssocList.nil)) (by
  decide) (0)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_eq_find?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_eq_find?.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp] [inst : BEq α]
        (l : Batteries.AssocList α β),
        Batteries.AssocList.KeysOrdered cmp l →
          ∀ (x : α), Batteries.AssocList.orderedFind? cmp l x = Batteries.AssocList.find? x l := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (by
  decide) (1)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_eq_find?, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_eq_find?.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : LawfulBEq α] (l : Batteries.AssocList α β) (x : α),
        Batteries.AssocList.orderedFind? cmp l x = Batteries.AssocList.find? x l := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (instBEqOfDecidableEq) _ (Batteries.AssocList.cons 1 Bool.false (Batteries.AssocList.cons 0 Bool.false Batteries.AssocList.nil)) (0)) (by
  decide +kernel)

-- Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 5: necessary
/- FAILED: 6:2: failed to synthesize
  Decidable (∀ {x y z : Bool}, x < y → y < z → x < z)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 8:2: failed to synthesize
  Decidable (∀ {x y z : Bool}, x < y → y < z → x < z)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 6:2: failed to synthesize
  Decidable (∀ {x y z : Bool}, x < y → y < z → x < z)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 8:2: failed to synthesize
  Decidable (∀ {x y z : Bool}, x < y → y < z → x < z)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 8:11: `dsimp` made no progress | 26:486: don't know how to synthesize implicit argument `y`
  @h5.prem1 (?m.17 hc_h) (?m.18 hc_h)
context:
hc_h :
  ∀ {α : Type} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : DecidableEq α] [inst_3 : LE α],
    (∀ {x y z : α}, x < y → y < z → x < z) →
      (∀ {x y : α}, ¬x < y ↔ y ≤ x) →
        (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → Std.LawfulLECmp fun x1 x2 => compareOfLessAndEq x1 x2
x✝ y✝ : Bool
⊢ Bool | 8:11: `dsimp` made no progress | 26:486: don't know how to synthesize implicit argument `y`
  @h5.prem1 (?m.17 hc_h) (?m.18 hc_h)
context:
hc_h :
  ∀ {α : Type} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : DecidableEq α] [inst_3 : LE α],
    (∀ {x y z : α}, x < y → y < z → x < z) →
      (∀ {x y : α}, ¬x < y ↔ y ≤ x) →
        (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → Std.LawfulLECmp fun x1 x2 => compareOfLessAndEq x1 x2
x✝ y✝ : Bool
⊢ Bool
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5 : ¬∀ {α : Type} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : DecidableEq α] [inst_3 : LE α],
        (∀ {x y z : α}, x < y → y < z → x < z) →
          (∀ {x y : α}, ¬x < y ↔ y ≤ x) →
            (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → Std.LawfulLECmp fun (x1 x2 : α) => compareOfLessAndEq x1 x2 := fun hc_h => absurd (@hc_h (Bool) (⟨fun _ _ => True⟩ : LT Bool) (fun (a b : Bool) => instDecidableTrue) (instDecidableEqBool) (⟨fun _ _ => False⟩ : LE Bool) (by
  decide) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))
-/

-- Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.inst : Not
      (@Std.LawfulLECmp Bool (@LE.mk Bool fun (a b : Bool) => @Eq Bool a b) fun (x1 x2 : Bool) =>
        @compareOfLessAndEq Bool x1 x2 (@LT.mk Bool fun (a b : Bool) => @Ne Bool a b)
          ((fun (a b : Bool) => @instDecidableNot (@Eq Bool a b) (instDecidableEqBool a b)) x1 x2) instDecidableEqBool) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.true : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem0 : ∀ (x : Bool), Not (@Ne Bool x x) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem1 : ∀ {x y : Bool}, Iff (Not (@Ne Bool x y)) (@Eq Bool y x) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem2 : ∀ {x y : Bool}, @Eq Bool x y → @Eq Bool y x → @Eq Bool x y := by
  decide
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α] [inst_3 : LE α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y : α}, Iff (Not (@LT.lt α inst x y)) (@LE.le α inst_3 y x)) →
            (∀ {x y : α}, @LE.le α inst_3 x y → @LE.le α inst_3 y x → @Eq α x y) →
              @Std.LawfulLECmp α inst_3 fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.inst (@hc_h (Bool) (@LT.mk Bool fun (a b : Bool) => @Ne Bool a b) (fun (a b : Bool) => @instDecidableNot (@Eq Bool a b) (instDecidableEqBool a b)) (instDecidableEqBool) (@LE.mk Bool fun (a b : Bool) => @Eq Bool a b) HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem0 HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem1 HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem2)

-- Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.inst : Not
      (@Std.LawfulLECmp Nat (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2 instLTNat (x1.decLt x2) instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.isLE_iff_le (x := (0 : Nat)) (y := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem0 : ∀ (x : Nat), Not (@LT.lt Nat instLTNat x x) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem1 : ∀ {x y z : Nat}, @LT.lt Nat instLTNat x y → @LT.lt Nat instLTNat y z → @LT.lt Nat instLTNat x z := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem2 : ∀ {x y : Nat}, @LE.le Nat instLENat y x → @LE.le Nat instLENat x y → @Eq Nat x y := by
  omega
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α] [inst_3 : LE α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            (∀ {x y : α}, @LE.le α inst_3 x y → @LE.le α inst_3 y x → @Eq α x y) →
              @Std.LawfulLECmp α inst_3 fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.inst (@hc_h (Nat) (instLTNat) (Nat.decLt) (instDecidableEqNat) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem0 HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem1 HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem2)

-- Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.inst : Not
      (@Std.LawfulLECmp Nat
        (@LE.mk Nat fun (a b : Nat) =>
          @LE.le Nat instLENat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2
          (@LT.mk Nat fun (a b : Nat) =>
            @LT.lt Nat instLTNat
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((fun (a b : Nat) =>
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x1 x2)
          instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (2 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem0 : ∀ (x : Nat),
      Not
        (@LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem1 : ∀ {x y z : Nat},
      @LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem2 : ∀ {x y : Nat},
      Iff
        (Not
          (@LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@LE.le Nat instLENat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
theorem HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α] [inst_3 : LE α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            (∀ {x y : α}, Iff (Not (@LT.lt α inst x y)) (@LE.le α inst_3 y x)) →
              @Std.LawfulLECmp α inst_3 fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (fun (a b : Nat) =>
      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem0 HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem1 HypCheckProof.Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem2)

-- Batteries.AssocList.orderedFind?_orderedInsert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_orderedInsert.h5 : ¬∀ {α β : Type} {x : α} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] (l : Batteries.AssocList α β),
        Batteries.AssocList.KeysOrdered cmp l →
          ∀ (a : α) (b : β),
            Batteries.AssocList.orderedFind? cmp (Batteries.AssocList.orderedInsert cmp l a b) x =
              if cmp x a = Ordering.eq then Option.some b else Batteries.AssocList.orderedFind? cmp l x := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (by
  decide) (1) (0)) (by
  decide +kernel)

-- congrArg₂, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congrArg₂.h8 : ¬∀ {α β γ : Type} (f : α → β → γ) {x x' : α} {y y' : β}, y = y' → f x y = f x' y' := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => a - b : Nat → Nat → Nat) (0) (1) _ (0) rfl) (by
  decide +kernel)

-- congrArg₂, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congrArg₂.h9 : ¬∀ {α β γ : Type} (f : α → β → γ) {x x' : α} {y y' : β}, x = x' → f x y = f x' y' := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => a - b : Nat → Nat → Nat) _ (1) (0) (1) rfl) (by
  decide +kernel)

-- congr_arg₂, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congr_arg₂.h8 : ¬∀ {α β γ : Type} (f : α → β → γ) {x x' : α} {y y' : β}, y = y' → f x y = f x' y' := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => a - b : Nat → Nat → Nat) (0) (1) _ (0) rfl) (by
  decide +kernel)

-- congr_arg₂, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congr_arg₂.h9 : ¬∀ {α β γ : Type} (f : α → β → γ) {x x' : α} {y y' : β}, x = x' → f x y = f x' y' := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun a b => a - b : Nat → Nat → Nat) _ (1) (0) (1) rfl) (by
  decide +kernel)

-- Batteries.OrderedAssocList.getElem?_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_add.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β : Type} {l₂ : Batteries.OrderedAssocList cmp β}
        [inst : Add β] {l₁ : Batteries.OrderedAssocList cmp β} {a : α}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) (instAddNat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) (Bool.false)) (by
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

-- Batteries.OrderedAssocList.getElem?_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_add.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β : Type} {l₂ : Batteries.OrderedAssocList cmp β}
        [inst : Add β] {l₁ : Batteries.OrderedAssocList cmp β} {a : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) (instAddNat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.getElem?_mk_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_mk_cons.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β} {x : α}
        {h : Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t)},
        { toAssocList := Batteries.AssocList.cons a b t, keysOrdered := h : Batteries.OrderedAssocList cmp β }[x]? =
          if cmp x a = Ordering.eq then Option.some b
          else
            { toAssocList := t, keysOrdered := Batteries.AssocList.KeysOrdered.tail h :
                Batteries.OrderedAssocList cmp β }[x]? := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (1) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (0) hc_k0) (by
  decide +kernel)

-- Batteries.OrderedAssocList.getElem?_mk_cons, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_mk_cons.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β} {x : α}
        [inst : Std.TransCmp cmp], Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (0) _) (by
  decide +kernel)

-- Batteries.OrderedAssocList.getElem?_filterMapVal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_filterMapVal.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β α_1 : Type} {f : α → β → Option α_1} {a : α} [inst : Std.LawfulEqCmp cmp]
        (l : Batteries.OrderedAssocList cmp β), Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (fun (a x : Nat) => Option.none) (0) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat })) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.getElem?_filterMapVal, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_filterMapVal.h7 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.TransCmp α cmp] {β α_1 : Type} {f : α → β → Option α_1} {a : α}
        (l : @Batteries.OrderedAssocList α cmp β),
        @Eq (Option α_1)
          (@GetElem?.getElem? (@Batteries.OrderedAssocList α cmp α_1) α α_1
            (fun (l : @Batteries.OrderedAssocList α cmp α_1) (a : α) =>
              @Eq Bool (@Batteries.OrderedAssocList.contains α cmp α_1 l a) Bool.true)
            (@Batteries.OrderedAssocList.instGetElem?EqBoolContainsTrue α cmp α_1)
            (@Batteries.OrderedAssocList.filterMapVal α cmp inst β α_1 f l) a)
          (@Option.bind β α_1
            (@GetElem?.getElem? (@Batteries.OrderedAssocList α cmp β) α β
              (fun (l : @Batteries.OrderedAssocList α cmp β) (a : α) =>
                @Eq Bool (@Batteries.OrderedAssocList.contains α cmp β l a) Bool.true)
              (@Batteries.OrderedAssocList.instGetElem?EqBoolContainsTrue α cmp β) l a)
            fun (b : β) => f a b)) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (fun (a : Bool) =>
      @ite (Nat → Option Nat) (@Eq Bool a Bool.false) (instDecidableEqBool a Bool.false) (fun (x : Nat) => @Option.none Nat)
        (@Option.some Nat)) (Bool.false) (@Batteries.OrderedAssocList.mk Bool (fun (x x_1 : Bool) => Ordering.eq) Nat
      (@Batteries.AssocList.cons Bool Nat Bool.true (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Batteries.AssocList.nil Bool Nat))
      (@of_decide_eq_true
        (@Batteries.AssocList.KeysOrdered Bool Nat (fun (x x_1 : Bool) => Ordering.eq)
          (@Batteries.AssocList.cons Bool Nat Bool.true (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Batteries.AssocList.nil Bool Nat)))
        (@HypCheckDec.keysOrdered Bool Nat (fun (x x_1 : Bool) => Ordering.eq)
          (@Batteries.AssocList.cons Bool Nat Bool.true (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Batteries.AssocList.nil Bool Nat)))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Batteries.AssocList.KeysOrdered Bool Nat (fun (x x_1 : Bool) => Ordering.eq)
                (@Batteries.AssocList.cons Bool Nat Bool.true (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Batteries.AssocList.nil Bool Nat)))
              (@HypCheckDec.keysOrdered Bool Nat (fun (x x_1 : Bool) => Ordering.eq)
                (@Batteries.AssocList.cons Bool Nat Bool.true (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Batteries.AssocList.nil Bool Nat))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_cons.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β} {x : α},
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) →
          Batteries.AssocList.orderedFind? cmp (Batteries.AssocList.cons a b t) x =
            if cmp x a = Ordering.eq then Option.some b else Batteries.AssocList.orderedFind? cmp t x := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (1) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (0) (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_cons, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_cons.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β} {x : α}
        [inst : Std.TransCmp cmp],
        Batteries.AssocList.orderedFind? cmp (Batteries.AssocList.cons a b t) x =
          if cmp x a = Ordering.eq then Option.some b else Batteries.AssocList.orderedFind? cmp t x := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (1) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (0) _) (by
  decide +kernel)

-- Batteries.OrderedAssocList.getElem?_insert, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_insert.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β : Type} {x : α}
        (l : Batteries.OrderedAssocList cmp β) (a : α) (b : β), Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Bool.false) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) (Bool.false) (0)) (by
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

-- Batteries.OrderedAssocList.getElem?_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_insert.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β : Type} {x : α}
        (l : Batteries.OrderedAssocList cmp β) (a : α) (b : β), Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (0) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.getElem?_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_mul.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β : Type} {l₂ : Batteries.OrderedAssocList cmp β}
        [inst : Mul β] {l₁ : Batteries.OrderedAssocList cmp β} {a : α}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) (instMulNat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) (Bool.false)) (by
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

-- Batteries.OrderedAssocList.getElem?_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_mul.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β : Type} {l₂ : Batteries.OrderedAssocList cmp β}
        [inst : Mul β] {l₁ : Batteries.OrderedAssocList cmp β} {a : α}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) (instMulNat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.getElem?_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_cons.h6 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {a : α} {b : β} {x : α} {l : @Batteries.OrderedAssocList α cmp β}
        {w : @Batteries.OrderedAssocList.LTHeadKey α cmp β a l},
        @Eq (Option β)
          (@GetElem?.getElem? (@Batteries.OrderedAssocList α cmp β) α β
            (fun (l : @Batteries.OrderedAssocList α cmp β) (a : α) =>
              @Eq Bool (@Batteries.OrderedAssocList.contains α cmp β l a) Bool.true)
            (@Batteries.OrderedAssocList.instGetElem?EqBoolContainsTrue α cmp β)
            (@Batteries.OrderedAssocList.cons α cmp β a b l w) x)
          (@ite (Option β) (@Eq Ordering (cmp x a) Ordering.eq) (instDecidableEqOrdering (cmp x a) Ordering.eq)
            (@Option.some β b)
            (@GetElem?.getElem? (@Batteries.OrderedAssocList α cmp β) α β
              (fun (l : @Batteries.OrderedAssocList α cmp β) (a : α) =>
                @Eq Bool (@Batteries.OrderedAssocList.contains α cmp β l a) Bool.true)
              (@Batteries.OrderedAssocList.instGetElem?EqBoolContainsTrue α cmp β) l x))) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.OrderedAssocList.mk Nat
      (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) Nat
      (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))
      (@of_decide_eq_true
        (@Batteries.AssocList.KeysOrdered Nat Nat
          (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@HypCheckDec.keysOrdered Nat Nat
          (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Batteries.AssocList.KeysOrdered Nat Nat
                (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
              (@HypCheckDec.keysOrdered Nat Nat
                (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) hc_k0) (by
  decide +kernel)

-- Batteries.OrderedAssocList.getElem?_cons, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_cons.h8 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {a : α} {b : β} {x : α} [inst : @Std.TransCmp α cmp]
        {l : @Batteries.OrderedAssocList α cmp β}, @Batteries.OrderedAssocList.LTHeadKey α cmp β a l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) _ (@Batteries.OrderedAssocList.mk Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
      (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))
      (@of_decide_eq_true
        (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
              (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.inst : Not
      (@Std.LawfulLTCmp Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2 (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)
          ((fun (a b : Nat) => a.decLe b) x1 x2) instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.prem0 : ∀ {x y z : Nat}, @LE.le Nat instLENat x y → @LE.le Nat instLENat y z → @LE.le Nat instLENat x z := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.prem1 : ∀ {x y : Nat}, Not (@LE.le Nat instLENat x y) → Not (@LE.le Nat instLENat y x) → @Eq Nat x y := by
  omega
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α],
        (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
          (∀ {x y : α}, Not (@LT.lt α inst x y) → Not (@LT.lt α inst y x) → @Eq α x y) →
            @Std.LawfulLTCmp α inst fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) (fun (a b : Nat) => a.decLe b) (instDecidableEqNat) HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.prem0 HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.prem1)

-- Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h5 : ¬∀ {α : Type} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : DecidableEq α],
        (∀ (x : α), ¬x < x) →
          (∀ {x y : α}, ¬x < y → ¬y < x → x = y) → Std.LawfulLTCmp fun (x1 x2 : α) => compareOfLessAndEq x1 x2 := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≠ b⟩ : LT Nat) (fun (a b : Nat) => instDecidableNot) (instDecidableEqNat) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.inst : Not
      (@Std.LawfulLTCmp Nat
        (@LT.mk Nat fun (a b : Nat) =>
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2
          (@LT.mk Nat fun (a b : Nat) =>
            @LT.lt Nat instLTNat
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((fun (a b : Nat) =>
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x1 x2)
          instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (2 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.prem0 : ∀ (x : Nat),
      Not
        (@LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.prem1 : ∀ {x y z : Nat},
      @LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  omega
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            @Std.LawfulLTCmp α inst fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (fun (a b : Nat) =>
      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.prem0 HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.prem1)

-- Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.inst : Not
      (@Std.TransCmp Nat fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2 (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)
          ((fun (a b : Nat) => a.decLe b) x1 x2) instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.prem0 : ∀ {x y z : Nat}, @LE.le Nat instLENat x y → @LE.le Nat instLENat y z → @LE.le Nat instLENat x z := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.prem1 : ∀ {x y : Nat}, Not (@LE.le Nat instLENat x y) → Not (@LE.le Nat instLENat y x) → @Eq Nat x y := by
  omega
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α],
        (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
          (∀ {x y : α}, Not (@LT.lt α inst x y) → Not (@LT.lt α inst y x) → @Eq α x y) →
            @Std.TransCmp α fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) (fun (a b : Nat) => a.decLe b) (instDecidableEqNat) HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.prem0 HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h4.prem1)

-- Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h5 : ¬∀ {α : Type} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : DecidableEq α],
        (∀ (x : α), ¬x < x) →
          (∀ {x y : α}, ¬x < y → ¬y < x → x = y) → Std.TransCmp fun (x1 x2 : α) => compareOfLessAndEq x1 x2 := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≠ b⟩ : LT Nat) (fun (a b : Nat) => instDecidableNot) (instDecidableEqNat) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.inst : Not
      (@Std.TransCmp Nat fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2
          (@LT.mk Nat fun (a b : Nat) =>
            @LT.lt Nat instLTNat
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((fun (a b : Nat) =>
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x1 x2)
          instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (2 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.prem0 : ∀ (x : Nat),
      Not
        (@LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.prem1 : ∀ {x y z : Nat},
      @LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  omega
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            @Std.TransCmp α fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (fun (a b : Nat) =>
      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.prem0 HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm.h6.prem1)

-- List.cons_subperm_of_not_mem_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_subperm_of_not_mem_of_mem.h4 : ¬∀ {α : Type} {a : α} {l₁ l₂ : List α}, a ∈ l₂ → l₁.Subperm l₂ → (a :: l₁).Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) (0) ([0]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.cons_subperm_of_not_mem_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_subperm_of_not_mem_of_mem.h5 : ¬∀ {α : Type} {a : α} {l₁ l₂ : List α}, ¬a ∈ l₁ → l₁.Subperm l₂ → (a :: l₁).Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) (0) ([]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.cons_subperm_of_not_mem_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_subperm_of_not_mem_of_mem.h6 : ¬∀ {α : Type} {a : α} {l₁ l₂ : List α}, ¬a ∈ l₁ → a ∈ l₂ → (a :: l₁).Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) (0) ([1]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.toAssocList_insert, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_insert.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.OrientedCmp cmp] {β : Type} (l : Batteries.OrderedAssocList cmp β)
        (a : α) (b : β), Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) (Bool.false) (0)) (by
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

-- Batteries.OrderedAssocList.toAssocList_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_insert.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β : Type} (l : Batteries.OrderedAssocList cmp β)
        (a : α) (b : β), Std.OrientedCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.merge_nil_nil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_nil_nil.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β γ δ : Type}
        {f : α → Option β → Option γ → Option δ}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (Nat) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none)) (by
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

-- Batteries.OrderedAssocList.merge_nil_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_nil_nil.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β γ δ : Type}
        {f : α → Option β → Option γ → Option δ}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (Nat) (Nat) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.none)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.AssocList.KeysOrdered.filterMapVal, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.filterMapVal.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {l : Batteries.AssocList α β} {α_1 : Type} {f : α → β → Option α_1}
        [inst : Std.TransCmp cmp], Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.filterMapVal f l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Batteries.AssocList.cons 0 0 (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (Nat) (fun (a : Nat) => Option.some) _) (by
  decide +kernel)

-- List.Perm.diff_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.diff_right.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] (t : List α), l₁.Perm l₂ → (l₁.diff t).Perm (l₂.diff t) := fun hc_h => absurd (@hc_h (Nat) ([0, 1]) ([1, 0]) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Perm.diff_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.diff_right.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (t : List α), (l₁.diff t).Perm (l₂.diff t) := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (instBEqOfDecidableEq) _ ([])) (by
  decide +kernel)

-- List.Perm.union_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.union_left.h6 : ¬∀ {α : Type} {t₁ t₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (l : List α), (l ∪ t₁).Perm (l ∪ t₂) := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (instBEqOfDecidableEq) _ ([])) (by
  decide +kernel)

-- List.findIdxNth_eq_findIdxNth_of_ge_countP_ge_countP, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_eq_findIdxNth_of_ge_countP_ge_countP.h5 : ¬∀ {α : Type} {p : α → Bool} {n m : Nat} {xs : List α},
        List.countP p xs ≤ m → List.findIdxNth p xs n = List.findIdxNth p xs m := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) (0) (1) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.findIdxNth_eq_findIdxNth_of_ge_countP_ge_countP, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_eq_findIdxNth_of_ge_countP_ge_countP.h6 : ¬∀ {α : Type} {p : α → Bool} {n m : Nat} {xs : List α},
        List.countP p xs ≤ n → List.findIdxNth p xs n = List.findIdxNth p xs m := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) (1) (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.partialSums_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.partialSums_append.h4 : ¬∀ {α : Type} [inst : Add α] [inst_1 : Zero α] [inst_2 : Std.Associative fun (x1 x2 : α) => x1 + x2] {l₁ l₂ : List α},
        (l₁ ++ l₂).partialSums = l₁.partialSums ++ List.map (fun (x : α) => l₁.sum + x) l₂.partialSums.tail := fun hc_h => absurd (@hc_h (Nat) (instAddNat) (⟨1⟩ : Zero Nat) _ ([]) ([0])) (by
  decide +kernel)

-- List.append_eq_of_isPrefixOf?_eq_some, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.append_eq_of_isPrefixOf?_eq_some.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys zs : List α}, xs.isPrefixOf? ys = Option.some zs → xs ++ zs = ys := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([1]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.append_eq_of_isPrefixOf?_eq_some, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.append_eq_of_isPrefixOf?_eq_some.h6 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys zs : List α}, xs ++ zs = ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([]) ([0])) (by
  decide +kernel)

-- Std.LawfulBEqCmp.compareOfLessAndEq_of_lt_irrefl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulBEqCmp.compareOfLessAndEq_of_lt_irrefl.h5 : ¬∀ {α : Type} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : DecidableEq α] [inst_3 : BEq α],
        (∀ (x : α), ¬x < x) → Std.LawfulBEqCmp fun (x1 x2 : α) => compareOfLessAndEq x1 x2 := fun hc_h => absurd (@hc_h (Nat) (instLTNat) (Nat.decLt) (instDecidableEqNat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (by
  simp)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.LawfulBEqCmp.compareOfLessAndEq_of_lt_irrefl, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulBEqCmp.compareOfLessAndEq_of_lt_irrefl.h6 : ¬∀ {α : Type} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : DecidableEq α] [inst_3 : BEq α] [inst_4 : LawfulBEq α],
        Std.LawfulBEqCmp fun (x1 x2 : α) => compareOfLessAndEq x1 x2 := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (fun (a b : Nat) => a.decLe b) (instDecidableEqNat) (instBEqOfDecidableEq) _) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- BitVec.getElem_ofFnLEAux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.BitVec.getElem_ofFnLEAux.h4 : ¬∀ {n m : Nat} (f : Fin n → Bool) (i : Nat), i < m → i < n := fun hc_h => absurd (@hc_h (0) (1) (fun (a : Fin 0) => Bool.false) (0) (by
  decide)) (by
  decide +kernel)

-- BitVec.getElem_ofFnLEAux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.BitVec.getElem_ofFnLEAux.h5 : ¬∀ {n m : Nat} (f : Fin n → Bool) (i : Nat), i < n → i < m := fun hc_h => absurd (@hc_h (1) (0) (fun (a : Fin 1) => Bool.false) (0) (by
  decide)) (by
  decide +kernel)

-- Substring.Raw.Valid.next, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.next.h5 : ¬∀ {m₁ : List Char} {c : Char} {m₂ : List Char} {s : Substring.Raw},
        s.Valid →
          s.next { byteIdx := String.utf8Len m₁ : String.Pos.Raw } =
            { byteIdx := String.utf8Len m₁ + c.utf8Size : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) ('a') ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) ((@Substring.Raw.Valid.mk ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   decide)))) (by
  decide +kernel)

-- Batteries.UnionFind.setParent_rankD_lt, hypothesis 3: necessary
/- FAILED: 10:90: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.30 = true) = true
in the application
  id (Eq.refl true) | 24:28: Function expected at
  (fun {arr} {x y} a =>
      Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl true)))
        (Lean.Omega.Constraint.combine_sat' (?m.147 a) (?m.149 a)))
    ?m.153
but this term has type
  False

Note: Expected a function because this term is being applied to the argument
  ⋯ | 2:108: missing end of character literal | 2:108: missing end of character literal | 41:15: unexpected token ';'; expected ':=', 'where' or '|' | 126:27: (deterministic) timeout at `elaborator`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 2:113: missing end of character literal | 2:113: missing end of character literal
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.setParent_rankD_lt.h3 : ¬∀ {arr : Array Batteries.UFNode} {x y : Fin arr.size} {i : Nat},
        (Batteries.UnionFind.parentD arr i ≠ i →
            Batteries.UnionFind.rankD arr i < Batteries.UnionFind.rankD arr (Batteries.UnionFind.parentD arr i)) →
          have arr' :=
            arr.set ↑x { parent := ↑y, rank := arr[x].rank : Batteries.UFNode }
              fun {arr : Array Batteries.UFNode} {x y : Fin arr.size} =>
              Decidable.byContradiction fun (a : ¬↑x < arr.size) =>
                (fun {arr : Array Batteries.UFNode} {x y : Fin arr.size} (a : ¬↑x < arr.size) =>
                    Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                      (Lean.Omega.Constraint.combine_sat'
                        (Lean.Omega.tidy_sat
                          (Lean.Omega.Constraint.addInequality_sat
                            (le_of_le_of_eq
                              (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt x.isLt)))
                              (Eq.trans
                                (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                  (Eq.trans
                                    (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                      (id (Eq.refl 1)))
                                    (Eq.symm
                                      (Lean.Omega.LinearCombo.add_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                        { const := 1 : Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList [↑arr[↑y].rank, ↑arr[↑x].rank, ↑↑x, ↑arr.size])))))
                                (Eq.symm
                                  (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                    { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList [↑arr[↑y].rank, ↑arr[↑x].rank, ↑↑x, ↑arr.size])))))))
                        (Lean.Omega.Constraint.addInequality_sat
                          (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt a)))
                            (Eq.trans
                              (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3))
                              (Eq.symm
                                (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                  { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                  (Lean.Omega.Coeffs.ofList [↑arr[↑y].rank, ↑arr[↑x].rank, ↑↑x, ↑arr.size]))))))))
                  a;
          Batteries.UnionFind.parentD arr' i ≠ i →
            Batteries.UnionFind.rankD arr' i < Batteries.UnionFind.rankD arr' (Batteries.UnionFind.parentD arr' i) := fun hc_h => absurd (@hc_h (#[{ parent := 0, rank := 1 : Batteries.UFNode }, { parent := 0, rank := 0 : Batteries.UFNode }]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (0) (by
  decide)) (by
  decide +kernel)
-/

-- Batteries.UnionFind.setParent_rankD_lt, hypothesis 5: necessary
/- FAILED: 10:92: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.33 = true) = true
in the application
  id (Eq.refl true) | 25:30: Function expected at
  (fun {arr} {x y} a =>
      Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl true)))
        (Lean.Omega.Constraint.combine_sat' (?m.150 a) (?m.152 a)))
    ?m.156
but this term has type
  False

Note: Expected a function because this term is being applied to the argument
  ⋯ | 2:108: missing end of character literal | 2:108: missing end of character literal | 41:15: unexpected token ';'; expected ':=', 'where' or '|' | 126:27: (deterministic) timeout at `elaborator`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 2:113: missing end of character literal | 2:113: missing end of character literal
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.setParent_rankD_lt.h5 : ¬∀ {arr : Array Batteries.UFNode} {x y : Fin arr.size},
        arr[↑x].rank < arr[↑y].rank →
          ∀ {i : Nat},
            have arr' :=
              arr.set ↑x { parent := ↑y, rank := arr[x].rank : Batteries.UFNode }
                fun {arr : Array Batteries.UFNode} {x y : Fin arr.size} =>
                Decidable.byContradiction fun (a : ¬↑x < arr.size) =>
                  (fun {arr : Array Batteries.UFNode} {x y : Fin arr.size} (a : ¬↑x < arr.size) =>
                      Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                        (Lean.Omega.Constraint.combine_sat'
                          (Lean.Omega.tidy_sat
                            (Lean.Omega.Constraint.addInequality_sat
                              (le_of_le_of_eq
                                (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt x.isLt)))
                                (Eq.trans
                                  (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                    (Eq.trans
                                      (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                        (id (Eq.refl 1)))
                                      (Eq.symm
                                        (Lean.Omega.LinearCombo.add_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                          { const := 1 : Lean.Omega.LinearCombo }
                                          (Lean.Omega.Coeffs.ofList [↑arr[↑y].rank, ↑arr[↑x].rank, ↑↑x, ↑arr.size])))))
                                  (Eq.symm
                                    (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                      { const := 1, coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                      (Lean.Omega.Coeffs.ofList [↑arr[↑y].rank, ↑arr[↑x].rank, ↑↑x, ↑arr.size])))))))
                          (Lean.Omega.Constraint.addInequality_sat
                            (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt a)))
                              (Eq.trans
                                (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_2)
                                  (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3))
                                (Eq.symm
                                  (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 1] : Lean.Omega.LinearCombo }
                                    { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList [↑arr[↑y].rank, ↑arr[↑x].rank, ↑↑x, ↑arr.size]))))))))
                    a;
            Batteries.UnionFind.parentD arr' i ≠ i →
              Batteries.UnionFind.rankD arr' i < Batteries.UnionFind.rankD arr' (Batteries.UnionFind.parentD arr' i) := fun hc_h => absurd (@hc_h (#[{ parent := 0, rank := 0 : Batteries.UFNode }, { parent := 0, rank := 1 : Batteries.UFNode }]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1)) (by
  decide +kernel)
-/

-- Batteries.AssocList.find?_mapVal, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.find?_mapVal.h4 : ¬∀ {α β γ : Type} [inst : BEq α] (f : α → β → γ) (a : α) (l : Batteries.AssocList α β),
        Batteries.AssocList.find? a (Batteries.AssocList.mapVal f l) = Option.map (f a) (Batteries.AssocList.find? a l) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (fun a b => a - b : Nat → Nat → Nat) (0) (Batteries.AssocList.cons 1 0 Batteries.AssocList.nil)) (by
  decide +kernel)

-- Vector.getElem_succ_scanl, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.getElem_succ_scanl.h7 : ¬∀ {β α : Type} {n i : Nat} {init : β} {f : β → α → β} {as : Vector α n}, i + 1 < n + 1 := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (0) (0) (fun a b => a - b : Nat → Nat → Nat) (#v[])) (by
  decide +kernel)

-- Vector.getElem_scanr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.getElem_scanr.h7 : ¬∀ {α β : Type} {n i : Nat} {init : β} {f : α → β → β} {as : Vector α n}, i < n + 1 := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (1) (0) (fun a b => a - b : Nat → Nat → Nat) (#v[])) (by
  decide +kernel)

-- Vector.getElem_scanl, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.getElem_scanl.h7 : ¬∀ {β α : Type} {n i : Nat} {init : β} {f : β → α → β} {as : Vector α n}, i < n + 1 := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (1) (0) (fun a b => a - b : Nat → Nat → Nat) (#v[])) (by
  decide +kernel)

-- Fin.get_findRev?_maximal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.get_findRev?_maximal.h2 : ¬∀ {n : Nat} {p : Fin n → Bool} (j : Fin n), (Fin.findRev? p).isSome = Bool.true := fun hc_h => absurd (@hc_h (1) (fun (a : Fin 1) => Bool.false) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.get_findRev?_maximal, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.get_findRev?_maximal.h4 : ¬∀ {n : Nat} {p : Fin n → Bool}, (Fin.findRev? p).isSome = Bool.true → ∀ (j : Fin n), p j = Bool.false := fun hc_h => absurd (@hc_h (1) (fun (a : Fin 1) => Bool.true) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Subperm.exists_of_length_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.exists_of_length_lt.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.length < l₂.length → ∃ (a : α), (a :: l₁).Subperm l₂ := fun hc_h => absurd (@hc_h (Bool) ([Bool.true]) ([Bool.false, Bool.false]) (by
  decide)) (by
  decide +kernel)

-- List.Subperm.exists_of_length_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.exists_of_length_lt.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Subperm l₂ → ∃ (a : α), (a :: l₁).Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) ([]) ([]) (by
  decide)) (by
  simp)

-- Nat.and_or_left_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.and_or_left_injective.h3 : ¬∀ {m x y : Nat}, m ||| x = m ||| y → x = y := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.and_or_left_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.and_or_left_injective.h4 : ¬∀ {m x y : Nat}, m &&& x = m &&& y → x = y := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.and_or_right_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.and_or_right_injective.h3 : ¬∀ {m x y : Nat}, x ||| m = y ||| m → x = y := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.and_or_right_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.and_or_right_injective.h4 : ¬∀ {m x y : Nat}, x &&& m = y &&& m → x = y := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.forIn_eq_bindList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forIn_eq_bindList.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] (f : α → β → m (ForInStep β)) (l : List α) (init : β),
        ForIn.forIn l init f = ForInStep.run <$> ForInStep.bindList f l (ForInStep.yield init) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, ForInStep.yield 0)) ([]) (0)) (by
  decide +kernel)

-- List.getElem_idxOf_eq_idxOfNth_add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_idxOf_eq_idxOfNth_add.h6 : ¬∀ {α : Type} {n : Nat} {x : α} {s : Nat} {xs : List α} [inst : BEq α], n < (List.idxsOf x xs s).length := fun hc_h => absurd (@hc_h (Nat) (0) (0) (0) ([]) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- Vector.finIdxOf?_eq_some_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.finIdxOf?_eq_some_iff.h3 : ¬∀ {α : Type} {n : Nat} [inst : BEq α] {v : Vector α n} {a : α} {i : Fin n},
        v.finIdxOf? a = Option.some i ↔ v.get i = a ∧ ∀ (j : Fin n), j < i → ¬v.get j = a := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (#v[0]) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.foldl_assoc, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.foldl_assoc.h3 : ¬∀ {α : Type} {n : Nat} {op : α → α → α} {f : Fin n → α} {a₁ a₂ : α},
        Fin.foldl n (fun (x : α) (i : Fin n) => op x (f i)) (op a₁ a₂) =
          op a₁ (Fin.foldl n (fun (x : α) (i : Fin n) => op x (f i)) a₂) := fun hc_h => absurd (@hc_h (Bool) (1) (fun a b => !a || b : Bool → Bool → Bool) (fun (a : Fin 1) => Bool.false) (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Fin.dfoldrM_loop_zero, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Fin.dfoldrM_loop_zero.h3.der.{u_1, u_2} : ∀ {m : Type u_1 → Type u_2} {n : Nat} {α : Fin (n + 1) → Type u_1} [inst : Monad m]
      (f : (i : Fin n) → α i.succ → m (α i.castSucc)), 0 < n + 1 := by
  (intros; omega)
theorem HypCheckProof.Fin.dfoldrM_loop_zero.h3.{u_1, u_2} : ∀ {m : Type u_1 → Type u_2} {n : Nat} {α : Fin (n + 1) → Type u_1} [inst : Monad m]
      (f : (i : Fin n) → α i.succ → m (α i.castSucc))
      (x : α (⟨0, HypCheckProof.Fin.dfoldrM_loop_zero.h3.der f⟩ : Fin (n + 1))),
      Fin.dfoldrM.loop n α f 0 (HypCheckProof.Fin.dfoldrM_loop_zero.h3.der f) x = Pure.pure x := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Fin.dfoldrM_loop_zero hc_x0 hc_x1 hc_x2 (@HypCheckProof.Fin.dfoldrM_loop_zero.h3.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x3 hc_x4 hc_x5

-- Array.getElem_succ_scanl, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_succ_scanl.h6 : ¬∀ {β α : Type} {i : Nat} {b : β} {as : Array α} {f : β → α → β}, i + 1 < (Array.scanl f b as).size := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (0) (#[]) (fun a b => a - b : Nat → Nat → Nat)) (by
  decide +kernel)

-- Array.getElem_scanr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_scanr.h6 : ¬∀ {α β : Type} {i : Nat} {b : β} {l : Array α} {f : α → β → β}, i < (Array.scanr f b l).size := fun hc_h => absurd (@hc_h (Nat) (Nat) (1) (0) (#[]) (fun a b => a - b : Nat → Nat → Nat)) (by
  decide +kernel)

-- List.idxOfNth_cons_of_not_beq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_cons_of_not_beq.h6 : ¬∀ {α : Type} {x : α} {xs : List α} {n : Nat} {a : α} [inst : BEq α],
        List.idxOfNth x (a :: xs) n = List.idxOfNth x xs n + 1 := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (0) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- List.prod_pair, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prod_pair.h3 : ¬∀ {α : Type} [inst : Mul α] [inst_1 : One α] {a b : α}, [a, b].prod = a * b := fun hc_h => absurd (@hc_h (Nat) (instMulNat) (⟨0⟩ : One Nat) (1) (1)) (by
  decide +kernel)

-- Std.LawfulBCmp.toTransCmp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulBCmp.toTransCmp.h5 : ¬∀ {α : Type} {inst : LE α} {inst : LT α} {inst : BEq α} {cmp : α → α → Ordering}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (instBEqOfDecidableEq) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.findIdxNth_cons_succ_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_cons_succ_of_pos.h5 : ¬∀ {α : Type} {p : α → Bool} {xs : List α} {n : Nat} {a : α},
        List.findIdxNth p (a :: xs) (n + 1) = List.findIdxNth p xs n + 1 := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([0]) (0) (1)) (by
  decide +kernel)

-- Std.LawfulBCmp.toLawfulBEqCmp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulBCmp.toLawfulBEqCmp.h5 : ¬∀ {α : Type} {inst : LE α} {inst : LT α} {inst : BEq α} {cmp : α → α → Ordering}, Std.LawfulBEqCmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (instBEqOfDecidableEq) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_eq_iff_beq (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.insertP, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.insertP.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} (p : α → Bool) (a : α), (List.insertP p a l₁).Perm (List.insertP p a l₂) := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (fun n => n % 2 == 0 : Nat → Bool) (0)) (by
  decide +kernel)

-- Std.LawfulBCmp.toLawfulLTCmp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulBCmp.toLawfulLTCmp.h5 : ¬∀ {α : Type} [inst : LE α] [inst : LT α] [inst_1 : BEq α] {cmp : α → α → Ordering}, Std.LawfulLTCmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (instBEqOfDecidableEq) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.eq_lt_iff_lt (x := (0 : Nat)) (y := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.inter_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.inter_right.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] (t₁ : List α), (l₁ ∩ t₁).Perm (l₂ ∩ t₁) := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (instBEqOfDecidableEq) ([0])) (by
  decide +kernel)

-- List.subperm_cons_diff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm_cons_diff.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l₁ l₂ : List α}, ((a :: l₁).diff l₂).Subperm (a :: l₁.diff l₂) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) ([1]) ([0])) (by
  decide +kernel)

-- List.getElem_getElem_findIdxs_sub, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_getElem_findIdxs_sub.h5 : ¬∀ {i : Nat} {α : Type} {xs : List α} {p : α → Bool} (s : Nat), i < (List.findIdxs p xs s).length := fun hc_h => absurd (@hc_h (0) (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool) (0)) (by
  decide +kernel)

-- List.idxOfNth_eq_length_of_ge_count, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_eq_length_of_ge_count.h5 : ¬∀ {α : Type} {x : α} {n : Nat} {xs : List α} [inst : BEq α], List.idxOfNth x xs n = xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (0) ([0]) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- List.getElem_findIdxs_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_findIdxs_lt.h5 : ¬∀ {i : Nat} {α : Type} {xs : List α} {p : α → Bool} {s : Nat}, i < (List.findIdxs p xs s).length := fun hc_h => absurd (@hc_h (0) (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool) (0)) (by
  decide +kernel)

-- Std.LawfulLECmp.ne_lt_iff_ge, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLECmp.ne_lt_iff_ge.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y : α} [inst : LE α], cmp x y ≠ Ordering.lt ↔ y ≤ x := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering) (0) (1) (instLENat)) (by
  decide +kernel)

-- Batteries.BinomialHeap.Imp.HeapNode.WF.rank_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinomialHeap.Imp.HeapNode.WF.rank_eq.h5 : ¬∀ {α : Type} {le : α → α → Bool} {a : α} {n : Nat} {s : Batteries.BinomialHeap.Imp.HeapNode α}, s.rank = n := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (0) (Batteries.BinomialHeap.Imp.HeapNode.node 0 Batteries.BinomialHeap.Imp.HeapNode.nil
      Batteries.BinomialHeap.Imp.HeapNode.nil)) (by
  decide +kernel)

-- List.countPBefore_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countPBefore_mono.h5 : ¬∀ {α : Type} {i j : Nat} {p : α → Bool} {xs : List α}, List.countPBefore p xs i ≤ List.countPBefore p xs j := fun hc_h => absurd (@hc_h (Nat) (1) (0) (fun n => n % 2 == 0 : Nat → Bool) ([0])) (by
  decide +kernel)

-- Std.LawfulLTCmp.eq_lt_iff_lt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.eq_lt_iff_lt.h3.inst : ¬((fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.lt ↔ 0 ≤ 0) := by
  decide +kernel
theorem HypCheckProof.Std.LawfulLTCmp.eq_lt_iff_lt.h3 : ¬∀ {α : Type} {inst : LT α} {cmp : α → α → Ordering} {x y : α}, cmp x y = Ordering.lt ↔ x < y := fun hc_h => HypCheckProof.Std.LawfulLTCmp.eq_lt_iff_lt.h3.inst (@hc_h (Nat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) (fun (a b : Nat) => Ord.compare a b) (0) (0))

-- List.dropPrefix?_append_of_beq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dropPrefix?_append_of_beq.h5 : ¬∀ {α : Type} [inst : BEq α] {l₁ l₂ : List α} (p : List α), (l₁ ++ p).dropPrefix? l₂ = Option.some p := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) ([]) ([0]) ([])) (by
  decide +kernel)

-- Nat.toFinDigits_ofFinDigits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigits_ofFinDigits.h3 : ¬∀ {base : Nat}, 2 ≤ base → ∀ {l : List (Fin base)}, (Nat.ofFinDigits l).toFinDigits base = l := fun hc_h => absurd (@hc_h (2) (by
  decide) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)])) (by
  decide +kernel)

-- List.getElem_idxOf_eq_idxOfNth, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_idxOf_eq_idxOfNth.h5 : ¬∀ {α : Type} {n : Nat} {x : α} {xs : List α} [inst : BEq α], n < (List.idxsOf x xs).length := fun hc_h => absurd (@hc_h (Nat) (0) (0) ([]) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- String.Pos.Raw.extract.go₁_append_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.extract.go₁_append_right.h5 : ¬∀ (s t : List Char) (i b : Nat) (e : String.Pos.Raw),
        String.Pos.Raw.extract.go₁ (s ++ t) { byteIdx := i : String.Pos.Raw } { byteIdx := b : String.Pos.Raw } e =
          String.Pos.Raw.extract.go₂ t { byteIdx := b : String.Pos.Raw } e := fun hc_h => absurd (@hc_h ([]) (['a']) (0) (1) ({ : String.Pos.Raw })) (by
  decide +kernel)

-- Substring.Raw.ValidFor.nextn_stop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.nextn_stop.h4 : ¬∀ {l : List Char} {m : List Char} {r : List Char} {s : Substring.Raw} (n : Nat),
        s.nextn n { byteIdx := String.utf8Len m : String.Pos.Raw } = { byteIdx := String.utf8Len m : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (1)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.all, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.all.h5 : ¬∀ {l : List Char} {m : List Char} {r : List Char} (f : Char → Bool) {s : Substring.Raw},
        Substring.Raw.Legacy.all s f = m.all f := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) (fun (a : Char) => Bool.false) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Substring.Raw.ValidFor.takeWhile, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.takeWhile.h5 : ¬∀ {l m r : List Char} (p : Char → Bool) {s : Substring.Raw},
        Substring.Raw.ValidFor l (List.takeWhile p m) (List.dropWhile p m ++ r) (s.takeWhile p) := fun hc_h => absurd (@hc_h ([]) ([]) ([]) (fun (a : Char) => Bool.false) ({ str := "a", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- List.idxOfNth_lt_length_of_lt_count, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_lt_length_of_lt_count.h5 : ¬∀ {α : Type} {n : Nat} {x : α} {xs : List α} [inst : BEq α], List.idxOfNth x xs n < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (0) ([]) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- List.interleave_append_append_of_length_eq_length_add_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleave_append_append_of_length_eq_length_add_one.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} (l₃ l₄ : List α), (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₄.interleave l₃ := fun hc_h => absurd (@hc_h (Nat) ([]) ([]) ([0]) ([1])) (by
  decide +kernel)

-- String.utf8PrevAux_of_valid, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.utf8PrevAux_of_valid.h5 : ¬∀ {cs cs' : List Char} {c : Char} {i p : Nat},
        String.Pos.Raw.utf8PrevAux (cs ++ c :: cs') { byteIdx := i : String.Pos.Raw } { byteIdx := p : String.Pos.Raw } =
          { byteIdx := i + String.utf8Len cs : String.Pos.Raw } := fun hc_h => absurd (@hc_h (['a']) ([]) ('a') (0) (0)) (by
  decide +kernel)

-- List.countBefore_idxOfNth_of_lt_count, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countBefore_idxOfNth_of_lt_count.h5 : ¬∀ {α : Type} {n : Nat} {x : α} [inst : BEq α] {xs : List α}, List.countBefore x xs (List.idxOfNth x xs n) = n := fun hc_h => absurd (@hc_h (Nat) (1) (0) (instBEqOfDecidableEq) ([])) (by
  decide +kernel)

-- List.countBefore_of_ge_length, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countBefore_of_ge_length.h5 : ¬∀ {α : Type} {i : Nat} {x : α} [inst : BEq α] {xs : List α}, List.countBefore x xs i = List.count x xs := fun hc_h => absurd (@hc_h (Nat) (0) (0) (instBEqOfDecidableEq) ([0])) (by
  decide +kernel)

-- List.getElem_filter_eq_getElem_getElem_findIdxs_sub, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_filter_eq_getElem_getElem_findIdxs_sub.h5 : ¬∀ {i : Nat} {α : Type} {xs : List α} {p : α → Bool} (s : Nat), i < (List.filter p xs).length := fun hc_h => absurd (@hc_h (0) (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool) (0)) (by
  decide +kernel)

-- eq_rec_constant, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.eq_rec_constant.h5 : ¬∀ {α : Type} {a a' : α} {β : Type} (y : β), a = a' := fun hc_h => absurd (@hc_h (Nat) (0) (1) (Nat) (0)) (by
  decide +kernel)

-- Batteries.BinomialHeap.Imp.Heap.realSize_deleteMin, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinomialHeap.Imp.Heap.realSize_deleteMin.h5 : ¬∀ {α : Type} {le : α → α → Bool} {a : α} {s' s : Batteries.BinomialHeap.Imp.Heap α}, s.realSize = s'.realSize + 1 := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (Batteries.BinomialHeap.Imp.Heap.nil) (Batteries.BinomialHeap.Imp.Heap.nil)) (by
  decide +kernel)

-- List.diff_erase, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.diff_erase.h2 : ¬∀ {α : Type} [inst : BEq α] (l₁ l₂ : List α) (a : α), (l₁.diff l₂).erase a = (l₁.erase a).diff l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([0, 1]) ([0]) (1)) (by
  decide +kernel)

-- Std.instOrientedCmpByKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instOrientedCmpByKey.h4 : ¬∀ {α β : Type} (f : α → β) (cmp : β → β → Ordering), Std.OrientedCmp (Ordering.byKey f cmp) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n + 1 : Nat → Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TransOrd.instOn, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TransOrd.instOn.h3 : Not (∀ {β α : Type} [ord : Ord β] (f : α → β), @Std.TransOrd α (@Ord.on β α ord f)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (fun n => n + 1 : Nat → Nat)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.pos_findIdxNth_getElem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pos_findIdxNth_getElem.h4 : ¬∀ {α : Type} {p : α → Bool} {n : Nat} {xs : List α}, List.findIdxNth p xs n < xs.length := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) (0) ([])) (by
  decide +kernel)

-- Vector.get_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.get_mk.h3 : ¬∀ {α : Type} {n : Nat} (a : Array α) (i : Fin n), a.size = n := fun hc_h => absurd (@hc_h (Nat) (1) (#[]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.disjoint_of_disjoint_append_right_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_disjoint_append_right_right.h4 : ¬∀ {α : Type} {l : List α} {l₁ : List α} {l₂ : List α}, l.Disjoint l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) ([0])) (by
  simp)

-- List.findIdx_add_mem_findIdxs, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdx_add_mem_findIdxs.h4 : ¬∀ {α : Type} {xs : List α} {p : α → Bool} (s : Nat), List.findIdx p xs + s ∈ List.findIdxs p xs s := fun hc_h => absurd (@hc_h (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool) (0)) (by
  decide +kernel)

-- Vector.toBinaryHeap_wf, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toBinaryHeap_wf.h3 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] {a : Vector α sz}, a.toBinaryHeap.WF := fun hc_h => absurd (@hc_h (Nat) (2) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (#v[0, 1])) (by
  decide +kernel)

-- Std.instOrientedCmpCompareOnOfOrientedOrd_batteries, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instOrientedCmpCompareOnOfOrientedOrd_batteries.h3 : ¬∀ {β α : Type} [inst : Ord β] (f : α → β), Std.OrientedCmp (compareOn f) := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (fun n => n + 1 : Nat → Nat)) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.any_congr_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.any_congr_mem.h4 : ¬∀ {α : Type} {xs : List α} {p q : α → Bool}, xs.any p = xs.any q := fun hc_h => absurd (@hc_h (Nat) ([0]) (fun n => n % 2 == 0 : Nat → Bool) (fun _ => false : Nat → Bool)) (by
  decide +kernel)

-- ByteArray.get_extract_aux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.get_extract_aux.h4 : ¬∀ {i : Nat} {a : ByteArray} {start : Nat} {stop : Nat}, start + i < a.size := fun hc_h => absurd (@hc_h (0) ({ data := #[] : ByteArray }) (0) (0)) (by
  decide +kernel)

-- Std.LawfulCmp.toLawfulLECmp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulCmp.toLawfulLECmp.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] {cmp : α → α → Ordering}, Std.LawfulLECmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.isLE_iff_le (x := (1 : Nat)) (y := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.isChain_of_isChain_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_of_isChain_cons.h4 : ¬∀ {α : Type} {R : α → α → Prop} {b : α} {l : List α}, List.IsChain R l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) ([1, 0])) (by
  decide +kernel)

-- Array.extract_eq_of_size_le_stop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.extract_eq_of_size_le_stop.h4 : ¬∀ {α : Type} {j i : Nat} {a : Array α}, a.extract i j = a.extract i := fun hc_h => absurd (@hc_h (Nat) (0) (0) (#[0])) (by
  decide +kernel)

-- List.disjoint_of_disjoint_cons_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_disjoint_cons_right.h4 : ¬∀ {α : Type} {a : α} {l₁ l₂ : List α}, l₁.Disjoint l₂ := fun hc_h => absurd (@hc_h (Nat) (0) ([0]) ([0])) (by
  simp)

-- List.getElem?_set_eq_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem?_set_eq_of_lt.h4 : ¬∀ {α : Type} (a : α) {n : Nat} {l : List α}, (l.set n a)[n]? = Option.some a := fun hc_h => absurd (@hc_h (Nat) (0) (0) ([])) (by
  decide +kernel)

-- List.findIdxNth_lt_length_of_lt_countP, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_lt_length_of_lt_countP.h4 : ¬∀ {α : Type} {n : Nat} {p : α → Bool} {xs : List α}, List.findIdxNth p xs n < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) ([])) (by
  decide +kernel)

-- List.disjoint_of_disjoint_append_left_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_disjoint_append_left_right.h4 : ¬∀ {α : Type} {l₁ : List α} {l₂ l : List α}, l₂.Disjoint l := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) ([0])) (by
  simp)

-- Fin.eq_none_of_findSomeRev?_eq_none, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_none_of_findSomeRev?_eq_none.h3 : ¬∀ {n : Nat} {α : Type} {f : Fin n → Option α} (i : Fin n), f i = Option.none := fun hc_h => absurd (@hc_h (1) (Nat) (fun (a : Fin 1) => Option.some 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.isSome_findSome?_of_isSome, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.isSome_findSome?_of_isSome.h4 : ¬∀ {n : Nat} {α : Type} {i : Fin n} {f : Fin n → Option α}, (Fin.findSome? f).isSome = Bool.true := fun hc_h => absurd (@hc_h (1) (Nat) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Option.none)) (by
  decide +kernel)

-- Fin.eq_none_of_findSome?_eq_none, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_none_of_findSome?_eq_none.h3 : ¬∀ {n : Nat} {α : Type} {f : Fin n → Option α} (i : Fin n), f i = Option.none := fun hc_h => absurd (@hc_h (1) (Nat) (fun (a : Fin 1) => Option.some 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.pos_iff_exists_findIdxNth, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pos_iff_exists_findIdxNth.h4 : ¬∀ {α : Type} {i : Nat} {p : α → Bool} {xs : List α}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) ([])) (by
  decide +kernel)

-- List.take_succ_drop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.take_succ_drop.h4 : ¬∀ {α : Type} {l : List α} {n stop : Nat}, n < l.length - stop := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0)) (by
  decide +kernel)

-- Fin.findSome?_succ_of_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.findSome?_succ_of_some.h4 : ¬∀ {n : Nat} {α : Type} {x : α} {f : Fin (n + 1) → Option α}, Fin.findSome? f = Option.some x := fun hc_h => absurd (@hc_h (0) (Nat) (0) (fun (a : Fin (0 + 1)) => Option.none)) (by
  decide +kernel)

-- Fin.exists_eq_some_of_findSomeRev?_eq_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_eq_some_of_findSomeRev?_eq_some.h4 : ¬∀ {n : Nat} {α : Type} {x : α} {f : Fin n → Option α}, ∃ (i : Fin n), f i = Option.some x := fun hc_h => absurd (@hc_h (0) (Nat) (0) (fun (a : Fin 0) => Option.none)) (by
  decide +kernel)

-- Fin.exists_minimal_of_findSome?_eq_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_minimal_of_findSome?_eq_some.h4 : ¬∀ {n : Nat} {α : Type} {x : α} {f : Fin n → Option α},
        ∃ (i : Fin n), f i = Option.some x ∧ ∀ (j : Fin n), j < i → f j = Option.none := fun hc_h => absurd (@hc_h (0) (Nat) (0) (fun (a : Fin 0) => Option.none)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.str, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.str.h4 : ¬∀ {l m r : List Char} {s : Substring.Raw}, s.str = String.ofList (l ++ m ++ r) := fun hc_h => absurd (@hc_h ([]) ([]) ([]) ({ str := "a", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Fin.exists_minimal_of_findSomeRev?_eq_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_minimal_of_findSomeRev?_eq_some.h4 : ¬∀ {n : Nat} {α : Type} {x : α} {f : Fin n → Option α},
        ∃ (i : Fin n), f i = Option.some x ∧ ∀ (j : Fin n), i < j → f j = Option.none := fun hc_h => absurd (@hc_h (0) (Nat) (0) (fun (a : Fin 0) => Option.none)) (by
  decide +kernel)

-- String.utf8GetAux?_of_valid, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.utf8GetAux?_of_valid.h4 : ¬∀ (cs cs' : List Char) {i p : Nat},
        String.Pos.Raw.utf8GetAux? (cs ++ cs') { byteIdx := i : String.Pos.Raw } { byteIdx := p : String.Pos.Raw } =
          cs'.head? := fun hc_h => absurd (@hc_h (['a']) ([]) (0) (0)) (by
  decide +kernel)

-- List.min!_eq_min_of_ne_nil, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min!_eq_min_of_ne_nil.h4 : ¬∀ {α : Type} [inst : Inhabited α] [inst : Min α] (l : List α), l ≠ [] := fun hc_h => absurd (@hc_h (Nat) (instInhabitedNat) (instMinNat) ([])) (by
  decide +kernel)

-- Substring.Raw.ValidFor.next_stop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.next_stop.h4 : ¬∀ {l : List Char} {m : List Char} {r : List Char} {s : Substring.Raw},
        s.next { byteIdx := String.utf8Len m : String.Pos.Raw } = { byteIdx := String.utf8Len m : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- List.findIdxNth_eq_length_of_ge_countP, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_eq_length_of_ge_countP.h4 : ¬∀ {α : Type} {p : α → Bool} {n : Nat} {xs : List α}, List.findIdxNth p xs n = xs.length := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) (0) ([0])) (by
  decide +kernel)

-- Substring.Raw.ValidFor.toString, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.toString.h4 : ¬∀ {l : List Char} {m : List Char} {r : List Char} {s : Substring.Raw}, s.toString = String.ofList m := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.next, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.next.h4 : ¬∀ {l : List Char} {c : Char} {r : List Char} {it : String.Legacy.Iterator},
        String.Legacy.Iterator.ValidFor (c :: l) r it.next := fun hc_h => absurd (@hc_h ([]) ('a') ([]) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- List.getElem_getElem_findIdxs, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_getElem_findIdxs.h4 : ¬∀ {i : Nat} {α : Type} {xs : List α} {p : α → Bool}, i < (List.findIdxs p xs).length := fun hc_h => absurd (@hc_h (0) (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Substring.Raw.Valid.foldl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.foldl.h4 : ¬∀ {α : Type} (f : α → Char → α) (init : α) {s : Substring.Raw},
        Substring.Raw.Legacy.foldl f init s = List.foldl f init s.toString.toList := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) (a_1 : Char) => 0) (1) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { byteIdx := 1 : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Vector.toArray_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toArray_injective.h4 : ¬∀ {α : Type} {n : Nat} {v w : Vector α n}, v = w := fun hc_h => absurd (@hc_h (Nat) (1) (#v[0]) (#v[1])) (by
  decide +kernel)

-- List.isChain_lt_range', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_lt_range'.h3 : ¬∀ {step : Nat} (s n : Nat), List.IsChain (fun (x1 x2 : Nat) => x1 < x2) (List.range' s n step) := fun hc_h => absurd (@hc_h (0) (0) (2)) (by
  decide +kernel)

-- ByteArray.uset_eq_set, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.uset_eq_set.h2 : ¬∀ (a : ByteArray) {i : USize} (v : UInt8), i.toNat < a.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (USize.ofNat 0) (UInt8.ofNat 0)) (by
  decide +kernel)

-- Batteries.BinaryHeap.popMax_perm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.popMax_perm.h3 : ¬∀ {α : Type} [inst : Ord α] {heap : Batteries.BinaryHeap α}, 0 < heap.size := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) ({ arr := #[] : Batteries.BinaryHeap Nat })) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.curr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.curr.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator}, it.curr = r.headD Inhabited.default := fun hc_h => absurd (@hc_h ([]) (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- Fin.eq_false_of_isNone_findRev?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_false_of_isNone_findRev?.h3 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool}, p i = Bool.false := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Bool.true)) (by
  decide +kernel)

-- Nat.toFinDigits_head?_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigits_head?_ne_zero.h3 : Not
      (∀ {n : Nat} {base : Nat} (d : Fin base),
        @Ne Nat (@Fin.val base d) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Fin.isSome_findRev?_of_eq_true, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.isSome_findRev?_of_eq_true.h3 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool}, (Fin.findRev? p).isSome = Bool.true := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Bool.false)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.out, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.out.h3 : ¬∀ {l r : List Char} {it : String.Legacy.Iterator},
        it =
          { s := String.ofList (l.reverseAux r), i := { byteIdx := String.utf8Len l : String.Pos.Raw } :
            String.Legacy.Iterator } := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- Nat.ofFinDigits_toFinDigitsFixed, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofFinDigits_toFinDigitsFixed.h3 : ¬∀ {base : Nat} {n prec : Nat}, NeZero base := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- String.Legacy.Iterator.ValidFor.pos_eq_rawEndPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.pos_eq_rawEndPos.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator}, it.i = it.s.rawEndPos ↔ r = [] := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.remainingBytes, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.remainingBytes.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator}, it.remainingBytes = String.utf8Len r := fun hc_h => absurd (@hc_h ([]) (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- String.Legacy.Iterator.Valid.remainingToString, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.Valid.remainingToString.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator}, it.remainingToString = String.ofList r := fun hc_h => absurd (@hc_h ([]) (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- List.Subperm.subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.subset.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ ⊆ l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([])) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.pos.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator},
        it.i = { byteIdx := String.utf8Len l : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- List.leftInverse_sigmaCountToIdx_idxToSigmaCount, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.leftInverse_sigmaCountToIdx_idxToSigmaCount.h2 : ¬∀ {α : Type} [inst : BEq α] {xs : List α}, ReflBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.rfl (a := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Array.toBinaryHeap_wf, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.toBinaryHeap_wf.h2 : ¬∀ {α : Type} [inst : Ord α] {a : Array α}, a.toBinaryHeap.WF := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (#[0, 1])) (by
  decide +kernel)

-- Int.testBit_ofBits_ge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.testBit_ofBits_ge.h3 : ¬∀ {n i : Nat} {f : Fin n → Bool}, (Int.ofBits f).testBit i = Decidable.decide (Int.ofBits f < 0) := fun hc_h => absurd (@hc_h (2) (0) (fun (a : Fin 2) => if a = (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) then Bool.false else Bool.true)) (by
  decide +kernel)

-- List.sections_eq_nil_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sections_eq_nil_of_isEmpty.h2 : ¬∀ {α : Type} {L : List (List α)}, L.sections = [] := fun hc_h => absurd (@hc_h (Nat) ([])) (by
  decide +kernel)

-- Nat.avg_lt_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.avg_lt_left.h2 : ¬∀ {b a : Nat}, a.avg b < a := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- String.Pos.Raw.Valid.le_rawEndPos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.Valid.le_rawEndPos.h2 : ¬∀ {s : String} {p : String.Pos.Raw}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("") ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide +kernel)

-- Nat.avg_le_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.avg_le_left.h2 : ¬∀ {b a : Nat}, a.avg b ≤ a := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- String.utf8Len_le_of_sublist, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.utf8Len_le_of_sublist.h2 : ¬∀ {cs₁ cs₂ : List Char}, String.utf8Len cs₁ ≤ String.utf8Len cs₂ := fun hc_h => absurd (@hc_h (['a']) ([])) (by
  decide +kernel)

-- UInt32.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.UInt32.ext.h2 : ¬∀ {x y : UInt32}, x = y := fun hc_h => absurd (@hc_h (UInt32.ofNat 0) (UInt32.ofNat 1)) (by
  decide +kernel)

-- Substring.Raw.Valid.atEnd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.atEnd.h2 : ¬∀ {p : Nat} {s : Substring.Raw}, s.atEnd { byteIdx := p : String.Pos.Raw } = Bool.true ↔ p = s.toString.utf8ByteSize := fun hc_h => absurd (@hc_h (0) ({ str := "", startPos := { byteIdx := 1 : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Nat.le_avg_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_avg_right.h2 : ¬∀ {b a : Nat}, b ≤ a.avg b := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.eq_of_xor_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_xor_eq_zero.h2 : ¬∀ {x y : Nat}, x = y := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.ofFinDigits_of_le_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofFinDigits_of_le_one.h1 : ¬∀ {base : Nat} {l : List (Fin base)}, Nat.ofFinDigits l = 0 := fun hc_h => absurd (@hc_h (2) ([(⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)])) (by
  decide +kernel)

-- Nat.avg_lt_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.avg_lt_right.h2 : ¬∀ {a b : Nat}, a.avg b < b := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.parentD_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.parentD_eq.h2 : ¬∀ {arr : Array Batteries.UFNode} {i : Nat}, i < arr.size := fun hc_h => absurd (@hc_h (#[]) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.rank_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.rank_lt.h2 : ¬∀ {self : Batteries.UnionFind} {i : Nat}, self.rank i < self.rank (self.parent i) := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.parentD_of_not_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.parentD_of_not_lt.h2 : ¬∀ {i : Nat} {arr : Array Batteries.UFNode}, Batteries.UnionFind.parentD arr i = i := fun hc_h => absurd (@hc_h (1) (#[{ parent := 0, rank := 0 : Batteries.UFNode }, { parent := 0, rank := 1 : Batteries.UFNode }])) (by
  decide +kernel)

-- Batteries.UnionFind.lt_of_parentD, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.lt_of_parentD.h2 : ¬∀ {arr : Array Batteries.UFNode} {i : Nat}, i < arr.size := fun hc_h => absurd (@hc_h (#[]) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.parentD_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.parentD_lt.h2 : ¬∀ (self : Batteries.UnionFind) {i : Nat}, Batteries.UnionFind.parentD self.arr i < self.arr.size := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (0)) (by
  decide +kernel)

-- Substring.Raw.Valid.bsize, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.bsize.h1 : ¬∀ {s : Substring.Raw}, s.bsize = String.utf8Len s.toString.toList := fun hc_h => absurd (@hc_h ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { byteIdx := 1 : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Char.isAscii_of_isAlpha, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.isAscii_of_isAlpha.h1 : ¬∀ {c : Char}, c.isAscii = Bool.true := fun hc_h => absurd (@hc_h ('é')) (by
  decide +kernel)

-- Char.isAscii_of_isAlphanum, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.isAscii_of_isAlphanum.h1 : ¬∀ {c : Char}, c.isAscii = Bool.true := fun hc_h => absurd (@hc_h ('é')) (by
  decide +kernel)

