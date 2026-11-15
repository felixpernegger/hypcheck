import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- List.apply_minOn_lt_apply_getElem_of_lt_minIdxOn, hypothesis 6: necessary
/- FAILED: 3:105: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
β α : Type
inst : LE β
inst_1 : DecidableLE β
inst_2 : LT β
inst_3 : Std.IsLinearPreorder β
f : α → β
xs : List α
h : xs ≠ []
k : Nat
 | 1016:22: Application type mismatch: The argument
  β
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.56 ≠ []
of sort `Prop` in the application
  (@fun {β α} [LE β] [DecidableLE β] {f} {xs} h {k} hk this a =>
      Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl true)))
        (Lean.Omega.Constraint.combine_sat'
          (Lean.Omega.tidy_sat
            (Lean.Omega.combo_sat' { lowerBound := some 1, upperBound := none }
              { lowerBound := none | 3:224: `grind` has failed, use `+verbose` to obtain diagnostic information | 6:194: `grind` has failed, use `+verbose` to obtain diagnostic information | 4:2: Tactic `decide` proved that the proposition
  ¬∀ (h : [0, 1] ≠ []) (hk : 0 < List.minIdxOn (fun n => n + 1) [0, 1] h),
      (fun n => n + 1) (List.minOn (fun n => n + 1) [0, 1] h) < (fun n => n + 1) [0, 1][0]
is false | 143:46: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 6:2: Tactic `decide` proved that the proposition
  ¬∀ (h : [0, 1] ≠ []),
      0 < List.minIdxOn (fun n => n + 1) [0, 1] h →
        (fun n => n + 1) (List.minOn (fun n => n + 1) [0, 1] h) < (fun n => n + 1) [0, 1][0]
is false | 62:194: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.apply_minOn_lt_apply_getElem_of_lt_minIdxOn.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [inst_3 : Std.IsLinearPreorder β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {k : Nat} (hk : k < List.minIdxOn f xs h), f (List.minOn f xs h) < f xs[k] := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (fun (a b : Nat) => (a % 2).decLe (b % 2)) (instLTNat) (@Std.IsLinearPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (fun n => n + 1 : Nat → Nat) ([0, 1]) hc_k0 (0) hc_k1) (by
  decide)
-/

-- Array.Perm.extract, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.Perm.extract.h3 : ¬∀ {α : Type} {xs ys : Array α} {lo hi : Nat},
        (∀ (i : Nat), i < lo → xs[i]? = ys[i]?) →
          (∀ (i : Nat), hi ≤ i → xs[i]? = ys[i]?) → (xs.extract lo hi).Perm (ys.extract lo hi) := fun hc_h => absurd (@hc_h (Nat) (#[0]) (#[1]) (0) (1) (by
  decide) (by
  grind)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))

-- Array.Perm.extract, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.Perm.extract.h6 : ¬∀ {α : Type} {xs ys : Array α},
        xs.Perm ys → ∀ {lo hi : Nat}, (∀ (i : Nat), hi ≤ i → xs[i]? = ys[i]?) → (xs.extract lo hi).Perm (ys.extract lo hi) := fun hc_h => absurd (@hc_h (Nat) (#[0, 1]) (#[1, 0]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (2) (by
  grind)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))

-- Array.set_eraseIdx_gt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.set_eraseIdx_gt.h6 : ¬∀ {α : Type} {xs : Array α} {i : Nat} {w : i < xs.size} {j : Nat} {a : α}, j < (xs.eraseIdx i w).size → j < i := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (#[0, 1]) (0) hc_k0 (0) (0) hc_k1) (by
  decide +kernel)

-- Array.set_eraseIdx_gt, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Array.set_eraseIdx_gt.h7.{u_1} : ∀ {α : Type u_1} {xs : Array α} {i : Nat} {w : i < xs.size} {j : Nat} {a : α}, j < i → j < (xs.eraseIdx i w).size := by
  (intros; grind)

-- Array.getElem_setIfInBounds_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_setIfInBounds_ne.h6 : ¬∀ {α : Type} {xs : Array α} {i : Nat} {a : α} {j : Nat} (hj : j < xs.size),
        GetElem.getElem (xs.setIfInBounds i a) j (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = GetElem.getElem xs j hj := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (#[0]) (0) (1) (0) hc_k0) (by
  decide)

-- Array.eraseIdx_set, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.eraseIdx_set.h6 : ¬∀ {α : Type} {xs : Array α} {i : Nat} {a : α} {hi : i < xs.size} {j : Nat}, j < (xs.set i a hi).size := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (#[0]) (0) (0) hc_k0 (1)) (by
  decide)

-- Array.set_eraseIdx, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.set_eraseIdx.h6 : ¬∀ {α : Type} {xs : Array α} {i : Nat} {w : i < xs.size} {j : Nat} {a : α}, j < (xs.eraseIdx i w).size := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (#[0]) (0) hc_k0 (0) (0)) (by
  decide +kernel)

-- List.getElem_set_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_set_ne.h4 : ¬∀ {α : Type} {l : List α} {i j : Nat} {a : α} (hj : j < (l.set i a).length),
        GetElem.getElem (l.set i a) j hj = GetElem.getElem l j (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) ([0]) (0) (0) (1) hc_k0) (by
  decide)

-- Array.back_filterMap_of_eq_some, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.back_filterMap_of_eq_some.h6 : ¬∀ {α β : Type} {f : α → Option β} {xs : Array α} {w : 0 < xs.size} {b : β}, f (xs.back w) = Option.some b := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (fun _ => none : Nat → Option Nat) (#[0]) hc_k0 (0)) (by
  decide)

-- List.zipWithM_cons_cons, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.zipWithM_cons_cons.h9 : Not
      (∀ {m : Type → Type} {α β γ : Type} {a : α} {as : List α} {b : β} {bs : List β} [inst : Monad m] {f : α → β → m γ},
        @Eq (m (List γ)) (@List.zipWithM m inst α β γ f (@List.cons α a as) (@List.cons β b bs))
          (@Bind.bind m (@Monad.toBind m inst) γ (List γ) (f a b) fun (__do_lift : γ) =>
            @Bind.bind m (@Monad.toBind m inst) (List γ) (List γ) (@List.zipWithM m inst α β γ f as bs)
              fun (__do_lift_1 : List γ) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List γ)
                (@List.cons γ __do_lift __do_lift_1))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun (a a_1 : Nat) =>
      @Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide)

-- Option.elimM_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.elimM_map.h5 : Not
      (∀ {m : Type → Type} {α β γ : Type} [inst : Monad m] (x : m α) (f : α → Option β) (y : m γ) (z : β → m γ),
        @Eq (m γ)
          (@Option.elimM m β γ inst
            (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) α (Option β) f x) y z)
          (@Bind.bind m (@Monad.toBind m inst) α γ x fun (__do_lift : α) => @Option.elim β (m γ) (f __do_lift) y z)) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun _ => none : Nat → Option Nat) (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (a : Nat) =>
      @Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide)

-- List.max_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.max_cons.h2 : ¬∀ {α : Type} [inst : Max α] {a : α} {l : List α} {h : a :: l ≠ []},
        (a :: l).max h = l.max?.elim a fun (x : α) => Max.max a x := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (⟨fun a b => a - b⟩ : Max Nat) (1) ([0, 1]) hc_k0) (by
  decide)

-- List.min_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min_cons.h2 : ¬∀ {α : Type} [inst : Min α] {a : α} {l : List α} {h : a :: l ≠ []},
        (a :: l).min h = l.min?.elim a fun (x : α) => Min.min a x := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (⟨fun a b => a - b⟩ : Min Nat) (1) ([0, 1]) hc_k0) (by
  decide)

-- Vector.forIn_eq_foldlM, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.forIn_eq_foldlM.h5 : ¬∀ {m : Type → Type} {α : Type} {n : Nat} {β : Type} [inst : Monad m] {xs : Vector α n} (f : α → β → m (ForInStep β))
        (init : β),
        ForIn.forIn xs init f =
          ForInStep.value <$>
            Vector.foldlM
              (fun (b : ForInStep β) (a : α) =>
                match b with
                | ForInStep.yield b => f a b
                | ForInStep.done b => Pure.pure (ForInStep.done b))
              (ForInStep.yield init) xs := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (0) (Nat) ({ pure := some, bind := Option.bind, map := fun _ _ => none } : Monad Option) (#v[]) (fun (a a_1 : Nat) => Option.none) (0)) (by
  decide)

-- List.zipWithM'_eq_zipWithM, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.zipWithM'_eq_zipWithM.h5 : ¬∀ {m : Type → Type} {α β γ : Type} [inst : Monad m] {f : α → β → m γ} {l : List α} {l' : List β},
        List.zipWithM' f l l' = List.zipWithM f l l' := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) ([0]) ([0])) (by
  decide)

-- List.foldlM_cons_eq_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldlM_cons_eq_append.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {f : α → m β} {as : List α} {b : β} {bs : List β},
        List.foldlM (fun (acc : List β) (a : α) => (fun (x : β) => x :: acc) <$> f a) (b :: bs) as =
          (fun (x : List β) => x ++ b :: bs) <$>
            List.foldlM (fun (acc : List β) (a : α) => (fun (x : β) => x :: acc) <$> f a) [] as := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, 0)) ([]) (0) ([])) (by
  decide)

-- List.scanrM_concat, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.scanrM_concat.h7 : Not
      (∀ {m : Type → Type} {α β : Type} {init : β} {xs : List α} {x : α} [inst : Monad m] {f : α → β → m β},
        @Eq (m (List β))
          (@List.scanrM m α β inst f init
            (@HAppend.hAppend (List α) (List α) (List α) (@instHAppendOfAppend (List α) (@List.instAppend α)) xs
              (@List.cons α x (@List.nil α))))
          (@Bind.bind m (@Monad.toBind m inst) β (List β) (f x init) fun (__do_lift : β) =>
            @Bind.bind m (@Monad.toBind m inst) (List β) (List β) (@List.scanrM m α β inst f __do_lift xs)
              fun (__do_lift : List β) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List β)
                (@HAppend.hAppend (List β) (List β) (List β) (@instHAppendOfAppend (List β) (@List.instAppend β)) __do_lift
                  (@List.cons β init (@List.nil β))))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun (a a_1 : Nat) =>
      @Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide)

-- List.filterMapM_loop_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.filterMapM_loop_eq.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {f : α → m (Option β)} {l : List α} {acc : List β},
        List.filterMapM.loop f l acc = (fun (x : List β) => acc.reverse ++ x) <$> List.filterMapM.loop f l [] := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, Option.none)) ([]) ([])) (by
  decide)

-- List.scanlM_pure, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.scanlM_pure.h5 : Not
      (∀ {m : Type → Type} {β α : Type} {init : β} [inst : Monad m] {f : β → α → β} {as : List α},
        @Eq (m (List β))
          (@List.scanlM m β α inst
            (fun (x1 : β) (x2 : α) => @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) β (f x1 x2)) init
            as)
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List β) (@List.scanl β α f init as))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun a b => a - b : Nat → Nat → Nat) (@List.nil Nat)) (by
  decide)

-- List.flatMapM_toArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.flatMapM_toArray.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {l : List α} {f : α → m (Array β)},
        Array.flatMapM f l.toArray = List.toArray <$> List.flatMapM (fun (a : α) => Array.toList <$> f a) l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) ([]) (fun (a : Nat) => (0, #[]))) (by
  decide)

-- List.mapIdxM_toArray, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mapIdxM_toArray.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {l : List α} {f : Nat → α → m β},
        Array.mapIdxM f l.toArray = List.toArray <$> List.mapIdxM f l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) ([]) (fun (a a_1 : Nat) => (0, 0))) (by
  decide)

-- List.ofFnM_pure, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ofFnM_pure.h3 : Not
      (∀ {m : Type → Type} {α : Type} [inst : Monad m] {n : Nat} {f : Fin n → α},
        @Eq (m (List α))
          (@List.ofFnM m α n inst fun (i : Fin n) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) α (f i))
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List α) (@List.ofFn α n f))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
      @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide)

-- List.findM?_eq_findSomeM?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findM?_eq_findSomeM?.h3 : ¬∀ {m : Type → Type} {α : Type} [inst : Monad m] {p : α → m Bool} {as : List α},
        List.findM? p as =
          List.findSomeM?
            (fun (a : α) => do
              let __do_lift ← p a
              Pure.pure (if __do_lift = Bool.true then Option.some a else Option.none))
            as := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, Bool.false)) ([0])) (by
  decide)

-- Vector.ofFnM_succ', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.ofFnM_succ'.h4 : Not
      (∀ {m : Type → Type} {α : Type} {n : Nat} [inst : Monad m]
        {f :
          Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            m α},
        @Eq
          (m
            (Vector α
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@Vector.ofFnM m α
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            inst f)
          (@Bind.bind m (@Monad.toBind m inst) α
            (Vector α
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (f
              (@OfNat.ofNat
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) (nat_lit 0))))
            fun (a : α) =>
            @Bind.bind m (@Monad.toBind m inst) (Vector α n)
              (Vector α
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Vector.ofFnM m α n inst fun (i : Fin n) => f (@Fin.succ n i)) fun (as : Vector α n) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                (Vector α
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Vector.cast
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  α (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)
                  (@HAppend.hAppend (Vector α (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Vector α n)
                    (Vector α
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n))
                    (@Vector.instHAppendHAddNat α (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
                    (@Vector.mk α (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@List.toArray α (@List.cons α a (@List.nil α))) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind))
                    as)))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun
        (a :
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide +kernel)

