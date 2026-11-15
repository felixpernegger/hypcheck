import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- List.min_map_eq_min, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min_map_eq_min.h10 : ¬∀ {α β : Type} [inst : Min α] [inst_1 : LE α] [inst_2 : DecidableLE α] [inst_3 : Std.LawfulOrderLeftLeaningMin α]
        [inst_4 : Min β] [inst_5 : LE β] [inst_6 : DecidableLE β] [inst_7 : Std.IsLinearPreorder β] {f : α → β},
        (∀ (a b : α), f a ≤ f b ↔ a ≤ b) → ∀ {l : List α} {h : l ≠ []}, (List.map f l).min (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = f (l.min h) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (instMinNat) (instLENat) (Nat.decLe) _ (⟨fun a b => a - b⟩ : Min Nat) (instLENat) (Nat.decLe) _ (fun n => n + 1 : Nat → Nat) hc_k0 ([0, 1]) hc_k1) (by
  simp)

-- List.min_map_eq_min, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min_map_eq_min.h12 : ¬∀ {α β : Type} [inst : Min α] [inst_1 : LE α] [inst_2 : DecidableLE α] [inst_3 : Std.LawfulOrderLeftLeaningMin α]
        [inst_4 : Min β] [inst_5 : LE β] [inst_6 : DecidableLE β] [inst_7 : Std.IsLinearPreorder β]
        [inst_8 : Std.LawfulOrderLeftLeaningMin β] {f : α → β} {l : List α} {h : l ≠ []},
        (List.map f l).min (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = f (l.min h) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Bool) (instMinNat) (instLENat) (Nat.decLe) _ (Bool.instMin) (Bool.instLE) (Bool.instDecidableLe) (@Std.IsLinearPreorder.mk (Bool) (Bool.instLE) (@Std.IsPreorder.mk (Bool) (Bool.instLE) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (@Std.LawfulOrderLeftLeaningMin.mk (Bool) (Bool.instMin) (Bool.instLE) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : Nat → Bool) ([0, 1]) hc_k0) (by
  decide)

-- List.minOn_eq_min, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minOn_eq_min.h5 : ¬∀ {α β : Type} [inst : Min α] [inst_1 : LE α] [inst_2 : DecidableLE α] [inst_3 : LE β] [inst_4 : DecidableLE β]
        {f : α → β} {l : List α} {h : l ≠ []}, (∀ (a b : α), f a ≤ f b ↔ a ≤ b) → List.minOn f l h = l.min h := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (⟨fun a b => a - b⟩ : Min Nat) (instLENat) (Nat.decLe) (instLENat) (Nat.decLe) (fun n => n + 1 : Nat → Nat) ([1, 0]) hc_k0 hc_k1) (by
  (simp <;> decide))

-- List.minOn_eq_min, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minOn_eq_min.h11 : ¬∀ {α β : Type} [inst : Min α] [inst_1 : LE α] [inst_2 : DecidableLE α] [inst_3 : Std.LawfulOrderLeftLeaningMin α]
        [inst_4 : LE β] [inst_5 : DecidableLE β] {f : α → β} {l : List α} {h : l ≠ []}, List.minOn f l h = l.min h := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (instMinNat) (instLENat) (Nat.decLe) _ (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (fun (a b : Nat) => (a % 2).decLe (b % 2)) (fun n => n + 1 : Nat → Nat) ([0, 1]) hc_k0) (by
  decide)

-- List.maxIdxOn_eq_iff, hypothesis 6: necessary
/- FAILED: 7:2: failed to synthesize
  Decidable
    ¬∀ (hc_k0 : [0, 1] ≠ []),
        List.maxIdxOn (fun x => 0) [0, 1] hc_k0 = 1 ↔
          ∃ h, (∀ (j : Nat), j < [0, 1].length → 0 ≤ 0) ∧ ∀ (j : Nat), j < 1 → 0 < 0

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 1060:30: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.53 < List.length ?m.52
of sort `Prop` in the application
  (fun {α} {xs} {i} hi j x a =>
      Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl true)))
        (Lean.Omega.Constraint.combine_sat'
          (Lean.Omega.tidy_sat
            (Lean.Omega.combo_sat' { lowerBound := some 1, upperBound := none }
              { lowerBound := none, upperBound := so | 7:161: `grind` has failed, use `+verbose` to obtain diagnostic information | 10:198: `grind` has failed, use `+verbose` to obtain diagnostic information | 6:60: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 150:37: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 8:113: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 53:91: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maxIdxOn_eq_iff.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [inst_3 : Std.IsLinearPreorder β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat},
        List.maxIdxOn f xs h = i ↔
          ∃ (h : i < xs.length),
            (∀ (j : Nat) (x : j < xs.length), f xs[j] ≤ f xs[i]) ∧ ∀ (j : Nat) (x : j < i), f xs[j] < f xs[i] := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (⟨fun a b => a ≤ b⟩ : LT Nat) _ (fun _ => 0 : Nat → Nat) ([0, 1]) hc_k0 (1)) (by
  decide)
-/

-- Vector.insertIdx_eraseIdx_of_le, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Vector.insertIdx_eraseIdx_of_le.h7.{u} : ∀ {α : Type u} {a : α} {n i j : Nat} {xs : Vector α n}, i < n → j ≤ i → j ≤ n - 1 := by
  (intros; omega)

-- Array.forIn_eq_foldlM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.forIn_eq_foldlM.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {xs : Array α} (f : α → β → m (ForInStep β)) (init : β),
        ForIn.forIn xs init f =
          ForInStep.value <$>
            Array.foldlM
              (fun (b : ForInStep β) (a : α) =>
                match b with
                | ForInStep.yield b => f a b
                | ForInStep.done b => Pure.pure (ForInStep.done b))
              (ForInStep.yield init) xs := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) ({ pure := some, bind := Option.bind, map := fun _ _ => none } : Monad Option) (#[]) (fun (a a_1 : Nat) => Option.none) (0)) (by
  decide)

-- List.filterMapM_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.filterMapM_cons.h6 : Not
      (∀ {m : Type → Type} {α β : Type} {a : α} {l : List α} [inst : Monad m] {f : α → m (Option β)},
        @Eq (m (List β)) (@List.filterMapM m inst α β f (@List.cons α a l))
          (@Bind.bind m (@Monad.toBind m inst) (Option β) (List β) (f a) fun (__do_lift : Option β) =>
            @List.filterMapM_cons.match_1 β (fun (__do_lift : Option β) => m (List β)) __do_lift
              (fun (_ : Unit) => @List.filterMapM m inst α β f l) fun (b : β) =>
              @Bind.bind m (@Monad.toBind m inst) (List β) (List β) (@List.filterMapM m inst α β f l)
                fun (__do_lift : List β) =>
                @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List β) (@List.cons β b __do_lift))) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (fun (a : Nat) =>
      @Prod.mk Nat (Option Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) (by
  decide)

-- Vector.toArray_mapIdxM, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toArray_mapIdxM.h5 : ¬∀ {m : Type → Type} {α : Type} {n : Nat} {β : Type} [inst : Monad m] {xs : Vector α n} {f : Nat → α → m β},
        Vector.toArray <$> Vector.mapIdxM f xs = Array.mapIdxM f xs.toArray := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (0) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (#v[]) (fun (a a_1 : Nat) => (0, 0))) (by
  decide)

-- Array.toList_filterMapM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.toList_filterMapM.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {xs : Array α} {f : α → m (Option β)},
        Array.toList <$> Array.filterMapM f xs = List.filterMapM f xs.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (#[]) (fun (a : Nat) => (0, Option.none))) (by
  decide)

-- List.mapM'_eq_mapM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mapM'_eq_mapM.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {f : α → m β} {l : List α}, List.mapM' f l = List.mapM f l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, 0)) ([0])) (by
  decide)

-- Array.toList_mapM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.toList_mapM.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {f : α → m β} {xs : Array α},
        Array.toList <$> Array.mapM f xs = List.mapM f xs.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, 0)) (#[])) (by
  decide)

-- Array.erase_eq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.erase_eq_iff.h3 : ¬∀ {α : Type} [inst : BEq α] {ys : Array α} {a : α} {xs : Array α},
        xs.erase a = ys ↔
          ¬a ∈ xs ∧ xs = ys ∨ ∃ (as : Array α), ∃ (bs : Array α), ¬a ∈ as ∧ xs = as.push a ++ bs ∧ ys = as ++ bs := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (#[]) (0) (#[1])) (by
  (simp <;> decide))

-- Vector.toList_ofFnM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toList_ofFnM.h4 : ¬∀ {m : Type → Type} {n : Nat} {α : Type} [inst : Monad m] {f : Fin n → m α},
        Vector.toList <$> Vector.ofFnM f = List.ofFnM f := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (1) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Fin 1) => (0, 0))) (by
  decide +kernel)

-- Array.ofFnM_succ', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.ofFnM_succ'.h4 : Not
      (∀ {m : Type → Type} {α : Type} {n : Nat} [inst : Monad m]
        {f :
          Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            m α},
        @Eq (m (Array α))
          (@Array.ofFnM m α
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            inst f)
          (@Bind.bind m (@Monad.toBind m inst) α (Array α)
            (f
              (@OfNat.ofNat
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0))))
            fun (a : α) =>
            @Bind.bind m (@Monad.toBind m inst) (Array α) (Array α)
              (@Array.ofFnM m α n inst fun (i : Fin n) => f (@Fin.succ n i)) fun (as : Array α) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (Array α)
                (@HAppend.hAppend (Array α) (Array α) (Array α) (@instHAppendOfAppend (Array α) (@Array.instAppend α))
                  (@List.toArray α (@List.cons α a (@List.nil α))) as))) := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := some, bind := Option.bind, map := fun _ _ => none } : Monad Option) (fun
        (a :
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide +kernel)

-- Std.Iterators.PostconditionT.run_pure, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Iterators.PostconditionT.run_pure.h2 : Not
      (∀ {m : Type → Type} [inst : Monad m] {α : Type} {x : α},
        @Eq (m α)
          (@Std.Iterators.PostconditionT.run m inst α
            (@Pure.pure (Std.Iterators.PostconditionT m)
              (@Applicative.toPure (Std.Iterators.PostconditionT m)
                (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
              α x))
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) α x)) := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Prod Nat α) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide)

