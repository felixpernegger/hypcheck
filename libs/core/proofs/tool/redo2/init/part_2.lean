import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- List.apply_maxOn_lt_apply_getElem_of_lt_maxIdxOn, hypothesis 6: necessary
/- FAILED: 3:81: failed to prove index is valid, possible solutions:
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
              { lowerBound := none | 3:200: `grind` has failed, use `+verbose` to obtain diagnostic information | 6:153: `grind` has failed, use `+verbose` to obtain diagnostic information | 4:2: Tactic `decide` proved that the proposition
  ¬∀ (h : [1, 0] ≠ []) (hk : 0 < List.maxIdxOn (fun n => n + 1) [1, 0] h),
      (fun n => n + 1) [1, 0][0] < (fun n => n + 1) (List.maxOn (fun n => n + 1) [1, 0] h)
is false | 122:29: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 6:2: Tactic `decide` proved that the proposition
  ¬∀ (h : [1, 0] ≠ []),
      0 < List.maxIdxOn (fun n => n + 1) [1, 0] h →
        (fun n => n + 1) [1, 0][0] < (fun n => n + 1) (List.maxOn (fun n => n + 1) [1, 0] h)
is false | 62:153: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.apply_maxOn_lt_apply_getElem_of_lt_maxIdxOn.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [inst_3 : Std.IsLinearPreorder β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {k : Nat} (hk : k < List.maxIdxOn f xs h), f xs[k] < f (List.maxOn f xs h) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (fun (a b : Nat) => (a % 2).decLe (b % 2)) (instLTNat) (@Std.IsLinearPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (fun n => n + 1 : Nat → Nat) ([1, 0]) hc_k0 (0) hc_k1) (by
  decide)
-/

-- Array.getElem_replace_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_replace_of_ne.h2 : ¬∀ {α : Type} [inst : BEq α] {a b : α} {xs : Array α} {i : Nat} {h : i < xs.size},
        GetElem.getElem xs i h ≠ a → GetElem.getElem (xs.replace a b) i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = GetElem.getElem xs i h := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) (#[1]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- Array.getElem_replace_of_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_replace_of_ne.h8 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a b : α} {xs : Array α} {i : Nat} {h : i < xs.size},
        GetElem.getElem (xs.replace a b) i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = GetElem.getElem xs i h := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (instBEqOfDecidableEq) _ (0) (1) (#[0]) (0) hc_k0) (by
  decide +kernel)

-- Array.set_comm, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.set_comm.h7 : ¬∀ {α : Type} (a b : α) {i j : Nat} {xs : Array α} {hi : i < xs.size}, i ≠ j → j < (xs.set i a hi).size := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (0) (0) (0) (1) (#[0]) hc_k0 hc_k1) (by
  decide)

-- Array.set_comm, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.set_comm.h8 : ¬∀ {α : Type} (a b : α) {i j : Nat} {xs : Array α} {hi : i < xs.size} {hj : j < (xs.set i a hi).size},
        (xs.set i a hi).set j b hj = (xs.set j b (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)).set i a (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (0) (1) (0) (0) (#[0]) hc_k0 hc_k1) (by
  decide)

-- List.getElem_replace_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_replace_of_ne.h4 : ¬∀ {α : Type} [inst : BEq α] {a b : α} {l : List α} {i : Nat} {h : i < l.length},
        GetElem.getElem l i h ≠ a → GetElem.getElem (l.replace a b) i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = GetElem.getElem l i h := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) ([1]) (0) hc_k0 hc_k1) (by
  decide)

-- List.getElem_replace_of_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_replace_of_ne.h8 : ¬∀ {α : Type} [inst : BEq α] {a b : α} [inst_1 : LawfulBEq α] {l : List α} {i : Nat} {h : i < l.length},
        GetElem.getElem (l.replace a b) i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = GetElem.getElem l i h := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (instBEqOfDecidableEq) (0) (1) _ ([0]) (0) hc_k0) (by
  decide)

-- Array.set_eraseIdx_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.set_eraseIdx_le.h6 : ¬∀ {α : Type} {xs : Array α} {i : Nat} {w : i < xs.size} {j : Nat} {a : α} (hj : j < (xs.eraseIdx i w).size),
        (xs.eraseIdx i w).set j a hj = (xs.set (j + 1) a (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)).eraseIdx i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (#[0, 1]) (1) hc_k0 (0) (1) hc_k1) (by
  decide +kernel)

-- Array.set_eraseIdx_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.set_eraseIdx_le.h7 : ¬∀ {α : Type} {xs : Array α} {i : Nat} {w : i < xs.size} {j : Nat} {a : α}, i ≤ j → j < (xs.eraseIdx i w).size := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (#[0]) (0) hc_k0 (0) (0) hc_k1) (by
  decide +kernel)

-- Array.insertIdx_eraseIdx_of_le, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Array.insertIdx_eraseIdx_of_le.h6.{u} : ∀ {α : Type u} {a : α} {i j : Nat} {as : Array α} (w₁ : i < as.size), j ≤ i → j ≤ (as.eraseIdx i w₁).size := by
  (intros; grind)

-- Option.get_merge, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.get_merge.h5 : ¬∀ {α : Type} {o o' : Option α} {f : α → α → α} {i : α} {h : (Option.merge f o o').isSome = Bool.true},
        (Option.merge f o o').get h = f (o.getD i) (o'.getD i) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Option.none) (Option.some 0) (fun a b => a - b : Nat → Nat → Nat) (1) hc_k0) (by
  decide)

-- List.getElem_modify_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_modify_ne.h5 : ¬∀ {α : Type} (f : α → α) {i j : Nat} (l : List α) (h' : j < (l.modify i f).length),
        GetElem.getElem (l.modify i f) j h' = GetElem.getElem l j (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (fun n => n + 1 : Nat → Nat) (0) (0) ([0]) hc_k0) (by
  decide)

-- Vector.le_iff_exists, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.le_iff_exists.h4 : ¬∀ {α : Type} {n : Nat} [inst : LT α] [inst_1 : Std.Asymm fun (x1 x2 : α) => x1 < x2] {xs ys : Vector α n},
        xs ≤ ys ↔ xs = ys ∨ ∃ (i : Nat), ∃ (h : i < n), (∀ (j : Nat) (hj : j < i), xs[j] = ys[j]) ∧ xs[i] < ys[i] := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a % 2 < b % 2⟩ : LT Nat) (@Std.Asymm.mk (Nat) (fun (x1 x2 : Nat) =>
      @LT.lt Nat
        (@LT.mk Nat fun (a b : Nat) =>
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        x1 x2) (by (try dsimp only);   (intros; omega))) (#v[0]) (#v[2])) (by
  decide)

-- Array.getElem_modify_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_modify_of_ne.h4 : ¬∀ {α : Type} {j : Nat} {xs : Array α} {i : Nat} (f : α → α) (hj : j < (xs.modify i f).size),
        GetElem.getElem (xs.modify i f) j hj = GetElem.getElem xs j (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (0) (#[0]) (0) (fun n => n + 1 : Nat → Nat) hc_k0) (by
  decide)

-- List.getElem_attachWith, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_attachWith.h5 : ¬∀ {α : Type} {xs : List α} {P : α → Prop} {H : ∀ (a : α), a ∈ xs → P a} {i : Nat}, i < (xs.attachWith P H).length := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) ([]) (fun n => n = 0 : Nat → Prop) hc_k0 (0)) (by
  decide)

-- String.Pos.Splits.exists_eq_singleton_append, hypothesis 4: necessary
/- FAILED: 3:3: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 3:3: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 3:3: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 3:3: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 300 in
theorem HypCheckProof.String.Pos.Splits.exists_eq_singleton_append.h4 : ¬∀ {t₁ t₂ s : String} {p : s.Pos}, p.Splits t₁ t₂ → p ≠ s.endPos := by
  (simp_all; done)
-/

-- Array.getElem_attachWith, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_attachWith.h5 : ¬∀ {α : Type} {xs : Array α} {P : α → Prop} {H : ∀ (a : α), a ∈ xs → P a} {i : Nat}, i < (xs.attachWith P H).size := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (#[]) (fun n => n = 0 : Nat → Prop) hc_k0 (0)) (by
  decide)

-- List.getElem_eraseIdx_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_eraseIdx_of_lt.h5 : ¬∀ {α : Type} {l : List α} {i j : Nat} (h : j < (l.eraseIdx i).length),
        GetElem.getElem (l.eraseIdx i) j h = GetElem.getElem l j (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) ([0, 1]) (0) (0) hc_k0) (by
  decide)

-- List.getLast_attachWith, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast_attachWith.h4 : ¬∀ {α : Type} {P : α → Prop} {xs : List α} {H : ∀ (a : α), a ∈ xs → P a}, xs.attachWith P H ≠ [] := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([]) hc_k0) (by
  decide)

-- List.head_attachWith, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head_attachWith.h4 : ¬∀ {α : Type} {P : α → Prop} {xs : List α} {H : ∀ (a : α), a ∈ xs → P a}, xs.attachWith P H ≠ [] := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([]) hc_k0) (by
  decide)

-- List.flatMapM_loop_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.flatMapM_loop_eq.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {f : α → m (List β)} {l : List α} {acc : List (List β)},
        List.flatMapM.loop f l acc = (fun (x : List β) => acc.reverse.flatten ++ x) <$> List.flatMapM.loop f l [] := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, [])) ([]) ([])) (by
  decide)

-- List.forIn_eq_foldlM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forIn_eq_foldlM.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {l : List α} (f : α → β → m (ForInStep β)) (init : β),
        ForIn.forIn l init f =
          ForInStep.value <$>
            List.foldlM
              (fun (b : ForInStep β) (a : α) =>
                match b with
                | ForInStep.yield b => f a b
                | ForInStep.done b => Pure.pure (ForInStep.done b))
              (ForInStep.yield init) l := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) ({ pure := some, bind := Option.bind, map := fun _ _ => none } : Monad Option) ([]) (fun (a a_1 : Nat) => Option.none) (0)) (by
  decide)

-- List.scanrM_eq_scanlM_reverse, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.scanrM_eq_scanlM_reverse.h6 : ¬∀ {m : Type → Type} {α β : Type} {init : β} {as : List α} [inst : Monad m] {f : α → β → m β},
        List.scanrM f init as = List.reverse <$> List.scanlM (flip f) init as.reverse := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ([]) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0))) (by
  decide)

-- Array.toList_flatMapM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.toList_flatMapM.h4 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {xs : Array α} {f : α → m (Array β)},
        Array.toList <$> Array.flatMapM f xs = List.flatMapM (fun (a : α) => Array.toList <$> f a) xs.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (#[]) (fun (a : Nat) => (0, #[]))) (by
  decide)

-- List.scanlM_nil, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.scanlM_nil.h5 : ¬∀ {m : Type → Type} {α β : Type} {init : α} [inst : Monad m] {f : α → β → m α},
        List.scanlM f init [] = Pure.pure [init] := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0))) (by
  decide)

-- Vector.map_toArray_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.map_toArray_inj.h4 : ¬∀ {m : Type → Type} {α : Type} {n : Nat} [inst : Monad m] {xs ys : m (Vector α n)},
        Vector.toArray <$> xs = Vector.toArray <$> ys ↔ xs = ys := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (0) ({ pure := some, bind := Option.bind, map := fun _ _ => none } : Monad Option) (Option.none) (Option.some #v[])) (by
  decide)

-- Std.Iterators.PostconditionT.run_attachLift, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Iterators.PostconditionT.run_attachLift.h3 : ¬∀ {m : Type → Type} [inst : Monad m] [inst_1 : MonadAttach m] {α : Type} {x : m α},
        (Std.Iterators.PostconditionT.attachLift x).run = x := fun hc_h => absurd (@hc_h (Option : Type → Type) ({ pure := some, bind := Option.bind, map := fun _ _ => none } : Monad Option) (Option.instMonadAttach) (Nat) (Option.some 0)) (by
  decide)

-- List.allM_eq_not_anyM_not, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.allM_eq_not_anyM_not.h3 : ¬∀ {m : Type → Type} {α : Type} [inst : Monad m] {p : α → m Bool} {as : List α},
        List.allM p as = (fun (x : Bool) => !x) <$> List.anyM (fun (x : α) => (fun (x : Bool) => !x) <$> p x) as := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, Bool.false)) ([])) (by
  decide)

-- List.findRevM?_toArray, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findRevM?_toArray.h3 : ¬∀ {m : Type → Type} {α : Type} [inst : Monad m] (f : α → m Bool) (l : List α),
        Array.findRevM? f l.toArray = List.findM? f l.reverse := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Nat) => (0, Bool.false)) ([0])) (by
  decide)

-- Vector.toArray_ofFnM, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toArray_ofFnM.h4 : ¬∀ {m : Type → Type} {n : Nat} {α : Type} [inst : Monad m] {f : Fin n → m α},
        Vector.toArray <$> Vector.ofFnM f = Array.ofFnM f := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (0) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a : Fin 0) => (0, 0))) (by
  decide +kernel)

-- List.filterRevM_toArray, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.filterRevM_toArray.h3 : ¬∀ {m : Type → Type} {α : Type} [inst : Monad m] {l : List α} {p : α → m Bool},
        Array.filterRevM p l.toArray = List.toArray <$> List.filterRevM p l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) ([0]) (fun (a : Nat) => (0, Bool.false))) (by
  decide)

-- Array.ofFnM_succ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.ofFnM_succ.h4 : Not
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
          (@Bind.bind m (@Monad.toBind m inst) (Array α) (Array α)
            (@Array.ofFnM m α n inst fun (i : Fin n) => f (@Fin.castSucc n i)) fun (as : Array α) =>
            @Bind.bind m (@Monad.toBind m inst) α (Array α) (f (Fin.last n)) fun (a : α) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (Array α) (@Array.push α as a))) := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := some, bind := Option.bind, map := fun _ _ => none } : Monad Option) (fun
        (a :
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide +kernel)

