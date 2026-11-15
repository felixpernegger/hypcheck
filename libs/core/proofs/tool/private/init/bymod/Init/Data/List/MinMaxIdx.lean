import Init

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
-- _private.Init.Data.List.MinMaxIdx.0.List.combineMinIdxOn_assoc, hypothesis 13: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.combineMinIdxOn_assoc.h13 : ¬∀ {β α : Type} {xys : List α} [inst : LE β] [inst_1 : DecidableLE β] [inst : Std.IsLinearPreorder β]
        {xs ys zs : List α} {i j k : Nat} {f : α → β}, j < ys.length → k < zs.length → xys = xs ++ ys → i < xs.length := fun hc_h => absurd (@hc_h (Nat) (Nat) _ (instLENat) (Nat.decLe) _ ([]) ([0]) ([0]) (0) (0) (0) (fun n => n + 1 : Nat → Nat) (by
  decide) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.combineMinIdxOn_assoc, hypothesis 14: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.combineMinIdxOn_assoc.h14 : ¬∀ {β α : Type} {xys : List α} [inst : LE β] [inst_1 : DecidableLE β] [inst : Std.IsLinearPreorder β]
        {xs ys zs : List α} {i j k : Nat} {f : α → β}, i < xs.length → k < zs.length → xys = xs ++ ys → j < ys.length := fun hc_h => absurd (@hc_h (Nat) (Nat) _ (instLENat) (Nat.decLe) _ ([0]) ([]) ([0]) (0) (0) (0) (fun n => n + 1 : Nat → Nat) (by
  decide) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.combineMinIdxOn_assoc, hypothesis 15: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.combineMinIdxOn_assoc.h15 : ¬∀ {β α : Type} {xys : List α} [inst : LE β] [inst_1 : DecidableLE β] [inst : Std.IsLinearPreorder β]
        {xs ys zs : List α} {i j k : Nat} {f : α → β}, i < xs.length → j < ys.length → xys = xs ++ ys → k < zs.length := fun hc_h => absurd (@hc_h (Nat) (Nat) _ (instLENat) (Nat.decLe) _ ([0]) ([0]) ([]) (0) (0) (0) (fun n => n + 1 : Nat → Nat) (by
  decide) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.combineMinIdxOn_lt', hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.combineMinIdxOn_lt'.h10 : ¬∀ {β α : Type} [inst : LE β] [inst : DecidableLE β] (f : α → β) {xs ys : List α} (zs : List α) {i j : Nat},
        j < ys.length → zs = xs ++ ys → i < xs.length := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (fun n => n + 1 : Nat → Nat) ([]) ([0]) _ (0) (0) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.combineMinIdxOn_lt', hypothesis 11: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.combineMinIdxOn_lt'.h11 : ¬∀ {β α : Type} [inst : LE β] [inst : DecidableLE β] (f : α → β) {xs ys : List α} (zs : List α) {i j : Nat},
        i < xs.length → zs = xs ++ ys → j < ys.length := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (fun n => n + 1 : Nat → Nat) ([0]) ([]) _ (0) (0) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.combineMinIdxOn_lt', hypothesis 12: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.combineMinIdxOn_lt'.h12 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] (f : α → β) {xs ys : List α} (zs : List α) {i j : Nat}
        (hi : i < xs.length) (hj : j < ys.length), List.combineMinIdxOn f i j hi hj < zs.length := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (fun n => n + 1 : Nat → Nat) ([0]) ([0]) ([]) (0) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.minIdxOn_cons_aux, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.minIdxOn_cons_aux.h8 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst : Std.IsLinearPreorder β] {x : α} {xs : List α}
        {f : α → β}, xs ≠ [] := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) _ (0) ([]) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.minIdxOn_eq_go_drop, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.minIdxOn_eq_go_drop.h7 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst : Std.IsLinearPreorder β] {f : α → β} {xs : List α}
        {k : Nat}, xs ≠ [] := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) _ (fun n => n + 1 : Nat → Nat) ([]) (0)) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.exists_getElem_eq_of_drop_eq_cons, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.exists_getElem_eq_of_drop_eq_cons.h5 : ¬∀ {α : Type} {xs : List α} {k : Nat} {y : α} {ys : List α}, ∃ (hlt : k < xs.length), xs[k] = y := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0) ([])) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.minIdxOn_append_aux, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.minIdxOn_append_aux.h8 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst : Std.IsLinearPreorder β] {xs ys : List α} {f : α → β},
        ys ≠ [] → xs ≠ [] := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) _ ([]) ([0]) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.minIdxOn_append_aux, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.minIdxOn_append_aux.h9 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst : Std.IsLinearPreorder β] {xs ys : List α} {f : α → β},
        xs ≠ [] → ys ≠ [] := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) _ ([0]) ([]) (fun n => n + 1 : Nat → Nat) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.combineMinIdxOn_lt, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.combineMinIdxOn_lt.h9 : ¬∀ {β α : Type} [inst : LE β] [inst : DecidableLE β] (f : α → β) {xs ys : List α} {i j : Nat},
        j < ys.length → i < xs.length := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (fun n => n + 1 : Nat → Nat) ([]) ([0]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.combineMinIdxOn_lt, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.combineMinIdxOn_lt.h10 : ¬∀ {β α : Type} [inst : LE β] [inst : DecidableLE β] (f : α → β) {xs ys : List α} {i j : Nat},
        i < xs.length → j < ys.length := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (fun n => n + 1 : Nat → Nat) ([0]) ([]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.minIdxOn.go_lt_length_add, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.minIdxOn.go_lt_length_add.h9 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x : α} {i j : Nat} {xs : List α},
        List.minIdxOn.go f x i j xs < xs.length + j := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (fun n => n + 1 : Nat → Nat) (0) (0) (0) ([])) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.minIdxOn.go_eq_of_forall_le, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.minIdxOn.go_eq_of_forall_le.h9 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x : α} {i j : Nat} {xs : List α},
        List.minIdxOn.go f x i j xs = i := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (fun n => n + 1 : Nat → Nat) (1) (0) (1) ([0])) (by
  decide +kernel)

-- _private.Init.Data.List.MinMaxIdx.0.List.take_succ_eq_append_of_drop_eq_cons, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.take_succ_eq_append_of_drop_eq_cons.h5 : ¬∀ {α : Type} {xs : List α} {k : Nat} {y : α} {ys : List α}, List.take (k + 1) xs = List.take k xs ++ [y] := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0) ([])) (by
  decide +kernel)

