import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- _private.Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_foldl_alter, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TreeMap.getElem?_foldl_alter.h9 : ¬∀ {K V : Type} [inst : Ord K] [inst_1 : Std.TransOrd K] [inst_2 : Std.LawfulEqOrd K] {k : K} {f : K → V → V → V}
        {l : List (K × V)} {init : Std.TreeMap K V Ord.compare},
        (List.foldl
              (fun (acc : Std.TreeMap K V Ord.compare) (kv : K × V) =>
                acc.alter kv.fst (Option.insertOrMerge (f kv.fst) kv.snd))
              init l)[k]? =
          Option.pairMerge f init[k]? (List.find? (fun (kv : K × V) => (Ord.compare kv.fst k).isEq) l) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instOrdNat) _ _ (0) (fun (a a_1 b : Nat) => a_1 + b) ([(0, 0), (0, 1)]) (Std.TreeMap.ofList [] Ord.compare)) (by
  decide +kernel)

-- _private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.map_eq_append_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.HeapLang.map_eq_append_cons.h7 : ¬∀ {α β : Type} {f : α → β} {l : List α} {xs : List β} {y : β} {ys : List β},
        ∃ (la : List α), ∃ (a : α), ∃ (lb : List α), l = la ++ a :: lb ∧ List.map f la = xs ∧ f a = y ∧ List.map f lb = ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n + 1 : Nat → Nat) ([]) ([]) (0) ([])) (by
  simp)

-- _private.Iris.Std.GenSets.0.Iris.Std.FiniteSet.foldl_cons_comm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Std.FiniteSet.foldl_cons_comm.h3 : ¬∀ {A β : Type} {f : β → A → β} (l : List A) (init : β) (a : A), List.foldl f (f init a) l = f (List.foldl f init l) a := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun (a : Bool) (n : Nat) => n % 2 == 0) ([0]) (Bool.false) (1)) (by
  decide +kernel)

-- _private.Iris.Algebra.Mra.0.Iris.Mra.rel_iff_of_toMra_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Mra.rel_iff_of_toMra_eq.h4 : ¬∀ {α : Type} {R : α → α → Prop} {a b : α} (c : α), R c a ↔ R c b := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (1) (0)) (by
  decide +kernel)

-- _private.Iris.BI.BigOp.BigSepList.0.Iris.BI.list_split, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.BI.list_split.h4 : ¬∀ {A : Type} {l : List A} {i : Nat} {x : A}, l = List.take i l ++ x :: List.drop (i + 1) l := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0)) (by
  decide +kernel)

-- _private.Iris.ProgramLogic.AbstractLangCompleteness.0.Iris.ProgramLogic.qp_div_ofPNat_succ_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ProgramLogic.qp_div_ofPNat_succ_nil.h3 : ¬∀ {α : Type} (qc : Iris.Qp) {l : List α}, qc.divide_even (l.length + 1) (Nat.succ_pos l.length) = qc := fun hc_h => absurd (@hc_h (Nat) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ([0])) (by
  decide +kernel)

