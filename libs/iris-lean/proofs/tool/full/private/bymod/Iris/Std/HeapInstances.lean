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

