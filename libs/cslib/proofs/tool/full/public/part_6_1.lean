import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LTS.Execution.mk, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.mk.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s t : State} {μs : List Label} {ss : List State},
        ss.length = μs.length + 1 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) ([]) ([])) (by
  decide +kernel)

-- Cslib.LTS.TraceEq.exists_tr_of_tr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.TraceEq.exists_tr_of_tr.h9 : ¬∀ {State₁ Label State₂ : Type} {s₁ : State₁} {s₂ : State₂} {μ : Label} {s₁' : State₁} {lts₁ : Cslib.LTS State₁ Label}
        {lts₂ : Cslib.LTS State₂ Label}, lts₁.Tr s₁ μ s₁' → ∃ (s₂' : State₂), lts₂.Tr s₂ μ s₂' := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (0) (0) (Bool.false) (0) ({ Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }) ({ Tr := fun (a : ℕ) (a_1 : Bool) (x : ℕ) => False : Cslib.LTS ℕ Bool }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Cslib.SKI.unique_normal_form, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.unique_normal_form.h3 : ¬∀ {x y z : Cslib.SKI}, Relation.ReflTransGen Cslib.SKI.Red x z → y.RedexFree → z.RedexFree → y = z := fun hc_h => absurd (@hc_h (.S : Cslib.SKI) (.K : Cslib.SKI) (.S : Cslib.SKI) (by
  rfl) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Cslib.SKI.unique_normal_form, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.unique_normal_form.h4 : ¬∀ {x y z : Cslib.SKI}, Relation.ReflTransGen Cslib.SKI.Red x y → y.RedexFree → z.RedexFree → y = z := fun hc_h => absurd (@hc_h (.S : Cslib.SKI) (.S : Cslib.SKI) (.K : Cslib.SKI) (by
  rfl) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Cslib.SKI.unique_normal_form, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.unique_normal_form.h5 : ¬∀ {x y z : Cslib.SKI},
        Relation.ReflTransGen Cslib.SKI.Red x y → Relation.ReflTransGen Cslib.SKI.Red x z → z.RedexFree → y = z := fun hc_h => absurd (@hc_h (.app .I .I : Cslib.SKI) (.app .I .I : Cslib.SKI) (.I : Cslib.SKI) (by
  rfl) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  decide +kernel)

-- Cslib.SKI.unique_normal_form, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.unique_normal_form.h6 : ¬∀ {x y z : Cslib.SKI},
        Relation.ReflTransGen Cslib.SKI.Red x y → Relation.ReflTransGen Cslib.SKI.Red x z → y.RedexFree → y = z := fun hc_h => absurd (@hc_h (.app .I .I : Cslib.SKI) (.I : Cslib.SKI) (.app .I .I : Cslib.SKI) (by
  (repeat' constructor) <;> done) (by
  rfl) (by
  decide)) (by
  decide +kernel)

-- Relation.RelatesInSteps.head, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.head.h6 : ¬∀ {α : Type} {r : α → α → Prop} (t t' t'' : α) (n : ℕ),
        Relation.RelatesInSteps r t' t'' n → Relation.RelatesInSteps r t t'' (n + 1) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (0) (0) (by
  simp)) (by
  nofun)

-- Relation.RelatesInSteps.head, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.RelatesInSteps.head.h7.inst : ¬Relation.RelatesInSteps (fun (a b : ℕ) => a < b) 0 0 (0 + 1) := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.RelatesInSteps.head.h7.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Relation.RelatesInSteps.head.h7 : ¬∀ {α : Type} {r : α → α → Prop} (t t' t'' : α) (n : ℕ), r t t' → Relation.RelatesInSteps r t t'' (n + 1) := fun hc_h => HypCheckProof.Relation.RelatesInSteps.head.h7.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (0) (1) (0) (0) HypCheckProof.Relation.RelatesInSteps.head.h7.prem0)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans.h6 : ¬∀ {Var : Type} {M N P : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], P.Standard N → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans.h7 : ¬∀ {Var : Type} {M N P : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.Standard P → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- List.IsChainFromTo.cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.cons.h6 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b c : α},
        List.IsChainFromTo r chain b c → List.IsChainFromTo r (a :: chain) a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (0) (0) (by
  simp)) (by
  simp)

-- List.IsChainFromTo.cons, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChainFromTo.cons.h7.inst : ¬List.IsChainFromTo (fun (a b : ℕ) => a < b) [0] 0 1 := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChainFromTo.cons.h7.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChainFromTo.cons.h7 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b c : α}, r a b → List.IsChainFromTo r (a :: chain) a c := fun hc_h => HypCheckProof.List.IsChainFromTo.cons.h7.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) ([]) (0) (1) (1) HypCheckProof.List.IsChainFromTo.cons.h7.prem0)

-- List.IsChainFromTo.reflTransGen_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.reflTransGen_of_mem.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a : α} {b : α} {x : α}, x ∈ chain → Relation.ReflTransGen r a x := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (1) (0) (0) (by
  decide)) (by
  nofun)

-- Relation.RelatesWithinSteps.apply_le_apply_add, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.RelatesWithinSteps.apply_le_apply_add.h5.inst : ¬(fun (b : Bool) => if b = Bool.true then 1 else 0) Bool.true ≤
        (fun (b : Bool) => if b = Bool.true then 1 else 0) Bool.false + 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.RelatesWithinSteps.apply_le_apply_add.h5.prem0 : ∀ (a b : Bool),
      True → (fun (b : Bool) => if b = Bool.true then 1 else 0) b ≤ (fun (b : Bool) => if b = Bool.true then 1 else 0) a + 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Relation.RelatesWithinSteps.apply_le_apply_add.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {m : ℕ} (h : α → ℕ), (∀ (a b : α), r a b → h b ≤ h a + 1) → h b ≤ h a + m := fun hc_h => HypCheckProof.Relation.RelatesWithinSteps.apply_le_apply_add.h5.inst (@hc_h (Bool) (fun (x x_1 : Bool) => True) (Bool.false) (Bool.true) (0) (fun (b : Bool) => if b = Bool.true then 1 else 0) HypCheckProof.Relation.RelatesWithinSteps.apply_le_apply_add.h5.prem0)

-- Relation.RelatesWithinSteps.apply_le_apply_add, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesWithinSteps.apply_le_apply_add.h7 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {m : ℕ}, Relation.RelatesWithinSteps r a b m → ∀ (h : α → ℕ), h b ≤ h a + m := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (2) (1) (by
  (repeat' constructor) <;> done) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Cslib.ωSequence.append_left_right_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.append_left_right_injective.h5 : ¬∀ {α : Type} (l1 l2 : List α) (s1 s2 : Cslib.ωSequence α), l1.length = l2.length → l1 = l2 ∧ s1 = s2 := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([1]) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (by
  decide)) (by
  simp)

-- Cslib.ωSequence.flatten_get_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.flatten_get_add.h5 : ¬∀ {α : Type} [inst : Inhabited α] (ls : Cslib.ωSequence (List α)) {n k : ℕ},
        (∀ (n : ℕ), 0 < (ls n).length) → k < (ls n).length := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ({ get := fun (n : ℕ) => [n] : Cslib.ωSequence (List ℕ) }) (0) (1) (by
  simp)) (by
  decide +kernel)

-- Cslib.Automata.TwoWayNACfg.eta, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Cslib.Automata.TwoWayNACfg.eta.h5.der.{u_1, u_2} : ∀ {State : Type u_1} {Symbol : Type u_2} {input : List Symbol} {c : Cslib.Automata.TwoWayNACfg State Symbol},
      c.input = input → ↑c.pos < input.length + 1 := by
  (intros; grind)
theorem HypCheckProof.Cslib.Automata.TwoWayNACfg.eta.h5.{u_1, u_2} : ∀ {State : Type u_1} {Symbol : Type u_2} {input : List Symbol} {c : Cslib.Automata.TwoWayNACfg State Symbol}
      (h : c.input = input),
      { input := input, state := c.state,
          pos := (⟨↑c.pos, HypCheckProof.Cslib.Automata.TwoWayNACfg.eta.h5.der h⟩ : Fin (input.length + 1)) :
          Cslib.Automata.TwoWayNACfg State Symbol } =
        c := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Cslib.Automata.TwoWayNACfg.eta hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Cslib.Automata.TwoWayNACfg.eta.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_le.h4 : ¬∀ {Var : Type} (M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (i j : ℕ),
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.LcAt i M = Bool.true →
          Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.LcAt j M = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_le.h5 : ¬∀ {Var : Type} (M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (i j : ℕ),
        i ≤ j → Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.LcAt j M = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.isAbs_r, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.isAbs_r.h4 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {n : ℕ}, M.IsAbs → N.IsAbs := fun hc_h => absurd (@hc_h (ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.isAbs_r, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.isAbs_r.h5 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {n : ℕ},
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq n M N → N.IsAbs := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.cbn_step_trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.cbn_step_trans.h4 : ¬∀ {Var : Type} {M N P : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, P.Standard N → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.Algorithms.Lean.TimeM.sorted_merge, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Algorithms.Lean.TimeM.sorted_merge.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l1 l2 : List α},
        Cslib.Algorithms.Lean.TimeM.IsSorted l2 →
          Cslib.Algorithms.Lean.TimeM.IsSorted (Cslib.Algorithms.Lean.TimeM.merge l1 l2).ret := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([1, 0]) ([]) (by
  decide)) (by
  simp)

-- Cslib.Algorithms.Lean.TimeM.sorted_merge, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Algorithms.Lean.TimeM.sorted_merge.h5 : ¬∀ {α : Type} [inst : LinearOrder α] {l1 l2 : List α},
        Cslib.Algorithms.Lean.TimeM.IsSorted l1 →
          Cslib.Algorithms.Lean.TimeM.IsSorted (Cslib.Algorithms.Lean.TimeM.merge l1 l2).ret := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) ([1, 0]) (by
  decide)) (by
  simp)

-- Cslib.Automata.NA.hist_run_proj, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.NA.hist_run_proj.h8 : ¬∀ {Symbol State Hist : Type} {na : Cslib.Automata.NA State Symbol} {start' : State → Hist}
        {tr' : State × Hist → Symbol → State → Hist} {xs : Cslib.ωSequence Symbol} {ss : Cslib.ωSequence (State × Hist)},
        na.Run xs (Cslib.ωSequence.map Prod.fst ss) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) ({ Tr := fun (a : Bool) (a_1 : ℕ) (b : Bool) => b = Bool.true, start := {b : Bool | b = Bool.true} :
      Cslib.Automata.NA Bool ℕ }) (fun b => if b then 1 else 0 : Bool → ℕ) (fun (a : Bool × ℕ) (a_1 : ℕ) (b : Bool) => if b = Bool.true then 1 else 0) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) ({ get := fun (a : ℕ) => (Bool.false, 0) : Cslib.ωSequence (Bool × ℕ) })) (by
  nofun)

-- List.IsChain.isChainFromTo_of_ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.isChainFromTo_of_ne_nil.h3 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} (h_ne_nil : chain ≠ []),
        List.IsChainFromTo r chain (chain.head h_ne_nil) (chain.getLast h_ne_nil) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) hc_k0) (by
  simp)

-- List.IsChain.isChainFromTo_of_ne_nil, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.isChainFromTo_of_ne_nil.h4 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α}, List.IsChain r chain → chain ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (by
  decide)) (by
  decide +kernel)

-- Cslib.LTS.Execution.nonEmpty_states, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.nonEmpty_states.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        ss ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_cbn_step, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_cbn_step.h3 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, N.LC → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LTS.Execution.to_mTr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.to_mTr.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.MTr s μs t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (1) ([])) (by
  simp)

-- Cslib.FinFun.congrFinFun, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FinFun.congrFinFun.h5 : Not
      (∀ {β α : Type} [inst : Zero β] {f g : @Cslib.FinFun α β inst} (a : α),
        @Eq β (@DFunLike.coe (@Cslib.FinFun α β inst) α (fun (x : α) => β) (@Cslib.FinFun.instFunLike β α inst) f a)
          (@DFunLike.coe (@Cslib.FinFun α β inst) α (fun (x : α) => β) (@Cslib.FinFun.instFunLike β α inst) g a)) := fun hc_h => absurd (@hc_h (Nat) (Bool) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (@Cslib.FinFun.mk Bool Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
      (fun (x : Bool) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool))
      (@of_decide_eq_true
        (∀ {a : Bool},
          Iff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
            (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
        (@Bool.instDecidableForallOfDecidablePred
          (fun (a : Bool) =>
            Iff
              (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
              (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
          fun (a : Bool) =>
          @instDecidableIff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
            (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
            (@Finset.decidableMem Bool instDecidableEqBool a
              (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)))
            (@instDecidableNot
              (@Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
              (instDecidableEqNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ {a : Bool},
                Iff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
                  (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
              (@Bool.instDecidableForallOfDecidablePred
                (fun (a : Bool) =>
                  Iff
                    (@Membership.mem Bool (Finset Bool)
                      (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                      (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
                    (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
                fun (a : Bool) =>
                @instDecidableIff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
                  (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                  (@Finset.decidableMem Bool instDecidableEqBool a
                    (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)))
                  (@instDecidableNot
                    (@Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                    (instDecidableEqNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 0)
                        (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Cslib.FinFun.mk Bool Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
      (fun (b : Bool) =>
        @ite Nat (@Eq Bool b Bool.true) (instDecidableEqBool b Bool.true)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true)
      (@of_decide_eq_true
        (∀ {a : Bool},
          Iff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
            (@Ne Nat
              (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
        (@Bool.instDecidableForallOfDecidablePred
          (fun (a : Bool) =>
            Iff
              (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
              (@Ne Nat
                (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
          fun (a : Bool) =>
          @instDecidableIff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
            (@Ne Nat
              (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
            (@Finset.decidableMem Bool instDecidableEqBool a
              (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true))
            (@instDecidableNot
              (@Eq Nat
                (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
              (instDecidableEqNat
                (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ {a : Bool},
                Iff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
                  (@Ne Nat
                    (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
              (@Bool.instDecidableForallOfDecidablePred
                (fun (a : Bool) =>
                  Iff
                    (@Membership.mem Bool (Finset Bool)
                      (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                      (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
                    (@Ne Nat
                      (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
                fun (a : Bool) =>
                @instDecidableIff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
                  (@Ne Nat
                    (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                  (@Finset.decidableMem Bool instDecidableEqBool a
                    (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true))
                  (@instDecidableNot
                    (@Eq Nat
                      (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                    (instDecidableEqNat
                      (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat Nat (nat_lit 0)
                        (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (Bool.true)) (by
  decide +kernel)

-- List.orderedInsertM_pure, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.orderedInsertM_pure.h3 : Not
      (∀ {α : Type} {m : Type → Type} [inst : Monad m] (r : α → α → Bool) (a : α) (xs : List α),
        @Eq (m (List α))
          (@List.orderedInsertM α m inst
            (fun (x y : α) => @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) Bool (r x y)) a xs)
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List α)
            (@List.orderedInsert α (fun (x1 x2 : α) => @Eq Bool (r x1 x2) Bool.true)
              (fun (a b : α) => instDecidableEqBool (r a b) Bool.true) a xs))) := fun hc_h => absurd (@hc_h (Nat) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun a b => a < b : Nat → Nat → Bool) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.lc_r, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.lc_r.h3 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, N.LC := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Relation.instLeftEuclideanElemValMemSet, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.instLeftEuclideanElemValMemSet.h2 : ¬∀ {α : Type} {r : α → α → Prop} (s : Set α), Relation.LeftEuclidean fun (a b : ↑s) => r ↑a ↑b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ({n : ℕ | n % 2 = 0})) (by
  exact fun hc_c =>
    absurd
      (hc_c.leftEuclidean (a :=
        ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }))
        (b :=
        ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }))
        (c :=
        ((⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Relation.Convergent.unique_normal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Convergent.unique_normal.h2 : ¬∀ {α : Type} {r : α → α → Prop} (a : α), ∃! n : α, Relation.ReflTransGen r a n ∧ Relation.Normal r n := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (Bool.false)) (by
  simp)

-- Relation.Convergent.to_normalizing, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Convergent.to_normalizing.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Relation.Normalizing r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop)) (by
  simp)

-- Relation.LeftEuclidean.rightEuclidean_swap, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.LeftEuclidean.rightEuclidean_swap.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Relation.RightEuclidean fun (a b : α) => r b a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.rightEuclidean (a := (1 : ℕ)) (b := (0 : ℕ)) (c := (0 : ℕ))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.eq_nil_ofIsEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_nil_ofIsEmpty.h1 : ¬∀ {α : Type} (xl : List α), xl = [] := fun hc_h => absurd (@hc_h (ℕ) ([0])) (by
  decide +kernel)

-- Relation.Terminating.isNormalizing, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Terminating.isNormalizing.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Relation.Normalizing r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop)) (by
  simp)

