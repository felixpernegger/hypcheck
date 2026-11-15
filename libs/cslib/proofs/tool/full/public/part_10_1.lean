import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst.h7 : ¬∀ {Var : Type} {M M' N N' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], N.Standard N' → N.LC → N'.LC → (M.open' N).Standard (M'.open' N') := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LTS.Deterministic.eq_of_mTr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Deterministic.eq_of_mTr.h7 : ¬∀ {State Label : Type} {s1 : State} {μs : List Label} {s2 s2' : State} {lts : Cslib.LTS State Label},
        lts.MTr s1 μs s2 → lts.MTr s1 μs s2' → s2 = s2' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) ([0]) (0) (1) ({ Tr := fun (a a_1 b : ℕ) => a_1 ≤ b : Cslib.LTS ℕ ℕ }) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Cslib.LTS.Execution.drop, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.drop.h9 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss → ∀ (n : ℕ), n < ss.length := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([0]) (by
  (repeat' constructor) <;> done) (1)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.weaken, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.weaken.h8 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var]
        {Γ Δ Θ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var} {τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}
        {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var},
        (Γ ++ Θ ++ Δ).Wf → Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing (Γ ++ Θ ++ Δ) t τ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) ([]) ([]) ([]) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.abs .top (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_injective.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] (x : Var) (M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        x ∉ M'.fv →
          M.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) =
              M'.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) →
            M = M' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_injective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_injective.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] (x : Var) (M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        x ∉ M.fv →
          M.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) =
              M'.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) →
            M = M' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_injective, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_injective.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] (x : Var) (M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        x ∉ M.fv → x ∉ M'.fv → M = M' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (1) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_open_out, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_open_out.h8 : ¬∀ {Var : Type} {M M' N N' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var] (L : Finset Var), M'.Parallel N' → (M.open' M').Parallel (N.open' N') := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (∅ : Finset ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Relation.RelatesWithinSteps.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesWithinSteps.trans.h7 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α} {n₁ n₂ : ℕ},
        Relation.RelatesWithinSteps r b c n₂ → Relation.RelatesWithinSteps r a c (n₁ + n₂) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0) (0) (0) (0) (by
  simp)) (by
  simp)

-- Relation.RelatesWithinSteps.trans, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesWithinSteps.trans.h8 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α} {n₁ n₂ : ℕ},
        Relation.RelatesWithinSteps r a b n₁ → Relation.RelatesWithinSteps r a c (n₁ + n₂) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (1) (0) (0) (by
  simp)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_subst_cong_l, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_subst_cong_l.h7 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var] {x : Var}
        (s s' N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        N.LC → Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta s[x := N] s'[x := N] := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.open_subst_var, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.open_subst_var.h7 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        {δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {Y X : Var}
        (σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var),
        δ.LC →
          (σ.open' (Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.fvar Y))[X := δ] =
            σ[X := δ].open' (Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.fvar Y) := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.Automata.TwoWayNA.mTr_toCfgNA_of_mTr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.TwoWayNA.mTr_toCfgNA_of_mTr.h7 : ¬∀ {State Symbol : Type} {input : List Symbol} {a : Cslib.Automata.NA.FinAcc State Symbol} {s s' : State}
        {pre : List Symbol}, a.MTr s pre s' → pre <+: input := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([]) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.NA.FinAcc ℕ ℕ }) (0) (1) ([0]) (by
  simp)) (by
  decide +kernel)

-- Cslib.Automata.TwoWayNA.mTr_toCfgNA_of_mTr, hypothesis 8: necessary
/- FAILED: 39:93: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  (0 + ?m.157).blt' 0 = true
in the application
  eagerReduce (Eq.refl true) | 262:20: Application type mismatch: The argument
  Symbol
has type
  Type
of sort `Type 1` but is expected to have type
  ?m.3 <+: ?m.2
of sort `Prop` in the application
  (fun {Symbol} {input pre} hpre =>
      Eq.mpr
        (id
          (Eq.trans (Lean.Grind.Nat.lt_eq pre.length (input.length + 1))
            (Nat.Simproc.add_le_add_le pre.length input.length (of_decide_eq_true (Eq.refl true)))))
        (Classical.byContradiction
          (Lean.Grind.intro_with_eq (¬pre.length ≤ input.length) (inp | 8:166: `grind` failed
case grind
State Symbol : Type
input : List Symbol
a : Cslib.Automata.NA.FinAcc State Symbol
s s' : State
pre : List Symbol
h : input.length + 1 ≤ pre.length
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] input.length + 1 ≤ pre.length
  [eqc] True propositions
    [prop] input.length + 1 ≤ pre.length
  [ematch] E-matching patterns
    [thm] Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le: [@LE.le `[ℕ] `[instLENat] `[2] #1]
    [thm] Cslib.Algorithms.Lean.Time | 26:144: `grind` failed
case grind
State Symbol : Type
input : List Symbol
a : Cslib.Automata.NA.FinAcc State Symbol
s s' : State
pre : List Symbol
h : input.length + 1 ≤ pre.length
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] input.length + 1 ≤ pre.length
  [eqc] True propositions
    [prop] input.length + 1 ≤ pre.length
  [ematch] E-matching patterns
    [thm] Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le: [@LE.le `[ℕ] `[instLENat] `[2] #1]
    [thm] Cslib.Algorithms.Lean.Time | 41:93: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  (0 + ?m.181).blt' 0 = true
in the application
  eagerReduce (Eq.refl true) | 68:32: (deterministic) timeout at `elaborator`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 2:77: don't know how to synthesize implicit argument `α`
  @List.IsPrefix ?m.3 [] []
context:
⊢ Type ?u.5

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be | 56:144: `grind` failed
case grind
State Symbol : Type
input : List Symbol
a : Cslib.Automata.NA.FinAcc State Symbol
s s' : State
pre : List Symbol
h : input.length + 1 ≤ pre.length
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] input.length + 1 ≤ pre.length
  [eqc] True propositions
    [prop] input.length + 1 ≤ pre.length
  [ematch] E-matching patterns
    [thm] Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le: [@LE.le `[ℕ] `[instLENat] `[2] #1]
    [thm] Cslib.Algorithms.Lean.Time
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.TwoWayNA.mTr_toCfgNA_of_mTr.h8 : ¬∀ {State Symbol : Type} {input : List Symbol} {a : Cslib.Automata.NA.FinAcc State Symbol} {s s' : State}
        {pre : List Symbol} (hpre : pre <+: input),
        (a.toTwoWayNA.toCfgNA input).MTr { input := input, state := s, pos := 0 : Cslib.Automata.TwoWayNACfg State Symbol }
          (List.map (fun (x : Symbol) => (x, SignType.pos)) pre)
          { input := input, state := s',
            pos :=
              (⟨pre.length,
                  (fun {Symbol : Type} {input pre : List Symbol} (hpre : pre <+: input) =>
                      (fun {Symbol : Type} {input pre : List Symbol} (hpre : pre <+: input) =>
                          Eq.mpr
                            (id
                              (Eq.trans (Lean.Grind.Nat.lt_eq pre.length (input.length + 1))
                                (Nat.Simproc.add_le_add_le pre.length input.length
                                  (of_decide_eq_true (Eq.refl Bool.true)))))
                            (Classical.byContradiction
                              (Lean.Grind.intro_with_eq (¬pre.length ≤ input.length) (input.length + 1 ≤ pre.length) False
                                (Nat.not_le_eq pre.length input.length) fun (h : input.length + 1 ≤ pre.length) =>
                                id
                                  (Eq.mp
                                    (Eq.trans
                                      (Eq.trans
                                        (Eq.symm
                                          (eq_true
                                            (Eq.mp (Eq.refl (pre <+: input → pre.length ≤ input.length))
                                              fun (h : pre <+: input) => List.IsPrefix.length_le h)))
                                        (Lean.Grind.imp_eq_of_eq_true_left (eq_true hpre)))
                                      (Lean.Grind.Order.eq_trans_false
                                        (Nat.ToInt.le_eq (Eq.refl ↑pre.length) (Eq.refl ↑input.length))
                                        (Lean.Grind.Order.eq_trans_false
                                          (id
                                            (Lean.Grind.CommRing.le_norm_expr
                                              (Lean.RArray.branch 1 (Lean.RArray.leaf ↑input.length)
                                                (Lean.RArray.leaf ↑pre.length))
                                              (Lean.Grind.CommRing.Expr.var 1) (Lean.Grind.CommRing.Expr.var 0)
                                              (Lean.Grind.CommRing.Expr.var 1)
                                              ((Lean.Grind.CommRing.Expr.var 0).add (Lean.Grind.CommRing.Expr.intCast 0))
                                              (eagerReduce (Eq.refl Bool.true))))
                                          (Lean.Grind.Order.le_eq_false_of_le_k (eagerReduce (Eq.refl Bool.true))
                                            (Lean.Grind.Order.eq_mp
                                              (id
                                                (Lean.Grind.CommRing.le_norm_expr
                                                  (Lean.RArray.branch 1 (Lean.RArray.leaf ↑input.length)
                                                    (Lean.RArray.leaf ↑pre.length))
                                                  ((Lean.Grind.CommRing.Expr.var 0).add (Lean.Grind.CommRing.Expr.num 1))
                                                  (Lean.Grind.CommRing.Expr.var 1) (Lean.Grind.CommRing.Expr.var 0)
                                                  ((Lean.Grind.CommRing.Expr.var 1).add
                                                    (Lean.Grind.CommRing.Expr.intCast (-1)))
                                                  (eagerReduce (Eq.refl Bool.true))))
                                              (of_eq_true
                                                (Lean.Grind.Order.eq_trans_true'
                                                  (Nat.ToInt.le_eq
                                                    (Nat.ToInt.add_congr (Eq.refl ↑input.length)
                                                      (Nat.ToInt.natCast_ofNat 1))
                                                    (Eq.refl ↑pre.length))
                                                  (eq_true h))))))))
                                    True.intro))))
                        hpre)
                    hpre⟩ :
                Fin (input.length + 1)) :
            Cslib.Automata.TwoWayNACfg State Symbol } := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (ℕ) ([]) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.NA.FinAcc ℕ ℕ }) (0) (1) ([]) hc_k0) (by
  simp)
-/

-- Turing.Storage.FitsIn.cell_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.Storage.FitsIn.cell_le.h5 : ¬∀ {k : ℕ} {State Symbol : Type} {x : Turing.Storage Symbol State k} {w : Fin k → ℕ} (j : Fin k) (z : ℤ),
        x.workTapes j z ≠ Option.none → z.natAbs ≤ w j := fun hc_h => absurd (@hc_h (1) (ℕ) (ℕ) ({ state := Option.none, workTapes := fun (i : Fin 1) (a : ℤ) => Option.some 0, workTapePos := fun (i : Fin 1) => 0 :
      Turing.Storage ℕ ℕ 1 }) (fun (a : Fin 1) => 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Turing.Storage.FitsIn.cell_le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.Storage.FitsIn.cell_le.h8 : ¬∀ {k : ℕ} {State Symbol : Type} {x : Turing.Storage Symbol State k} {w : Fin k → ℕ},
        x.FitsIn w → ∀ (j : Fin k) (z : ℤ), z.natAbs ≤ w j := fun hc_h => absurd (@hc_h (1) (ℕ) (ℕ) ({ state := Option.none, workTapes := fun (i : Fin 1) (a : ℤ) => Option.none, workTapePos := fun (i : Fin 1) => 0 :
      Turing.Storage ℕ ℕ 1 }) (fun (a : Fin 1) => 0) ((@Turing.Storage.FitsIn.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat) (Nat) (@Turing.Storage.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Option.none Nat)
      (fun (i : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (a : Int) => @Option.none Nat)
      fun (i : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
      @OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
      @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)))) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (1)) (by
  decide +kernel)

-- Relation.RelatesInSteps.apply_le_apply_add, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.RelatesInSteps.apply_le_apply_add.h5.inst : ¬(fun (b : Bool) => if b = Bool.true then 1 else 0) Bool.true ≤
        (fun (b : Bool) => if b = Bool.true then 1 else 0) Bool.false + 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.RelatesInSteps.apply_le_apply_add.h5.prem0 : ∀ (a b : Bool),
      True → (fun (b : Bool) => if b = Bool.true then 1 else 0) b ≤ (fun (b : Bool) => if b = Bool.true then 1 else 0) a + 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Relation.RelatesInSteps.apply_le_apply_add.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {m : ℕ} (h : α → ℕ), (∀ (a b : α), r a b → h b ≤ h a + 1) → h b ≤ h a + m := fun hc_h => HypCheckProof.Relation.RelatesInSteps.apply_le_apply_add.h5.inst (@hc_h (Bool) (fun (x x_1 : Bool) => True) (Bool.false) (Bool.true) (0) (fun (b : Bool) => if b = Bool.true then 1 else 0) HypCheckProof.Relation.RelatesInSteps.apply_le_apply_add.h5.prem0)

-- Relation.RelatesInSteps.apply_le_apply_add, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.apply_le_apply_add.h7 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {m : ℕ}, Relation.RelatesInSteps r a b m → ∀ (h : α → ℕ), h b ≤ h a + m := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (2) (1) (by
  (repeat' constructor) <;> done) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec_neq_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec_neq_eq.h6 : ¬∀ {Var : Type} {X Y : ℕ} {σ τ γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec Y τ σ =
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec X γ
              (Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec Y τ σ) →
          σ = Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec X γ σ := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  rfl)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec_neq_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec_neq_eq.h7 : ¬∀ {Var : Type} {X Y : ℕ} {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}
        {τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        X ≠ Y → σ = Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec X γ σ := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  decide)) (by
  nofun)

-- List.IsChainFromTo.drop, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.drop.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a : α} {b : α} {i : ℕ} (hi : i < chain.length),
        List.IsChainFromTo r (List.drop i chain) chain[i] b := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0, 1]) (0) (0) (0) hc_k0) (by
  simp)

-- List.IsChainFromTo.drop, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.drop.h7 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α},
        List.IsChainFromTo r chain a b → ∀ {i : ℕ}, i < chain.length := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (0) (by
  simp) (1)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.lc_r, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.lc_r.h6 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {n : ℕ} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.LC → N.LC := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.lc_r, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.lc_r.h7 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {n : ℕ} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq n M N → N.LC := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.to_standard, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.to_standard.h6 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {n : ℕ} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.LC → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.to_standard, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.to_standard.h7 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {n : ℕ} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq n M N → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- List.IsChain.relatesInSteps_getElem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.relatesInSteps_getElem.h6 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α}, List.IsChain r chain → ∀ (i k : ℕ), i + k < chain.length := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (by
  decide) (0) (0)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken_head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken_head.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        Cslib.HasWellFormed.wf (Γ ++ Δ) → Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf (Γ ++ Δ) σ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.listFullBeta_cons_r, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.listFullBeta_cons_r.h4 : ¬∀ {Var : Type} {Ns Ns' l : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)},
        (∀ M ∈ l, M.LC) → Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ListFullBeta (l ++ Ns) (l ++ Ns') := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) ([]) (by
  decide)) (by
  nofun)

-- Cslib.Algorithms.Lean.TimeM.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Algorithms.Lean.TimeM.ext.h4 : ¬∀ {T α : Type} {x y : Cslib.Algorithms.Lean.TimeM T α}, x.time = y.time → x = y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ ret := 0, time := 0 : Cslib.Algorithms.Lean.TimeM ℕ ℕ }) ({ ret := 1, time := 0 : Cslib.Algorithms.Lean.TimeM ℕ ℕ }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Cslib.Algorithms.Lean.TimeM.ext, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Algorithms.Lean.TimeM.ext.h5 : ¬∀ {T α : Type} {x y : Cslib.Algorithms.Lean.TimeM T α}, x.ret = y.ret → x = y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ ret := 0, time := 0 : Cslib.Algorithms.Lean.TimeM ℕ ℕ }) ({ ret := 0, time := 1 : Cslib.Algorithms.Lean.TimeM ℕ ℕ }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Cslib.LTS.pairViaLang_split, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.pairViaLang_split.h8 : ¬∀ {Symbol State : Type} {lts : Cslib.LTS State Symbol} {s0 s2 : State} {xs1 xs2 : List Symbol} {via : Set State},
        ∃ (s1 : State),
          xs1 ∈ lts.pairViaLang via s0 s1 ∧ xs2 ∈ lts.pairLang s1 s2 ∨
            xs1 ∈ lts.pairLang s0 s1 ∧ xs2 ∈ lts.pairViaLang via s1 s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) ([]) ([]) ({x : ℕ | False})) (by
  simp)

-- Cslib.LTS.Execution.reverse, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.reverse.h7 : ¬∀ {State Label : Type} {s : State} {μs : List Label} {s' : State} {ss : List State} {lts : Cslib.LTS State Label},
        lts.reverse.Execution s' μs.reverse s ss.reverse := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) ([]) (0) ([]) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ })) (by
  nofun)

-- Cslib.LTS.Execution.head, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.head.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  nofun)

-- Cslib.LTS.Execution.getLast, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.getLast.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.invert_steps_abs, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.invert_steps_abs.h5 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        {s t : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        ∃ (s' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
          Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta s.abs s'.abs ∧ t = s'.abs := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  (simp <;> omega))

-- List.IsChainFromTo.isChain, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.isChain.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α}, List.IsChain r chain := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) (0) (0)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.open_subst_intro, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.open_subst_intro.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var}
        (δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var),
        γ.open' δ = (γ.open' (Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.fvar X))[X := δ] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ)) (by
  nofun)

-- Nat.count_notMem_range_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_notMem_range_pos.h1 : Not
      (∀ {f : Nat → Nat},
        ∀ n ∉ @Set.range Nat Nat f,
          @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Nat.count (fun (x : Nat) => @Membership.mem Nat (Set Nat) (@Set.instMembership Nat) (@Set.range Nat Nat f) x)
              (fun (a : Nat) =>
                Classical.propDecidable (@Membership.mem Nat (Set Nat) (@Set.instMembership Nat) (@Set.range Nat Nat f) a))
              n)) := fun hc_h => absurd (@hc_h (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  simp)) (by
  decide +kernel)

-- Nat.count_notMem_range_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_notMem_range_pos.h3 : Not
      (∀ {f : Nat → Nat},
        @Eq Nat (f (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          ∀ (n : Nat),
            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@Nat.count
                (fun (x : Nat) => @Membership.mem Nat (Set Nat) (@Set.instMembership Nat) (@Set.range Nat Nat f) x)
                (fun (a : Nat) =>
                  Classical.propDecidable
                    (@Membership.mem Nat (Set Nat) (@Set.instMembership Nat) (@Set.range Nat Nat f) a))
                n)) := fun hc_h => absurd (@hc_h (fun _ => 0 : Nat → Nat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- List.IsChainFromTo.ne_nil, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.ne_nil.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α}, chain ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (0)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.subst_fresh, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.subst_fresh.h4 : ¬∀ {Var : Type} [inst : DecidableEq Var] {γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var}
        (δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var), γ = γ[X := δ] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ)) (by
  nofun)

-- List.IsChainFromTo.getElem_length_sub_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.getElem_length_sub_one.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α}, List.IsChainFromTo r chain a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (0)) (by
  nofun)

-- List.insertionSortM_pure, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insertionSortM_pure.h3 : Not
      (∀ {α : Type} {m : Type → Type} [inst : Monad m] (xs : List α) (r : α → α → Bool),
        @Eq (m (List α))
          (@List.insertionSortM α m inst
            (fun (x y : α) => @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) Bool (r x y)) xs)
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List α)
            (@List.insertionSort α (fun (x1 x2 : α) => @Eq Bool (r x1 x2) Bool.true)
              (fun (a b : α) => instDecidableEqBool (r a b) Bool.true) xs))) := fun hc_h => absurd (@hc_h (Nat) (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)) (fun a b => a < b : Nat → Nat → Bool)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.of_env_ty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.of_env_ty.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Γ σ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0)) (by
  nofun)

-- List.IsChainFromTo.getElem_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.getElem_zero.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α}, List.IsChainFromTo r chain a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (0)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.le_countRedexes, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.le_countRedexes.h5 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {i : ℕ} [inst : Cslib.HasFresh Var], i ≤ N.countRedexes := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (1) (Cslib.instHasFreshNat)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress.h5 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var} {τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        t.Value ∨ ∃ (t' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var), t.Red t' := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ)) (by
  nofun)

-- Relation.ReflTransGen.relatesInSteps, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflTransGen.relatesInSteps.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, ∃ (n : ℕ), Relation.RelatesInSteps r a b n := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0)) (by
  nofun)

-- Cslib.ωSequence.forall_flatten_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.forall_flatten_iff.h3 : ¬∀ {α : Type} [inst : Inhabited α] {ls : Cslib.ωSequence (List α)} (p : α → Prop),
        (∀ (n : ℕ), p (ls.flatten n)) ↔ ∀ (k : ℕ), List.Forall p (ls k) := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ({ get := fun (x : ℕ) => [] : Cslib.ωSequence (List ℕ) }) (fun _ => False : ℕ → Prop)) (by
  simp)

-- Cslib.BitString.flipBlock_erase, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Cslib.BitString.flipBlock_erase.h3.gneg : ∀ {n : ℕ} {B : Finset (Fin n)} {i : Fin n},
      i ∉ B →
        ∀ (x : Cslib.BitString n),
          Cslib.BitString.flipBlock (B.erase i) x = Function.update (Cslib.BitString.flipBlock B x) i (x i) := by
  (intros; simp_all; done)
theorem HypCheckProof.Cslib.BitString.flipBlock_erase.h3 : ∀ {n : ℕ} {B : Finset (Fin n)} {i : Fin n} (x : Cslib.BitString n),
      Cslib.BitString.flipBlock (B.erase i) x = Function.update (Cslib.BitString.flipBlock B x) i (x i) := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @Cslib.BitString.flipBlock_erase hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.Cslib.BitString.flipBlock_erase.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)

-- Cslib.QueryComplexity.forces_iff_isCertificate_support, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.QueryComplexity.forces_iff_isCertificate_support.h4 : ¬∀ {n : ℕ} {f : Cslib.BooleanFunction n} {x : Cslib.BitString n} {C : Cslib.QueryComplexity.PartialAssignment n},
        Cslib.QueryComplexity.Forces f C (f x) ↔ Cslib.QueryComplexity.IsCertificate f x (Cslib.QueryComplexity.support C) := fun hc_h => absurd (@hc_h (1) (fun (a : Cslib.BitString 1) => if a = fun (a : Fin 1) => Bool.false then Bool.false else Bool.true) (fun (a : Fin 1) => Bool.false) (fun (a : Fin 1) => Option.some Bool.true)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiSubst_fvar_fresh, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiSubst_fvar_fresh.h4 : ¬∀ {Var : Type} [inst : DecidableEq Var] (E : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Env Var) (x : Var),
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiSubst E
            (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) =
          Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([(⟨1, Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar 0⟩ :
        (_ : ℕ) × Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)]) (1)) (by
  decide +kernel)

-- Cslib.ωSequence.take_append_of_le_length, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.take_append_of_le_length.h4 : ¬∀ {α : Type} (n : ℕ) (x : List α) (a : Cslib.ωSequence α), Cslib.ωSequence.take n (x ++ω a) = List.take n x := fun hc_h => absurd (@hc_h (ℕ) (1) ([]) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ })) (by
  decide +kernel)

-- Cslib.ωSequence.get_append_right', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.get_append_right'.h4 : ¬∀ {α : Type} {xl : List α} {xs : Cslib.ωSequence α} {k : ℕ}, (xl ++ω xs) k = xs (k - xl.length) := fun hc_h => absurd (@hc_h (ℕ) ([0]) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0)) (by
  decide +kernel)

-- Relation.ReflGen.symmGen_symm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflGen.symmGen_symm.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.ReflGen (Relation.SymmGen r) b a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (0) (1)) (by
  nofun)

-- Cslib.Automata.εNA.FinAcc.toSingleStartAccept_tr_start, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.εNA.FinAcc.toSingleStartAccept_tr_start.h4 : ¬∀ {State Symbol : Type} {a : Cslib.Automata.εNA.FinAcc State Symbol} {s : State},
        a.toSingleStartAccept.Tr (Sum.inl Bool.false) Option.none (Sum.inr s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a : ℕ) (a_1 : Option ℕ) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.εNA.FinAcc ℕ ℕ }) (1)) (by
  nofun)

-- Relation.RelatesInSteps.zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.zero.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, a = b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (1)) (by
  decide +kernel)

-- Relation.RelatesWithinSteps.single, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesWithinSteps.single.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.RelatesWithinSteps r a b 1 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaNormal.app_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaNormal.app_inv.h3 : ¬∀ {Var : Type} {L M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, ¬L.IsAbs ∧ L.BetaNormal ∧ M.BetaNormal := fun hc_h => absurd (@hc_h (ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaNormal.abs_open, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaNormal.abs_open.h3 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {x : Var},
        (M.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x)).BetaNormal := fun hc_h => absurd (@hc_h (ℕ) (.app (.abs (.bvar 0)) (.fvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0)) (by
  nofun)

-- Relation.SN.normalizable, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.SN.normalizable.h3 : ¬∀ {α : Type} {r : α → α → Prop} {x : α}, Relation.Normalizable r x := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (Bool.false)) (by
  simp)

