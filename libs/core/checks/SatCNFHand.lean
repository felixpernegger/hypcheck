import Std
import Lean

/-!
Hand pass `SatCNF` (hand15): the 97 unresolved hypotheses of `Std.Sat.CNF.*` (`Basic`, `Sat`,
`Entails`, `Negation`, `Redundancy`, `Relabel`, `RelabelFin`) and the two `Std.Do.Spec.*_cnfClause`
loop specs. 96 necessary, 1 removable.

Reusable models (namespace `SatCNFHand`, all over `Nat` atoms):
* formulas `T` (no clauses, always sat), `F` (one empty clause, unsat), `FU = {x0}`,
  `FR = {x0}, {¬x1}` (sat, but unsat after the non-injective relabelling `fun _ => 0`);
* clauses `U = x0`, `V = x0 ∨ ¬x0` (tautology), `Clause.empty`; assignments `aT` (all true), `a0`;
* facts `T_sat`, `F_not_sat`, `F_unsat`, `V_sat`, `not_entails_T_F`, `not_entailsClause_T_empty`,
  `isNegationOf_T_empty`, `isNegationOf_F_V`, `not_entails_of`, `not_entailsClause_of`, …;
* `NB`: `Nat` with the all-false `BEq` (not lawful): `contains` is always false (`NB.contains_go`)
  and `erase` is the identity (`NB.erase_eq`);
* `literals_erase_go_any`: `Clause.erase` evaluates for every `BEq` (this makes `literals_erase`'s
  `LawfulBEq` removable); the private `where go` loops are reached with `privconst%`;
* `Std.Do` loop specs: in `Id`, the invariant "prefix is empty" (`PostCond.noThrow`) holds at the
  start and fails at the end of any nonempty loop, so the conclusion reduces to `U.literals = []`.

Removable: `LawfulBEq` of `Std.Sat.CNF.Clause.literals_erase` (`erase.go` and the filter compare with
the same `atom == lit.1 && pol == lit.2`).

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/SatCNFHand.lean`.
-/

set_option linter.unusedVariables false

open Lean Meta Elab Term in
/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

open Lean Meta Elab Term in
/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)



open Lean Meta Elab Term in
/-- `privconst% M N`: the private constant `N` of module `M` (for the `where go` loops of
`Clause.erase` and `Clause.contains`, which are private in the module system). -/
elab "privconst% " m:ident n:ident : term => do
  let pn := mkPrivateNameCore m.getId n.getId
  let c ← getConstInfo pn
  return mkConst pn (← c.levelParams.mapM fun _ => mkFreshLevelMVar)

open Std.Sat Std.Sat.CNF

namespace SatCNFHand

/-! ## Models -/

/-- Always satisfied formula (no clauses). -/
def T : CNF Nat := CNF.empty
/-- Unsatisfiable formula (one empty clause). -/
def F : CNF Nat := CNF.empty.add .empty
/-- Single unit clause `x0`. -/
def U : Clause Nat := Clause.unit 0 true
/-- Tautological clause `x0 ∨ ¬x0`. -/
def V : Clause Nat := (Clause.unit 0 true).add 0 false
/-- Formula `{x0}`. -/
def FU : CNF Nat := CNF.empty.add U
/-- Satisfiable formula `{x0}, {¬x1}` whose relabelling along `fun _ => 0` is unsatisfiable. -/
def FR : CNF Nat := (CNF.empty.add (Clause.unit 0 true)).add (Clause.unit 1 false)
/-- The all-true assignment. -/
def aT : Nat → Bool := fun _ => true

theorem T_sat (a : Nat → Bool) : Sat a T := sat_empty
theorem F_not_sat (a : Nat → Bool) : ¬ Sat a F := unsat_iff_not_sat.mp unsat_add_empty a
theorem F_unsat : Unsat F := unsat_add_empty
theorem T_not_unsat : ¬ Unsat T := not_unsat_empty
theorem V_sat (a : Nat → Bool) : Clause.Sat a V := by
  simp only [V, Clause.sat_add, Clause.sat_unit_iff]; cases a 0 <;> simp
theorem U_not_unsat : ¬ Clause.Unsat U := Clause.not_unsat_unit
theorem empty_not_sat (a : Nat → Bool) : ¬ Clause.Sat a (Clause.empty : Clause Nat) := Clause.not_sat_empty
theorem not_entails_T_F : ¬ Entails T F := fun h => F_not_sat aT (h aT (T_sat aT))
theorem not_entails_of {f g : CNF Nat} (a : Nat → Bool) (h1 : Sat a f) (h2 : ¬ Sat a g) :
    ¬ Entails f g := fun h => h2 (h a h1)
theorem not_entailsClause_of {f : CNF Nat} {c : Clause Nat} (a : Nat → Bool) (h1 : Sat a f)
    (h2 : ¬ Clause.Sat a c) : ¬ EntailsClause f c := fun h => h2 (h a h1)
theorem entails_F (g : CNF Nat) : Entails F g := fun a h => absurd h (F_not_sat a)
theorem entails_T (g : CNF Nat) : Entails g T := fun a _ => T_sat a
theorem not_entailsClause_T_empty : ¬ EntailsClause T Clause.empty :=
  fun h => empty_not_sat aT (h aT (T_sat aT))
theorem entailsClause_F (c : Clause Nat) : EntailsClause F c := fun a h => absurd h (F_not_sat a)
theorem entailsClause_V (g : CNF Nat) : EntailsClause g V := fun a _ => V_sat a
theorem isNegationOf_T_empty : IsNegationOf T Clause.empty := fun a => by simp [T_sat]
theorem not_isNegationOf_T_V : ¬ IsNegationOf T V := fun h => (h aT).mp (T_sat aT) (V_sat aT)
theorem not_isNegationOf_F_empty : ¬ IsNegationOf F Clause.empty :=
  fun h => F_not_sat aT ((h aT).mpr (empty_not_sat aT))
theorem isNegationOf_F_V : IsNegationOf F V := fun a => by simp [F_not_sat, V_sat]
theorem U_mem_FU : U ∈ FU := by simp [FU]
theorem FU_sat : Sat aT FU := by simp [FU, U, aT]
theorem varMem_FU : VarMem 0 FU := by simp [FU, U, CNF.VarMem_add]
theorem not_varMem_F (v : Nat) : ¬ VarMem v F := by simp [F, CNF.VarMem_add, not_VarMem_empty]

/-! ## Std.Sat.CNF.Basic -/

-- `Std.Sat.CNF.Clause.ext`: the empty clause and x0 have different literals.
theorem Clause_ext_3 : ¬ drop0% Std.Sat.CNF.Clause.ext 3 :=
  fun H => Clause.unit_ne_empty (H (c1 := Clause.unit (0 : Nat) true) (c2 := .empty))

-- `Std.Sat.CNF.Clause.exists_eq_add_of_ne_empty`: the empty clause is not of the form c.add atom pol.
theorem exists_eq_add_of_ne_empty_2 : ¬ drop0% Std.Sat.CNF.Clause.exists_eq_add_of_ne_empty 2 :=
  fun H => by
    obtain ⟨c', atom, pol, h⟩ := H (c := (Clause.empty : Clause Nat))
    exact Clause.add_ne_empty c' atom pol h.symm

-- `Std.Sat.CNF.Clause.ne_of_mem_of_negate_mem`: l = l' = (0, true), c empty.
theorem ne_of_mem_of_negate_mem_4 : ¬ drop0% Std.Sat.CNF.Clause.ne_of_mem_of_negate_mem 4 :=
  fun H => H (l := ((0 : Nat), true)) (l' := (0, true)) (c := .empty) (by simp) (by simp) rfl

-- `Std.Sat.CNF.Clause.ne_of_mem_of_negate_mem`: l = l' = (0, true), c = x0.
theorem ne_of_mem_of_negate_mem_5 : ¬ drop0% Std.Sat.CNF.Clause.ne_of_mem_of_negate_mem 5 :=
  fun H => H (l := ((0 : Nat), true)) (l' := (0, true)) (c := U) (by simp [U])
    (by simp [U, Literal.negate]) rfl

-- `Std.Sat.CNF.Clause.ne_of_mem_of_negate_mem`: l = (0, true), l' = (0, false), c = x0.
theorem ne_of_mem_of_negate_mem_6 : ¬ drop0% Std.Sat.CNF.Clause.ne_of_mem_of_negate_mem 6 :=
  fun H => H (l := ((0 : Nat), true)) (l' := (0, false)) (c := U) (by simp [U]) (by simp [U]) rfl

-- `Std.Sat.CNF.Clause.VarMem_add_ne_self`: atom1 = atom2 = 0, c empty.
theorem VarMem_add_ne_self_5 : ¬ drop0% Std.Sat.CNF.Clause.VarMem_add_ne_self 5 :=
  fun H => by
    have := H (pol := true) (c := (Clause.empty : Clause Nat)) (atom1 := 0) (atom2 := 0)
    simp at this

-- `Std.Sat.CNF.Clause.inductionOn`: motive c ≠ empty holds for every add but not for empty.
theorem inductionOn_2 : ¬ drop0% Std.Sat.CNF.Clause.inductionOn 2 :=
  fun H => H (motive := fun c : Clause Nat => c ≠ .empty)
    (fun c atom pol _ => Clause.add_ne_empty c atom pol) .empty rfl

-- `Std.Sat.CNF.Clause.inductionOn`: motive c = empty holds for empty but not for x0.
theorem inductionOn_3 : ¬ drop0% Std.Sat.CNF.Clause.inductionOn 3 :=
  fun H => Clause.unit_ne_empty (H (motive := fun c : Clause Nat => c = .empty) rfl (Clause.unit 0 true))

-- `Std.Sat.CNF.VarMem_of`: c = x0 is not in the empty formula.
theorem VarMem_of_4 : ¬ drop0% Std.Sat.CNF.VarMem_of 4 :=
  fun H => not_VarMem_empty (H (f := CNF.empty) (c := U) (v := 0) (by simp [U]))

-- `Std.Sat.CNF.VarMem_of`: F contains only the empty clause, which has no variables.
theorem VarMem_of_5 : ¬ drop0% Std.Sat.CNF.VarMem_of 5 :=
  fun H => not_varMem_F 0 (H (f := F) (c := .empty) (v := 0) (by simp [F]))

/-! ## Std.Sat.CNF.Entails -/

-- `Std.Sat.CNF.entails_trans`: T ⊨ F fails, F ⊨ F holds.
theorem entails_trans_4 : ¬ drop0% Std.Sat.CNF.entails_trans 4 :=
  fun H => not_entails_T_F (H (f1 := T) (f2 := F) (f3 := F) (entails_F F))

-- `Std.Sat.CNF.entails_trans`: T ⊨ T holds, T ⊨ F fails.
theorem entails_trans_5 : ¬ drop0% Std.Sat.CNF.entails_trans 5 :=
  fun H => not_entails_T_F (H (f1 := T) (f2 := T) (f3 := F) (entails_T T))

-- `Std.Sat.CNF.entails_of_forall_sat`: T ⊨ F fails.
theorem entails_of_forall_sat_3 : ¬ drop0% Std.Sat.CNF.entails_of_forall_sat 3 :=
  fun H => not_entails_T_F (H T F)

-- `Std.Sat.CNF.entails_add_of_entails_clause`: T ⊨ T.add empty fails.
theorem entails_add_of_entails_clause_3 : ¬ drop0% Std.Sat.CNF.entails_add_of_entails_clause 3 :=
  fun H => not_entails_T_F (H T .empty)

-- `Std.Sat.CNF.entails_of_all_mem`: T ⊨ F fails.
theorem entails_of_all_mem_3 : ¬ drop0% Std.Sat.CNF.entails_of_all_mem 3 :=
  fun H => not_entails_T_F (H F T)

-- `Std.Sat.CNF.unsat_of_entails_unsat`: T ⊨ T but T is satisfiable.
theorem unsat_of_entails_unsat_3 : ¬ drop0% Std.Sat.CNF.unsat_of_entails_unsat 3 :=
  fun H => T_not_unsat (H (f1 := T) (f2 := T) (entails_T T))

-- `Std.Sat.CNF.unsat_of_entails_unsat`: F unsat but T ⊨ F fails; T satisfiable.
theorem unsat_of_entails_unsat_4 : ¬ drop0% Std.Sat.CNF.unsat_of_entails_unsat 4 :=
  fun H => T_not_unsat (H (f1 := T) (f2 := F) F_unsat)

-- `Std.Sat.CNF.unsat_of_entails_clause_unsat`: T entails the tautology V.
theorem unsat_of_entails_clause_unsat_3 : ¬ drop0% Std.Sat.CNF.unsat_of_entails_clause_unsat 3 :=
  fun H => T_not_unsat (H (f := T) (c := V) (entailsClause_V T))

-- `Std.Sat.CNF.unsat_of_entails_clause_unsat`: the empty clause is unsat, T is satisfiable.
theorem unsat_of_entails_clause_unsat_4 : ¬ drop0% Std.Sat.CNF.unsat_of_entails_clause_unsat 4 :=
  fun H => T_not_unsat (H (f := T) (c := .empty) Clause.unsat_empty)

-- `Std.Sat.CNF.entails_append_of_entails`: f1 = T, f2 = F, f3 = T.
theorem entails_append_of_entails_4 : ¬ drop0% Std.Sat.CNF.entails_append_of_entails 4 :=
  fun H => not_entails_T_F (entails_trans (H (f1 := T) (f2 := F) (f3 := T) (entails_T T))
    append_entails_left)

-- `Std.Sat.CNF.entails_append_of_entails`: f1 = T, f2 = T, f3 = F.
theorem entails_append_of_entails_5 : ¬ drop0% Std.Sat.CNF.entails_append_of_entails 5 :=
  fun H => not_entails_T_F (entails_trans (H (f1 := T) (f2 := T) (f3 := F) (entails_T T))
    append_entails_right)

-- `Std.Sat.CNF.entails_append_congr_right`: f1 = f2 = T, f3 = F.
theorem entails_append_congr_right_4 : ¬ drop0% Std.Sat.CNF.entails_append_congr_right 4 :=
  fun H => not_entails_of aT (by simp [T_sat]) (by simp [F_not_sat])
    (H (f1 := T) (f2 := T) (f3 := F))

-- `Std.Sat.CNF.entails_append_congr_left`: f1 = f2 = T, f3 = F.
theorem entails_append_congr_left_4 : ¬ drop0% Std.Sat.CNF.entails_append_congr_left 4 :=
  fun H => not_entails_of aT (by simp [T_sat]) (by simp [F_not_sat])
    (H (f1 := T) (f2 := T) (f3 := F))

-- `Std.Sat.CNF.entails_clause_append_of_forall`: T does not entail empty ++ empty.
theorem entails_clause_append_of_forall_4 : ¬ drop0% Std.Sat.CNF.entails_clause_append_of_forall 4 :=
  fun H => not_entailsClause_of aT (T_sat aT) (by simp)
    (H (f := T) (c1 := .empty) (c2 := .empty))

-- `Std.Sat.CNF.entails_clause_append_left`: T does not entail empty ++ empty.
theorem entails_clause_append_left_4 : ¬ drop0% Std.Sat.CNF.entails_clause_append_left 4 :=
  fun H => not_entailsClause_of aT (T_sat aT) (by simp)
    (H (f := T) (c1 := .empty) (c2 := .empty))

-- `Std.Sat.CNF.entails_clause_append_right`: T does not entail empty ++ empty.
theorem entails_clause_append_right_4 : ¬ drop0% Std.Sat.CNF.entails_clause_append_right 4 :=
  fun H => not_entailsClause_of aT (T_sat aT) (by simp)
    (H (f := T) (c1 := .empty) (c2 := .empty))

-- `Std.Sat.CNF.entails_clause_append_comm`: T does not entail empty ++ empty.
theorem entails_clause_append_comm_4 : ¬ drop0% Std.Sat.CNF.entails_clause_append_comm 4 :=
  fun H => not_entailsClause_of aT (T_sat aT) (by simp)
    (H (f := T) (c1 := .empty) (c2 := .empty))

-- `Std.Sat.CNF.unsat_of_entails_clause_append_unsat`: c1 = V (tautology), c2 = empty, f = T.
theorem unsat_of_entails_clause_append_unsat_4 :
    ¬ drop0% Std.Sat.CNF.unsat_of_entails_clause_append_unsat 4 :=
  fun H => T_not_unsat (H (f := T) (c1 := V) (c2 := .empty) Clause.unsat_empty
    (fun a _ => Clause.sat_append_left (V_sat a)))

-- `Std.Sat.CNF.unsat_of_entails_clause_append_unsat`: c1 = empty, c2 = V (tautology), f = T.
theorem unsat_of_entails_clause_append_unsat_5 :
    ¬ drop0% Std.Sat.CNF.unsat_of_entails_clause_append_unsat 5 :=
  fun H => T_not_unsat (H (f := T) (c1 := .empty) (c2 := V) Clause.unsat_empty
    (fun a _ => Clause.sat_append_right (V_sat a)))

-- `Std.Sat.CNF.unsat_of_entails_clause_append_unsat`: c1 = c2 = empty, f = T.
theorem unsat_of_entails_clause_append_unsat_6 :
    ¬ drop0% Std.Sat.CNF.unsat_of_entails_clause_append_unsat 6 :=
  fun H => T_not_unsat (H (f := T) (c1 := .empty) (c2 := .empty) Clause.unsat_empty Clause.unsat_empty)

-- `Std.Sat.CNF.entails_clause_of_mem`: T does not entail the empty clause.
theorem entails_clause_of_mem_3 : ¬ drop0% Std.Sat.CNF.entails_clause_of_mem 3 :=
  fun H => not_entailsClause_T_empty (H (f := T) (c := .empty))

-- `Std.Sat.CNF.entails_clause_trans`: f = T, g = F, c = empty.
theorem entails_clause_trans_4 : ¬ drop0% Std.Sat.CNF.entails_clause_trans 4 :=
  fun H => not_entailsClause_T_empty (H (f := T) (g := F) (c := .empty) (entailsClause_F _))

-- `Std.Sat.CNF.entails_clause_trans`: f = g = T, c = empty.
theorem entails_clause_trans_5 : ¬ drop0% Std.Sat.CNF.entails_clause_trans 5 :=
  fun H => not_entailsClause_T_empty (H (f := T) (g := T) (c := .empty) (entails_T T))

-- `Std.Sat.CNF.entails_add_congr`: f = T, g = F, c = V.
theorem entails_add_congr_4 : ¬ drop0% Std.Sat.CNF.entails_add_congr 4 :=
  fun H => not_entails_of aT (by simp [T_sat, V_sat]) (by simp [F_not_sat])
    (H (f := T) (g := F) (c := V))

-- `Std.Sat.CNF.biEntails_trans`: f1 = T, f2 = f3 = F.
theorem biEntails_trans_4 : ¬ drop0% Std.Sat.CNF.biEntails_trans 4 :=
  fun H => not_entails_T_F (H (f1 := T) (f2 := F) (f3 := F) biEntails_refl).1

-- `Std.Sat.CNF.biEntails_trans`: f1 = f2 = T, f3 = F.
theorem biEntails_trans_5 : ¬ drop0% Std.Sat.CNF.biEntails_trans 5 :=
  fun H => not_entails_T_F (H (f1 := T) (f2 := T) (f3 := F) biEntails_refl).1

-- `Std.Sat.CNF.biEntails_symm`: f1 = F, f2 = T.
theorem biEntails_symm_3 : ¬ drop0% Std.Sat.CNF.biEntails_symm 3 :=
  fun H => not_entails_T_F (H (f1 := F) (f2 := T)).1

/-! ## Std.Sat.CNF.Negation -/

-- `Std.Sat.CNF.forall_mem_eq_not_of_isNegationOf_of_sat`: f = T, c = x0, all-true assignment.
theorem forall_mem_eq_not_of_isNegationOf_of_sat_4 :
    ¬ drop0% Std.Sat.CNF.forall_mem_eq_not_of_isNegationOf_of_sat 4 :=
  fun H => absurd (H (f := T) (c := U) (a := aT) (T_sat aT) (0, true) (by simp [U])) (by simp [aT])

-- `Std.Sat.CNF.forall_mem_eq_not_of_isNegationOf_of_sat`: F is the negation of the tautology V.
theorem forall_mem_eq_not_of_isNegationOf_of_sat_5 :
    ¬ drop0% Std.Sat.CNF.forall_mem_eq_not_of_isNegationOf_of_sat 5 :=
  fun H => absurd (H (f := F) (c := V) (a := aT) isNegationOf_F_V (0, true) (by simp [V])) (by simp [aT])

-- `Std.Sat.CNF.forall_mem_eq_not_of_isNegationOf_of_sat`: lit = (0, true) not in c = empty.
theorem forall_mem_eq_not_of_isNegationOf_of_sat_7 :
    ¬ drop0% Std.Sat.CNF.forall_mem_eq_not_of_isNegationOf_of_sat 7 :=
  fun H => absurd (H (f := T) (c := .empty) (a := aT) isNegationOf_T_empty (T_sat aT) (0, true))
    (by simp [aT])

-- `Std.Sat.CNF.Clause.sat_negate_iff_sat_of_isNegationOf`: c = empty (negation always sat), f = F.
theorem sat_negate_iff_sat_of_isNegationOf_3 :
    ¬ drop0% Std.Sat.CNF.Clause.sat_negate_iff_sat_of_isNegationOf 3 :=
  fun H => F_not_sat aT ((H (c := .empty) F aT).mp
    (((isNegationOf_negate (Clause.empty : Clause Nat)) aT).mpr (empty_not_sat aT)))

-- `Std.Sat.CNF.isNegationOf_append_append_of_isNegationOf`: f1 = T, c1 = V, f2 = T, c2 = empty.
theorem isNegationOf_append_append_of_isNegationOf_5 :
    ¬ drop0% Std.Sat.CNF.isNegationOf_append_append_of_isNegationOf 5 :=
  fun H => by
    have := (H (f1 := T) (c1 := V) (f2 := T) (c2 := .empty) isNegationOf_T_empty) aT
    simp [T_sat, V_sat] at this

-- `Std.Sat.CNF.isNegationOf_append_append_of_isNegationOf`: f1 = T, c1 = empty, f2 = T, c2 = V.
theorem isNegationOf_append_append_of_isNegationOf_6 :
    ¬ drop0% Std.Sat.CNF.isNegationOf_append_append_of_isNegationOf 6 :=
  fun H => by
    have := (H (f1 := T) (c1 := .empty) (f2 := T) (c2 := V) isNegationOf_T_empty) aT
    simp [T_sat, V_sat] at this

-- `Std.Sat.CNF.isNegationOf_of_isNegationOf_of_biEntails`: f1 = f2 = T, c = V.
theorem isNegationOf_of_isNegationOf_of_biEntails_4 :
    ¬ drop0% Std.Sat.CNF.isNegationOf_of_isNegationOf_of_biEntails 4 :=
  fun H => not_isNegationOf_T_V (H (f1 := T) (c := V) (f2 := T) biEntails_refl)

-- `Std.Sat.CNF.isNegationOf_of_isNegationOf_of_biEntails`: f1 = T, c = empty, f2 = F.
theorem isNegationOf_of_isNegationOf_of_biEntails_5 :
    ¬ drop0% Std.Sat.CNF.isNegationOf_of_isNegationOf_of_biEntails 5 :=
  fun H => not_isNegationOf_F_empty (H (f1 := T) (c := .empty) (f2 := F) isNegationOf_T_empty)

/-! ## Std.Sat.CNF.Redundancy -/

-- `Std.Sat.CNF.entails_clause_of_forall_sat`: T does not entail the empty clause.
theorem entails_clause_of_forall_sat_3 : ¬ drop0% Std.Sat.CNF.entails_clause_of_forall_sat 3 :=
  fun H => not_entailsClause_T_empty (H (f := T) (c := .empty))

-- `Std.Sat.CNF.entails_clause_of_unsat_of_forall_not_sat`: f1 = F, f2 = T, c = empty.
theorem entails_clause_of_unsat_of_forall_not_sat_4 :
    ¬ drop0% Std.Sat.CNF.entails_clause_of_unsat_of_forall_not_sat 4 :=
  fun H => not_entailsClause_T_empty (H (c := .empty) (f2 := T) (f1 := F)
    (unsat_append_right F_unsat))

-- `Std.Sat.CNF.entails_clause_of_unsat_of_forall_not_sat`: f1 = f2 = T, c = empty.
theorem entails_clause_of_unsat_of_forall_not_sat_5 :
    ¬ drop0% Std.Sat.CNF.entails_clause_of_unsat_of_forall_not_sat 5 :=
  fun H => not_entailsClause_T_empty (H (c := .empty) (f2 := T) (f1 := T)
    (fun a h => absurd (T_sat a) h))

-- `Std.Sat.CNF.entails_clause_of_unsat_of_isNegationOf`: f1 = F, f2 = T, c = empty.
theorem entails_clause_of_unsat_of_isNegationOf_4 :
    ¬ drop0% Std.Sat.CNF.entails_clause_of_unsat_of_isNegationOf 4 :=
  fun H => not_entailsClause_T_empty (H (f1 := F) (c := .empty) (f2 := T)
    (unsat_append_right F_unsat))

-- `Std.Sat.CNF.entails_clause_of_unsat_of_isNegationOf`: f1 = f2 = T, c = empty.
theorem entails_clause_of_unsat_of_isNegationOf_5 :
    ¬ drop0% Std.Sat.CNF.entails_clause_of_unsat_of_isNegationOf 5 :=
  fun H => not_entailsClause_T_empty (H (f1 := T) (c := .empty) (f2 := T) isNegationOf_T_empty)

end SatCNFHand

namespace SatCNFHand

/-! ## A type with an unlawful `BEq` -/

/-- `Nat` with the `BEq` that answers `false` on all pairs (not reflexive, so not lawful). -/
def NB := Nat
instance : BEq NB := ⟨fun _ _ => false⟩
/-- The atom `0 : NB`. -/
def NB.z : NB := (0 : Nat)
@[simp] theorem NB.beq (x y : NB) : (x == y) = false := rfl
@[simp] theorem NB.lit_bne (l l' : Literal NB) : (l != l') = true := by
  cases l; cases l'; rfl

-- Helper: erase evaluates for any BEq (the library lemma's step without LawfulBEq).
theorem literals_erase_go_any {α : Type u} [BEq α] {c : Clause α} {lit : Literal α} {i : Nat}
    {acc : Clause α} :
    ((privconst% Std.Sat.CNF.Basic Std.Sat.CNF.Clause.erase.go) c lit i acc).literals
      = acc.literals ++ (c.literals.drop i).filter (fun l => l != lit) := by
  fun_induction (privconst% Std.Sat.CNF.Basic Std.Sat.CNF.Clause.erase.go) c lit i acc with
  | case1 i acc h atom pol heq ih =>
    have hlt : i < c.literals.length := by rw [Clause.length_literals]; exact h
    have hlit : c.literals[i] = (atom, pol) := by
      rw [Clause.Internal.getElem_literals hlt,
        Clause.Internal.polarity_eq_getElem (by rw [c.size_polarities]; exact h)]
    have hb : (((atom, pol) : Literal α) != lit) = false := by
      cases lit; simp only [bne, BEq.beq] at heq ⊢; simp [heq]
    rw [List.drop_eq_getElem_cons hlt, List.filter_cons, hlit, hb]
    simp [ih]
  | case2 i acc h atom pol heq ih =>
    have hlt : i < c.literals.length := by rw [Clause.length_literals]; exact h
    have hlit : c.literals[i] = (atom, pol) := by
      rw [Clause.Internal.getElem_literals hlt,
        Clause.Internal.polarity_eq_getElem (by rw [c.size_polarities]; exact h)]
    have hb : (((atom, pol) : Literal α) != lit) = true := by
      cases lit; simp only [bne, BEq.beq] at heq ⊢; simp [heq]
    rw [List.drop_eq_getElem_cons hlt, List.filter_cons, hlit, ih, Clause.literals_add, hb]
    simp
  | case3 i acc h =>
    rw [List.drop_of_length_le (by rw [Clause.length_literals]; omega)]
    simp

-- `Std.Sat.CNF.Clause.literals_erase`: removable, erase and filter (· != lit) use the same
-- BEq comparison (atom == lit.1 && pol == lit.2), so they agree for every BEq.
theorem literals_erase_2 : drop% Std.Sat.CNF.Clause.literals_erase 2 := by
  intro α _ c lit
  rw [Clause.erase, literals_erase_go_any]
  simp

-- Helper: with the all-false BEq, erase removes nothing.
theorem NB.erase_eq (c : Clause NB) (l : Literal NB) : c.erase l = c :=
  Clause.ext (by rw [Clause.erase, literals_erase_go_any]; simp)

-- Helper: with the all-false BEq, contains is always false.
theorem NB.contains_go (c : Clause NB) (l : Literal NB) (i : Nat) :
    (privconst% Std.Sat.CNF.Basic Std.Sat.CNF.Clause.contains.go) c l i = false := by
  fun_induction (privconst% Std.Sat.CNF.Basic Std.Sat.CNF.Clause.contains.go) c l i with
  | case1 i h h1 h2 hc => simp at hc
  | case2 i h h1 h2 hc ih => exact ih
  | case3 i h => rfl

-- `Std.Sat.CNF.Clause.contains_iff_mem`: all-false BEq on NB; (0, true) ∈ x0 but contains is false.
theorem contains_iff_mem_2 : ¬ drop0% Std.Sat.CNF.Clause.contains_iff_mem 2 :=
  fun H => by
    have := (@H NB _ (Clause.unit NB.z true) (NB.z, true)).mpr (by simp)
    rw [Clause.contains, NB.contains_go] at this
    exact Bool.false_ne_true this

-- `Std.Sat.CNF.Clause.mem_erase_iff`: all-false BEq on NB; erasing (0, true) from x0 keeps it.
theorem mem_erase_iff_4 : ¬ drop0% Std.Sat.CNF.Clause.mem_erase_iff 4 :=
  fun H => by
    have := (@H NB (NB.z, true) (NB.z, true) _ (Clause.unit NB.z true)).mp
      (by rw [NB.erase_eq]; simp)
    exact this.1 rfl

/-! ## Std.Sat.CNF.Redundancy: `exists_sat_add_of_rat` -/

-- `Std.Sat.CNF.exists_sat_add_of_rat`: all-false BEq on NB, so erase is the identity and h2
-- holds trivially; f = {¬x0}, c = x0, l = (0, true): f sat, f.add c unsat.
theorem exists_sat_add_of_rat_2 : ¬ drop0% Std.Sat.CNF.exists_sat_add_of_rat 2 :=
  fun H => by
    obtain ⟨a', ha'⟩ := @H NB _ (CNF.empty.add (Clause.unit NB.z false)) (Clause.unit NB.z true)
      (NB.z, true) (by simp)
      (fun c' hc' _ => by
        rw [NB.erase_eq]
        exact fun a ha => Clause.sat_append_right (sat_of_mem ha hc'))
      (fun _ => false) (by simp)
    simp at ha'

-- `Std.Sat.CNF.exists_sat_add_of_rat`: f = T, c = empty, l = (0, true) (not in c).
theorem exists_sat_add_of_rat_6 : ¬ drop0% Std.Sat.CNF.exists_sat_add_of_rat 6 :=
  fun H => by
    obtain ⟨a', ha'⟩ := H (f := T) (c := .empty) (l := ((0 : Nat), true))
      (fun c' hc' => by simp [T] at hc') aT (T_sat aT)
    simp at ha'

-- `Std.Sat.CNF.exists_sat_add_of_rat`: f = {¬x0}, c = x0, l = (0, true).
theorem exists_sat_add_of_rat_7 : ¬ drop0% Std.Sat.CNF.exists_sat_add_of_rat 7 :=
  fun H => by
    obtain ⟨a', ha'⟩ := H (f := CNF.empty.add (Clause.unit (0 : Nat) false)) (c := U)
      (l := ((0 : Nat), true)) (by simp [U]) (fun _ => false) (by simp)
    simp [U] at ha'

-- `Std.Sat.CNF.exists_sat_add_of_rat`: f = F is unsat, so f.add c is unsat; h2 is vacuous.
theorem exists_sat_add_of_rat_9 : ¬ drop0% Std.Sat.CNF.exists_sat_add_of_rat 9 :=
  fun H => by
    obtain ⟨a', ha'⟩ := H (f := F) (c := U) (l := ((0 : Nat), true)) (by simp [U])
      (fun c' hc' hn => by simp [F] at hc'; subst hc'; simp at hn) aT
    exact F_not_sat a' (sat_add.mp ha').2

/-! ## Std.Sat.CNF.Relabel -/

/-- Assignment true exactly on `0`. -/
def a0 : Nat → Bool := fun n => n == 0

-- `Std.Sat.CNF.Clause.relabel_congr`: c = x0, r1 = id, r2 = fun _ => 1 (evaluate under a0).
theorem Clause_relabel_congr_5 : ¬ drop0% Std.Sat.CNF.Clause.relabel_congr 5 :=
  fun H => by
    have := congrArg (Clause.eval a0) (H (c := U) (r1 := id) (r2 := fun _ => (1 : Nat)))
    simp [U, a0] at this

-- `Std.Sat.CNF.relabel_congr`: f = {x0}, r1 = id, r2 = fun _ => 1 (evaluate under a0).
theorem relabel_congr_5 : ¬ drop0% Std.Sat.CNF.relabel_congr 5 :=
  fun H => by
    have := congrArg (CNF.eval a0) (H (f := FU) (r1 := id) (r2 := fun _ => (1 : Nat)))
    simp [FU, U, a0] at this

-- `Std.Sat.CNF.sat_relabel`: f = F relabels to an unsatisfiable formula.
theorem sat_relabel_5 : ¬ drop0% Std.Sat.CNF.sat_relabel 5 :=
  fun H => by
    have := H (r1 := aT) (r2 := (id : Nat → Nat)) (f := F)
    simp [sat_def, F] at this

-- `Std.Sat.CNF.unsat_relabel`: f = T relabels to the empty formula.
theorem unsat_relabel_4 : ¬ drop0% Std.Sat.CNF.unsat_relabel 4 :=
  fun H => by
    have := H (f := T) (id : Nat → Nat)
    simp [T] at this

-- `Std.Sat.CNF.unsat_relabel_iff`: {x0}, {¬x1} is sat; relabelled along fun _ => 0 it is {x0}, {¬x0}.
theorem unsat_relabel_iff_4 : ¬ drop0% Std.Sat.CNF.unsat_relabel_iff 4 :=
  fun H => by
    have h := H (f := FR) (r := fun _ : Nat => (0 : Nat))
    have hs : ¬ Unsat FR := fun hu => (unsat_iff_not_sat.mp hu) a0 (by simp [FR, a0])
    apply hs; apply h.mp
    rw [unsat_iff_not_sat]; intro a ha
    simp [FR] at ha

/-! ## Std.Sat.CNF.RelabelFin -/

-- `Std.Sat.CNF.Clause.of_maxLiteral_eq_some`: c = x1, maxLit = 0, lit = 1.
theorem Clause_of_maxLiteral_eq_some_2 : ¬ drop0% Std.Sat.CNF.Clause.of_maxLiteral_eq_some 2 :=
  fun H => absurd (H (maxLit := 0) (Clause.unit 1 true) 1 (by simp)) (by decide)

-- `Std.Sat.CNF.Clause.of_maxLiteral_eq_some`: c = x0 (max 0), lit = 1 not in c.
theorem Clause_of_maxLiteral_eq_some_4 : ¬ drop0% Std.Sat.CNF.Clause.of_maxLiteral_eq_some 4 :=
  fun H => absurd (H (maxLit := 0) (Clause.unit 0 true) (by decide) 1) (by decide)

-- `Std.Sat.CNF.Clause.maxLiteral_eq_some_of_mem`: the empty clause has maxLiteral = none.
theorem maxLiteral_eq_some_of_mem_2 : ¬ drop0% Std.Sat.CNF.Clause.maxLiteral_eq_some_of_mem 2 :=
  fun H => by
    obtain ⟨m, hm⟩ := H (l := 0) Clause.empty
    have h0 : (Clause.empty : Clause Nat).maxLiteral = none := by decide
    rw [h0] at hm; cases hm

-- `Std.Sat.CNF.Clause.of_maxLiteral_eq_none`: 0 occurs in x0.
theorem Clause_of_maxLiteral_eq_none_1 : ¬ drop0% Std.Sat.CNF.Clause.of_maxLiteral_eq_none 1 :=
  fun H => H (Clause.unit 0 true) 0 (by simp)

-- `Std.Sat.CNF.of_maxLiteral_eq_some'`: f = {x1}, clause = x1, localMax = 1, maxLit = 0.
theorem of_maxLiteral_eq_some'_3 : ¬ drop0% Std.Sat.CNF.of_maxLiteral_eq_some' 3 :=
  fun H => absurd (H (maxLit := 0) (localMax := 1) (CNF.empty.add (Clause.unit 1 true))
    (Clause.unit 1 true) (by simp) (by decide)) (by decide)

-- `Std.Sat.CNF.of_maxLiteral_eq_some'`: f = {x0}, clause = x1 (not in f), localMax = 1.
theorem of_maxLiteral_eq_some'_5 : ¬ drop0% Std.Sat.CNF.of_maxLiteral_eq_some' 5 :=
  fun H => absurd (H (maxLit := 0) (localMax := 1) (CNF.empty.add (Clause.unit 0 true))
    (by decide) (Clause.unit 1 true) (by decide)) (by decide)

-- `Std.Sat.CNF.of_maxLiteral_eq_some'`: f = {x0}, clause = x0, localMax = 1.
theorem of_maxLiteral_eq_some'_6 : ¬ drop0% Std.Sat.CNF.of_maxLiteral_eq_some' 6 :=
  fun H => absurd (H (maxLit := 0) (localMax := 1) (CNF.empty.add (Clause.unit 0 true))
    (by decide) (Clause.unit 0 true) (by simp)) (by decide)

-- `Std.Sat.CNF.of_maxLiteral_eq_some`: f = {x1}, maxLit = 0, lit = 1.
theorem of_maxLiteral_eq_some_2 : ¬ drop0% Std.Sat.CNF.of_maxLiteral_eq_some 2 :=
  fun H => absurd (H (maxLit := 0) (CNF.empty.add (Clause.unit 1 true)) 1
    (by simp [CNF.VarMem_add])) (by decide)

-- `Std.Sat.CNF.of_maxLiteral_eq_some`: f = {x0} (max 0), lit = 1 not in f.
theorem of_maxLiteral_eq_some_4 : ¬ drop0% Std.Sat.CNF.of_maxLiteral_eq_some 4 :=
  fun H => absurd (H (maxLit := 0) (CNF.empty.add (Clause.unit 0 true)) (by decide) 1) (by decide)

-- `Std.Sat.CNF.of_maxLiteral_eq_none`: 0 occurs in {x0}.
theorem of_maxLiteral_eq_none_1 : ¬ drop0% Std.Sat.CNF.of_maxLiteral_eq_none 1 :=
  fun H => H FU 0 varMem_FU

-- `Std.Sat.CNF.lt_numLiterals`: the empty formula has numLiterals = 0.
theorem lt_numLiterals_2 : ¬ drop0% Std.Sat.CNF.lt_numLiterals 2 :=
  fun H => absurd (H (v := 0) (f := CNF.empty)) (by decide)

-- `Std.Sat.CNF.numLiterals_pos`: the empty formula has numLiterals = 0.
theorem numLiterals_pos_2 : ¬ drop0% Std.Sat.CNF.numLiterals_pos 2 :=
  fun H => absurd (H (v := 0) (f := CNF.empty)) (by decide)

/-! ## Std.Sat.CNF.Sat -/

-- `Std.Sat.CNF.Clause.eval_congr`: c = x0, a1 = true, a2 = false.
theorem Clause_eval_congr_4 : ¬ drop0% Std.Sat.CNF.Clause.eval_congr 4 :=
  fun H => absurd (H (fun _ => true) (fun _ => false) U) (by simp [U])

-- `Std.Sat.CNF.Clause.sat_append_left`: empty ++ empty is not sat.
theorem Clause_sat_append_left_4 : ¬ drop0% Std.Sat.CNF.Clause.sat_append_left 4 :=
  fun H => absurd (H (a := aT) (c1 := (Clause.empty : Clause Nat)) (c2 := .empty)) (by simp)

-- `Std.Sat.CNF.Clause.sat_append_right`: empty ++ empty is not sat.
theorem Clause_sat_append_right_4 : ¬ drop0% Std.Sat.CNF.Clause.sat_append_right 4 :=
  fun H => absurd (H (a := aT) (c1 := (Clause.empty : Clause Nat)) (c2 := .empty)) (by simp)

-- `Std.Sat.CNF.Clause.unsat_of_unsat_append_left`: c1 = x0 is not unsat.
theorem Clause_unsat_of_unsat_append_left_3 : ¬ drop0% Std.Sat.CNF.Clause.unsat_of_unsat_append_left 3 :=
  fun H => U_not_unsat (H (c1 := U) (c2 := .empty))

-- `Std.Sat.CNF.Clause.unsat_of_unsat_append_right`: c2 = x0 is not unsat.
theorem Clause_unsat_of_unsat_append_right_3 :
    ¬ drop0% Std.Sat.CNF.Clause.unsat_of_unsat_append_right 3 :=
  fun H => U_not_unsat (H (c1 := .empty) (c2 := U))

-- `Std.Sat.CNF.Clause.sat_of_mem_of_eq`: c = empty, lit = (0, true), all-true assignment.
theorem Clause_sat_of_mem_of_eq_4 : ¬ drop0% Std.Sat.CNF.Clause.sat_of_mem_of_eq 4 :=
  fun H => empty_not_sat aT (H (a := aT) (c := .empty) (lit := (0, true)) rfl)

-- `Std.Sat.CNF.Clause.sat_of_mem_of_eq`: c = x0, lit = (0, true), all-false assignment.
theorem Clause_sat_of_mem_of_eq_5 : ¬ drop0% Std.Sat.CNF.Clause.sat_of_mem_of_eq 5 :=
  fun H => absurd (H (a := fun _ => false) (c := U) (lit := (0, true)) (by simp [U])) (by simp [U])

-- `Std.Sat.CNF.Clause.sat_of_mem_of_mem_neg`: c = ¬x0, pol = true; all-true assignment.
theorem Clause_sat_of_mem_of_mem_neg_4 : ¬ drop0% Std.Sat.CNF.Clause.sat_of_mem_of_mem_neg 4 :=
  fun H => absurd (H (pol := true) (c := Clause.unit 0 false) (atom := (0 : Nat)) (by simp) aT)
    (by simp [aT])

-- `Std.Sat.CNF.Clause.sat_of_mem_of_mem_neg`: c = x0, pol = true; all-false assignment.
theorem Clause_sat_of_mem_of_mem_neg_5 : ¬ drop0% Std.Sat.CNF.Clause.sat_of_mem_of_mem_neg 5 :=
  fun H => absurd (H (pol := true) (c := U) (atom := (0 : Nat)) (by simp [U]) (fun _ => false))
    (by simp [U])

-- `Std.Sat.CNF.eval_congr`: f = {x0}, a1 = true, a2 = false.
theorem eval_congr_4 : ¬ drop0% Std.Sat.CNF.eval_congr 4 :=
  fun H => absurd (H (fun _ => true) (fun _ => false) FU) (by simp [FU, U])

-- `Std.Sat.CNF.sat_of_all_mem_sat`: F is not sat.
theorem sat_of_all_mem_sat_3 : ¬ drop0% Std.Sat.CNF.sat_of_all_mem_sat 3 :=
  fun H => F_not_sat aT (H (f := F) (a := aT))

-- `Std.Sat.CNF.sat_of_mem`: f = F contains the empty clause, which is not sat.
theorem sat_of_mem_4 : ¬ drop0% Std.Sat.CNF.sat_of_mem 4 :=
  fun H => empty_not_sat aT (H (a := aT) (c := .empty) (f := F) (by simp [F]))

-- `Std.Sat.CNF.sat_of_mem`: f = T is sat, c = empty is not.
theorem sat_of_mem_5 : ¬ drop0% Std.Sat.CNF.sat_of_mem 5 :=
  fun H => empty_not_sat aT (H (a := aT) (c := .empty) (f := T) (T_sat aT))

-- `Std.Sat.CNF.unsat_of_mem_unsat`: f = T, c = empty.
theorem unsat_of_mem_unsat_3 : ¬ drop0% Std.Sat.CNF.unsat_of_mem_unsat 3 :=
  fun H => T_not_unsat (H (c := .empty) (f := T) Clause.unsat_empty)

-- `Std.Sat.CNF.unsat_of_mem_unsat`: f = {x0}, c = x0.
theorem unsat_of_mem_unsat_4 : ¬ drop0% Std.Sat.CNF.unsat_of_mem_unsat 4 :=
  fun H => (unsat_iff_not_sat.mp (H (c := U) (f := FU) U_mem_FU)) aT FU_sat

-- `Std.Sat.CNF.unsat_add_of_clause_unsat`: T.add x0 is sat.
theorem unsat_add_of_clause_unsat_3 : ¬ drop0% Std.Sat.CNF.unsat_add_of_clause_unsat 3 :=
  fun H => (unsat_iff_not_sat.mp (H (c := U) (f := CNF.empty))) aT FU_sat

-- `Std.Sat.CNF.unsat_add_of_unsat`: T.add x0 is sat.
theorem unsat_add_of_unsat_3 : ¬ drop0% Std.Sat.CNF.unsat_add_of_unsat 3 :=
  fun H => (unsat_iff_not_sat.mp (H (c := U) (f := CNF.empty))) aT FU_sat

-- `Std.Sat.CNF.unsat_append_left`: T ++ T is sat.
theorem unsat_append_left_3 : ¬ drop0% Std.Sat.CNF.unsat_append_left 3 :=
  fun H => (unsat_iff_not_sat.mp (H (f1 := T) (f2 := T))) aT (by simp [T_sat])

-- `Std.Sat.CNF.unsat_append_right`: T ++ T is sat.
theorem unsat_append_right_3 : ¬ drop0% Std.Sat.CNF.unsat_append_right 3 :=
  fun H => (unsat_iff_not_sat.mp (H (f1 := T) (f2 := T))) aT (by simp [T_sat])

-- `Std.Sat.CNF.unsat_of_forall_exists`: c1 = T, c2 = F.
theorem unsat_of_forall_exists_3 : ¬ drop0% Std.Sat.CNF.unsat_of_forall_exists 3 :=
  fun H => T_not_unsat (H (c1 := T) (c2 := F) F_unsat)

-- `Std.Sat.CNF.unsat_of_forall_exists`: c1 = c2 = T.
theorem unsat_of_forall_exists_4 : ¬ drop0% Std.Sat.CNF.unsat_of_forall_exists 4 :=
  fun H => T_not_unsat (H (c1 := T) (c2 := T) (fun a h => ⟨a, h⟩))

/-! ## Std.Sat.CNF.SpecLemmas -/

open Std.Do in
-- `Std.Do.Spec.forIn'_cnfClause`: in Id, xs = x0, invariant "prefix is empty": it holds at the
-- start but not at the end, whatever the loop body does.
theorem forIn'_cnfClause_10 : ¬ drop0% Std.Do.Spec.forIn'_cnfClause 10 :=
  fun H => by
    have h := H (m := Id) (ps := .pure) (xs := U) (init := ()) (f := fun _ _ b => pure (.yield b))
      (PostCond.noThrow fun p => ⌜p.1.prefix = []⌝)
    have h2 : ([] : List (Literal Nat)) = [] → U.literals = [] := h
    simp [U] at h2
    exact Clause.unit_ne_empty h2

open Std.Do in
-- `Std.Do.Spec.forIn_cnfClause`: as for forIn'_cnfClause.
theorem forIn_cnfClause_10 : ¬ drop0% Std.Do.Spec.forIn_cnfClause 10 :=
  fun H => by
    have h := H (m := Id) (ps := .pure) (xs := U) (init := ()) (f := fun _ b => pure (.yield b))
      (PostCond.noThrow fun p => ⌜p.1.prefix = []⌝)
    have h2 : ([] : List (Literal Nat)) = [] → U.literals = [] := h
    simp [U] at h2
    exact Clause.unit_ne_empty h2

end SatCNFHand
