import Std
import Lean

/-!
Hand pass `BVGrow` (hand19, 2026-11-08): the 10 growth premises (`idx < aig.decls.size` in the
`go_decl_eq` lemmas of Clz, Cpop, Mul, the shifts and unsigned division) and the carry-in premise
of the adder's `go_denote_eq`, left open by the BVDecide cluster (hand15). All 11 are necessary.

Growth rows, semantic argument instead of gate tracing: the model `A` has the nodes `false`,
`atom 0`, `atom 1` (cache built by inserting the two atoms). If the operation added no node, the
library lemma `go_decl_eq` makes the result's declarations equal to those of `A`, so every output
reference denotes a literal of `A` (`nogrow_den`). The library's own correctness lemma for the
operation then says some output bit is a non-literal function such as `a0 ∧ ¬a1` or `a0 xor a1`,
which `not_lit` rules out over the four assignments `asg b0 b1`.

Carry-in row: from position 1 the adder never reads the `lhs` bits below the position
(`add_go_congr`), so two operand vectors differing only in bit 0 give the same circuit, while the
statement without the carry-in premise predicts different output bits.

Helpers (namespace `BVGrowHand`): `A`, `litB`, `asg`, `denA`, `nogrow_den`, `not_lit`, `vr`
(reference vectors of `A`), `den_vr`, `bv`, `add_go_congr`; `priv%` reaches the two private cpop
denote lemmas.

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/BVGrowHand.lean`.
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

-- helper: a dotted name with numeric components (for private names)
def parseName (s : String) : Lean.Name :=
  (s.splitOn ".").foldl (fun n c => if !c.isEmpty && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous

open Lean Meta Elab Term in
/-- `priv% "c"`: the constant `c` given by its (possibly private) name. -/
elab "priv% " c:str : term => do
  mkConstWithFreshMVarLevels (parseName c.getString)

open Std.Sat Std.Sat.AIG Std.Tactic.BVDecide BVExpr.bitblast

namespace BVGrowHand

/-! ### The model `A`: nodes `false`, `atom 0`, `atom 1` -/

def c0 : Cache Nat #[.false] := Cache.empty
def c1 : Cache Nat (#[.false].push (.atom 0)) :=
  Cache.insert _ c0 (.atom 0) (by simp [c0, Cache.empty])
def c2 : Cache Nat ((#[.false].push (.atom 0)).push (.atom 1)) :=
  Cache.insert _ c1 (.atom 1) (by unfold c1 Cache.insert; simp [c0, Cache.empty])

def A : AIG Nat where
  decls := (#[.false].push (.atom 0)).push (.atom 1)
  cache := c2
  hdag := by
    intro i l r h hd
    have : i < 3 := h
    match i, this with
    | 0, _ | 1, _ | 2, _ => simp at hd
  hzero := by simp
  hconst := rfl

theorem A_size : A.decls.size = 3 := rfl

/-- Denotation of a literal of `A` under the assignment `asg b0 b1`. -/
def litB (g : Nat) (inv b0 b1 : Bool) : Bool :=
  match g with
  | 0 => inv
  | 1 => b0 ^^ inv
  | _ => b1 ^^ inv

def asg (b0 b1 : Bool) : Nat → Bool := fun i => if i = 0 then b0 else b1

theorem denA (r : A.Ref) (b0 b1 : Bool) :
    denote (asg b0 b1) ⟨A, r⟩ = litB r.gate r.invert b0 b1 := by
  obtain ⟨g, inv, hg⟩ := r
  have : g < 3 := hg
  match g, this with
  | 0, _ => exact denote_idx_false rfl
  | 1, _ => rw [denote_idx_atom (a := 0) rfl]; rfl
  | 2, _ => rw [denote_idx_atom (a := 1) rfl]; rfl

/-- If an operation on `A` adds no node, every output reference denotes a literal of `A`. -/
theorem nogrow_den (E : AIG Nat) (hle : A.decls.size ≤ E.decls.size) (hge : E.decls.size ≤ A.decls.size)
    (hde : ∀ (idx : Nat) (h1 : idx < A.decls.size) (h2 : idx < E.decls.size), E.decls[idx]'h2 = A.decls[idx]'h1)
    (r : E.Ref) (b0 b1 : Bool) :
    denote (asg b0 b1) ⟨E, r⟩ = litB r.gate r.invert b0 b1 := by
  have hp : IsPrefix A.decls E.decls := ⟨hle, fun idx h => hde idx h _⟩
  have := denote.eq_of_isPrefix (entry := ⟨A, ⟨r.gate, r.invert, by have := r.hgate; omega⟩⟩)
    (newAIG := E) hp (assign := asg b0 b1)
  rw [denA] at this
  exact this

/-- No literal of `A` computes `f`. -/
theorem not_lit (f : Bool → Bool → Bool) (hf : ∀ g, g < 3 → ∀ inv : Bool, ∃ b0 b1, litB g inv b0 b1 ≠ f b0 b1)
    (g : Nat) (inv : Bool) (hg : g < 3) (h : ∀ b0 b1, litB g inv b0 b1 = f b0 b1) : False := by
  obtain ⟨b0, b1, hne⟩ := hf g hg inv
  exact hne (h b0 b1)

/-- A vector of references of `A` from (gate, invert) pairs. -/
def vr (l : List (Nat × Bool)) (h : ∀ p ∈ l, p.1 < 3) : A.RefVec l.length :=
  ⟨Vector.ofFn fun i => Fanin.mk l[i].1 l[i].2, by
    intro i hi
    simp only [Vector.getElem_ofFn, Fanin.gate_mk]
    exact h _ (List.getElem_mem _)⟩

@[simp] theorem vr_get (l : List (Nat × Bool)) (h) (i : Nat) (hi : i < l.length) :
    ((vr l h).get i hi).gate = l[i].1 ∧ ((vr l h).get i hi).invert = l[i].2 := by
  simp [vr, AIG.RefVec.get, Fanin.gate_mk, Fanin.invert_mk]

theorem den_vr (l : List (Nat × Bool)) (h) (i : Nat) (hi : i < l.length) (b0 b1 : Bool) :
    denote (asg b0 b1) ⟨A, (vr l h).get i hi⟩ = litB l[i].1 l[i].2 b0 b1 := by
  rw [denA, (vr_get l h i hi).1, (vr_get l h i hi).2]

/-- Bit-vector from a list of bits (least significant first). -/
abbrev bv (l : List Bool) : BitVec l.length := BitVec.ofBoolListLE l


-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_decl_eq`: necessary; on `A` with value bits
-- `[a0, 0]` and distance bits `[0, a1]`, output bit 0 is `a0 ∧ ¬a1`, which no literal of `A` computes,
-- so `go` must add a node.
theorem shl_10 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_decl_eq 10 := by
  intro H
  let dist := vr [(0, false), (2, false)] (by decide)
  let acc := vr [(1, false), (0, false)] (by decide)
  have hle := blastShiftLeft.go_le_size A dist 0 acc
  have hge : (blastShiftLeft.go A dist 0 acc).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A dist 0 acc A.decls.size hlt; omega
  have hde := blastShiftLeft.go_decl_eq A dist 0 acc
  let o := (blastShiftLeft.go A dist 0 acc).vec.get 0 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 && !b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge hde]
  rw [blastShiftLeft.go_denote_eq A dist 0 (by decide) acc (bv [b0, false]) (bv [false, b1]) (asg b0 b1)]
  · revert b0 b1; decide
  · intro idx hidx
    rw [den_vr]
    revert b0 b1 idx; decide
  · intro idx hidx
    rw [den_vr]
    revert b0 b1 idx; decide

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_decl_eq`: necessary; value bits `[0, a0]`,
-- distance bits `[0, a1]`: output bit 1 is `a0 ∧ ¬a1`, not a literal of `A`.
theorem shr_10 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_decl_eq 10 := by
  intro H
  let dist := vr [(0, false), (2, false)] (by decide)
  let acc := vr [(0, false), (1, false)] (by decide)
  have hle := blastShiftRight.go_le_size A dist 0 acc
  have hge : (blastShiftRight.go A dist 0 acc).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A dist 0 acc A.decls.size hlt; omega
  have hde := blastShiftRight.go_decl_eq A dist 0 acc
  let o := (blastShiftRight.go A dist 0 acc).vec.get 1 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 && !b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge hde]
  rw [blastShiftRight.go_denote_eq A dist 0 (by decide) acc (bv [false, b0]) (bv [false, b1]) (asg b0 b1)]
  · revert b0 b1; decide
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_decl_eq`: necessary; value bits
-- `[a0, 0]`, distance bits `[0, a1]`: output bit 0 is `a0 ∧ ¬a1`, not a literal of `A`.
theorem sar_10 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_decl_eq 10 := by
  intro H
  let dist := vr [(0, false), (2, false)] (by decide)
  let acc := vr [(1, false), (0, false)] (by decide)
  have hle := blastArithShiftRight.go_le_size A dist 0 acc
  have hge : (blastArithShiftRight.go A dist 0 acc).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A dist 0 acc A.decls.size hlt; omega
  have hde := blastArithShiftRight.go_decl_eq A dist 0 acc
  let o := (blastArithShiftRight.go A dist 0 acc).vec.get 0 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 && !b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge hde]
  rw [blastArithShiftRight.go_denote_eq A dist 0 (by decide) acc (bv [b0, false]) (bv [false, b1]) (asg b0 b1)]
  · revert b0 b1; decide
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_decl_eq`: necessary; `[a0, 0] * [0, a1]` (from
-- step 1, accumulator `0`): output bit 1 is `a0 ∧ a1`, not a literal of `A`.
theorem mul_10 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_decl_eq 10 := by
  intro H
  let lhs := vr [(1, false), (0, false)] (by decide)
  let rhs := vr [(0, false), (2, false)] (by decide)
  let acc := vr [(0, false), (0, false)] (by decide)
  have hle := blastMul.go_le_size A 1 acc lhs rhs
  have hge : (blastMul.go A lhs rhs 1 acc).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A 1 acc lhs rhs A.decls.size hlt; omega
  have hde := blastMul.go_decl_eq A 1 acc lhs rhs
  let o := (blastMul.go A lhs rhs 1 acc).vec.get 1 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 && b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge hde]
  rw [blastMul.go_denote_eq A 0 (by decide) acc lhs rhs (bv [b0, false]) (bv [false, b1]) (asg b0 b1)]
  · revert b0 b1; decide
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_decl_eq`: necessary; `clz [a0, a1]` from the
-- start (accumulator `2`): output bit 0 is `a0 ∧ ¬a1`, not a literal of `A`.
theorem clz_10 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_decl_eq 10 := by
  intro H
  let xc := vr [(1, false), (2, false)] (by decide)
  let acc := vr [(0, false), (0, true)] (by decide)
  have hle := blastClz.go_le_size A 0 acc xc
  have hge : (blastClz.go A xc 0 acc).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A 0 acc xc A.decls.size hlt; omega
  have hde := blastClz.go_decl_eq A 0 acc xc
  let o := (blastClz.go A xc 0 acc).vec.get 0 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 && !b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge (fun i h1 h2 => hde i h2 h1)]
  rw [blastClz.go_denote_eq (curr := 0) A acc xc (bv [b0, b1]) (asg b0 b1)]
  · revert b0 b1; decide
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide
  · intro idx hidx; simp only [↓reduceIte]; rw [den_vr]; revert b0 b1 idx; decide

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastCpop_decl_eq`: necessary; `cpop [a0, a1]` has bit 0
-- `a0 xor a1`, not a literal of `A`.
theorem cpop_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastCpop_decl_eq 8 := by
  intro H
  let xc := vr [(1, false), (2, false)] (by decide)
  have hle := blastCpop_le_size A xc
  have hge : (blastCpop A xc).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A xc A.decls.size hlt; omega
  have hde := blastCpop_decl_eq A xc
  let o := (blastCpop A xc).vec.get 0 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 ^^ b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge (fun i h1 h2 => hde i h2 h1)]
  rw [denote_blastCpop A xc (bv [b0, b1]) (asg b0 b1)]
  · revert b0 b1; decide
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopTree.go_decl_eq`: necessary; the tree over the two
-- chunks `[a0, 0]`, `[a1, 0]` has bit 0 `a0 xor a1`, not a literal of `A`.
theorem cpoptree_10 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopTree.go_decl_eq 10 := by
  intro H
  let l : A.RefVec (2 * 2) := vr [(1, false), (0, false), (2, false), (0, false)] (by decide)
  have hle := blastCpopTree.go_le_size A l (by decide)
  have hge : (blastCpopTree.go l (by decide)).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A l (by decide) A.decls.size hlt; omega
  have hde := blastCpopTree.go_decl_eq A l (by decide)
  let o := (blastCpopTree.go l (by decide)).vec.get 0 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 ^^ b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge (fun i h1 h2 => hde i h2 h1)]
  rw [(priv% "_private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.0.Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree.go") A 2 l (by decide) (bv [b0, false, b1, false])]
  · revert b0 b1; decide +kernel
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer.go_decl_eq`: necessary; one layer over the two
-- chunks `[a0, 0]`, `[a1, 0]` has bit 0 `a0 xor a1`, not a literal of `A`.
theorem cpoplayer_14 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer.go_decl_eq 14 := by
  intro H
  let l : A.RefVec (2 * 2) := vr [(1, false), (0, false), (2, false), (0, false)] (by decide)
  let nl : A.RefVec (0 * 2) := vr [] (by decide)
  have hle := blastCpopLayer.go_le_size (outWidth := 2) A 0 l nl (by decide) rfl
  have hge : (blastCpopLayer.go (outWidth := 2) 0 l nl (by decide) rfl).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A 0 l nl (by decide) rfl A.decls.size hlt; omega
  have hde := blastCpopLayer.go_decl_eq (outWidth := 2) A 0 l nl (by decide) rfl
  let o := (blastCpopLayer.go (outWidth := 2) 0 l nl (by decide) rfl).vec.get 0 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 ^^ b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge (fun i h1 h2 => hde i h2 h1)]
  rw [(priv% "_private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.0.Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go") (assign := asg b0 b1) A 0 l nl (bv [b0, false, b1, false]) (by decide)]
  · revert b0 b1; decide +kernel
  · intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide
  · intro idx hidx; omega

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.blastDivSubtractShift_decl_eq`: necessary; one step
-- at width 1 with dividend bit `a0`, divisor `a1`, zero state: the quotient bit is `a0 ∨ ¬a1`.
theorem dss_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.blastDivSubtractShift_decl_eq 12 := by
  intro H
  let n := vr [(1, false)] (by decide)
  let d := vr [(2, false)] (by decide)
  let z := vr [(0, false)] (by decide)
  have hle := blastUdiv.blastDivSubtractShift_le_size A n d 1 0 z z
  have hge : (blastUdiv.blastDivSubtractShift A n d 1 0 z z).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A n d 1 0 z z A.decls.size hlt; omega
  have hde := blastUdiv.blastDivSubtractShift_decl_eq A n d 1 0 z z
  let o := (blastUdiv.blastDivSubtractShift A n d 1 0 z z).q.get 0 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 || !b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge hde]
  rw [blastUdiv.denote_blastDivSubtractShift_q A (asg b0 b1) (bv [b0]) (bv [b1]) n d 1 0 z z (bv [false]) (bv [false])]
  · revert b0 b1; decide
  all_goals intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.go_decl_eq`: necessary; one division step at width
-- 1 with dividend bit `a0`, divisor `a1`, zero state: the quotient bit is `a0 ∨ ¬a1`.
theorem udivgo_13 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.go_decl_eq 13 := by
  intro H
  let n := vr [(1, false)] (by decide)
  let d := vr [(2, false)] (by decide)
  let z := vr [(0, false)] (by decide)
  have hle := blastUdiv.go_le_size A 1 n d 1 0 z z
  have hge : (blastUdiv.go A 1 n d 1 0 z z).aig.decls.size ≤ A.decls.size :=
    Nat.le_of_not_lt fun hlt => by have := H A 1 n d 1 0 z z A.decls.size hlt; omega
  have hde := blastUdiv.go_decl_eq A 1 n d 1 0 z z
  let o := (blastUdiv.go A 1 n d 1 0 z z).q.get 0 (by decide)
  have hg := o.hgate
  refine not_lit (fun b0 b1 => b0 || !b1) (by decide) o.gate o.invert (by have := A_size; omega) fun b0 b1 => ?_
  rw [← nogrow_den _ hle hge hde]
  rw [blastUdiv.denote_go_eq_divRec_q A (asg b0 b1) 1 (bv [b0]) (bv [b1]) (bv [false]) (bv [false]) n d z z 1 0]
  · revert b0 b1; decide
  all_goals intro idx hidx; rw [den_vr]; revert b0 b1 idx; decide

-- helper: `blastAdd.go` from position `curr` never reads the `lhs` bits below `curr`
theorem add_go_congr {aig : AIG Nat} {w : Nat} (curr : Nat) (hcurr : curr ≤ w) (cin : aig.Ref)
    (s : aig.RefVec curr) (lhs lhs' rhs : aig.RefVec w)
    (h : ∀ i (hi : i < w), curr ≤ i → lhs.get i hi = lhs'.get i hi) :
    blastAdd.go aig lhs rhs curr hcurr cin s = blastAdd.go aig lhs' rhs curr hcurr cin s := by
  unfold blastAdd.go
  by_cases hidx : curr < w
  · simp only [hidx, ↓reduceDIte]
    rw [h curr hidx (Nat.le_refl _)]
    apply add_go_congr
    intro i hi hci
    simp only [AIG.RefVec.get_cast, h i hi (by omega)]
  · simp only [hidx, ↓reduceDIte]
termination_by w - curr

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq`: necessary; from position 1 with carry
-- `0`, the circuit for `lhs = [1, 0]` and `lhs = [0, 0]` (with `rhs = [1, 0]`) is the same (`go` never
-- reads bit 0), but without `hcin` the statement gives output bit 1 = `1` for the first and `0`
-- for the second.
theorem add_hcin_16 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq 16 := by
  intro H
  let rhs := vr [(0, true), (0, false)] (by decide)
  let l1 := vr [(0, true), (0, false)] (by decide)
  let l2 := vr [(0, false), (0, false)] (by decide)
  let cin : A.Ref := ⟨0, false, A.hzero⟩
  let s := vr [(0, false)] (by decide)
  have e := add_go_congr 1 (by decide) cin s l1 l2 rhs (by
    intro i hi hci
    have hi' : i < 2 := hi
    have : i = 1 := by omega
    subst this; rfl)
  have h1 := H A 1 (by decide) cin s l1 rhs (asg false false) (bv [true, false]) (bv [true, false])
    (by intro idx hidx; rw [den_vr]; revert idx; decide)
    (by intro idx hidx; rw [den_vr]; revert idx; decide) 1 (by decide) (by decide)
  have h2 := H A 1 (by decide) cin s l2 rhs (asg false false) (bv [false, false]) (bv [true, false])
    (by intro idx hidx; rw [den_vr]; revert idx; decide)
    (by intro idx hidx; rw [den_vr]; revert idx; decide) 1 (by decide) (by decide)
  rw [e, den_vr] at h1
  rw [h1, den_vr, den_vr] at h2
  revert h2; decide

end BVGrowHand
