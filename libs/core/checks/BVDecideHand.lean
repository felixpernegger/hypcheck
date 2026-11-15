import Std
import Lean

/-!
Hand pass `BVDecide` (hand15): unresolved hypotheses of `Std.Tactic.BVDecide` (bitblaster circuits,
caches, LRAT checker, reflection). 241 of 257 decided: 209 necessary, 32 removable.

Reusable models and tools (namespace `BVDecideHand`):
* `refute_indep` (copied from `checks/StdDepHand.lean`) with two extensions: a hook `bv_extra` for extra
  premise provers (here the library's `*_go_le_size` lemmas and `Cache.Inv_empty`), and candidates for
  structures (fields filled recursively) and the empty `BVExpr`/`BVLogicalExpr` caches.
* `G α`: AIG `#[false, gate(¬0,¬0), gate(¬0,¬0)]` with the empty cache (no atoms, so `Cache.WF.empty`);
  `g1`, `g2` its two non-constant gate nodes. `gate_grow`: `mkGateCached` on two distinct non-constant
  nodes of an AIG whose cache misses everything adds a node (`G_grow`); `atom_grow`: the same for
  `mkAtomCached`. Growth of a recursive builder: unfold it once, bound the rest by the library's
  `go_le_size`/`LawfulOperator.le_size`, down to the first gate on `G`.
* `cb aig b` (constant reference to node 0) and `vb aig bs` (constant vector, least significant bit first)
  with simp lemmas `vb_get`, `den_cb`, `den0`, `denG`; tactic `dprem` proves premises
  `∀ i < n, ⟦v[i]⟧ = x.getLsbD i` over them, `dfin` closes the final `¬ a = b`.
* Two-instantiation refutations (`n_*`): the original theorem at the true specification values and the
  hypothetical `T'` at a wrong value for the dropped premise, with the same circuit on the left-hand side;
  the two right-hand sides evaluate to different bits. No circuit is ever evaluated. The same trick with a
  sibling lemma (`denote_go_eq_divRec_q/_r`) handles the division rows.
* Loops started at their last index return their accumulator `s` (`a_*`, `fin_s`).
* Caches with a wrong entry: `ebad` (`1#1 ↦ [false]`), `ebad2`, `lbad` (`true ↦ false`), `lbad2`; their
  lookup lemmas and `ebad_not_inv`/`lbad_not_inv` (through the library's `denote_eq_eval_of_get?_eq_some_of_Inv`);
  `ebad_goCache`/`lbad_goCache` (a cache hit returns the cache unchanged).
* LRAT: `st0` (empty state), `lsimp` (CNF/assignment satisfiability normalization via `sat_toCNF_iff`).

Removable (32): the `h2`-style bounds of 17 `*_go_decl_eq` and the 5 `hfoo` of `*_go_get_aux` (library
`go_le_size`); `h1` of `go_decl_eq` for the four reference-only loops (shift left/right by a constant,
zero extension, extract-and-extend: `go` returns `aig`); `hcurr` of `blastReplicate.go_get`
(`w * curr ≤ idx < w * n`); `hcurr` of `blastMul/ShiftLeft/ShiftRight/ArithShiftRight.go_denote_eq` (past the
end the loop returns `acc` and `mulRec`/`*Rec` are constant there); `hlt` of `udiv_ofNat_eq_of_lt`
(for `k ≥ w` both sides are `0`).

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/BVDecideHand.lean`.
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


set_option maxErrors 10000
set_option linter.deprecated false
/-! ## `refute_indep`: small-value counterexample search for `¬ ∀ xs, P`

Instantiates the binders one by one with small candidates and refutes the instantiated conclusion:
types `Nat`/`Bool`/`Unit` (monads `Id`/`Option`), instances by synthesis, `Nat` 0–3, `Bool`, AIG
values built from node 0 (`.false`, present in every AIG: `ref0`, `vec0`, `entry0`), constant
functions, else `default`/`Classical.ofNonempty`. Prop premises are proved and the conclusion is
refuted by `decide`/`omega`/`simp`/`trivial`/`rfl`. Searches at most 150 proof attempts. -/

/-- Extra premise prover for `refute_indep`, extended below by `macro_rules`. -/
syntax "bv_extra" : tactic
macro_rules | `(tactic| bv_extra) => `(tactic| fail "bv_extra")

namespace RefuteIndep
open Std.Sat

/-- A reference to node 0 of any AIG. -/
def ref0 {α : Type} [DecidableEq α] [Hashable α] (aig : AIG α) : aig.Ref := ⟨0, false, aig.hzero⟩
/-- The inverted reference to node 0. -/
def ref1 {α : Type} [DecidableEq α] [Hashable α] (aig : AIG α) : aig.Ref := ⟨0, true, aig.hzero⟩
/-- A vector of `n` references to node 0. -/
def vec0 {α : Type} [DecidableEq α] [Hashable α] (aig : AIG α) : (n : Nat) → aig.RefVec n
  | 0 => .empty
  | n + 1 => (vec0 aig n).push (ref0 aig)
/-- The empty AIG with a reference to its node 0. -/
def entry0 {α : Type} [DecidableEq α] [Hashable α] : AIG.Entrypoint α := ⟨.empty, ref0 _⟩

open Lean Meta Elab Tactic

/-- `c` applied to fresh metavariables, if its result type unifies with `d` and no metavariable is left. -/
def instAt (c : Name) (d : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let e ← mkConstWithFreshMVarLevels c
    let (xs, bis, r) ← forallMetaTelescopeReducing (← inferType e)
    if ← isDefEq r d then
      for x in xs, bi in bis do
        if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
          let some i ← synthInstance? (← instantiateMVars (← inferType x)) | pure ()
          discard <| isDefEq x i
      let v ← instantiateMVars (mkAppN e xs)
      if !v.hasExprMVar then return some v
    s.restore; return none
  catch _ => s.restore; return none

/-- `c` applied to its leading implicit and instance arguments only, if its type then unifies with `d`. -/
def instAtFn (c : Name) (d : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let e ← mkConstWithFreshMVarLevels c
    let mut e := e
    let mut t ← inferType e
    let mut insts := #[]
    repeat
      let .forallE _ dom b bi := t | break
      if bi.isExplicit then break
      let m ← mkFreshExprMVar dom
      if bi.isInstImplicit then insts := insts.push m
      e := mkApp e m; t := b.instantiate1 m
    if ← isDefEq t d then
      for m in insts do
        unless ← m.mvarId!.isAssigned do
          let some i ← synthInstance? (← instantiateMVars (← inferType m)) | pure ()
          discard <| isDefEq m i
      let v ← instantiateMVars e
      if !v.hasExprMVar then return some v
    s.restore; return none
  catch _ => s.restore; return none

def proveBy (budget : IO.Ref Nat) (ty : Expr) : TacticM (Option Expr) := do
  if (← budget.get) == 0 then return none
  budget.modify (· - 1)
  let s ← saveState
  let msgs := (← getThe Core.State).messages
  let mv ← mkFreshExprMVar ty
  try
    let gs ← withoutRecover <| Tactic.run mv.mvarId! (evalTactic (← `(tactic|
      first | decide | omega | (simp; done) | trivial | rfl | (intro h; simp at h) | (intro h; omega) | (intros; omega) | (intros; simp_all; done) | (simp_all; done) | bv_extra)))
    modifyThe Core.State ({ · with messages := msgs })
    if gs.isEmpty then
      let p ← instantiateMVars mv
      unless p.hasExprMVar || p.hasSorry do return some p
    s.restore; modifyThe Core.State ({ · with messages := msgs }); return none
  catch _ => s.restore; modifyThe Core.State ({ · with messages := msgs }); return none

partial def cands (budget : IO.Ref Nat) (d : Expr) (bi : BinderInfo) : TacticM (Array Expr) := do
  let d ← instantiateMVars d
  if bi.isInstImplicit || (← isClass? d).isSome then
    return (← try synthInstance? d catch _ => pure none).toArray
  if ← isProp d then return (← proveBy budget d).toArray
  let dw ← whnfR d
  if let .sort u := dw then
    if ← isLevelDefEq u Level.one then return #[mkConst ``Nat, mkConst ``Bool, mkConst ``Unit]
    if ← isLevelDefEq u Level.zero then return #[mkConst ``True, mkConst ``False]
    return #[]
  if let .forallE _ (.sort _) (.sort _) _ := dw then
    return #[mkConst ``Id [Level.zero], mkConst ``Option [Level.zero]]
  if d.isConstOf ``Nat then return #[0, 1, 2, 3].map mkNatLit
  if d.isConstOf ``Bool then return #[mkConst ``Bool.false, mkConst ``Bool.true]
  if d.isConstOf ``Int then return #[mkIntLit 0, mkIntLit 1, mkIntLit (-1)]
  let mut out := #[]
  for c in [``Std.Sat.AIG.empty, ``ref0, ``ref1, ``vec0, ``entry0,
      ``Std.Tactic.BVDecide.BVExpr.Cache.empty, ``Std.Tactic.BVDecide.BVLogicalExpr.Cache.empty] do
    if let some v ← instAt c d then out := out.push v
  unless out.isEmpty do return out
  if dw.isForall then
    for c in [``Std.Sat.AIG.mkAndCached, ``Std.Sat.AIG.mkOrCached, ``Std.Sat.AIG.mkNotCached,
        ``Std.Sat.AIG.mkIfCached, ``Std.Sat.AIG.RefVec.ite, ``Std.Sat.AIG.RefVec.map] do
      if let some v ← instAtFn c d then out := out.push v
    unless out.isEmpty do return out
  if dw.isForall then
    let r ← forallTelescope dw fun xs body => do
      if ← isProp body then return #[]
      let cs ← cands budget body .default
      cs.extract 0 2 |>.mapM (mkLambdaFVars xs ·)
    unless r.isEmpty do return r
  -- structures: fill the fields with the first candidate of each field type
  if let .const sn _ := dw.getAppFn then
    if isStructure (← getEnv) sn then
      let ctor := getStructureCtor (← getEnv) sn
      let st ← saveState
      try
        let e ← mkConstWithFreshMVarLevels ctor.name
        let (xs, bis, r) ← forallMetaTelescopeReducing (← inferType e)
        if ← isDefEq r d then
          let mut ok := true
          for x in xs, bi in bis do
            unless ← x.mvarId!.isAssigned do
              let cs ← cands budget (← instantiateMVars (← inferType x)) bi
              match cs[0]? with
              | some c => unless ← isDefEq x c do ok := false
              | none => ok := false
          let v ← instantiateMVars (mkAppN e xs)
          if ok && !v.hasExprMVar then return #[v]
        st.restore
      catch _ => st.restore
  if let some i ← (try synthInstance? (mkApp (mkConst ``Inhabited [← getLevel d]) d) catch _ => pure none) then
    return #[mkApp2 (mkConst ``Inhabited.default [← getLevel d]) d i]
  if let some i ← (try synthInstance? (mkApp (mkConst ``Nonempty [← getLevel d]) d) catch _ => pure none) then
    return #[mkApp2 (mkConst ``Classical.ofNonempty [← getLevel d]) d i]
  return #[]

partial def go (budget : IO.Ref Nat) (e ty : Expr) : TacticM (Option Expr) := do
  if (← budget.get) == 0 then return none
  let ty ← instantiateMVars ty
  let ty ← if ty.isForall then pure ty else whnfR ty
  match ty with
  | .forallE _ d b bi =>
    let cs ← cands budget d bi
    -- a binder the rest does not mention needs only one value
    let cs := if b.hasLooseBVars then cs else cs.extract 0 1
    for c in cs do
      if let some p ← go budget (mkApp e c) (b.instantiate1 c) then return some p
    return none
  | _ =>
    let some np ← proveBy budget (mkNot ty) | return none
    logInfo m!"refute_indep: {e}"
    return some (mkApp np e)

elab "refute_indep" : tactic => do
  let g ← getMainGoal
  let some (h, g') ← observing? g.intro1 | throwError "refute_indep: goal is not a negation"
  g'.withContext do
    let budget ← IO.mkRef 150
    let some p ← go budget (mkFVar h) (← h.getType) | throwError "refute_indep: no counterexample"
    g'.assign p
  replaceMainGoal []

end RefuteIndep

open Std.Sat Std.Tactic.BVDecide

namespace BVDecideHand
variable {α : Type} [Hashable α] [DecidableEq α]

/-- Decls: false, then two (non-constant) gates. -/
def gdecls (α : Type) : Array (AIG.Decl α) :=
  #[.false, .gate (.mk 0 true) (.mk 0 true), .gate (.mk 0 true) (.mk 0 true)]

def G (α : Type) [Hashable α] [DecidableEq α] : AIG α where
  decls := gdecls α
  cache := ⟨{}, AIG.Cache.WF.empty (by
    intro i h a
    have : i < 3 := h
    match i, this with
    | 0, _ | 1, _ | 2, _ => simp [gdecls])⟩
  hdag := by
    intro i l r h hd
    have : i < 3 := h
    match i, this with
    | 0, _ => simp [gdecls] at hd
    | 1, _ => simp [gdecls] at hd; obtain ⟨rfl, rfl⟩ := hd; exact ⟨by decide, by decide⟩
    | 2, _ => simp [gdecls] at hd; obtain ⟨rfl, rfl⟩ := hd; exact ⟨by decide, by decide⟩
  hzero := by show 0 < 3; decide
  hconst := rfl

def g1 : (G α).Ref := ⟨1, false, by show 1 < 3; decide⟩
def g2 : (G α).Ref := ⟨2, false, by show 2 < 3; decide⟩

theorem G_size : (G α).decls.size = 3 := rfl

theorem gate_grow (aig : AIG α) (input : AIG.BinaryInput aig)
    (hmiss : ∀ d : AIG.Decl α, aig.cache.val[d]? = none)
    (hl : aig.getConstant input.lhs = none) (hr : aig.getConstant input.rhs = none)
    (hne : input.lhs.gate ≠ input.rhs.gate) :
    aig.decls.size < (aig.mkGateCached input).aig.decls.size := by
  obtain ⟨decls, cache, hdag, hzero, hconst⟩ := aig
  obtain ⟨⟨lg, li, lh⟩, ⟨rg, ri, rh⟩⟩ := input
  simp only at hne
  have hm : ∀ d, cache.get? d = none := fun d => AIG.Cache.get?_eq_none_iff.mpr (hmiss d)
  unfold AIG.mkGateCached
  dsimp only
  split <;>
  · unfold AIG.mkGateCached.go
    dsimp only
    split
    · rename_i h; simp [hm] at h
    · simp only at hl hr; simp [hl, hr, hne, Ne.symm hne]

theorem G_miss : ∀ d : AIG.Decl α, (G α).cache.val[d]? = none := fun _ => Std.HashMap.getElem?_empty

/-- The first gate built on `G` from its two gate nodes adds a node. -/
theorem G_grow : (G α).decls.size < ((G α).mkGateCached ⟨g1, g2⟩).aig.decls.size :=
  gate_grow _ _ G_miss rfl rfl (by simp [g1, g2])


/-- A reference to node 0 denotes its inverter bit. -/
theorem den0 {aig : AIG α} {h} {inv : Bool} {assign : α → Bool} :
    AIG.denote assign ⟨aig, ⟨0, inv, h⟩⟩ = inv := AIG.denote_idx_false aig.hconst

/-- A reference to node 0 denotes its inverter bit. -/
theorem denG {aig : AIG α} {r : aig.Ref} {assign : α → Bool} (h : r.gate = 0) :
    AIG.denote assign ⟨aig, r⟩ = r.invert := by
  obtain ⟨g, i, hg⟩ := r; subst h; exact den0

/-- The constant `b` as a reference to node 0. -/
def cb (aig : AIG α) (b : Bool) : aig.Ref := ⟨0, b, aig.hzero⟩

/-- The constant vector `bs` (least significant bit first) as references to node 0. -/
def vb (aig : AIG α) (bs : List Bool) : aig.RefVec bs.length :=
  ⟨Vector.ofFn fun i => AIG.Fanin.mk 0 bs[i], by intro i h; simp [AIG.Fanin.gate_mk, aig.hzero]⟩

@[simp] theorem vb_get (aig : AIG α) (bs : List Bool) (i : Nat) (h : i < bs.length) :
    (vb aig bs).get i h = cb aig bs[i] := by
  simp [vb, cb, AIG.RefVec.get, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

@[simp] theorem den_cb {aig : AIG α} {b : Bool} {assign : α → Bool} :
    AIG.denote assign ⟨aig, cb aig b⟩ = b := den0

/-- Premises `∀ i < n, ⟦v[i]⟧ = x.getLsbD i` and `⟦cb b⟧ = c` over constant references. -/
macro "dprem" : tactic => `(tactic| first
  | decide
  | (simp only [BVDecideHand.den_cb, BVDecideHand.vb_get]; done)
  | (simp only [BVDecideHand.den_cb, BVDecideHand.vb_get]; decide)
  | (intro i h; simp only [BVDecideHand.vb_get, BVDecideHand.den_cb]; revert i h; decide))

/-- Closes `¬ a = b` between two evaluated specifications. -/
macro "dfin" : tactic => `(tactic| first
  | decide
  | (simp only [BVDecideHand.den_cb, BVDecideHand.vb_get]; decide))

/-- An assignment of `BVExpr` variables. -/
def asg0 : BVExpr.Assignment := .leaf ⟨0#0⟩

/-- The shift-by-constant loop only collects references. -/
theorem slc_go_aig {w : Nat} (aig : AIG α) (input : aig.RefVec w) (distance curr : Nat) (hcurr : curr ≤ w)
    (s : aig.RefVec curr) :
    (BVExpr.bitblast.blastShiftLeftConst.go aig input distance curr hcurr s).aig = aig := by
  unfold BVExpr.bitblast.blastShiftLeftConst.go
  split
  · dsimp only; split <;> apply slc_go_aig
  · simp
termination_by w - curr

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_decl_eq`: removable, `go` returns `aig` unchanged.
theorem t_slc_11 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_decl_eq 11 := by
  intro α _ _ w aig distance input curr hcurr s idx h
  rwa [slc_go_aig] at h

-- `Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_decl_eq`: one full adder on the gates of `G` adds a node.
theorem t_ovf_10 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_decl_eq 10 := by
  intro H
  have := H (α := Nat) (w := 1) (curr := 0) (aig := G Nat) (cin := g1)
    (lhs := AIG.RefVec.empty.push g1) (rhs := AIG.RefVec.empty.push g2) 3 (by
      show (G Nat).decls.size < _
      unfold BVExpr.bitblast.mkOverflowBit.go
      rw [dif_pos (by decide)]
      dsimp only
      refine Nat.lt_of_lt_of_le ?_ (by apply BVExpr.bitblast.mkOverflowBit.go_le_size)
      unfold BVExpr.bitblast.mkFullAdderCarry
      dsimp only
      refine Nat.lt_of_lt_of_le ?_ (AIG.LawfulOperator.le_size (f := AIG.mkOrCached) ..)
      refine Nat.lt_of_lt_of_le ?_ (AIG.LawfulOperator.le_size (f := AIG.mkAndCached) ..)
      refine Nat.lt_of_lt_of_le ?_ (AIG.LawfulOperator.le_size (f := AIG.mkAndCached) ..)
      unfold AIG.mkXorCached
      dsimp only
      refine Nat.lt_of_lt_of_le ?_ (AIG.LawfulOperator.le_size (f := AIG.mkGateCached) ..)
      refine Nat.lt_of_lt_of_le ?_ (AIG.LawfulOperator.le_size (f := AIG.mkGateCached) ..)
      exact G_grow)
  exact absurd this (by decide)


macro_rules | `(tactic| bv_extra) => `(tactic| first | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopTree.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastCpop_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastExtractAndExtend.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.blastDivSubtractShift_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_le_size) | (apply Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_le_size))

-- `Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_mkOverflowBit_go_decl_eq_11 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_decl_eq 11 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastAdd_go_decl_eq_13 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_decl_eq 13 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastClz_go_decl_eq_9 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_decl_eq 9 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastExtractAndExtend.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastExtractAndExtend_go_decl_eq_13 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastExtractAndExtend.go_decl_eq 13 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastExtractAndExtend.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastCpopLayer_go_decl_eq_13 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer.go_decl_eq 13 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopTree.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastCpopTree_go_decl_eq_9 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopTree.go_decl_eq 9 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopTree.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastCpop_decl_eq`: removable, `idx < aig.decls.size` and `blastCpop_le_size` give the bound for the result.
theorem t_blastCpop_decl_eq_7 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastCpop_decl_eq 7 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastCpop_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastMul_go_decl_eq_11 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_decl_eq 11 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastShiftLeftConst_go_decl_eq_12 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_decl_eq 12 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastShiftLeft_go_decl_eq_11 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_decl_eq 11 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastShiftRightConst_go_decl_eq_12 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_decl_eq 12 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastShiftRight_go_decl_eq_11 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_decl_eq 11 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastArithShiftRight_go_decl_eq_11 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_decl_eq 11 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.blastDivSubtractShift_decl_eq`: removable, `idx < aig.decls.size` and `blastDivSubtractShift_le_size` give the bound for the result.
theorem t_blastUdiv_blastDivSubtractShift_decl_eq_13 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.blastDivSubtractShift_decl_eq 13 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.blastDivSubtractShift_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastUdiv_go_decl_eq_14 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.go_decl_eq 14 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastZeroExtend_go_decl_eq_12 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_decl_eq 12 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_decl_eq`: removable, `idx < aig.decls.size` and `go_le_size` give the bound for the result.
theorem t_blastVar_go_decl_eq_8 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_decl_eq 8 := by
  intros; apply Nat.lt_of_lt_of_le (by assumption); apply Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_get_aux`: removable, the size bound is `go_le_size`.
theorem t_blastAdd_go_get_aux_13 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_get_aux 13 := by
  intros; apply Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_get_aux`: removable, the size bound is `go_le_size`.
theorem t_blastShiftLeftConst_go_get_aux_12 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_get_aux 12 := by
  intros; apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_get_aux`: removable, the size bound is `go_le_size`.
theorem t_blastShiftRightConst_go_get_aux_12 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_get_aux 12 := by
  intros; apply Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_get_aux`: removable, the size bound is `go_le_size`.
theorem t_blastZeroExtend_go_get_aux_12 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_get_aux 12 := by
  intros; apply Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_get_aux`: removable, the size bound is `go_le_size`.
theorem t_blastVar_go_get_aux_8 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_get_aux 8 := by
  intros; apply Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_le_size

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_get_aux`: `curr = 0` (empty prefix `s`), the size premise holds by the library bound.
theorem t_blastAdd_go_get_aux_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_get_aux 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_get_aux`: `curr = 0` (empty prefix `s`), the size premise holds by the library bound.
theorem t_blastShiftLeftConst_go_get_aux_11 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_get_aux 11 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_get_aux`: `curr = 0` (empty prefix `s`), the size premise holds by the library bound.
theorem t_blastShiftRightConst_go_get_aux_11 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_get_aux 11 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_get_aux`: `curr = 0` (empty prefix `s`), the size premise holds by the library bound.
theorem t_blastZeroExtend_go_get_aux_11 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_get_aux 11 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_get_aux`: `curr = 0` (empty prefix `s`), the size premise holds by the library bound.
theorem t_blastVar_go_get_aux_7 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_get_aux 7 := by refute_indep


-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.mkFullAdder_denote_mem_prefix`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_blastAdd_mkFullAdder_denote_mem_prefix_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.mkFullAdder_denote_mem_prefix 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.denote_blast`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_blastAdd_denote_blast_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.denote_blast 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAdd`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastAdd_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAdd 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAppend`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastAppend_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAppend 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtract`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastExtract_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtract 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.denote_blast`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_blastMul_denote_blast_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.denote_blast 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastMul`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastMul_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastMul 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastReplicate`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastReplicate_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastReplicate 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastRotateLeft`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastRotateLeft_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastRotateLeft 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastRotateRight`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastRotateRight_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastRotateRight 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeftConst`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastShiftLeftConst_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeftConst 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.twoPowShift_eq`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_blastShiftLeft_twoPowShift_eq_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.twoPowShift_eq 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeft`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastShiftLeft_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeft 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRightConst`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastShiftRightConst_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRightConst 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRightConst`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastArithShiftRightConst_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRightConst 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.twoPowShift_eq`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_blastShiftRight_twoPowShift_eq_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.twoPowShift_eq 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRight`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastShiftRight_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRight 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.twoPowShift_eq`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_blastArithShiftRight_twoPowShift_eq_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.twoPowShift_eq 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRight`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastArithShiftRight_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRight 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastSub`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastSub_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastSub 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_blastUdiv_denote_blastShiftConcat_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat 8 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUdiv`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastUdiv_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUdiv 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUmod`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastUmod_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUmod 12 := by refute_indep

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastZeroExtend`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_BVExpr_bitblast_denote_blastZeroExtend_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastZeroExtend 8 := by refute_indep

-- `Std.Tactic.BVDecide.LRAT.Internal.State.get?_add_one_of_getElem_eq_some`: small instance found by `refute_indep` (width 0 or 1, refs to node 0, empty caches).
set_option maxHeartbeats 400000 in
theorem r_LRAT_Internal_State_get_add_one_of_getElem_eq_some_3 : ¬ indep0% Std.Tactic.BVDecide.LRAT.Internal.State.get?_add_one_of_getElem_eq_some 3 := by refute_indep


open RefuteIndep


/-- Premises `⟦…⟧ = b` and `∀ i < 1, ⟦…[i]⟧ = …` over references to node 0. -/
macro "den1" : tactic => `(tactic| first
  | (rw [BVDecideHand.denG] <;> simp [RefuteIndep.vec0, RefuteIndep.ref0, RefuteIndep.ref1, AIG.RefVec.get,
      AIG.RefVec.push, AIG.RefVec.empty]; done)
  | (intro i h; match i, h with
      | 0, _ => (rw [BVDecideHand.denG] <;> simp [RefuteIndep.vec0, RefuteIndep.ref0, RefuteIndep.ref1,
        AIG.RefVec.get, AIG.RefVec.push, AIG.RefVec.empty]) <;> decide))

/-- The `BVExpr` cache with the single entry `(0#0) ↦ []`. -/
def ec1 (aig : AIG BVBit) : BVExpr.Cache aig := BVExpr.Cache.empty.insert (BVExpr.const 0#0) .empty

theorem ec1_get? (aig : AIG BVBit) : (ec1 aig).get? (BVExpr.const 0#0) = some .empty := by
  rw [BVExpr.Cache.get?_eq_some_iff]; simp [ec1, BVExpr.Cache.insert, BVExpr.Cache.empty, AIG.RefVec.empty]

theorem ec1_mem (aig : AIG BVBit) : (⟨0, BVExpr.const 0#0⟩ : BVExpr.Cache.Key) ∈ (ec1 aig).map := by
  simp [ec1, BVExpr.Cache.insert, BVExpr.Cache.empty]

theorem ec1_inv (aig : AIG BVBit) (assign) : BVExpr.Cache.Inv assign aig (ec1 aig) :=
  BVExpr.Cache.Inv_insert _ _ _ (BVExpr.Cache.Inv_empty _) (fun _ h => absurd h (Nat.not_lt_zero _))

-- `Std.Tactic.BVDecide.BVExpr.Cache.hbound`: the empty cache contains no key.
theorem t_BVExpr_Cache_hbound_4 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.Cache.hbound 4 := fun H =>
  absurd (H (aig := AIG.empty) BVExpr.Cache.empty (i := 0) ⟨1, .const 0#1⟩ (by decide))
    (by simp [BVExpr.Cache.empty])

-- `Std.Tactic.BVDecide.BVExpr.Cache.hbound`: a cache entry of width 0 and `i = 0`.
theorem t_BVExpr_Cache_hbound_5 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.Cache.hbound 5 := fun H =>
  Nat.lt_irrefl 0 (H (aig := AIG.empty) (ec1 _) (i := 0) _ (ec1_mem _))

-- `Std.Tactic.BVDecide.BVExpr.bitblast.FullAdderInput.lhs_cast`: `aig1` with three nodes, `aig2` empty.
theorem t_lhs_cast_6 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.FullAdderInput.lhs_cast 6 := fun H =>
  absurd (H (α := Nat) (aig1 := G Nat) (aig2 := AIG.empty) ⟨g1, g1, g1⟩) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.FullAdderInput.rhs_cast`: as for `lhs_cast`.
theorem t_rhs_cast_6 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.FullAdderInput.rhs_cast 6 := fun H =>
  absurd (H (α := Nat) (aig1 := G Nat) (aig2 := AIG.empty) ⟨g1, g1, g1⟩) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.FullAdderInput.cin_cast`: as for `lhs_cast`.
theorem t_cin_cast_6 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.FullAdderInput.cin_cast 6 := fun H =>
  absurd (H (α := Nat) (aig1 := G Nat) (aig2 := AIG.empty) ⟨g1, g1, g1⟩) (by decide)

-- `Std.Tactic.BVDecide.BVLogicalExpr.Cache.hbound`: the empty cache contains no key.
theorem t_BVLogicalExpr_Cache_hbound_3 : ¬ indep0% Std.Tactic.BVDecide.BVLogicalExpr.Cache.hbound 3 := fun H =>
  absurd (H (aig := AIG.empty) BVLogicalExpr.Cache.empty (.const true)) (by simp [BVLogicalExpr.Cache.empty])

-- `Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_denote_mem_prefix`: `start = 1` in the empty AIG.
theorem t_lgoCache_denote_mem_prefix_6 :
    ¬ indep0% Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_denote_mem_prefix 6 := fun H =>
  absurd (H (assign := fun _ => false) (expr := .const true) (start := 1) (inv := false) AIG.empty
    BVLogicalExpr.Cache.empty) (by decide)

-- `Std.Tactic.BVDecide.BVLogicalExpr.Cache.Inv_cast`: `aig1` with three nodes is no prefix of the empty AIG.
theorem t_lInv_cast_4 : ¬ indep0% Std.Tactic.BVDecide.BVLogicalExpr.Cache.Inv_cast 4 := fun H =>
  absurd (H (aig1 := G BVBit) (assign := asg0) (aig2 := AIG.empty) BVLogicalExpr.Cache.empty
    (BVLogicalExpr.Cache.Inv_empty _)).size_le (by decide)

-- `Std.Tactic.BVDecide.BVExpr.Cache.Inv_cast`: `aig1` with three nodes is no prefix of the empty AIG.
theorem t_Inv_cast_4 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.Cache.Inv_cast 4 := fun H =>
  absurd (H (aig1 := G BVBit) (assign := asg0) (aig2 := AIG.empty) BVExpr.Cache.empty
    (BVExpr.Cache.Inv_empty _)).size_le (by decide)

-- `Std.Tactic.BVDecide.BVExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv`: width 0, the entry `0#0 ↦ []`.
theorem t_denote_eq_eval_of_get_9 :
    ¬ indep0% Std.Tactic.BVDecide.BVExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv 9 := fun H =>
  Nat.lt_irrefl 0 (H (aig := AIG.empty) (assign := asg0) (ec1 _) _ _ (ec1_get? _) (ec1_inv _ _) 0)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.go_denote_mem_prefix`: `start = 1` in the empty AIG.
theorem t_go_denote_mem_prefix_7 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.go_denote_mem_prefix 7 := fun H =>
  absurd (H (w := 0) (inv := false) AIG.empty (.const 0#0) asg0 BVExpr.Cache.empty 1) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_denote_mem_prefix`: `start = 1` in the empty AIG.
theorem t_goCache_denote_mem_prefix_7 :
    ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.goCache_denote_mem_prefix 7 := fun H =>
  absurd (H (w := 0) (inv := false) AIG.empty (.const 0#0) asg0 BVExpr.Cache.empty 1) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast_denote_mem_prefix`: `start = 1` in the empty AIG.
theorem t_bitblast_denote_mem_prefix_6 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast_denote_mem_prefix 6 :=
  fun H => absurd (H (w := 0) (inv := false) AIG.empty ⟨.const 0#0, BVExpr.Cache.empty⟩ asg0 1) (by decide)

-- `Std.Tactic.BVDecide.BVPred.bitblast_denote_mem_prefix`: `start = 1` in the empty AIG.
theorem t_pbitblast_denote_mem_prefix_5 : ¬ indep0% Std.Tactic.BVDecide.BVPred.bitblast_denote_mem_prefix 5 :=
  fun H => absurd (H (inv := false) AIG.empty ⟨.getLsbD (.const 0#1) 0, BVExpr.Cache.empty⟩ asg0 1)
    (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_denote_eq`: width 0, empty cache.
theorem t_goCache_denote_eq_7 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.goCache_denote_eq 7 := fun H =>
  Nat.lt_irrefl 0 (H (w := 0) AIG.empty (.const 0#0) asg0 BVExpr.Cache.empty (BVExpr.Cache.Inv_empty _) 0)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.go_denote_eq`: width 0, empty cache.
theorem t_go_denote_eq_7 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.go_denote_eq 7 := fun H =>
  Nat.lt_irrefl 0 (H (w := 0) AIG.empty (.const 0#0) asg0 BVExpr.Cache.empty (BVExpr.Cache.Inv_empty _) 0)

-- `Std.Tactic.BVDecide.BVExpr.denote_bitblast`: width 0, empty cache.
theorem t_denote_bitblast_6 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.denote_bitblast 6 := fun H =>
  Nat.lt_irrefl 0 (H (w := 0) AIG.empty ⟨.const 0#0, BVExpr.Cache.empty⟩ asg0 (BVExpr.Cache.Inv_empty _) 0)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq`: `w = curr = idx = 0`.
theorem t_blastAdd_go_denote_eq_18 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq 18 :=
  fun H => Nat.lt_irrefl 0 (H (α := Nat) (w := 0) AIG.empty 0 (Nat.le_refl 0) (ref0 _) .empty .empty .empty
    (fun _ => false) 0#0 0#0 (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (by den1) 0 (Nat.le_refl 0))

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq`: `w = 1`, `curr = 0`, `idx = 1`, all refs `false`.
theorem t_blastMul_go_denote_eq_17 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq 17 :=
  fun H => Nat.lt_irrefl 1 (H (α := Nat) (w := 1) AIG.empty 0 (Nat.le_refl 1) (vec0 _ 1) (vec0 _ 1) (vec0 _ 1)
    0#1 0#1 (fun _ => false) (by den1) (by den1) (by den1) 1)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.go_get`: removable, `w * curr ≤ idx < w * n` gives `curr < n`.
theorem t_blastReplicate_go_get_7 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.go_get 7 := by
  intro α _ _ w aig n curr input s idx h1 h2
  exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h2 h1))

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat_eq_shiftConcat`: width 0.
theorem t_denote_blastShiftConcat_eq_shiftConcat_12 :
    ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat_eq_shiftConcat 12 := fun H =>
  Nat.lt_irrefl 0 (H (α := Nat) (w := 0) AIG.empty ⟨.empty, ref0 _⟩ 0#0 false (fun _ => false)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (by den1) 0)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go`: `w = 1`, `lhs = 0`, `rhs = 1`, `idx = 1`.
theorem t_udiv_denote_go_18 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go 18 := fun H =>
  Nat.lt_irrefl 1 (H (α := Nat) (w := 1) AIG.empty (fun _ => false) 0#1 1#1 (vec0 _ 1)
    (AIG.RefVec.empty.push (ref1 _)) (vec0 _ 1) (vec0 _ 1) (by den1) (by den1) (by den1) (by den1)
    (by decide) 1)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go`: `w = 1`, `lhs = 0`, `rhs = 1`, `idx = 1`.
theorem t_umod_denote_go_18 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go 18 := fun H =>
  Nat.lt_irrefl 1 (H (α := Nat) (w := 1) AIG.empty (fun _ => false) 0#1 1#1 (vec0 _ 1)
    (AIG.RefVec.empty.push (ref1 _)) (vec0 _ 1) (vec0 _ 1) (by den1) (by den1) (by den1) (by den1)
    (by decide) 1)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq`: `w = curr = idx = 0`.
theorem t_blastVar_go_denote_eq_8 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq 8 :=
  fun H => Nat.lt_irrefl 0 (H (w := 0) AIG.empty 0 asg0 0 (Nat.le_refl 0) .empty 0 (Nat.le_refl 0))

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastVar`: width 0.
theorem t_denote_blastVar_5 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastVar 5 :=
  fun H => Nat.lt_irrefl 0 (H (w := 0) AIG.empty ⟨0⟩ asg0 0)


-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAdd`: the same circuit at true values {lhs: 0#1, rhs: 0#1} and at {lhs: 1#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_denote_blastAdd_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAdd 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAdd (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAdd`: the same circuit at true values {lhs: 0#1, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_denote_blastAdd_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAdd 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastAdd (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.denote_blast`: the same circuit at true values {lhs: 0#1, rhs: 0#1} and at {lhs: 1#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastAdd_denote_blast_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.denote_blast 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.denote_blast (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.denote_blast`: the same circuit at true values {lhs: 0#1, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_blastAdd_denote_blast_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.denote_blast 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.denote_blast (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastSub`: the same circuit at true values {lhs: 0#1, rhs: 0#1} and at {lhs: 1#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_denote_blastSub_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastSub 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastSub (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastSub`: the same circuit at true values {lhs: 0#1, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_denote_blastSub_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastSub 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastSub (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastMul`: the same circuit at true values {lhs: 1#1, rhs: 1#1} and at {lhs: 0#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_denote_blastMul_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastMul 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastMul (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 0#1) (rhs := 1#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastMul`: the same circuit at true values {lhs: 1#1, rhs: 1#1} and at {rhs: 0#1} (dropped `hright`).
theorem n_BVExpr_bitblast_denote_blastMul_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastMul 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastMul (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.denote_blast`: the same circuit at true values {lhs: 1#1, rhs: 1#1} and at {lhs: 0#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastMul_denote_blast_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.denote_blast 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.denote_blast (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 0#1) (rhs := 1#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.denote_blast`: the same circuit at true values {lhs: 1#1, rhs: 1#1} and at {rhs: 0#1} (dropped `hright`).
theorem n_BVExpr_bitblast_blastMul_denote_blast_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.denote_blast 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.denote_blast (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUdiv`: the same circuit at true values {lhs: 1#1, rhs: 1#1} and at {lhs: 0#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_denote_blastUdiv_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUdiv 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUdiv (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 0#1) (rhs := 1#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUdiv`: the same circuit at true values {lhs: 1#1, rhs: 1#1} and at {rhs: 0#1} (dropped `hright`).
theorem n_BVExpr_bitblast_denote_blastUdiv_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUdiv 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUdiv (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [true]⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUmod`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {lhs: 0#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_denote_blastUmod_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUmod 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUmod (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUmod`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_denote_blastUmod_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUmod 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastUmod (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [true], vb _ [false]⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVPred.mkUlt_denote_eq`: the same circuit at true values {lhs: 0#1, rhs: 1#1} and at {lhs: 1#1} (dropped `hleft`).
theorem n_BVPred_mkUlt_denote_eq_9 : ¬ drop0% Std.Tactic.BVDecide.BVPred.mkUlt_denote_eq 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVPred.mkUlt_denote_eq (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [true]⟩) (lhs := 0#1) (rhs := 1#1) (hleft := by dprem) (hright := by dprem) ).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [true]⟩) (lhs := 1#1) (rhs := 1#1) (hright := by dprem) )) (by decide)

-- `Std.Tactic.BVDecide.BVPred.mkUlt_denote_eq`: the same circuit at true values {lhs: 0#1, rhs: 1#1} and at {rhs: 0#1} (dropped `hright`).
theorem n_BVPred_mkUlt_denote_eq_10 : ¬ drop0% Std.Tactic.BVDecide.BVPred.mkUlt_denote_eq 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVPred.mkUlt_denote_eq (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [true]⟩) (lhs := 0#1) (rhs := 1#1) (hleft := by dprem) (hright := by dprem) ).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨vb _ [false], vb _ [true]⟩) (lhs := 0#1) (rhs := 0#1) (hleft := by dprem) )) (by decide)

-- `Std.Tactic.BVDecide.BVPred.mkEq_denote_eq`: the same circuit at true values {lhs: 0#1, rhs: 0#1} and at {lhs: 1#1} (dropped `hleft`).
theorem n_BVPred_mkEq_denote_eq_9 : ¬ drop0% Std.Tactic.BVDecide.BVPred.mkEq_denote_eq 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVPred.mkEq_denote_eq (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (pair := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) ).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (pair := ⟨vb _ [false], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hright := by dprem) )) (by decide)

-- `Std.Tactic.BVDecide.BVPred.mkEq_denote_eq`: the same circuit at true values {lhs: 0#1, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVPred_mkEq_denote_eq_10 : ¬ drop0% Std.Tactic.BVDecide.BVPred.mkEq_denote_eq 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVPred.mkEq_denote_eq (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (pair := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) ).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (pair := ⟨vb _ [false], vb _ [false]⟩) (lhs := 0#1) (rhs := 1#1) (hleft := by dprem) )) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastNeg`: the same circuit at true values {value: 0#1} and at {value: 1#1} (dropped `htarget`).
theorem n_BVExpr_bitblast_denote_blastNeg_8 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastNeg 8 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastNeg (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := vb _ [false]) (value := 0#1) (htarget := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := vb _ [false]) (value := 1#1)  (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpop`: the same circuit at true values {x: 0#1} and at {x: 1#1} (dropped `hx`).
theorem n_BVExpr_bitblast_denote_blastCpop_8 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpop 8 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpop (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (xc := vb _ [false]) (x := 0#1) (hx := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (xc := vb _ [false]) (x := 1#1)  (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastClz`: the same circuit at true values {x: 0#1} and at {x: 1#1} (dropped `hx`).
theorem n_BVExpr_bitblast_denote_blastClz_8 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastClz 8 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastClz (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (xc := vb _ [false]) (x := 0#1) (hx := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (xc := vb _ [false]) (x := 1#1)  (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_denote_eq`: the same circuit at true values {x: 0#1} and at {x: 1#1} (dropped `hx`).
theorem n_BVExpr_bitblast_blastClz_go_denote_eq_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_denote_eq 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_denote_eq (w := 1) (curr := 0) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (xc := vb _ [false]) (acc := vb _ [true]) (x := 0#1) (hx := by dprem) (hacc := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (curr := 0) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (xc := vb _ [false]) (acc := vb _ [true]) (x := 1#1) (hacc := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.twoPowShift_eq`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {lhs: 0#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastShiftLeft_twoPowShift_eq_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.twoPowShift_eq 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.twoPowShift_eq (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false], 0⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false], 0⟩) (lhs := 0#1) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.twoPowShift_eq`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_blastShiftLeft_twoPowShift_eq_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.twoPowShift_eq 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.twoPowShift_eq (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false], 0⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false], 0⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.twoPowShift_eq`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {lhs: 0#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastShiftRight_twoPowShift_eq_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.twoPowShift_eq 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.twoPowShift_eq (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false], 0⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false], 0⟩) (lhs := 0#1) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.twoPowShift_eq`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_blastShiftRight_twoPowShift_eq_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.twoPowShift_eq 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.twoPowShift_eq (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false], 0⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false], 0⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.twoPowShift_eq`: the same circuit at true values {lhs: 1#2, rhs: 0#1} and at {lhs: 0#2} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastArithShiftRight_twoPowShift_eq_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.twoPowShift_eq 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.twoPowShift_eq (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true, false], vb _ [false], 0⟩) (lhs := 1#2) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true, false], vb _ [false], 0⟩) (lhs := 0#2) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.twoPowShift_eq`: the same circuit at true values {lhs: 1#2, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_blastArithShiftRight_twoPowShift_eq_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.twoPowShift_eq 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.twoPowShift_eq (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true, false], vb _ [false], 0⟩) (lhs := 1#2) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true, false], vb _ [false], 0⟩) (lhs := 1#2) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeft`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {lhs: 0#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_denote_blastShiftLeft_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeft 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeft (w0 := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w0 := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeft`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_denote_blastShiftLeft_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeft 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftLeft (w0 := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w0 := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false]⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRight`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {lhs: 0#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_denote_blastShiftRight_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRight 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRight (w0 := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w0 := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false]⟩) (lhs := 0#1) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRight`: the same circuit at true values {lhs: 1#1, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_denote_blastShiftRight_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRight 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastShiftRight (w0 := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false]⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w0 := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true], vb _ [false]⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRight`: the same circuit at true values {lhs: 1#2, rhs: 0#1} and at {lhs: 0#2} (dropped `hleft`).
theorem n_BVExpr_bitblast_denote_blastArithShiftRight_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRight 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRight (w0 := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true, false], vb _ [false]⟩) (lhs := 1#2) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w0 := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true, false], vb _ [false]⟩) (lhs := 0#2) (rhs := 0#1) (hright := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRight`: the same circuit at true values {lhs: 1#2, rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_denote_blastArithShiftRight_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRight 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastArithShiftRight (w0 := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true, false], vb _ [false]⟩) (lhs := 1#2) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w0 := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨1, vb _ [true, false], vb _ [false]⟩) (lhs := 1#2) (rhs := 1#1) (hleft := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat_eq_shiftConcat`: the same circuit at true values {x: 0#2, b: false} and at {x: 1#2} (dropped `hx`).
theorem n_BVExpr_bitblast_blastUdiv_denote_blastShiftConcat_eq_shiftConcat_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat_eq_shiftConcat 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat_eq_shiftConcat (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨vb _ [false, false], cb _ false⟩) (x := 0#2) (b := false) (hx := by dprem) (hb := by dprem) (idx := 1) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨vb _ [false, false], cb _ false⟩) (x := 1#2) (b := false) (hb := by dprem) (idx := 1) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat_eq_shiftConcat`: the same circuit at true values {x: 0#2, b: false} and at {b: true} (dropped `hb`).
theorem n_BVExpr_bitblast_blastUdiv_denote_blastShiftConcat_eq_shiftConcat_10 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat_eq_shiftConcat 10 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastShiftConcat_eq_shiftConcat (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨vb _ [false, false], cb _ false⟩) (x := 0#2) (b := false) (hx := by dprem) (hb := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (target := ⟨vb _ [false, false], cb _ false⟩) (x := 0#2) (b := true) (hx := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q`: the same circuit at true values {n: vb _ [false, false], d: vb _ [true, false], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 1#2, qbv: 0#2, rbv: 0#2} and at {lhs: 2#2} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastUdiv_denote_blastDivSubtractShift_q_16 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q 16 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q`: the same circuit at true values {n: vb _ [false, false], d: vb _ [false, false], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 0#2, qbv: 0#2, rbv: 0#2} and at {rhs: 1#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastUdiv_denote_blastDivSubtractShift_q_17 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q 17 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [false, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 0#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [false, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q`: the same circuit at true values {n: vb _ [false, false], d: vb _ [true, false], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 1#2, qbv: 0#2, rbv: 0#2} and at {qbv: 1#2} (dropped `hq`).
theorem n_BVExpr_bitblast_blastUdiv_denote_blastDivSubtractShift_q_18 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q 18 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 1) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 1#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hr := by dprem) (idx := 1) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q`: the same circuit at true values {n: vb _ [false, false], d: vb _ [true, false], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 1#2, qbv: 0#2, rbv: 0#2} and at {rbv: 1#2} (dropped `hr`).
theorem n_BVExpr_bitblast_blastUdiv_denote_blastDivSubtractShift_q_19 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q 19 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 1#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_r`: the same circuit at true values {n: vb _ [false, false], d: vb _ [false, true], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 2#2, qbv: 0#2, rbv: 0#2} and at {lhs: 2#2} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastUdiv_denote_blastDivSubtractShift_r_16 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_r 16 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_r (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 2#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 2#2) (qbv := 0#2) (rbv := 0#2) (hright := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_r`: the same circuit at true values {n: vb _ [false, true], d: vb _ [false, true], q: vb _ [false, false], r: vb _ [false, false], lhs: 2#2, rhs: 2#2, qbv: 0#2, rbv: 0#2} and at {rhs: 1#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastUdiv_denote_blastDivSubtractShift_r_17 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_r 17 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_r (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, true]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 2#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, true]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_r`: the same circuit at true values {n: vb _ [false, false], d: vb _ [true, true], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 3#2, qbv: 0#2, rbv: 0#2} and at {rbv: 1#2} (dropped `hr`).
theorem n_BVExpr_bitblast_blastUdiv_denote_blastDivSubtractShift_r_18 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_r 18 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_r (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 3#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hr := by dprem) (idx := 1) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 3#2) (qbv := 0#2) (rbv := 1#2) (hleft := by dprem) (hright := by dprem) (idx := 1) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q`: the same circuit at true values {n: vb _ [false, false], d: vb _ [true, false], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 1#2, qbv: 0#2, rbv: 0#2} and at {lhs: 2#2} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastUdiv_denote_go_eq_divRec_q_17 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q 17 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q`: the same circuit at true values {n: vb _ [false, false], d: vb _ [false, false], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 0#2, qbv: 0#2, rbv: 0#2} and at {rhs: 1#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastUdiv_denote_go_eq_divRec_q_18 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q 18 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [false, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 0#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [false, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q`: the same circuit at true values {n: vb _ [false, false], d: vb _ [true, false], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 1#2, qbv: 0#2, rbv: 0#2} and at {qbv: 1#2} (dropped `hq`).
theorem n_BVExpr_bitblast_blastUdiv_denote_go_eq_divRec_q_19 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q 19 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 1) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 1#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hr := by dprem) (idx := 1) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q`: the same circuit at true values {n: vb _ [false, false], d: vb _ [true, false], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 1#2, qbv: 0#2, rbv: 0#2} and at {rbv: 1#2} (dropped `hr`).
theorem n_BVExpr_bitblast_blastUdiv_denote_go_eq_divRec_q_20 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q 20 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 1#2) (qbv := 0#2) (rbv := 1#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r`: the same circuit at true values {n: vb _ [false, false], d: vb _ [false, true], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 2#2, qbv: 0#2, rbv: 0#2} and at {lhs: 2#2} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastUmod_denote_go_eq_divRec_r_17 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r 17 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 2#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 2#2) (qbv := 0#2) (rbv := 0#2) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r`: the same circuit at true values {n: vb _ [false, true], d: vb _ [false, true], q: vb _ [false, false], r: vb _ [false, false], lhs: 2#2, rhs: 2#2, qbv: 0#2, rbv: 0#2} and at {rhs: 1#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastUmod_denote_go_eq_divRec_r_18 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r 18 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, true]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 2#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, true]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 1#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r`: the same circuit at true values {n: vb _ [false, false], d: vb _ [true, true], q: vb _ [false, false], r: vb _ [false, false], lhs: 0#2, rhs: 3#2, qbv: 0#2, rbv: 0#2} and at {rbv: 1#2} (dropped `hr`).
theorem n_BVExpr_bitblast_blastUmod_denote_go_eq_divRec_r_20 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r 20 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 3#2) (qbv := 0#2) (rbv := 0#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 1) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 1) (wn := 2) (wr := 0) (n := vb _ [false, false]) (d := vb _ [true, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 3#2) (qbv := 0#2) (rbv := 1#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (idx := 1) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go`: the same circuit at true values {lhs: 1#1, rhs: 1#1} and at {lhs: 0#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastUdiv_denote_go_12 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go 12 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (n := vb _ [true]) (d := vb _ [true]) (q := vb _ [false]) (r := vb _ [false]) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (hzero := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (n := vb _ [true]) (d := vb _ [true]) (q := vb _ [false]) (r := vb _ [false]) (lhs := 0#1) (rhs := 1#1) (hright := by dprem) (hq := by dprem) (hr := by dprem) (hzero := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go`: the same circuit at true values {lhs: 1#2, rhs: 2#2} and at {lhs: 0#2} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastUmod_denote_go_12 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go 12 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (n := vb _ [true, false]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 1#2) (rhs := 2#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (hzero := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (n := vb _ [true, false]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 0#2) (rhs := 2#2) (hright := by dprem) (hq := by dprem) (hr := by dprem) (hzero := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go`: the same circuit at true values {lhs: 1#2, rhs: 2#2} and at {rhs: 1#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastUmod_denote_go_13 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go 13 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (n := vb _ [true, false]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 1#2) (rhs := 2#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (hzero := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (n := vb _ [true, false]) (d := vb _ [false, true]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 1#2) (rhs := 1#2) (hleft := by dprem) (hq := by dprem) (hr := by dprem) (hzero := by dprem) (idx := 0) (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go`: the same circuit at true values {lhs: 2#2, rhs: 1#2} and at {rhs: 2#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastUdiv_denote_go_13 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go 13 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (n := vb _ [false, true]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 1#2) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (hzero := by dprem) (idx := 1) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (n := vb _ [false, true]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [false, false]) (lhs := 2#2) (rhs := 2#2) (hleft := by dprem) (hq := by dprem) (hr := by dprem) (hzero := by dprem) (idx := 1) (hidx := by decide))) (by decide)


-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_denote_eq`: the same circuit at true values {rhs: 0#2} and at {rhs: 2#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastShiftLeft_go_denote_eq_14 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_denote_eq 14 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_denote_eq (n := 2) (w := 3) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (distance := vb _ [false, false]) (acc := vb _ [true, false, false]) (lhs := 1#3) (rhs := 0#2) (hacc := by dprem) (hright := by dprem) (idx := 2) (hidx := by decide)).symm.trans
    (H (n := 2) (w := 3) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (distance := vb _ [false, false]) (acc := vb _ [true, false, false]) (lhs := 1#3) (rhs := 2#2) (hacc := by dprem) (idx := 2) (hidx := by decide))) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_denote_eq`: the same circuit at true values {rhs: 0#2} and at {rhs: 2#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastShiftRight_go_denote_eq_14 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_denote_eq 14 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_denote_eq (n := 2) (w := 3) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (distance := vb _ [false, false]) (acc := vb _ [false, false, true]) (lhs := 4#3) (rhs := 0#2) (hacc := by dprem) (hright := by dprem) (idx := 0) (hidx := by decide)).symm.trans
    (H (n := 2) (w := 3) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (distance := vb _ [false, false]) (acc := vb _ [false, false, true]) (lhs := 4#3) (rhs := 2#2) (hacc := by dprem) (idx := 0) (hidx := by decide))) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_denote_eq`: the same circuit at true values {rhs: 0#2} and at {rhs: 2#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastArithShiftRight_go_denote_eq_14 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_denote_eq 14 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_denote_eq (n := 2) (w := 3) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (distance := vb _ [false, false]) (acc := vb _ [false, true, false]) (lhs := 2#3) (rhs := 0#2) (hacc := by dprem) (hright := by dprem) (idx := 1) (hidx := by decide)).symm.trans
    (H (n := 2) (w := 3) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (distance := vb _ [false, false]) (acc := vb _ [false, true, false]) (lhs := 2#3) (rhs := 2#2) (hacc := by dprem) (idx := 1) (hidx := by decide))) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry`: the same circuit at true values {lhsExpr: 0#1} and at {lhsExpr: 1#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_mkOverflowBit_go_eq_carry_14 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry 14 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ false) (origCin := cb _ false) (lhs := vb _ [false]) (rhs := vb _ [true]) (rhsExpr := 1#1) (lhsExpr := 0#1) (hleft := by dprem) (hright := by dprem) (hcin := by dprem) ).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ false) (origCin := cb _ false) (lhs := vb _ [false]) (rhs := vb _ [true]) (rhsExpr := 1#1) (lhsExpr := 1#1) (hright := by dprem) (hcin := by dprem) )) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry`: the same circuit at true values {rhsExpr: 0#1} and at {rhsExpr: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_mkOverflowBit_go_eq_carry_15 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry 15 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ false) (origCin := cb _ false) (lhs := vb _ [true]) (rhs := vb _ [false]) (lhsExpr := 1#1) (rhsExpr := 0#1) (hleft := by dprem) (hright := by dprem) (hcin := by dprem) ).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ false) (origCin := cb _ false) (lhs := vb _ [true]) (rhs := vb _ [false]) (lhsExpr := 1#1) (rhsExpr := 1#1) (hleft := by dprem) (hcin := by dprem) )) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry`: the same circuit at true values {origCin: cb _ true} and at {origCin: cb _ false} (dropped `hcin`).
theorem n_BVExpr_bitblast_mkOverflowBit_go_eq_carry_16 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry 16 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ true) (lhs := vb _ [true]) (rhs := vb _ [false]) (lhsExpr := 1#1) (rhsExpr := 0#1) (origCin := cb _ true) (hleft := by dprem) (hright := by dprem) (hcin := by dprem) ).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ true) (lhs := vb _ [true]) (rhs := vb _ [false]) (lhsExpr := 1#1) (rhsExpr := 0#1) (origCin := cb _ false) (hleft := by dprem) (hright := by dprem) )) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit_eq_carry`: the same circuit at true values {lhs: 0#1} and at {lhs: 1#1} (dropped `hleft`).
theorem n_BVExpr_bitblast_mkOverflowBit_eq_carry_8 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit_eq_carry 8 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit_eq_carry (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨1, ⟨vb _ [false], vb _ [true]⟩, cb _ false⟩) (rhs := 1#1) (lhs := 0#1) (hleft := by dprem) (hright := by dprem) ).symm.trans
    (H (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨1, ⟨vb _ [false], vb _ [true]⟩, cb _ false⟩) (rhs := 1#1) (lhs := 1#1) (hright := by dprem) )) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit_eq_carry`: the same circuit at true values {rhs: 0#1} and at {rhs: 1#1} (dropped `hright`).
theorem n_BVExpr_bitblast_mkOverflowBit_eq_carry_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit_eq_carry 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit_eq_carry (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨1, ⟨vb _ [true], vb _ [false]⟩, cb _ false⟩) (lhs := 1#1) (rhs := 0#1) (hleft := by dprem) (hright := by dprem) ).symm.trans
    (H (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (input := ⟨1, ⟨vb _ [true], vb _ [false]⟩, cb _ false⟩) (lhs := 1#1) (rhs := 1#1) (hleft := by dprem) )) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq`: the same circuit at true values {lhsExpr: 0#2} and at {lhsExpr: 1#2} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastAdd_go_denote_eq_14 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq 14 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ false) (s := vb _ []) (lhs := vb _ [false, false]) (rhs := vb _ [true, true]) (rhsExpr := 3#2) (lhsExpr := 0#2) (hleft := by dprem) (hright := by dprem) (hcin := by dprem) (idx := 1) (hidx1 := by decide) (by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ false) (s := vb _ []) (lhs := vb _ [false, false]) (rhs := vb _ [true, true]) (rhsExpr := 3#2) (lhsExpr := 1#2) (hright := by dprem) (hcin := by dprem) (idx := 1) (hidx1 := by decide) (by decide))) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq`: the same circuit at true values {rhsExpr: 0#2} and at {rhsExpr: 1#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastAdd_go_denote_eq_15 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq 15 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ false) (s := vb _ []) (lhs := vb _ [true, true]) (rhs := vb _ [false, false]) (lhsExpr := 3#2) (rhsExpr := 0#2) (hleft := by dprem) (hright := by dprem) (hcin := by dprem) (idx := 1) (hidx1 := by decide) (by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (cin := cb _ false) (s := vb _ []) (lhs := vb _ [true, true]) (rhs := vb _ [false, false]) (lhsExpr := 3#2) (rhsExpr := 1#2) (hleft := by dprem) (hcin := by dprem) (idx := 1) (hidx1 := by decide) (by decide))) (by dfin)

-- `Std.Tactic.BVDecide.BVPred.denote_getD_eq_getLsbD`: the same circuit at true values {x: 0#1} and at {x: 1#1} (dropped `hx`).
theorem n_BVPred_denote_getD_eq_getLsbD_9 : ¬ drop0% Std.Tactic.BVDecide.BVPred.denote_getD_eq_getLsbD 9 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVPred.denote_getD_eq_getLsbD (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (xv := vb _ [false]) (falseRef := cb _ false) (x := 0#1) (hx := by dprem) (hfalse := by dprem) (idx := 0)).symm.trans
    (H (w := 1) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (xv := vb _ [false]) (falseRef := cb _ false) (x := 1#1) (hfalse := by dprem) (idx := 0))) (by dfin)


-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq`: the same circuit at true values {lexpr: 0#2} and at {lexpr: 1#2} (dropped `hleft`).
theorem n_BVExpr_bitblast_blastMul_go_denote_eq_13 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq 13 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (acc := vb _ [false, false]) (lhs := vb _ [false, false]) (rhs := vb _ [false, true]) (rexpr := 2#2) (lexpr := 0#2) (hleft := by dprem) (hright := by dprem) (hacc := by dprem) (idx := 1) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (acc := vb _ [false, false]) (lhs := vb _ [false, false]) (rhs := vb _ [false, true]) (rexpr := 2#2) (lexpr := 1#2) (hright := by dprem) (hacc := by dprem) (idx := 1) (hidx := by decide))) (by dfin)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq`: the same circuit at true values {rexpr: 0#2} and at {rexpr: 2#2} (dropped `hright`).
theorem n_BVExpr_bitblast_blastMul_go_denote_eq_14 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq 14 := fun H =>
  absurd ((Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (acc := vb _ [false, false]) (lhs := vb _ [true, false]) (rhs := vb _ [false, false]) (lexpr := 1#2) (rexpr := 0#2) (hleft := by dprem) (hright := by dprem) (hacc := by dprem) (idx := 1) (hidx := by decide)).symm.trans
    (H (w := 2) (α := Nat) (aig := AIG.empty) (assign := fun _ => false) (curr := 0) (hcurr := by decide) (acc := vb _ [false, false]) (lhs := vb _ [true, false]) (rhs := vb _ [false, false]) (lexpr := 1#2) (rexpr := 2#2) (hleft := by dprem) (hacc := by dprem) (idx := 1) (hidx := by decide))) (by dfin)


/-! ### Loops started at their last position return the accumulator `s` -/

/-- Evaluates the hypothesis `this` over constant references to `False`. -/
macro "fin_s " h:ident : tactic => `(tactic| first
  | (simp at $h:ident; done)
  | (simp [BVDecideHand.den_cb, BVDecideHand.den0, BVDecideHand.vb_get, BVDecideHand.cb, AIG.RefVec.getD, AIG.mkConstCached] at $h:ident; done)
  | (simp [BVDecideHand.den_cb, BVDecideHand.den0, BVDecideHand.vb_get, BVDecideHand.cb, AIG.RefVec.getD, AIG.mkConstCached] at $h:ident;
      revert $h:ident; decide))

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_denote_eq`: `curr = w = 1` with `s = [true]` but `c = 0`.
theorem a_blastConst_go_denote_eq_12 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go_denote_eq 12 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty 0#1 (fun _ => false) 1 (by decide) (vb _ [true]) 0 (by decide)
  rw [BVExpr.bitblast.blastConst.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastExtract.go_get`: `curr = newWidth = 1` with `s = [true]`, input `[false]`.
theorem a_blastExtract_go_get_13 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastExtract.go_get 13 := by
  intro H
  have := H (α := Nat) (w := 1) (newWidth := 1) AIG.empty (vb _ [false]) 0 1 (by decide) (vb _ [true]) 0 (by decide)
  rw [BVExpr.bitblast.blastExtract.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.go_get`: `curr = n = 1` with `s = [true]`, input `[false]`.
theorem a_blastReplicate_go_get_12 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastReplicate.go_get 12 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty 1 1 (by decide) (vb _ [false]) (vb _ [true]) 0 (by decide)
  rw [BVExpr.bitblast.blastReplicate.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get`: `curr = w = 1` with `s = [true]`, input `[false]`.
theorem a_blastRotateLeft_go_get_12 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateLeft.go_get 12 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty 0 (vb _ [false]) 1 (by decide) (vb _ [true]) 0 (by decide)
  rw [BVExpr.bitblast.blastRotateLeft.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateRight.go_get`: `curr = w = 1` with `s = [true]`, input `[false]`.
theorem a_blastRotateRight_go_get_12 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastRotateRight.go_get 12 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty 0 (vb _ [false]) 1 (by decide) (vb _ [true]) 0 (by decide)
  rw [BVExpr.bitblast.blastRotateRight.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq`: `curr = w = 1`, `s = [true]`, input `[false]`.
theorem a_blastShiftLeftConst_go_denote_eq_13 :
    ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq 13 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty 0 (vb _ [false]) (fun _ => false) 1 (by decide) (vb _ [true]) 0 (by decide)
  rw [BVExpr.bitblast.blastShiftLeftConst.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq`: `curr = w = 1`, `s = [true]`, input `[false]`.
theorem a_blastShiftRightConst_go_denote_eq_13 :
    ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_denote_eq 13 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty 0 (vb _ [false]) (fun _ => false) 1 (by decide) (vb _ [true]) 0 (by decide)
  rw [BVExpr.bitblast.blastShiftRightConst.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq`: `curr = w = 1`, `s = [true]`, input `[false]`.
theorem a_blastArithShiftRightConst_go_denote_eq_13 :
    ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRightConst.go_denote_eq 13 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty 0 (vb _ [false]) (fun _ => false) 1 (by decide) (vb _ [true]) 0 (by decide)
  rw [BVExpr.bitblast.blastArithShiftRightConst.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq`: `curr = newWidth = 1`, `s = [true]`, input `[false]`.
theorem a_blastZeroExtend_go_denote_eq_13 :
    ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_denote_eq 13 := by
  intro H
  have := H (α := Nat) AIG.empty 1 (vb _ [false]) 1 1 (by decide) (vb _ [true]) (fun _ => false) 0 (by decide)
  rw [BVExpr.bitblast.blastZeroExtend.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq`: `curr = w = 1` with `s = [true]`, variable value `0`.
theorem a_blastVar_go_denote_eq_9 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_denote_eq 9 := by
  intro H
  have := H (w := 1) AIG.empty 0 (.leaf ⟨0#0⟩) 1 (by decide) (vb _ [true]) 0 (by decide)
  rw [BVExpr.bitblast.blastVar.go] at this
  simp [BVExpr.eval, BVExpr.Assignment.get, Lean.RArray.get] at this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq`: `curr = w = 1` with `s = [true]`, operands `0`.
theorem a_blastAdd_go_denote_eq_19 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq 19 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty 1 (by decide) (cb _ false) (vb _ [true]) (vb _ [false]) (vb _ [false])
    (fun _ => false) 0#1 0#1 (by dprem) (by dprem) (by dprem) 0 (by decide)
  rw [BVExpr.bitblast.blastAdd.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_denote_eq`: `curr = w = 1`, the accumulator is returned as is.
theorem a_blastClz_go_denote_eq_11 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastClz.go_denote_eq 11 := by
  intro H
  have := H (α := Nat) (curr := 1) (w := 1) AIG.empty (vb _ [!(((0#1).clzAuxRec 0).getLsbD 0)]) (vb _ [false]) 0#1
    (fun _ => false) (by dprem) 0 (by decide)
  rw [BVExpr.bitblast.blastClz.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq`: `w = 1`, `curr = 0`, the accumulator `[true]` is returned.
theorem a_blastMul_go_denote_eq_15 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq 15 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty 0 (by decide) (vb _ [true]) (vb _ [false]) (vb _ [false]) 0#1 0#1
    (fun _ => false) (by dprem) (by dprem) 0 (by decide)
  rw [BVExpr.bitblast.blastMul.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_denote_eq`: `n = 1`, `curr = 0`, the accumulator `[true]` is returned.
theorem a_blastShiftLeft_go_denote_eq_13 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_denote_eq 13 := by
  intro H
  have := H (α := Nat) (n := 1) (w := 1) AIG.empty (vb _ [false]) 0 (by decide) (vb _ [true]) 0#1 0#1
    (fun _ => false) (by dprem) 0 (by decide)
  rw [BVExpr.bitblast.blastShiftLeft.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_denote_eq`: `n = 1`, `curr = 0`, the accumulator `[true]` is returned.
theorem a_blastShiftRight_go_denote_eq_13 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_denote_eq 13 := by
  intro H
  have := H (α := Nat) (n := 1) (w := 1) AIG.empty (vb _ [false]) 0 (by decide) (vb _ [true]) 0#1 0#1
    (fun _ => false) (by dprem) 0 (by decide)
  rw [BVExpr.bitblast.blastShiftRight.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_denote_eq`: `n = 1`, `curr = 0`, the accumulator `[true]` is returned.
theorem a_blastArithShiftRight_go_denote_eq_13 :
    ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_denote_eq 13 := by
  intro H
  have := H (α := Nat) (n := 1) (w := 1) AIG.empty (vb _ [false]) 0 (by decide) (vb _ [true]) 0#1 0#1
    (fun _ => false) (by dprem) 0 (by decide)
  rw [BVExpr.bitblast.blastArithShiftRight.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry`: `curr = 1 > w = 0` returns `cin = false`, but the carry of `origCin = true` is `true`.
theorem a_mkOverflowBit_go_eq_carry_6 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.mkOverflowBit.go_eq_carry 6 := by
  intro H
  have := H (α := Nat) (w := 0) AIG.empty 1 (cb _ false) (cb _ true) (vb _ []) (vb _ []) 0#0 0#0 (fun _ => false)
    (by dprem) (by dprem) (by dprem)
  rw [BVExpr.bitblast.mkOverflowBit.go] at this
  fin_s this

-- `Std.Tactic.BVDecide.BVPred.denote_getD_eq_getLsbD`: out-of-range `getD` returns `falseRef = true`, but bit 5 of `0#1` is `false`.
theorem a_denote_getD_eq_getLsbD_10 : ¬ drop0% Std.Tactic.BVDecide.BVPred.denote_getD_eq_getLsbD 10 := by
  intro H
  have := H (α := Nat) (w := 1) AIG.empty (fun _ => false) 0#1 (vb _ [false]) (cb _ true) (by dprem) 5
  fin_s this


/-- The shift-right-by-constant loop only collects references. -/
theorem src_go_aig {w : Nat} (aig : AIG α) (input : aig.RefVec w) (distance curr : Nat) (hcurr : curr ≤ w)
    (s : aig.RefVec curr) :
    (BVExpr.bitblast.blastShiftRightConst.go aig input distance curr hcurr s).aig = aig := by
  unfold BVExpr.bitblast.blastShiftRightConst.go
  split
  · dsimp only; split <;> apply src_go_aig
  · simp
termination_by w - curr

/-- The zero-extension loop only collects references. -/
theorem ze_go_aig (aig : AIG α) (w : Nat) (input : aig.RefVec w) (newWidth curr : Nat) (hcurr : curr ≤ newWidth)
    (s : aig.RefVec curr) :
    (BVExpr.bitblast.blastZeroExtend.go aig w input newWidth curr hcurr s).aig = aig := by
  unfold BVExpr.bitblast.blastZeroExtend.go
  split
  · dsimp only; split <;> apply ze_go_aig
  · simp
termination_by newWidth - curr

/-- Extracting and zero-extending one bit only collects references. -/
theorem eaeb_aig {w : Nat} (aig : AIG α) (t : BVExpr.bitblast.ExtractAndExtendBitTarget aig w) :
    (BVExpr.bitblast.blastExtractAndExtendBit aig t).aig = aig := by
  simp only [BVExpr.bitblast.blastExtractAndExtendBit, BVExpr.bitblast.blastExtract,
    BVExpr.bitblast.blastZeroExtend]
  exact ze_go_aig ..

/-- The extract-and-extend loop only collects references. -/
theorem eae_go_aig {w outWidth : Nat} (aig : AIG α) (idx : Nat) (x : aig.RefVec w) (acc : aig.RefVec (w * idx))
    (h : idx ≤ w) (h' : outWidth = w * w) :
    (BVExpr.bitblast.blastExtractAndExtend.go idx x acc h h').aig = aig := by
  unfold BVExpr.bitblast.blastExtractAndExtend.go
  dsimp only
  split
  · rw [eae_go_aig]; exact eaeb_aig ..
  · simp
termination_by w - idx

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_decl_eq`: removable, `go` returns `aig` unchanged.
theorem t_src_11 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRightConst.go_decl_eq 11 := by
  intro α _ _ w aig distance input curr hcurr s idx h
  rwa [src_go_aig] at h

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_decl_eq`: removable, `go` returns `aig` unchanged.
theorem t_ze_11 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastZeroExtend.go_decl_eq 11 := by
  intro α _ _ aig w input newWidth curr hcurr s idx h
  rwa [ze_go_aig] at h

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastExtractAndExtend.go_decl_eq`: removable, `go` returns `aig` unchanged.
theorem t_eae_12 : indep% Std.Tactic.BVDecide.BVExpr.bitblast.blastExtractAndExtend.go_decl_eq 12 := by
  intro α _ _ w outWidth aig idx' x acc h h' idx hi
  rwa [eae_go_aig] at hi


/-! ### Caches with a wrong entry -/

/-- `BVExpr` cache with the wrong entry `1#1 ↦ [false]`. -/
def ebad : BVExpr.Cache (AIG.empty : AIG BVBit) := BVExpr.Cache.empty.insert (BVExpr.const 1#1) (vb _ [false])

theorem ebad_get : ebad.get? (BVExpr.const 1#1) = some (vb _ [false]) := by
  rw [BVExpr.Cache.get?_eq_some_iff]; simp [ebad, BVExpr.Cache.insert, BVExpr.Cache.empty, vb]

theorem ebad_not_inv (assign) : ¬ BVExpr.Cache.Inv assign AIG.empty ebad := fun h => by
  have := BVExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv _ _ _ ebad_get h 0 (by decide)
  simp [BVExpr.eval] at this

/-- The wrong cache with a second, correct entry `0#0 ↦ []`. -/
def ebad2 : BVExpr.Cache (AIG.empty : AIG BVBit) := ebad.insert (BVExpr.const 0#0) .empty

theorem ebad2_get : ebad2.get? (BVExpr.const 1#1) = some (vb _ [false]) := by
  rw [BVExpr.Cache.get?_eq_some_iff]
  simp [ebad2, ebad, BVExpr.Cache.insert, BVExpr.Cache.empty, vb, Std.DHashMap.get?_insert]

theorem ebad2_not_inv (assign) : ¬ BVExpr.Cache.Inv assign AIG.empty ebad2 := fun h => by
  have := BVExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv _ _ _ ebad2_get h 0 (by decide)
  simp [BVExpr.eval] at this

theorem ebad_goCache : BVExpr.bitblast.goCache AIG.empty (BVExpr.const 1#1) ebad =
    ⟨⟨⟨AIG.empty, vb _ [false]⟩, Nat.le_refl _⟩, ebad⟩ := by
  rw [BVExpr.bitblast.goCache]; simp only [ebad_get]

-- `Std.Tactic.BVDecide.BVExpr.Cache.Inv_cast`: the wrong cache, cast along the trivial prefix.
theorem i_Inv_cast_5 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.Cache.Inv_cast 5 := fun H =>
  ebad_not_inv asg0 (H (aig1 := AIG.empty) (aig2 := AIG.empty) ebad AIG.IsPrefix.rfl)

-- `Std.Tactic.BVDecide.BVExpr.Cache.Inv_insert`: inserting a correct entry into the wrong cache.
theorem i_Inv_insert_6 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.Cache.Inv_insert 6 := fun H =>
  ebad2_not_inv asg0 (H (assign := asg0) ebad (BVExpr.const 0#0) .empty (fun _ h => absurd h (Nat.not_lt_zero _)))

-- `Std.Tactic.BVDecide.BVExpr.Cache.Inv_insert`: inserting `1#1 ↦ [false]` into the empty cache.
theorem i_Inv_insert_7 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.Cache.Inv_insert 7 := fun H =>
  ebad_not_inv asg0 (H (assign := asg0) BVExpr.Cache.empty (BVExpr.const 1#1) (vb _ [false])
    (BVExpr.Cache.Inv_empty _))

-- `Std.Tactic.BVDecide.BVExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv`: empty cache, refs `[false]` for `1#1`.
theorem i_denote_eq_eval_6 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv 6 :=
  fun H => by
    have := H (aig := AIG.empty) (assign := asg0) BVExpr.Cache.empty (BVExpr.const 1#1) (vb _ [false])
      (BVExpr.Cache.Inv_empty _) 0 (by decide)
    simp [BVExpr.eval] at this

-- `Std.Tactic.BVDecide.BVExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv`: the wrong cache.
theorem i_denote_eq_eval_7 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv 7 :=
  fun H => by
    have := H (assign := asg0) ebad _ _ ebad_get 0 (by decide)
    simp [BVExpr.eval] at this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv`: the wrong cache hits and is returned.
theorem i_goCache_Inv_of_Inv_4 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv 4 := fun H => by
  have := H (assign := asg0) ebad (BVExpr.const 1#1)
  rw [ebad_goCache] at this
  exact ebad_not_inv _ this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.go_Inv_of_Inv`: a constant leaves the wrong cache as it is.
theorem i_go_Inv_of_Inv_4 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.go_Inv_of_Inv 4 := fun H => by
  have := H (assign := asg0) ebad (BVExpr.const 1#1)
  rw [BVExpr.bitblast.go] at this
  exact ebad_not_inv _ this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_denote_eq`: the wrong cache hits, `[false]` for `1#1`.
theorem i_goCache_denote_eq_5 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.goCache_denote_eq 5 := fun H => by
  have := H AIG.empty (BVExpr.const 1#1) asg0 ebad 0 (by decide)
  rw [ebad_goCache] at this
  simp [BVExpr.eval] at this

-- `Std.Tactic.BVDecide.BVExpr.bitblast.go_denote_eq`: `~~~(1#1)` uses the wrong cached `[false]` and gives `[true]`.
theorem i_go_denote_eq_5 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.go_denote_eq 5 := fun H => by
  have := H AIG.empty (BVExpr.un .not (BVExpr.const 1#1)) asg0 ebad 0 (by decide)
  rw [BVExpr.bitblast.go] at this
  simp only at this
  rw [ebad_goCache] at this
  simp only at this
  rw [BVExpr.bitblast.denote_blastNot] at this
  simp [BVExpr.eval] at this

-- `Std.Tactic.BVDecide.BVExpr.bitblast_Inv_of_Inv`: the wrong cache hits and is returned.
theorem i_bitblast_Inv_of_Inv_4 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast_Inv_of_Inv 4 := fun H => by
  have := H (assign := asg0) ⟨BVExpr.const 1#1, ebad⟩
  simp only [BVExpr.bitblast] at this
  rw [ebad_goCache] at this
  exact ebad_not_inv _ this

-- `Std.Tactic.BVDecide.BVExpr.denote_bitblast`: the wrong cache hits, `[false]` for `1#1`.
theorem i_denote_bitblast_4 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.denote_bitblast 4 := fun H => by
  have := H AIG.empty ⟨BVExpr.const 1#1, ebad⟩ asg0 0 (by decide)
  simp only [BVExpr.bitblast] at this
  rw [ebad_goCache] at this
  simp [BVExpr.eval] at this

-- `Std.Tactic.BVDecide.BVPred.bitblast_Inv_of_Inv`: bit 0 of `1#1` hits the wrong cache, which is returned.
theorem i_pbitblast_Inv_of_Inv_3 : ¬ drop0% Std.Tactic.BVDecide.BVPred.bitblast_Inv_of_Inv 3 := fun H => by
  have := H (assign := asg0) ⟨.getLsbD (BVExpr.const 1#1) 0, ebad⟩
  simp only [BVPred.bitblast, BVExpr.bitblast] at this
  rw [ebad_goCache] at this
  exact ebad_not_inv _ this

-- `Std.Tactic.BVDecide.BVPred.denote_bitblast`: bit 0 of `1#1` from the wrong cache is `false`.
theorem i_pdenote_bitblast_3 : ¬ drop0% Std.Tactic.BVDecide.BVPred.denote_bitblast 3 := fun H => by
  have := H AIG.empty ⟨.getLsbD (BVExpr.const 1#1) 0, ebad⟩ asg0
  simp only [BVPred.bitblast, BVExpr.bitblast] at this
  rw [ebad_goCache] at this
  simp [BVPred.eval, BVExpr.eval, BVPred.blastGetLsbD] at this

/-- `BVLogicalExpr` cache with the wrong entry `true ↦ false`. -/
def lbad : BVLogicalExpr.Cache (AIG.empty : AIG BVBit) := BVLogicalExpr.Cache.empty.insert (.const true) (cb _ false)

theorem lbad_get : lbad.get? (.const true) = some (cb _ false) := by
  rw [BVLogicalExpr.Cache.get?_eq_some_iff]; simp [lbad, BVLogicalExpr.Cache.insert, BVLogicalExpr.Cache.empty, cb]

theorem lbad_not_inv (assign) : ¬ BVLogicalExpr.Cache.Inv assign AIG.empty lbad := fun h => by
  have := BVLogicalExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv _ _ _ lbad_get h
  simp [BVLogicalExpr.eval] at this

/-- The wrong logical cache with a second, correct entry `false ↦ false`. -/
def lbad2 : BVLogicalExpr.Cache (AIG.empty : AIG BVBit) := lbad.insert (.const false) (cb _ false)

theorem lbad2_get : lbad2.get? (.const true) = some (cb _ false) := by
  rw [BVLogicalExpr.Cache.get?_eq_some_iff]
  simp [lbad2, lbad, BVLogicalExpr.Cache.insert, BVLogicalExpr.Cache.empty, cb]
  rw [Std.HashMap.getElem_insert]; simp

theorem lbad2_not_inv (assign) : ¬ BVLogicalExpr.Cache.Inv assign AIG.empty lbad2 := fun h => by
  have := BVLogicalExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv _ _ _ lbad2_get h
  simp [BVLogicalExpr.eval] at this

theorem lbad_goCache : BVLogicalExpr.bitblastWithCache.goCache AIG.empty (.const true) lbad =
    ⟨⟨⟨AIG.empty, cb _ false⟩, Nat.le_refl _⟩, lbad⟩ := by
  rw [BVLogicalExpr.bitblastWithCache.goCache]; simp only [lbad_get]

-- `Std.Tactic.BVDecide.BVLogicalExpr.Cache.Inv_cast`: the wrong cache, cast along the trivial prefix.
theorem i_lInv_cast_5 : ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.Cache.Inv_cast 5 := fun H =>
  lbad_not_inv asg0 (H (aig1 := AIG.empty) (aig2 := AIG.empty) lbad AIG.IsPrefix.rfl)

-- `Std.Tactic.BVDecide.BVLogicalExpr.Cache.Inv_insert`: inserting a correct entry into the wrong cache.
theorem i_lInv_insert_5 : ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.Cache.Inv_insert 5 := fun H =>
  lbad2_not_inv asg0 (H (assign := asg0) lbad (.const false) (cb _ false) (by simp [BVLogicalExpr.eval]))

-- `Std.Tactic.BVDecide.BVLogicalExpr.Cache.Inv_insert`: inserting `true ↦ false` into the empty cache.
theorem i_lInv_insert_6 : ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.Cache.Inv_insert 6 := fun H =>
  lbad_not_inv asg0 (H (assign := asg0) BVLogicalExpr.Cache.empty (.const true) (cb _ false)
    (BVLogicalExpr.Cache.Inv_empty _))

-- `Std.Tactic.BVDecide.BVLogicalExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv`: empty cache, `false` for `true`.
theorem i_ldenote_eq_eval_5 :
    ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv 5 := fun H => by
  have := H (aig := AIG.empty) (assign := asg0) BVLogicalExpr.Cache.empty (.const true) (cb _ false)
    (BVLogicalExpr.Cache.Inv_empty _)
  simp [BVLogicalExpr.eval] at this

-- `Std.Tactic.BVDecide.BVLogicalExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv`: the wrong cache.
theorem i_ldenote_eq_eval_6 :
    ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.Cache.denote_eq_eval_of_get?_eq_some_of_Inv 6 := fun H => by
  have := H (assign := asg0) lbad _ _ lbad_get
  simp [BVLogicalExpr.eval] at this

-- `Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_Inv_of_Inv`: the wrong cache hits and is returned.
theorem i_lgoCache_Inv_of_Inv_4 : ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_Inv_of_Inv 4 :=
  fun H => by
    have := H (.const true) AIG.empty asg0 lbad
    rw [lbad_goCache] at this
    exact lbad_not_inv _ this

-- `Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_Inv_of_Inv`: a constant leaves the wrong cache as it is.
theorem i_lgo_Inv_of_Inv_4 : ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_Inv_of_Inv 4 :=
  fun H => by
    have := H (.const true) AIG.empty asg0 lbad
    rw [BVLogicalExpr.bitblastWithCache.go] at this
    exact lbad_not_inv _ this

-- `Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_eval_eq_eval`: the wrong cache hits, `false` for `true`.
theorem i_lgoCache_eval_eq_eval_4 :
    ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_eval_eq_eval 4 := fun H => by
  have := H (.const true) AIG.empty asg0 lbad
  rw [lbad_goCache] at this
  simp [BVLogicalExpr.eval] at this

-- `Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_eval_eq_eval`: `not true` uses the wrong cached `false`.
theorem i_lgo_eval_eq_eval_4 : ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_eval_eq_eval 4 :=
  fun H => by
    have := H (.not (.const true)) AIG.empty asg0 lbad
    rw [BVLogicalExpr.bitblastWithCache.go] at this
    simp only at this
    rw [lbad_goCache] at this
    simp [BVLogicalExpr.eval, AIG.denote_mkNotCached] at this


/-! ### LRAT checker, reflection, logical expressions -/

open Std.Tactic.BVDecide.LRAT.Internal in
/-- The empty LRAT state. -/
def st0 : LRAT.Internal.State := ⟨#[]⟩

theorem st0_toCNF : st0.toCNF = CNF.empty := rfl

/-- Normalizes satisfiability statements over small CNFs, clauses and LRAT assignments. -/
macro "lsimp" : tactic => `(tactic| simp_all [CNF.unsat_iff_not_sat, CNF.Clause.unsat_iff_not_sat,
  CNF.Entails, CNF.EntailsClause, CNF.sat_append, CNF.sat_add, CNF.Clause.sat_unit_iff,
  LRAT.Internal.Assignment.sat_toCNF_iff, BVDecideHand.st0_toCNF, CNF.isNegationOf_def,
  LRAT.Internal.State.add_toCNF_eq_toCNF_add])

-- `Std.Tactic.BVDecide.LRAT.check_sound`: the empty CNF is satisfiable.
theorem l_check_sound_2 : ¬ drop0% Std.Tactic.BVDecide.LRAT.check_sound 2 := fun H => by
  exact CNF.not_unsat_empty (H #[] CNF.empty)

-- `Std.Tactic.BVDecide.LRAT.Internal.unsat_of_check`: the empty CNF is satisfiable.
theorem l_unsat_of_check_2 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.unsat_of_check 2 := fun H => by
  have := H (proof := #[]) (formula := CNF.empty); exact CNF.not_unsat_empty this

-- `Std.Tactic.BVDecide.Reflect.verifyCert_correct`: the empty CNF is satisfiable.
theorem l_verifyCert_correct_2 : ¬ drop0% Std.Tactic.BVDecide.Reflect.verifyCert_correct 2 := fun H => by
  exact CNF.not_unsat_empty (H CNF.empty "")

-- `Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true`: the constant `true` is satisfiable.
theorem l_unsat_of_verifyBVExpr_eq_true_2 : ¬ drop0% Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true 2 :=
  fun H => by have := H (.const true) "" asg0; simp [BVLogicalExpr.eval] at this

-- `Std.Tactic.BVDecide.BVLogicalExpr.unsat_of_bitblast`: the constant `true` is satisfiable.
theorem l_unsat_of_bitblast_1 : ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.unsat_of_bitblast 1 :=
  fun H => by have := H (.const true) asg0; simp [BVLogicalExpr.eval] at this

-- `Std.Tactic.BVDecide.BVLogicalExpr.sat_and`: `x = false`, `y = true`.
theorem l_sat_and_3 : ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.sat_and 3 := fun H => by
  have := H (x := .const false) (y := .const true) (assign := asg0) (by simp [BVLogicalExpr.Sat, BVLogicalExpr.eval])
  simp [BVLogicalExpr.Sat, BVLogicalExpr.eval, Gate.eval] at this

-- `Std.Tactic.BVDecide.BVLogicalExpr.sat_and`: `x = true`, `y = false`.
theorem l_sat_and_4 : ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.sat_and 4 := fun H => by
  have := H (x := .const true) (y := .const false) (assign := asg0) (by simp [BVLogicalExpr.Sat, BVLogicalExpr.eval])
  simp [BVLogicalExpr.Sat, BVLogicalExpr.eval, Gate.eval] at this

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.get?_insert_of_eq`: atom 1 stays unassigned after inserting atom 0.
theorem l_get?_insert_of_eq_4 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.get?_insert_of_eq 4 := fun H => by
  have := H (atom := 0) (atom' := 1) (b := true) (a := .empty)
  simp at this

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.get?_insert_of_ne`: inserting atom 0 changes atom 0.
theorem l_get?_insert_of_ne_4 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.get?_insert_of_ne 4 := fun H => by
  have := H (atom := 0) (atom' := 0) (b := true) (a := .empty)
  simp at this

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.not_sat_of_forall_falsified`: assignment `0 ↦ false`, clause `x0`, all-true valuation.
theorem l_not_sat_of_forall_falsified_3 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.not_sat_of_forall_falsified 3 := fun H => by
  have := H (assign := LRAT.Internal.Assignment.empty.insert 0 false) (c := CNF.Clause.unit 0 true)
    (a := fun _ => true) (by intro lit h; rw [CNF.Clause.mem_unit] at h; subst h; simp)
  exact this (CNF.Clause.sat_unit_iff.mpr rfl)

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.not_sat_of_forall_falsified`: empty assignment, clause `x0`, all true.
theorem l_not_sat_of_forall_falsified_4 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.not_sat_of_forall_falsified 4 := fun H => by
  have := H (assign := .empty) (c := CNF.Clause.unit 0 true) (a := fun _ => true) (by lsimp)
  exact this (CNF.Clause.sat_unit_iff.mpr rfl)

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.unit_propagation`: assignment `1 ↦ false`, clause `x1`, unit `x0`, valuation `x1` only.
theorem l_unit_propagation_4 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.unit_propagation 4 := fun H => by
  have := H (assign := LRAT.Internal.Assignment.empty.insert 1 false) (c := CNF.Clause.unit 1 true)
    (unit := (0, true)) (a := fun x => x == 1) (CNF.Clause.sat_unit_iff.mpr rfl)
    (by intro lit h; rw [CNF.Clause.mem_unit] at h; subst h; simp)
  simp at this

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.unit_propagation`: clause `x0` false under the all-false valuation.
theorem l_unit_propagation_5 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.unit_propagation 5 := fun H => by
  have := H (assign := .empty) (c := CNF.Clause.unit 0 true) (unit := (0, true)) (a := fun _ => false) (by lsimp)
    (by intro lit h; rw [CNF.Clause.mem_unit] at h; exact .inl h)
  simp at this

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.unit_propagation`: clause `x1`, unit `x0`, valuation `x1` only.
theorem l_unit_propagation_6 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.unit_propagation 6 := fun H => by
  have := H (assign := .empty) (c := CNF.Clause.unit 1 true) (unit := (0, true)) (a := fun x => x == 1) (by lsimp)
    (CNF.Clause.sat_unit_iff.mpr rfl)
  simp at this

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.exists_lit_of_ofClause_eq_none`: the empty clause has no literal.
theorem l_exists_lit_of_ofClause_eq_none_1 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.exists_lit_of_ofClause_eq_none 1 := fun H => by
  obtain ⟨atom, pol, h, _⟩ := H (clause := .empty)
  rw [← CNF.Clause.mem_literals_iff] at h; simp [CNF.Clause.literals, CNF.Clause.empty] at h

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.sat_of_ofClause_eq_none`: the empty clause is unsatisfiable.
theorem l_sat_of_ofClause_eq_none_1 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.sat_of_ofClause_eq_none 1 := fun H => by
  have := H (clause := .empty) (fun _ => false); simp at this

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.get_eq_of_ofClause_eq_some`: assignment `0 ↦ false`, empty clause.
theorem l_get_eq_of_ofClause_eq_some_2 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.get_eq_of_ofClause_eq_some 2 := fun H => by
  have := (H (clause := .empty) (assignment := LRAT.Internal.Assignment.empty.insert 0 false) (0, true)).mpr (by simp)
  rw [← CNF.Clause.mem_literals_iff] at this; simp [CNF.Clause.literals, CNF.Clause.empty] at this

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.isNegationOf_of_ofClause_eq_some`: empty assignment, clause `x0`, all true.
theorem l_isNegationOf_of_ofClause_eq_some_2 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.isNegationOf_of_ofClause_eq_some 2 := fun H => by
  have := (H (clause := CNF.Clause.unit 0 true) (assignment := .empty)) (fun _ => true)
  revert this; lsimp

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.entails_clause_of_unsat_of_ofClause_eq_some`: `f = [x0]`, assignment `0 ↦ false`, empty clause.
theorem l_entails_clause_of_unsat_3 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.entails_clause_of_unsat_of_ofClause_eq_some 3 :=
  fun H => by
    have := H (clause := .empty) (assignment := LRAT.Internal.Assignment.empty.insert 0 false)
      (f := CNF.empty.add (CNF.Clause.unit 0 true)) (by
        rw [CNF.unsat_iff_not_sat]; intro a h
        rw [CNF.sat_append, LRAT.Internal.Assignment.sat_toCNF_iff] at h
        have h1 := h.2 0 false (by simp)
        have h2 := h.1
        simp [CNF.sat_add, CNF.Clause.sat_unit_iff] at h2
        simp_all)
    have := this (fun _ => true) (by simp [CNF.sat_add, CNF.Clause.sat_unit_iff])
    simp at this

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.mem_or_get?_eq_iff_of_extendOfClauseWithout_eq_some`: `newAssign = 0 ↦ false`, rest empty.
theorem l_mem_or_get?_eq_iff_4 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.mem_or_get?_eq_iff_of_extendOfClauseWithout_eq_some 4 :=
  fun H => by
    have := (H (a := .empty) (clause := .empty) (lit := (0, true))
      (newAssign := LRAT.Internal.Assignment.empty.insert 0 false) (0, true)).mpr (by simp)
    rcases this with ⟨h, _⟩ | h
    · rw [← CNF.Clause.mem_literals_iff] at h; simp [CNF.Clause.literals, CNF.Clause.empty] at h
    · simp at h

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.entails_clause_of_extendOfClauseWithout_eq_none`: empty assignment and clause.
theorem l_entails_clause_of_extend_3 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.entails_clause_of_extendOfClauseWithout_eq_none 3 :=
  fun H => by
    have := H (a := .empty) (clause := .empty) (lit := (0, true)) (fun _ => false) (by lsimp)
    obtain ⟨l, hl, _⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp this
    rw [CNF.Clause.mem_erase_iff] at hl
    have := hl.2; rw [← CNF.Clause.mem_literals_iff] at this
    simp [CNF.Clause.literals, CNF.Clause.empty] at this

-- `Std.Tactic.BVDecide.LRAT.Internal.State.mem_toCNF_of_eq_some`: the empty state has no clause.
theorem l_mem_toCNF_of_eq_some_3 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.mem_toCNF_of_eq_some 3 := fun H => by
  have := H (idx := 0) (c := .empty) (s := st0)
  rw [LRAT.Internal.State.toCNF, CNF.Internal.mem_iff] at this; simp [st0] at this

-- `Std.Tactic.BVDecide.LRAT.Internal.State.exists_getElem_eq_some_of_mem`: the empty state has no clause.
theorem l_exists_getElem_eq_some_of_mem_2 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.exists_getElem_eq_some_of_mem 2 := fun H => by
  obtain ⟨i, hi, _⟩ := H (c := .empty) (s := st0)
  simp [st0] at hi

-- `Std.Tactic.BVDecide.LRAT.Internal.State.exists_get?_eq_some_of_mem`: the empty state has no clause.
theorem l_exists_get?_eq_some_of_mem_2 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.exists_get?_eq_some_of_mem 2 := fun H => by
  obtain ⟨i, h⟩ := H (c := .empty) (s := st0)
  simp [st0, LRAT.Internal.State.get?] at h

-- `Std.Tactic.BVDecide.LRAT.Internal.State.forall_of_all_eq_true`: state with the empty clause, `p = false`.
theorem l_forall_of_all_eq_true_2 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.forall_of_all_eq_true 2 :=
  fun H => by
    obtain ⟨i, _, h⟩ := H (s := ⟨#[some .empty]⟩) (p := fun _ _ => false) .empty (by
      rw [LRAT.Internal.State.toCNF, CNF.Internal.mem_iff]; simp)
    simp at h

-- `Std.Tactic.BVDecide.LRAT.Internal.State.forall_of_all_eq_true`: the empty state, `all` holds vacuously.
theorem l_forall_of_all_eq_true_4 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.forall_of_all_eq_true 4 :=
  fun H => by
    obtain ⟨i, h, _⟩ := H (s := st0) (p := fun _ _ => false)
      (by rw [LRAT.Internal.State.all_eq_true_iff]; simp [st0]) .empty
    simp [st0, LRAT.Internal.State.get?] at h

-- `Std.Tactic.BVDecide.LRAT.Internal.State.entails_clause_empty_of_checkEmpty`: the empty state does not entail the empty clause.
theorem l_entails_clause_empty_of_checkEmpty_2 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.entails_clause_empty_of_checkEmpty 2 := fun H => by
  have := H (s := st0) (rupHints := #[]); revert this; lsimp

-- `Std.Tactic.BVDecide.LRAT.Internal.State.unsat_of_unsat_of_checkRat`: adding the empty clause to the empty state.
theorem l_unsat_of_unsat_of_checkRat_6 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.unsat_of_unsat_of_checkRat 6 := fun H => by
  obtain ⟨a', h⟩ := H (a := fun _ => false) (s := st0) (clause := .empty) (pivot := (0, true)) (rupHints := #[])
    (ratHints := #[]) (by lsimp)
  revert h; lsimp

-- `Std.Tactic.BVDecide.LRAT.Internal.State.entails_add_of_entails_clause`: adding the empty clause to the empty state.
theorem l_entails_add_of_entails_clause_2 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.entails_add_of_entails_clause 2 := fun H => by
  have := H (s := st0) (c := .empty) (fun _ => false) (by lsimp); revert this; lsimp

-- `Std.Tactic.BVDecide.LRAT.Internal.State.unsat_of_propagateHints_eq_conflict`: empty state and assignment.
theorem l_unsat_of_propagateHints_eq_conflict_3 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.unsat_of_propagateHints_eq_conflict 3 := fun H => by
  have := H (s := st0) (assign := .empty) (hints := #[]); revert this; lsimp

-- `Std.Tactic.BVDecide.LRAT.Internal.State.entails_of_propagateHints_eq_extended`: `newAssign = 0 ↦ true`, valuation all false.
theorem l_entails_of_propagateHints_eq_extended_4 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.entails_of_propagateHints_eq_extended 4 := fun H => by
  have := H (s := st0) (assign := .empty) (hints := #[]) (newAssign := LRAT.Internal.Assignment.empty.insert 0 true)
    (fun _ => false) (by lsimp)
  revert this; rw [LRAT.Internal.Assignment.sat_toCNF_iff]; intro h; simpa using h 0 true (by simp)

-- `Std.Tactic.BVDecide.LRAT.Internal.State.unsat_of_checkPropagate`: empty state and assignment.
theorem l_unsat_of_checkPropagate_3 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.unsat_of_checkPropagate 3 :=
  fun H => by
    have := H (s := st0) (assign := .empty) (rupHints := #[]); revert this; lsimp

-- `Std.Tactic.BVDecide.LRAT.Internal.State.entails_clause_of_checkRup`: the empty state does not entail the empty clause.
theorem l_entails_clause_of_checkRup_3 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.entails_clause_of_checkRup 3 :=
  fun H => by
    have := H (s := st0) (clause := .empty) (rupHints := #[]); revert this; lsimp


/-! ### Removable bounds -/

-- `Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt`: removable, for `k ≥ w` both sides are `0`.
theorem r_udiv_ofNat_eq_of_lt_5 : drop% Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt 5 := by
  intro w x n k hk
  by_cases hlt : k < w
  · exact Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt w x n k hk hlt
  · subst hk
    apply BitVec.eq_of_toNat_eq
    have h1 : 2 ^ w ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    have h2 : x.toNat < 2 ^ k := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    simp [BitVec.toNat_udiv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_zero_of_dvd h1,
      Nat.div_eq_of_lt h2]

/-- Partial products past the width add nothing. -/
theorem mulRec_ge {w : Nat} (x y : BitVec w) (m : Nat) (hm : w ≤ m) : x.mulRec y m = x.mulRec y w := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih => rw [Nat.add_succ, BitVec.mulRec_succ_eq, ih (by omega), BitVec.getLsbD_of_ge y _ (by omega)]; simp

/-- A power of two past the width is zero. -/
theorem and_twoPow_ge {n : Nat} (y : BitVec n) (i : Nat) (h : n ≤ i) : (y &&& BitVec.twoPow n i) = 0#n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [BitVec.getLsbD_twoPow]; omega

theorem slr_ge {w₁ w₂ : Nat} (x : BitVec w₁) (y : BitVec w₂) (m : Nat) (hm : w₂ - 1 ≤ m) :
    x.shiftLeftRec y m = x.shiftLeftRec y (w₂ - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih => rw [Nat.add_succ, BitVec.shiftLeftRec_succ, ih (by omega), and_twoPow_ge y _ (by omega)]; simp

theorem usrr_ge {w₁ w₂ : Nat} (x : BitVec w₁) (y : BitVec w₂) (m : Nat) (hm : w₂ - 1 ≤ m) :
    x.ushiftRightRec y m = x.ushiftRightRec y (w₂ - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih => rw [Nat.add_succ, BitVec.ushiftRightRec_succ, ih (by omega), and_twoPow_ge y _ (by omega)]; simp

theorem ssrr_ge {w₁ w₂ : Nat} (x : BitVec w₁) (y : BitVec w₂) (m : Nat) (hm : w₂ - 1 ≤ m) :
    x.sshiftRightRec y m = x.sshiftRightRec y (w₂ - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih => rw [Nat.add_succ, BitVec.sshiftRightRec_succ_eq, ih (by omega), and_twoPow_ge y _ (by omega)]; simp

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq`: removable, for `curr ≥ w` the loop returns `acc` and `mulRec` is constant past `w`.
theorem r_blastMul_go_denote_eq_6 : drop% Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq 6 := by
  intro α _ _ w aig curr acc lhs rhs lexpr rexpr assign hleft hright hacc idx hidx
  by_cases hc : curr + 1 ≤ w
  · exact BVExpr.bitblast.blastMul.go_denote_eq aig curr hc acc lhs rhs lexpr rexpr assign hleft hright hacc idx hidx
  · rw [BVExpr.bitblast.blastMul.go, dif_neg (by omega)]
    dsimp only
    rw [hacc idx hidx, mulRec_ge _ _ curr (by omega)]

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_denote_eq`: removable, for `curr ≥ n - 1` the loop returns `acc` and `shiftLeftRec` is constant past `n - 1`.
theorem r_blastShiftLeft_go_denote_eq_8 : drop% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeft.go_denote_eq 8 := by
  intro α _ _ n w aig distance curr acc lhs rhs assign hacc hright idx hidx
  by_cases hc : curr ≤ n - 1
  · exact BVExpr.bitblast.blastShiftLeft.go_denote_eq aig distance curr hc acc lhs rhs assign hacc hright idx hidx
  · rw [BVExpr.bitblast.blastShiftLeft.go, if_neg (by omega)]
    dsimp only
    rw [hacc idx hidx, slr_ge lhs rhs curr (by omega)]

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_denote_eq`: removable, for `curr ≥ n - 1` the loop returns `acc` and `ushiftRightRec` is constant past `n - 1`.
theorem r_blastShiftRight_go_denote_eq_8 : drop% Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftRight.go_denote_eq 8 := by
  intro α _ _ n w aig distance curr acc lhs rhs assign hacc hright idx hidx
  by_cases hc : curr ≤ n - 1
  · exact BVExpr.bitblast.blastShiftRight.go_denote_eq aig distance curr hc acc lhs rhs assign hacc hright idx hidx
  · rw [BVExpr.bitblast.blastShiftRight.go, if_neg (by omega)]
    dsimp only
    rw [hacc idx hidx, usrr_ge lhs rhs curr (by omega)]

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_denote_eq`: removable, for `curr ≥ n - 1` the loop returns `acc` and `sshiftRightRec` is constant past `n - 1`.
theorem r_blastArithShiftRight_go_denote_eq_8 :
    drop% Std.Tactic.BVDecide.BVExpr.bitblast.blastArithShiftRight.go_denote_eq 8 := by
  intro α _ _ n w aig distance curr acc lhs rhs assign hacc hright idx hidx
  by_cases hc : curr ≤ n - 1
  · exact BVExpr.bitblast.blastArithShiftRight.go_denote_eq aig distance curr hc acc lhs rhs assign hacc hright idx hidx
  · rw [BVExpr.bitblast.blastArithShiftRight.go, if_neg (by omega)]
    dsimp only
    rw [hacc idx hidx, ssrr_ge lhs rhs curr (by omega)]


/-! ### Growth of recursive builders on `G` -/

/-- An atom missing from the cache adds a node. -/
theorem atom_grow (aig : AIG α) (a : α) (hmiss : ∀ d : AIG.Decl α, aig.cache.val[d]? = none) :
    aig.decls.size < (aig.mkAtomCached a).aig.decls.size := by
  obtain ⟨decls, cache, hdag, hzero, hconst⟩ := aig
  have hm : ∀ d, cache.get? d = none := fun d => AIG.Cache.get?_eq_none_iff.mpr (hmiss d)
  unfold AIG.mkAtomCached
  dsimp only
  split
  · rename_i h; simp [hm] at h
  · simp

theorem ec_empty_get {aig : AIG BVBit} {w : Nat} (e : BVExpr w) :
    (BVExpr.Cache.empty : BVExpr.Cache aig).get? e = none := by
  unfold BVExpr.Cache.get?
  split
  · rename_i h; exfalso; revert h
    first | (simp [BVExpr.Cache.empty]; done) | (show (∅ : Std.DHashMap _ _).get? _ = _ → _; simp)
  · rfl

theorem lc_empty_get {aig : AIG BVBit} (e : BVLogicalExpr) :
    (BVLogicalExpr.Cache.empty : BVLogicalExpr.Cache aig).get? e = none := by
  unfold BVLogicalExpr.Cache.get?
  split
  · rename_i h; exfalso; revert h
    first | (simp [BVLogicalExpr.Cache.empty]; done) | (show (∅ : Std.HashMap _ _)[_]? = _ → _; simp)
  · rfl

/-- One variable bit on `G` adds an atom. -/
theorem var_grow : (G BVBit).decls.size < (BVExpr.bitblast.blastVar.go (G BVBit) 1 0 0 .empty (by decide)).aig.decls.size := by
  unfold BVExpr.bitblast.blastVar.go
  rw [dif_pos (by decide)]
  dsimp only
  refine Nat.lt_of_lt_of_le ?_ (by apply BVExpr.bitblast.blastVar.go_le_size)
  exact atom_grow _ _ G_miss

theorem go_var_grow : (G BVBit).decls.size <
    (BVExpr.bitblast.go (G BVBit) (BVExpr.var (w := 1) 0) BVExpr.Cache.empty).result.val.aig.decls.size := by
  rw [BVExpr.bitblast.go]
  exact var_grow

theorem goCache_var_grow : (G BVBit).decls.size <
    (BVExpr.bitblast.goCache (G BVBit) (BVExpr.var (w := 1) 0) BVExpr.Cache.empty).result.val.aig.decls.size := by
  rw [BVExpr.bitblast.goCache]
  simp only [ec_empty_get]
  exact go_var_grow

theorem pred_var_grow : (G BVBit).decls.size <
    (BVPred.bitblast (G BVBit) ⟨.getLsbD (BVExpr.var (w := 1) 0) 0, BVExpr.Cache.empty⟩).result.val.aig.decls.size := by
  simp only [BVPred.bitblast, BVExpr.bitblast]
  exact goCache_var_grow

theorem lgo_var_grow : (G BVBit).decls.size <
    (BVLogicalExpr.bitblastWithCache.go (G BVBit) (.literal (.getLsbD (BVExpr.var (w := 1) 0) 0))
      BVLogicalExpr.Cache.empty).result.val.aig.decls.size := by
  rw [BVLogicalExpr.bitblastWithCache.go]
  exact pred_var_grow

theorem lgoCache_var_grow : (G BVBit).decls.size <
    (BVLogicalExpr.bitblastWithCache.goCache (G BVBit) (.literal (.getLsbD (BVExpr.var (w := 1) 0) 0))
      BVLogicalExpr.Cache.empty).result.val.aig.decls.size := by
  rw [BVLogicalExpr.bitblastWithCache.goCache]
  simp only [lc_empty_get]
  exact lgo_var_grow

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_decl_eq`: one variable bit on the three-node AIG adds an atom.
theorem g_blastVar_go_decl_eq_7 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go_decl_eq 7 := fun H =>
  Nat.lt_irrefl 3 (H (w := 1) (aig := G BVBit) 0 .empty 0 (by decide) 3 var_grow)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq`: a one-bit variable on the three-node AIG adds an atom.
theorem g_go_decl_eq_5 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq 5 := fun H =>
  Nat.lt_irrefl 3 (H (G BVBit) (BVExpr.var (w := 1) 0) BVExpr.Cache.empty 3 go_var_grow)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq`: a one-bit variable (empty cache) adds an atom.
theorem g_goCache_decl_eq_5 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq 5 := fun H =>
  Nat.lt_irrefl 3 (H (G BVBit) (BVExpr.var (w := 1) 0) BVExpr.Cache.empty 3 goCache_var_grow)

-- `Std.Tactic.BVDecide.BVExpr.bitblast_decl_eq`: a one-bit variable (empty cache) adds an atom.
theorem g_bitblast_decl_eq_4 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast_decl_eq 4 := fun H =>
  Nat.lt_irrefl 3 (H (G BVBit) ⟨BVExpr.var (w := 1) 0, BVExpr.Cache.empty⟩ 3 goCache_var_grow)

-- `Std.Tactic.BVDecide.BVPred.bitblast_decl_eq`: bit 0 of a one-bit variable adds an atom.
theorem g_pbitblast_decl_eq_3 : ¬ indep0% Std.Tactic.BVDecide.BVPred.bitblast_decl_eq 3 := fun H =>
  Nat.lt_irrefl 3 (H (G BVBit) ⟨.getLsbD (BVExpr.var (w := 1) 0) 0, BVExpr.Cache.empty⟩ 3 pred_var_grow)

-- `Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_decl_eq`: a literal on a one-bit variable adds an atom.
theorem g_lgo_decl_eq_4 : ¬ indep0% Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.go_decl_eq 4 := fun H =>
  Nat.lt_irrefl 3 (H (G BVBit) (.literal (.getLsbD (BVExpr.var (w := 1) 0) 0)) BVLogicalExpr.Cache.empty 3
    lgo_var_grow)

-- `Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_decl_eq`: a literal on a one-bit variable adds an atom.
theorem g_lgoCache_decl_eq_4 : ¬ indep0% Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_decl_eq 4 :=
  fun H => Nat.lt_irrefl 3 (H (G BVBit) (.literal (.getLsbD (BVExpr.var (w := 1) 0) 0)) BVLogicalExpr.Cache.empty 3
    lgoCache_var_grow)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_decl_eq`: one full adder on the gates of `G` adds a node.
theorem g_blastAdd_go_decl_eq_12 : ¬ indep0% Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_decl_eq 12 := by
  intro H
  have := H (α := Nat) (w := 1) (G Nat) 0 (by decide) g1 .empty (AIG.RefVec.empty.push g1)
    (AIG.RefVec.empty.push g2) 3 (by
      show (G Nat).decls.size < _
      unfold BVExpr.bitblast.blastAdd.go
      rw [dif_pos (by decide)]
      dsimp only
      refine Nat.lt_of_lt_of_le ?_ (by apply BVExpr.bitblast.blastAdd.go_le_size)
      unfold BVExpr.bitblast.mkFullAdder
      dsimp only
      refine Nat.lt_of_lt_of_le ?_ (AIG.LawfulOperator.le_size (f := BVExpr.bitblast.mkFullAdderCarry) ..)
      unfold BVExpr.bitblast.mkFullAdderOut
      dsimp only
      refine Nat.lt_of_lt_of_le ?_ (AIG.LawfulOperator.le_size (f := AIG.mkXorCached) ..)
      unfold AIG.mkXorCached
      dsimp only
      refine Nat.lt_of_lt_of_le ?_ (AIG.LawfulOperator.le_size (f := AIG.mkGateCached) ..)
      refine Nat.lt_of_lt_of_le ?_ (AIG.LawfulOperator.le_size (f := AIG.mkGateCached) ..)
      exact G_grow)
  exact absurd this (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast_lt_size_of_lt_aig_size`: a constant leaves the one-node AIG unchanged, `x = 1`.
theorem g_bitblast_lt_size_4 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast_lt_size_of_lt_aig_size 4 := by
  intro H
  have := H (w := 0) (x := 1) AIG.empty ⟨BVExpr.const 0#0, BVExpr.Cache.empty⟩
  simp only [BVExpr.bitblast] at this
  rw [BVExpr.bitblast.goCache] at this
  simp only [ec_empty_get] at this
  rw [BVExpr.bitblast.go] at this
  exact absurd this (by decide)

-- `Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_lt_size_of_lt_aig_size`: a constant leaves the one-node AIG unchanged, `x = 1`.
theorem g_lgoCache_lt_size_4 :
    ¬ drop0% Std.Tactic.BVDecide.BVLogicalExpr.bitblastWithCache.goCache_lt_size_of_lt_aig_size 4 := by
  intro H
  have := H (x := 1) AIG.empty (.const true) BVLogicalExpr.Cache.empty
  rw [BVLogicalExpr.bitblastWithCache.goCache] at this
  simp only [lc_empty_get] at this
  rw [BVLogicalExpr.bitblastWithCache.go] at this
  exact absurd this (by decide)


/-! ### Division from nonzero remainders and by zero (compared through the `divRec` lemmas) -/

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go`: start remainder `1`, `0 / 1` but the circuit gives `divRec` with `r = 1`.
theorem d_udiv_denote_go_15 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go 15 := fun H =>
  absurd ((BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q (α := Nat) (w := 2) (aig := AIG.empty)
      (assign := fun _ => false) (curr := 2) (lhs := 0#2) (rhs := 1#2) (rbv := 1#2) (qbv := 0#2)
      (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [true, false])
      (wn := 2) (wr := 0) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem)
      (idx := 0) (hidx := by decide)).symm.trans
    (H (α := Nat) (w := 2) (aig := AIG.empty) (assign := fun _ => false) (lhs := 0#2) (rhs := 1#2)
      (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [true, false])
      (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hzero := by decide) (idx := 0)
      (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go`: divisor `0`, the circuit gives quotient bits `1` but `0 / 0 = 0`.
theorem d_udiv_denote_go_16 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go 16 := fun H =>
  absurd ((BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q (α := Nat) (w := 1) (aig := AIG.empty)
      (assign := fun _ => false) (curr := 1) (lhs := 0#1) (rhs := 0#1) (rbv := 0#1) (qbv := 0#1)
      (n := vb _ [false]) (d := vb _ [false]) (q := vb _ [false]) (r := vb _ [false])
      (wn := 1) (wr := 0) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem)
      (idx := 0) (hidx := by decide)).symm.trans
    (H (α := Nat) (w := 1) (aig := AIG.empty) (assign := fun _ => false) (lhs := 0#1) (rhs := 0#1)
      (n := vb _ [false]) (d := vb _ [false]) (q := vb _ [false]) (r := vb _ [false])
      (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem) (idx := 0)
      (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go`: start remainder `1`, `0 % 1 = 0` but the circuit gives remainder `1`.
theorem d_umod_denote_go_15 : ¬ drop0% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go 15 := fun H =>
  absurd ((BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r (α := Nat) (w := 2) (aig := AIG.empty)
      (assign := fun _ => false) (curr := 2) (lhs := 0#2) (rhs := 1#2) (rbv := 1#2) (qbv := 0#2)
      (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [true, false])
      (wn := 2) (wr := 0) (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hr := by dprem)
      (idx := 0) (hidx := by decide)).symm.trans
    (H (α := Nat) (w := 2) (aig := AIG.empty) (assign := fun _ => false) (lhs := 0#2) (rhs := 1#2)
      (n := vb _ [false, false]) (d := vb _ [true, false]) (q := vb _ [false, false]) (r := vb _ [true, false])
      (hleft := by dprem) (hright := by dprem) (hq := by dprem) (hzero := by decide) (idx := 0)
      (hidx := by decide))) (by decide)

-- `Std.Tactic.BVDecide.LRAT.Internal.Assignment.entails_clause_of_unsat_of_ofClause_eq_some`: clause `x0` has an assignment, `f` empty.
theorem l_entails_clause_of_unsat_4 :
    ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.Assignment.entails_clause_of_unsat_of_ofClause_eq_some 4 :=
  fun H => by
    obtain ⟨asg, h⟩ : ∃ asg, LRAT.Internal.Assignment.ofClause (CNF.Clause.unit 0 true) = some asg := by
      cases hc : LRAT.Internal.Assignment.ofClause (CNF.Clause.unit 0 true) with
      | some a => exact ⟨a, rfl⟩
      | none =>
        obtain ⟨atom, pol, h1, h2⟩ := LRAT.Internal.Assignment.exists_lit_of_ofClause_eq_none hc
        rw [CNF.Clause.mem_unit] at h1 h2
        simp at h1 h2; cases h1.2; simp at h2
    have := H (f := CNF.empty) h (fun _ => false) CNF.sat_empty
    simp [CNF.Clause.sat_unit_iff] at this


end BVDecideHand
