import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init
import Std.Sat.AIG.CNF
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop
import Std.Tactic.BVDecide.LRAT.Internal.Rat


/-!
Hand pass `SatBV` (hand22, 2026-11-08): the 98 unresolved hypotheses of private theorems of
Std.Sat.AIG.CNF (Tseitin transformation), Std.Sat.CNF.Basic (Clause.erase), the Cpop bitblaster
lemmas (Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop) and the LRAT RAT check.
90 necessary, 8 removable.

Reusable models (namespace SatBVHand, all over Nat atoms; private constants reached with priv%):
* AIGs without atoms (empty cache): A2 = #[false, false] (A2_false, A2_den) and
  B = #[false, gate(0,¬0), gate(¬1,¬1), gate(1,¬1), gate(¬1,1), gate(¬2,¬2)] with values
  false, false, true, false, false, false (B_den0..B_den4); node 1 has complementary fanins, so
  detectIte.go recognises an ite at nodes 2..4, not at node 5. den0: a reference to node 0 of any
  AIG denotes its invert bit.
* CNF caches/states of A2 with arbitrary marks: FF = unit clauses ¬x0, ¬x1 (FF_eval, FF_inv),
  cc m (toCNF.Cache A2 FF), st m (toCNF.State A2); Fbad = one empty clause. notInv: a CNF that is
  false at cnfSatAssignment violates State.Inv; csa = satAssignment_lt.
* IsExtensionBy facts on these caches are decided by decide (marks are literal arrays).
* Bitblaster: vk aig n inv (n references to node 0, den_vk), eae1 (bit k of extractAndExtend 1 x),
  cpopTree_one, cpl (bit 0 of cpopLayer for len = w = 1), cpopGo_done / eaeGo_done (the go loops
  at their last index return the accumulator). Most refutations use the two-instantiation trick:
  the same circuit at x = 0#1 and x = 1#1 must denote two different bits.
* literals_erase_go_any (copied from checks/SatCNFHand.lean): Clause.erase.go evaluates for every BEq.
* sN: LRAT state with the single clause ¬x0.

Removable: the auto-bound bounds named omega of Cache/State.IsExtensionBy_rfl (the statement
writes the term have := ...; omega, which binds a variable called omega) and their h bounds
(each follows from the other and hmarks); hl/hr of detectIte.denote_go (DAG property of heqroot);
the premise of toCNF'.go_as_denote' (the go CNF is always sat at cnfSatAssignment, sibling go_sat);
LawfulBEq of Clause.literals_erase_go (same comparison on both sides).

Run with the lean4 repo's stage1 binary: runs/hand22/lean.sh checks/SatBVHand.lean.
-/

set_option linter.unusedVariables false

open Lean Meta Elab Term

/-- `_private.M.«0».x` ↦ `_private.M.0.x`: all-digit string components become numeric. -/
def hcFixName : Name → Name
  | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (hcFixName p) s.toNat! else .str (hcFixName p) s
  | .num p k => .num (hcFixName p) k
  | .anonymous => .anonymous

/-- The constant named by `T`: a public name (resolved as usual) or a private one written in full
as `_private.Mod.«0».x` (private names are not reachable by their short name from another module). -/
def hcConst (T : Ident) : TermElabM Name := do
  let n := hcFixName T.getId
  if isPrivateName n then
    unless (← getEnv).contains n do throwError "unknown private constant {n}"
    return n
  realizeGlobalConstNoOverloadWithInfo T

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
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

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
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

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

open Std Std.Sat Std.Sat.AIG

namespace SatBVHand

/-- #[false, false]. -/
def A2 : AIG Nat where
  decls := #[.false, .false]
  cache := ⟨{}, Cache.WF.empty (by intro i h a; match i, h with | 0, _ => nofun | 1, _ => nofun)⟩
  hdag := by
    intro i l r h hg
    match i, h with
    | 0, _ => cases hg
    | 1, _ => cases hg
  hzero := by simp
  hconst := rfl

theorem A2_false : ∀ (i : Nat) (h : i < A2.decls.size), A2.decls[i] = .false := by
  intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl

theorem A2_den (i inv h assign) : ⟦A2, ⟨i, inv, h⟩, assign⟧ = inv := denote_idx_false (A2_false i h)

/-- Node 0 of every AIG is false. -/
theorem den0 {aig : AIG Nat} (r : aig.Ref) (hg : r.gate = 0) (assign) : ⟦aig, r, assign⟧ = r.invert := by
  obtain ⟨g, inv, h⟩ := r
  simp only at hg; subst hg
  exact denote_idx_false aig.hconst

/-- #[false, gate(0,¬0), gate(¬1,¬1), gate(1,¬1), gate(¬1,1), gate(¬2,¬2)]; values
false, false, true, false, false, false. -/
def B : AIG Nat where
  decls := #[.false, .gate (.mk 0 false) (.mk 0 true), .gate (.mk 1 true) (.mk 1 true),
    .gate (.mk 1 false) (.mk 1 true), .gate (.mk 1 true) (.mk 1 false), .gate (.mk 2 true) (.mk 2 true)]
  cache := ⟨{}, Cache.WF.empty (by
    intro i h a
    match i, h with
    | 0, _ => nofun | 1, _ => nofun | 2, _ => nofun | 3, _ => nofun | 4, _ => nofun | 5, _ => nofun)⟩
  hdag := by
    intro i l r h hg
    match i, h with
    | 0, _ => cases hg
    | 1, _ => cases hg; decide
    | 2, _ => cases hg; decide
    | 3, _ => cases hg; decide
    | 4, _ => cases hg; decide
    | 5, _ => cases hg; decide
  hzero := by simp
  hconst := rfl

theorem B_den0 (inv h a) : ⟦B, ⟨0, inv, h⟩, a⟧ = inv := den0 _ rfl a
theorem B_den1 (inv h a) : ⟦B, ⟨1, inv, h⟩, a⟧ = inv := by
  rw [denote_idx_gate (lhs := .mk 0 false) (rhs := .mk 0 true) rfl]
  simp [B_den0]
theorem B_den2 (inv h a) : ⟦B, ⟨2, inv, h⟩, a⟧ = !inv := by
  rw [denote_idx_gate (lhs := .mk 1 true) (rhs := .mk 1 true) rfl]
  simp [B_den1]
theorem B_den3 (inv h a) : ⟦B, ⟨3, inv, h⟩, a⟧ = inv := by
  rw [denote_idx_gate (lhs := .mk 1 false) (rhs := .mk 1 true) rfl]
  simp [B_den1]
theorem B_den4 (inv h a) : ⟦B, ⟨4, inv, h⟩, a⟧ = inv := by
  rw [denote_idx_gate (lhs := .mk 1 true) (rhs := .mk 1 false) rfl]
  simp [B_den1]

/-- Unit clauses ¬x0, ¬x1: satisfied exactly by the assignments that agree with A2. -/
def FF : CNF Nat := (CNF.empty.add (CNF.Clause.empty.add 0 false)).add (CNF.Clause.empty.add 1 false)

theorem FF_eval (a : Nat → Bool) : FF.eval a = (!a 1 && !a 0) := by
  simp [FF]

/-- A CNF cache of A2 with arbitrary marks (valid for FF). -/
def cc (m : Array Bool) (hm : m.size = 2) : toCNF.Cache A2 FF where
  marks := m
  hmarks := hm
  inv := by
    intro assign heval idx hbound _
    rw [FF_eval] at heval
    rw [A2_den]
    have : idx = 0 ∨ idx = 1 := by simp [A2] at hbound; omega
    rcases this with rfl | rfl <;> simp_all

theorem FF_inv : toCNF.State.Inv A2 FF := by
  intro assign1 assign hagree
  have h0 := hagree 0 (by decide)
  have h1 := hagree 1 (by decide)
  rw [A2_den] at h0 h1
  simp [CNF.sat_def, FF_eval, h0, h1]

/-- A CNF state of A2 with arbitrary marks. -/
def st (m : Array Bool) (hm : m.size = 2) : toCNF.State A2 := ⟨FF, cc m hm, FF_inv⟩

/-- An unsatisfiable CNF (one empty clause). -/
def Fbad : CNF Nat := CNF.empty.add CNF.Clause.empty

/-- A CNF that is false at the canonical satisfying assignment violates State.Inv. -/
theorem notInv (aig : AIG Nat) (cnf : CNF Nat) (a1 : Nat → Bool)
    (h : cnf.eval ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.cnfSatAssignment) aig a1) = false) :
    ¬ toCNF.State.Inv aig cnf := by
  intro hi
  have := hi a1 _ (fun idx h => (priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.satAssignment_lt) h)
  rw [CNF.sat_def] at this
  simp_all

theorem csa (aig : AIG Nat) (a1 : Nat → Bool) (i : Nat) (h : i < aig.decls.size) :
    (priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.cnfSatAssignment) aig a1 i = ⟦aig, ⟨i, false, h⟩, a1⟧ :=
  (priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.satAssignment_lt) h


local notation "tt" => cc #[true, true] rfl
local notation "ff" => cc #[false, false] rfl
local notation "tf" => cc #[true, false] rfl
local notation "ft" => cc #[false, true] rfl
local notation "stt" => st #[true, true] rfl
local notation "sff" => st #[false, false] rfl
local notation "stf" => st #[true, false] rfl
local notation "sft" => st #[false, true] rfl
local notation "af" => (fun _ : Nat => false)
local notation "fz" => Fanin.mk 0 false

-- `Std.Sat.AIG.toCNF'.denote_as_go` (h1): start = 5 in the two-node AIG A2.
theorem cnf_toCNFq_denote_as_go_6 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.denote_as_go 6 := fun H => by
  exact absurd (@H Nat _ _ A2 5 false af) (by decide)

-- `Std.Sat.AIG.toCNF'.denote_as_go` (a): A2, start = 0, inv = true, assign = cnfSatAssignment: the go CNF is sat there (go_sat) and the final unit clause asks node 0 to be false, so the CNF evaluates to true although node 0 inverted denotes true.
theorem cnf_toCNFq_denote_as_go_8 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.denote_as_go 8 := fun H => by
  have h := @H Nat _ _ A2 0 true (by decide) ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.cnfSatAssignment) A2 af)
  have hs := (priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.go_sat) A2 0 (by decide) af (toCNF.State.empty A2)
  have hs' := (CNF.sat_def _ _).mp hs
  simp only [CNF.eval_add, hs', Bool.and_true, CNF.Clause.eval_add, CNF.Clause.eval_empty] at h
  rw [csa A2 _ 0 (by decide), A2_den] at h
  simp at h

-- `Std.Sat.AIG.toCNF'.go_as_denote` (h1): start = 5 in A2.
theorem cnf_toCNFq_go_as_denote_7 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.go_as_denote 7 := fun H => by
  exact absurd (@H Nat _ _ false false A2 5 af) (by decide)

-- `Std.Sat.AIG.toCNF'.go_as_denote` (a): without the premise the conclusion fixes the denotation to an arbitrary sat?: node 0 of A2 with sat? = true.
theorem cnf_toCNFq_go_as_denote_9 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.go_as_denote 9 := fun H => by
  have := @H Nat _ _ false true A2 0 (by decide) af
  rw [A2_den] at this
  exact Bool.false_ne_true this

-- `Std.Sat.AIG.toCNF'.go_as_denote'` (h1): start = 5 in A2.
theorem cnf_toCNFq_go_as_denoteq_6 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.go_as_denote' 6 := fun H => by
  exact absurd (@H Nat _ _ A2 5 false af) (by decide)

-- `Std.Sat.AIG.toCNF'.go_marks` (h): start = 5 in A2.
theorem cnf_toCNFq_go_marks_5 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.go_marks 5 := fun H => by
  exact absurd (@H Nat _ _ A2 5 sff) (by decide)

-- `Std.Sat.AIG.toCNF'.go_sat` (h1): start = 5 in A2.
theorem cnf_toCNFq_go_sat_5 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.go_sat 5 := fun H => by
  exact absurd (@H Nat _ _ A2 5 af sff) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy.extension` (hnew): new = 5 in A2 (caches with all marks set).
theorem cnf_toCNF_Cache_IsExtensionBy_extension_9 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.extension 9 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF tt tt 5 0 (by decide) rfl) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy.extension` (self): cache1 with all marks, cache2 with none (no extension): mark 0 is lost.
theorem cnf_toCNF_Cache_IsExtensionBy_extension_10 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.extension 10 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF tt ff 0 (by decide) 0 (by decide) rfl) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy.extension` (hidx): idx = 5 in A2.
theorem cnf_toCNF_Cache_IsExtensionBy_extension_12 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.extension 12 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF tt tt 0 (by decide) ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl) 5) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy.extension` (a): cache1 unmarked, cache2 marks only node 0 (an extension by 0): node 1 is not marked in cache2.
theorem cnf_toCNF_Cache_IsExtensionBy_extension_13 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.extension 13 := fun H => by
  have := @H Nat _ _ A2 FF FF ff tf 0 (by decide) ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl) 1 (by decide)
  exact absurd this (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy.trueAt` (hnew): new = 5 in A2.
theorem cnf_toCNF_Cache_IsExtensionBy_trueAt_9 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.trueAt 9 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF tt tt 5) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy.trueAt` (self): cache2 without marks: node 0 is not marked.
theorem cnf_toCNF_Cache_IsExtensionBy_trueAt_10 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.trueAt 10 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF tt ff 0 (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_rfl` (omega): removable (derivable): the bound omega (an auto-bound implicit produced by the term have := cache.hmarks; omega) follows from h : idx < cache.marks.size and cache.hmarks.
theorem cnf_toCNF_Cache_IsExtensionBy_rfl_6 : indep% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_rfl 6 := by
  intro α _ _ aig cnf idx cache h _
  exact cache.hmarks ▸ h

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_rfl` (h): removable (derivable): idx < cache.marks.size follows from omega : idx < aig.decls.size and cache.hmarks.
theorem cnf_toCNF_Cache_IsExtensionBy_rfl_8 : indep% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_rfl 8 := by
  intro α _ _ aig cnf idx omega cache
  rw [cache.hmarks]; exact omega

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_rfl` (hmarked): unmarked cache of A2, idx = 0: trueAt fails.
theorem cnf_toCNF_Cache_IsExtensionBy_rfl_9 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_rfl 9 := fun H => by
  obtain ⟨_, h⟩ := @H Nat _ _ A2 FF 0 (by decide) ff (by decide)
  exact absurd h (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_set` (hbound): idx = 5 in A2.
theorem cnf_toCNF_Cache_IsExtensionBy_set_9 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_set 9 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF ff ff 5) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_set` (h): cache2 unmarked (not the set array): trueAt at 0 fails.
theorem cnf_toCNF_Cache_IsExtensionBy_set_10 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_set 10 := fun H => by
  obtain ⟨_, h⟩ := @H Nat _ _ A2 FF FF ff ff 0 (by decide)
  exact absurd h (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_left` (hnew1): new1 = 5 in A2 (caches with all marks).
theorem cnf_toCNF_Cache_IsExtensionBy_trans_left_8 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_left 8 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF FF 5 0 (by decide) tt tt tt ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_left` (hnew2): new2 = 5 in A2 (caches with all marks).
theorem cnf_toCNF_Cache_IsExtensionBy_trans_left_10 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_left 10 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF FF 0 (by decide) 5 tt tt tt ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_left` (h12): marks 1: {0}, 2: {}, 3: {1}, new1 = 0, new2 = 1: 2 to 3 is an extension by 1, but 3 does not mark 0.
theorem cnf_toCNF_Cache_IsExtensionBy_trans_left_14 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_left 14 := fun H => by
  obtain ⟨_, h⟩ := @H Nat _ _ A2 FF FF FF 0 (by decide) 1 (by decide) tf ff ft ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)
  exact absurd h (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_left` (h23): 1 = 2 fully marked, 3 unmarked, new1 = new2 = 0: 3 does not mark 0.
theorem cnf_toCNF_Cache_IsExtensionBy_trans_left_15 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_left 15 := fun H => by
  obtain ⟨_, h⟩ := @H Nat _ _ A2 FF FF FF 0 (by decide) 0 (by decide) tt tt ff ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)
  exact absurd h (by decide)

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_left` (hnew1): new1 = 5 in A2 (states with all marks).
theorem cnf_toCNF_State_IsExtensionBy_trans_left_5 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_left 5 := fun H => by
  exact absurd (@H Nat _ _ A2 5 0 (by decide) stt stt stt ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)) (by decide)

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_left` (hnew2): new2 = 5 in A2 (states with all marks).
theorem cnf_toCNF_State_IsExtensionBy_trans_left_7 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_left 7 := fun H => by
  exact absurd (@H Nat _ _ A2 0 (by decide) 5 stt stt stt ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)) (by decide)

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_left` (h12): marks 1: {0}, 2: {}, 3: {1}, new1 = 0, new2 = 1: 2 to 3 is an extension by 1, but 3 does not mark 0.
theorem cnf_toCNF_State_IsExtensionBy_trans_left_11 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_left 11 := fun H => by
  obtain ⟨_, h⟩ := @H Nat _ _ A2 0 (by decide) 1 (by decide) stf sff sft ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)
  exact absurd h (by decide)

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_left` (h23): 1 = 2 fully marked, 3 unmarked, new1 = new2 = 0: 3 does not mark 0.
theorem cnf_toCNF_State_IsExtensionBy_trans_left_12 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_left 12 := fun H => by
  obtain ⟨_, h⟩ := @H Nat _ _ A2 0 (by decide) 0 (by decide) stt stt sff ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)
  exact absurd h (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_right` (hnew1): new1 = 5 in A2 (caches with all marks).
theorem cnf_toCNF_Cache_IsExtensionBy_trans_right_8 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_right 8 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF FF 5 0 (by decide) tt tt tt ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_right` (hnew2): new2 = 5 in A2 (caches with all marks).
theorem cnf_toCNF_Cache_IsExtensionBy_trans_right_10 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_right 10 := fun H => by
  exact absurd (@H Nat _ _ A2 FF FF FF 0 (by decide) 5 tt tt tt ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_right` (h12): marks 1: {0}, 2: {}, 3: {1}, new1 = 0, new2 = 1: 2 to 3 is an extension by 1, but mark 0 of 1 is lost in 3.
theorem cnf_toCNF_Cache_IsExtensionBy_trans_right_14 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_right 14 := fun H => by
  obtain ⟨h, _⟩ := @H Nat _ _ A2 FF FF FF 0 (by decide) 1 (by decide) tf ff ft ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)
  exact absurd (h 0 (by decide) rfl) (by decide)

-- `Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_right` (h23): 1 = 2 fully marked, 3 unmarked, new1 = new2 = 0: 3 does not mark 0.
theorem cnf_toCNF_Cache_IsExtensionBy_trans_right_15 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy_trans_right 15 := fun H => by
  obtain ⟨_, h⟩ := @H Nat _ _ A2 FF FF FF 0 (by decide) 0 (by decide) tt tt ff ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)
  exact absurd h (by decide)

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_right` (hnew1): new1 = 5 in A2 (states with all marks).
theorem cnf_toCNF_State_IsExtensionBy_trans_right_5 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_right 5 := fun H => by
  exact absurd (@H Nat _ _ A2 5 0 (by decide) stt stt stt ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)) (by decide)

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_right` (hnew2): new2 = 5 in A2 (states with all marks).
theorem cnf_toCNF_State_IsExtensionBy_trans_right_7 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_right 7 := fun H => by
  exact absurd (@H Nat _ _ A2 0 (by decide) 5 stt stt stt ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)) (by decide)

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_right` (h12): marks 1: {0}, 2: {}, 3: {1}, new1 = 0, new2 = 1: 2 to 3 is an extension by 1, but mark 0 of 1 is lost in 3.
theorem cnf_toCNF_State_IsExtensionBy_trans_right_11 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_right 11 := fun H => by
  obtain ⟨h, _⟩ := @H Nat _ _ A2 0 (by decide) 1 (by decide) stf sff sft ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)
  exact absurd (h 0 (by decide) rfl) (by decide)

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_right` (h23): 1 = 2 fully marked, 3 unmarked, new1 = new2 = 0: 3 does not mark 0.
theorem cnf_toCNF_State_IsExtensionBy_trans_right_12 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_trans_right 12 := fun H => by
  obtain ⟨_, h⟩ := @H Nat _ _ A2 0 (by decide) 0 (by decide) stt stt sff ((priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.Cache.IsExtensionBy.mk) (by decide) rfl)
  exact absurd h (by decide)

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_rfl` (omega): removable (derivable): the bound omega (auto-bound implicit from the term have := state.cache.hmarks; omega) follows from h and state.cache.hmarks.
theorem cnf_toCNF_State_IsExtensionBy_rfl_5 : indep% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_rfl 5 := by
  intro α _ _ aig idx state h _
  exact state.cache.hmarks ▸ h

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_rfl` (h): removable (derivable): idx < state.cache.marks.size follows from omega and state.cache.hmarks.
theorem cnf_toCNF_State_IsExtensionBy_rfl_7 : indep% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_rfl 7 := by
  intro α _ _ aig idx omega state
  rw [state.cache.hmarks]; exact omega

-- `Std.Sat.AIG.toCNF.State.IsExtensionBy_rfl` (hmarked): unmarked state of A2, idx = 0: trueAt fails.
theorem cnf_toCNF_State_IsExtensionBy_rfl_8 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.IsExtensionBy_rfl 8 := fun H => by
  obtain ⟨_, h⟩ := @H Nat _ _ A2 0 (by decide) sff (by decide)
  exact absurd h (by decide)

-- `Std.Sat.AIG.toCNF.State.Inv_append` (h1): cnf1 = one empty clause (unsat), cnf2 = FF on A2: the append is false at the agreeing assignment.
theorem cnf_toCNF_State_Inv_append_6 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_append 6 := fun H => by
  exact notInv A2 _ af (by simp [Fbad]) (@H Nat _ _ A2 Fbad FF FF_inv)

-- `Std.Sat.AIG.toCNF.State.Inv_append` (h2): cnf1 = FF on A2, cnf2 = one empty clause (unsat).
theorem cnf_toCNF_State_Inv_append_7 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_append 7 := fun H => by
  exact notInv A2 _ af (by simp [Fbad]) (@H Nat _ _ A2 FF Fbad FF_inv)

-- `Std.Sat.AIG.toCNF.State.Inv_falseToCNF` (h): upper = 5 in A2.
theorem cnf_toCNF_State_Inv_falseToCNF_5 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_falseToCNF 5 := fun H => by
  exact absurd (@H Nat _ _ A2 5) (by decide)

-- `Std.Sat.AIG.toCNF.State.Inv_falseToCNF` (heq): node 2 of B is a gate denoting true; the clause 'node 2 is false' fails at the agreeing assignment.
theorem cnf_toCNF_State_Inv_falseToCNF_6 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_falseToCNF 6 := fun H => by
  refine notInv B _ af ?_ (@H Nat _ _ B 2 (by decide))
  simp [priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.Decl.falseToCNF_eval, csa B _ 2 (by decide), B_den2]

-- `Std.Sat.AIG.toCNF.State.Inv_gateToCNF` (h): upper = 5 in A2.
theorem cnf_toCNF_State_Inv_gateToCNF_7 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_gateToCNF 7 := fun H => by
  exact absurd (@H Nat _ _ 5 fz fz A2) (by decide)

-- `Std.Sat.AIG.toCNF.State.Inv_gateToCNF` (heq): node 0 of A2 (false) treated as gate(¬0, ¬0) = true: the gate CNF fails at the agreeing assignment.
theorem cnf_toCNF_State_Inv_gateToCNF_8 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_gateToCNF 8 := fun H => by
  refine notInv A2 _ af ?_ (@H Nat _ _ 0 (.mk 0 true) (.mk 0 true) A2 (by decide))
  simp [priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.Decl.gateToCNF_eval, csa A2 _ 0 (by decide), A2_den]

-- `Std.Sat.AIG.toCNF.State.Inv_iteToCNF` (h): idx = 5 in A2, all fanins node 0.
theorem cnf_toCNF_State_Inv_iteToCNF_8 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_iteToCNF 8 := fun H => by
  exact absurd (@H Nat _ _ A2 fz fz fz 5 (by decide) (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.State.Inv_iteToCNF` (hltc): idx = 1 in A2, cond = node 1.
theorem cnf_toCNF_State_Inv_iteToCNF_9 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_iteToCNF 9 := fun H => by
  exact absurd (@H Nat _ _ A2 (.mk 1 false) fz fz 1 (by decide) (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.State.Inv_iteToCNF` (hltt): idx = 1 in A2, ifTrue = node 1.
theorem cnf_toCNF_State_Inv_iteToCNF_10 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_iteToCNF 10 := fun H => by
  exact absurd (@H Nat _ _ A2 fz (.mk 1 false) fz 1 (by decide) (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.State.Inv_iteToCNF` (hltf): idx = 1 in A2, ifFalse = node 1.
theorem cnf_toCNF_State_Inv_iteToCNF_11 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_iteToCNF 11 := fun H => by
  exact absurd (@H Nat _ _ A2 fz fz (.mk 1 false) 1 (by decide) (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.State.Inv_iteToCNF` (hdenote): A2, idx = 1 (false) with cond = ifTrue = ¬node0 (true): the ite CNF says node 1 is true, false at the agreeing assignment.
theorem cnf_toCNF_State_Inv_iteToCNF_12 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.State.Inv_iteToCNF 12 := fun H => by
  refine notInv A2 _ af ?_ (@H Nat _ _ A2 (.mk 0 true) (.mk 0 true) fz 1 (by decide) (by decide) (by decide) (by decide))
  simp [priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.Decl.iteToCNF_eval, csa A2 _ 0 (by decide), csa A2 _ 1 (by decide), A2_den]

-- `Std.Sat.AIG.toCNF.denote_detectIte` (h): root = 5 in A2.
theorem cnf_toCNF_denote_detectIte_6 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.denote_detectIte 6 := fun H => by
  exact absurd (@H Nat _ _ A2 af 5 fz fz fz) (by decide)

-- `Std.Sat.AIG.toCNF.denote_detectIte` (heq): root = 0 of A2 is not a gate, detectIte gives none.
theorem cnf_toCNF_denote_detectIte_10 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.denote_detectIte 10 := fun H => by
  exact absurd (@H Nat _ _ A2 af 0 (by decide) fz fz fz) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte.denote_go` (hroot): AIG B, root = 10, l = r = ¬node1 with node1 = gate(0, ¬0) (go detects the ite).
theorem cnf_toCNF_detectIte_denote_go_15 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte.denote_go 15 := fun H => by
  exact absurd (@H Nat _ _ af B 10 (.mk 1 true) (.mk 1 true) fz (.mk 0 true) fz (.mk 0 true) fz fz (.mk 0 true)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte.denote_go` (hl): removable (derivable): heqroot and the DAG property give l.gate < root < size.
theorem cnf_toCNF_detectIte_denote_go_16 : indep% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte.denote_go 16 := by
  intro α _ _ assign aig root l r l0 l1 r0 r1 c t f hroot hr heq heqroot heqr hinvl hinvr
  exact Nat.lt_trans (aig.hdag hroot heqroot).1 hroot

-- `Std.Sat.AIG.toCNF.detectIte.denote_go` (hr): removable (derivable): heqroot and the DAG property give r.gate < root < size.
theorem cnf_toCNF_detectIte_denote_go_17 : indep% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte.denote_go 17 := by
  intro α _ _ assign aig root l r l0 l1 r0 r1 c t f hroot hl heq heqroot heql hinvl hinvr
  exact Nat.lt_trans (aig.hdag hroot heqroot).2 hroot

-- `Std.Sat.AIG.toCNF.detectIte.denote_go` (heq): AIG B, root 5 = gate(¬2, ¬2), node 2 = gate(¬1, ¬1): no complementary fanins, go gives none.
theorem cnf_toCNF_detectIte_denote_go_18 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte.denote_go 18 := fun H => by
  exact absurd (@H Nat _ _ af B 5 (.mk 2 true) (.mk 2 true) (.mk 1 true) (.mk 1 true) (.mk 1 true) (.mk 1 true) fz fz fz
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte.denote_go` (heqroot): AIG B, root = 0 (false) while l = r = ¬node1 describe the ite (0 ? 0 : ¬0) = true.
theorem cnf_toCNF_detectIte_denote_go_19 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte.denote_go 19 := fun H => by
  have := @H Nat _ _ af B 0 (.mk 1 true) (.mk 1 true) fz (.mk 0 true) fz (.mk 0 true) fz fz (.mk 0 true)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp [B_den0] at this

-- `Std.Sat.AIG.toCNF.detectIte.denote_go` (heql): AIG B, root 2, l = r = ¬node1, wrong l0 = l1 = ¬0 (go still matches l0 with r0 = 0): node 1 is gate(0, ¬0).
theorem cnf_toCNF_detectIte_denote_go_20 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte.denote_go 20 := fun H => by
  exact absurd (@H Nat _ _ af B 2 (.mk 1 true) (.mk 1 true) (.mk 0 true) (.mk 0 true) fz (.mk 0 true) (.mk 0 true) fz fz
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte.denote_go` (heqr): AIG B, root 2, l = r = ¬node1, wrong r0 = r1 = ¬0 (go still matches l0 = 0 with r0): node 1 is gate(0, ¬0).
theorem cnf_toCNF_detectIte_denote_go_21 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte.denote_go 21 := fun H => by
  exact absurd (@H Nat _ _ af B 2 (.mk 1 true) (.mk 1 true) fz (.mk 0 true) (.mk 0 true) (.mk 0 true) fz fz fz
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte.denote_go` (hinvl): AIG B, root 3 = gate(node1, ¬node1) (l not inverted) denotes false, the detected ite (0 ? 0 : ¬0) is true.
theorem cnf_toCNF_detectIte_denote_go_22 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte.denote_go 22 := fun H => by
  have := @H Nat _ _ af B 3 (.mk 1 false) (.mk 1 true) fz (.mk 0 true) fz (.mk 0 true) fz fz (.mk 0 true)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp [B_den3, B_den0] at this

-- `Std.Sat.AIG.toCNF.detectIte.denote_go` (hinvr): AIG B, root 4 = gate(¬node1, node1) (r not inverted) denotes false, the detected ite (0 ? 0 : ¬0) is true.
theorem cnf_toCNF_detectIte_denote_go_23 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte.denote_go 23 := fun H => by
  have := @H Nat _ _ af B 4 (.mk 1 true) (.mk 1 false) fz (.mk 0 true) fz (.mk 0 true) fz fz (.mk 0 true)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp [B_den4, B_den0] at this

-- `Std.Sat.AIG.toCNF.detectIte_cond_lt` (h): root = 5 in A2.
theorem cnf_toCNF_detectIte_cond_lt_8 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte_cond_lt 8 := fun H => by
  exact absurd (@H Nat _ _ A2 5 fz fz fz) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte_cond_lt` (heq): root = 0 of A2, c = node 3.
theorem cnf_toCNF_detectIte_cond_lt_9 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte_cond_lt 9 := fun H => by
  exact absurd (@H Nat _ _ A2 0 (.mk 3 false) fz fz (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte_ifTrue_lt` (h): root = 5 in A2.
theorem cnf_toCNF_detectIte_ifTrue_lt_8 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte_ifTrue_lt 8 := fun H => by
  exact absurd (@H Nat _ _ A2 5 fz fz fz) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte_ifTrue_lt` (heq): root = 0 of A2, t = node 3.
theorem cnf_toCNF_detectIte_ifTrue_lt_9 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte_ifTrue_lt 9 := fun H => by
  exact absurd (@H Nat _ _ A2 0 fz (.mk 3 false) fz (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte_ifFalse_lt` (h): root = 5 in A2.
theorem cnf_toCNF_detectIte_ifFalse_lt_8 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte_ifFalse_lt 8 := fun H => by
  exact absurd (@H Nat _ _ A2 5 fz fz fz) (by decide)

-- `Std.Sat.AIG.toCNF.detectIte_ifFalse_lt` (heq): root = 0 of A2, f = node 3.
theorem cnf_toCNF_detectIte_ifFalse_lt_9 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.detectIte_ifFalse_lt 9 := fun H => by
  exact absurd (@H Nat _ _ A2 0 fz fz (.mk 3 false) (by decide)) (by decide)

-- `Std.Sat.AIG.toCNF.projectLeftAssign_atom` (hidx): idx = 5 in A2.
theorem cnf_toCNF_projectLeftAssign_atom_7 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.projectLeftAssign_atom 7 := fun H => by
  exact absurd (@H Nat _ _ 5 0 af A2) (by decide)

-- `Std.Sat.AIG.toCNF.projectLeftAssign_atom` (h): the left side does not depend on idx: idx = 0 and idx = 1 in A2 with assign = (· == 0) give true = false.
theorem cnf_toCNF_projectLeftAssign_atom_8 : ¬ drop0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.projectLeftAssign_atom 8 := fun H => by
  have h0 := @H Nat _ _ 0 0 (fun i => i == 0) A2 (by decide)
  have h1 := @H Nat _ _ 1 0 (fun i => i == 0) A2 (by decide)
  exact absurd (h0.symm.trans h1) (by decide)

-- `Std.Sat.AIG.toCNF.satAssignment_lt` (h): idx = 5 in A2.
theorem cnf_toCNF_satAssignment_lt_6 : ¬ indep0% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF.satAssignment_lt 6 := fun H => by
  exact absurd (@H Nat _ _ A2 5 af) (by decide)

-- `Std.Sat.AIG.toCNF'.go_as_denote'` (a): removable: the CNF produced by go is always true at cnfSatAssignment (sibling lemma go_sat), whatever the node denotes.
theorem cnf_toCNFq_go_as_denoteq_8 : drop% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.go_as_denote' 8 := by
  intro α _ _ aig start inv h1 assign1
  exact (priv% _private.Std.Sat.AIG.CNF.«0».Std.Sat.AIG.toCNF'.go_sat) aig start h1 assign1 _

end SatBVHand

namespace SatBVHand
open Std Std.Sat Std.Sat.AIG Std.Tactic.BVDecide

/-! ## Bitblaster (`Cpop`): reference vectors to node 0 of the empty AIG -/

local notation "A0" => (AIG.empty : AIG Nat)
local notation "af" => (fun _ : Nat => false)

/-- n references to node 0 (inverted iff inv): they denote inv in every AIG. -/
def vk (aig : AIG Nat) (n : Nat) (inv : Bool) : aig.RefVec n :=
  ⟨Vector.replicate n (Fanin.mk 0 inv), by intro i h; simp [aig.hzero]⟩

theorem den_vk (aig : AIG Nat) (n inv i h assign) : ⟦aig, (vk aig n inv).get i h, assign⟧ = inv := by
  rw [den0 _ (by simp [vk, RefVec.get])]
  simp [vk, RefVec.get]

theorem eae1 (x : BitVec 1) (k : Nat) : (BitVec.extractAndExtend 1 x).getLsbD k = x.getLsbD k := by
  rw [BitVec.getLsbD_extractAndExtend (by decide)]
  simp only [Nat.mod_one, Nat.sub_zero, Nat.div_one]
  rw [BitVec.getLsbD_extractAndExtendBit]
  simp

theorem cpopTree_one {w : Nat} (x : BitVec (1 * w)) : BitVec.cpopTree x = x.cast (by simp) := by
  rw [BitVec.cpopTree]; simp

theorem cpl (bv : BitVec (1 * 1)) (h) : (bv.cpopLayer 0#(0 * 1) h).getLsbD 0 = bv.getLsbD 0 := by
  rw [BitVec.getLsbD_cpopLayer h (by intro i hi; omega)]
  revert bv; decide

/-- blastCpopLayer.go at the last iteration returns newLayer. -/
theorem cpopGo_done : BVExpr.bitblast.blastCpopLayer.go (outWidth := (1 + 1) / 2 * 1) (aig := A0) (len := 1)
    (w := 1) 1 (vk A0 (1*1) false) (vk A0 (1*1) true) (by decide) rfl = ⟨A0, vk A0 (1*1) true⟩ := by
  rw [BVExpr.bitblast.blastCpopLayer.go]
  rfl

/-- blastExtractAndExtend.go at the last index returns acc. -/
theorem eaeGo_done : BVExpr.bitblast.blastExtractAndExtend.go (outWidth := 1 * 1) (aig := A0) (w := 1) 1
    (vk A0 1 false) (vk A0 (1*1) true) (by decide) rfl = ⟨A0, vk A0 (1*1) true⟩ := by
  rw [BVExpr.bitblast.blastExtractAndExtend.go]
  rfl

/-- Erase evaluates for every BEq (copy of the library proof of literals_erase_go without LawfulBEq). -/
theorem literals_erase_go_any {α : Type u} [BEq α] {c : CNF.Clause α} {lit : Literal α} {i : Nat}
    {acc : CNF.Clause α} :
    ((priv% _private.Std.Sat.CNF.Basic.«0».Std.Sat.CNF.Clause.erase.go) c lit i acc).literals
      = acc.literals ++ (c.literals.drop i).filter (fun l => l != lit) := by
  fun_induction (priv% _private.Std.Sat.CNF.Basic.«0».Std.Sat.CNF.Clause.erase.go) c lit i acc with
  | case1 i acc h atom pol heq ih =>
    have hlt : i < c.literals.length := by rw [CNF.Clause.length_literals]; exact h
    have hlit : c.literals[i] = (atom, pol) := by
      rw [CNF.Clause.Internal.getElem_literals hlt,
        CNF.Clause.Internal.polarity_eq_getElem (by rw [c.size_polarities]; exact h)]
    have hb : (((atom, pol) : Literal α) != lit) = false := by
      cases lit; simp only [bne, BEq.beq] at heq ⊢; simp [heq]
    rw [List.drop_eq_getElem_cons hlt, List.filter_cons, hlit, hb]
    simp [ih]
  | case2 i acc h atom pol heq ih =>
    have hlt : i < c.literals.length := by rw [CNF.Clause.length_literals]; exact h
    have hlit : c.literals[i] = (atom, pol) := by
      rw [CNF.Clause.Internal.getElem_literals hlt,
        CNF.Clause.Internal.polarity_eq_getElem (by rw [c.size_polarities]; exact h)]
    have hb : (((atom, pol) : Literal α) != lit) = true := by
      cases lit; simp only [bne, BEq.beq] at heq ⊢; simp [heq]
    rw [List.drop_eq_getElem_cons hlt, List.filter_cons, hlit, ih, CNF.Clause.literals_add, hb]
    simp
  | case3 i acc h =>
    rw [List.drop_of_length_le (by rw [CNF.Clause.length_literals]; omega)]
    simp

/-- The LRAT state with the single clause ¬x0 (at index 1). -/
def sN : Std.Tactic.BVDecide.LRAT.Internal.State := ⟨#[some (CNF.Clause.unit 0 false)]⟩

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer_denote_mem_prefix.go` (hstart): start = 5 in the empty AIG (len = 1, w = 0, iterNum = 0).
theorem cpop_blastCpopLayer_denote_mem_prefix_go_10 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer_denote_mem_prefix.go 10 := fun H => by
  exact absurd (@H Nat _ _ 1 0 af 5 false A0 0 (by decide) (vk A0 (1*0) false) (vk A0 (0*0) false)) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer_denote_mem_prefix.go` (hold'): len = 0, iterNum = 0: 2 * (0 - 1) < 0 fails.
theorem cpop_blastCpopLayer_denote_mem_prefix_go_11 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer_denote_mem_prefix.go 11 := fun H => by
  exact absurd (@H Nat _ _ 0 0 af 0 false A0 0 (by decide) (vk A0 (0*0) false) (vk A0 (0*0) false)) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastExtractAndExtendBit_denote_mem_prefix` (hstart): start = 5 in the empty AIG.
theorem cpop_blastExtractAndExtendBit_denote_mem_prefix_10 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.blastExtractAndExtendBit_denote_mem_prefix 10 := fun H => by
  exact absurd (@H Nat _ _ 0 5 af false A0 0 (vk A0 0 false)) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_append_blastExtractAndExtendBit` (hidx): w = currIdx = idx = 0.
theorem cpop_denote_append_blastExtractAndExtendBit_11 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_append_blastExtractAndExtendBit 11 := fun H => by
  exact absurd (@H Nat _ _ 0 af A0 0 0 0#0 (vk A0 0 false) (vk A0 (0*0) false) (by intro _ h; omega) (by intro _ h; omega)) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_append_blastExtractAndExtendBit` (hacc): w = currIdx = 1, x = 0, acc = one reference to ¬node0 (true): index 0 comes from acc, which disagrees with bit 0 of extractAndExtend.
theorem cpop_denote_append_blastExtractAndExtendBit_12 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_append_blastExtractAndExtendBit 12 := fun H => by
  have h := @H Nat _ _ 0 af A0 1 1 0#1 (vk A0 1 false) (vk A0 (1*1) true) (by decide) (by intro i hi; rw [den_vk]; simp)
  rw [RefVec.get_append] at h
  simp only [show (0 : Nat) < 1 * 1 from Nat.one_pos, dite_true, RefVec.get_cast] at h
  rw [den0 _ (by simp [vk, RefVec.get, Ref.cast]), eae1] at h
  simp [vk, RefVec.get, Ref.cast] at h

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_append_blastExtractAndExtendBit` (hx): the same circuit (w = 1, currIdx = 0) at x = 0#1 and x = 1#1: the predicted bit 0 differs.
theorem cpop_denote_append_blastExtractAndExtendBit_13 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_append_blastExtractAndExtendBit 13 := fun H => by
  have h0 := @H Nat _ _ 0 af A0 0 1 0#1 (vk A0 1 false) (vk A0 (1*0) false) (by decide) (by intro _ h; omega)
  have h1 := @H Nat _ _ 0 af A0 0 1 1#1 (vk A0 1 false) (vk A0 (1*0) false) (by decide) (by intro _ h; omega)
  have := h0.symm.trans h1
  rw [eae1, eae1] at this
  exact absurd this (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer` (hold'): len = w = 1, iterNum = 5: 2 * 4 < 1 fails.
theorem cpop_denote_blastCpopLayer_10 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer 10 := fun H => by
  exact absurd (@H Nat _ _ 1 1 5 af A0 (vk A0 (1*1) false) 0#(1*1) (by intro i hi; rw [den_vk]; simp) 0 (by decide)) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer` (hold): the same circuit (len = w = 1) at oldLayerBv = 0#1 and 1#1: the predicted bit 0 differs.
theorem cpop_denote_blastCpopLayer_11 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer 11 := fun H => by
  have h0 := @H Nat _ _ 1 1 0 af A0 (vk A0 (1*1) false) 0#(1*1) (by decide) 0 (by decide)
  have h1 := @H Nat _ _ 1 1 0 af A0 (vk A0 (1*1) false) 1#(1*1) (by decide) 0 (by decide)
  have := h0.symm.trans h1
  rw [cpl, cpl] at this
  exact absurd this (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer` (hidx): len = w = 1, idx = 5.
theorem cpop_denote_blastCpopLayer_13 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer 13 := fun H => by
  exact absurd (@H Nat _ _ 1 1 0 af A0 (vk A0 (1*1) false) 0#(1*1) (by decide) (by intro i hi; rw [den_vk]; simp) 5) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go` (hold'): len = w = 1, iterNum = 5: 2 * 4 < 1 fails.
theorem cpop_denote_blastCpopLayer_go_11 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go 11 := fun H => by
  exact absurd (@H Nat _ _ 1 1 af A0 5 (vk A0 (1*1) false) (vk A0 (5*1) false) 0#(1*1) (by intro i hi; rw [den_vk]; simp) 0 (by decide)) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go` (hold): the same circuit (len = w = 1, iterNum = 0, empty newLayer) at oldLayerBv = 0#1 and 1#1: the predicted bit 0 differs.
theorem cpop_denote_blastCpopLayer_go_12 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go 12 := fun H => by
  have h0 := @H Nat _ _ 1 1 af A0 0 (vk A0 (1*1) false) (vk A0 (0*1) false) 0#(1*1) (by decide) (by intro _ h; omega) 0 (by decide)
  have h1 := @H Nat _ _ 1 1 af A0 0 (vk A0 (1*1) false) (vk A0 (0*1) false) 1#(1*1) (by decide) (by intro _ h; omega) 0 (by decide)
  have := h0.symm.trans h1
  rw [cpl, cpl] at this
  exact absurd this (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go` (hnew): len = w = iterNum = 1: go returns newLayer = ¬node0 (true), but bit 0 of the layer of 0#1 is false.
theorem cpop_denote_blastCpopLayer_go_13 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go 13 := fun H => by
  have h := @H Nat _ _ 1 1 af A0 1 (vk A0 (1*1) false) (vk A0 (1*1) true) 0#(1*1) (by decide)
    (by intro i hi; rw [den_vk]; simp) 0 (by decide)
  rw [cpopGo_done, den_vk, cpl] at h
  exact absurd h (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go` (hidx): len = w = 1, iterNum = 0, idx = 5.
theorem cpop_denote_blastCpopLayer_go_15 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go 15 := fun H => by
  exact absurd (@H Nat _ _ 1 1 af A0 0 (vk A0 (1*1) false) (vk A0 (0*1) false) 0#(1*1) (by decide) (by intro i hi; rw [den_vk]; simp) (by intro _ h; omega) 5) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree` (h): len = 0, w = 1, idx = 0.
theorem cpop_denote_blastCpopTree_8 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree 8 := fun H => by
  exact absurd (@H Nat _ _ 1 af A0 0 (vk A0 (0*1) false) 0#(0*1) (by intro _ h; omega) 0 (by decide)) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree` (hpar): the same circuit (len = w = 1) at bv = 0#1 and 1#1: the predicted bit 0 differs.
theorem cpop_denote_blastCpopTree_10 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree 10 := fun H => by
  have h0 := @H Nat _ _ 1 af A0 1 (vk A0 (1*1) false) (by decide) 0#(1*1) 0 (by decide)
  have h1 := @H Nat _ _ 1 af A0 1 (vk A0 (1*1) false) (by decide) 1#(1*1) 0 (by decide)
  have := h0.symm.trans h1
  rw [cpopTree_one, cpopTree_one] at this
  exact absurd this (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree` (hidx): w = 0, len = 1, idx = 0.
theorem cpop_denote_blastCpopTree_12 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree 12 := fun H => by
  exact absurd (@H Nat _ _ 0 af A0 1 (vk A0 (1*0) false) (by decide) 0#(1*0) (by intro _ h; omega) 0) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree.go` (h): len = 0, w = 1, idx = 0.
theorem cpop_denote_blastCpopTree_go_8 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree.go 8 := fun H => by
  exact absurd (@H Nat _ _ 1 af A0 0 (vk A0 (0*1) false) 0#(0*1) (by intro _ h; omega) 0 (by decide)) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree.go` (hpar): the same circuit (len = w = 1) at bv = 0#1 and 1#1: the predicted bit 0 differs.
theorem cpop_denote_blastCpopTree_go_10 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree.go 10 := fun H => by
  have h0 := @H Nat _ _ 1 af A0 1 (vk A0 (1*1) false) (by decide) 0#(1*1) 0 (by decide)
  have h1 := @H Nat _ _ 1 af A0 1 (vk A0 (1*1) false) (by decide) 1#(1*1) 0 (by decide)
  have := h0.symm.trans h1
  rw [cpopTree_one, cpopTree_one] at this
  exact absurd this (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree.go` (hidx): w = 0, len = 1, idx = 0.
theorem cpop_denote_blastCpopTree_go_12 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopTree.go 12 := fun H => by
  exact absurd (@H Nat _ _ 0 af A0 1 (vk A0 (1*0) false) (by decide) 0#(1*0) (by intro _ h; omega) 0) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend` (hx): the same circuit (w = 1) at x = 0#1 and x = 1#1: the predicted bit 0 differs.
theorem cpop_denote_blastExtractAndExtend_8 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend 8 := fun H => by
  have h0 := @H Nat _ _ af A0 1 (vk A0 1 false) 0#1 0 (by decide)
  have h1 := @H Nat _ _ af A0 1 (vk A0 1 false) 1#1 0 (by decide)
  have := h0.symm.trans h1
  rw [eae1, eae1] at this
  exact absurd this (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend` (hidx): w = 0, idx = 0.
theorem cpop_denote_blastExtractAndExtend_10 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend 10 := fun H => by
  exact absurd (@H Nat _ _ af A0 0 (vk A0 0 false) 0#0 (by intro _ h; omega) 0) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend.go` (hlt): w = 1, currIdx = 5 with acc five references to node 0 (all bits of extractAndExtend 0#1 are false).
theorem cpop_denote_blastExtractAndExtend_go_10 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend.go 10 := fun H => by
  exact absurd (@H Nat _ _ af A0 5 1 (vk A0 1 false) 0#1 (vk A0 (1*5) false) (by intro i hi; rw [den_vk, eae1]; simp)
    (by intro i hi; rw [den_vk]; simp) 0 (by decide)) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend.go` (hacc): w = currIdx = 1: go returns acc = ¬node0 (true), but bit 0 of extractAndExtend 0#1 is false.
theorem cpop_denote_blastExtractAndExtend_go_11 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend.go 11 := fun H => by
  have h := @H Nat _ _ af A0 1 1 (vk A0 1 false) 0#1 (vk A0 (1*1) true) (by decide) (by intro i hi; rw [den_vk]; simp) 0 (by decide)
  rw [eaeGo_done, den_vk, eae1] at h
  exact absurd h (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend.go` (hx): the same circuit (w = 1, currIdx = 0) at x = 0#1 and x = 1#1: the predicted bit 0 differs.
theorem cpop_denote_blastExtractAndExtend_go_12 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend.go 12 := fun H => by
  have h0 := @H Nat _ _ af A0 0 1 (vk A0 1 false) 0#1 (vk A0 (1*0) false) (by decide) (by intro _ h; omega) 0 (by decide)
  have h1 := @H Nat _ _ af A0 0 1 (vk A0 1 false) 1#1 (vk A0 (1*0) false) (by decide) (by intro _ h; omega) 0 (by decide)
  have := h0.symm.trans h1
  rw [eae1, eae1] at this
  exact absurd this (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend.go` (hidx): w = currIdx = idx = 0.
theorem cpop_denote_blastExtractAndExtend_go_14 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtend.go 14 := fun H => by
  exact absurd (@H Nat _ _ af A0 0 0 (vk A0 0 false) 0#0 (vk A0 (0*0) false) (by decide) (by intro _ h; omega) (by intro _ h; omega) 0) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtendBit` (hx): the same circuit (w = 1, start = 0) at x = 0#1 and x = 1#1: the predicted bit 0 differs.
theorem cpop_denote_blastExtractAndExtendBit_9 : ¬ drop0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtendBit 9 := fun H => by
  have h0 := @H Nat _ _ 1 af A0 (vk A0 1 false) 0#1 0 0 (by decide)
  have h1 := @H Nat _ _ 1 af A0 (vk A0 1 false) 1#1 0 0 (by decide)
  exact absurd (h0.symm.trans h1) (by decide)

-- `Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtendBit` (hidx): w = 0, idx = 0.
theorem cpop_denote_blastExtractAndExtendBit_11 : ¬ indep0% _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastExtractAndExtendBit 11 := fun H => by
  exact absurd (@H Nat _ _ 0 af A0 (vk A0 0 false) 0#0 0 (by intro _ h; omega) 0) (by decide)

-- `Std.Sat.CNF.Clause.literals_erase_go` (inst): removable: erase.go and the filter (· != lit) compare literals with the same atom == lit.1 && pol == lit.2, so the equation holds for every BEq (copy of the library proof; the sibling literals_erase is removable for the same reason).
theorem cnfb_literals_erase_go_2 : drop% _private.Std.Sat.CNF.Basic.«0».Std.Sat.CNF.Clause.literals_erase_go 2 := by
  intro α _ c lit i acc
  exact literals_erase_go_any

-- `Std.Tactic.BVDecide.LRAT.Internal.State.checkRatHintsExhaustive_spec` (h): state with the single clause ¬x0, negPivot = ¬x0, no RAT hints: the clause contains negPivot but no hint names it.
theorem lrat_checkRatHintsExhaustive_spec_3 : ¬ drop0% _private.Std.Tactic.BVDecide.LRAT.Internal.Rat.«0».Std.Tactic.BVDecide.LRAT.Internal.State.checkRatHintsExhaustive_spec 3 := fun H => by
  obtain ⟨idx, hints, _, hm⟩ := @H sN #[] (0, false) (CNF.Clause.unit 0 false)
    (by show _ ∈ (#[some (CNF.Clause.unit 0 false)].filterMap id); simp) (by simp [CNF.Clause.mem_unit])
  simp at hm

end SatBVHand
