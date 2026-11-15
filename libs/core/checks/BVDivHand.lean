import Std
import Lean

/-!
Hand pass `BVDiv` (hand18, 2026-11-08): the four division/remainder premises left open by the
BVDecide cluster (hand15). All four are removable:

* `blastUmod.denote_go_eq_divRec_r` idx 19 and `blastUmod.denote_go` idx 14 (`hq`): the
  remainder computed by `BitVec.divRec` never reads the quotient register.
* `blastUdiv.denote_go` idx 14 (`hq`): after `w` steps the initial quotient register has been
  shifted out completely.
* `blastUmod.denote_go` idx 16 (`hzero`): with divisor `0`, `divRec` leaves the dividend in the
  remainder register, and `lhs % 0 = lhs`.

Helpers (namespace `BVDivHand`): `bvOf` (a bit-vector with prescribed low bits), `step_agree` and
`divRec_agree` (quotient independence of `divRec`), `divRec_zero_d` (divisor-zero recurrence).

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/BVDivHand.lean`.
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

open Std.Tactic.BVDecide BVExpr.bitblast

namespace BVDivHand

/-! ### Bit-vector helpers -/

-- helper: a bit-vector of width `k` whose bits below `k` are given by `f`
def bvOf (f : Nat → Bool) : (k : Nat) → BitVec k
  | 0 => 0#0
  | k + 1 => BitVec.cons (f k) (bvOf f k)

theorem bvOf_getLsbD (f : Nat → Bool) (k i : Nat) (h : i < k) : (bvOf f k).getLsbD i = f i := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [bvOf, BitVec.getLsbD_cons]
    split
    · subst_vars; rfl
    · exact ih (by omega)

-- helper: one division step from two states that agree on `wn`, `wr`, `r` and on the quotient bits
-- below `k` gives states that agree on `wn`, `wr`, `r` and on the quotient bits below `k + 1`
theorem step_agree (k : Nat) (args : BitVec.DivModArgs w) (s t : BitVec.DivModState w)
    (hwn : s.wn = t.wn) (hwr : s.wr = t.wr) (hr : s.r = t.r)
    (hq : ∀ i, i < k → s.q.getLsbD i = t.q.getLsbD i) :
    (BitVec.divSubtractShift args s).wn = (BitVec.divSubtractShift args t).wn ∧
    (BitVec.divSubtractShift args s).wr = (BitVec.divSubtractShift args t).wr ∧
    (BitVec.divSubtractShift args s).r = (BitVec.divSubtractShift args t).r ∧
    (∀ i, i < k + 1 →
      (BitVec.divSubtractShift args s).q.getLsbD i = (BitVec.divSubtractShift args t).q.getLsbD i) := by
  rcases args with ⟨n, d⟩
  rcases s with ⟨wn, wr, q, r⟩
  rcases t with ⟨wn', wr', q', r'⟩
  simp only at hwn hwr hr hq
  subst hwn hwr hr
  simp only [BitVec.divSubtractShift]
  by_cases hc : BitVec.shiftConcat r (n.getLsbD (wn - 1)) < d
  all_goals
    simp only [hc, ↓reduceIte, BitVec.getLsbD_shiftConcat, true_and]
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · simp [h0]
    · simp [show i ≠ 0 by omega, hq (i - 1) (by omega)]

-- helper: `divRec` from states agreeing on `wn`, `wr`, `r` and quotient bits below `k` agrees on `r`
-- and on the quotient bits below `k + m`
theorem divRec_agree (m k : Nat) (args : BitVec.DivModArgs w) (s t : BitVec.DivModState w)
    (hwn : s.wn = t.wn) (hwr : s.wr = t.wr) (hr : s.r = t.r)
    (hq : ∀ i, i < k → s.q.getLsbD i = t.q.getLsbD i) :
    (BitVec.divRec m args s).r = (BitVec.divRec m args t).r ∧
    (∀ i, i < k + m → (BitVec.divRec m args s).q.getLsbD i = (BitVec.divRec m args t).q.getLsbD i) := by
  induction m generalizing k s t with
  | zero => exact ⟨hr, hq⟩
  | succ m ih =>
    simp only [BitVec.divRec_succ]
    obtain ⟨h1, h2, h3, h4⟩ := step_agree k args s t hwn hwr hr hq
    obtain ⟨e1, e2⟩ := ih (k + 1) _ _ h1 h2 h3 h4
    exact ⟨e1, fun i hi => e2 i (by omega)⟩

-- helper: with divisor `0`, the remainder register holds the dividend's bits above `wn`
theorem divRec_zero_d (n : BitVec w) (m wn wr : Nat) (q : BitVec w) (hm : m ≤ wn) :
    (BitVec.divRec m { n := n, d := 0#w } { wn := wn, wr := wr, q := q, r := n >>> wn }).r =
      n >>> (wn - m) := by
  induction m generalizing wn wr q with
  | zero => simp
  | succ m ih =>
    rw [BitVec.divRec_succ]
    have hs : BitVec.divSubtractShift { n := n, d := 0#w } { wn := wn, wr := wr, q := q, r := n >>> wn } =
        { wn := wn - 1, wr := wr + 1, q := q.shiftConcat true, r := n >>> (wn - 1) } := by
      simp only [BitVec.divSubtractShift, BitVec.not_lt_zero, ↓reduceIte, BitVec.sub_zero]
      rw [← BitVec.shiftRight_sub_one_eq_shiftConcat n (by omega)]
    rw [hs, ih (wn - 1) (wr + 1) _ (by omega)]
    congr 1
    omega

/-! ### Verdicts -/

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r`: `hq` is removable; the
-- remainder computed by `divRec` never reads the quotient (`divRec_agree`), so apply the theorem at
-- the bit-vector `bvOf` of the actual denotation of `q`.
theorem umod_divRec_r_hq : drop% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r 19 := by
  intro α _ _ w aig assign curr lhs rhs rbv qbv n d q r wn wr hleft hright hr idx hidx
  let f : Nat → Bool := fun i => if h : i < w then Std.Sat.AIG.denote assign ⟨aig, q.get i h⟩ else false
  rw [blastUmod.denote_go_eq_divRec_r aig assign curr lhs rhs rbv (bvOf f w) n d q r wn wr hleft hright
    ?_ hr idx hidx]
  · rw [(divRec_agree curr 0 { n := lhs, d := rhs } { wn := wn, wr := wr, q := bvOf f w, r := rbv }
      { wn := wn, wr := wr, q := qbv, r := rbv } rfl rfl rfl (by omega)).1]
  · intro i hi
    rw [bvOf_getLsbD f w i hi]
    simp [f, hi]

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go`: `hq` is removable; the library proof
-- goes through, using `umod_divRec_r_hq` (no quotient premise) for the recurrence.
theorem umod_denote_go_hq : drop% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go 14 := by
  intro α _ _ w aig assign lhs rhs n d q r hleft hright hr hzero idx hidx
  rw [BitVec.umod_eq_divRec hzero, BitVec.DivModState.init]
  exact umod_divRec_r_hq aig assign w lhs rhs 0#w 0#w n d q r w 0 hleft hright
    (by intro i hi; simp [hr]) idx hidx

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go`: `hzero` is removable; for divisor `0`,
-- `divRec` leaves the dividend in the remainder (`divRec_zero_d`) and `lhs % 0 = lhs`.
theorem umod_denote_go_hzero : drop% Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go 16 := by
  intro α _ _ w aig assign lhs rhs n d q r hleft hright hq hr idx hidx
  by_cases hz : 0#w < rhs
  · exact blastUmod.denote_go aig assign lhs rhs n d q r hleft hright hq hr hz idx hidx
  · have h0 : rhs = 0#w := by
      rw [BitVec.not_lt, BitVec.le_zero_iff] at hz
      exact hz
    subst h0
    rw [BitVec.umod_zero]
    rw [blastUmod.denote_go_eq_divRec_r aig assign w lhs 0#w 0#w 0#w n d q r w 0 hleft hright
      (by intro i hi; simp [hq]) (by intro i hi; simp [hr]) idx hidx]
    have := divRec_zero_d lhs w w 0 0#w (Nat.le_refl _)
    rw [BitVec.ushiftRight_eq_zero (Nat.le_refl w)] at this
    rw [this]
    simp

-- `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go`: `hq` is removable; after `w` steps the
-- initial quotient is shifted out completely (`divRec_agree` with `k = 0`, `m = w`).
theorem udiv_denote_go_hq : drop% Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go 14 := by
  intro α _ _ w aig assign lhs rhs n d q r hleft hright hr hzero idx hidx
  let f : Nat → Bool := fun i => if h : i < w then Std.Sat.AIG.denote assign ⟨aig, q.get i h⟩ else false
  rw [BitVec.udiv_eq_divRec hzero, BitVec.DivModState.init]
  rw [blastUdiv.denote_go_eq_divRec_q aig assign w lhs rhs 0#w (bvOf f w) n d q r w 0 hleft hright
    ?_ (by intro i hi; simp [hr]) idx hidx]
  · exact (divRec_agree w 0 { n := lhs, d := rhs } { wn := w, wr := 0, q := bvOf f w, r := 0#w }
      { wn := w, wr := 0, q := 0#w, r := 0#w } rfl rfl rfl (by omega)).2 idx (by omega)
  · intro i hi
    rw [bvOf_getLsbD f w i hi]
    simp [f, hi]

end BVDivHand
